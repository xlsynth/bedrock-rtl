// Copyright 2024 The Bedrock-RTL Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Bedrock-RTL AXI4 to AXI4-Lite Bridge Core
//
// This module is the core of the AXI4 to AXI4-Lite bridge. It handles the unrolling of AXI4 bursts
// into AXI4-Lite transactions, and the aggregation of AXI4-Lite responses.
//
// This module also supports optional datapaths for both requests and responses. If
// `ReqDatapathEnable` is set, the module will pass through the AXI4 request and data signals to the
// AXI4-Lite interface. If `RespDatapathEnable` is set, the module will pass through the AXI4-Lite
// response signals to the AXI4 interface.
//
// This module is instantiated twice in the br_amba_axi2axil module to support both read and write
// requests separately.

`include "br_asserts_internal.svh"
`include "br_registers.svh"
`include "br_unused.svh"

module br_amba_axi2axil_core #(
    parameter int AddrWidth = 12,  // Must be at least 12
    parameter int DataWidth = 32,  // Must be at least 32
    parameter int IdWidth = 4,  // Must be at least 1
    parameter int ReqUserWidth = 8,  // Must be at least 1
    parameter int RespUserWidth = 8,  // Must be at least 1
    parameter int ReqDataUserWidth = 8,  // Must be at least 1
    parameter int MaxOutstandingReqs = 16,  // Must be at least 2
    parameter bit IsReadNotWrite = 0,  // Must be 0 or 1
    localparam int StrobeWidth = DataWidth / 8
) (
    input clk,
    input rst,  // Synchronous, active-high reset

    // AXI4 interface
    input  logic [                 AddrWidth-1:0] axi_req_addr,
    input  logic [                   IdWidth-1:0] axi_req_id,
    input  logic [ br_amba::AxiBurstLenWidth-1:0] axi_req_len,
    input  logic [br_amba::AxiBurstSizeWidth-1:0] axi_req_size,
    input  logic [br_amba::AxiBurstTypeWidth-1:0] axi_req_burst,
    input  logic [     br_amba::AxiProtWidth-1:0] axi_req_prot,
    input  logic [              ReqUserWidth-1:0] axi_req_user,
    input  logic                                  axi_req_valid,
    output logic                                  axi_req_ready,

    input  logic [       DataWidth-1:0] axi_req_data,
    input  logic [     StrobeWidth-1:0] axi_req_data_strb,
    input  logic [ReqDataUserWidth-1:0] axi_req_data_user,
    input  logic                        axi_req_data_valid,
    output logic                        axi_req_data_ready,

    output logic [              IdWidth-1:0] axi_resp_id,
    output logic [        RespUserWidth-1:0] axi_resp_user,
    output logic [br_amba::AxiRespWidth-1:0] axi_resp_resp,
    output logic [            DataWidth-1:0] axi_resp_data,
    output logic                             axi_resp_data_last,
    output logic                             axi_resp_valid,
    input  logic                             axi_resp_ready,

    // AXI4-Lite interface
    output logic [            AddrWidth-1:0] axil_req_addr,
    output logic [br_amba::AxiProtWidth-1:0] axil_req_prot,
    output logic [         ReqUserWidth-1:0] axil_req_user,
    output logic                             axil_req_valid,
    input  logic                             axil_req_ready,

    output logic [       DataWidth-1:0] axil_req_data,
    output logic [     StrobeWidth-1:0] axil_req_data_strb,
    output logic [ReqDataUserWidth-1:0] axil_req_data_user,
    output logic                        axil_req_data_valid,
    input  logic                        axil_req_data_ready,

    input  logic [br_amba::AxiRespWidth-1:0] axil_resp_resp,
    input  logic [        RespUserWidth-1:0] axil_resp_user,
    input  logic [            DataWidth-1:0] axil_resp_data,
    input  logic                             axil_resp_valid,
    output logic                             axil_resp_ready
);

  //----------------------------------------------------------------------------
  // Integration checks
  //----------------------------------------------------------------------------

  // ri lint_check_off GENERATE_NAME
  `BR_ASSERT_STATIC(addr_width_must_be_at_least_12_a, AddrWidth >= 12)
  `BR_ASSERT_STATIC(data_width_must_be_32_or_64_a, (DataWidth == 32) || (DataWidth == 64))
  `BR_ASSERT_STATIC(id_width_must_be_at_least_1_a, IdWidth >= 1)
  `BR_ASSERT_STATIC(req_user_width_must_be_at_least_1_a, ReqUserWidth >= 1)
  `BR_ASSERT_STATIC(resp_user_width_must_be_at_least_1_a, RespUserWidth >= 1)
  `BR_ASSERT_STATIC(req_data_user_width_must_be_at_least_1_a, ReqDataUserWidth >= 1)
  `BR_ASSERT_STATIC(max_outstanding_reqs_must_be_at_least_2_a, MaxOutstandingReqs >= 2)
  // ri lint_check_on GENERATE_NAME

  // These signals are only read from in assertions.
  logic supported_burst_type;
  logic resp_fifo_pop_valid;
  `BR_UNUSED(supported_burst_type)
  `BR_UNUSED(resp_fifo_pop_valid)

  // ri lint_check_off ENUM_COMPARE
  assign supported_burst_type =
      (axi_req_burst == br_amba::AxiBurstIncr) || (axi_req_burst == br_amba::AxiBurstFixed);
  // ri lint_check_on ENUM_COMPARE

  // We should only get requests with a supported burst type (Incr or Fixed)
  `BR_ASSERT_INTG(valid_burst_type_a, axi_req_valid |-> supported_burst_type)

  // We should only get responses when the response FIFO is not empty
  `BR_ASSERT_INTG(resp_fifo_not_empty_when_resp_valid_a, axil_resp_valid |-> resp_fifo_pop_valid)

  //----------------------------------------------------------------------------
  // Functions
  //----------------------------------------------------------------------------

  // Compute next address for each beat:
  function automatic logic [AddrWidth-1:0] next_address(
      input logic [AddrWidth-1:0] start_addr, input logic [br_amba::AxiBurstSizeWidth-1:0] size,
      input logic [br_amba::AxiBurstLenWidth-1:0] burst_len,
      input logic [br_amba::AxiBurstTypeWidth-1:0] burst_type,
      input logic [br_amba::AxiBurstLenWidth:0] index);
    logic [AddrWidth-1:0] increment;
    logic [AddrWidth-1:0] base_address;  // aligned to wrap boundary
    logic [AddrWidth-1:0] wrap_mask;  // mask the wrap boundary

    increment = start_addr + (index << size);  // ri lint_check_waive VAR_SHIFT

    unique case (br_amba::axi_burst_type_t'(burst_type))
      br_amba::AxiBurstIncr: begin
        next_address = start_addr + increment;
      end
      br_amba::AxiBurstWrap: begin
        wrap_mask = ((burst_len + 1) << size) - 1;  // ri lint_check_waive ARITH_EXTENSION VAR_SHIFT TRUNC_LSHIFT
        base_address = start_addr & ~wrap_mask;
        next_address = base_address | ((start_addr + increment) & wrap_mask);
      end
      default: begin
        next_address = start_addr;
      end
    endcase
  endfunction

  //----------------------------------------------------------------------------
  // Signal Declarations
  //----------------------------------------------------------------------------

  localparam int RespFifoWidth = (IdWidth + 1);  // 1 bit to indicate if the burst is complete

  // Request signals
  logic [IdWidth-1:0] current_req_id;
  logic [AddrWidth-1:0] req_base_addr;
  logic [br_amba::AxiProtWidth-1:0] req_prot;
  logic [ReqUserWidth-1:0] req_user;
  logic [br_amba::AxiBurstLenWidth-1:0] req_burst_len;
  logic [br_amba::AxiBurstSizeWidth-1:0] req_burst_size;
  logic [br_amba::AxiBurstTypeWidth-1:0] req_burst_type;
  logic [br_amba::AxiBurstLenWidth:0] req_count;
  logic [br_amba::AxiRespWidth-1:0] resp, resp_next;
  logic state_le;
  logic axi_req_handshake;
  logic axi_resp_handshake;
  logic axil_req_handshake;
  logic axil_resp_handshake;
  logic [br_amba::AxiBurstLenWidth:0] burst_len_extended;
  logic [RespFifoWidth-1:0] resp_fifo_push_data, resp_fifo_pop_data;
  logic resp_fifo_push_valid;
  logic resp_fifo_push_ready, resp_fifo_pop_ready;
  logic zero_burst_len;
  logic is_last_req_beat;

  typedef enum logic [1:0] {
    StateIdle     = 2'b01,
    StateReqSplit = 2'b10
  } state_t;
  state_t state, state_next;  // ri lint_check_waive ONE_BIT_STATE_REG

  //----------------------------------------------------------------------------
  // Registers
  //----------------------------------------------------------------------------

  `BR_REGIL(state, state_next, state_le, StateIdle)
  `BR_REGLN(current_req_id, axi_req_id, axi_req_handshake)
  `BR_REGLN(req_prot, axi_req_prot, axi_req_handshake)
  `BR_REGLN(req_user, axi_req_user, axi_req_handshake)
  `BR_REGLN(req_base_addr, axi_req_addr, axi_req_handshake)
  `BR_REGLN(req_burst_len, axi_req_len, axi_req_handshake)
  `BR_REGLN(req_burst_size, axi_req_size, axi_req_handshake)
  `BR_REGLN(req_burst_type, axi_req_burst, axi_req_handshake)
  `BR_REGLN(resp, resp_next, (axi_resp_handshake || axil_resp_handshake))

  //----------------------------------------------------------------------------
  // AXI4 and AXI4-Lite Handshakes
  //----------------------------------------------------------------------------

  assign axi_req_handshake   = axi_req_valid && axi_req_ready;
  assign axi_resp_handshake  = axi_resp_valid && axi_resp_ready;

  assign axil_req_handshake  = axil_req_valid && axil_req_ready;
  assign axil_resp_handshake = axil_resp_valid && axil_resp_ready;

  //----------------------------------------------------------------------------
  // Request Split State Machine and Signals
  //----------------------------------------------------------------------------

  // ri lint_check_off GRAY_CODE_FSM
  always_comb begin
    state_next = state;
    state_le = 1'b0;
    axi_req_ready = 1'b0;
    axil_req_valid = 1'b0;
    resp_fifo_push_data = {(IdWidth + 1) {1'b0}};

    unique case (state)
      // Wait for a new request
      StateIdle: begin
        axi_req_ready = axil_req_ready && resp_fifo_push_ready;
        axil_req_valid = axi_req_valid && resp_fifo_push_ready;

        resp_fifo_push_data = {axi_req_id, zero_burst_len};

        // If there is a new request, and it is not a single beat request, then we need to split it
        // into multiple AXI4-Lite requests.
        if (axi_req_handshake && !zero_burst_len) begin
          state_next = StateReqSplit;
          state_le   = 1'b1;
        end
      end

      // Issue AXI4-Lite requests
      StateReqSplit: begin
        axil_req_valid = resp_fifo_push_ready;

        resp_fifo_push_data = {current_req_id, is_last_req_beat};

        if (axil_req_handshake && is_last_req_beat) begin
          state_next = StateIdle;
          state_le   = 1'b1;
        end
      end

      default: begin
        state_next = state;  // ri lint_check_waive ENUM_ASSIGN FSM_DEFAULT_REQ
      end
    endcase
  end
  // ri lint_check_on GRAY_CODE_FSM

  //----------------------------------------------------------------------------
  // Request Counter
  //----------------------------------------------------------------------------

  // Request count
  br_counter_incr #(
      .MaxValue(1 << br_amba::AxiBurstLenWidth),
      .MaxIncrement(1)
  ) br_counter_incr_req (
      .clk,
      .rst,
      .reinit(axi_req_handshake),
      .initial_value({{br_amba::AxiBurstLenWidth{1'b0}}, 1'b1}),
      .incr_valid(axil_req_handshake),
      .incr(1'b1),
      .value(req_count),
      .value_next()
  );

  assign zero_burst_len = (axi_req_len == {br_amba::AxiBurstLenWidth{1'b0}});
  assign burst_len_extended = {1'b0, req_burst_len};  // ri lint_check_waive ZERO_EXT
  assign is_last_req_beat = (req_count == burst_len_extended);

  //----------------------------------------------------------------------------
  // Request Transaction Signals
  //----------------------------------------------------------------------------

  // AXI4-Lite request signals
  assign axil_req_addr = next_address(
      req_base_addr, req_burst_size, req_burst_len, req_burst_type, req_count
  );
  assign axil_req_prot = req_prot;
  assign axil_req_user = req_user;

  //----------------------------------------------------------------------------
  // Request Data Path Signals
  //----------------------------------------------------------------------------

  assign axi_req_data_ready = axil_req_data_ready;
  assign axil_req_data = axi_req_data;
  assign axil_req_data_strb = axi_req_data_strb;
  assign axil_req_data_user = axi_req_data_user;
  assign axil_req_data_valid = axi_req_data_valid;

  //----------------------------------------------------------------------------
  // Response Data Path
  //----------------------------------------------------------------------------

  br_fifo_flops #(
      .Depth(MaxOutstandingReqs),
      .Width(RespFifoWidth),
      .EnableBypass(0),
      .RegisterPopOutputs(0),
      .FlopRamDepthTiles(1),
      .FlopRamWidthTiles(1),
      .FlopRamAddressDepthStages(0),
      .FlopRamReadDataDepthStages(0),
      .FlopRamReadDataWidthStages(0)
  ) br_fifo_flops_resp_tracker (
      .clk,
      .rst,

      // Push-side interface.
      .push_ready(resp_fifo_push_ready),
      .push_valid(resp_fifo_push_valid),
      .push_data (resp_fifo_push_data),

      // Pop-side interface.
      .pop_ready(resp_fifo_pop_ready),
      .pop_valid(resp_fifo_pop_valid),
      .pop_data (resp_fifo_pop_data),

      // Push-side status flags
      .full(),
      .full_next(),
      .slots(),
      .slots_next(),

      // Pop-side status flags
      .empty(),
      .empty_next(),
      .items(),
      .items_next()
  );

  assign resp_fifo_push_valid = axil_req_handshake;
  assign resp_fifo_pop_ready = axil_resp_handshake;

  //----------------------------------------------------------------------------
  // Response Signals
  //----------------------------------------------------------------------------

  assign axi_resp_data = axil_resp_data;
  assign axi_resp_user = axil_resp_user;

  // Extract the ID and last signal from the response FIFO
  assign {axi_resp_id, axi_resp_data_last} = resp_fifo_pop_data;

  // For write responses, we need to aggregate the responses from each beat. We need to
  // reset it after each response.
  assign resp_next = (axi_resp_handshake) ? br_amba::AxiRespOkay :  // ri lint_check_waive ENUM_RHS
      (axil_resp_resp != br_amba::AxiRespOkay) ?  // ri lint_check_waive ENUM_COMPARE
      axil_resp_resp : resp;

  // The handling of read and write responses is different. For read responses, we need to
  // generate an AXI4 response for each AXI4-Lite response. For write responses, we only need to
  // generate an AXI4 response for the last beat as indicated by axi_resp_data_last.
  generate
    if (IsReadNotWrite) begin : gen_read_response
      assign axi_resp_valid  = axil_resp_valid;
      assign axi_resp_resp   = axil_resp_resp;
      assign axil_resp_ready = axi_resp_ready;
    end else begin : gen_write_response
      assign axi_resp_valid = (axi_resp_data_last && axil_resp_valid);
      assign axi_resp_resp = (axil_resp_resp != br_amba::AxiRespOkay) ?  // ri lint_check_waive ENUM_COMPARE
          axil_resp_resp : resp;
      assign axil_resp_ready = (!axi_resp_data_last || axi_resp_ready);
    end
  endgenerate

endmodule : br_amba_axi2axil_core
