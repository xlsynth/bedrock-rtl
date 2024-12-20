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

// Bedrock-RTL AXI4 to AXI4-Lite Bridge
//
// Converts an AXI4 interface to an AXI4-Lite interface. This module supports FIXED and INCR bursts.
// It does not support WRAP bursts. AXI4 burst transactions will be split into multiple AXI4-Lite
// transactions. All write responses will be aggregated into a single AXI4 write response.
//
// NOTE: This module does not support multiple outstanding AXI4 transactions. If there is a pending
// transaction, the AXI4 interface will be stalled until the pending transaction has completed.

`include "br_asserts_internal.svh"
`include "br_registers.svh"

module br_amba_axi2axil #(
    parameter int AddrWidth = 12,  // Must be at least 12
    parameter int DataWidth = 32,  // Must be at least 32
    parameter int IdWidth = 4,  // Must be at least 1
    parameter int AWUserWidth = 8,  // Must be at least 1
    parameter int ARUserWidth = 8,  // Must be at least 1
    parameter int WUserWidth = 8,  // Must be at least 1
    parameter int BUserWidth = 8,  // Must be at least 1
    parameter int RUserWidth = 8,  // Must be at least 1
    localparam int StrbWidth = DataWidth / 8
) (
    input clk,
    input rst,  // Synchronous, active-high reset

    // AXI4 interface
    input  logic [                 AddrWidth-1:0] axi_awaddr,
    input  logic [                   IdWidth-1:0] axi_awid,
    input  logic [ br_amba::AxiBurstLenWidth-1:0] axi_awlen,
    input  logic [br_amba::AxiBurstSizeWidth-1:0] axi_awsize,
    input  logic [br_amba::AxiBurstTypeWidth-1:0] axi_awburst,
    input  logic [     br_amba::AxiProtWidth-1:0] axi_awprot,
    input  logic [               AWUserWidth-1:0] axi_awuser,
    input  logic                                  axi_awvalid,
    output logic                                  axi_awready,
    input  logic [                 DataWidth-1:0] axi_wdata,
    input  logic [             (DataWidth/8)-1:0] axi_wstrb,
    input  logic                                  axi_wvalid,
    output logic                                  axi_wready,
    output logic [                   IdWidth-1:0] axi_bid,
    output logic [                BUserWidth-1:0] axi_buser,
    output logic                                  axi_bvalid,
    input  logic                                  axi_bready,
    input  logic [                 AddrWidth-1:0] axi_araddr,
    input  logic [                   IdWidth-1:0] axi_arid,
    input  logic [ br_amba::AxiBurstLenWidth-1:0] axi_arlen,
    input  logic [br_amba::AxiBurstSizeWidth-1:0] axi_arsize,
    input  logic [br_amba::AxiBurstTypeWidth-1:0] axi_arburst,
    input  logic [     br_amba::AxiProtWidth-1:0] axi_arprot,
    input  logic [               ARUserWidth-1:0] axi_aruser,
    input  logic                                  axi_arvalid,
    output logic                                  axi_arready,
    output logic [                   IdWidth-1:0] axi_rid,
    output logic [                RUserWidth-1:0] axi_ruser,
    output logic                                  axi_rvalid,
    input  logic                                  axi_rready,

    // AXI4-Lite interface
    output logic [            AddrWidth-1:0] axil_awaddr,
    output logic [br_amba::AxiProtWidth-1:0] axil_awprot,
    output logic [          AWUserWidth-1:0] axil_awuser,
    output logic                             axil_awvalid,
    input  logic                             axil_awready,
    output logic [            DataWidth-1:0] axil_wdata,
    output logic [        (DataWidth/8)-1:0] axil_wstrb,
    output logic [           WUserWidth-1:0] axil_wuser,
    output logic                             axil_wvalid,
    input  logic                             axil_wready,
    input  logic [br_amba::AxiRespWidth-1:0] axil_bresp,
    input  logic                             axil_bvalid,
    output logic                             axil_bready,
    output logic [            AddrWidth-1:0] axil_araddr,
    output logic [br_amba::AxiProtWidth-1:0] axil_arprot,
    output logic [          ARUserWidth-1:0] axil_aruser,
    output logic                             axil_arvalid,
    input  logic                             axil_arready,
    input  logic [            DataWidth-1:0] axil_rdata,
    input  logic [br_amba::AxiRespWidth-1:0] axil_rresp,
    input  logic [           RUserWidth-1:0] axil_ruser,
    input  logic                             axil_rvalid,
    output logic                             axil_rready
);

  //----------------------------------------------------------------------------
  // Integration checks
  //----------------------------------------------------------------------------
  `BR_ASSERT_STATIC(addr_width_must_be_at_least_12_a, AddrWidth >= 12)
  `BR_ASSERT_STATIC(data_width_must_be_32_or_64_a, (DataWidth == 32) || (DataWidth == 64))
  `BR_ASSERT_STATIC(id_width_must_be_at_least_1_a, IdWidth >= 1)
  `BR_ASSERT_STATIC(awuser_width_must_be_at_least_1_a, AWUserWidth >= 1)
  `BR_ASSERT_STATIC(aruser_width_must_be_at_least_1_a, ARUserWidth >= 1)
  `BR_ASSERT_STATIC(wuser_width_must_be_at_least_1_a, WUserWidth >= 1)
  `BR_ASSERT_STATIC(buser_width_must_be_at_least_1_a, BUserWidth >= 1)
  `BR_ASSERT_STATIC(ruser_width_must_be_at_least_1_a, RUserWidth >= 1)

  logic supported_write_burst_type, supported_read_burst_type;
  assign supported_write_burst_type =
      (axi_awburst == br_amba::AxiBurstIncr) || (axi_awburst == br_amba::AxiBurstFixed);
  assign supported_read_burst_type =
      (axi_arburst == br_amba::AxiBurstIncr) || (axi_arburst == br_amba::AxiBurstFixed);

  `BR_ASSERT_INTG(valid_awburst_type_a, axi_awvalid |-> supported_write_burst_type)
  `BR_ASSERT_INTG(valid_arburst_type_a, axi_arvalid |-> supported_read_burst_type)

  //----------------------------------------------------------------------------
  // Functions
  //----------------------------------------------------------------------------

  // Compute next address for each beat:
  function automatic logic [AddrWidth-1:0] next_address(
      input logic [AddrWidth-1:0] start_addr, input logic [br_amba::AxiBurstSizeWidth-1:0] size,
      input logic [br_amba::AxiBurstTypeWidth-1:0] burst_type,
      input logic [br_amba::AxiBurstLenWidth-1:0] index);
    logic [AddrWidth-1:0] increment;
    increment = (burst_type == br_amba::AxiBurstIncr) ? (index << size) : 0;
    next_address = start_addr + increment;
  endfunction

  //----------------------------------------------------------------------------
  // Signal Declarations
  //----------------------------------------------------------------------------

  logic [IdWidth-1:0] current_write_id, current_read_id;
  logic [AddrWidth-1:0] write_base_addr, read_base_addr;
  logic [br_amba::AxiProtWidth-1:0] write_prot, read_prot;
  logic [AWUserWidth-1:0] write_user, read_user;
  logic [br_amba::AxiBurstLenWidth-1:0] write_burst_len, read_burst_len;
  logic [br_amba::AxiBurstSizeWidth-1:0] write_burst_size, read_burst_size;
  logic [br_amba::AxiBurstTypeWidth-1:0] write_burst_type, read_burst_type;
  logic [br_amba::AxiBurstLenWidth:0] write_req_count, write_data_count, read_req_count;
  logic [br_amba::AxiBurstLenWidth:0] write_resp_count, read_resp_count;
  logic [br_amba::AxiRespWidth-1:0] write_resp, write_resp_next;
  logic wstate_le, rstate_le;
  logic axi_write_req_handshake, axi_write_data_handshake, axi_read_req_handshake;
  logic axi_write_resp_handshake, axi_read_resp_handshake;
  logic axil_write_req_handshake, axil_write_data_handshake, axil_read_req_handshake;
  logic axil_write_resp_handshake, axil_read_resp_handshake;

  typedef enum logic [1:0] {
    WriteStateIdle   = 2'd0,
    WriteStateActive = 2'd1,
    WriteStateDone   = 2'd2
  } wstate_t;
  wstate_t wstate, wstate_next;

  typedef enum logic [1:0] {
    ReadStateIdle   = 2'd0,
    ReadStateActive = 2'd1,
    ReadStateDone   = 2'd2
  } rstate_t;
  rstate_t rstate, rstate_next;

  //----------------------------------------------------------------------------
  // Registers
  //----------------------------------------------------------------------------

  `BR_REGIL(wstate, wstate_next, wstate_le, WriteStateIdle)
  `BR_REGLN(current_write_id, axi_awid, axi_write_req_handshake)
  `BR_REGLN(write_prot, axi_awprot, axi_write_req_handshake)
  `BR_REGLN(write_user, axi_awuser, axi_write_req_handshake)
  `BR_REGLN(write_base_addr, axi_awaddr, axi_write_req_handshake)
  `BR_REGLN(write_burst_len, axi_awlen, axi_write_req_handshake)
  `BR_REGLN(write_burst_size, axi_awsize, axi_write_req_handshake)
  `BR_REGLN(write_burst_type, axi_awburst, axi_write_req_handshake)
  `BR_REGLN(write_resp, write_resp_next, (axi_write_req_handshake || axil_write_resp_handshake))

  `BR_REGIL(rstate, rstate_next, rstate_le, ReadStateIdle)
  `BR_REGLN(current_read_id, axi_arid, axi_read_req_handshake)
  `BR_REGLN(read_prot, axi_arprot, axi_read_req_handshake)
  `BR_REGLN(read_user, axi_aruser, axi_read_req_handshake)
  `BR_REGLN(read_base_addr, axi_araddr, axi_read_req_handshake)
  `BR_REGLN(read_burst_len, axi_arlen, axi_read_req_handshake)
  `BR_REGLN(read_burst_size, axi_arsize, axi_read_req_handshake)
  `BR_REGLN(read_burst_type, axi_arburst, axi_read_req_handshake)

  //----------------------------------------------------------------------------
  // AXI4 and AXI4-Lite Handshakes
  //----------------------------------------------------------------------------

  assign axi_write_req_handshake = axi_awvalid && axi_awready;
  assign axi_write_data_handshake = axi_wvalid && axi_wready;
  assign axi_write_resp_handshake = axi_bvalid && axi_bready;
  assign axi_read_req_handshake = axi_arvalid && axi_arready;
  assign axi_read_resp_handshake = axi_rvalid && axi_rready;
  assign axil_write_req_handshake = axil_awvalid && axil_awready;
  assign axil_write_data_handshake = axil_wvalid && axil_wready;
  assign axil_write_resp_handshake = axil_bvalid && axil_bready;
  assign axil_read_req_handshake = axil_arvalid && axil_arready;
  assign axil_read_resp_handshake = axil_rvalid && axil_rready;

  //----------------------------------------------------------------------------
  // Request, Data, and Response Counters
  //----------------------------------------------------------------------------

  // Write request count
  br_counter_incr #(
      .MaxValue(1 << br_amba::AxiBurstLenWidth),
      .MaxIncrement(1)
  ) br_counter_incr_write_req (
      .clk,
      .rst,
      .reinit(axi_write_req_handshake),
      .initial_value('0),
      .incr_valid(axil_write_req_handshake),
      .incr(1'b1),
      .value(write_req_count),
      .value_next()
  );

  // Write data count
  br_counter_incr #(
      .MaxValue(1 << br_amba::AxiBurstLenWidth),
      .MaxIncrement(1)
  ) br_counter_incr_write_data (
      .clk,
      .rst,
      .reinit(axi_write_req_handshake),
      .initial_value('0),
      .incr_valid(axil_write_data_handshake),
      .incr(1'b1),
      .value(write_data_count),
      .value_next()
  );

  // Write response count
  br_counter_incr #(
      .MaxValue(1 << br_amba::AxiBurstLenWidth),
      .MaxIncrement(1)
  ) br_counter_incr_write_resp (
      .clk,
      .rst,
      .reinit(axi_write_req_handshake),
      .initial_value('0),
      .incr_valid(axil_write_resp_handshake),
      .incr(1'b1),
      .value(write_resp_count),
      .value_next()
  );

  // Read request count
  br_counter_incr #(
      .MaxValue(1 << br_amba::AxiBurstLenWidth),
      .MaxIncrement(1)
  ) br_counter_incr_read_req (
      .clk,
      .rst,
      .reinit(axi_read_req_handshake),
      .initial_value('0),
      .incr_valid(axil_read_req_handshake),
      .incr(1'b1),
      .value(read_req_count),
      .value_next()
  );

  // Read response count
  br_counter_incr #(
      .MaxValue(1 << br_amba::AxiBurstLenWidth),
      .MaxIncrement(1)
  ) br_counter_incr_read_resp (
      .clk,
      .rst,
      .reinit(axi_read_req_handshake),
      .initial_value('0),
      .incr_valid(axil_read_resp_handshake),
      .incr(1'b1),
      .value(read_resp_count),
      .value_next()
  );

  //----------------------------------------------------------------------------
  // Write State Machine and Signals
  //----------------------------------------------------------------------------

  // For write responses, we need to aggregate the responses from each beat. We need to
  // reset it when starting a new transaction.
  assign write_resp_next =
      (axi_write_req_handshake) ? br_amba::AxiRespOkay :
      (axil_bresp != br_amba::AxiRespOkay) ? axil_bresp : write_resp;

  // AXI4 write request signals
  assign axi_awready = (wstate == WriteStateIdle);

  // AXI4 write data signals
  assign axi_wready = (wstate == WriteStateActive) && axil_wready &&
                      (write_data_count <= write_burst_len);

  // AXI4 write response signals
  assign axi_bvalid = (wstate == WriteStateDone);
  assign axi_bid = current_write_id;
  assign axi_bresp = write_resp;
  assign axi_buser = write_user;

  // AXI4-Lite write request signals
  assign axil_awvalid = (wstate == WriteStateActive) && (write_req_count <= write_burst_len);
  assign axil_awaddr = next_address(
      write_base_addr, write_burst_size, write_burst_type, write_data_count
  );
  assign axil_awprot = write_prot;
  assign axil_awuser = write_user;

  // AXI4-Lite write data signals
  assign axil_wvalid = (wstate == WriteStateActive) && axi_wvalid &&
                       (write_data_count <= write_burst_len);
  assign axil_wdata = axi_wdata;
  assign axil_wstrb = axi_wstrb;
  assign axil_wuser = write_user;

  // AXI4-Lite write response signals
  assign axil_bready = 1'b1;

  always_comb begin
    wstate_next = wstate;
    wstate_le   = 1'b0;

    unique case (wstate)
      // Wait for a new write request
      WriteStateIdle: begin
        if (axi_write_req_handshake) begin
          wstate_next = WriteStateActive;
          wstate_le   = 1'b1;
        end
      end

      // Issue AXI4-Lite write requests and write data, and wait for all of the write responses
      WriteStateActive: begin
        if ((write_req_count > write_burst_len) && (write_data_count > write_burst_len) &&
            (write_resp_count > write_burst_len)) begin
          wstate_next = WriteStateDone;
          wstate_le   = 1'b1;
        end
      end

      // Perform the AXI4 write response handshake
      WriteStateDone: begin
        if (axi_write_resp_handshake) begin
          wstate_next = WriteStateIdle;
          wstate_le   = 1'b1;
        end
      end

      default: begin
        wstate_next = wstate;
      end
    endcase
  end

  //----------------------------------------------------------------------------
  // Read State Machine and Signals
  //----------------------------------------------------------------------------

  assign axi_arready = (rstate == ReadStateIdle);

  assign axi_rid = current_read_id;
  assign axi_rresp = axil_rresp;
  assign axi_rdata = axil_rdata;
  assign axi_rlast = (read_resp_count == read_burst_len);
  assign axi_ruser = axil_ruser;

  assign axil_arvalid = (rstate == ReadStateActive) && (read_req_count <= read_burst_len);
  assign axil_araddr = next_address(
      read_base_addr, read_burst_size, read_burst_type, read_resp_count
  );
  assign axil_arprot = read_prot;
  assign axil_aruser = read_user;
  assign axil_rready = (rstate == ReadStateActive) && axi_rready;

  always_comb begin
    rstate_next = rstate;
    rstate_le   = 1'b0;
    unique case (rstate)
      // Wait for a new read request
      ReadStateIdle: begin
        if (axi_read_req_handshake) begin
          rstate_next = ReadStateActive;
          rstate_le   = 1'b1;
        end
      end

      // Issue AXI4-Lite read requests and wait for all of the read responses
      ReadStateActive: begin
        if ((read_req_count > read_burst_len) && (read_resp_count > read_burst_len)) begin
          rstate_next = ReadStateDone;
          rstate_le   = 1'b1;
        end
      end

      // Perform the AXI4 read response handshake
      ReadStateDone: begin
        if (axi_read_resp_handshake) begin
          rstate_next = ReadStateIdle;
          rstate_le   = 1'b1;
        end
      end

      default: begin
        rstate_next = rstate;
      end
    endcase
  end

endmodule : br_amba_axi2axil
