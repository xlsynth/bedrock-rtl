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
    input  logic [                 UserWidth-1:0] axi_awuser,
    input  logic                                  axi_awvalid,
    output logic                                  axi_awready,
    input  logic [                 DataWidth-1:0] axi_wdata,
    input  logic [             (DataWidth/8)-1:0] axi_wstrb,
    input  logic                                  axi_wvalid,
    output logic                                  axi_wready,
    output logic [                   IdWidth-1:0] axi_bid,
    output logic [                 UserWidth-1:0] axi_buser,
    output logic                                  axi_bvalid,
    input  logic                                  axi_bready,
    input  logic [                 AddrWidth-1:0] axi_araddr,
    input  logic [                   IdWidth-1:0] axi_arid,
    input  logic [ br_amba::AxiBurstLenWidth-1:0] axi_arlen,
    input  logic [br_amba::AxiBurstSizeWidth-1:0] axi_arsize,
    input  logic [br_amba::AxiBurstTypeWidth-1:0] axi_arburst,
    input  logic [     br_amba::AxiProtWidth-1:0] axi_arprot,
    input  logic [                 UserWidth-1:0] axi_aruser,
    input  logic                                  axi_arvalid,
    output logic                                  axi_arready,
    output logic [                   IdWidth-1:0] axi_rid,
    output logic [                 UserWidth-1:0] axi_ruser,
    output logic                                  axi_rvalid,
    input  logic                                  axi_rready,

    // AXI4-Lite interface
    input  logic [            AddrWidth-1:0] axil_awaddr,
    input  logic [br_amba::AxiProtWidth-1:0] axil_awprot,
    input  logic                             axil_awvalid,
    output logic                             axil_awready,
    input  logic [            DataWidth-1:0] axil_wdata,
    input  logic [        (DataWidth/8)-1:0] axil_wstrb,
    input  logic                             axil_wvalid,
    output logic                             axil_wready,
    output logic [br_amba::AxiRespWidth-1:0] axil_bresp,
    output logic                             axil_bvalid,
    input  logic                             axil_bready,
    input  logic [            AddrWidth-1:0] axil_araddr,
    input  logic [br_amba::AxiProtWidth-1:0] axil_arprot,
    input  logic                             axil_arvalid,
    output logic                             axil_arready,
    output logic [            DataWidth-1:0] axil_rdata,
    output logic [br_amba::AxiRespWidth-1:0] axil_rresp,
    output logic                             axil_rvalid,
    input  logic                             axil_rready
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
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
      (axi_awburst == br_amba::AxiBurstTypeIncr) || (axi_awburst == br_amba::AxiBurstTypeFixed);
  assign supported_read_burst_type =
      (axi_arburst == br_amba::AxiBurstTypeIncr) || (axi_arburst == br_amba::AxiBurstTypeFixed);

  `BR_ASSERT_INTG(valid_awburst_type_a, axi_awvalid |-> supported_write_burst_type)
  `BR_ASSERT_INTG(valid_arburst_type_a, axi_arvalid |-> supported_read_burst_type)

  //------------------------------------------
  // Functions
  //------------------------------------------

  // Compute next address for each beat:
  function automatic logic [AddrWidth-1:0] next_address(
      input logic [AddrWidth-1:0] start_addr, input logic [br_amba::AxiBurstSizeWidth-1:0] size,
      input logic [br_amba::AxiBurstTypeWidth-1:0] burst_type,
      input logic [br_amba::AxiBurstLenWidth-1:0] index);
    logic [AddrWidth-1:0] increment;
    increment = (burst_type == br_amba::AxiBurstTypeIncr) ? (index << size) : 0;
    next_address = start_addr + increment;
  endfunction

  //------------------------------------------
  // Implementation
  //------------------------------------------

  logic [IdWidth-1:0] current_write_id, current_read_id;
  logic [AddrWidth-1:0] write_base_addr, read_base_addr;
  logic [br_amba::AxiProtWidth-1:0] write_prot, read_prot;
  logic [br_amba::AxiBurstLenWidth-1:0] write_burst_len, read_burst_len;
  logic [br_amba::AxiBurstSizeWidth-1:0] write_burst_size, read_burst_size;
  logic [br_amba::AxiBurstTypeWidth-1:0] write_burst_type, read_burst_type;
  logic [br_amba::AxiBurstLenWidth-1:0] write_beat_count, read_beat_count;
  logic [br_amba::AxiRespWidth-1:0] write_resp, write_resp_next;
  logic wstate_le, rstate_le;
  logic axi_write_req_handshake, axi_write_data_handshake, axi_read_req_handshake;
  logic axi_write_resp_handshake, axi_read_resp_handshake;
  logic axil_write_req_handshake, axil_write_data_handshake, axil_read_req_handshake;
  logic axil_write_resp_handshake, axil_read_resp_handshake;

  typedef enum logic [2:0] {
    WriteStateIdle = 3'd0,
    WriteStateReq  = 3'd1,
    WriteStateData = 3'd2,
    WriteStateResp = 3'd3,
    WriteStateDone = 3'd4
  } wstate_t;
  wstate_t wstate, wstate_next;

  typedef enum logic [1:0] {
    ReadStateIdle = 2'd0,
    ReadStateReq  = 2'd1,
    ReadStateResp = 2'd2,
    ReadStateDone = 2'd3
  } rstate_t;
  rstate_t rstate, rstate_next;

  `BR_REGIL(wstate, wstate_next, wstate_le, WriteStateIdle)
  `BR_REGNL(current_write_id, axi_awid, axi_write_req_handshake)
  `BR_REGNL(write_prot, axi_awprot, axi_write_req_handshake)
  `BR_REGNL(write_base_addr, axi_awaddr, axi_write_req_handshake)
  `BR_REGNL(write_burst_len, axi_awlen, axi_write_req_handshake)
  `BR_REGNL(write_burst_size, axi_awsize, axi_write_req_handshake)
  `BR_REGNL(write_burst_type, axi_awburst, axi_write_req_handshake)
  `BR_REGNL(write_resp, write_resp_next, (axi_write_req_handshake || axil_write_resp_handshake))

  `BR_REGIL(rstate, rstate_next, rstate_le, ReadStateIdle)
  `BR_REGNL(current_read_id, axi_arid, axi_read_req_handshake)
  `BR_REGNL(read_prot, axi_arprot, axi_read_req_handshake)
  `BR_REGNL(read_base_addr, axi_araddr, axi_read_req_handshake)
  `BR_REGNL(read_burst_len, axi_arlen, axi_read_req_handshake)
  `BR_REGNL(read_burst_size, axi_arsize, axi_read_req_handshake)
  `BR_REGNL(read_burst_type, axi_arburst, axi_read_req_handshake)

  `BR_REGN(write_beat_count, '0)
  `BR_REGN(read_beat_count, '0)

  `BR_REGN(write_resp, '0)
  `BR_REGN(read_resp, '0)

  // Create handshakes for write and read requests and responses
  assign valid_axi_write_req = axi_awvalid && axi_awready;
  assign valid_axi_write_data = axi_wvalid && axi_wready;
  assign valid_axi_write_resp = axi_bvalid && axi_bready;
  assign valid_axi_read_req = axi_arvalid && axi_arready;
  assign valid_axi_read_resp = axi_rvalid && axi_rready;
  assign valid_axil_write_req = axil_awvalid && axil_awready;
  assign valid_axil_write_data = axil_wvalid && axil_wready;
  assign valid_axil_write_resp = axil_bvalid && axil_bready;
  assign valid_axil_read_req = axil_arvalid && axil_arready;
  assign valid_axil_read_resp = axil_rvalid && axil_rready;

  // For write requests, we can only accept write data if we are in the WriteStateData state or
  // if we are doing a burst transactions and have more beats to send.
  assign can_accept_write_data = (wstate == WriteStateData) ||
      ((wstate == WriteStateReq) && (write_burst_type == br_amba::AxiBurstTypeIncr) &&
          (write_beat_count < write_burst_len));

  // For write responses, we need to aggregate the responses from each beat. We need to
  // reset it when starting a new transaction.
  assign write_resp_next = (valid_write_req) ? br_amba::AxiRespOkay : axil_bresp;

  // Update transaction context when new AW or AR accepted
  always @(posedge clk) begin
    if (rst) begin
      // Already reset above
    end else begin
      // Accept AW
      if (axi_write_req_handshake) begin
        write_beat_count <= 0;
      end
      // Accept AR
      if (axi_read_req_handshake) begin
        read_beat_count <= 0;
      end
    end
  end

  //----------------------------------------------------------------------------
  // Write State Machine
  //----------------------------------------------------------------------------

  // W_IDLE: Wait for AW handshake
  // Once AW accepted, start issuing each beat:
  // For each beat:
  //   W_AW: Issue AW on AXI4-Lite
  //   W_W:  Issue W on AXI4-Lite
  //   W_B:  Wait for B from AXI4-Lite, aggregate response
  // After all beats done:
  //   W_DONE: Send single B response to AXI4 master
  // Then go back to W_IDLE

  assign axi_awready = (wstate == WriteStateIdle);
  assign axi_wready = ((wstate == WriteStateData) || (wstate == WriteStateResp)) && axil_wready;

  assign axi_bvalid = (wstate == WriteStateDone);
  assign axi_bid = current_write_id;
  assign axi_bresp = write_resp;

  // Assign AXI4-Lite handshake signals based on state machine and AXI4 handshake signals
  assign axil_awaddr = next_address(
      write_base_addr, write_burst_size, write_burst_type, write_beat_count
  );
  assign axil_awprot = write_prot;
  // TODO: need to keep sending axil write requests until we are done with all beats, could use wlast
  assign axil_awvalid = (wstate == WriteStateReq);

  assign axil_wvalid = ((wstate == WriteStateData) || (wstate == WriteStateResp)) && axi_wvalid;
  assign axil_wdata = axi_wdata;
  assign axil_wstrb = axi_wstrb;

  assign axil_bready = (wstate == WriteStateResp) && axi_bready;

  always_comb begin
    wstate_next = wstate;

    unique case (wstate)
      WriteStateIdle: begin
        if (axi_write_req_handshake) begin
          wstate_next = WriteStateReq;
        end
      end

      WriteStateReq: begin
        // Issue AW on AXI4-Lite
        M_AXI_AWVALID = 1'b1;
        if (M_AXI_AWREADY) begin
          wstate_next = WriteStateData;
        end
      end

      WriteStateData: begin
        // Now wait for AXI4 master W beat
        // Once we have W beat (S_AXI_WVALID) that corresponds to this address
        // We send it to AXI4-Lite
        // Actually, since we know bursts are sequential, we can drive M_AXI_WDATA directly
        S_AXI_WREADY = 1'b1;
        if (S_AXI_WVALID && S_AXI_WREADY) begin
          M_AXI_WDATA  = S_AXI_WDATA;
          M_AXI_WSTRB  = S_AXI_WSTRB;
          M_AXI_WVALID = 1'b1;
          // Wait for M_AXI_WREADY
          if (M_AXI_WREADY) begin
            wstate_next = WriteStateResp;
          end
        end
      end

      WriteStateResp: begin
        // Wait for B from AXI4-Lite
        M_AXI_BREADY = 1'b1;
        if (M_AXI_BVALID && M_AXI_BREADY) begin
          // Aggregate response
          // If any error (SLVERR=2'b10 or DECERR=2'b11) occurs, store it
          if (M_AXI_BRESP != 2'b00) aggregate_bresp = M_AXI_BRESP;
          // Check if we are done with all beats
          if (beat_count == burst_len) begin
            // Done with all beats
            wstate_next = WriteStateDone;
          end else begin
            // More beats to go
            wstate_next = WriteStateReq;
          end
        end
      end

      WriteStateDone: begin
        // Send final B response to AXI4
        S_AXI_BID    = current_id;
        S_AXI_BRESP  = aggregate_bresp;
        S_AXI_BVALID = 1'b1;
        if (S_AXI_BREADY && S_AXI_BVALID) begin
          // Transaction completed
          wstate_next = WriteStateIdle;
        end
      end

      default: begin
        wstate_next = wstate;
      end
    endcase
  end

  // Update beat_count during write
  always @(posedge clk) begin
    if (rst) begin
      beat_count <= 0;
    end else begin
      if (wstate == WriteStateResp && wstate_next == WriteStateReq) begin
        // Completed one beat, go to next
        beat_count <= beat_count + 1;
      end else if (wstate == WriteStateDone && wstate_next == WriteStateIdle) begin
        // Reset count after done
        beat_count <= 0;
      end
    end
  end

  //----------------------------------------------------------------------------
  // Read State Machine
  //----------------------------------------------------------------------------

  // R_IDLE: Wait for AR handshake
  // For each beat:
  //   R_AR: Issue AR on AXI4-Lite
  //   R_R: Wait for R from AXI4-Lite, then send it out as AXI4 R beat
  // After all beats:
  //   R_DONE: Wait until AXI4 master takes last R with RLAST=1
  // Go back to R_IDLE

  assign axi_rid = current_read_id;
  assign axi_rresp = read_resp;

  assign axil_rready = (rstate == ReadStateResp) && axi_rready;

  always_comb begin
    rstate_next   = rstate;

    M_AXI_ARVALID = 1'b0;
    M_AXI_RREADY  = 1'b0;

    S_AXI_ARREADY = can_accept_ar;
    S_AXI_RVALID  = 1'b0;
    S_AXI_RRESP   = 2'b00;
    S_AXI_RLAST   = 1'b0;
    S_AXI_RID     = current_id;

    unique case (rstate)
      ReadStateIdle: begin
        // Accept AR
        if (S_AXI_ARVALID && S_AXI_ARREADY) begin
          rstate_next = ReadStateReq;
        end
      end

      ReadStateReq: begin
        // Issue AR to AXI4-Lite
        M_AXI_ARADDR  = next_address(base_addr, burst_size, burst_type, beat_count);
        M_AXI_ARVALID = 1'b1;
        if (M_AXI_ARREADY && M_AXI_ARVALID) begin
          rstate_next = ReadStateResp;
        end
      end

      ReadStateResp: begin
        // Wait for RDATA from AXI4-Lite
        M_AXI_RREADY = 1'b1;
        if (M_AXI_RVALID && M_AXI_RREADY) begin
          // Send this data out on AXI4 side
          S_AXI_RDATA  = M_AXI_RDATA;
          S_AXI_RRESP  = M_AXI_RRESP;
          S_AXI_RVALID = 1'b1;
          S_AXI_RLAST  = (beat_count == burst_len);

          if (S_AXI_RREADY && S_AXI_RVALID) begin
            // AXI4 master accepted the data
            if (beat_count == burst_len) begin
              // Done with all beats
              rstate_next = ReadStateDone;
            end else begin
              // More beats to request
              rstate_next = ReadStateReq;
            end
          end
        end
      end

      ReadStateDone: begin
        // All data returned. Just wait here until we've served all responses.
        // Actually, once we are here, we completed everything.
        // We can go back to idle once AXI4 master took the last beat.
        // The last beat acceptance was done in R_R.
        rstate_next = ReadStateIdle;
      end

      default: begin
        rstate_next = rstate;
      end
    endcase
  end

  // Update beat_count during read
  always @(posedge clk) begin
    if (rst) begin
      beat_count <= 0;
    end else begin
      if (rstate == R_R && rstate_next == R_AR) begin
        // One beat done, move to next
        beat_count <= beat_count + 1;
      end else if (rstate == R_DONE && rstate_next == R_IDLE) begin
        // Reset count
        beat_count <= 0;
      end
    end
  end

endmodule : br_amba_axi2axil
