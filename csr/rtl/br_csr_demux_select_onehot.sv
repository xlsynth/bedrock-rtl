// SPDX-License-Identifier: Apache-2.0
//
// Bedrock-RTL CSR Demux with Onehot Select
//
// Routes an SCB request according to a onehot selection input. Responses from
// downstream interfaces are muxed together and passed upstream to the request
// initiator. Each downstream interface can be retimed independently.
//
// A valid request with no selected downstream receives a decode error response.

`include "br_asserts_internal.svh"
`include "br_registers.svh"

module br_csr_demux_select_onehot #(
    parameter int AddrWidth = 1,  // Must be at least 1
    parameter int DataWidth = 32,  // Must be 32 or 64
    parameter int NumDownstreams = 1,  // Must be at least 1
    // ri lint_check_waive ARRAY_LENGTH_ONE
    parameter int NumRetimeStages[NumDownstreams] = '{default: 0},
    localparam int StrobeWidth = DataWidth / 8
) (
    input logic clk,
    input logic rst,

    // For a valid request, select one downstream or leave all zero.
    input logic [NumDownstreams-1:0] select_onehot,

    input logic upstream_req_valid,
    input logic upstream_req_write,
    input logic [AddrWidth-1:0] upstream_req_addr,
    input logic [DataWidth-1:0] upstream_req_wdata,
    input logic [StrobeWidth-1:0] upstream_req_wstrb,
    input logic upstream_req_privileged,
    input logic upstream_req_secure,
    input logic upstream_req_abort,

    output logic upstream_resp_valid,
    output logic [DataWidth-1:0] upstream_resp_rdata,
    output logic upstream_resp_decerr,
    output logic upstream_resp_slverr,

    output logic [NumDownstreams-1:0] downstream_req_valid,
    output logic [NumDownstreams-1:0] downstream_req_write,
    output logic [NumDownstreams-1:0][AddrWidth-1:0] downstream_req_addr,
    output logic [NumDownstreams-1:0][DataWidth-1:0] downstream_req_wdata,
    output logic [NumDownstreams-1:0][StrobeWidth-1:0] downstream_req_wstrb,
    output logic [NumDownstreams-1:0] downstream_req_privileged,
    output logic [NumDownstreams-1:0] downstream_req_secure,
    output logic [NumDownstreams-1:0] downstream_req_abort,

    input logic [NumDownstreams-1:0] downstream_resp_valid,
    input logic [NumDownstreams-1:0][DataWidth-1:0] downstream_resp_rdata,
    input logic [NumDownstreams-1:0] downstream_resp_decerr,
    input logic [NumDownstreams-1:0] downstream_resp_slverr
);
  // Integration Checks

  `BR_ASSERT_STATIC(legal_num_downstreams_a, NumDownstreams >= 1)
  `BR_ASSERT_STATIC(legal_addr_width_a, AddrWidth >= 1)
  `BR_ASSERT_STATIC(legal_data_width_a, DataWidth == 32 || DataWidth == 64)
  `BR_ASSERT_INTG(select_onehot0_a, upstream_req_valid |-> $onehot0(select_onehot))

  // Implementation

  logic [NumDownstreams-1:0] downstream_req_valid_int;
  logic [NumDownstreams-1:0] downstream_req_write_int;
  logic [NumDownstreams-1:0][AddrWidth-1:0] downstream_req_addr_int;
  logic [NumDownstreams-1:0][DataWidth-1:0] downstream_req_wdata_int;
  logic [NumDownstreams-1:0][StrobeWidth-1:0] downstream_req_wstrb_int;
  logic [NumDownstreams-1:0] downstream_req_privileged_int;
  logic [NumDownstreams-1:0] downstream_req_secure_int;
  logic [NumDownstreams-1:0] downstream_req_abort_int;

  assign downstream_req_valid_int = select_onehot & {NumDownstreams{upstream_req_valid}};
  assign downstream_req_write_int = {NumDownstreams{upstream_req_write}};
  assign downstream_req_addr_int = {NumDownstreams{upstream_req_addr}};
  assign downstream_req_wdata_int = {NumDownstreams{upstream_req_wdata}};
  assign downstream_req_wstrb_int = {NumDownstreams{upstream_req_wstrb}};
  assign downstream_req_privileged_int = {NumDownstreams{upstream_req_privileged}};
  assign downstream_req_secure_int = {NumDownstreams{upstream_req_secure}};
  // It's safe to broadcast abort to all downstreams. A branch with no active
  // request ignores abort.
  assign downstream_req_abort_int = {NumDownstreams{upstream_req_abort}};

  // Request retiming
  for (genvar i = 0; i < NumDownstreams; i++) begin : gen_downstream_req_retime
    // Retime the valid-qualified signals (exclude abort).
    br_delay_valid #(
        .Width(1 + AddrWidth + DataWidth + StrobeWidth + 2),
        // ri lint_check_waive PARAM_BIT_SEL
        .NumStages(NumRetimeStages[i])
    ) br_delay_valid_req (
        .clk,
        .rst,
        .in_valid(downstream_req_valid_int[i]),
        .in({
          downstream_req_write_int[i],
          downstream_req_addr_int[i],
          downstream_req_wdata_int[i],
          downstream_req_wstrb_int[i],
          downstream_req_privileged_int[i],
          downstream_req_secure_int[i]
        }),
        .out_valid(downstream_req_valid[i]),
        .out({
          downstream_req_write[i],
          downstream_req_addr[i],
          downstream_req_wdata[i],
          downstream_req_wstrb[i],
          downstream_req_privileged[i],
          downstream_req_secure[i]
        }),
        .out_valid_stages(),
        .out_stages()
    );

    // Retime the abort signal.
    br_delay #(
        .Width(1),
        // ri lint_check_waive PARAM_BIT_SEL
        .NumStages(NumRetimeStages[i])
    ) br_delay_req_abort (
        .clk,
        .rst,
        .in(downstream_req_abort_int[i]),
        .out(downstream_req_abort[i]),
        .out_stages()
    );
  end

  // Response struct for retiming/muxing
  typedef struct packed {
    logic [DataWidth-1:0] rdata;
    logic decerr;
    logic slverr;
  } resp_t;

  // Decode error handling
  logic  decerr_resp_valid_next;
  logic  decerr_resp_valid;
  resp_t decerr_resp;

  // If no downstream is selected, return decerr.
  assign decerr_resp_valid_next = upstream_req_valid && !(|select_onehot);
  assign decerr_resp = '{rdata: '0, decerr: 1'b1, slverr: 1'b0};

  `BR_REG(decerr_resp_valid, decerr_resp_valid_next)

  // Response retiming
  resp_t [NumDownstreams-1:0] downstream_resp;
  logic  [NumDownstreams-1:0] downstream_resp_valid_int;
  resp_t [NumDownstreams-1:0] downstream_resp_int;

  for (genvar i = 0; i < NumDownstreams; i++) begin : gen_downstream_resp_retime
    assign downstream_resp[i] = '{
            rdata: downstream_resp_rdata[i],
            decerr: downstream_resp_decerr[i],
            slverr: downstream_resp_slverr[i]
        };

    br_delay_valid #(
        .Width($bits(resp_t)),
        // ri lint_check_waive PARAM_BIT_SEL
        .NumStages(NumRetimeStages[i])
    ) br_delay_valid_resp (
        .clk,
        .rst,
        .in_valid(downstream_resp_valid[i]),
        .in(downstream_resp[i]),
        .out_valid(downstream_resp_valid_int[i]),
        .out(downstream_resp_int[i]),
        .out_valid_stages(),
        .out_stages()
    );
  end

  // Response muxing
  // Choose between retimed downstream responses and the decode error response.
  resp_t upstream_resp;

  br_mux_onehot #(
      .NumSymbolsIn(NumDownstreams + 1),
      .SymbolWidth ($bits(resp_t))
  ) br_mux_onehot_resp (
      .select({decerr_resp_valid, downstream_resp_valid_int}),
      .in({decerr_resp, downstream_resp_int}),
      .out(upstream_resp)
  );

  assign upstream_resp_valid  = decerr_resp_valid || (|downstream_resp_valid_int);
  assign upstream_resp_rdata  = upstream_resp.rdata;
  assign upstream_resp_decerr = upstream_resp.decerr;
  assign upstream_resp_slverr = upstream_resp.slverr;

endmodule : br_csr_demux_select_onehot
