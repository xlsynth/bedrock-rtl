// SPDX-License-Identifier: Apache-2.0
//
// Bedrock-RTL SCB Demux
//
// Routes SCB requests to the correct downstream interface based on the request
// address. The address range for each downstream interface is specified by a
// pair of static inputs. Responses from the downstream interfaces are muxed
// together and passed upstream to the request initiator. Each downstream
// interface can be retimed by a configurable number of stages.
//

`include "br_asserts_internal.svh"
`include "br_registers.svh"

module br_csr_demux #(
    parameter int AddrWidth = 1,  // Must be at least 1
    parameter int DataWidth = 32,  // Must be 32 or 64
    parameter int NumDownstreams = 1,  // Must be at least 1
    // ri lint_check_waive ARRAY_LENGTH_ONE
    parameter int NumRetimeStages[NumDownstreams] = '{default: 0},

    localparam int StrobeWidth = DataWidth / 8
) (
    input logic clk,
    input logic rst,

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

    // Inclusive min and max addresses for each downstream interface
    input logic [NumDownstreams-1:0][AddrWidth-1:0] downstream_addr_base,
    input logic [NumDownstreams-1:0][AddrWidth-1:0] downstream_addr_limit,

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

  for (genvar i = 0; i < NumDownstreams; i++) begin : gen_positive_range_check
    `BR_ASSERT_INTG(downstream_addr_range_positive_a,
                    $fell(rst) |-> downstream_addr_base[i] <= downstream_addr_limit[i])
  end

  for (genvar i = 0; i < NumDownstreams - 1; i++) begin : gen_range_overlap_check_i
    for (genvar j = i + 1; j < NumDownstreams; j++) begin : gen_range_overlap_check_j
      `BR_ASSERT_INTG(downstream_addr_range_overlap_a,
                      $fell(
                          rst
                      ) |-> downstream_addr_limit[i] < downstream_addr_base[j] ||
                          downstream_addr_base[i] > downstream_addr_limit[j])
    end
  end

  // Implementation

  logic [NumDownstreams-1:0] select_onehot;
  logic [NumDownstreams-1:0] downstream_req_valid_int;
  logic [NumDownstreams-1:0] downstream_req_write_int;
  logic [NumDownstreams-1:0][AddrWidth-1:0] downstream_req_addr_int;
  logic [NumDownstreams-1:0][DataWidth-1:0] downstream_req_wdata_int;
  logic [NumDownstreams-1:0][StrobeWidth-1:0] downstream_req_wstrb_int;
  logic [NumDownstreams-1:0] downstream_req_privileged_int;
  logic [NumDownstreams-1:0] downstream_req_secure_int;
  logic [NumDownstreams-1:0] downstream_req_abort_int;

  // Request address decoding
  for (genvar i = 0; i < NumDownstreams; i++) begin : gen_select
    assign select_onehot[i] =
        (upstream_req_addr >= downstream_addr_base[i]) &&
        (upstream_req_addr <= downstream_addr_limit[i]);
  end

  assign downstream_req_valid_int = select_onehot & {NumDownstreams{upstream_req_valid}};
  assign downstream_req_write_int = {NumDownstreams{upstream_req_write}};
  assign downstream_req_addr_int = {NumDownstreams{upstream_req_addr}};
  assign downstream_req_wdata_int = {NumDownstreams{upstream_req_wdata}};
  assign downstream_req_wstrb_int = {NumDownstreams{upstream_req_wstrb}};
  assign downstream_req_privileged_int = {NumDownstreams{upstream_req_privileged}};
  assign downstream_req_secure_int = {NumDownstreams{upstream_req_secure}};
  // It's safe to just broadcast the abort signal to all downstreams
  // If there is no active request on a branch, the abort signal will be ignored.
  assign downstream_req_abort_int = {NumDownstreams{upstream_req_abort}};

  // Request retiming
  for (genvar i = 0; i < NumDownstreams; i++) begin : gen_downstream_req_retime
    // Retime the valid-qualified signals (exclude abort)
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

    // Retime the abort signal
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

  // If we get a request that doesn't match any downstream address range,
  // send a response with decerr=1.
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
  // Choose between retimed downstream responses and the decode error response
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

endmodule
