`include "br_asserts_internal.svh"
`include "br_unused.svh"
`include "br_registers.svh"

module br_csr_axil_widget #(
    parameter int AddrWidth = 1,  // Must be at least 1
    parameter int DataWidth = 8,  // Must be at least 8
    parameter int NumOutstanding = 1,  // Must be at least 1
    parameter bit RegisterResponseOutputs = 0,

    localparam int StrobeWidth = DataWidth / 8,
    localparam int TagWidth = br_math::clamped_clog2(NumOutstanding)
) (
    input clk,
    input rst,  // Synchronous, active-high reset

    // AXI4-Lite target interface
    input  logic                             axil_awvalid,
    output logic                             axil_awready,
    input  logic [            AddrWidth-1:0] axil_awaddr,
    input  logic [br_amba::AxiProtWidth-1:0] axil_awprot,
    input  logic                             axil_wvalid,
    output logic                             axil_wready,
    input  logic [            DataWidth-1:0] axil_wdata,
    input  logic [          StrobeWidth-1:0] axil_wstrb,
    output logic                             axil_bvalid,
    input  logic                             axil_bready,
    output logic [br_amba::AxiRespWidth-1:0] axil_bresp,
    input  logic                             axil_arvalid,
    output logic                             axil_arready,
    input  logic [            AddrWidth-1:0] axil_araddr,
    input  logic [br_amba::AxiProtWidth-1:0] axil_arprot,
    output logic                             axil_rvalid,
    input  logic                             axil_rready,
    output logic [            DataWidth-1:0] axil_rdata,
    output logic [br_amba::AxiRespWidth-1:0] axil_rresp,

    output logic                 csr_req_valid,
    input  logic                 csr_req_ready,
    output logic                 csr_req_write,
    output logic [AddrWidth-1:0] csr_req_addr,
    output logic [DataWidth-1:0] csr_req_data,
    output logic [ TagWidth-1:0] csr_req_tag,

    input logic                 csr_resp_valid,
    input logic                 csr_resp_write,
    input logic [DataWidth-1:0] csr_resp_data,
    input logic [ TagWidth-1:0] csr_resp_tag,
    input logic                 csr_resp_slverr,
    input logic                 csr_resp_decerr
);

  //----------------------------------------------------------------------------
  // Integration checks
  //----------------------------------------------------------------------------
  `BR_ASSERT_STATIC(legal_addr_width_a, AddrWidth >= 1)
  `BR_ASSERT_STATIC(legal_data_width_a, DataWidth >= 8)
  `BR_ASSERT_STATIC(legal_num_outstanding_a, NumOutstanding >= 1)

  // TODO(zhemao): Add support for partial writes through RMW
  `BR_ASSERT_INTG(no_partial_writes_a, axil_wvalid |-> axil_wstrb == '1)

  //----------------------------------------------------------------------------
  // Implementation
  //----------------------------------------------------------------------------

  logic csr_write_valid;
  logic csr_write_ready;

  br_flow_join #(
      .NumFlows(2)
  ) br_flow_join_csr_write (
      .clk,
      .rst,
      .push_ready({axil_awready, axil_wready}),
      .push_valid({axil_awvalid, axil_wvalid}),
      .pop_ready (csr_write_ready),
      .pop_valid (csr_write_valid)
  );

  logic csr_req_no_tag_ready;
  logic csr_req_no_tag_valid;

  br_flow_mux_rr_stable #(
      .NumFlows(2),
      .Width(AddrWidth + DataWidth + 1)
  ) br_flow_mux_rr_stable_csr_req (
      .clk,
      .rst,
      .push_ready({csr_write_ready, axil_arready}),
      .push_valid({csr_write_valid, axil_arvalid}),
      .push_data ({axil_awaddr, axil_wdata, 1'b1, axil_araddr, {DataWidth{1'b0}}, 1'b0}),
      .pop_ready (csr_req_no_tag_ready),
      .pop_valid (csr_req_no_tag_valid),
      .pop_data  ({csr_req_addr, csr_req_data, csr_req_write})
  );

  // CSR bus doesn't currently support protection bits
  `BR_UNUSED_NAMED(axil_axprot, {axil_awprot, axil_arprot})
  // Not currently supporting partial writes
  `BR_UNUSED(axil_wstrb)

  logic csr_req_tag_valid;
  logic csr_req_tag_ready;

  br_amba::axi_resp_t csr_resp_resp;
  logic reordered_csr_resp_valid;
  logic reordered_csr_resp_ready;
  br_amba::axi_resp_t reordered_csr_resp_resp;
  logic [DataWidth-1:0] reordered_csr_resp_data;
  logic reordered_csr_resp_write;

  assign csr_resp_resp =
      csr_resp_decerr ? br_amba::AxiRespDecerr :
      csr_resp_slverr ? br_amba::AxiRespSlverr :
      br_amba::AxiRespOkay;

  br_tracker_reorder_buffer_flops #(
      .NumEntries(NumOutstanding),
      .EntryIdWidth(TagWidth),
      .DataWidth(br_amba::AxiRespWidth + DataWidth + 1)
  ) br_tracker_reorder_buffer_flops_csr (
      .clk,
      .rst,
      .alloc_ready(csr_req_tag_ready),
      .alloc_valid(csr_req_tag_valid),
      .alloc_entry_id(csr_req_tag),
      .unordered_resp_push_valid(csr_resp_valid),
      .unordered_resp_push_entry_id(csr_resp_tag),
      .unordered_resp_push_data({csr_resp_resp, csr_resp_data, csr_resp_write}),
      .reordered_resp_pop_ready(reordered_csr_resp_ready),
      .reordered_resp_pop_valid(reordered_csr_resp_valid),
      .reordered_resp_pop_data({
        reordered_csr_resp_resp, reordered_csr_resp_data, reordered_csr_resp_write
      }),
      .resp_pending()
  );

  br_flow_join #(
      .NumFlows(2)
  ) br_flow_join_csr_req (
      .clk,
      .rst,
      .push_ready({csr_req_no_tag_ready, csr_req_tag_ready}),
      .push_valid({csr_req_no_tag_valid, csr_req_tag_valid}),
      .pop_ready (csr_req_ready),
      .pop_valid (csr_req_valid)
  );

  logic axil_bvalid_int;
  logic axil_bready_int;
  br_amba::axi_resp_t axil_bresp_int;
  logic [DataWidth-1:0] axil_bdata_unused;

  logic axil_rvalid_int;
  logic axil_rready_int;
  logic [DataWidth-1:0] axil_rdata_int;
  br_amba::axi_resp_t axil_rresp_int;

  br_flow_demux_select_unstable #(
      .NumFlows(2),
      .Width(br_amba::AxiRespWidth + DataWidth)
  ) br_flow_demux_select_unstable_resp (
      .clk,
      .rst,
      .select(reordered_csr_resp_write),
      .push_ready(reordered_csr_resp_ready),
      .push_valid(reordered_csr_resp_valid),
      .push_data({reordered_csr_resp_resp, reordered_csr_resp_data}),
      .pop_ready({axil_bready_int, axil_rready_int}),
      .pop_valid_unstable({axil_bvalid_int, axil_rvalid_int}),
      .pop_data_unstable({axil_bresp_int, axil_bdata_unused, axil_rresp_int, axil_rdata_int})
  );

  `BR_UNUSED(axil_bdata_unused)

  if (RegisterResponseOutputs) begin : gen_reg_resp_out
    br_flow_reg_fwd #(
        .Width(br_amba::AxiRespWidth)
    ) br_flow_reg_fwd_b (
        .clk,
        .rst,
        .push_ready(axil_bready_int),
        .push_valid(axil_bvalid_int),
        .push_data ({axil_bresp_int}),
        .pop_ready (axil_bready),
        .pop_valid (axil_bvalid),
        .pop_data  (axil_bresp)
    );

    br_flow_reg_fwd #(
        .Width(DataWidth + br_amba::AxiRespWidth)
    ) br_flow_reg_fwd_r (
        .clk,
        .rst,
        .push_ready(axil_rready_int),
        .push_valid(axil_rvalid_int),
        .push_data ({axil_rdata_int, axil_rresp_int}),
        .pop_ready (axil_rready),
        .pop_valid (axil_rvalid),
        .pop_data  ({axil_rdata, axil_rresp})
    );
  end else begin : gen_no_reg_resp_out
    assign axil_bvalid = axil_bvalid_int;
    assign axil_bready_int = axil_bready;
    assign axil_bresp = {axil_bresp_int};
    assign axil_rvalid = axil_rvalid_int;
    assign axil_rready_int = axil_rready;
    assign axil_rresp = {axil_rresp_int};
    assign axil_rdata = axil_rdata_int;
  end

endmodule
