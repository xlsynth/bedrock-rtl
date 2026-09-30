// SPDX-License-Identifier: Apache-2.0


// Elaboration coverage for canonical ready-valid flow declaration, binding, connect, and fire
// macros.
// Verible checks bind macros before expansion, so each affected instantiation needs one local
// module-port waiver immediately before its first port connection.

`include "br_flow.svh"
`include "br_asserts.svh"
`include "br_unused.svh"

module br_flow_test #(
    parameter int LogNumFlows = 2,
    parameter int NumFlows = 1 << LogNumFlows,
    localparam type br_flow_test_payload_t = logic [31:0]
) (
    input logic clk,
    input logic rst,

    input  logic                  scalar_push_valid_in,
    input  br_flow_test_payload_t scalar_push_data_in,
    output logic                  scalar_push_ready_out,
    input  logic                  scalar_pop_ready_in,
    output logic                  scalar_pop_valid_out,
    output br_flow_test_payload_t scalar_pop_data_out,
    output logic                  scalar_push_fire_out,

    input  logic [NumFlows-1:0]       vector_push_valid_in,
    input  logic [NumFlows-1:0][31:0] vector_push_data_in,
    output logic [NumFlows-1:0]       vector_push_ready_out,
    input  logic [NumFlows-1:0]       vector_pop_ready_in,
    output logic [NumFlows-1:0]       vector_pop_valid_out,
    output logic [NumFlows-1:0][31:0] vector_pop_data_out,
    output logic [NumFlows-1:0]       vector_push_fire_out,
    output logic                      vector_push_fire_index_out,

    input  logic [NumFlows-1:0]       struct_push_valid_in,
    input  logic [NumFlows-1:0][31:0] struct_push_data_in,
    output logic [NumFlows-1:0]       struct_push_ready_out,
    input  logic [NumFlows-1:0]       struct_pop_ready_in,
    output logic [NumFlows-1:0]       struct_pop_valid_out,
    output logic [NumFlows-1:0][31:0] struct_pop_data_out,

    input  logic                  unstable_scalar_push_valid_unstable_in,
    input  br_flow_test_payload_t unstable_scalar_push_data_unstable_in,
    output logic                  unstable_scalar_push_ready_out,
    input  logic                  unstable_scalar_pop_ready_in,
    output logic                  unstable_scalar_pop_valid_unstable_out,
    output br_flow_test_payload_t unstable_scalar_pop_data_unstable_out,
    output logic                  unstable_scalar_push_fire_out,

    input  logic [NumFlows-1:0]       unstable_vector_push_valid_unstable_in,
    input  logic [NumFlows-1:0][31:0] unstable_vector_push_data_unstable_in,
    output logic [NumFlows-1:0]       unstable_vector_push_ready_out,
    input  logic [NumFlows-1:0]       unstable_vector_pop_ready_in,
    output logic [NumFlows-1:0]       unstable_vector_pop_valid_unstable_out,
    output logic [NumFlows-1:0][31:0] unstable_vector_pop_data_unstable_out,
    output logic [NumFlows-1:0]       unstable_vector_push_fire_out,
    output logic                      unstable_vector_push_fire_index_out,

    input  logic [NumFlows-1:0]       unstable_struct_push_valid_unstable_in,
    input  logic [NumFlows-1:0][31:0] unstable_struct_push_data_unstable_in,
    output logic [NumFlows-1:0]       unstable_struct_push_ready_out,
    input  logic [NumFlows-1:0]       unstable_struct_pop_ready_in,
    output logic [NumFlows-1:0]       unstable_struct_pop_valid_unstable_out,
    output logic [NumFlows-1:0][31:0] unstable_struct_pop_data_unstable_out,

    input  logic control_scalar_push_valid_in,
    output logic control_scalar_push_ready_out,
    input  logic control_scalar_pop_ready_in,
    output logic control_scalar_pop_valid_unstable_out,

    input  logic [NumFlows-1:0] control_array_push_valid_in,
    output logic [NumFlows-1:0] control_array_push_ready_out,
    input  logic [NumFlows-1:0] control_array_pop_ready_in,
    output logic [NumFlows-1:0] control_array_pop_valid_unstable_out,

    input  logic control_connect_scalar_push_valid_in,
    output logic control_connect_scalar_push_ready_out,
    input  logic control_connect_scalar_pop_ready_in,
    output logic control_connect_scalar_pop_valid_out,

    input  logic [NumFlows-1:0] control_connect_array_push_valid_in,
    output logic [NumFlows-1:0] control_connect_array_push_ready_out,
    input  logic [NumFlows-1:0] control_connect_array_pop_ready_in,
    output logic [NumFlows-1:0] control_connect_array_pop_valid_out,

    input  logic unstable_control_connect_scalar_push_valid_unstable_in,
    output logic unstable_control_connect_scalar_push_ready_out,
    input  logic unstable_control_connect_scalar_pop_ready_in,
    output logic unstable_control_connect_scalar_pop_valid_unstable_out,

    input  logic [NumFlows-1:0] unstable_control_connect_array_push_valid_unstable_in,
    output logic [NumFlows-1:0] unstable_control_connect_array_push_ready_out,
    input  logic [NumFlows-1:0] unstable_control_connect_array_pop_ready_in,
    output logic [NumFlows-1:0] unstable_control_connect_array_pop_valid_unstable_out
);

  // Packed payload used to verify that one array index selects one complete payload.
  typedef struct packed {
    logic [7:0]  tag;
    logic [23:0] value;
  } br_flow_test_struct_payload_t;

  `BR_FLOW_DECLARE(scalar_push, br_flow_test_payload_t)
  `BR_FLOW_DECLARE(scalar_pop, br_flow_test_payload_t)
  `BR_FLOW_DECLARE(scalar_connect_sink, br_flow_test_payload_t)

  // The shift expression verifies that declaration macros group the flow count before `-1`.
  `BR_FLOW_DECLARE_ARRAY(vector_push, logic [31:0], 1 << LogNumFlows)
  `BR_FLOW_DECLARE_ARRAY(vector_pop, br_flow_test_payload_t, NumFlows)
  `BR_FLOW_DECLARE_ARRAY(vector_connect_sink, br_flow_test_payload_t, NumFlows)

  `BR_FLOW_DECLARE_ARRAY(struct_push, br_flow_test_struct_payload_t, NumFlows)
  `BR_FLOW_DECLARE_ARRAY(struct_pop, br_flow_test_struct_payload_t, NumFlows)
  `BR_FLOW_DECLARE_ARRAY(struct_index_sink, br_flow_test_struct_payload_t, NumFlows)
  `BR_FLOW_DECLARE_ARRAY(struct_connect_sink, br_flow_test_struct_payload_t, NumFlows)

  `BR_FLOW_DECLARE_UNSTABLE(unstable_scalar_push, br_flow_test_payload_t)
  `BR_FLOW_DECLARE_UNSTABLE(unstable_scalar_pop, br_flow_test_payload_t)
  `BR_FLOW_DECLARE_UNSTABLE(unstable_scalar_connect_sink, br_flow_test_payload_t)
  `BR_FLOW_DECLARE_UNSTABLE_ARRAY(unstable_scalar_fifo_push, br_flow_test_payload_t, 2)
  `BR_FLOW_DECLARE_ARRAY(unstable_scalar_fifo_pop, br_flow_test_payload_t, 2)
  `BR_FLOW_DECLARE_ARRAY(unstable_scalar_mux_push, br_flow_test_payload_t, 1)

  // This shift expression covers the unstable array declaration separately.
  `BR_FLOW_DECLARE_UNSTABLE_ARRAY(unstable_vector_push, logic [31:0], 1 << LogNumFlows)
  `BR_FLOW_DECLARE_UNSTABLE_ARRAY(unstable_vector_pop, br_flow_test_payload_t, NumFlows)
  `BR_FLOW_DECLARE_UNSTABLE_ARRAY(unstable_vector_connect_sink, br_flow_test_payload_t, NumFlows)
  `BR_FLOW_DECLARE_ARRAY(unstable_vector_fifo_pop, br_flow_test_payload_t, NumFlows)

  `BR_FLOW_DECLARE_UNSTABLE_ARRAY(unstable_struct_push, br_flow_test_struct_payload_t, NumFlows)
  `BR_FLOW_DECLARE_UNSTABLE_ARRAY(unstable_struct_pop, br_flow_test_struct_payload_t, NumFlows)
  `BR_FLOW_DECLARE_UNSTABLE_ARRAY(unstable_struct_index_sink, br_flow_test_struct_payload_t,
                                  NumFlows)
  `BR_FLOW_DECLARE_UNSTABLE_ARRAY(unstable_struct_connect_sink, br_flow_test_struct_payload_t,
                                  NumFlows)
  `BR_FLOW_DECLARE_ARRAY(unstable_struct_fifo_pop, br_flow_test_struct_payload_t, NumFlows)

  `BR_FLOW_CONTROL_DECLARE(control_scalar_push)
  `BR_FLOW_CONTROL_DECLARE_UNSTABLE(control_scalar_pop)
  `BR_FLOW_CONTROL_DECLARE_UNSTABLE_ARRAY(control_scalar_fork_pop, 1)

  `BR_FLOW_CONTROL_DECLARE_ARRAY(control_array_push, 1 << LogNumFlows)
  `BR_FLOW_CONTROL_DECLARE_UNSTABLE_ARRAY(control_array_pop, 1 << LogNumFlows)

  `BR_FLOW_CONTROL_DECLARE(control_connect_scalar_push)
  `BR_FLOW_CONTROL_DECLARE(control_connect_scalar_pop)

  `BR_FLOW_CONTROL_DECLARE_ARRAY(control_connect_array_bind_push, NumFlows)
  `BR_FLOW_CONTROL_DECLARE_ARRAY(control_connect_array_source, NumFlows)
  `BR_FLOW_CONTROL_DECLARE_ARRAY(control_connect_array_direct_sink, NumFlows)
  `BR_FLOW_CONTROL_DECLARE_ARRAY(control_connect_array_index_sink, NumFlows)
  `BR_FLOW_CONTROL_DECLARE_ARRAY(control_connect_array_sink, NumFlows)

  `BR_FLOW_CONTROL_DECLARE_UNSTABLE(unstable_control_connect_scalar_push)
  `BR_FLOW_CONTROL_DECLARE_UNSTABLE(unstable_control_connect_scalar_pop)

  `BR_FLOW_CONTROL_DECLARE_UNSTABLE_ARRAY(unstable_control_connect_array_bind_push, NumFlows)
  `BR_FLOW_CONTROL_DECLARE_UNSTABLE_ARRAY(unstable_control_connect_array_source, NumFlows)
  `BR_FLOW_CONTROL_DECLARE_UNSTABLE_ARRAY(unstable_control_connect_array_direct_sink, NumFlows)
  `BR_FLOW_CONTROL_DECLARE_UNSTABLE_ARRAY(unstable_control_connect_array_index_sink, NumFlows)
  `BR_FLOW_CONTROL_DECLARE_UNSTABLE_ARRAY(unstable_control_connect_array_sink, NumFlows)

  `BR_ASSERT_STATIC(num_flows_supports_shared_fifo_a, NumFlows >= 2)
  `BR_ASSERT_STATIC(vector_push_ready_width_a, $bits(vector_push_ready) == NumFlows)
  `BR_ASSERT_STATIC(vector_push_valid_width_a, $bits(vector_push_valid) == NumFlows)
  `BR_ASSERT_STATIC(vector_push_data_width_a, $bits(vector_push_data) == (NumFlows * 32))
  `BR_ASSERT_STATIC(control_array_push_ready_width_a, $bits(control_array_push_ready) == NumFlows)
  `BR_ASSERT_STATIC(control_array_push_valid_width_a, $bits(control_array_push_valid) == NumFlows)
  `BR_ASSERT_STATIC(control_array_pop_ready_width_a, $bits(control_array_pop_ready) == NumFlows)
  `BR_ASSERT_STATIC(control_array_pop_valid_width_a, $bits(control_array_pop_valid_unstable)
                    == NumFlows)
  `BR_ASSERT_STATIC(unstable_scalar_ready_width_a, $bits(unstable_scalar_push_ready) == 1)
  `BR_ASSERT_STATIC(unstable_scalar_valid_width_a, $bits(unstable_scalar_push_valid_unstable) == 1)
  `BR_ASSERT_STATIC(unstable_scalar_data_width_a, $bits(unstable_scalar_push_data_unstable)
                    == $bits(br_flow_test_payload_t))
  `BR_ASSERT_STATIC(unstable_vector_ready_width_a, $bits(unstable_vector_push_ready) == NumFlows)
  `BR_ASSERT_STATIC(unstable_vector_valid_width_a, $bits(unstable_vector_push_valid_unstable)
                    == NumFlows)
  `BR_ASSERT_STATIC(unstable_vector_data_width_a, $bits(unstable_vector_push_data_unstable)
                    == (NumFlows * 32))
  `BR_ASSERT_STATIC(unstable_vector_data_lane_width_a, $bits(unstable_vector_push_data_unstable[0])
                    == 32)
  `BR_ASSERT_STATIC(unstable_struct_ready_width_a, $bits(unstable_struct_push_ready) == NumFlows)
  `BR_ASSERT_STATIC(unstable_struct_valid_width_a, $bits(unstable_struct_push_valid_unstable)
                    == NumFlows)
  `BR_ASSERT_STATIC(unstable_struct_data_width_a, $bits(unstable_struct_push_data_unstable)
                    == (NumFlows * $bits(br_flow_test_struct_payload_t)))
  `BR_ASSERT_STATIC(unstable_struct_data_lane_width_a, $bits(unstable_struct_push_data_unstable[0])
                    == $bits(br_flow_test_struct_payload_t))
  `BR_ASSERT_STATIC(scalar_fire_width_a, $bits(`BR_FLOW_FIRE(scalar_push)) == 1)
  `BR_ASSERT_STATIC(vector_fire_width_a, $bits(`BR_FLOW_FIRE(vector_push)) == NumFlows)
  `BR_ASSERT_STATIC(vector_fire_index_width_a, $bits
                    (`BR_FLOW_FIRE_INDEX(vector_push, NumFlows - 1)) == 1)
  `BR_ASSERT_STATIC(unstable_scalar_fire_width_a, $bits
                    (`BR_FLOW_FIRE_UNSTABLE(unstable_scalar_push)) == 1)
  `BR_ASSERT_STATIC(unstable_vector_fire_width_a, $bits
                    (`BR_FLOW_FIRE_UNSTABLE(unstable_vector_push)) == NumFlows)
  `BR_ASSERT_STATIC(unstable_vector_fire_index_width_a, $bits
                    (`BR_FLOW_FIRE_UNSTABLE_INDEX(unstable_vector_push, NumFlows - 1)) == 1)

  assign scalar_push_valid = scalar_push_valid_in;
  assign scalar_push_data = scalar_push_data_in;
  assign scalar_push_ready_out = scalar_push_ready;
  assign scalar_push_fire_out = `BR_FLOW_FIRE(scalar_push);
  assign scalar_connect_sink_ready = scalar_pop_ready_in;
  assign scalar_pop_valid_out = scalar_connect_sink_valid;
  assign scalar_pop_data_out = scalar_connect_sink_data;
  `BR_FLOW_CONNECT(scalar_pop, scalar_connect_sink)

  assign vector_push_valid = vector_push_valid_in;
  assign vector_push_data = vector_push_data_in;
  assign vector_push_ready_out = vector_push_ready;
  assign vector_push_fire_out = `BR_FLOW_FIRE(vector_push);
  assign vector_push_fire_index_out = `BR_FLOW_FIRE_INDEX(vector_push, NumFlows - 1);
  assign vector_connect_sink_ready = vector_pop_ready_in;
  assign vector_pop_valid_out = vector_connect_sink_valid;
  assign vector_pop_data_out = vector_connect_sink_data;
  `BR_FLOW_CONNECT(vector_pop, vector_connect_sink)

  assign struct_push_valid = struct_push_valid_in;
  assign struct_push_data = struct_push_data_in;
  assign struct_push_ready_out = struct_push_ready;
  assign struct_connect_sink_ready = struct_pop_ready_in;
  assign struct_pop_valid_out = struct_connect_sink_valid;
  assign struct_pop_data_out = struct_connect_sink_data;

  assign unstable_scalar_push_valid_unstable = unstable_scalar_push_valid_unstable_in;
  assign unstable_scalar_push_data_unstable = unstable_scalar_push_data_unstable_in;
  assign unstable_scalar_push_ready_out = unstable_scalar_push_ready;
  assign unstable_scalar_push_fire_out = `BR_FLOW_FIRE_UNSTABLE(unstable_scalar_push);
  assign unstable_scalar_connect_sink_ready = unstable_scalar_pop_ready_in;
  assign unstable_scalar_pop_valid_unstable_out = unstable_scalar_connect_sink_valid_unstable;
  assign unstable_scalar_pop_data_unstable_out = unstable_scalar_connect_sink_data_unstable;
  `BR_FLOW_CONNECT_UNSTABLE(unstable_scalar_pop, unstable_scalar_connect_sink)

  assign unstable_vector_push_valid_unstable = unstable_vector_push_valid_unstable_in;
  assign unstable_vector_push_data_unstable = unstable_vector_push_data_unstable_in;
  assign unstable_vector_push_ready_out = unstable_vector_push_ready;
  assign unstable_vector_push_fire_out = `BR_FLOW_FIRE_UNSTABLE(unstable_vector_push);
  assign unstable_vector_push_fire_index_out = `BR_FLOW_FIRE_UNSTABLE_INDEX(
          unstable_vector_push, NumFlows - 1);
  assign unstable_vector_connect_sink_ready = unstable_vector_pop_ready_in;
  assign unstable_vector_pop_valid_unstable_out = unstable_vector_connect_sink_valid_unstable;
  assign unstable_vector_pop_data_unstable_out = unstable_vector_connect_sink_data_unstable;
  `BR_FLOW_CONNECT_UNSTABLE(unstable_vector_pop, unstable_vector_connect_sink)

  assign unstable_struct_push_valid_unstable = unstable_struct_push_valid_unstable_in;
  assign unstable_struct_push_data_unstable = unstable_struct_push_data_unstable_in;
  assign unstable_struct_push_ready_out = unstable_struct_push_ready;
  assign unstable_struct_connect_sink_ready = unstable_struct_pop_ready_in;
  assign unstable_struct_pop_valid_unstable_out = unstable_struct_connect_sink_valid_unstable;
  assign unstable_struct_pop_data_unstable_out = unstable_struct_connect_sink_data_unstable;

  assign control_scalar_push_valid = control_scalar_push_valid_in;
  assign control_scalar_push_ready_out = control_scalar_push_ready;
  assign control_scalar_pop_ready = control_scalar_pop_ready_in;
  assign control_scalar_pop_valid_unstable_out = control_scalar_pop_valid_unstable;

  assign control_array_push_valid = control_array_push_valid_in;
  assign control_array_push_ready_out = control_array_push_ready;
  assign control_array_pop_ready = control_array_pop_ready_in;
  assign control_array_pop_valid_unstable_out = control_array_pop_valid_unstable;

  assign control_connect_scalar_push_valid = control_connect_scalar_push_valid_in;
  assign control_connect_scalar_push_ready_out = control_connect_scalar_push_ready;
  assign control_connect_scalar_pop_ready = control_connect_scalar_pop_ready_in;
  assign control_connect_scalar_pop_valid_out = control_connect_scalar_pop_valid;
  `BR_FLOW_CONTROL_CONNECT(control_connect_scalar_push, control_connect_scalar_pop)

  assign control_connect_array_bind_push_valid = control_connect_array_push_valid_in;
  assign control_connect_array_push_ready_out = control_connect_array_bind_push_ready;
  assign control_connect_array_sink_ready = control_connect_array_pop_ready_in;
  assign control_connect_array_pop_valid_out = control_connect_array_sink_valid;
  `BR_FLOW_CONTROL_CONNECT(control_connect_array_source, control_connect_array_direct_sink)

  assign unstable_control_connect_scalar_push_valid_unstable =
      unstable_control_connect_scalar_push_valid_unstable_in;
  assign unstable_control_connect_scalar_push_ready_out =
      unstable_control_connect_scalar_push_ready;
  assign unstable_control_connect_scalar_pop_ready = unstable_control_connect_scalar_pop_ready_in;
  assign unstable_control_connect_scalar_pop_valid_unstable_out =
      unstable_control_connect_scalar_pop_valid_unstable;
  `BR_FLOW_CONTROL_CONNECT_UNSTABLE(unstable_control_connect_scalar_push,
                                    unstable_control_connect_scalar_pop)

  assign unstable_control_connect_array_bind_push_valid_unstable =
      unstable_control_connect_array_push_valid_unstable_in;
  assign unstable_control_connect_array_push_ready_out =
      unstable_control_connect_array_bind_push_ready;
  assign unstable_control_connect_array_sink_ready = unstable_control_connect_array_pop_ready_in;
  assign unstable_control_connect_array_pop_valid_unstable_out =
      unstable_control_connect_array_sink_valid_unstable;
  `BR_FLOW_CONTROL_CONNECT_UNSTABLE(unstable_control_connect_array_source,
                                    unstable_control_connect_array_direct_sink)

  // The first bind needs a caller-supplied comma; the last bind must not emit one.
  br_flow_reg_none #(
      .Width($bits(br_flow_test_payload_t))
  ) u_scalar_endpoint (
      // verilog_lint: waive module-port
      .clk,
      .rst,
      `BR_FLOW_BIND(push, scalar_push),
      `BR_FLOW_BIND(pop, scalar_pop)
  );

  // Inline packed-vector payload syntax and complete packed-array binding elaborate together.
  br_flow_xbar_fixed #(
      .NumPushFlows(NumFlows),
      .NumPopFlows(NumFlows),
      .Width($bits(br_flow_test_payload_t)),
      .RegisterPopOutputs(1'b1)
  ) u_array_endpoint (
      // verilog_lint: waive module-port
      .clk,
      .rst,
      `BR_FLOW_BIND(push, vector_push),
      .push_dest_id('0),
      `BR_FLOW_BIND(pop, vector_pop)
  );

  // Reversed lanes exercise indexed binding and connection with an arithmetic expression.
  for (genvar i = 0; i < NumFlows; i++) begin : gen_struct_endpoints
    `BR_FLOW_DECLARE(struct_scalar_bridge, br_flow_test_struct_payload_t)

    br_flow_reg_none #(
        .Width($bits(br_flow_test_struct_payload_t))
    ) u_struct_endpoint (
        // verilog_lint: waive module-port
        .clk,
        .rst,
        `BR_FLOW_BIND_INDEX(push, struct_push, NumFlows - 1 - i),
        `BR_FLOW_BIND_INDEX(pop, struct_pop, NumFlows - 1 - i)
    );
    `BR_FLOW_CONNECT_INDEX(struct_pop, NumFlows - 1 - i, struct_index_sink, i)
    `BR_FLOW_CONNECT_FROM_INDEX(struct_index_sink, i, struct_scalar_bridge)
    `BR_FLOW_CONNECT_TO_INDEX(struct_scalar_bridge, struct_connect_sink, NumFlows - 1 - i)
  end

  // A real FIFO bypass accepts the unstable scalar source in lane zero and stabilizes it.
  `BR_FLOW_CONNECT_UNSTABLE_TO_INDEX(unstable_scalar_push, unstable_scalar_fifo_push, 0)
  assign unstable_scalar_fifo_push_valid_unstable[1] = 1'b0;
  assign unstable_scalar_fifo_push_data_unstable[1]  = '0;

  br_fifo_shared_pop_ctrl #(
      .NumReadPorts(1),
      .NumFifos(2),
      .Depth(5),
      .Width($bits(br_flow_test_payload_t)),
      .StagingBufferDepth(1),
      .RegisterPopOutputs(1'b1),
      .EnableBypass(1'b1),
      .RamReadLatency(0)
  ) u_unstable_scalar_stabilizer (
      // verilog_lint: waive module-port
      .clk,
      .rst,
      .head_valid('0),
      .head_ready(),
      .head('0),
      .ram_empty('1),
      .ram_items('0),
      `BR_FLOW_BIND_UNSTABLE(bypass, unstable_scalar_fifo_push),
      `BR_FLOW_BIND(pop, unstable_scalar_fifo_pop),
      .pop_empty(),
      .dealloc_valid(),
      .dealloc_entry_id(),
      .data_ram_rd_addr_valid(),
      .data_ram_rd_addr(),
      .data_ram_rd_data_valid('0),
      .data_ram_rd_data('0)
  );
  assign unstable_scalar_fifo_pop_ready[1] = 1'b1;
  `BR_UNUSED_NAMED(unstable_scalar_fifo_unused_lane, {unstable_scalar_fifo_push_ready[1],
                                                      unstable_scalar_fifo_pop_valid[1],
                                                      unstable_scalar_fifo_pop_data[1]})
  `BR_FLOW_CONNECT_INDEX(unstable_scalar_fifo_pop, 0, unstable_scalar_mux_push, 0)

  br_flow_mux_select_unstable #(
      .NumFlows(1),
      .Width($bits(br_flow_test_payload_t))
  ) u_unstable_scalar_endpoint (
      // verilog_lint: waive module-port
      .clk,
      .rst,
      .select('0),
      `BR_FLOW_BIND(push, unstable_scalar_mux_push),
      `BR_FLOW_BIND_UNSTABLE(pop, unstable_scalar_pop)
  );

  // The shared FIFO's bypass ports are a real packed unstable-input interface.
  br_fifo_shared_pop_ctrl #(
      .NumReadPorts(1),
      .NumFifos(NumFlows),
      .Depth(5),
      .Width($bits(br_flow_test_payload_t)),
      .StagingBufferDepth(1),
      .RegisterPopOutputs(1'b1),
      .EnableBypass(1'b1),
      .RamReadLatency(0)
  ) u_unstable_vector_endpoint (
      // verilog_lint: waive module-port
      .clk,
      .rst,
      .head_valid('0),
      .head_ready(),
      .head('0),
      .ram_empty('1),
      .ram_items('0),
      `BR_FLOW_BIND_UNSTABLE(bypass, unstable_vector_push),
      `BR_FLOW_BIND(pop, unstable_vector_fifo_pop),
      .pop_empty(),
      .dealloc_valid(),
      .dealloc_entry_id(),
      .data_ram_rd_addr_valid(),
      .data_ram_rd_addr(),
      .data_ram_rd_data_valid('0),
      .data_ram_rd_data('0)
  );

  for (genvar i = 0; i < NumFlows; i++) begin : gen_unstable_vector_endpoints
    // The declaration macro's element typedef intentionally follows the generated lane's scope.
    // ri lint_check_waive GENERATE_TYPEDEF
    `BR_FLOW_DECLARE_ARRAY(unstable_vector_mux_push, br_flow_test_payload_t, 1)

    `BR_FLOW_CONNECT_INDEX(unstable_vector_fifo_pop, i, unstable_vector_mux_push, 0)
    br_flow_mux_select_unstable #(
        .NumFlows(1),
        .Width($bits(br_flow_test_payload_t))
    ) u_unstable_vector_lane_endpoint (
        // verilog_lint: waive module-port
        .clk,
        .rst,
        .select('0),
        `BR_FLOW_BIND(push, unstable_vector_mux_push),
        `BR_FLOW_BIND_UNSTABLE_INDEX(pop, unstable_vector_pop, i)
    );
  end

  // A second FIFO bypass verifies whole-array binding with a packed-struct payload.
  br_fifo_shared_pop_ctrl #(
      .NumReadPorts(1),
      .NumFifos(NumFlows),
      .Depth(5),
      .Width($bits(br_flow_test_struct_payload_t)),
      .StagingBufferDepth(1),
      .RegisterPopOutputs(1'b1),
      .EnableBypass(1'b1),
      .RamReadLatency(0)
  ) u_unstable_struct_stabilizer (
      // verilog_lint: waive module-port
      .clk,
      .rst,
      .head_valid('0),
      .head_ready(),
      .head('0),
      .ram_empty('1),
      .ram_items('0),
      `BR_FLOW_BIND_UNSTABLE(bypass, unstable_struct_push),
      `BR_FLOW_BIND(pop, unstable_struct_fifo_pop),
      .pop_empty(),
      .dealloc_valid(),
      .dealloc_entry_id(),
      .data_ram_rd_addr_valid(),
      .data_ram_rd_addr(),
      .data_ram_rd_data_valid('0),
      .data_ram_rd_data('0)
  );

  // Reversed lanes verify indexed binding and connection of an unstable packed-struct payload.
  for (genvar i = 0; i < NumFlows; i++) begin : gen_unstable_struct_endpoints
    // The declaration macro's element typedef intentionally follows the generated lane's scope.
    // ri lint_check_waive GENERATE_TYPEDEF
    `BR_FLOW_DECLARE_ARRAY(unstable_struct_mux_push, br_flow_test_struct_payload_t, 1)
    `BR_FLOW_DECLARE_UNSTABLE(unstable_struct_scalar_bridge, br_flow_test_struct_payload_t)

    `BR_FLOW_CONNECT_INDEX(unstable_struct_fifo_pop, NumFlows - 1 - i, unstable_struct_mux_push, 0)

    br_flow_mux_select_unstable #(
        .NumFlows(1),
        .Width($bits(br_flow_test_struct_payload_t))
    ) u_unstable_struct_endpoint (
        // verilog_lint: waive module-port
        .clk,
        .rst,
        .select('0),
        `BR_FLOW_BIND(push, unstable_struct_mux_push),
        `BR_FLOW_BIND_UNSTABLE_INDEX(pop, unstable_struct_pop, NumFlows - 1 - i)
    );
    `BR_FLOW_CONNECT_UNSTABLE_INDEX(unstable_struct_pop, NumFlows - 1 - i,
                                    unstable_struct_index_sink, i)
    `BR_FLOW_CONNECT_UNSTABLE_FROM_INDEX(unstable_struct_index_sink, i,
                                         unstable_struct_scalar_bridge)
    `BR_FLOW_CONNECT_UNSTABLE_TO_INDEX(unstable_struct_scalar_bridge, unstable_struct_connect_sink,
                                       NumFlows - 1 - i)
  end

  // Stable control connections exercise whole-array, indexed, array-to-scalar, and
  // scalar-to-array forms while indexed binding reverses lanes at the endpoint.
  for (genvar i = 0; i < NumFlows; i++) begin : gen_control_connect_endpoints
    `BR_FLOW_CONTROL_DECLARE_ARRAY(control_connect_join_push, 1)
    `BR_FLOW_CONTROL_DECLARE(control_connect_scalar_bridge)

    `BR_FLOW_CONTROL_CONNECT_INDEX(control_connect_array_bind_push, NumFlows - 1 - i,
                                   control_connect_join_push, 0)
    br_flow_join #(
        .NumFlows(1)
    ) u_control_stable_endpoint (
        // verilog_lint: waive module-port
        .clk,
        .rst,
        `BR_FLOW_CONTROL_BIND(push, control_connect_join_push),
        `BR_FLOW_CONTROL_BIND_INDEX(pop, control_connect_array_source, NumFlows - 1 - i)
    );
    `BR_FLOW_CONTROL_CONNECT_INDEX(control_connect_array_direct_sink, NumFlows - 1 - i,
                                   control_connect_array_index_sink, i)
    `BR_FLOW_CONTROL_CONNECT_FROM_INDEX(control_connect_array_index_sink, i,
                                        control_connect_scalar_bridge)
    `BR_FLOW_CONTROL_CONNECT_TO_INDEX(control_connect_scalar_bridge, control_connect_array_sink,
                                      NumFlows - 1 - i)
  end

  // The arbiter permits unstable requests and preserves that contract at its pop interface.
  for (genvar i = 0; i < NumFlows; i++) begin : gen_unstable_control_connect_endpoints
    `BR_FLOW_CONTROL_DECLARE_ARRAY(unstable_control_connect_arb_push, 1)
    `BR_FLOW_CONTROL_DECLARE_UNSTABLE(unstable_control_connect_scalar_bridge)

    assign unstable_control_connect_array_bind_push_ready[NumFlows-1-i] =
        unstable_control_connect_arb_push_ready[0];
    assign unstable_control_connect_arb_push_valid[0] =
        unstable_control_connect_array_bind_push_valid_unstable[NumFlows-1-i];

    br_flow_arb_fixed #(
        .NumFlows(1),
        .EnableAssertPushValidStability(1'b0)
    ) u_control_unstable_endpoint (
        // verilog_lint: waive module-port
        .clk,
        .rst,
        `BR_FLOW_CONTROL_BIND(push, unstable_control_connect_arb_push),
        `BR_FLOW_CONTROL_BIND_UNSTABLE_INDEX(pop, unstable_control_connect_array_source,
                                             NumFlows - 1 - i)
    );
    `BR_FLOW_CONTROL_CONNECT_UNSTABLE_INDEX(unstable_control_connect_array_direct_sink,
                                            NumFlows - 1 - i,
                                            unstable_control_connect_array_index_sink, i)
    `BR_FLOW_CONTROL_CONNECT_UNSTABLE_FROM_INDEX(unstable_control_connect_array_index_sink, i,
                                                 unstable_control_connect_scalar_bridge)
    `BR_FLOW_CONTROL_CONNECT_UNSTABLE_TO_INDEX(unstable_control_connect_scalar_bridge,
                                               unstable_control_connect_array_sink,
                                               NumFlows - 1 - i)
  end

  // A real fork provides the scalar stable-input and packed unstable-output control ports.
  br_flow_fork #(
      .NumFlows(1)
  ) u_control_scalar_endpoint (
      // verilog_lint: waive module-port
      .clk,
      .rst,
      `BR_FLOW_CONTROL_BIND(push, control_scalar_push),
      `BR_FLOW_CONTROL_BIND_UNSTABLE(pop, control_scalar_fork_pop)
  );
  `BR_FLOW_CONTROL_CONNECT_UNSTABLE_FROM_INDEX(control_scalar_fork_pop, 0, control_scalar_pop)

  // A valve has complete packed stable-input and unstable-output control arrays.
  br_flow_valve #(
      .NumFlows(NumFlows)
  ) u_control_array_endpoint (
      // verilog_lint: waive module-port
      .clk,
      .rst,
      .en('1),
      `BR_FLOW_CONTROL_BIND(push, control_array_push),
      `BR_FLOW_CONTROL_BIND_UNSTABLE(pop, control_array_pop)
  );

endmodule : br_flow_test
