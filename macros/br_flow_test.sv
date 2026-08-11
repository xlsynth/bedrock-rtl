// SPDX-License-Identifier: Apache-2.0


// Elaboration coverage for ready-valid flow declaration and direct-connection macros.

`include "br_flow.svh"
`include "br_asserts.svh"

module br_flow_test #(
    parameter int LogNumFlows = 2,
    localparam int NumFlows = 1 << LogNumFlows,
    localparam type payload_t = logic [31:0]
) (
    input  logic        stimulus,
    input  logic [31:0] payload_in,
    output logic        observed
);

  // Packed payload verifies that one array index selects one complete payload.
  typedef struct packed {
    logic [7:0]  tag;
    logic [23:0] value;
  } struct_payload_t;

  localparam int PayloadWidth = $bits(payload_t);
  localparam int StructPayloadWidth = $bits(struct_payload_t);

  `BR_ASSERT_STATIC(log_num_flows_must_be_nonnegative_a, LogNumFlows >= 0)

  //------------------------------------------
  // Stable data flows
  //------------------------------------------
  `BR_FLOW_DECLARE(stable_scalar_source, payload_t)
  `BR_FLOW_DECLARE(stable_scalar_sink, payload_t)

  // The shift expression verifies that declaration macros group the flow count before `-1`.
  `BR_FLOW_DECLARE_ARRAY(stable_array_source, logic [31:0], 1 << LogNumFlows)
  `BR_FLOW_DECLARE_ARRAY(stable_array_sink, payload_t, NumFlows)

  `BR_FLOW_DECLARE_ARRAY(stable_from_source, struct_payload_t, 1)
  `BR_FLOW_DECLARE(stable_from_sink, struct_payload_t)

  `BR_FLOW_DECLARE(stable_to_source, struct_payload_t)
  `BR_FLOW_DECLARE_ARRAY(stable_to_sink, struct_payload_t, 1)

  `BR_FLOW_DECLARE_ARRAY(stable_index_source, struct_payload_t, NumFlows)
  `BR_FLOW_DECLARE_ARRAY(stable_index_sink, struct_payload_t, NumFlows)

  assign stable_scalar_source_valid = stimulus;
  assign stable_scalar_source_data  = payload_in;
  assign stable_scalar_sink_ready   = stimulus;
  `BR_FLOW_CONNECT(stable_scalar_source, stable_scalar_sink)

  assign stable_array_source_valid = {NumFlows{stimulus}};
  assign stable_array_source_data  = {NumFlows{payload_in}};
  assign stable_array_sink_ready   = {NumFlows{stimulus}};
  `BR_FLOW_CONNECT(stable_array_source, stable_array_sink)

  assign stable_from_source_valid = stimulus;
  assign stable_from_source_data  = payload_in;
  assign stable_from_sink_ready   = stimulus;
  `BR_FLOW_CONNECT_FROM_INDEX(stable_from_source, 0, stable_from_sink)

  assign stable_to_source_valid = stimulus;
  assign stable_to_source_data  = payload_in;
  assign stable_to_sink_ready   = stimulus;
  `BR_FLOW_CONNECT_TO_INDEX(stable_to_source, stable_to_sink, 0)

  assign stable_index_source_valid = {NumFlows{stimulus}};
  assign stable_index_source_data  = {NumFlows{payload_in}};
  assign stable_index_sink_ready   = {NumFlows{stimulus}};
  for (genvar i = 0; i < NumFlows; i++) begin : gen_stable_data_index
    `BR_FLOW_CONNECT_INDEX(stable_index_source, i, stable_index_sink, NumFlows - 1 - i)
  end

  `BR_ASSERT_STATIC(stable_array_ready_width_a, $bits(stable_array_source_ready) == NumFlows)
  `BR_ASSERT_STATIC(stable_array_data_width_a, $bits(stable_array_source_data)
                    == (NumFlows * PayloadWidth))
  `BR_ASSERT_STATIC(stable_array_element_width_a, $bits(stable_array_source_data[0])
                    == PayloadWidth)
  `BR_ASSERT_STATIC(stable_struct_element_width_a, $bits(stable_index_source_data[0])
                    == StructPayloadWidth)

  //------------------------------------------
  // Unstable data flows
  //------------------------------------------
  `BR_FLOW_DECLARE_UNSTABLE(unstable_scalar_source, payload_t)
  `BR_FLOW_DECLARE_UNSTABLE(unstable_scalar_sink, payload_t)

  `BR_FLOW_DECLARE_UNSTABLE_ARRAY(unstable_array_source, logic [31:0], 1 << LogNumFlows)
  `BR_FLOW_DECLARE_UNSTABLE_ARRAY(unstable_array_sink, payload_t, NumFlows)

  `BR_FLOW_DECLARE_UNSTABLE_ARRAY(unstable_from_source, struct_payload_t, 1)
  `BR_FLOW_DECLARE_UNSTABLE(unstable_from_sink, struct_payload_t)

  `BR_FLOW_DECLARE_UNSTABLE(unstable_to_source, struct_payload_t)
  `BR_FLOW_DECLARE_UNSTABLE_ARRAY(unstable_to_sink, struct_payload_t, 1)

  `BR_FLOW_DECLARE_UNSTABLE_ARRAY(unstable_index_source, struct_payload_t, NumFlows)
  `BR_FLOW_DECLARE_UNSTABLE_ARRAY(unstable_index_sink, struct_payload_t, NumFlows)

  assign unstable_scalar_source_valid_unstable = stimulus;
  assign unstable_scalar_source_data_unstable = payload_in;
  assign unstable_scalar_sink_ready = stimulus;
  `BR_FLOW_CONNECT_UNSTABLE(unstable_scalar_source, unstable_scalar_sink)

  assign unstable_array_source_valid_unstable = {NumFlows{stimulus}};
  assign unstable_array_source_data_unstable = {NumFlows{payload_in}};
  assign unstable_array_sink_ready = {NumFlows{stimulus}};
  `BR_FLOW_CONNECT_UNSTABLE(unstable_array_source, unstable_array_sink)

  assign unstable_from_source_valid_unstable = stimulus;
  assign unstable_from_source_data_unstable = payload_in;
  assign unstable_from_sink_ready = stimulus;
  `BR_FLOW_CONNECT_UNSTABLE_FROM_INDEX(unstable_from_source, 0, unstable_from_sink)

  assign unstable_to_source_valid_unstable = stimulus;
  assign unstable_to_source_data_unstable = payload_in;
  assign unstable_to_sink_ready = stimulus;
  `BR_FLOW_CONNECT_UNSTABLE_TO_INDEX(unstable_to_source, unstable_to_sink, 0)

  assign unstable_index_source_valid_unstable = {NumFlows{stimulus}};
  assign unstable_index_source_data_unstable = {NumFlows{payload_in}};
  assign unstable_index_sink_ready = {NumFlows{stimulus}};
  for (genvar i = 0; i < NumFlows; i++) begin : gen_unstable_data_index
    `BR_FLOW_CONNECT_UNSTABLE_INDEX(unstable_index_source, i, unstable_index_sink, NumFlows - 1 - i)
  end

  `BR_ASSERT_STATIC(unstable_array_ready_width_a, $bits(unstable_array_source_ready) == NumFlows)
  `BR_ASSERT_STATIC(unstable_array_data_width_a, $bits(unstable_array_source_data_unstable)
                    == (NumFlows * PayloadWidth))
  `BR_ASSERT_STATIC(unstable_array_element_width_a, $bits(unstable_array_source_data_unstable[0])
                    == PayloadWidth)
  `BR_ASSERT_STATIC(unstable_struct_element_width_a, $bits(unstable_index_source_data_unstable[0])
                    == StructPayloadWidth)

  //------------------------------------------
  // Stable control flows
  //------------------------------------------
  `BR_FLOW_CONTROL_DECLARE(control_scalar_source)
  `BR_FLOW_CONTROL_DECLARE(control_scalar_sink)

  `BR_FLOW_CONTROL_DECLARE_ARRAY(control_array_source, 1 << LogNumFlows)
  `BR_FLOW_CONTROL_DECLARE_ARRAY(control_array_sink, NumFlows)

  `BR_FLOW_CONTROL_DECLARE_ARRAY(control_from_source, 1)
  `BR_FLOW_CONTROL_DECLARE(control_from_sink)

  `BR_FLOW_CONTROL_DECLARE(control_to_source)
  `BR_FLOW_CONTROL_DECLARE_ARRAY(control_to_sink, 1)

  `BR_FLOW_CONTROL_DECLARE_ARRAY(control_index_source, NumFlows)
  `BR_FLOW_CONTROL_DECLARE_ARRAY(control_index_sink, NumFlows)

  assign control_scalar_source_valid = stimulus;
  assign control_scalar_sink_ready   = stimulus;
  `BR_FLOW_CONTROL_CONNECT(control_scalar_source, control_scalar_sink)

  assign control_array_source_valid = {NumFlows{stimulus}};
  assign control_array_sink_ready   = {NumFlows{stimulus}};
  `BR_FLOW_CONTROL_CONNECT(control_array_source, control_array_sink)

  assign control_from_source_valid = stimulus;
  assign control_from_sink_ready   = stimulus;
  `BR_FLOW_CONTROL_CONNECT_FROM_INDEX(control_from_source, 0, control_from_sink)

  assign control_to_source_valid = stimulus;
  assign control_to_sink_ready   = stimulus;
  `BR_FLOW_CONTROL_CONNECT_TO_INDEX(control_to_source, control_to_sink, 0)

  assign control_index_source_valid = {NumFlows{stimulus}};
  assign control_index_sink_ready   = {NumFlows{stimulus}};
  for (genvar i = 0; i < NumFlows; i++) begin : gen_stable_control_index
    `BR_FLOW_CONTROL_CONNECT_INDEX(control_index_source, i, control_index_sink, NumFlows - 1 - i)
  end

  `BR_ASSERT_STATIC(control_array_width_a, $bits(control_array_source_ready) == NumFlows)

  //------------------------------------------
  // Unstable control flows
  //------------------------------------------
  `BR_FLOW_CONTROL_DECLARE_UNSTABLE(unstable_control_scalar_source)
  `BR_FLOW_CONTROL_DECLARE_UNSTABLE(unstable_control_scalar_sink)

  `BR_FLOW_CONTROL_DECLARE_UNSTABLE_ARRAY(unstable_control_array_source, 1 << LogNumFlows)
  `BR_FLOW_CONTROL_DECLARE_UNSTABLE_ARRAY(unstable_control_array_sink, NumFlows)

  `BR_FLOW_CONTROL_DECLARE_UNSTABLE_ARRAY(unstable_control_from_source, 1)
  `BR_FLOW_CONTROL_DECLARE_UNSTABLE(unstable_control_from_sink)

  `BR_FLOW_CONTROL_DECLARE_UNSTABLE(unstable_control_to_source)
  `BR_FLOW_CONTROL_DECLARE_UNSTABLE_ARRAY(unstable_control_to_sink, 1)

  `BR_FLOW_CONTROL_DECLARE_UNSTABLE_ARRAY(unstable_control_index_source, NumFlows)
  `BR_FLOW_CONTROL_DECLARE_UNSTABLE_ARRAY(unstable_control_index_sink, NumFlows)

  assign unstable_control_scalar_source_valid_unstable = stimulus;
  assign unstable_control_scalar_sink_ready = stimulus;
  `BR_FLOW_CONTROL_CONNECT_UNSTABLE(unstable_control_scalar_source, unstable_control_scalar_sink)

  assign unstable_control_array_source_valid_unstable = {NumFlows{stimulus}};
  assign unstable_control_array_sink_ready = {NumFlows{stimulus}};
  `BR_FLOW_CONTROL_CONNECT_UNSTABLE(unstable_control_array_source, unstable_control_array_sink)

  assign unstable_control_from_source_valid_unstable = stimulus;
  assign unstable_control_from_sink_ready = stimulus;
  `BR_FLOW_CONTROL_CONNECT_UNSTABLE_FROM_INDEX(unstable_control_from_source, 0,
                                               unstable_control_from_sink)

  assign unstable_control_to_source_valid_unstable = stimulus;
  assign unstable_control_to_sink_ready = stimulus;
  `BR_FLOW_CONTROL_CONNECT_UNSTABLE_TO_INDEX(unstable_control_to_source, unstable_control_to_sink,
                                             0)

  assign unstable_control_index_source_valid_unstable = {NumFlows{stimulus}};
  assign unstable_control_index_sink_ready = {NumFlows{stimulus}};
  for (genvar i = 0; i < NumFlows; i++) begin : gen_unstable_control_index
    `BR_FLOW_CONTROL_CONNECT_UNSTABLE_INDEX(unstable_control_index_source, i,
                                            unstable_control_index_sink, NumFlows - 1 - i)
  end

  `BR_ASSERT_STATIC(unstable_control_array_width_a, $bits(unstable_control_array_source_ready)
                    == NumFlows)

  // Consume every result so lint also checks that each connection produces the expected signals.
  assign observed = |{
    stable_scalar_source_ready,
    stable_scalar_sink_valid,
    stable_scalar_sink_data,
    stable_array_source_ready,
    stable_array_sink_valid,
    stable_array_sink_data,
    stable_from_source_ready,
    stable_from_sink_valid,
    stable_from_sink_data,
    stable_to_source_ready,
    stable_to_sink_valid,
    stable_to_sink_data,
    stable_index_source_ready,
    stable_index_sink_valid,
    stable_index_sink_data,
    unstable_scalar_source_ready,
    unstable_scalar_sink_valid_unstable,
    unstable_scalar_sink_data_unstable,
    unstable_array_source_ready,
    unstable_array_sink_valid_unstable,
    unstable_array_sink_data_unstable,
    unstable_from_source_ready,
    unstable_from_sink_valid_unstable,
    unstable_from_sink_data_unstable,
    unstable_to_source_ready,
    unstable_to_sink_valid_unstable,
    unstable_to_sink_data_unstable,
    unstable_index_source_ready,
    unstable_index_sink_valid_unstable,
    unstable_index_sink_data_unstable,
    control_scalar_source_ready,
    control_scalar_sink_valid,
    control_array_source_ready,
    control_array_sink_valid,
    control_from_source_ready,
    control_from_sink_valid,
    control_to_source_ready,
    control_to_sink_valid,
    control_index_source_ready,
    control_index_sink_valid,
    unstable_control_scalar_source_ready,
    unstable_control_scalar_sink_valid_unstable,
    unstable_control_array_source_ready,
    unstable_control_array_sink_valid_unstable,
    unstable_control_from_source_ready,
    unstable_control_from_sink_valid_unstable,
    unstable_control_to_source_ready,
    unstable_control_to_sink_valid_unstable,
    unstable_control_index_source_ready,
    unstable_control_index_sink_valid_unstable
  };

endmodule : br_flow_test
