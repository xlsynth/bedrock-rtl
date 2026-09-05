// SPDX-License-Identifier: Apache-2.0


`ifndef BR_FLOW_SVH
`define BR_FLOW_SVH

// Declares one canonical data-carrying ready-valid flow.
`define BR_FLOW_DECLARE(__flow__, __data_t__) \
  logic __flow__``_ready; \
  logic __flow__``_valid; \
  __data_t__ __flow__``_data;

// Declares a packed, little-endian array of canonical data-carrying ready-valid flows.
// The element typedef keeps each data index aligned with one ready-valid lane.
`define BR_FLOW_DECLARE_ARRAY(__flow__, __data_t__, __num_flows__) \
  typedef __data_t__ __flow__``_data_element_t; \
  logic [(__num_flows__)-1:0] __flow__``_ready; \
  logic [(__num_flows__)-1:0] __flow__``_valid; \
  __flow__``_data_element_t [(__num_flows__)-1:0] __flow__``_data;

// Declares one data-carrying ready/unstable-valid flow.
// Valid and data may change while ready is low.
`define BR_FLOW_DECLARE_UNSTABLE(__flow__, __data_t__) \
  logic __flow__``_ready; \
  logic __flow__``_valid_unstable; \
  __data_t__ __flow__``_data_unstable;

// Declares a packed, little-endian array of data-carrying ready/unstable-valid flows.
// The element typedef keeps each data index aligned with one ready-valid lane.
`define BR_FLOW_DECLARE_UNSTABLE_ARRAY(__flow__, __data_t__, __num_flows__) \
  typedef __data_t__ __flow__``_data_element_t; \
  logic [(__num_flows__)-1:0] __flow__``_ready; \
  logic [(__num_flows__)-1:0] __flow__``_valid_unstable; \
  __flow__``_data_element_t [(__num_flows__)-1:0] __flow__``_data_unstable;

// Declares one control-only ready-valid flow.
`define BR_FLOW_CONTROL_DECLARE(__flow__) \
  logic __flow__``_ready; \
  logic __flow__``_valid;

// Declares a packed, little-endian array of control-only ready-valid flows.
`define BR_FLOW_CONTROL_DECLARE_ARRAY(__flow__, __num_flows__) \
  logic [(__num_flows__)-1:0] __flow__``_ready; \
  logic [(__num_flows__)-1:0] __flow__``_valid;

// Declares one control-only ready/unstable-valid flow.
`define BR_FLOW_CONTROL_DECLARE_UNSTABLE(__flow__) \
  logic __flow__``_ready; \
  logic __flow__``_valid_unstable;

// Declares a packed, little-endian array of control-only ready/unstable-valid flows.
`define BR_FLOW_CONTROL_DECLARE_UNSTABLE_ARRAY(__flow__, __num_flows__) \
  logic [(__num_flows__)-1:0] __flow__``_ready; \
  logic [(__num_flows__)-1:0] __flow__``_valid_unstable;

// Returns the scalar handshake or per-lane packed handshake for a canonical flow.
// Bitwise AND preserves the shape of the ready and valid signals.
`define BR_FLOW_FIRE(__flow__) ((__flow__``_valid) & (__flow__``_ready))

// Selects one canonical packed-flow lane and returns its scalar handshake.
`define BR_FLOW_FIRE_INDEX(__flow__, __index__) \
  ((__flow__``_valid[(__index__)]) && (__flow__``_ready[(__index__)]))

// Returns the scalar handshake or per-lane packed handshake for an unstable-valid flow.
// Bitwise AND preserves the shape of the ready and unstable-valid signals.
`define BR_FLOW_FIRE_UNSTABLE(__flow__) \
  ((__flow__``_valid_unstable) & (__flow__``_ready))

// Selects one unstable-valid packed-flow lane and returns its scalar handshake.
`define BR_FLOW_FIRE_UNSTABLE_INDEX(__flow__, __index__) \
  ((__flow__``_valid_unstable[(__index__)]) && (__flow__``_ready[(__index__)]))

// Binds a scalar flow or a complete packed flow array to canonical module ports.
// The caller owns any comma that follows this port group.
`define BR_FLOW_BIND(__port__, __flow__) \
  .__port__``_ready(__flow__``_ready), \
  .__port__``_valid(__flow__``_valid), \
  .__port__``_data (__flow__``_data)

// Binds one element of a packed flow array to canonical scalar module ports.
// The caller owns any comma that follows this port group.
`define BR_FLOW_BIND_INDEX(__port__, __flow__, __index__) \
  .__port__``_ready(__flow__``_ready[__index__]), \
  .__port__``_valid(__flow__``_valid[__index__]), \
  .__port__``_data (__flow__``_data[__index__])

// Binds a scalar flow or a complete packed flow array to unstable-valid/data module ports.
// The local flow uses the same instability contract. The caller owns any following comma.
`define BR_FLOW_BIND_UNSTABLE(__port__, __flow__) \
  .__port__``_ready(__flow__``_ready), \
  .__port__``_valid_unstable(__flow__``_valid_unstable), \
  .__port__``_data_unstable (__flow__``_data_unstable)

// Binds one packed-array element to scalar unstable-valid/data module ports.
// The local flow uses the same instability contract. The caller owns any following comma.
`define BR_FLOW_BIND_UNSTABLE_INDEX(__port__, __flow__, __index__) \
  .__port__``_ready(__flow__``_ready[__index__]), \
  .__port__``_valid_unstable(__flow__``_valid_unstable[__index__]), \
  .__port__``_data_unstable (__flow__``_data_unstable[__index__])

// Continuously connects one canonical source flow or aligned packed flow array to one sink.
// Ready travels toward the source; valid and data travel toward the sink.
`define BR_FLOW_CONNECT(__source__, __sink__) \
  assign __source__``_ready = __sink__``_ready; \
  assign __sink__``_valid = __source__``_valid; \
  assign __sink__``_data = __source__``_data;

// Continuously connects one canonical source flow-array lane to one scalar sink flow.
// Ready travels toward the source; valid and data travel toward the sink.
`define BR_FLOW_CONNECT_FROM_INDEX(__source__, __source_index__, __sink__) \
  assign __source__``_ready[__source_index__] = __sink__``_ready; \
  assign __sink__``_valid = __source__``_valid[__source_index__]; \
  assign __sink__``_data = __source__``_data[__source_index__];

// Continuously connects one canonical scalar source flow to one sink flow-array lane.
// Ready travels toward the source; valid and data travel toward the sink.
`define BR_FLOW_CONNECT_TO_INDEX(__source__, __sink__, __sink_index__) \
  assign __source__``_ready = __sink__``_ready[__sink_index__]; \
  assign __sink__``_valid[__sink_index__] = __source__``_valid; \
  assign __sink__``_data[__sink_index__] = __source__``_data;

// Continuously connects one canonical source flow-array lane to one sink lane.
// Ready travels toward the source; valid and data travel toward the sink.
`define BR_FLOW_CONNECT_INDEX(__source__, __source_index__, __sink__, __sink_index__) \
  assign __source__``_ready[__source_index__] = __sink__``_ready[__sink_index__]; \
  assign __sink__``_valid[__sink_index__] = __source__``_valid[__source_index__]; \
  assign __sink__``_data[__sink_index__] = __source__``_data[__source_index__];

// Continuously connects one explicitly unstable source flow or aligned packed flow array to
// one sink. Ready travels toward the source; unstable valid and data travel toward the sink.
`define BR_FLOW_CONNECT_UNSTABLE(__source__, __sink__) \
  assign __source__``_ready = __sink__``_ready; \
  assign __sink__``_valid_unstable = __source__``_valid_unstable; \
  assign __sink__``_data_unstable = __source__``_data_unstable;

// Continuously connects one explicitly unstable source flow-array lane to one scalar sink flow.
// Ready travels toward the source; unstable valid and data travel toward the sink.
`define BR_FLOW_CONNECT_UNSTABLE_FROM_INDEX(__source__, __source_index__, __sink__) \
  assign __source__``_ready[__source_index__] = __sink__``_ready; \
  assign __sink__``_valid_unstable = __source__``_valid_unstable[__source_index__]; \
  assign __sink__``_data_unstable = __source__``_data_unstable[__source_index__];

// Continuously connects one explicitly unstable scalar source flow to one sink flow-array lane.
// Ready travels toward the source; unstable valid and data travel toward the sink.
`define BR_FLOW_CONNECT_UNSTABLE_TO_INDEX(__source__, __sink__, __sink_index__) \
  assign __source__``_ready = __sink__``_ready[__sink_index__]; \
  assign __sink__``_valid_unstable[__sink_index__] = __source__``_valid_unstable; \
  assign __sink__``_data_unstable[__sink_index__] = __source__``_data_unstable;

// Continuously connects one explicitly unstable source flow-array lane to one sink lane.
// Ready travels toward the source; unstable valid and data travel toward the sink.
`define BR_FLOW_CONNECT_UNSTABLE_INDEX(__source__, __source_index__, __sink__, __sink_index__) \
  assign __source__``_ready[__source_index__] = __sink__``_ready[__sink_index__]; \
  assign __sink__``_valid_unstable[__sink_index__] = \
      __source__``_valid_unstable[__source_index__]; \
  assign __sink__``_data_unstable[__sink_index__] = \
      __source__``_data_unstable[__source_index__];

// Binds a scalar control flow or a complete packed control-flow array to canonical module ports.
// The caller owns any comma that follows this port group.
`define BR_FLOW_CONTROL_BIND(__port__, __flow__) \
  .__port__``_ready(__flow__``_ready), \
  .__port__``_valid(__flow__``_valid)

// Binds one packed control-flow-array element to canonical scalar module ports.
// The caller owns any comma that follows this port group.
`define BR_FLOW_CONTROL_BIND_INDEX(__port__, __flow__, __index__) \
  .__port__``_ready(__flow__``_ready[__index__]), \
  .__port__``_valid(__flow__``_valid[__index__])

// Binds a scalar control flow or a complete packed control-flow array to an unstable-valid port.
// The local flow's valid signal uses the same instability contract.
// The caller owns any comma that follows this port group.
`define BR_FLOW_CONTROL_BIND_UNSTABLE(__port__, __flow__) \
  .__port__``_ready(__flow__``_ready), \
  .__port__``_valid_unstable(__flow__``_valid_unstable)

// Binds one packed control-flow-array element to scalar unstable-valid module ports.
// The local flow uses the same instability contract. The caller owns any following comma.
`define BR_FLOW_CONTROL_BIND_UNSTABLE_INDEX(__port__, __flow__, __index__) \
  .__port__``_ready(__flow__``_ready[__index__]), \
  .__port__``_valid_unstable(__flow__``_valid_unstable[__index__])

// Continuously connects one canonical control source or aligned packed source array to one sink.
// Ready travels toward the source; valid travels toward the sink.
`define BR_FLOW_CONTROL_CONNECT(__source__, __sink__) \
  assign __source__``_ready = __sink__``_ready; \
  assign __sink__``_valid = __source__``_valid;

// Continuously connects one canonical control source-array lane to one scalar sink flow.
// Ready travels toward the source; valid travels toward the sink.
`define BR_FLOW_CONTROL_CONNECT_FROM_INDEX(__source__, __source_index__, __sink__) \
  assign __source__``_ready[__source_index__] = __sink__``_ready; \
  assign __sink__``_valid = __source__``_valid[__source_index__];

// Continuously connects one canonical scalar control source to one sink-array lane.
// Ready travels toward the source; valid travels toward the sink.
`define BR_FLOW_CONTROL_CONNECT_TO_INDEX(__source__, __sink__, __sink_index__) \
  assign __source__``_ready = __sink__``_ready[__sink_index__]; \
  assign __sink__``_valid[__sink_index__] = __source__``_valid;

// Continuously connects one canonical control source-array lane to one sink-array lane.
// Ready travels toward the source; valid travels toward the sink.
`define BR_FLOW_CONTROL_CONNECT_INDEX(__source__, __source_index__, __sink__, __sink_index__) \
  assign __source__``_ready[__source_index__] = __sink__``_ready[__sink_index__]; \
  assign __sink__``_valid[__sink_index__] = __source__``_valid[__source_index__];

// Continuously connects one explicitly unstable control source or aligned packed source array to
// one sink. Ready travels toward the source; unstable valid travels toward the sink.
`define BR_FLOW_CONTROL_CONNECT_UNSTABLE(__source__, __sink__) \
  assign __source__``_ready = __sink__``_ready; \
  assign __sink__``_valid_unstable = __source__``_valid_unstable;

// Continuously connects one explicitly unstable control source-array lane to one scalar sink flow.
// Ready travels toward the source; unstable valid travels toward the sink.
`define BR_FLOW_CONTROL_CONNECT_UNSTABLE_FROM_INDEX(__source__, __source_index__, __sink__) \
  assign __source__``_ready[__source_index__] = __sink__``_ready; \
  assign __sink__``_valid_unstable = __source__``_valid_unstable[__source_index__];

// Continuously connects one explicitly unstable scalar control source to one sink-array lane.
// Ready travels toward the source; unstable valid travels toward the sink.
`define BR_FLOW_CONTROL_CONNECT_UNSTABLE_TO_INDEX(__source__, __sink__, __sink_index__) \
  assign __source__``_ready = __sink__``_ready[__sink_index__]; \
  assign __sink__``_valid_unstable[__sink_index__] = __source__``_valid_unstable;

// Continuously connects one explicitly unstable control source-array lane to one sink-array lane.
// Ready travels toward the source; unstable valid travels toward the sink.
`define BR_FLOW_CONTROL_CONNECT_UNSTABLE_INDEX(__source__, __source_i__, __sink__, __sink_i__) \
  assign __source__``_ready[__source_i__] = __sink__``_ready[__sink_i__]; \
  assign __sink__``_valid_unstable[__sink_i__] = __source__``_valid_unstable[__source_i__];

`endif  // BR_FLOW_SVH
