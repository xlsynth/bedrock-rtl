module br_flow_mux_arb_last #(
    parameter int NumFlows = 2,  // Must be at least 2
    parameter int Width = 1  // Must be at least 1
) (
    input  logic                           clk,
    input  logic                           rst,
    //
    output logic [NumFlows-1:0]            push_ready,
    input  logic [NumFlows-1:0]            push_valid,
    input  logic [NumFlows-1:0][Width-1:0] push_data,
    input  logic [NumFlows-1:0]            push_last,
    //
    input  logic                           pop_ready,
    output logic                           pop_valid,
    output logic [   Width-1:0]            pop_data,
    output logic                           pop_last
);

  logic [NumFlows-1:0] request;
  logic [NumFlows-1:0] request_gated;
  logic [NumFlows-1:0] can_grant;
  logic [NumFlows-1:0] grant;
  logic [NumFlows-1:0] grant_hold;
  logic [NumFlows-1:0] grant_hold_gated;
  logic enable_priority_update_to_arb;
  logic [NumFlows-1:0] grant_from_arb;
  logic enable_priority_update_to_arb;
  logic enable_grant_hold_update;

  // grant_hold is always asserted except for the last beat of a request. It is asserted when
  // push_valid is low, which is OK because it will not win arbitration if valid is low.
  assign grant_hold = ~(push_valid & push_last);

  // We need to ensure the grant_hold logic doesn't update when there is pop-side backpressure.
  // The enable_priority_update input on the grant_hold module doesn't actually quite do this,
  // so have to do the below "gating" instead to ensure the grant_hold logic doesn't update.
  assign request_gated = enable_grant_hold_update ? request : {NumFlows{1'b0}};
  assign grant_hold_gated = enable_grant_hold_update ? grant_hold : grant;

  br_arb_rr_internal #(
      .NumRequesters(NumFlows)
  ) br_arb_rr_internal (
      .clk,
      .rst,
      .request(request_gated),
      .can_grant,
      .grant,
      .enable_priority_update(enable_priority_update_to_arb)
  );

  br_arb_grant_hold #(
      .NumRequesters(NumFlows)
  ) br_arb_grant_hold (
      .clk,
      .rst,
      .grant_hold(grant_hold_gated),
      .enable_priority_update(1'b1),
      .grant_from_arb(grant),
      .enable_priority_update_to_arb,
      .grant
  );

  br_flow_mux_core #(
      .NumFlows(NumFlows),
      .Width(Width)
  ) br_flow_mux_core (
      .clk,
      .rst,
      .request,
      .can_grant,
      .grant,
      .enable_priority_update(enable_grant_hold_update),
      .push_ready,
      .push_valid,
      .push_data,
      .pop_ready,
      .pop_valid_unstable,
      .pop_data_unstable
  );

endmodule
