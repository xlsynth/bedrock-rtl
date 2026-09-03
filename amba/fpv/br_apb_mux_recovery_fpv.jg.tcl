# SPDX-License-Identifier: Apache-2.0

# Normal clock/reset set up
clock clk
reset rst
get_design_info

# This mode deliberately violates the top-level requester contract. Disable only
# its input-stability integration assertions; retain all implementation assertions.
assert -disable {*gen_upstream_checks*access_stable_while_waiting_a}
assert -disable {*gen_upstream_checks*request_stable_while_pending_a}
assert -disable {*gen_upstream_checks*gen_wdata_checks*wdata_stable_while_pending_a}
cover -disable {*gen_upstream_checks*access_stable_while_waiting_a:precondition*}
cover -disable {*gen_upstream_checks*request_stable_while_pending_a:precondition*}
cover -disable {*gen_upstream_checks*gen_wdata_checks*wdata_stable_while_pending_a:precondition*}

# No protocol, data-stability, or response-fairness assumptions in this safety task.
set_prove_time_limit 10m
prove -all

# Isolate the eventual-response premise from the unrestricted safety proof.
# A fresh task inherits global clock/reset but none of the safety properties.
task -create downstream_progress -set
assume -name downstream_ready_fair_a {s_eventually downstream_pready}
assert -name downstream_eventually_setup_a {
  downstream_penable |-> s_eventually !downstream_penable
}
check_assumptions -task downstream_progress -live -time_limit 30s
prove -task downstream_progress
task -set <embedded>
