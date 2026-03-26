# SPDX-License-Identifier: Apache-2.0


# clock/reset set up
clock clk
reset rst
get_design_info

# These LRU covers are unreachable in the burst mux wrappers because push_valid & push_ready are fed into the checker
# for br_flow_burst_mux_lru/stable, DUT intentionally holds grant until push_last is asserted
# So, many LRU checker covers are unreachable.
cover -disable *monitor.lru_check.gen_cover_wait_count_max.gen_counter*.wait_count_c
cover -disable *monitor.lru_check.grant_latency_a:precondition1
cover -disable *monitor.lru_check.gen_fairness_checks.gen_priority_covers*.same_priority_c
cover -disable *monitor.lru_check.gen_fairness_checks.gen_priority_covers*.low_priority_c
cover -disable *monitor.lru_check.gen_fairness_checks.gen_priority_covers*.high_priority_c

# Assertion no_wait_a fails: grant == request
# because grant intentionally holds across a burst until push_last.
assert -disable *monitor.lru_check.gen_assert_no_wait.no_wait_a

# prove command
prove -all
