# clock/reset set up
clock clk
reset rst
get_design_info

# primary output control signal should be legal during reset
assert -name fv_rst_check_grant {rst |-> grant == 'd0}

# disable unreachable RTL inline covers
cover -disable br_arb_weighted_rr.gen_accumulated_weight\[*\].br_counter.increment_min_c
cover -disable br_arb_weighted_rr.gen_accumulated_weight\[*\].br_counter.decrement_min_c
cover -disable br_arb_weighted_rr.gen_accumulated_weight\[*\].br_counter.decrement_max_c
# tied to 0 in RTL
cover -disable br_arb_weighted_rr.gen_accumulated_weight\[*\].br_counter.reinit_and_change_c

# standard use case: request will hold until grant
task -create standard -copy_all -source_task <embedded>

# non-standard use case: request will NOT hold until grant
task -create special -copy_all -source_task <embedded>
assume -disable {special::*req_hold_until_grant_a}
assert -disable {special::*forward_progress_a}

# prove command
prove -task {standard}
prove -task {special}
