# SPDX-License-Identifier: Apache-2.0


# clock/reset set up
create_clock clk -period 100
create_reset rst -high
#design infomation
report_fv_complexity

# disable unreachable RTL inline covers
fvdisable br_arb_weighted_rr.gen_accumulated_weight\[*\].br_counter.increment_min_c
fvdisable br_arb_weighted_rr.gen_accumulated_weight\[*\].br_counter.decrement_min_c
fvdisable br_arb_weighted_rr.gen_accumulated_weight\[*\].br_counter.decrement_max_c
# tied to 0 in RTL
fvdisable br_arb_weighted_rr.gen_accumulated_weight\[*\].br_counter.reinit_and_change_c

# standard use case: request will hold until grant
fvtask -create standard -copy FPV

# non-standard use case: request will NOT hold until grant
fvtask -create special -copy FPV
fvdisable {special::*req_hold_until_grant_a}
fvdisable {special::*forward_progress_a}

#run properties
fvtask standard
check_fv -block

fvtask special
check_fv -block
