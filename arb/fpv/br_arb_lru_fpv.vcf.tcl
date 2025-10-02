# SPDX-License-Identifier: Apache-2.0


# clock/reset set up
create_clock clk -period 100
create_reset rst -high
#design infomation
report_fv_complexity

#reset simulation
sim_run -stable
sim_save_reset

# standard use case: request will hold until grant
fvtask -create standard -copy FPV

# non-standard use case: request will NOT hold until grant
fvtask -create special -copy FPV
fvdisable {special::*req_hold_until_grant_a}
fvdisable {special::*no_deadlock_a}

#run properties
fvtask standard
check_fv -block
report_fv

fvtask special
check_fv -block
