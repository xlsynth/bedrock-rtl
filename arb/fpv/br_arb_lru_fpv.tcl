# clock/reset set up
clock clk
reset rst
get_design_info

# primary output control signal should be legal during reset
assert -name fv_rst_check_grant {rst |-> grant == 'd0}

# standard use case: request will hold until grant
task -create standard -copy_all -source_task <embedded>

# non-standard use case: request will NOT hold until grant
task -create special -copy_all -source_task <embedded>
assume -disable {special::*req_hold_until_grant_a}
assert -disable {special::*no_deadlock_a}
assert -disable {special::*lru_a}

# prove command
prove -task {standard}
prove -task {special}
