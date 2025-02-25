# clock/reset set up
create_clock clk -period 100
create_reset rst -high
#design infomation
report_fv_complexity

# primary output control signal should be legal during reset
fvassert fv_rst_check_grant -expr {rst |-> grant == 'd0}

# If index i > j, and request[j] is always high, request[i] will hang
# This is RTL intention
fvdisable {*no_deadlock_a*}

#reset simulation
sim_run -stable
sim_save_reset

#run properties
check_fv -block
report_fv -list
