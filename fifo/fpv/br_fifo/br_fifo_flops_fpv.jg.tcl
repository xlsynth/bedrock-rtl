# SPDX-License-Identifier: Apache-2.0


# clock/reset set up
clock clk
reset rst
get_design_info

# primary input control signal should be legal during reset
assume -name no_push_valid_during_reset {rst |-> push_valid == 'd0}

# primary output control signal should be legal during reset
assert -name fv_rst_check_pop_valid {rst |-> pop_valid == 'd0}

# source ram invariant properties
array set local_param_list [get_design_info -instance monitor -list local_parameter]
set WolperColorEn $local_param_list(WolperColorEn)
if {$WolperColorEn eq "1'b1"} {
    set invariant_path [file join $::env(TEST_SRCDIR) $::env(TEST_WORKSPACE) fifo fpv br_ram_invariant.tcl]
    source $invariant_path
}

# limit run time to 10-mins
set_prove_time_limit 10m

# prove command
prove -all -time_limit 1m
prove -all -with_proven
