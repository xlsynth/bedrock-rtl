# SPDX-License-Identifier: Apache-2.0


# clock/reset set up
clock clk
reset rst
get_design_info

# primary input control signal should be legal during reset
assume -name no_push_valid_during_reset {rst |-> push_valid == 'd0}

# primary output control signal should be legal during reset
assert -name fv_rst_check_pop_valid {rst |-> pop_valid == 'd0}

# limit run time to 10-mins
set_prove_time_limit 600s

# prove command
prove -all
