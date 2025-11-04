# SPDX-License-Identifier: Apache-2.0


# clock/reset set up
clock clk
reset rst
get_design_info

# primary input control signal should be legal during reset
assume -name no_push_valid_during_reset {rst |-> push_valid == 'd0}

# primary output control signal should be legal during reset
assert -name fv_rst_check_pop_valid {rst |-> pop_valid == 'd0}

array set param_list [get_design_info -list parameter]
set Depth $param_list(FlopRamDepthTiles)
set Width $param_list(FlopRamWidthTiles)
for {set r 0} {$r < $Depth} {incr r} {
    for {set c 0} {$c < $Width} {incr c} {
        # initalize ram to 0 so we don't get spurious 1s
        assume -name init_ram_to_0_row${r}_col${c} "\$fell(rst) |-> br_ram_flops.gen_row\[$r\].gen_col\[$c\].br_ram_flops_tile.mem == '0"
    }
}

# limit run time to 10-mins
set_prove_time_limit 10m

# prove command
prove -all -time_limit 1m
prove -all -with_proven
