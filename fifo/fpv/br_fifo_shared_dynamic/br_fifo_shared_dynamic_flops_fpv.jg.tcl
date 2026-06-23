# SPDX-License-Identifier: Apache-2.0


# clock/reset set up
clock clk
reset rst
get_design_info

# limit run time to 10-mins
set_prove_time_limit 10m

array set param_list [get_design_info -list parameter]
set NumReadPorts $param_list(NumReadPorts)
set Depth $param_list(Depth)
if {$Depth < 2 * $NumReadPorts} {
  cover -disable *br_ram_flops_pointer*br_ram_flops_tile.gen_multi_read_checks.all_rd_ports_active_a
}

# prove command
prove -all
