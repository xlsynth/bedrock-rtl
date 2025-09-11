# SPDX-License-Identifier: Apache-2.0

clock clk
reset -none
assume -reset -name set_rst_during_reset {rst}
assume -bound 1 -name delay_rst {rst}
assume -name deassert_rst {##1 !rst}

get_design_info

assume -name initial_value_during_reset {rst |-> initial_value <= MaxValue}

# limit run time to 30-mins
set_prove_time_limit 1800s

# prove command
prove -all
