# SPDX-License-Identifier: Apache-2.0


# clock/reset set up
clock clk
reset -none
assume -reset -name set_rst_during_reset {rst}
assume -bound 1 -name lfsr_rst {rst}
assume -name deassert_rst {##1 !rst}
assume -name initial_state_non_zero_during_reset {rst |-> initial_state != '0}
get_design_info

# The full-period checks are intentionally run on small configured widths.
set_prove_time_limit 1800s

# prove command
prove -all
