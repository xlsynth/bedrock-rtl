# SPDX-License-Identifier: Apache-2.0


# clock/reset set up
clock clk
reset rst
get_design_info

# br_flow_fork ties select to all ones, so the zero-select assertion is inapplicable.
assert -disable {br_flow_fork.br_flow_fork_select_multihot.always_ready_when_unselected_a}

# prove command
prove -all
