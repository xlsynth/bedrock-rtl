# SPDX-License-Identifier: Apache-2.0


# clock/reset set up
clock clk
reset -none
get_design_info

# prove command
prove -all
