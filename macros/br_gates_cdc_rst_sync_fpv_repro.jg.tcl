# SPDX-License-Identifier: Apache-2.0

clock clk
reset -none
get_design_info

set_prove_time_limit 1800s
prove -all
