# SPDX-License-Identifier: Apache-2.0

# Normal clock/reset set up
clock clk
reset rst
get_design_info

# limit run time to 10-mins
set_prove_time_limit 10m

# prove command
prove -all
