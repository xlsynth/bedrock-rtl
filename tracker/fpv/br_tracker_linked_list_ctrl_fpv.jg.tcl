# SPDX-License-Identifier: Apache-2.0

clock clk
reset rst
get_design_info

# limit run time to 30-mins
set_prove_time_limit 1800s

# prove command
prove -all
