# SPDX-License-Identifier: Apache-2.0

# Normal clock/reset set up
clock clk
reset rst
get_design_info

set_prove_time_limit 10m
prove -all
