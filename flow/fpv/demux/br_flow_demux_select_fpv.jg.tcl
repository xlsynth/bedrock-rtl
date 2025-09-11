# SPDX-License-Identifier: Apache-2.0

clock clk
reset rst
get_design_info

# select aligns with push interface
assert -disable {*must_grant_a*}

# prove command
prove -all
