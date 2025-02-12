# clock/reset set up
clock clk
reset rst
get_design_info

# EnableAssertPushValidStability and EnableAssertPushDataStability
# doesn't apply to DUT pop_valid and pop_data
assert -disable {*pop_valid_stable_a}
assert -disable {*pop_data_stable_a}

# prove command
prove -all
