# clock/reset set up
clock clk
reset rst
get_design_info

# pop_data_unstable is unstable regardless of whether push_data is stable
assert -disable {*pop_data_stable_a}

# prove command
prove -all
