# clock/reset set up
clock clk
reset rst
get_design_info

# pop_valid is flopped
assert -disable {*must_grant_a}
# this is stable version DUT: disable unreachable covers due to RTL instantiation
cover -disable {*data_unstable_c}
cover -disable {*valid_unstable_c}

# prove command
prove -all
