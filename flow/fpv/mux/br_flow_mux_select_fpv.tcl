# clock/reset set up
clock clk
reset rst
get_design_info

# select can pick invalid index
assert -disable {*must_grant_a*}

# prove command
prove -all
