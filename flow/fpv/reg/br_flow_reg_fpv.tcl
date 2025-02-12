# clock/reset set up
clock clk
reset rst
get_design_info

# TODO: parameters are tied when instantiating sub-DUT, so there are many unreachable covers
cover -disable *

# prove command
prove -all
