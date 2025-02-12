# clock/reset set up
clock clk
reset -none
get_design_info

# prove command
prove -all
