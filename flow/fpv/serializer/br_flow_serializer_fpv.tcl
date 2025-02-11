# clock/reset set up
clock clk
reset rst
get_design_info

# RTL pop_id counter never reinit or increment by 0 (always+1)
cover -disable {*br_counter_incr_pop_flit_id.plus_zero_a*}
cover -disable {*br_counter_incr_pop_flit_id.reinit_and_incr_c}

# prove command
prove -all
