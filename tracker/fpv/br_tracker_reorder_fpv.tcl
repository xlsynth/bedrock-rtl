# clock/reset set up
clock clk
reset rst
get_design_info

# counter inc and dec is always 1
# there is no reinit
cover -disable {*br_counter_incr_allocate_counter.plus_zero_a*}
cover -disable {*br_counter_incr_allocate_counter.reinit_no_incr_a*}
cover -disable {*br_counter_incr_allocate_counter.reinit_and_incr_c*}
cover -disable {*br_counter_incr_deallocate_counter.plus_zero_a*}
cover -disable {*br_counter_incr_deallocate_counter.reinit_no_incr_a*}
cover -disable {*br_counter_incr_deallocate_counter.reinit_and_incr_c*}
cover -disable {*br_counter_free_entry_counter.increment_min_c*}
cover -disable {*br_counter_free_entry_counter.decrement_min_c*}
cover -disable {*br_counter_free_entry_counter.reinit_and_change_c*}

# prove command
prove -all
