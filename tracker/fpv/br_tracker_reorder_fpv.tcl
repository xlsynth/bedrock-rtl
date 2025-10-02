# SPDX-License-Identifier: Apache-2.0


# clock/reset set up
clock clk
reset rst
get_design_info

# counter inc and dec is always 1
# there is no reinit
cover -disable {*br_counter_free_entry_counter.increment_min_c*}
cover -disable {*br_counter_free_entry_counter.decrement_min_c*}
cover -disable {*br_counter_free_entry_counter.reinit_and_change_c*}

# prove command
prove -all
