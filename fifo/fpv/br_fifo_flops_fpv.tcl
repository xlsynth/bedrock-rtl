# clock/reset set up
clock clk
reset rst
get_design_info

# primary input control signal should be legal during reset
assume -name no_push_valid_during_reset {rst |-> push_valid == 'd0}

# primary output control signal should be legal during reset
assert -name fv_rst_check_pop_valid {rst |-> pop_valid == 'd0}

# disable primary input side RTL integration assertion
# it's best practice to have valid/data stability when backpressured,
# but the FIFO itself doesn't care and will work fine even if it's unstable
assert -disable *br_fifo_push_ctrl.*valid_data_stable_when_backpressured_a

# prove command
prove -all
