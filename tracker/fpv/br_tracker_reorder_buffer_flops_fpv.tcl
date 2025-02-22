# clock/reset set up
clock clk
reset rst
get_design_info

# TODO: ignore many unreachable RTL inline covers for now
cover -disable {*br_tracker_reorder_buffer_flops.br_tracker_reorder_buffer_ctrl_1r1w_inst*}

# prove command
prove -all
