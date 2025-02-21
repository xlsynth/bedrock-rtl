# clock/reset set up
clock clk
reset rst
get_design_info

# when alloc_valid is back pressured, it can not change next cycle
cover -disable {*gen_single_alloc_port.br_flow_reg_fwd.*_unstable_c}
cover -disable {*gen_multi_alloc_ports.br_multi_xfer_reg_fwd.*_instability_c}

# prove command
prove -all
