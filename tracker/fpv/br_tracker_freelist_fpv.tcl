# clock/reset set up
clock clk
reset rst
get_design_info

# when alloc_valid is back pressured, it can not change next cycle
cover -disable {*gen_alloc_port*br_flow_reg_rev.br_flow_checks_valid_data_impl.*unstable_c}
cover -disable {*gen_alloc_port*br_flow_reg_rev.br_flow_checks_valid_data_intg.*unstable_c}
cover -disable {*gen_alloc_port*br_flow_reg_fwd.br_flow_checks_valid_data_intg.*unstable_c}
cover -disable {*gen_single_alloc_port*br_flow_reg_fwd.br_flow_checks_valid_data_intg.*unstable_c}

# prove command
prove -all
