# clock/reset set up
clock clk
reset rst
get_design_info

# no ecc error: encoder and decoder are directly connected
task -create no_error -copy_all -source_task <embedded>
cover -disable {no_error::br_ecc_sed_fpv_monitor.br_ecc_sed_decoder.due_c}
assert -disable {no_error::br_ecc_sed_fpv_monitor.ecc_error*}
cover -disable {no_error::br_ecc_sed_fpv_monitor.ecc_error*}
prove -task {no_error}

# ecc error into decoder:
task -create ecc_error -copy_all -source_task <embedded>
task -set ecc_error
stopat enc_codeword
assert -disable {ecc_error::br_ecc_sed_fpv_monitor.*data_integrity_a}
prove -task {ecc_error}
