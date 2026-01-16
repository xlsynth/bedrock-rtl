# SPDX-License-Identifier: Apache-2.0

# clock/reset set up
clock clk
reset rst
get_design_info

# Bus masters must drive req_valid and req_abort  to 0 during reset.
assert -name fv_rst_check_req_valid {rst |-> csr_req_valid == 'd0}
assert -name fv_rst_check_req_abort {rst |-> csr_req_abort == 'd0}

# prove command
prove -all
