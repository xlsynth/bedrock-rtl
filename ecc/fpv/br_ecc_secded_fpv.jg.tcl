# SPDX-License-Identifier: Apache-2.0


# clock/reset set up
clock clk
reset rst
get_design_info

# disable ecc error covers
cover -disable {<embedded>::br_ecc_secded_fpv_monitor.br_ecc_secded_decoder.due_no_h_column_match_a:precondition1}
cover -disable {<embedded>::br_ecc_secded_fpv_monitor.br_ecc_secded_decoder.error_correction_a:precondition1}
cover -disable {<embedded>::br_ecc_secded_fpv_monitor.br_ecc_secded_decoder.ce_c}
cover -disable {<embedded>::br_ecc_secded_fpv_monitor.br_ecc_secded_decoder.due_c}

# prove command
prove -all
