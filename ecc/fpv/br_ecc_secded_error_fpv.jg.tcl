# SPDX-License-Identifier: Apache-2.0


 # clock/reset set up
 clock clk
 reset rst
 get_design_info

# limit run time to 10-mins
set_prove_time_limit 600s

# se_decoder only gets correctable errors
cover -disable *se_decoder.due_no_h_column_match_a*
cover -disable *se_decoder.no_error_correction_a*
cover -disable *se_decoder.due_c*

# de_decoder only gets uncorrectable errors
cover -disable *de_decoder.error_correction_a*
cover -disable *de_decoder.ce_c*

# te_decoder only gets correctable errors
cover -disable *te_decoder.due_no_h_column_match_a*
cover -disable *te_decoder.no_error_correction_a*
cover -disable *te_decoder.due_c*

 # prove command
 prove -all
