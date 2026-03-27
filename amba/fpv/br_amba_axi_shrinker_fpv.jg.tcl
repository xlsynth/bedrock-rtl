# SPDX-License-Identifier: Apache-2.0


# clock/reset set up
clock clk
reset rst
get_design_info

# limit run time to 30-mins
set_prove_time_limit 30m

# fv_fifo is a bit oversized
cover -disable *monitor.w_fifo.gen_Bypass_ast.no_push_full_a:precondition1

# prove command
prove -all
