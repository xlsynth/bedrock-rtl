# SPDX-License-Identifier: Apache-2.0

clock clk
reset rst
get_design_info

# limit run time to 30-mins
set_prove_time_limit 1800s

# flow of DUT: alloc -> unordered response -> ordered response
# If unordered response interface sends data to DUT, entry_id can be reused at alloc interface.
# Before unordered response interface also gets back pressure, we can hold NumEntries x 2 outstanding requests.
# when DUT reads back data from external RAM, once the read request is sent out, entry_id can be reused at alloc interface.
# However, it takes RamReadLatency to get ordered_response_valid.
# Therefore, for FV modeling purpose, fv_fifo is sized to be (NumEntries x 2) + RamReadLatency to hold outstanding entry_id.
# for a few parameter set up, fv_fifo full is unreachable.
# This only means fv_fifo is over-sized, won't miss any bugs.
cover -disable *fv_checker.entry_id_fifo.gen_ast.no_push_full_a*

# prove command
prove -all
