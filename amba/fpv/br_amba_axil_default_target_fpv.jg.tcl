# SPDX-License-Identifier: Apache-2.0


# clock/reset set up
clock clk
reset rst
get_design_info

# disable AXI ABVIP cover properties
# ABVIP Max_pending default is 2, if overwritten to 1, those covers are reachable (then bunch of other covers are unreachable).
# TODO(bgelb): please double check, RTL probably has no back pressure
cover -disable *monitor*tbl_no_overflow:precondition1

# limit run time to 30-mins
set_prove_time_limit 1800s

# prove command
prove -all
