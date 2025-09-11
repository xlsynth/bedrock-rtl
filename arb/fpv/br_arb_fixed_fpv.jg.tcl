# SPDX-License-Identifier: Apache-2.0

clock clk
reset rst
get_design_info

# primary output control signal should be legal during reset
assert -name fv_rst_check_grant {rst |-> grant == 'd0}

# If index i > j, and request[j] is always high, request[i] will hang
# This is RTL intention
assert -disable {*no_deadlock_a*}

# prove command
prove -task {<embedded>}
