# SPDX-License-Identifier: Apache-2.0

# br_mux_onehot is a combinational DUT with no clock or reset ports.
clock -none
reset -none
get_design_info

prove -all
