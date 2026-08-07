# SPDX-License-Identifier: Apache-2.0

# Normal clock/reset set up
clock clk
reset rst
get_design_info

# APB requests are inactive while the interface is held in reset.
assume -name no_upstream_request_during_reset {
  rst |-> !upstream_psel && !upstream_penable
}

# Prove command
prove -all
