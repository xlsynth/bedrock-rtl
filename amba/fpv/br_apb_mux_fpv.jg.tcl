# SPDX-License-Identifier: Apache-2.0

# Normal clock/reset set up
clock clk
reset rst
get_design_info

# APB VIP defaults to downstream-response liveness. Safety must permit arbitrary
# waits, and fixed priority cannot guarantee eventual service to every upstream.
assume -disable {*monitor.downstream.genLiveChks.slave_pready_eventually}
assert -disable {*monitor.gen_upstream_vip*.upstream.genLiveChks.slave_pready_eventually}

# Safety proofs place no bound or eventual-response requirement on PREADY.
set_prove_time_limit 10m
prove -all
