# SPDX-License-Identifier: Apache-2.0


# Normal clock/reset set up
clock clk
reset rst
get_design_info

# ABVIP has two more write-table entries than the DUT can admit, so its table-full
# overflow preconditions are structurally unreachable.
cover -disable *monitor*tbl_no_overflow:precondition1

# Upstream initiators may present AWVALID and WVALID on different cycles; the monitor has explicit
# covers for both arrival orders followed by request acceptance. These ABVIP DBC preconditions
# instead require AW and W to handshake separately. The DUT's join asserts both READYs together,
# so those internal preconditions are structurally unreachable.
cover -disable *monitor.gen_upstream_abvip*upstream*assume_master_aw_dbc_latched_addr2:precondition1
cover -disable *monitor.gen_upstream_abvip*upstream*assume_master_aw_dbc_latched_burst2:precondition1
cover -disable *monitor.gen_upstream_abvip*upstream*assume_master_aw_dbc_latched_size2:precondition1
cover -disable *monitor.gen_upstream_abvip*upstream*assume_master_aw_dbc_latched_len2:precondition1
cover -disable *monitor.gen_upstream_abvip*upstream*master_w_aw_wstrb_valid_non_dbc:precondition1

# The DUT launches downstream AWVALID/WVALID together. Downstream ABVIP data-before-control
# scenarios that require one write channel to start without the other are therefore structurally
# unreachable. These are scoped separately because the upstream and downstream reachability
# constraints have different causes.
cover -disable *monitor.downstream*assume_master_aw_dbc_latched_addr2:precondition1
cover -disable *monitor.downstream*assume_master_aw_dbc_latched_burst2:precondition1
cover -disable *monitor.downstream*assume_master_aw_dbc_latched_size2:precondition1
cover -disable *monitor.downstream*assume_master_aw_dbc_latched_len2:precondition1
cover -disable *monitor.downstream*master_w_aw_wstrb_valid_non_dbc:precondition1

# Because downstream AWVALID and WVALID are launched together, ABVIP's data-before-control
# liveness antecedents requiring one VALID to precede the other cannot activate.
cover -disable *monitor.downstream*master_aw_awvalid_eventually:precondition1
cover -disable *monitor.downstream*master_w_wvalid_eventually:precondition1

# Prove command
prove -all
