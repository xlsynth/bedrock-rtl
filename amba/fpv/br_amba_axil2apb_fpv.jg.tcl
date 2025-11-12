# SPDX-License-Identifier: Apache-2.0


# clock/reset set up
clock clk
reset rst
get_design_info

# TODO(bgelb): please check unreachable RTL covers
cover -disable *br_amba_axil2apb.br_arb_rr.no_update_same_grants_A:precondition1
cover -disable *br_amba_axil2apb.br_arb_rr.grant_without_state_update_c

# TODO(masai): ABVIP covers are fully encrypted, impossible to debug
# OK to disable for now since those dbc related covers are checking data before control
# I realize these covers are unreachable for AXI-Lite
cover -disable *monitor.axi.genPropChksWRInf.genByStrb.genDbcl.genDatAcpt.assume_master_aw_dbc_latched_addr2:precondition1
cover -disable *monitor.axi.genPropChksWRInf.genByStrb.genDbcl.genDatAcpt.assume_master_aw_dbc_latched_burst2:precondition1
cover -disable *monitor.axi.genPropChksWRInf.genByStrb.genDbcl.genDatAcpt.assume_master_aw_dbc_latched_size2:precondition1
cover -disable *monitor.axi.genPropChksWRInf.genByStrb.genDbcl.genDatAcpt.assume_master_aw_dbc_latched_len2:precondition1
cover -disable *monitor.axi.genPropChksWRInf.genByStrb.master_w_aw_wstrb_valid_non_dbc:precondition1


# prove command
prove -all
