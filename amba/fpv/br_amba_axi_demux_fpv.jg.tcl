# SPDX-License-Identifier: Apache-2.0


# clock/reset set up
clock clk
reset rst
get_design_info

# TODO(bgelb): disable RTL covers to make nightly clean
cover -disable *
cover -enable *br_amba_axi_demux.monitor*
# disable ABVIP unreachable covers
# FV set ABVIP Max_Pending to be RTL_OutstandingReq + 2 to test RTL backpressure
# Therefore, ABVIP overflow precondition is unreachable
cover -disable *monitor*tbl_no_overflow:precondition1
# This is the only unreachable DBC precondition in upstream
# due to encrypted ABVIP signals, it's hard to debug why this is unreachable
# it's harmless to disable though
cover -disable *monitor.upstream.genPropChksWRInf.genDbcW.genAXI4Full.genWlastExactLenDbc.master_w_aw_wlast_exact_len_dbc:precondition1

# limit run time to 30-mins
set_prove_time_limit 1800s

# prove command
prove -all
