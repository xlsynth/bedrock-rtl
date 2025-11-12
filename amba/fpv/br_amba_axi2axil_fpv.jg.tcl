# SPDX-License-Identifier: Apache-2.0


# clock/reset set up
clock clk
reset rst
get_design_info

# These should be assumptions because signals are primary inputs
assume -from_assert <embedded>::br_amba_axi2axil.monitor.axi4.genStableChksRDInf.genRStableChks.slave_r_rdata_stable
assume -from_assert <embedded>::br_amba_axi2axil.monitor.axi4_lite.genPropChksWRInf.genNoWrDatTblOverflow.genMas.master_w_wr_tbl_no_overflow

# disable ABVIP unreachable covers
# FV set ABVIP Max_Pending to be RTL_OutstandingReq + 2 to test RTL backpressure
# Therefore, ABVIP overflow precondition is unreachable
cover -disable *monitor*tbl_no_overflow:precondition1

# limit run time to 30-mins
set_prove_time_limit 1800s

# prove command
prove -all
