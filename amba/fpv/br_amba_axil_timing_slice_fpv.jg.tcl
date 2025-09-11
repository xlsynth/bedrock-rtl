# SPDX-License-Identifier: Apache-2.0

clock clk
reset rst
get_design_info

# AW/W, AR/R backpressure at one side is not guaranteed in timing slice
# target side
assert -disable <embedded>::br_amba_axil_timing_slice.monitor.target.genPropChksRDInf.genNoRdTblOverflow.genSlv.slave_ar_rd_tbl_no_overflow
assert -disable <embedded>::br_amba_axil_timing_slice.monitor.target.genPropChksWRInf.genNoWrTblOverflow.genSlv.slave_aw_wr_tbl_no_overflow
assert -disable <embedded>::br_amba_axil_timing_slice.monitor.target.genPropChksWRInf.genNoWrDatTblOverflow.genSlv.slave_w_wr_tbl_no_overflow
# init side
assert -disable <embedded>::br_amba_axil_timing_slice.monitor.init.genPropChksRDInf.genNoRdTblOverflow.genMas.master_ar_rd_tbl_no_overflow
assert -disable <embedded>::br_amba_axil_timing_slice.monitor.init.genPropChksWRInf.genNoWrTblOverflow.genMas.master_aw_wr_tbl_no_overflow
assert -disable <embedded>::br_amba_axil_timing_slice.monitor.init.genPropChksWRInf.genNoWrDatTblOverflow.genMas.master_w_wr_tbl_no_overflow

# limit run time to 30-mins
set_prove_time_limit 1800s

# prove command
prove -all
