# SPDX-License-Identifier: Apache-2.0


# clock/reset set up
create_clock wr_clk -period 100
create_clock rd_clk -period 100

create_reset wr_rst -high
create_reset rd_rst -high

#design infomation
report_fv_complexity

#run properties
check_fv -block
report_fv -list
