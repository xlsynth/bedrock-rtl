# SPDX-License-Identifier: Apache-2.0

clock wr_clk -from 1 -to 10 -both_edges
clock rd_clk -from 1 -to 10 -both_edges
reset wr_rst rd_rst

# wr/rd primary input signals only toggle w.r.t its clock
clock -rate {wr_rst \
            wr_valid \
            wr_addr \
            wr_data \
            wr_word_en \
            monitor.fv_checker.fv_addr} wr_clk
clock -rate {rd_rst \
            rd_addr_valid \
            rd_addr \
            rd_data_valid \
            rd_data \
            monitor.fv_checker.fv_addr} rd_clk

# prove command
prove -all
