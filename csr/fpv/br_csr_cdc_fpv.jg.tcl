# SPDX-License-Identifier: Apache-2.0

# clock/reset set up
clock clk
clock upstream_clk -from 1 -to 10 -both_edges
clock downstream_clk -from 1 -to 10 -both_edges

# declare a system reset
reset -none
assume -reset -name set_rst_during_reset {rst}
assume -bound 1 -name delay_rst {rst}
assume -name deassert_rst {##1 !rst}
# reset are ready at different times
assume -env {rst |-> upstream_rst}
assume -env {rst |-> downstream_rst}
assume -env {!upstream_rst |=> !upstream_rst}
assume -env {!downstream_rst |=> !downstream_rst}
assume -env {s_eventually !upstream_rst}
assume -env {s_eventually !downstream_rst}

# primary input signals only toggle w.r.t their clocks
clock -rate {upstream_rst \
            upstream_req_valid \
            upstream_req_write \
            upstream_req_addr \
            upstream_req_wdata \
            upstream_req_wstrb \
            upstream_req_secure \
            upstream_req_privileged \
            upstream_req_abort} upstream_clk

clock -rate {downstream_rst \
            downstream_resp_valid \
            downstream_resp_rdata \
            downstream_resp_slverr \
            downstream_resp_decerr} downstream_clk

get_design_info

# primary input control signal should be legal during reset
assume -name no_req_valid_during_reset {@(posedge upstream_clk) \
upstream_rst |-> upstream_req_valid == 'd0}

assume -name no_req_abort_during_reset {@(posedge upstream_clk) \
upstream_rst |-> upstream_req_abort == 'd0}

assume -name no_resp_valid_during_reset {@(posedge downstream_clk) \
downstream_rst |-> downstream_resp_valid == 'd0}

# limit run time to 10-mins
set_prove_time_limit 600s

prove -all
