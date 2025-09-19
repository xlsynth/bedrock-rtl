# SPDX-License-Identifier: Apache-2.0


# clock/reset set up
clock clk
reset rst
get_design_info

# There is no flush signals in RTL
assert -disable <embedded>::br_amba_atb_funnel.monitor.gen_src\[*\].src.slv_stable.slave_af_afvalid_stable
assert -disable <embedded>::br_amba_atb_funnel.monitor.gen_src\[*\].src.deassert.slave_af_afvalid_deasserted
assert -disable <embedded>::br_amba_atb_funnel.monitor.gen_src\[*\].src.ATB_v1_0.syncreq.assert_syncreq_disabled_rev0_0

# limit run time to 30-mins
set_prove_time_limit 1800s

# prove command
prove -all
