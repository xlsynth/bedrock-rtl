# SPDX-License-Identifier: Apache-2.0

clock clk
reset -none
assume -reset -name set_rst_during_reset {rst}
assume -bound 1 -name delay_rst {rst}
assume -name deassert_rst {##1 !rst}

# limit run time to 10-mins
set_prove_time_limit 600s

# The output of this flow fork will not be unstable because we constrain the
# ready to hold until valid is asserted.
# TODO(zhemao): Find a way to disable in RTL
cover -disable *br_flow_fork_head.br_flow_checks_valid_data_impl.*valid_unstable_c

# prove command
prove -all
