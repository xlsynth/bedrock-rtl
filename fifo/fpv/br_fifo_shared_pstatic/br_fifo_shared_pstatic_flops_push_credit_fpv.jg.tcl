# SPDX-License-Identifier: Apache-2.0

clock clk
reset -none
assume -reset -name set_rst_during_reset {rst}
assume -bound 1 -name delay_rst {rst}
assume -name deassert_rst {##1 !rst}

# primary input control signal should be legal during reset
array set param_list [get_design_info -list parameter]
set NumFifos $param_list(NumFifos)
for {set i 0} {$i < $NumFifos} {incr i} {
  assume -name initial_value_during_reset_$i "\$stable(credit_initial_push\[$i\])"
}

# The output of this flow fork will not be unstable because we constrain the
# ready to hold until valid is asserted.
# TODO(zhemao): Find a way to disable in RTL
cover -disable *br_flow_fork_head.br_flow_checks_valid_data_impl.*valid_unstable_c

# limit run time to 10-mins
set_prove_time_limit 600s

# prove command
prove -all
