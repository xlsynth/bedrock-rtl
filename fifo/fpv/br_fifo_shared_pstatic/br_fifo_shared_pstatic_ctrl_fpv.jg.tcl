# SPDX-License-Identifier: Apache-2.0


# clock/reset set up
clock clk
reset -none
assume -reset -name set_rst_during_reset {rst}
assume -bound 1 -name delay_rst {rst}
assume -name deassert_rst {##1 !rst}

# limit run time to 10-mins
set_prove_time_limit 600s

# br_flow_fork_head ties select to all ones, so zero select is impossible in this no-buffer path.
assert -disable {br_fifo_shared_pstatic_ctrl.br_fifo_shared_pop_ctrl_inst.br_fifo_shared_pop_ctrl_ext_arbiter.gen_fifo_ram_read*.gen_no_buffer.br_flow_fork_head.br_flow_fork_select_multihot.always_ready_when_unselected_a}

# prove command
prove -all
