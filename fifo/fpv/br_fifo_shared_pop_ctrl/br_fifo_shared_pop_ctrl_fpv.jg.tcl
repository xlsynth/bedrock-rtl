# SPDX-License-Identifier: Apache-2.0

# Normal clock/reset set up
clock clk
reset rst
get_design_info

# limit run time to 10-mins
set_prove_time_limit 10m

# br_flow_fork_head ties select to all ones, so zero select is impossible in this no-buffer path.
assert -disable {br_fifo_shared_pop_ctrl.br_fifo_shared_pop_ctrl_ext_arbiter.gen_fifo_ram_read*.gen_no_buffer.br_flow_fork_head.br_flow_fork_select_multihot.always_ready_when_unselected_a}

# br_flow_fork_head ties select to all ones, so zero select is impossible in this no-buffer path.
assert -disable {br_fifo_shared_pop_ctrl_ext_arbiter.gen_fifo_ram_read*.gen_no_buffer.br_flow_fork_head.br_flow_fork_select_multihot.always_ready_when_unselected_a}

# prove command
prove -all
