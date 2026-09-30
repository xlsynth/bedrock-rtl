# SPDX-License-Identifier: Apache-2.0


# clock/reset set up
clock clk
reset rst
get_design_info

# primary input control signal should be legal during reset
assume -name no_push_valid_during_reset {rst |-> push_valid == 'd0}
assume -name no_data_ram_rd_data_valid {rst |-> data_ram_rd_data_valid == 'd0}
assume -name no_ptr_ram_rd_data_valid {rst |-> ptr_ram_rd_data_valid == 'd0}

# primary output control signal should be legal during reset
assert -name fv_rst_check_pop_valid {rst |-> pop_valid == 'd0}
assert -name fv_rst_check_ram_wr_valid {rst |-> data_ram_wr_valid == 'd0}
assert -name fv_rst_check_ram_rd_addr_valid {rst |-> data_ram_rd_addr_valid == 'd0}
assert -name fv_rst_check_ptr_ram_wr_valid {rst |-> ptr_ram_wr_valid == 'd0}
assert -name fv_rst_check_ptr_ram_rd_addr_valid {rst |-> ptr_ram_rd_addr_valid == 'd0}

# limit run time to 10-mins
set_prove_time_limit 10m

# br_flow_fork_head ties select to all ones, so zero select is impossible in this no-buffer path.
assert -disable {br_fifo_shared_dynamic_ctrl.br_fifo_shared_pop_ctrl_inst.br_fifo_shared_pop_ctrl_ext_arbiter.gen_fifo_ram_read*.gen_no_buffer.br_flow_fork_head.br_flow_fork_select_multihot.always_ready_when_unselected_a}

# prove command
prove -all
