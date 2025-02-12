# clock/reset set up
clock clk
clock push_clk -from 1 -to 10 -both_edges
clock pop_clk -from 1 -to 10 -both_edges

reset -none
assume -reset -name set_rst_during_reset {rst}
assume -bound 1 -name delay_rst {rst}
assume -name deassert_rst {##1 !rst}
assume -env {rst == push_rst}
assume -env {rst == pop_rst}

# push/pop side primary input signals only toggle w.r.t its clock
clock -rate {push_rst \
            push_valid \
            push_data} push_clk
clock -rate {pop_rst \
            pop_ready \
            pop_ram_rd_data_valid \
            pop_ram_rd_data} pop_clk

get_design_info

# primary input control signal should be legal during reset
assume -name no_push_valid_during_reset {@(posedge push_clk) \
push_rst |-> push_valid == 'd0}

assume -name no_pop_ram_rd_data_valid_during_reset {@(posedge pop_clk) \
pop_rst |-> pop_ram_rd_data_valid == 'd0}

# primary output control signal should be legal during reset
assert -name fv_rst_check_push_ram_write_valid {@(posedge push_clk) \
push_rst |-> push_ram_wr_valid == 'd0}

assert -name fv_rst_check_pop_valid {@(posedge pop_clk) \
pop_rst |-> pop_valid == 'd0}

assert -name fv_rst_check_pop_ram_rd_addr_valid {@(posedge pop_clk) \
pop_rst |-> pop_ram_rd_addr_valid == 'd0}

# prove command
prove -all
