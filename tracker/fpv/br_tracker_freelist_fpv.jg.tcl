# SPDX-License-Identifier: Apache-2.0

clock clk
reset rst
get_design_info

# These implementation assertions can't always have their preconditions reached depending on the parameters
# TODO(zhemao): Find a way to disable these with more granularity
cover -disable {br_tracker_freelist.br_enc_priority_encoder_free_entries*no_out_if_higher_prio_in_a*}
cover -disable {br_tracker_freelist.br_enc_priority_encoder_free_entries*out_lower_prio_than_prev_out_a*}

# prove command
prove -all
