// SPDX-License-Identifier: Apache-2.0

virtual class br_dv_item_sink #(
    type ItemType = br_item
);
  pure virtual task write(input ItemType item);
endclass : br_dv_item_sink
