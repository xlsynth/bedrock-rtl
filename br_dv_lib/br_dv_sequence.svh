// SPDX-License-Identifier: Apache-2.0

class br_dv_sequence #(
    type ItemType = br_item
) extends br_dv_sequence_base;
  local ItemType item_q[$];
  local br_dv_driver #(.ItemType(ItemType)) driver;

  function new(input br_dv_context ctx = null);
    super.new(ctx);
    if (ctx != null) begin
      ctx.register(this);
    end
  endfunction

  function void connect(input br_dv_driver#(.ItemType(ItemType)) driver);
    this.driver = driver;
  endfunction

  function void push_item(input ItemType item);
    item_q.push_back(item);
  endfunction

  virtual function bit has_item();
    return item_q.size() != 0;
  endfunction

  function ItemType pop_item();
    if (!has_item()) begin
      return null;
    end
    return item_q.pop_front();
  endfunction

  function bit is_connected();
    return driver != null;
  endfunction

  task start();
    ItemType item;

    if (!is_connected()) begin
      $fatal(1, "sequence started without connected driver");
    end

    started = 1'b1;
    while (has_item()) begin
      item = item_q[0];
      driver.drive_item_with_timeout(item);
      void'(pop_item());
    end
    driver.drive_item_with_timeout(null);
    started = 1'b0;
  endtask
endclass
