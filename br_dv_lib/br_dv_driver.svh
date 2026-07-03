// SPDX-License-Identifier: Apache-2.0

class br_dv_driver #(
    type ItemType = br_item
) extends br_dv_component;
  protected time driver_timeout;
  local time last_timeout_poke_time;

  function new(input br_dv_context ctx = null);
    super.new(ctx);
    if (ctx != null) begin
      ctx.register(this);
    end
    driver_timeout = 10000;
    last_timeout_poke_time = 0;
  endfunction

  virtual function br_dv_component_kind_e get_kind();
    return BrDvDriver;
  endfunction

  function void set_driver_timeout(input time driver_timeout);
    this.driver_timeout = driver_timeout;
  endfunction

  function void poke_timeout();
    last_timeout_poke_time = $time;
  endfunction

  task drive_item_with_timeout(input ItemType item);
    bit drive_done;

    if (driver_timeout == 0) begin
      drive_item(item);
      return;
    end

    poke_timeout();
    drive_done = 1'b0;
    fork : drive_item_timeout_fork
      begin
        drive_item(item);
        drive_done = 1'b1;
      end
      begin
        while (!drive_done) begin
          #(driver_timeout);
          if (!drive_done && (($time - last_timeout_poke_time) >= driver_timeout)) begin
            $fatal(1, "driver drive_item timeout after %0d time units", driver_timeout);
          end
        end
      end
    join_any
    disable drive_item_timeout_fork;
  endtask

  virtual task drive_item(input ItemType item);
    $fatal(1, "drive_item is not implemented");
  endtask
endclass : br_dv_driver
