// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

module br_amba_axil_msi_tb;
  logic clk;
  logic rst;
  logic [1:0] done;

  br_test_driver td (
      .clk,
      .rst
  );

  for (genvar variant = 0; variant < 2; variant++) begin : gen_data_width
    localparam int DataWidth = 32 << variant;
    localparam int AddrWidth = 40;
    localparam int StrobeWidth = DataWidth / 8;

    logic [1:0] irq;
    logic [1:0][AddrWidth-1:0] msi_dest_addr;
    logic [1:0][0:0] msi_dest_idx;
    logic [1:0][15:0] device_id_per_irq;
    logic [1:0][15:0] event_id_per_irq;
    logic error;
    logic [AddrWidth-1:0] init_awaddr;
    logic init_awvalid;
    logic init_awready;
    logic [DataWidth-1:0] init_wdata;
    logic [StrobeWidth-1:0] init_wstrb;
    logic init_wvalid;
    logic init_wready;
    logic init_bvalid;
    logic init_bready;
    logic [1:0][AddrWidth-1:0] expected_addr;
    logic [1:0][DataWidth-1:0] expected_data;
    logic [1:0][StrobeWidth-1:0] expected_strb;
    int unsigned aw_count;
    int unsigned w_count;
    int unsigned b_count;

    br_amba_axil_msi #(
        .AddrWidth(AddrWidth),
        .DataWidth(DataWidth),
        .NumInterrupts(2),
        .NumMsiDestAddr(2),
        .DeviceIdWidth(16),
        .EventIdWidth(16)
    ) dut (
        .clk,
        .rst,
        .irq,
        .msi_dest_addr,
        .msi_enable(2'b11),
        .msi_dest_idx,
        .device_id_per_irq,
        .event_id_per_irq,
        .throttle_en(1'b0),
        .throttle_cntr_threshold(16'b0),
        .error,
        .init_awaddr,
        .init_awvalid,
        .init_awready,
        .init_wdata,
        .init_wstrb,
        .init_wvalid,
        .init_wready,
        .init_bresp(2'b00),
        .init_bvalid,
        .init_bready
    );

    assign init_bvalid = (b_count < aw_count) && (b_count < w_count);

    // Checking every valid cycle also checks stability while either channel is stalled.
    always @(posedge clk) begin
      if (!rst) begin
        td.check(error === 1'b0, $sformatf("DataWidth=%0d unexpected MSI error", DataWidth));
        if (init_awvalid) begin
          td.check(aw_count < 2, $sformatf("DataWidth=%0d unexpected AW", DataWidth));
          if (aw_count < 2) begin
            td.check(init_awaddr === expected_addr[aw_count], $sformatf(
                     "DataWidth=%0d AW[%0d]=%h expected=%h",
                     DataWidth,
                     aw_count,
                     init_awaddr,
                     expected_addr[aw_count]
                     ));
          end
          if (init_awready) aw_count++;
        end
        if (init_wvalid) begin
          td.check(w_count < 2, $sformatf("DataWidth=%0d unexpected W", DataWidth));
          if (w_count < 2) begin
            td.check({init_wdata, init_wstrb} === {expected_data[w_count], expected_strb[w_count]},
                     $sformatf(
                     "DataWidth=%0d W[%0d] data=%h strb=%h expected data=%h strb=%h",
                     DataWidth,
                     w_count,
                     init_wdata,
                     init_wstrb,
                     expected_data[w_count],
                     expected_strb[w_count]
                     ));
          end
          if (init_wready) w_count++;
        end
        if (init_bvalid && init_bready) b_count++;
      end
    end

    initial begin
      done[variant] = 1'b0;
      irq = '0;
      msi_dest_addr = '0;
      msi_dest_idx = 2'b10;
      device_id_per_irq = '0;
      event_id_per_irq = '0;
      init_awready = 1'b0;
      init_wready = 1'b0;
      aw_count = 0;
      w_count = 0;
      b_count = 0;
      wait (rst === 1'b0);

      for (int base_bit = 0; base_bit < 2; base_bit++) begin
        for (int device_bit = 0; device_bit < 2; device_bit++) begin
          @(negedge clk);
          init_awready = 1'b0;
          init_wready = 1'b0;
          aw_count = 0;
          w_count = 0;
          b_count = 0;
          msi_dest_addr[0] = 40'h10_0000_1ff8 + 40'(4 * base_bit);
          msi_dest_addr[1] = 40'h20_0000_2ff8 + 40'(4 * (1 - base_bit));
          device_id_per_irq[0] = 16'h0120 + 16'(device_bit);
          device_id_per_irq[1] = 16'h0122 + 16'(device_bit);
          event_id_per_irq[0] = 16'ha135 + 16'(2 * base_bit + device_bit);
          event_id_per_irq[1] = 16'hc246 + 16'(2 * base_bit + device_bit);
          for (int i = 0; i < 2; i++) begin
            expected_addr[i] = msi_dest_addr[i] + AddrWidth'(device_id_per_irq[i]) * 40'd4;
            expected_data[i] = DataWidth'(event_id_per_irq[i]) <<
                (8 * (expected_addr[i] % StrobeWidth));
            expected_strb[i] = StrobeWidth'(4'hf) << (expected_addr[i] % StrobeWidth);
          end

          // Queue two messages with distinct addresses and opposite 64-bit byte lanes.
          for (int i = 0; i < 2; i++) begin
            irq[i] = 1'b1;
            @(negedge clk);
            irq[i] = 1'b0;
            repeat (8) @(negedge clk);
          end
          td.check(init_awvalid && init_wvalid, $sformatf(
                   "DataWidth=%0d missing buffered MSI", DataWidth));

          // Drain one channel fully while the other retains both queued messages.
          init_awready = 1'(base_bit);
          init_wready  = !base_bit;
          repeat (8) @(negedge clk);
          td.check(
              aw_count == 2 * base_bit && w_count == 2 * (1 - base_bit), $sformatf(
              "DataWidth=%0d independent channel drain AW=%0d W=%0d", DataWidth, aw_count, w_count
              ));
          init_awready = 1'b1;
          init_wready  = 1'b1;
          repeat (12) @(negedge clk);
          td.check(aw_count == 2 && w_count == 2 && b_count == 2, $sformatf(
                   "DataWidth=%0d incomplete MSI burst AW=%0d W=%0d B=%0d",
                   DataWidth,
                   aw_count,
                   w_count,
                   b_count
                   ));
        end
      end
      done[variant] = 1'b1;
    end
  end

  initial begin
    td.reset_dut();
    wait (&done);
    td.finish();
  end

  initial begin
    repeat (1000) @(posedge clk);
    $fatal(1, "MSI byte-lane test timed out");
  end
endmodule : br_amba_axil_msi_tb
