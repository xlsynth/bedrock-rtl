module br_cdc_bit_pulse_tb;

  parameter int NumStages = 3;
  parameter bit RegisterOutput = 0;
  parameter int SrcClkPeriod = 10;
  parameter int DstClkPeriod = 10;
  parameter int MaxResetCycles = 10;
  parameter int NumPulses = 20;

  // Need to wait at least this long to ensure that the source level
  // resets and propagates through the synchronizer.
  localparam int MinResetTime = SrcClkPeriod + NumStages * DstClkPeriod;
  localparam int SrcClkHalfPeriod = SrcClkPeriod / 2;
  localparam int DstClkHalfPeriod = DstClkPeriod / 2;
  localparam int MinSrcCycleSpacing = br_math::ceil_div(2 * DstClkPeriod, SrcClkPeriod);
  localparam int MaxSrcCycleSpacing = MinSrcCycleSpacing + 4;
  localparam int DstTimeoutCycles = br_math::ceil_div(
      MaxSrcCycleSpacing * SrcClkPeriod, DstClkPeriod
  ) + NumStages + RegisterOutput;

  logic src_clk;
  logic src_rst;
  logic src_pulse;

  logic dst_clk;
  logic dst_rst;
  logic dst_pulse;

  int   timeout;
  int   pulse_count;

  br_cdc_bit_pulse #(
      .NumStages(NumStages),
      .RegisterOutput(RegisterOutput)
  ) dut (
      .src_clk,
      .src_rst,
      .src_pulse,
      .dst_clk,
      .dst_rst,
      .dst_pulse
  );

  always #SrcClkHalfPeriod src_clk = ~src_clk;
  always #DstClkHalfPeriod dst_clk = ~dst_clk;

  task automatic drive_src_pulse();
    int src_delay;

    repeat (NumPulses) begin
      src_delay = $urandom_range(MinSrcCycleSpacing, MaxSrcCycleSpacing);
      repeat (src_delay) @(posedge src_clk);
      src_pulse <= 1;
      @(posedge src_clk);
      src_pulse <= 0;
    end
  endtask

  task automatic check_dst_pulse();
    timeout = DstTimeoutCycles;
    pulse_count = 0;

    while (timeout > 0 && pulse_count < NumPulses) begin
      @(posedge dst_clk);

      if (!dst_pulse) begin
        timeout--;
        continue;
      end

      pulse_count++;
      timeout = DstTimeoutCycles;
    end
  endtask

  initial begin
    int src_reset_cycles;
    int dst_reset_cycles;

    src_clk   = 0;
    dst_clk   = 0;
    src_rst   = 1;
    dst_rst   = 1;
    src_pulse = 0;

    #MinResetTime;

    src_reset_cycles = $urandom_range(0, MaxResetCycles);
    dst_reset_cycles = $urandom_range(0, MaxResetCycles);

    // Reset each cycle for random lengths of time
    fork
      begin
        repeat (src_reset_cycles) @(posedge src_clk);
        src_rst <= 0;
      end
      begin
        repeat (dst_reset_cycles) @(posedge dst_clk);
        dst_rst <= 0;
      end
    join

    fork
      drive_src_pulse();
      check_dst_pulse();
    join

    if (pulse_count < NumPulses) begin
      $error("Failed to detect all pulses. Expected %0d, got %0d.", NumPulses, pulse_count);
    end else begin
      $display("TEST PASSED");
    end
    $finish;
  end

endmodule
