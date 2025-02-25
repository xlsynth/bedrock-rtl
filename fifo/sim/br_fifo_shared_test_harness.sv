module br_fifo_shared_test_harness #(
    parameter int TestSize = 1000,
    parameter int MaxRandomDelay = 4,
    parameter int NumFifos = 2,
    parameter int NumWritePorts = 1,
    parameter int Width = 8,

    localparam int FifoIdWidth = $clog2(NumFifos)
) (
    input  logic        clk,
    input  logic        rst,
    input  logic        start,
    output logic        finished,
    output logic [31:0] error_count,

    input logic [NumWritePorts-1:0] push_ready,
    output logic [NumWritePorts-1:0] push_valid,
    output logic [NumWritePorts-1:0][Width-1:0] push_data,
    output logic [NumWritePorts-1:0][FifoIdWidth-1:0] push_fifo_id,

    output logic [NumFifos-1:0] pop_ready,
    input logic [NumFifos-1:0] pop_valid,
    input logic [NumFifos-1:0][Width-1:0] pop_data
);

  localparam int WritePortIdWidth = br_math::max2(1, $clog2(NumWritePorts));
  // Reserve some bits to indicate write port.
  // The remaining bits can be randomly assigned.
  localparam int MaxRandomValue = 2 ** (Width - WritePortIdWidth) - 1;

  int expected_data[NumFifos][NumWritePorts][$];
  logic [NumWritePorts-1:0] push_finished;

  assign finished = &push_finished;

  task automatic random_push(int wport);
    int fifo_id;
    int data;
    int delay;

    @(posedge clk);
    push_valid[wport] <= 1'b0;

    $display("Pushing to wport %d", wport);

    for (int i = 0; i < TestSize; i++) begin
      fifo_id = $urandom_range(0, NumFifos - 1);
      data = $urandom_range(0, MaxRandomValue);
      delay = $urandom_range(0, MaxRandomDelay);

      expected_data[fifo_id][wport].push_back(data);

      repeat (delay) @(posedge clk);

      push_valid[wport] <= 1'b1;
      push_data[wport] <= (data << WritePortIdWidth) | wport;
      push_fifo_id[wport] <= fifo_id;
      @(posedge clk);

      while (!push_ready[wport]) @(posedge clk);
      push_valid[wport] <= 1'b0;
    end

    $display("Push finished for wport %d", wport);
    push_finished[wport] <= 1'b1;
  endtask

  task automatic random_pop(int fifo_id);
    int actual;
    int wport;
    int expected;
    int delay;

    @(posedge clk);
    pop_ready[fifo_id] <= 1'b0;

    $display("Popping from FIFO %d", fifo_id);

    forever begin
      delay = $urandom_range(0, MaxRandomDelay);
      repeat (delay) @(posedge clk);

      pop_ready[fifo_id] <= 1'b1;
      @(posedge clk);

      while (!pop_valid[fifo_id]) @(posedge clk);
      pop_ready[fifo_id] <= 1'b0;

      actual = pop_data[fifo_id] >> WritePortIdWidth;
      wport = pop_data[fifo_id][WritePortIdWidth-1:0];

      if (expected_data[fifo_id][wport].size() == 0) begin
        $display("FIFO %d got data from wport %d, but no data was pushed", fifo_id, wport);
        error_count++;
      end else begin
        expected = expected_data[fifo_id][wport].pop_front();

        if (actual !== expected) begin
          $display("FIFO %d got wrong data from wport %d. Expected %0x, Got %0x", fifo_id, wport,
                  expected, actual);
          error_count++;
        end
      end
    end
  endtask

  initial begin
    push_valid = '0;
    push_data = '0;
    push_fifo_id = '0;
    pop_ready = '0;
    error_count = 0;
    push_finished = '0;

    @(negedge rst);
    @(posedge clk);

    while (!start) @(posedge clk);

    $display("Starting test");

    for (int i = 0; i < NumWritePorts; i++) begin
      automatic int wport = i;
      fork
        random_push(wport);
      join_none
    end

    for (int i = 0; i < NumFifos; i++) begin
      automatic int fifo_id = i;
      fork
        random_pop(fifo_id);
      join_none
    end
  end


endmodule
