// Uses br_reorder_tracker to implement a reorder buffer. Tags are allocated
// from the allocate interface (i.e. for requests) and responses returned on the
// deallocate_request interface. The reordered responses are returned on the
// dealloc_complete interface.

`include "br_asserts.svh"

module br_tracker_reorder_buffer_1r1w #(
    parameter int NumEntries = 2,
    parameter int EntryIdWidth = $clog2(NumEntries),
    parameter int DataWidth = 1,
    parameter int RamReadLatency = 1,
    // If 1, then assert dealloc_valid is low at the end of the test.
    parameter bit EnableAssertFinalNotDeallocValid = 1,
    localparam int MinEntryIdWidth = $clog2(NumEntries)
) (
    input logic clk,
    input logic rst,

    // Allocation Interface
    input logic alloc_ready,
    output logic alloc_valid,
    output logic [EntryIdWidth-1:0] alloc_entry_id,

    // Deallocation Request Interface
    input logic dealloc_valid,
    input logic [EntryIdWidth-1:0] dealloc_entry_id,
    input logic [DataWidth-1:0] dealloc_data,

    // Deallocation Complete Interface
    input logic dealloc_complete_ready,
    output logic dealloc_complete_valid,
    output logic [EntryIdWidth-1:0] dealloc_complete_entry_id,
    output logic [DataWidth-1:0] dealloc_complete_data,

    // 1R1W RAM Interface
    output logic [MinEntryIdWidth-1:0] ram_wr_addr,
    output logic ram_wr_valid,
    output logic [DataWidth-1:0] ram_wr_data,
    output logic [MinEntryIdWidth-1:0] ram_rd_addr,
    output logic ram_rd_addr_valid,
    input logic [DataWidth-1:0] ram_rd_data,
    input logic ram_rd_data_valid
);

    `BR_ASSERT_STATIC(legal_entry_id_width_a, EntryIdWidth >= MinEntryIdWidth)

    localparam int StagingFifoDepth = RamReadLatency + 2;

    logic dealloc_complete_beat;
    logic dealloc_complete_beat_int;
    logic dealloc_complete_valid_int;
    logic dealloc_complete_ready_int;
    logic [EntryIdWidth-1:0] dealloc_complete_entry_id_int;
    logic id_skid_fifo_pop_valid;
    logic data_skid_fifo_pop_valid;

    br_fifo_flops #(
        .Depth(StagingFifoDepth),
        .Width(EntryIdWidth)
    ) id_skid_fifo (
        .clk,
        .rst,
        //
        .push_ready(dealloc_complete_ready_int),
        .push_valid(dealloc_complete_valid_int),
        .push_data(dealloc_complete_entry_id_int),
        //
        .pop_ready(dealloc_complete_beat),
        .pop_valid(id_skid_fifo_pop_valid),
        .pop_data(dealloc_complete_entry_id),
        //
        .full(),
        .full_next(),
        .slots(),
        .slots_next(),
        //
        .empty(),
        .empty_next(),
        .items(),
        .items_next()
    );

    br_fifo_flops #(
        .Depth(StagingFifoDepth),
        .Width(DataWidth)
    ) data_skid_fifo (
        .clk,
        .rst,
        //
        .push_ready(),
        .push_valid(ram_rd_data_valid),
        .push_data(ram_rd_data),
        //
        .pop_ready(dealloc_complete_beat),
        .pop_valid(data_skid_fifo_pop_valid),
        .pop_data(dealloc_complete_data),
        //
        .full(),
        .full_next(),
        .slots(),
        .slots_next(),
        //
        .empty(),
        .empty_next(),
        .items(),
        .items_next()
    );

    br_tracker_reorder #(
        .NumEntries(NumEntries),
        .EntryIdWidth(EntryIdWidth),
        .EnableAssertFinalNotDeallocValid(EnableAssertFinalNotDeallocValid)
    ) reorder_tracker (
        .clk,
        .rst,
        //
        .alloc_ready,
        .alloc_valid,
        .alloc_entry_id,
        //
        .dealloc_valid,
        .dealloc_entry_id,
        //
        .dealloc_complete_ready(dealloc_complete_ready_int),
        .dealloc_complete_valid(dealloc_complete_valid_int),
        .dealloc_complete_entry_id(dealloc_complete_entry_id_int)
    );

    assign ram_wr_addr = dealloc_entry_id[MinEntryIdWidth-1:0];
    assign ram_wr_valid = dealloc_valid;
    assign ram_wr_data = dealloc_data;

    assign ram_rd_addr = dealloc_complete_entry_id_int[MinEntryIdWidth-1:0];
    assign ram_rd_addr_valid = dealloc_complete_beat_int;

    assign dealloc_complete_beat_int = dealloc_complete_valid_int && dealloc_complete_ready_int;

    assign dealloc_complete_beat = dealloc_complete_valid && dealloc_complete_ready;
    assign dealloc_complete_valid = id_skid_fifo_pop_valid && data_skid_fifo_pop_valid;

endmodule
