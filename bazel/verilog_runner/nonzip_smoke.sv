// SPDX-License-Identifier: Apache-2.0

module nonzip_smoke #(
    parameter int Width = 1
);
  logic [Width-1:0] value;

  initial begin
    value = '0;
    $display("TEST PASSED");
    $finish;
  end
endmodule : nonzip_smoke
