// SPDX-License-Identifier: Apache-2.0

module br_dv_test_tb;
  import br_dv_lib::*;

  initial begin
    br_dv_test test;

    test = new("br_dv_test_tb");
    test.run();
  end

endmodule : br_dv_test_tb
