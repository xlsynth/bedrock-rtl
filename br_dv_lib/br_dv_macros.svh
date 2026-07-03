// SPDX-License-Identifier: Apache-2.0

`ifndef BR_DV_MACROS_SVH_
`define BR_DV_MACROS_SVH_

`define BR_DEFINE_TEST(TestClass, TestTimeout) \
  class TestClass extends br_dv_test; \
    function new(); \
      super.new(`"TestClass`"); \
      set_timeout(TestTimeout); \
    endfunction \
    virtual task test_body(); \
      run_all_tests(); \
    endtask \
  endclass

`define BR_RUN_TEST(TestClass) \
  TestClass test; \
  initial begin \
    test = new(); \
    test.start(); \
    run_all_tests(); \
    test.finish(); \
  end

`endif  // BR_DV_MACROS_SVH_
