// SPDX-License-Identifier: Apache-2.0

`ifndef BR_AMBA_SIM_MACROS_SVH
`define BR_AMBA_SIM_MACROS_SVH

`define BR_AMBA_SIM_CHECK_EQ(actual, expected, message, failed) \
  do begin \
    if ((actual) !== (expected)) begin \
      report_error($sformatf("%s: expected 0x%0h got 0x%0h", message, expected, actual), failed); \
    end \
  end while (0)

`endif  // BR_AMBA_SIM_MACROS_SVH
