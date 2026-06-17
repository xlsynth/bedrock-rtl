// SPDX-License-Identifier: Apache-2.0

interface compile_only_smoke_if;
  logic value;
endinterface : compile_only_smoke_if

module compile_only_smoke (
    compile_only_smoke_if bus
);
endmodule : compile_only_smoke
