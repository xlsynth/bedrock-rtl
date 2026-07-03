// SPDX-License-Identifier: Apache-2.0

class br_item;
  local string name;

  function new(input string name = "br_item");
    this.name = name;
  endfunction

  function string get_name();
    return name;
  endfunction
endclass
