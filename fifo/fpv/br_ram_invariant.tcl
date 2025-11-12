# SPDX-License-Identifier: Apache-2.0

# FV RAM invariant properties for br_ram_flops
# For br_fifos with internal flops, we use a tiled flop RAM architecture (br_ram_flops).
# This file contains FV properties that check the Wolper coloring invariant on the RAM.
# The invariant states that at most two '1's can exist in the RAM at the "magic_bit_index" position,
# where magic_bit_index is a parameter provided by the monitor module.

# Helper math utilities
proc ceil_div {value divisor} {
  if {$divisor <= 0} {
    error "ceil_div: divisor must be positive"
  }
  return [expr {($value + $divisor - 1) / $divisor}]
}

proc align_up {value multiple} {
  if {$multiple <= 0} {
    return $value
  }
  set quotient [ceil_div $value $multiple]
  return [expr {$quotient * $multiple}]
}

# Query elaborated parameters from the design under test
array set param_list [get_design_info -list parameter]

set Depth                          $param_list(Depth)
set Width                          $param_list(Width)
set EnableBypass                   $param_list(EnableBypass)
set RegisterPopOutputs             $param_list(RegisterPopOutputs)
set FlopRamDepthTiles              $param_list(FlopRamDepthTiles)
set FlopRamWidthTiles              $param_list(FlopRamWidthTiles)
set FlopRamAddressDepthStages      $param_list(FlopRamAddressDepthStages)
set FlopRamReadDataDepthStages     $param_list(FlopRamReadDataDepthStages)
set FlopRamReadDataWidthStages     $param_list(FlopRamReadDataWidthStages)

set RamReadLatency [expr {$FlopRamAddressDepthStages + $FlopRamReadDataDepthStages + $FlopRamReadDataWidthStages}]
if {$EnableBypass eq "1'b1" && (($RamReadLatency > 0) || $RegisterPopOutputs eq "1'b1")} {
  set depth_minus_latency [expr {$Depth - $RamReadLatency - 1}]
  if {$depth_minus_latency < 1} {
    set reduced_depth 1
  } else {
    set reduced_depth $depth_minus_latency
  }
} else {
  set reduced_depth $Depth
}

set RamDepth  [align_up $reduced_depth $FlopRamDepthTiles]
set TileDepth [ceil_div $RamDepth $FlopRamDepthTiles]
set TileWidth [ceil_div $Width $FlopRamWidthTiles]

if {$TileDepth <= 0} {
  error "Derived TileDepth is non-positive ($TileDepth)"
}
if {$TileWidth <= 0} {
  error "Derived TileWidth is non-positive ($TileWidth)"
}

# initalize ram to 0 so we don't get spurious 1s
for {set r 0} {$r < $FlopRamDepthTiles} {incr r} {
    for {set c 0} {$c < $FlopRamWidthTiles} {incr c} {
        # initalize ram to 0 so we don't get spurious 1s
        assume -name init_ram_to_0_row${r}_col${c} "\$fell(rst) |-> br_ram_flops.gen_row\[$r\].gen_col\[$c\].br_ram_flops_tile.mem == '0"
    }
}

# Build a list of expressions representing the magic column bits
set bit_exprs [lrepeat $Depth "1'b0"]
for {set r 0} {$r < $FlopRamDepthTiles} {incr r} {
  for {set d 0} {$d < $TileDepth} {incr d} {
    set depth_index [expr {$r * $TileDepth + $d}]
    if {$depth_index >= $RamDepth} {
      continue
    }
    set terms {}
    for {set c 0} {$c < $FlopRamWidthTiles} {incr c} {
      for {set b 0} {$b < $TileWidth} {incr b} {
        set mem_path [format {br_ram_flops.gen_row[%d].gen_col[%d].br_ram_flops_tile.mem[%d][0][%d]} $r $c $d $b]
        set cond     [format "((monitor.magic_bit_index / %d) == %d && (monitor.magic_bit_index %% %d) == %d)" $TileWidth $c $TileWidth $b]
        lappend terms "(($cond) ? $mem_path : 1'b0)"
      }
    }
    set bit_expr [format "(%s)" [join $terms " | "]]
    lset bit_exprs $depth_index $bit_expr
  }
}

assert -name fv_invariant_at_most_two_ones "\$countones({[join $bit_exprs ", "]}) <= 2"
