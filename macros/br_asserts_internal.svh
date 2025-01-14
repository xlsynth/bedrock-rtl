// Copyright 2024 The Bedrock-RTL Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

`ifndef BR_ASSERTS_INTERNAL_SVH
`define BR_ASSERTS_INTERNAL_SVH

`include "br_asserts.svh"

// ri lint_check_off LINE_LENGTH
// verilog_lint: waive-start line-length
// verilog_format: off

// Bedrock-internal macros for instantiating SystemVerilog Assertions (SVA).
// Not intended for use outside of Bedrock.
//
// Integration checks are intended to check a design's assumptions about its input stimulus.
// Implementation checks are intended to check a design's correctness given that its input assumptions
// are not violated.
//
// The macros in this file are guarded with the following defines.
// * BR_DISABLE_INTG_CHECKS -- if defined, then all the BR_*_INTG checks are no-ops.
// * BR_ENABLE_IMPL_CHECKS -- if not defined, then all the BR_*_IMPL checks are no-ops.
//
// The intent is that users should not need to do anything, so that by default they will get only
// the integration checks but not the implementation checks.
//
// The user should not need implementation checks because the Bedrock modules are pre-verified; omitting
// the checks speeds up tools and removes noisy covers that won't necessarily get hit in the user's design.

////////////////////////////////////////////////////////////////////////////////
// Concurrent assertion macros (evaluated on posedge of a clock and disabled during a synchronous active-high reset)
////////////////////////////////////////////////////////////////////////////////

// Clock: 'clk'
// Reset: 'rst'
`ifndef BR_DISABLE_INTG_CHECKS
`define BR_ASSERT_INTG(__name__, __expr__) \
`BR_ASSERT(__name__, __expr__)
`else  // BR_DISABLE_INTG_CHECKS
`define BR_ASSERT_INTG(__name__, __expr__) \
`BR_NOOP
`endif  // BR_DISABLE_INTG_CHECKS

// More expressive form of BR_ASSERT_INTG that allows the use of custom clock and reset signal names.
`ifndef BR_DISABLE_INTG_CHECKS
`define BR_ASSERT_CR_INTG(__name__, __expr__, __clk__, __rst__) \
`BR_ASSERT_CR(__name__, __expr__, __clk__, __rst__)
`else  // BR_DISABLE_INTG_CHECKS
`define BR_ASSERT_CR_INTG(__name__, __expr__, __clk__, __rst__) \
`BR_NOOP
`endif  // BR_DISABLE_INTG_CHECKS

// Assert an expression is always known.
`ifndef BR_DISABLE_INTG_CHECKS
`define BR_ASSERT_KNOWN_INTG(__name__, __expr__) \
`BR_ASSERT_KNOWN(__name__, __expr__)
`else  // BR_DISABLE_INTG_CHECKS
`define BR_ASSERT_KNOWN_INTG(__name__, __expr__) \
`BR_NOOP
`endif  // BR_DISABLE_INTG_CHECKS

// Assert an expression is known whenever a corresponding valid signal is 1.
`ifndef BR_DISABLE_INTG_CHECKS
`define BR_ASSERT_KNOWN_VALID_INTG(__name__, __valid__, __expr__) \
`BR_ASSERT_KNOWN_VALID(__name__, __valid__, __expr__)
`else  // BR_DISABLE_INTG_CHECKS
`define BR_ASSERT_KNOWN_VALID_INTG(__name__, __valid__, __expr__) \
`BR_NOOP
`endif  // BR_DISABLE_INTG_CHECKS

// More expressive form of BR_ASSERT_KNOWN_INTG that allows the use of custom clock and reset signal names.
`ifndef BR_DISABLE_INTG_CHECKS
`define BR_ASSERT_KNOWN_CR_INTG(__name__, __expr__, __clk__, __rst__) \
`BR_ASSERT_KNOWN_CR(__name__, __expr__, __clk__, __rst__)
`else  // BR_DISABLE_INTG_CHECKS
`define BR_ASSERT_KNOWN_CR_INTG(__name__, __expr__, __clk__, __rst__) \
`BR_NOOP
`endif  // BR_DISABLE_INTG_CHECKS

// More expressive form of BR_ASSERT_KNOWN_VALID_INTG that allows the use of custom clock and reset signal names.
`ifndef BR_DISABLE_INTG_CHECKS
`define BR_ASSERT_KNOWN_VALID_CR_INTG(__name__, __valid__, __expr__, __clk__, __rst__) \
`BR_ASSERT_KNOWN_VALID_CR(__name__, __valid__, __expr__, __clk__, __rst__)
`else  // BR_DISABLE_INTG_CHECKS
`define BR_ASSERT_KNOWN_VALID_CR_INTG(__name__, __valid__, __expr__, __clk__, __rst__) \
`BR_NOOP
`endif  // BR_DISABLE_INTG_CHECKS

// Clock: 'clk'
// Reset: 'rst'
`ifdef BR_ENABLE_IMPL_CHECKS
`define BR_ASSERT_IMPL(__name__, __expr__) \
`BR_ASSERT(__name__, __expr__)
`else  // BR_ENABLE_IMPL_CHECKS
`define BR_ASSERT_IMPL(__name__, __expr__) \
`BR_NOOP
`endif  // BR_ENABLE_IMPL_CHECKS

`ifndef BR_DISABLE_INTG_CHECKS
`define BR_ASSERT_IN_RST_INTG(__name__, __expr__) \
`BR_ASSERT_IN_RST(__name__, __expr__)
`else  // BR_DISABLE_INTG_CHECKS
`define BR_ASSERT_IN_RST_INTG(__name__, __expr__) \
`BR_NOOP
`endif  // BR_DISABLE_INTG_CHECKS

`ifndef BR_DISABLE_INTG_CHECKS
`define BR_ASSERT_IN_RST_C_INTG(__name__, __expr__, __clk__) \
`BR_ASSERT_IN_RST_C(__name__, __expr__, __clk__)
`else  // BR_DISABLE_INTG_CHECKS
`define BR_ASSERT_IN_RST_C_INTG(__name__, __expr__, __clk__) \
`BR_NOOP
`endif  // BR_DISABLE_INTG_CHECKS

// More expressive form of BR_ASSERT_IMPL that allows the use of custom clock and reset signal names.
`ifdef BR_ENABLE_IMPL_CHECKS
`define BR_ASSERT_CR_IMPL(__name__, __expr__, __clk__, __rst__) \
`BR_ASSERT_CR(__name__, __expr__, __clk__, __rst__)
`else  // BR_ENABLE_IMPL_CHECKS
`define BR_ASSERT_CR_IMPL(__name__, __expr__, __clk__, __rst__) \
`BR_NOOP
`endif  // BR_ENABLE_IMPL_CHECKS

// Assert an expression is always known.
`ifndef BR_ENABLE_IMPL_CHECKS
`define BR_ASSERT_KNOWN_IMPL(__name__, __expr__) \
`BR_ASSERT_KNOWN(__name__, __expr__)
`else  // BR_ENABLE_IMPL_CHECKS
`define BR_ASSERT_KNOWN_IMPL(__name__, __expr__) \
`BR_NOOP
`endif  // BR_ENABLE_IMPL_CHECKS

// Assert an expression is known whenever a corresponding valid signal is 1.
`ifndef BR_ENABLE_IMPL_CHECKS
`define BR_ASSERT_KNOWN_VALID_IMPL(__name__, __valid__, __expr__) \
`BR_ASSERT_KNOWN_VALID(__name__, __valid__, __expr__)
`else  // BR_ENABLE_IMPL_CHECKS
`define BR_ASSERT_KNOWN_VALID_IMPL(__name__, __valid__, __expr__) \
`BR_NOOP
`endif  // BR_ENABLE_IMPL_CHECKS

// More expressive form of BR_ASSERT_KNOWN_IMPL that allows the use of custom clock and reset signal names.
`ifndef BR_ENABLE_IMPL_CHECKS
`define BR_ASSERT_KNOWN_CR_IMPL(__name__, __expr__, __clk__, __rst__) \
`BR_ASSERT_KNOWN_CR(__name__, __expr__, __clk__, __rst__)
`else  // BR_ENABLE_IMPL_CHECKS
`define BR_ASSERT_KNOWN_CR_IMPL(__name__, __expr__, __clk__, __rst__) \
`BR_NOOP
`endif  // BR_ENABLE_IMPL_CHECKS

// More expressive form of BR_ASSERT_KNOWN_VALID_IMPL that allows the use of custom clock and reset signal names.
`ifndef BR_ENABLE_IMPL_CHECKS
`define BR_ASSERT_KNOWN_VALID_CR_IMPL(__name__, __valid__, __expr__, __clk__, __rst__) \
`BR_ASSERT_KNOWN_VALID_CR(__name__, __valid__, __expr__, __clk__, __rst__)
`else  // BR_ENABLE_IMPL_CHECKS
`define BR_ASSERT_KNOWN_VALID_CR_IMPL(__name__, __valid__, __expr__, __clk__, __rst__) \
`BR_NOOP
`endif  // BR_ENABLE_IMPL_CHECKS

`ifdef BR_ENABLE_IMPL_CHECKS
`define BR_ASSERT_IN_RST_IMPL(__name__, __expr__) \
`BR_ASSERT_IN_RST(__name__, __expr__)
`else  // BR_ENABLE_IMPL_CHECKS
`define BR_ASSERT_IN_RST_IMPL(__name__, __expr__) \
`BR_NOOP
`endif  // BR_ENABLE_IMPL_CHECKS

`ifdef BR_ENABLE_IMPL_CHECKS
`define BR_ASSERT_IN_RST_C_IMPL(__name__, __expr__, __clk__) \
`BR_ASSERT_IN_RST_C(__name__, __expr__, __clk__)
`else  // BR_ENABLE_IMPL_CHECKS
`define BR_ASSERT_IN_RST_C_IMPL(__name__, __expr__, __clk__) \
`BR_NOOP
`endif  // BR_ENABLE_IMPL_CHECKS

////////////////////////////////////////////////////////////////////////////////
// Combinational assertion macros (evaluated continuously based on the expression sensitivity)
////////////////////////////////////////////////////////////////////////////////
`ifndef BR_DISABLE_INTG_CHECKS
`define BR_ASSERT_COMB_INTG(__name__, __expr__) \
`BR_ASSERT_COMB(__name__, __expr__)
`else  // BR_DISABLE_INTG_CHECKS
`define BR_ASSERT_COMB_INTG(__name__, __expr__) \
`BR_NOOP
`endif  // BR_DISABLE_INTG_CHECKS

`ifdef BR_ENABLE_IMPL_CHECKS
`define BR_ASSERT_COMB_IMPL(__name__, __expr__) \
`BR_ASSERT_COMB(__name__, __expr__)
`else  // BR_ENABLE_IMPL_CHECKS
`define BR_ASSERT_COMB_IMPL(__name__, __expr__) \
`BR_NOOP
`endif  // BR_ENABLE_IMPL_CHECKS

////////////////////////////////////////////////////////////////////////////////
// Concurrent cover macros (evaluated on posedge of a clock and disabled during a synchronous active-high reset)
////////////////////////////////////////////////////////////////////////////////

// Clock: 'clk'
// Reset: 'rst'
`ifndef BR_DISABLE_INTG_CHECKS
`define BR_COVER_INTG(__name__, __expr__) \
`BR_COVER(__name__, __expr__)
`else  // BR_DISABLE_INTG_CHECKS
`define BR_COVER_INTG(__name__, __expr__) \
`BR_NOOP
`endif  // BR_DISABLE_INTG_CHECKS

// More expressive form of BR_COVER_INTG that allows the use of custom clock and reset signal names.
`ifndef BR_DISABLE_INTG_CHECKS
`define BR_COVER_CR_INTG(__name__, __expr__, __clk__, __rst__) \
`BR_COVER_CR(__name__, __expr__, __clk__, __rst__)
`else  // BR_DISABLE_INTG_CHECKS
`define BR_COVER_CR_INTG(__name__, __expr__, __clk__, __rst__) \
`BR_NOOP
`endif  // BR_DISABLE_INTG_CHECKS

// Clock: 'clk'
// Reset: 'rst'
`ifdef BR_ENABLE_IMPL_CHECKS
`define BR_COVER_IMPL(__name__, __expr__) \
`BR_COVER(__name__, __expr__)
`else  // BR_ENABLE_IMPL_CHECKS
`define BR_COVER_IMPL(__name__, __expr__) \
`BR_NOOP
`endif  // BR_ENABLE_IMPL_CHECKS

// More expressive form of BR_COVER_IMPL that allows the use of custom clock and reset signal names.
`ifdef BR_ENABLE_IMPL_CHECKS
`define BR_COVER_CR_IMPL(__name__, __expr__, __clk__, __rst__) \
`BR_COVER_CR(__name__, __expr__, __clk__, __rst__)
`else  // BR_ENABLE_IMPL_CHECKS
`define BR_COVER_CR_IMPL(__name__, __expr__, __clk__, __rst__) \
`BR_NOOP
`endif  // BR_ENABLE_IMPL_CHECKS

////////////////////////////////////////////////////////////////////////////////
// Combinational cover macros (evaluated continuously based on the expression sensitivity)
////////////////////////////////////////////////////////////////////////////////
`ifndef BR_DISABLE_INTG_CHECKS
`define BR_COVER_COMB_INTG(__name__, __expr__) \
`BR_COVER_COMB(__name__, __expr__)
`else  // BR_DISABLE_INTG_CHECKS
`define BR_COVER_COMB_INTG(__name__, __expr__) \
`BR_NOOP
`endif // BR_DISABLE_INTG_CHECKS

`ifdef BR_ENABLE_IMPL_CHECKS
`define BR_COVER_COMB_IMPL(__name__, __expr__) \
`BR_COVER_COMB(__name__, __expr__)
`else  // BR_ENABLE_IMPL_CHECKS
`define BR_COVER_COMB_IMPL(__name__, __expr__) \
`BR_NOOP
`endif  // BR_ENABLE_IMPL_CHECKS

// verilog_format: on
// verilog_lint: waive-stop line-length
// ri lint_check_on LINE_LENGTH

`endif  // BR_ASSERTS_INTERNAL_SVH
