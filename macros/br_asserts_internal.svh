// Copyright 2024 Mark Gottscho
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

// Bedrock-internal macros for instantiating SystemVerilog Assertions (SVA).
// Not intended for use outside of Bedrock.
//
// Integration checks are intended to check a design's assumptions about its input stimulus.
// Implementation checks are intended to check a design's correctness given that its input assumptions
// are not violated.
//
// The macros in this file are guarded with two magic defines:
// * BR_DISABLE_INTG_CHECKS -- If set, then the integration checks will be disabled in the design.
// * BR_ENABLE_IMPL_CHECKS -- If set, then the implementation checks will be included in the design.
//
// The intent is that users should not need to set either define, so that by default they will get only
// the integration checks and not the implementation checks.
// The user should not need implementation checks because the Bedrock modules are pre-verified; omitting
// the checks speeds up tools and removes noisy covers that won't necessarily get hit in the user's design.

////////////////////////////////////////////////////////////////////////////////
// Concurrent assertion macros (evaluated on posedge of a clock and disabled during a reset)
////////////////////////////////////////////////////////////////////////////////

// Clock: 'clk'
// Reset: 'rst'
`define BR_ASSERT_INTG(__name__, __expr__) \
`ifndef BR_DISABLE_INTG_CHECKS \
`BR_ASSERT(__name__, __expr__) \
`endif

// More expressive form of BR_ASSERT_INTG that allows the use of custom clock and reset signal names.
`define BR_ASSERT_CR_INTG(__name__, __expr__, __clk__, __rst__) \
`ifdef BR_DISABLE_INTG_CHECKS \
`BR_ASSERT_CR(__name__, __expr__, __clk__, __rst__) \
`endif

// Clock: 'clk'
// Reset: 'rst'
`define BR_ASSERT_IMPL(__name__, __expr__) \
`ifndef BR_ENABLE_IMPL_CHECKS \
`BR_ASSERT(__name__, __expr__) \
`endif

// More expressive form of BR_ASSERT_IMPL that allows the use of custom clock and reset signal names.
`define BR_ASSERT_CR_IMPL(__name__, __expr__, __clk__, __rst__) \
`ifdef BR_ENABLE_IMPL_CHECKS \
`BR_ASSERT_CR(__name__, __expr__, __clk__, __rst__) \
`endif

////////////////////////////////////////////////////////////////////////////////
// Combinational assertion macros (evaluated continuously based on the expression sensitivity)
////////////////////////////////////////////////////////////////////////////////
`define BR_ASSERT_COMB_INTG(__name__, __expr__) \
`ifndef BR_DISABLE_INTG_CHECKS \
`BR_ASSERT_COMB(__name__, __expr__) \
`endif

`define BR_ASSERT_COMB_IMPL(__name__, __expr__) \
`ifdef BR_ENABLE_IMPL_CHECKS \
`BR_ASSERT_COMB(__name__, __expr__) \
`endif

////////////////////////////////////////////////////////////////////////////////
// Concurrent cover macros (evaluated on posedge of a clock and disabled during a reset)
////////////////////////////////////////////////////////////////////////////////

// Clock: 'clk'
// Reset: 'rst'
`define BR_COVER_INTG(__name__, __expr__) \
`ifndef BR_DISABLE_INTG_CHECKS \
`BR_COVER(__name__, __expr__) \
`endif

// More expressive form of BR_COVER_INTG that allows the use of custom clock and reset signal names.
`define BR_COVER_CR_INTG(__name__, __expr__, __clk__, __rst__) \
`ifdef BR_DISABLE_INTG_CHECKS \
`BR_COVER_CR(__name__, __expr__, __clk__, __rst__) \
`endif

// Clock: 'clk'
// Reset: 'rst'
`define BR_COVER_IMPL(__name__, __expr__) \
`ifndef BR_ENABLE_IMPL_CHECKS \
`BR_COVER(__name__, __expr__) \
`endif

// More expressive form of BR_COVER_IMPL that allows the use of custom clock and reset signal names.
`define BR_COVER_CR_IMPL(__name__, __expr__, __clk__, __rst__) \
`ifdef BR_ENABLE_IMPL_CHECKS \
`BR_COVER_CR(__name__, __expr__, __clk__, __rst__) \
`endif

////////////////////////////////////////////////////////////////////////////////
// Combinational cover macros (evaluated continuously based on the expression sensitivity)
////////////////////////////////////////////////////////////////////////////////
`define BR_COVER_COMB_INTG(__name__, __expr__) \
`ifndef BR_DISABLE_INTG_CHECKS \
`BR_COVER_COMB(__name__, __expr__) \
`endif

`define BR_COVER_COMB_IMPL(__name__, __expr__) \
`ifdef BR_ENABLE_IMPL_CHECKS \
`BR_COVER_COMB(__name__, __expr__) \
`endif

`endif // BR_ASSERTS_INTERNAL_SVH
