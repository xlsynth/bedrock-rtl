// SPDX-License-Identifier: Apache-2.0

typedef class br_dv_clk_rst_driver;
typedef class br_dv_agent;
typedef class br_dv_env;
typedef class br_dv_component;
typedef class br_dv_context;
typedef class br_dv_sequence_base;
typedef class br_dv_test;
typedef class br_item;

typedef enum int {
  BrDvComponent,
  BrDvDriver,
  BrDvMonitor,
  BrDvScoreboard,
  BrDvSequence,
  BrDvAgent
} br_dv_component_kind_e;
