// SPDX-License-Identifier: Apache-2.0

package br_cdc_pkg;

  typedef enum logic [1:0] {
    CdcDelayNone = 2'b00,
    CdcDelayAlways = 2'b01,
    CdcDelayRandOnce = 2'b10,
    CdcDelayRandAlways = 2'b11
  } cdc_delay_mode_t;

  cdc_delay_mode_t cdc_delay_mode = CdcDelayNone;

endpackage
