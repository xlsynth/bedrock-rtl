// Copyright 2025 The Bedrock-RTL Authors
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

// Bedrock-RTL AXI4-Lite MSI Generator

`include "br_asserts.svh"
`include "br_registers.svh"

module br_amba_axil_msi_fpv_monitor #(
    parameter int AddrWidth = 40,  // must be at least 12
    parameter int DataWidth = 64,  // must be 32 or 64
    parameter int NumInterrupts = 2,  // must be at least 2
    parameter int DeviceIdWidth = 16,  // must be less than or equal to AddrWidth
    parameter int EventIdWidth = 16,  // must be less than or equal to DataWidth
    parameter int ThrottleCntrWidth = 16,  // must be at least 1
    localparam int StrobeWidth = (DataWidth + 7) / 8
) (
    input clk,
    input rst,  // Synchronous, active-high reset

    // Interrupt inputs
    input logic [NumInterrupts-1:0] irq,

    // MSI Configuration
    input logic [AddrWidth-1:0] msi_base_addr,
    input logic [NumInterrupts-1:0] msi_enable,
    input logic [NumInterrupts-1:0][DeviceIdWidth-1:0] device_id_per_irq,
    input logic [NumInterrupts-1:0][EventIdWidth-1:0] event_id_per_irq,

    // Throttle configuration
    input logic throttle_en,
    input logic [ThrottleCntrWidth-1:0] throttle_cntr_threshold,

    // Error output
    input logic error,

    // AXI4-Lite write-only initiator interface
    input logic [            AddrWidth-1:0] init_awaddr,
    input logic                             init_awvalid,
    input logic                             init_awready,
    input logic [            DataWidth-1:0] init_wdata,
    input logic [          StrobeWidth-1:0] init_wstrb,
    input logic                             init_wvalid,
    input logic                             init_wready,
    input logic [br_amba::AxiRespWidth-1:0] init_bresp,
    input logic                             init_bvalid,
    input logic                             init_bready
);

  // ----------FV assumptions----------
  `BR_ASSUME(throttle_en_stable_a, $stable(throttle_en))
  `BR_ASSUME(throttle_cntr_stable_a, $stable(throttle_cntr_threshold)
             && throttle_cntr_threshold != 'd0)
  `BR_ASSUME(msi_enable_stable_a, $stable(msi_enable))
  `BR_ASSUME(msi_base_addr_stable_a, $stable(msi_base_addr))
  `BR_ASSUME(device_id_stable_a, $stable(device_id_per_irq))
  `BR_ASSUME(event_id_stable_a, $stable(event_id_per_irq))

  // ----------FV assertions----------
  localparam int AddrWidthPadding = (AddrWidth - DeviceIdWidth) - 2;
  localparam int DataWidthPadding = DataWidth - EventIdWidth;
  localparam int EventIdStrobeWidth = 4;
  localparam int StrobeWidthPadding = StrobeWidth - EventIdStrobeWidth;

  logic [NumInterrupts-1:0][AddrWidth-1:0] fv_init_awaddr;
  logic [NumInterrupts-1:0][DataWidth-1:0] fv_init_wdata;
  logic [NumInterrupts-1:0][StrobeWidth-1:0] fv_init_wstrb;
  logic awaddr_match;
  logic wdata_match;
  logic wstrb_match;

  always_comb begin
    for (int i = 0; i < NumInterrupts; i++) begin
      fv_init_awaddr[i] = msi_base_addr + {{AddrWidthPadding{1'b0}}, device_id_per_irq[i], 2'b00};
      fv_init_wdata[i]  = {{DataWidthPadding{1'b0}}, event_id_per_irq[i]};
      fv_init_wstrb[i]  = {{StrobeWidthPadding{1'b0}}, {EventIdStrobeWidth{1'b1}}};
    end
  end

  // There is no 1-to-1 correspondence bwteen irq and AXI interface.
  // irq can drop before it's sent out at AXI interface.
  // as long as AXI won't send out spurious payload, it's fine
  always_comb begin
    awaddr_match = 1'b0;
    wdata_match  = 1'b0;
    wstrb_match  = 1'b0;
    for (int i = 0; i < NumInterrupts; i++) begin
      if (init_awvalid && (init_awaddr == fv_init_awaddr[i])) begin
        awaddr_match = 1'b1;
      end
      if (init_wvalid && (init_wdata == fv_init_wdata[i])) begin
        wdata_match = 1'b1;
      end
      if (init_wvalid && (init_wstrb == fv_init_wstrb[i])) begin
        wstrb_match = 1'b1;
      end
    end
  end

  // device_id/event_id encoding check
  `BR_ASSERT(awaddr_match_a, init_awvalid |-> awaddr_match)
  `BR_ASSERT(wdata_match_a, init_wvalid |-> wdata_match)
  `BR_ASSERT(wstrb_match_a, init_wvalid |-> wstrb_match)

  // throttle check
  logic [ThrottleCntrWidth-1:0] aw_throttle_cntr;
  logic [ThrottleCntrWidth-1:0] w_throttle_cntr;
  logic aw_in_progress;
  logic w_in_progress;

  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      aw_throttle_cntr <= 'd0;
    end else begin
      if ($rose(init_awvalid) & throttle_en) begin
        aw_throttle_cntr <= throttle_cntr_threshold - 'd1;
      end else begin
        aw_throttle_cntr <= aw_throttle_cntr != 'd0 ? aw_throttle_cntr - 'd1 : 'd0;
      end
    end
  end

  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      w_throttle_cntr <= 'd0;
    end else begin
      if ($rose(init_wvalid) & throttle_en) begin
        w_throttle_cntr <= throttle_cntr_threshold - 'd1;
      end else begin
        w_throttle_cntr <= w_throttle_cntr != 'd0 ? w_throttle_cntr - 'd1 : 'd0;
      end
    end
  end

  assign aw_in_progress = aw_throttle_cntr != 'd0;
  assign w_in_progress  = w_throttle_cntr != 'd0;

  `BR_ASSERT(awvalid_throttle_a, aw_in_progress |-> !$rose(init_awvalid))
  `BR_ASSERT(wvalid_throttle_a, w_in_progress |-> !$rose(init_wvalid))

  /*
   //______________________________________________________ABVIP USER DEFINED PARAMS
    bit CONFIG_CSR_INTERFACE    = 0,  // Set to 1: Enable ABVIP to connect with JasperGold App CSR-PA checker
    bit CONFIG_CSR_ADDR_ALIGN   = 0,  // Set to 1: Enable ABVIP to generate address aligned with CSR width
    bit CONFIG_CSR_FEED_EARLY_W = 0,  // Tune internal CSR logic behavior:
                                           // 0: Feed write data from buffer to CSR checker queue on B transaction
                                           // 1: Feed write data from buffer to CSR checker queue on W transaction
    bit CONFIG_CSR_FEED_ON_BVALID = 0, // Tune internal CSR logic behavior when CONFIG_CSR_FEED_EARLY_W = 0,
                                           // 0: Feed write data from buffer to CSR checker queue on write response channel "BVALID & BREADY" assertion
                                           // 1: Feed write data from buffer to CSR checker queue on write response channel "BVALID" assertion
    bit CONFIG_CSR_DISCARD_ON_ERROR = 0, // Tune internal CSR logic behavior to handle the error response (SLVERR/DECERR) scenarios,
                                             // 0: Erroneous read/write data will be send to CSR checker
                                             // 1: Read/Write behavior will be tuned according to below description,
                                                   // For Read: Discard the read data beat with error response to CSR checker
                                                   // For Write: Discard the all write data beat of the burst with error response to CSR checker when CONFIG_CSR_FEED_EARLY_W = 0,
    bit CONFIG_CSR_FEED_ON_RVALID = 0, //Tune internal CSR logic behaviour to provide csr_rd_valid on rvalid instead of rvalid && rready
    bit CONFIG_WAIT_FOR_VALID_BEFORE_READY = 0, // To enable *valid is asserted before *ready. Default value 0.

    bit AXI4_LITE               = 0,  // Set to 1: Enables to work in AXI4-Lite mode
    bit ALL_STROBES_HIGH_ON     = 0,  // Set to 1: All byte lanes are active
    bit ALLOW_SPARSE_STROBE     = 0,  // Set to 1: Allow wstrb bit to be 0 for active byte lanes
    `ifdef CDNS_AMBA5
    bit BARRIER_ON              = 0,  // DO NOT CHANGE for ACE5. Barrier transactions are not supported in ACE5 variants
    `else
    bit BARRIER_ON              = 1,  // Set to 0: Disable complete checking of barriers - ACE4
    `endif
    bit BYTE_STROBE_ON          = 0,  // Set to 1: WSTRB for active byte lanes enabled
    bit COVERAGE_ON             = 0,  // Set to 1: Enable functional covers
    bit CDNS_EXHAUSTIVE_COVER_ON = 0, // Set to 1: Enable exhaustive coverage on axi channels.
    bit DATA_BEFORE_CONTROL_ON  = 1,  // Set to 0: Disable data before control for write channel
    bit DATA_ACCEPT_WITH_OR_AFTER_CONTROL = 0,  // Set to 1: Enable slave to accept data after control
    bit DVM_ON                  = ARM_DSU_ON ? 1: 0,  // Set to 1: Enable distributed virtual messages (DVMv7) - ACE
                                      // ADDR_WIDTH should be 32 or more for DVM_ON
    bit DVM_V8                  = DVM_ON,  // Set to 1: Enable DVMv8 - ACE, Set Enable DVM_ON also to 1.
    bit EXCL_ACCESS_ON          = 0,  // Set to 1: Enable exclusive access
    bit EXCL_ACCESS_RD_RESP_OKAY_ALLOWED  = 1,  // Set to 0: Slave should only send EXOKAY response for valid exclusive read
    bit EXCL_ACCESS_SLAVE_ON              = 1,  // Set to 0: To disable exclusive access of slave
    bit EXCL_ACCESS_WRITE_MATCH_EX_READ   = 1,  // Set to 0: to enable the master to generate the illegal transactions in the exclusive access
    bit EXCL_ACCESS_WR_RESP_OKAY_ALLOWED  = 0,  // Set to 1: to allow that slave response can send EXOKAY or OKAY response in case of valid exclusive access
    bit BRIDGE_DUT              = 0, //Set to 1 if DUT is bridge across which ABVIP master and ABVIP slave are connected, and the DUT can cause order of transactions from master to slave change.
    bit LOW_POWER_ON            = ARM_DSU_ON ? 1: 0,  // Set to 1: Enable low power assertions

    int ID_WIDTH                = 2,  // Size of ID field. if you need separate read and write ID widths, use ID_WIDTH_RD and ID_WIDTH_WR.
    // NOTE: If (ID_WIDTH_RD == ID_WIDTH)/(ID_WIDTH_WR == ID_WIDTH), ID_WIDTH will be used
    // NOTE: If (ID_WIDTH_RD != ID_WIDTH)/(ID_WIDTH_WR != ID_WIDTH), those values will be used and ID_WIDTH will be IGNORED
    int ID_WIDTH_RD             = ARM_DSU_ON ? 9 : ID_WIDTH,  // Size of Read  ID field
    int ID_WIDTH_WR             = ARM_DSU_ON ? 8 : ID_WIDTH,  // Size of Write ID field

    int MAX_PENDING             = 2,  // Maximum pending read/write transactions
    int MAX_PENDING_WR          = ARM_DSU_ON ? 32 : MAX_PENDING,  // Maximum pending write transactions. For ARM DSU it is 32 if one cache slice is present or 96  if 2 cache slices are present.
    int MAX_PENDING_RD          = ARM_DSU_ON ? 34 : MAX_PENDING,  // Maximum pending read transactions. For ARM DSU it is 34 if one cache slice is present or 98 if 2 cache slices are present.
    int MAX_PENDING_BAR         = 2,    // Maximum pending barrier transactions           - ACE4
    int MAX_PENDING_DVM_SYNC    = 256,  // Maximum pending DVM Sync transactions          - ACE
    int MAX_PENDING_EXCL        = 2,    // Maximum pending exclusive access transactions
    int MAX_PENDING_SNOOP       = ARM_DSU_ON ? 9 : MAX_PENDING_RD,  // Maximum pending snoop transactions             - ACE4 and ACE5
    int MAXLEN                  = (AXI4_LITE || AXI5_LITE) ? 1 : CONFIG_CSR_INTERFACE ? 16 : 256, // Maximum Number of beats in a burst
    int MAXLEN_RD               = MAXLEN,
    int MAXLEN_WR               = MAXLEN,
    bit MAX_WAIT_CYCLES_ON      = 0,  // This parameter is deprecated and will be removed in future releases
    int MAX_WAIT_CYCLES_AW      = 0,  // Maximum wait cycles when AWREADY goes high after AWVALID
    int MAX_WAIT_CYCLES_W       = 0,  // Maximum wait cycles when WREADY  goes high after WVALID
    int MAX_WAIT_CYCLES_B       = 0,  // Maximum wait cycles when BREADY  goes high after BVALID
    int MAX_WAIT_CYCLES_AR      = 0,  // Maximum wait cycles when ARREADY goes high after ARVALID
    int MAX_WAIT_CYCLES_R       = 0,  // Maximum wait cycles when RREADY  goes high after RVALID
    int MAX_WAIT_CYCLES_AW_W    = 0, // Maximum wait cycles when write signals(WVALID/WREADY) go high after AWVALID
    int MAX_WAIT_CYCLES_W_AW    = 0, // Maximum wait cycles when write address signals(AWVALID/AWREADY) go high after WVALID
    int MAX_WAIT_CYCLES_AW_B    = 0, // This parameter has been deprecated and will be removed in future release
    int MAX_WAIT_CYCLES_W_B     = 0,  // Maximum wait cycles when write response goes high after WVALID
    int MAX_WAIT_CYCLES_AR_R    = 0, // Maximum wait cycles when read response goes high after ARVALID
   `ifdef CDNS_AMBA5_AXI
    int MAX_WAIT_CYCLES_AWAT_R  = 0, // Maximum wait cycles when read response goes high after AWATOP(load/swap/compare) with AWVALID
   `endif
    bit CONFIG_LIVENESS         = 1,  // Liveness properties will be created for the scenarios whose MAX_WAIT_CYCLES_* parameter is zero. Set to 0: Disable all liveness properties
    bit DEADLOCK_CHKS_ON        = 0,  // Liveness properties will be created for the scenarios whose MAX_WAIT_CYCLES_* parameter is zero. Set to 1: Enable all deadlock properties
  `ifdef CDNS_AMBA4_ACE               // Applicable for ACE4 and ACE5
    bit SINGLE_EXCL_MASTER      = 0,  // Set to 1: only single exclusive-capable master using interface.
    int MAX_WAIT_CYCLES_AC      = 0,  // Maximum wait cycles when ACREADY  goes high after ACVALID
    int MAX_WAIT_CYCLES_CR      = 0,  // Maximum wait cycles when CRREADY  goes high after CRVALID
    int MAX_WAIT_CYCLES_CD      = 0,  // Maximum wait cycles when CDREADY  goes high after CDVALID
    int MAX_WAIT_CYCLES_RACK    = 0,  // Maximum wait cycles when RACK goes high after read response
    int MAX_WAIT_CYCLES_WACK    = 0,  // Maximum wait cycles when WACK goes high after write response
    int MAX_WAIT_CYCLES_DVM_SYNC= 0,  // Maximum wait cycles when DVM sync is acknowledged
    int MAX_WAIT_CYCLES_AC_CR   = 0, // Maximum wait cycles when CRVALID goes high after ACVALID
    int MAX_WAIT_CYCLES_CR_CD   = 0, // Maximum wait cycles when CDVALID goes high after CRVALID with CRRESP[0]
  `endif
    bit READ_INTERLEAVE_ON      = 1,  // Set to 0: Disable interleaving of read data i.e. maintain RID ordering
    bit READ_RESP_IN_ORDER_ON   = 0,  // Set to 1: Enable read responses to come in order i.e. maintain RID ordering
    bit RST_CHECKS_ON           = 0,  // Set to 1: Enable AXI 4 reset checks
    bit WRITE_RESP_IN_ORDER_ON  = 0,  // Set to 1: Enable write responses to come in order i.e. maintain BID ordering
    bit RECM_CHECKS_EXCL_ON     = 1,  // Set to 1: Enable recommended exclusive checks
    bit RECM_CHECKS_ON          = 0,  // Set to 1: Enable recommended checks ony if the corresponding feature is set to 1.
    bit RECM_CHECKS_ALL_ON      = 0,  // Set to 1: Enable all recommended checks irrespective of corresponding feature parameter.
                                      // NOTE : Set this parameter carefully as few recommended check will be seen even when corresponding parameter is set to 0.
  `ifdef CDNS_AMBA4_ACE               // Applicable for ACE4 and ACE5
    bit ADDR_HAZARD_CHECKS_ON   = 0,  // Set to 1: Enable AXI4 ACE hazard checks
    bit HINT_MULTIPART          = 1,  // Set to 1: Enable Hint multipart message
                                      // Default value of the parameter changed to 1, in 11.30.044-s
    bit RECM_CHECKS_BARRIER_ON  = 0,  // Set to 1: Enable barrier recommended checks - ACE4 only
    bit RECM_CHECKS_DVM_ON      = 0,  // Set to 1: Enable dvm recommended checks
    bit ACK_TRANS_COMPLETE      = 0,  // Set to 1: Consider RACK/WACK as the end of the trasaction
                                      // This parameter is deprecated and no longer used in code.
    int ADDR_RANGE_CHECKS       = 0,  // Set to 1: To enable address range properties.
    int SHAREABLE_START_ADDR    = 0,
    int SHAREABLE_END_ADDR      = (10*CACHE_LINE_SIZE-1),
    int NONSHAREABLE_START_ADDR = (10*CACHE_LINE_SIZE),
    int NONSHAREABLE_END_ADDR   = (10*CACHE_LINE_SIZE)+5120,
    int SYSTEM_START_ADDR       = (10*CACHE_LINE_SIZE)+5121,
    bit CONFIG_SN_MI_NO_DAT     = 0,  // Set to 1: To enable the recommended behaviour of no data transfer for Makeinvalid snoop.
   `endif
    bit[2:0] BURST_TYPES = 3'b111, // This paramter is used to control the Burst checks.
                           //BURST_TYPES[0] : Set to 0,Disable the FIXED_BURST properties
                           //BURST_TYPES[1] : Set to 0,Disable the INCR_BURST properties
                           //BURST_TYPES[2] : Set to 0,Disable the WRAP_BURST properties

    bit CLK_CNTL_PRESENT        = 0,  // Set to 1: External Clock controller module present
    bit PROT_IN_OVERLAP         = 1,  // Set to 1: Consider prot value in overlapping address calculation
                                      // Default value of the parameter changed to 1, in 11.30.044-s
    bit CDNS_ABVIP_STOP_OVERFLOW= 1,  // Set to 0: Disable ABVIP assumptions to prevent table overflow
    bit CDNS_ABVIP_STOP_OVERFLOW_RD = CDNS_ABVIP_STOP_OVERFLOW,  // Set to 0: Disable ABVIP assumptions to prevent Read table overflow
    bit CDNS_ABVIP_STOP_OVERFLOW_WR = CDNS_ABVIP_STOP_OVERFLOW,  // Set to 0: Disable ABVIP assumptions to prevent Write table overflow
    bit CDNS_READY_OVFLOW_CHECKS= 1,  // Set to 0: Disable ABVIP assertion to prevent ready when table overflow
    bit CDNS_VALID_OVFLOW_CHECKS= 1,  // Set to 0: Disable ABVIP assertion to prevent valid when table overflow
    bit CDNS_ABVIP_SOFT_CONS_ON = 0,  // Set to 0: Disable assumptions required for ADS(search) Mode.
                                      // This parameter is deprecated and no longer used in code.
    bit READONLY_INTERFACE      = (MAX_PENDING_WR >=1) ? 0 : 1,  // Set to 1: Disable write interface
    bit WRITEONLY_INTERFACE     = (MAX_PENDING_RD >=1) ? 0 : 1,  // Set to 1: Disable read interface
    bit SNOOP_FILTER_PRESENT    = 0,  // Set to 1: Present snoop filter
    bit CCI400_MULTI_CACHE_LINE = 0,  // Set to 1: Apply CCI400 related assumption
    bit WREVICT_ON              = ARM_DSU_ON ? 1 : 0,  // Set to 1: To enable write evict transactions
    bit XCHECKS_ON              = 0,  // Set to 1: Enable ABVIP X-checks
    bit CONFIG_PARAM_CHECKS     = 1,  // Set to 0: Disable ABVIP parameter checks
    bit CONFIG_STABLE_CHECKS    = 1,  // Set to 0: Disable VALID & ~READY *_stable properties
    bit CONFIG_STABLE_CHECKS_AW = CONFIG_STABLE_CHECKS,  // Set to 0: Disable AWVALID & ~AWREADY *_stable properties
    bit CONFIG_STABLE_CHECKS_W  = CONFIG_STABLE_CHECKS,  // Set to 0: Disable WVALID & ~WREADY *_stable properties
    bit CONFIG_STABLE_CHECKS_B  = CONFIG_STABLE_CHECKS,  // Set to 0: Disable BVALID & ~BREADY *_stable properties
    bit CONFIG_STABLE_CHECKS_AR = CONFIG_STABLE_CHECKS,  // Set to 0: Disable ARVALID & ~ARREADY *_stable properties
    bit CONFIG_STABLE_CHECKS_R  = CONFIG_STABLE_CHECKS,  // Set to 0: Disable RVALID & ~RREADY *_stable properties
    bit CONFIG_RDATA_MASKED     = 1,  // Set to 0: RDATA X-propagation and stability properties apply to full RDATA
                                      // Set to 1: Properties apply to valid byte lanes only
    bit CONFIG_WDATA_MASKED     = 1,  // Set to 0: WDATA X-propagation and stability properties apply to full WDATA
                                      // Set to 1: Properties apply to valid byte lanes only
    bit CONFIG_RD_FULL_STRB     = 0,  // Set to 0: (default) Full read strobe not required
                                      // Set to 1: Full read strobes only

   `ifdef CDNS_AMBA4_ACE
    bit CDNS_ABVIP_STOP_OVERFLOW_SNP= CDNS_ABVIP_STOP_OVERFLOW,  // Set to 0: Disable ABVIP assumptions to prevent Snoop table overflow
    bit CONFIG_STABLE_CHECKS_AC     = CONFIG_STABLE_CHECKS,  // Set to 0: Disable ACVALID & ~ACREADY *_stable properties
    bit CONFIG_STABLE_CHECKS_CD     = CONFIG_STABLE_CHECKS,  // Set to 0: Disable CDVALID & ~CDREADY *_stable properties
    bit CONFIG_STABLE_CHECKS_CR     = CONFIG_STABLE_CHECKS,  // Set to 0: Disable CRALID & ~CRREADY *_stable properties
   `endif


  `ifdef CDNS_AMBA5
    bit CONFIG_NSAID                 = AXI5_LITE || ARM_DSU_ON ? 0 : 1, // Set to 0: Disable Non_secure Access Identifier checks   - AXI5 and ACE5
  `endif
  `ifdef CDNS_AMBA5_ACE
    bit DVM_V8_1                     = 1, // Set to 0: Disable DVMv8.1, Set DVM_ON and DVM_V8 also to 1. - ACE5
    bit CONFIG_CLEANSHAREDPERSIST    = ARM_DSU_ON ? 0 : 1, // Set to 0: Disable Cache Maintenance Operation           - ACE5
    bit CONFIG_SHAREABLE_DOMAIN_DEP  = CDNS_AMBA5_G ? 1'b0 : 1'b1, // Set to 0: Disable shareablity domain depreciation checks- ACE5
    bit CONFIG_LP_COHERENCY_CHKS     = 1, // Set to 0: Disable Coherency Connection Signaling
  `endif
  `ifdef CDNS_AMBA5_AXI
    bit CONFIG_ATOMIC_TRN            = AXI5_LITE ? 0 : 1, // Set to 0: Disable atomic transactions properties. Recommended to keep r/w id_width same and r/w user_width same. - AXI5. NOTE: Turn off atomic transactions while using CSR interface
  `endif
  `ifdef CDNS_AMBA5
    int MMUSID_WIDTH                 = 32, //Width of AxMMUSID signals
    int MMUSSID_WIDTH                = 20, //Width of AxMMUSSID signals
    int POISON_WIDTH                 = (DATA_WIDTH>64) ? DATA_WIDTH/64 : 1, // Poison bit width      - AXI5, AXI5-Lite and ACE5
    bit CONFIG_POISON_SIGNAL_CHKS    = ARM_DSU_ON ? 0 : 1, // Set to 0: Disable poison signaling checks               - AXI5, AXI5-Lite and ACE5
    bit CONFIG_DATA_CHK_SIGNAL_CHKS  = ARM_DSU_ON ? 0 : 1, // Set to 0: Disable data check signaling checks           - AXI5, AXI5-Lite and ACE5
    bit CONFIG_QOS_SIGNAL_CHKS       = AXI5_LITE || ARM_DSU_ON ? 0 : 1, // Set to 0: Disable QoS signaling checks  - AXI5 and ACE5
    int MAX_WAIT_CYCLES_QOSACCEPT    = 0, // Set to any integral value : deterministic maximum number of clock cycles taken to accept a transaction with qos level equal to or higher than va*qosaccept
                                          // Value of 0 means that property is disabled
    bit CONFIG_TRACE_SIGNAL_CHKS     = ARM_DSU_ON ? 0 : 1, // Set to 0: Disbale Trace signal checks                   - AXI5, AXI5-Lite and ACE5
    int LOOP_WIDTH                   = 8, //Width of awloop, bloop, arloop and rloop signals         - AXI5 and ACE5
    int LOOP_R_WIDTH                 = CDNS_AMBA5_H ? 8: LOOP_WIDTH , //Width of arloop and rloop signals         - AXI5-H and ACE5-H
    int LOOP_W_WIDTH                 = CDNS_AMBA5_H ? 8: LOOP_WIDTH , //Width of awloop, bloop signals            - AXI5-H and ACE5-H
    bit CONFIG_USER_LOOPBACK_CHKS    = AXI5_LITE || ARM_DSU_ON ? 0 : 1, // Set to 0: Disable User Loop Back signaling checks       - AXI5 and ACE5
    bit CONFIG_LP_WAKEUP_SIG_CHKS    = 1, // Set to 0: Disable Wakeup Signaling checks               - AXI5, AXI5-Lite and ACE5
  `endif

    bit CONFIG_MSG_ON                = 1,   // Set to 0: Disable the message printing
    bit CONFIG_SIMULATION            = 0,  // 0: normal, formal mode; 1: used in simulation
*/
  // AXI4-Lite write-only initiator interface
  axi4_slave #(
      .AXI4_LITE(1),
      .ADDR_WIDTH(AddrWidth),
      .DATA_WIDTH(DataWidth),
      .ALLOW_SPARSE_STROBE(1),
      .BYTE_STROBE_ON(1),
      .COVERAGE_ON(1),
      .CDNS_EXHAUSTIVE_COVER_ON(1)
  ) axi (
      // Global signals
      .aclk   (clk),
      .aresetn(!rst),
      .csysreq(1'b1),
      .csysack(1'b1),
      .cactive(1'b1),
      // Write Address Channel
      .awvalid(init_awvalid),
      .awready(init_awready),
      .awaddr (init_awaddr),
      .awprot ('d0),
      // Write Channel
      .wvalid (init_wvalid),
      .wready (init_wready),
      .wdata  (init_wdata),
      .wstrb  (init_wstrb),
      // Write Response channel
      .bvalid (init_bvalid),
      .bready (init_bready),
      .bresp  (init_bresp),
      // Read Address Channel
      .arvalid('d0),
      .arready('d0),
      // Read Channel
      .rvalid ('d0),
      .rready ('d0)
  );


endmodule : br_amba_axil_msi_fpv_monitor

bind br_amba_axil_msi br_amba_axil_msi_fpv_monitor #(
    .AddrWidth(AddrWidth),
    .DataWidth(DataWidth),
    .NumInterrupts(NumInterrupts),
    .DeviceIdWidth(DeviceIdWidth),
    .EventIdWidth(EventIdWidth),
    .ThrottleCntrWidth(ThrottleCntrWidth)
) monitor (.*);
