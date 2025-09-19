// I2C Controller Assertions
// Based on Implementation Specification Document

module i2c_assertions (
    // WISHBONE signals
    input wire        wb_clk_i,
    input wire        wb_rst_i,
    input wire        arst_i,
    input wire [2:0]  wb_adr_i,
    input wire [7:0]  wb_dat_i,
    input wire [7:0]  wb_dat_o,
    input wire        wb_we_i,
    input wire        wb_stb_i,
    input wire        wb_cyc_i,
    input wire        wb_ack_o,
    input wire        wb_inta_o,

    // I2C signals
    input wire        scl_pad_i,
    input wire        scl_pad_o,
    input wire        scl_padoen_o,
    input wire        sda_pad_i,
    input wire        sda_pad_o,
    input wire        sda_padoen_o,
    input reg  [15:0] prer,
    input reg  [ 7:0] ctr,
    input reg  [ 7:0] txr,
    input wire [ 7:0] rxr,
    input reg  [ 7:0] cr,
    input wire [ 7:0] sr
);

        // parameters
        parameter ARST_LVL = 1'b0; // asynchronous reset level
        parameter MAX_PERIOD = 32;

// arst_i
// This assertion was initially passing vacuously due to sr[3] was checked in the pre condition. However, the specifican and the RTL says sr[3] is a reserved bit and its valuse will be ZERO. So changed sr[3] -> sr[1]. Though it failed, but vacuity is gone.
property TXR_NoWriteDuringTIP;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  sr[1] |-> !(wb_cyc_i && wb_stb_i && wb_we_i && (wb_adr_i == 3'h03));
endproperty
TXR_NoWriteDuringTIP_assert: assert property (TXR_NoWriteDuringTIP);
// This assertion was initially passing vacuously due to sr[3] was checked in the pre condition. However, the specifican and the RTL says sr[3] is a reserved bit and its valuse will be ZERO. So changed sr[3] -> sr[1]. Though it failed, but vacuity is gone.
property TXR_Stability;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  (sr[1] && $past(sr[1])) |-> $stable(txr);
endproperty
TXR_Stability_assert: assert property (TXR_Stability);

// This assertion was initially passing vacuously due to sr[3] was checked in the pre condition. However, the specifican and the RTL says sr[3] is a reserved bit and its valuse will be ZERO. So changed sr[3] -> sr[1]. Though it failed, but vacuity is gone.
property TXR_Stability_v2;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  sr[1] |-> $stable(txr);
endproperty
TXR_Stability_v2_assert: assert property (TXR_Stability_v2);

// This assertion was initially passing vacuously due to sr[3] was checked in the pre condition. However, the specifican and the RTL says sr[3] is a reserved bit and its valuse will be ZERO. So changed sr[3] -> sr[1]. Though it failed, but vacuity is gone.
property TXR_StabilityDuringTransfer;
  @(posedge wb_clk_i) disable iff (wb_rst_i || arst_i == ARST_LVL)
  (sr[1] && $past(sr[1])) |-> ($stable(txr));
endproperty
TXR_StabilityDuringTransfer_assert: assert property (TXR_StabilityDuringTransfer);

property arst_ctr_en;
  @(posedge wb_clk_i) (arst_i == ARST_LVL) |-> (ctr[7] == 1'b0);
endproperty
arst_ctr_en_assert: assert property (arst_ctr_en);

property arst_prer_reset;
  @(posedge wb_clk_i) (arst_i == ARST_LVL) |-> (prer == 16'hFFFF);
endproperty
arst_prer_reset_assert: assert property (arst_prer_reset);

property arst_txr_reset;
  @(posedge wb_clk_i) (arst_i == ARST_LVL) |-> (txr == 8'h00);
endproperty
arst_txr_reset_assert: assert property (arst_txr_reset);

property arst_rxr_reset;
  @(posedge wb_clk_i) (arst_i == ARST_LVL) |-> (rxr == 8'h00);
endproperty
arst_rxr_reset_assert: assert property (arst_rxr_reset);

property arst_status_bits;
  @(posedge wb_clk_i) (arst_i == ARST_LVL) |-> 
    (sr[5] == 0 &&  // BUSY
     sr[4] == 0 &&  // AL
     sr[3] == 0 &&  // TIP
     sr[0] == 0);   // IF
endproperty
arst_status_bits_assert: assert property (arst_status_bits);

property arst_inta;
  @(posedge wb_clk_i) (arst_i == ARST_LVL) |-> (wb_inta_o == 1'b0);
endproperty
arst_inta_assert: assert property (arst_inta);

property arst_ctr_reset;
  @(posedge wb_clk_i) (arst_i == ARST_LVL) |-> (ctr == 8'h00);
endproperty
arst_ctr_reset_assert: assert property (arst_ctr_reset);

property arst_cr_reset;
  @(posedge wb_clk_i) (arst_i == ARST_LVL) |-> (cr == 8'h00);
endproperty
arst_cr_reset_assert: assert property (arst_cr_reset);

property arst_status_reset;
  @(posedge wb_clk_i) (arst_i == ARST_LVL) |-> (sr == 8'h00);
endproperty
arst_status_reset_assert: assert property (arst_status_reset);

property arst_scl_sda_default;
  @(posedge wb_clk_i) (arst_i == ARST_LVL) |-> 
    (scl_pad_o == 1'b1 && sda_pad_o == 1'b1);
endproperty
arst_scl_sda_default_assert: assert property (arst_scl_sda_default);

property arst_ctr_reset_1;
  @(posedge wb_clk_i) (arst_i == ARST_LVL) |-> 
    (ctr[7] == 1'b0) &&    // EN bit cleared
    (ctr[6] == 1'b0) &&    // IEN bit cleared
    $stable(ctr[5:0]);      // Reserved bits unchanged
endproperty
arst_ctr_reset_1_assert: assert property (arst_ctr_reset_1);

// cr

property ReservedBitsConnectivity;
  @(posedge wb_clk_i) 
  (wb_adr_i == 4'h4 && wb_we_i && wb_cyc_i && wb_stb_i) |=> 
  (cr[2:1] == 2'b00);
endproperty
ReservedBitsConnectivity_assert: assert property (ReservedBitsConnectivity);

// Reset values
property CR_ResetValue_Async;
  @(posedge wb_clk_i) (arst_i == ARST_LVL) |-> (cr == 8'h00);
endproperty
CR_ResetValue_Async_assert: assert property (CR_ResetValue_Async);

property CR_ResetValue_Sync;
  @(posedge wb_clk_i) wb_rst_i |=> (cr == 8'h00);
endproperty
CR_ResetValue_Sync_assert: assert property (CR_ResetValue_Sync);

// Command auto-clearing
property CommandAutoClear;
  @(posedge wb_clk_i)
  (wb_adr_i == 4'h4 && wb_we_i && wb_cyc_i && wb_stb_i) |=> 
  (cr[7:4] == 4'b0 && cr[0] == 0);
endproperty
CommandAutoClear_assert: assert property (CommandAutoClear);

// Individual command bit clearing
property STA_AutoClear;
  @(posedge wb_clk_i) (wb_adr_i == 4'h4 && wb_we_i && wb_cyc_i && wb_stb_i && wb_dat_i[7]) |=> (cr[7] == 0);
endproperty
STA_AutoClear_assert: assert property (STA_AutoClear);

property STO_AutoClear;
  @(posedge wb_clk_i) (wb_adr_i == 4'h4 && wb_we_i && wb_cyc_i && wb_stb_i && wb_dat_i[6]) |=> (cr[6] == 0);
endproperty
STO_AutoClear_assert: assert property (STO_AutoClear);

property RD_AutoClear;
  @(posedge wb_clk_i) (wb_adr_i == 4'h4 && wb_we_i && wb_cyc_i && wb_stb_i && wb_dat_i[5]) |=> (cr[5] == 0);
endproperty
RD_AutoClear_assert: assert property (RD_AutoClear);

property WR_AutoClear;
  @(posedge wb_clk_i) (wb_adr_i == 4'h4 && wb_we_i && wb_cyc_i && wb_stb_i && wb_dat_i[4]) |=> (cr[4] == 0);
endproperty
WR_AutoClear_assert: assert property (WR_AutoClear);

property IACK_AutoClear;
  @(posedge wb_clk_i) (wb_adr_i == 4'h4 && wb_we_i && wb_cyc_i && wb_stb_i && wb_dat_i[0]) |=> (cr[0] == 0);
endproperty
IACK_AutoClear_assert: assert property (IACK_AutoClear);

// Interrupt handling
property IACK_ClearsInterrupt;
  @(posedge wb_clk_i) (wb_adr_i == 4'h4 && wb_we_i && wb_cyc_i && wb_stb_i && wb_dat_i[0]) |=> (sr[0] == 0);
endproperty
IACK_ClearsInterrupt_assert: assert property (IACK_ClearsInterrupt);

// ACK behavior
property ACK_ValidDuringRead;
  @(posedge wb_clk_i) (cr[3] && !cr[5]) |-> (sr[3] == 1);
endproperty
ACK_ValidDuringRead_assert: assert property (ACK_ValidDuringRead);

property ACK_StableDuringRead;
  @(posedge wb_clk_i) 
  (cr[5] && $past(cr[5])) |-> $stable(cr[3]);
endproperty
ACK_StableDuringRead_assert: assert property (ACK_StableDuringRead);

// Asynchronous reset coverage
property AsyncResetValue;
  @(posedge wb_clk_i) 
  (ARST_LVL == 0 && $fell(arst_i)) || (ARST_LVL == 1 && $rose(arst_i)) |-> (cr == 8'h00);
endproperty
AsyncResetValue_assert: assert property (AsyncResetValue);

// ctr

// Control register write connectivity checks
property p_ctr_write_connectivity;
  @(posedge wb_clk_i) disable iff (wb_rst_i || arst_i == ARST_LVL)
  (wb_we_i && wb_stb_i && wb_cyc_i && (wb_adr_i == 2'h02)) 
  |=> (ctr == (wb_dat_i & 8'hC0));
endproperty
p_ctr_write_connectivity_assert: assert property (p_ctr_write_connectivity);

property p_ctr_write_connectivity_ack;
  @(posedge wb_clk_i) disable iff (wb_rst_i || arst_i == ARST_LVL)
  (wb_we_i && wb_stb_i && wb_cyc_i && (wb_adr_i == 2'h02)) 
  ##1 (wb_ack_o)
  |=> (ctr == (wb_dat_i & 8'hC0));
endproperty
p_ctr_write_connectivity_ack_assert: assert property (p_ctr_write_connectivity_ack);


// EN/IEN control checks
property p_en_clear_safety;
  @(posedge wb_clk_i) disable iff (wb_rst_i || (arst_i == ARST_LVL))
  ($fell(ctr[7]) && sr[3]) |-> ##[1:3] !sr[3];
endproperty
p_en_clear_safety_assert: assert property (p_en_clear_safety);

property p_en_safety;
  @(posedge wb_clk_i) disable iff (wb_rst_i || (arst_i == ARST_LVL))
  $fell(ctr[7]) |-> !sr[3];
endproperty
p_en_safety_assert: assert property (p_en_safety);

property p_ien_interrupt;
  @(posedge wb_clk_i) disable iff (wb_rst_i || (arst_i == ARST_LVL))
  (ctr[6] && sr[0]) |-> wb_inta_o;
endproperty
p_ien_interrupt_assert: assert property (p_ien_interrupt);

// Reset behavior checks
property p_ctr_reset_sync;
  @(posedge wb_clk_i) $rose(wb_rst_i) |=> (ctr == 8'h00);
endproperty
p_ctr_reset_sync_assert: assert property (p_ctr_reset_sync);

property p_ctr_reset_async;
  @(posedge wb_clk_i) $changed(arst_i) && (arst_i == ARST_LVL) |=> (ctr == 8'h00);
endproperty
p_ctr_reset_async_assert: assert property (p_ctr_reset_async);

// General write check
property p_ctr_write;
  @(posedge wb_clk_i) disable iff (wb_rst_i || (arst_i != ARST_LVL))
  (wb_we_i && wb_stb_i && wb_cyc_i && (wb_adr_i == 2'h02)) |=> (ctr == (wb_dat_i & 8'hC0));
endproperty
p_ctr_write_assert: assert property (p_ctr_write);

// prer

// Connectivity properties
property prer_lo_connectivity;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  (wb_cyc_i && wb_stb_i && wb_we_i && wb_ack_o && (wb_adr_i == 2'b00) && !ctr[7])
  |=> (prer[7:0] == $past(wb_dat_i,1));
endproperty
prer_lo_connectivity_assert: assert property (prer_lo_connectivity);

property prer_hi_connectivity;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  (wb_cyc_i && wb_stb_i && wb_we_i && wb_ack_o && (wb_adr_i == 2'b01) && !ctr[7])
  |=> (prer[15:8] == $past(wb_dat_i,1));
endproperty
prer_hi_connectivity_assert: assert property (prer_hi_connectivity);

// Write ignore when enabled
property prer_write_ignore_en;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  (wb_cyc_i && wb_stb_i && wb_we_i && wb_ack_o && (wb_adr_i inside {2'b00, 2'b01}) && ctr[7])
  |=> (prer == $past(prer,1));
endproperty
prer_write_ignore_en_assert: assert property (prer_write_ignore_en);

// Stability properties
property prer_stability;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  !(wb_cyc_i && wb_stb_i && wb_we_i && wb_ack_o && (wb_adr_i inside {2'b00, 2'b01}))
  |=> (prer == $past(prer));
endproperty
prer_stability_assert: assert property (prer_stability);

// Reset behavior
property prer_reset;
  @(posedge wb_clk_i)
  (arst_i == ARST_LVL || wb_rst_i) |=> (prer == 16'hFFFF);
endproperty
prer_reset_assert: assert property (prer_reset);

// Alternative connectivity checks
property prer_lo_connectivity_alt;
  @(posedge wb_clk_i) disable iff (arst_i != ARST_LVL || wb_rst_i)
  (wb_cyc_i && wb_stb_i && wb_we_i && wb_ack_o && (wb_adr_i == 2'b00) && !ctr[7])
  |=> (prer[7:0] == $past(wb_dat_i,1));
endproperty
prer_lo_connectivity_alt_assert: assert property (prer_lo_connectivity_alt);

property prer_hi_connectivity_alt;
  @(posedge wb_clk_i) disable iff (arst_i != ARST_LVL || wb_rst_i)
  (wb_cyc_i && wb_stb_i && wb_we_i && wb_ack_o && (wb_adr_i == 2'b01) && !ctr[7])
  |=> (prer[15:8] == $past(wb_dat_i,1));
endproperty
prer_hi_connectivity_alt_assert: assert property (prer_hi_connectivity_alt);

// Deep reset check
property prescale_reset_val;
  @(posedge wb_clk_i) 
  (arst_i == ARST_LVL || $past(wb_rst_i)) |=> (prer == 16'hFFFF);
endproperty
prescale_reset_val_assert: assert property (prescale_reset_val);


// rxr


// Write protection assertions
property p_rxr_write_protect;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  (wb_adr_i == 3 && wb_we_i && wb_stb_i && wb_cyc_i) |-> (rxr == $past(rxr));
endproperty
p_rxr_write_protect_assert: assert property (p_rxr_write_protect);

property p_rxr_write_protect_1;
  @(posedge wb_clk_i) 
  disable iff (wb_rst_i || arst_i != !ARST_LVL)
  (wb_adr_i == 3 && wb_we_i && wb_stb_i && wb_cyc_i) 
  |=> 
  (rxr == $past(rxr));
endproperty
p_rxr_write_protect_1_assert: assert property (p_rxr_write_protect_1);

property p_rxr_write_protect_2;
  @(posedge wb_clk_i) disable iff (wb_rst_i || arst_i == ARST_LVL)
  (wb_adr_i == 3 && wb_we_i && wb_stb_i && wb_cyc_i) |=> (rxr == $past(rxr));
endproperty
p_rxr_write_protect_2_assert: assert property (p_rxr_write_protect_2);

property p_rxr_write_protect_3;
  @(posedge wb_clk_i) disable iff (wb_rst_i || arst_i != !ARST_LVL)
  (wb_adr_i == 3 && wb_we_i && wb_stb_i && wb_cyc_i) |=> (rxr == $past(rxr));
endproperty
p_rxr_write_protect_3_assert: assert property (p_rxr_write_protect_3);

// Reset assertions
property p_rxr_reset;
  @(posedge wb_clk_i) disable iff (arst_i != ARST_LVL)
  (arst_i == ARST_LVL || wb_rst_i) |=> (rxr == 8'h00);
endproperty
p_rxr_reset_assert: assert property (p_rxr_reset);

property p_rxr_reset_1;
  @(posedge wb_clk_i) 
  (arst_i == !ARST_LVL || $past(wb_rst_i)) 
  |=> 
  (rxr == 8'h00);
endproperty
p_rxr_reset_1_assert: assert property (p_rxr_reset_1);

property p_rxr_reset_2;
  @(posedge wb_clk_i) disable iff (arst_i == !ARST_LVL)
  (wb_rst_i) |=> (rxr == 8'h00);
endproperty
p_rxr_reset_2_assert: assert property (p_rxr_reset_2);

// Update/read assertions
property p_rxr_update_after_read;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  $rose(sr[0]) && !sr[3] |=> !$stable(rxr);
endproperty
p_rxr_update_after_read_assert: assert property (p_rxr_update_after_read);

property p_rxr_read_update;
  @(posedge wb_clk_i) disable iff (wb_rst_i || arst_i == ARST_LVL)
  ($past(cr[2]) && $rose(sr[0]) && !sr[3]) |-> (rxr != $past(rxr, 2));
endproperty
p_rxr_read_update_assert: assert property (p_rxr_read_update);

property p_rxr_update_after_read_1;
  @(posedge wb_clk_i) disable iff (wb_rst_i || arst_i != !ARST_LVL)
  $rose(sr[0]) && !sr[3] |=> !$stable(rxr);
endproperty
p_rxr_update_after_read_1_assert: assert property (p_rxr_update_after_read_1);

// sda_pad_i

// Protocol condition assertions
property start_condition;
  @(posedge wb_clk_i) disable iff (wb_rst_i)
  (cr[3] && scl_pad_o) |-> $fell(sda_pad_i);
endproperty
start_condition_assert: assert property (start_condition);

property stop_condition;
  @(posedge wb_clk_i) disable iff (wb_rst_i)
  (cr[2] && scl_pad_o) |-> $rose(sda_pad_i);
endproperty
stop_condition_assert: assert property (stop_condition);

// sr

assert property (@(posedge wb_clk_i) $fell(arst_i) |=> (sr == 8'h00));
assert property (@(posedge wb_clk_i) (sr[4:2] == 3'b0));

property sr_connectivity_2;
  @(posedge wb_clk_i) disable iff (wb_rst_i)
  (wb_cyc_i && wb_stb_i && !wb_we_i && (wb_adr_i == 3'h4)) 
  ##1 wb_ack_o |-> wb_dat_o == sr;
endproperty
sr_connectivity_2_assert: assert property (sr_connectivity_2);

property tip_lifecycle_1;
  @(posedge wb_clk_i) disable iff (wb_rst_i)
  (cr[3] || cr[2]) |=> sr[1] until_with $fell(sr[1]);
endproperty
tip_lifecycle_1_assert: assert property (tip_lifecycle_1);

property iflag_comprehensive_1;
  @(posedge wb_clk_i) disable iff (wb_rst_i)
  ($fell(sr[1]) or $rose(sr[5])) |-> sr[0];
endproperty
iflag_comprehensive_1_assert: assert property (iflag_comprehensive_1);

property sr_connectivity_1;
  @(posedge wb_clk_i) disable iff (wb_rst_i || arst_i == ARST_LVL)
  (wb_cyc_i && wb_stb_i && !wb_we_i && (wb_adr_i == 3'h4)) 
  ##1 wb_ack_o |-> wb_dat_o == sr;
endproperty
sr_connectivity_1_assert: assert property (sr_connectivity_1);

property tip_lifecycle_2;
  @(posedge wb_clk_i) disable iff (wb_rst_i || arst_i == ARST_LVL)
  (cr[3] || cr[2]) |=> sr[1] throughout (cr[3] || cr[2])[->1] 
  ##0 $fell(sr[1]);
endproperty
tip_lifecycle_2_assert: assert property (tip_lifecycle_2);

property iflag_comprehensive;
  @(posedge wb_clk_i) disable iff (wb_rst_i || arst_i == ARST_LVL)
  ($fell(sr[1]) or $rose(sr[5])) |-> sr[0] 
  until (wb_we_i && (wb_adr_i == 3'h4) && cr[0]);
endproperty
iflag_comprehensive_assert: assert property (iflag_comprehensive);

property rxack_phase_aligned;
  @(posedge wb_clk_i) disable iff (wb_rst_i || arst_i == ARST_LVL)
  (sr[1] && cr[3]) |-> 
  ##8 (scl_pad_i && !sr[1]) |-> $past(sda_pad_i,1) == !sr[7];
endproperty
rxack_phase_aligned_assert: assert property (rxack_phase_aligned);

property sr_connectivity;
  @(posedge wb_clk_i) disable iff (wb_rst_i)
  (wb_cyc_i && wb_stb_i && !wb_we_i && (wb_adr_i == 3'h4)) |-> (wb_dat_o == sr);
endproperty
sr_connectivity_assert: assert property (sr_connectivity);

property tip_lifecycle;
  @(posedge wb_clk_i) disable iff (wb_rst_i)
  (cr[3] || cr[2]) |-> ##[1:2] sr[1] and 
  (sr[1] until_with (sr[0] || sr[5]));
endproperty
tip_lifecycle_assert: assert property (tip_lifecycle);

property iflag_management;
  @(posedge wb_clk_i) disable iff (wb_rst_i)
  ($fell(sr[1]) || $rose(sr[5])) |-> sr[0] and
  (cr[0] && wb_we_i && wb_adr_i == 3'h4) |=> !sr[0];
endproperty
iflag_management_assert: assert property (iflag_management);

property tip_active;
  @(posedge wb_clk_i) disable iff (wb_rst_i)
  (cr[3] || cr[2]) |=> sr[1];
endproperty
tup_active_assert: assert property (tip_active);

property iflag_set;
  @(posedge wb_clk_i) disable iff (wb_rst_i)
  ($fell(sr[1]) || $rose(sr[5])) |-> sr[0];
endproperty
iflag_set_assert: assert property (iflag_set);

property iflag_clear;
  @(posedge wb_clk_i) disable iff (wb_rst_i)
  (cr[0] && wb_we_i && (wb_adr_i == 3'h4)) |=> !sr[0];
endproperty
iflag_clear_assert: assert property (iflag_clear);

property rxack_nack;
  @(posedge wb_clk_i) disable iff (wb_rst_i)
  $fell(sr[1]) |-> (sr[7] == !sda_pad_i);
endproperty
rxack_nack_assert: assert property (rxack_nack);

property rxack_phase_aligned_1;
  @(posedge wb_clk_i) disable iff (wb_rst_i || arst_i == ARST_LVL)
  (sr[1] && cr[3]) |-> $past(sda_pad_i,1) == !sr[7];
endproperty
rxack_phase_aligned_assert_1: assert property (rxack_phase_aligned_1);

// txr

property TXR_WriteConnectivity;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  (wb_cyc_i && wb_stb_i && wb_we_i && (wb_adr_i == 3'h03))
  |=> (txr == $past(wb_dat_i));
endproperty
TXR_WriteConnectivity_assert: assert property (TXR_WriteConnectivity);

property TXR_ResetValue;
  @(posedge wb_clk_i) (arst_i == ARST_LVL || wb_rst_i) |=> (txr == 8'h00);
endproperty
TXR_ResetValue_assert: assert property (TXR_ResetValue);

property TXR_NoWriteDuringTIP;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  sr[3] |-> !(wb_cyc_i && wb_stb_i && wb_we_i && (wb_adr_i == 3'h03));
endproperty
TXR_NoWriteDuringTIP_assert: assert property (TXR_NoWriteDuringTIP);

property TXR_Stability;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  (sr[3] && $past(sr[3])) |-> $stable(txr);
endproperty
TXR_Stability_assert: assert property (TXR_Stability);

property TXR_WriteConnectivity_v2;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  (wb_cyc_i && wb_stb_i && wb_we_i && (wb_adr_i == 3'h03)) ##1 wb_ack_o
  |-> (txr == $past(wb_dat_i,2));
endproperty
TXR_WriteConnectivity_v2_assert: assert property (TXR_WriteConnectivity_v2);

property TXR_ResetValue_v2;
  @(posedge wb_clk_i) (arst_i == ARST_LVL || wb_rst_i) |-> (txr == 8'h00);
endproperty
TXR_ResetValue_v2_assert: assert property (TXR_ResetValue_v2);

property TXR_Stability_v2;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  sr[3] |-> $stable(txr);
endproperty
TXR_Stability_v2_assert: assert property (TXR_Stability_v2);

property TXR_Connectivity;
  @(posedge wb_clk_i) disable iff (wb_rst_i || arst_i)
  (wb_cyc_i && wb_stb_i && wb_we_i && (wb_adr_i == 3'h03)) |=> (txr == $past(wb_dat_i));
endproperty
TXR_Connectivity_assert: assert property (TXR_Connectivity);

property TXR_ValidRWBit_v3;
  @(posedge wb_clk_i) disable iff (wb_rst_i || arst_i)
  $rose(cr[2]) |-> (txr[0] inside {0,1});
endproperty
TXR_ValidRWBit_v3_assert: assert property (TXR_ValidRWBit_v3);

property TXR_StabilityDuringTransfer;
  @(posedge wb_clk_i) disable iff (wb_rst_i || arst_i)
  (sr[3] && $past(sr[3])) |-> ($stable(txr));
endproperty
TXR_StabilityDuringTransfer_assert: assert property (TXR_StabilityDuringTransfer);

// wb_ack_o

property ack_after_request;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  (wb_stb_i && wb_cyc_i) |=> wb_ack_o;
endproperty
ack_after_request_assert: assert property (ack_after_request);

property ack_with_cyc;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  wb_ack_o |-> wb_cyc_i;
endproperty
ack_with_cyc_assert: assert property (ack_with_cyc);

property no_spurious_ack;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  wb_ack_o |-> $past(wb_stb_i && wb_cyc_i, 1);
endproperty
no_spurious_ack_assert: assert property (no_spurious_ack);

property ack_one_cycle;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  wb_ack_o |=> !wb_ack_o throughout (!(wb_stb_i && wb_cyc_i));
endproperty
ack_one_cycle_assert: assert property (ack_one_cycle);

property ack_reset;
  @(posedge wb_clk_i) 
  (arst_i == ARST_LVL || wb_rst_i) |-> !wb_ack_o;
endproperty
ack_reset_assert: assert property (ack_reset);

property ack_cyc_relationship;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  wb_ack_o |-> $past(wb_cyc_i, 1);
endproperty
ack_cyc_relationship_assert: assert property (ack_cyc_relationship);

property ack_reset_behavior;
  @(posedge wb_clk_i) 
  (arst_i == ARST_LVL || wb_rst_i) |-> ##[0:$] !wb_ack_o;
endproperty
ack_reset_behavior_assert: assert property (ack_reset_behavior);

property ack_causality;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  wb_ack_o |-> $past(wb_stb_i && wb_cyc_i, 2);
endproperty
ack_causality_assert: assert property (ack_causality);


// wb_adr_i

property address_stability;
  @(posedge wb_clk_i) disable iff (wb_rst_i || arst_i)
  (wb_stb_i && wb_cyc_i) |-> $stable(wb_adr_i) until wb_ack_o;
endproperty
address_stability_assert: assert property (address_stability);

property address_stability_2;
  @(posedge wb_clk_i) disable iff (arst_i || wb_rst_i)
  (wb_stb_i && wb_cyc_i) |-> ##[0:1] $stable(wb_adr_i) throughout (wb_cyc_i[->1] ##0 wb_ack_o);
endproperty
address_stability_2_assert: assert property (address_stability_2);

property address_stability_1;
  @(posedge wb_clk_i) disable iff (wb_rst_i || arst_i)
  (wb_stb_i && wb_cyc_i && !wb_ack_o) |=> $stable(wb_adr_i);
endproperty
address_stability_1_assert: assert property (address_stability_1);

// wb_clk_i

// Toggle checks
property wb_clk_toggle_stability;
    @(posedge wb_clk_i) 
    not (##[1:$] $stable(wb_clk_i));
endproperty
wb_clk_toggle_stability_assert: assert property (wb_clk_toggle_stability);

property wb_clk_toggle_counter;
    int count;
    disable iff (arst_i !== ARST_LVL || wb_rst_i)
    (1, count = 0) |=> (wb_clk_i != $past(wb_clk_i), count = 0)
    or
    (1, count++) |=> (count < 100);
endproperty
wb_clk_toggle_counter_assert: assert property (wb_clk_toggle_counter);

property wb_clk_toggle_window;
    @(wb_clk_i) 
    (wb_clk_i |-> ##[1:100] !wb_clk_i) and 
    (!wb_clk_i |-> ##[1:100] wb_clk_i);
endproperty
wb_clk_toggle_window_assert: assert property (wb_clk_toggle_window);

property wb_clk_toggle_period;
    @(posedge wb_clk_i) 
    disable iff (arst_i != ARST_LVL || wb_rst_i)
    (wb_clk_i |-> ##[1:MAX_PERIOD] !wb_clk_i) and
    (!wb_clk_i |-> ##[1:MAX_PERIOD] wb_clk_i);
endproperty
wb_clk_toggle_period_assert: assert property (wb_clk_toggle_period);


// wb_cyc_i

// Transaction timing assertions
assert property (@(posedge wb_clk_i) disable iff (wb_rst_i) !wb_cyc_i |-> !wb_ack_o);
assert property (@(posedge wb_clk_i) wb_rst_i |-> !wb_ack_o);

// Cycle validity assertions
property cyc_until_ack;
  @(posedge wb_clk_i) disable iff (wb_rst_i)
  (wb_cyc_i && wb_stb_i) |-> wb_cyc_i throughout (##[1:2] wb_ack_o);
endproperty
cyc_until_ack_assert: assert property (cyc_until_ack);

property no_cyc_toggle;
  @(posedge wb_clk_i) disable iff (wb_rst_i)
  $rose(wb_cyc_i) |-> wb_cyc_i until wb_ack_o;
endproperty
no_cyc_toggle_assert: assert property (no_cyc_toggle);

// Transaction timing properties
property exact_2cycle_txn;
  @(posedge wb_clk_i) disable iff (wb_rst_i)
  (wb_cyc_i && wb_stb_i) |-> ##2 wb_ack_o;
endproperty
exact_2cycle_txn_assert: assert property (exact_2cycle_txn);

property cyc_stb_until_ack;
  @(posedge wb_clk_i) disable iff (wb_rst_i)
  (wb_cyc_i && wb_stb_i) |=> (wb_cyc_i && wb_stb_i) ##1 wb_ack_o;
endproperty
cyc_stb_until_ack_assert: assert property (cyc_stb_until_ack);

// Stability properties
property input_stability;
  @(posedge wb_clk_i) disable iff (wb_rst_i)
  (wb_cyc_i && wb_stb_i) |-> 
    (wb_adr_i == $past(wb_adr_i,2)) and 
    (wb_dat_i == $past(wb_dat_i,2)) and
    (wb_we_i == $past(wb_we_i,2)) until wb_ack_o;
endproperty
input_stability_assert: assert property (input_stability);


// wb_dat_i

parameter CTRL_RESV_MASK = 8'hFC;
parameter CMD_RESV_MASK = 8'hE8;

property wb_dat_stable_until_ack;
  @(posedge wb_clk_i) disable iff (arst_i != ARST_LVL || wb_rst_i)
  (wb_we_i && wb_stb_i && wb_cyc_i) |-> 
    $stable(wb_dat_i) throughout (1'b1 [*1:$] ##0 wb_ack_o);
endproperty
wb_dat_stable_until_ack_assert: assert property (wb_dat_stable_until_ack);

property p_data_stability;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  (wb_cyc_i && wb_stb_i && wb_we_i) |-> 
  $stable(wb_dat_i) throughout (##[1:2] wb_ack_o);
endproperty
p_data_stability_assert: assert property (p_data_stability);


// wb_dat_o

property reset_values;
  @(posedge wb_clk_i)
  (arst_i == !ARST_LVL || wb_rst_i) |=> 
  (wb_dat_o == 8'hFF && wb_adr_i == 2'h00 ||  // PRERlo reset
   wb_dat_o == 8'hFF && wb_adr_i == 2'h01 ||  // PRERhi reset
   wb_dat_o == 8'h00);                        // Other registers
endproperty
reset_values_assert: assert property (reset_values);

property data_stability_3;
  @(posedge wb_clk_i)
  !wb_ack_o |=> $stable(wb_dat_o);
endproperty
data_stability_3_assert: assert property (data_stability_3);

property prer_accessibility;
  @(posedge wb_clk_i)
  (ctr[0] == 0 && wb_adr_i inside {2'h00,2'h01}) |-> 
  ##1 (wb_ack_o && wb_dat_o == (wb_adr_i[0] ? prer[15:8] : prer[7:0]));
endproperty
prer_accessibility_assert: assert property (prer_accessibility);

property PRERlo_read;
  @(posedge wb_clk_i)
  (wb_ack_o && $past(wb_adr_i,1) == 2'h00 && !wb_we_i) |-> (wb_dat_o == prer[7:0]);
endproperty
PRERlo_read_assert: assert property (PRERlo_read);

property PRERhi_read;
  @(posedge wb_clk_i)
  (wb_ack_o && $past(wb_adr_i,1) == 2'h01 && !wb_we_i) |-> (wb_dat_o == prer[15:8]);
endproperty
PRERhi_read_assert: assert property (PRERhi_read);

property CTR_read;
  @(posedge wb_clk_i)
  (wb_ack_o && $past(wb_adr_i,1) == 2'h02 && !wb_we_i) |-> (wb_dat_o == ctr);
endproperty
CTR_read_assert: assert property (CTR_read);

property RXR_read;
  @(posedge wb_clk_i)
  (wb_ack_o && $past(wb_adr_i,1) == 2'h03 && !wb_we_i) |-> (wb_dat_o == rxr);
endproperty
RXR_read_assert: assert property (RXR_read);

property SR_read;
  @(posedge wb_clk_i)
  (wb_ack_o && $past(wb_adr_i,1) == 2'h04 && !wb_we_i) |-> (wb_dat_o == sr);
endproperty
SR_read_assert: assert property (SR_read);

property reset_values_1;
  @(posedge wb_clk_i)
  (arst_i == !ARST_LVL || wb_rst_i) |=> 
  ((wb_adr_i == 2'h00 && wb_dat_o == 8'hFF) ||  // PRERlo reset
   (wb_adr_i == 2'h01 && wb_dat_o == 8'hFF) ||  // PRERhi reset
   (wb_dat_o == 8'h00));                        // Other registers
endproperty
reset_values_1_assert: assert property (reset_values_1);

property data_stability_4;
  @(posedge wb_clk_i)
  (!wb_ack_o && !wb_we_i) |=> $stable(wb_dat_o);
endproperty
data_stability_4_assert: assert property (data_stability_4);

property prer_accessibility_1;
  @(posedge wb_clk_i)
  (ctr[0] == 0 && wb_adr_i inside {2'h00,2'h01} && wb_stb_i && wb_cyc_i) |-> 
  ##1 (wb_ack_o && wb_dat_o == (wb_adr_i[0] ? prer[15:8] : prer[7:0]));
endproperty
prer_accessibility_1_assert: assert property (prer_accessibility_1);

property PRERlo_read_1;
  @(posedge wb_clk_i)
  (wb_ack_o && wb_adr_i == 2'h00 && !wb_we_i) |-> (wb_dat_o == prer[7:0]);
endproperty
PRERlo_read_1_assert: assert property (PRERlo_read_1);

property PRERhi_read_1;
  @(posedge wb_clk_i)
  (wb_ack_o && wb_adr_i == 2'h01 && !wb_we_i) |-> (wb_dat_o == prer[15:8]);
endproperty
PRERhi_read_1_assert: assert property (PRERhi_read_1);

property CTR_read_1;
  @(posedge wb_clk_i)
  (wb_ack_o && wb_adr_i == 2'h02 && !wb_we_i) |-> (wb_dat_o == ctr);
endproperty
CTR_read_1_assert: assert property (CTR_read_1);

property RXR_read_1;
  @(posedge wb_clk_i)
  (wb_ack_o && wb_adr_i == 2'h03 && !wb_we_i) |-> (wb_dat_o == rxr);
endproperty
RXR_read_1_assert: assert property (RXR_read_1);

property SR_read_1;
  @(posedge wb_clk_i)
  (wb_ack_o && wb_adr_i == 2'h04 && !wb_we_i) |-> (wb_dat_o == sr);
endproperty
SR_read_1_assert: assert property (SR_read_1);

property PRERlo_read_2;
  @(posedge wb_clk_i)
  (wb_ack_o && !wb_we_i) |-> (wb_dat_o == (
    ($past(wb_adr_i,1) == 3'h00) ? prer[7:0] :
    ($past(wb_adr_i,1) == 3'h01) ? prer[15:8] :
    ($past(wb_adr_i,1) == 3'h02) ? ctr :
    ($past(wb_adr_i,1) == 3'h04) ? rxr : 
    ($past(wb_adr_i,1) == 3'h06) ? sr : 8'h00
  ));
endproperty
PRERlo_read_2_assert: assert property (PRERlo_read_2);


// wb_inta_o

property inta_reset_stable;
  @(posedge wb_clk_i)
  (arst_i != ARST_LVL || wb_rst_i) |-> !wb_inta_o throughout (##[0:$] (arst_i == ARST_LVL && !wb_rst_i));
endproperty
inta_reset_stable_assert: assert property (inta_reset_stable);

property inta_iack_clear_fixed;
  @(posedge wb_clk_i) disable iff (arst_i != ARST_LVL || wb_rst_i)
  (wb_we_i && wb_stb_i && wb_cyc_i && 
   (wb_adr_i[2:0] == 3'h4) &&    // Command Register
   wb_dat_i[7] &&                 // IACK bit
   wb_dat_i[6:5] == 2'b0)         // Reserved bits
  |=> (ctr[1] && !sr[4]);         // IF cleared
endproperty
inta_iack_clear_fixed_assert: assert property (inta_iack_clear_fixed);

property inta_reset_sync;
  @(posedge wb_clk_i) wb_rst_i |-> !wb_inta_o;
endproperty
inta_reset_sync_assert: assert property (inta_reset_sync);

property inta_functionality;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  (ctr[1] && sr[4]) |-> wb_inta_o;
endproperty
inta_functionality_assert: assert property (inta_functionality);

property inta_persistence;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  (ctr[1] && sr[4]) |-> wb_inta_o throughout (ctr[1] && sr[4])[->1];
endproperty
inta_persistence_assert: assert property (inta_persistence);

property arbitration_loss_interrupt;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  sr[2] |-> sr[4];
endproperty
arbitration_loss_interrupt_assert: assert property (arbitration_loss_interrupt);

property inta_reset_connectivity;
  @(posedge wb_clk_i) 
  (arst_i == ARST_LVL || wb_rst_i) |-> !wb_inta_o;
endproperty
inta_reset_connectivity_assert: assert property (inta_reset_connectivity);

property inta_functionality_delayed;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  (ctr[1] && sr[4]) |=> wb_inta_o;
endproperty
inta_functionality_delayed_assert: assert property (inta_functionality_delayed);

property inta_iack_clear_timed;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  (wb_we_i && wb_stb_i && wb_cyc_i && (wb_adr_i == 3'h4) && wb_dat_i[7])
  ##1 wb_ack_o |=> !wb_inta_o && !sr[4];
endproperty
inta_iack_clear_timed_assert: assert property (inta_iack_clear_timed);

property inta_arbitration_loss;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  $rose(sr[2]) && ctr[1] |=> ##[1:2] wb_inta_o;
endproperty
inta_arbitration_loss_assert: assert property (inta_arbitration_loss);

property inta_deassert;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  $fell(ctr[1] || sr[4]) |=> !wb_inta_o;
endproperty
inta_deassert_assert: assert property (inta_deassert);

property inta_reset_combined;
  @(posedge wb_clk_i or posedge arst_i)
  (arst_i == ARST_LVL || wb_rst_i) |-> !wb_inta_o;
endproperty
inta_reset_combined_assert: assert property (inta_reset_combined);


// wb_rst_i

property wb_outputs_reset;
  @(posedge wb_clk_i) wb_rst_i |-> (wb_ack_o == 0 && wb_inta_o == 0);
endproperty
wb_outputs_reset_assert: assert property (wb_outputs_reset);

property prer_stable_reset;
  @(posedge wb_clk_i) $rose(wb_rst_i) |=> always (prer == 16'hFFFF) until (!wb_rst_i);
endproperty
prer_stable_reset_assert: assert property (prer_stable_reset);

property arbitration_lost_reset;
  @(posedge wb_clk_i) wb_rst_i |-> !sr[2];
endproperty
arbitration_lost_reset_assert: assert property (arbitration_lost_reset);

property wb_data_reset;
  @(posedge wb_clk_i) 
  wb_rst_i && !(wb_cyc_i && wb_stb_i) |-> wb_dat_o == 8'h00;
endproperty
wb_data_reset_assert: assert property (wb_data_reset);

property scl_data_reset;
  @(posedge wb_clk_i) wb_rst_i |-> scl_pad_o == 1'b0;
endproperty
scl_data_reset_assert: assert property (scl_data_reset);

property sda_data_reset;
  @(posedge wb_clk_i) wb_rst_i |-> sda_pad_o == 1'b0;
endproperty
sda_data_reset_assert: assert property (sda_data_reset);

// Register reset assertions
property CTR_Reset;
  @(posedge wb_clk_i) wb_rst_i |-> (ctr == 8'h00);
endproperty
CTR_Reset_assert: assert property (CTR_Reset);

property PRER_Reset;
  @(posedge wb_clk_i) wb_rst_i |-> (prer == 16'hFFFF);
endproperty
PRER_Reset_assert: assert property (PRER_Reset);

property SR_Reset;
  @(posedge wb_clk_i) wb_rst_i |-> (sr == 8'h00);
endproperty
SR_Reset_assert: assert property (SR_Reset);

property CR_Reset;
  @(posedge wb_clk_i) wb_rst_i |-> (cr == 8'h00);
endproperty
CR_Reset_assert: assert property (CR_Reset);

property TXR_Reset;
  @(posedge wb_clk_i) wb_rst_i |-> (txr == 8'h00);
endproperty
TXR_Reset_assert: assert property (TXR_Reset);

property RXR_Reset;
  @(posedge wb_clk_i) wb_rst_i |-> (rxr == 8'h00);
endproperty
RXR_Reset_assert: assert property (RXR_Reset);

// Alternative formulations
property p_reset_prescale_reg;
  @(posedge wb_clk_i)
  wb_rst_i |=> (prer == 16'hFFFF);
endproperty
p_reset_prescale_reg_assert: assert property (p_reset_prescale_reg);

property p_reset_busy_flag;
  @(posedge wb_clk_i)
  wb_rst_i |=> !sr[5];
endproperty
p_reset_busy_flag_assert: assert property (p_reset_busy_flag);


// wb_stb_i

property wb_stb_reset_inactive;
  @(posedge wb_clk_i) (wb_rst_i || (arst_i ^ ARST_LVL)) |-> !wb_stb_i;
endproperty
wb_stb_reset_inactive_assert: assert property (wb_stb_reset_inactive);

property wb_stb_ack_response;
  @(posedge wb_clk_i) (wb_stb_i && wb_cyc_i) |-> ##2 wb_ack_o;
endproperty
wb_stb_ack_response_assert: assert property (wb_stb_ack_response);

property wb_input_stability;
  @(posedge wb_clk_i) disable iff (wb_rst_i || (arst_i ^ ARST_LVL))
  (wb_stb_i && wb_cyc_i) |-> 
    ($stable(wb_adr_i) && $stable(wb_dat_i) && $stable(wb_we_i)) throughout ##[0:2] wb_ack_o;
endproperty
wb_input_stability_assert: assert property (wb_input_stability);

property wb_stb_retention;
  @(posedge wb_clk_i) disable iff (wb_rst_i || (arst_i ^ ARST_LVL))
  (wb_stb_i && wb_cyc_i) |-> wb_stb_i throughout ##2 wb_ack_o;
endproperty
wb_stb_retention_assert: assert property (wb_stb_retention);

wb_stb_reset_inactive
// wb_we_i


// Stability during transfers
property wb_we_stable_p;
  @(posedge wb_clk_i) disable iff (wb_rst_i)
  (wb_cyc_i && wb_stb_i) |-> $stable(wb_we_i) throughout (##1 wb_ack_o);
endproperty
wb_we_stable_p_assert: assert property (wb_we_stable_p);

property wb_we_stability_p;
  @(posedge wb_clk_i) disable iff (wb_rst_i || arst_i)
  (wb_cyc_i && wb_stb_i) |-> $stable(wb_we_i) throughout (wb_cyc_i && wb_stb_i) until wb_ack_o;
endproperty
wb_we_stability_p_assert: assert property (wb_we_stability_p);

property wb_we_stable_p_v3;
  @(posedge wb_clk_i) disable iff (wb_rst_i || arst_i)
  (wb_cyc_i && wb_stb_i) |-> $stable(wb_we_i) throughout (wb_cyc_i && wb_stb_i)[->1] ##0 wb_ack_o;
endproperty
wb_we_stable_p_v3_assert: assert property (wb_we_stable_p_v3);

// Write acknowledgment timing
property wb_write_ack_p;
  @(posedge wb_clk_i) disable iff (wb_rst_i)
  (wb_cyc_i && wb_stb_i && wb_we_i) |=> ##1 wb_ack_o;
endproperty
wb_write_ack_p_assert: assert property (wb_write_ack_p);

property wb_write_ack_p_v2;
  @(posedge wb_clk_i) disable iff (wb_rst_i || arst_i)
  (wb_cyc_i && wb_stb_i && wb_we_i) |=> ##1 wb_ack_o;
endproperty
wb_write_ack_p_v2_assert: assert property (wb_write_ack_p_v2);

// Reset behavior with wb_we_i
property wb_reset_block_p;
  @(posedge wb_clk_i)
  wb_rst_i |-> !(wb_cyc_i && wb_stb_i && wb_we_i && wb_ack_o);
endproperty
wb_reset_block_p_assert: assert property (wb_reset_block_p);

property wb_reset_write_ack_p;
  @(posedge wb_clk_i)
  wb_rst_i |-> !(wb_cyc_i && wb_stb_i && wb_we_i && wb_ack_o);
endproperty
wb_reset_write_ack_p_assert: assert property (wb_reset_write_ack_p);

endmodule

