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

parameter CTRL_RESV_MASK = 8'hFC; 
parameter CMD_RESV_MASK = 8'hE8;
parameter ARST_LVL = 1'b0; // asynchronous reset level
parameter MAX_PERIOD = 32;

property p_rxr_valid_after_read;
  @(posedge wb_clk_i) 
  disable iff (arst_i == ARST_LVL || wb_rst_i)
  ($fell(sr[3]) && $rose(sr[0])) // Transfer completion
  |->
  !$isunknown(rxr);
endproperty
p_rxr_valid_after_read_assert: assert property (p_rxr_valid_after_read);


assert property (@(posedge wb_clk_i) disable iff (wb_rst_i || arst_i == ARST_LVL) $bits(wb_we_i) == 1);

assert property (@(posedge wb_clk_i) disable iff (wb_rst_i) $bits(wb_we_i) == 1);

// arst_i

assert property (@(posedge wb_clk_i) $fell(arst_i) |=> (sr == 8'h00));
assert property (@(posedge wb_clk_i) wb_rst_i |-> !wb_ack_o);

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


property CR_ResetValue_Async;
  @(posedge wb_clk_i) (arst_i == ARST_LVL) |-> (cr == 8'h00);
endproperty
CR_ResetValue_Async_assert: assert property (CR_ResetValue_Async);


property CR_ResetValue_Sync;
  @(posedge wb_clk_i) wb_rst_i |=> (cr == 8'h00);
endproperty
CR_ResetValue_Sync_assert: assert property (CR_ResetValue_Sync);


property STA_AutoClear;
  @(posedge wb_clk_i) disable iff (wb_rst_i || arst_i == ARST_LVL)
  (wb_adr_i == 4'h4 && wb_we_i && wb_cyc_i && wb_stb_i && wb_dat_i[7]) |=> (cr[7] == 0);
endproperty
STA_AutoClear_assert: assert property (STA_AutoClear);


property STO_AutoClear;
  @(posedge wb_clk_i) disable iff (wb_rst_i || arst_i == ARST_LVL)
  (wb_adr_i == 4'h4 && wb_we_i && wb_cyc_i && wb_stb_i && wb_dat_i[6]) |=> (cr[6] == 0);
endproperty
STO_AutoClear_assert: assert property (STO_AutoClear);


property RD_AutoClear;
  @(posedge wb_clk_i) disable iff (wb_rst_i || arst_i == ARST_LVL)
  (wb_adr_i == 4'h4 && wb_we_i && wb_cyc_i && wb_stb_i && wb_dat_i[5]) |=> (cr[5] == 0);
endproperty
RD_AutoClear_assert: assert property (RD_AutoClear);


property AsyncResetValue;
  @(posedge wb_clk_i) 
  (ARST_LVL == 0 && $fell(arst_i)) || (ARST_LVL == 1 && $rose(arst_i)) |-> (cr == 8'h00);
endproperty
AsyncResetValue_assert: assert property (AsyncResetValue);

// EN/IEN control checks
property p_en_clear_safety;
  @(posedge wb_clk_i) disable iff (wb_rst_i || (arst_i == ARST_LVL))
  ($fell(ctr[7]) && sr[3]) |-> ##[1:3] !sr[3];
endproperty
p_en_clear_safety_assert: assert property (p_en_clear_safety);


property p_ctr_reset_sync;
  @(posedge wb_clk_i) $rose(wb_rst_i) |=> (ctr == 8'h00);
endproperty
p_ctr_reset_sync_assert: assert property (p_ctr_reset_sync);


property p_ctr_reset_async;
  @(posedge wb_clk_i) $changed(arst_i) && (arst_i == ARST_LVL) |=> (ctr == 8'h00);
endproperty
p_ctr_reset_async_assert: assert property (p_ctr_reset_async);


property prer_reset;
  @(posedge wb_clk_i)
  (arst_i == ARST_LVL || wb_rst_i) |=> (prer == 16'hFFFF);
endproperty
prer_reset_assert: assert property (prer_reset);


property p_rxr_reset;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL)
  (arst_i == ARST_LVL || wb_rst_i) |=> (rxr == 8'h00);
endproperty
p_rxr_reset_assert: assert property (p_rxr_reset);


property p_rxr_reset_2;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL)
  (wb_rst_i) |=> (rxr == 8'h00);
endproperty
p_rxr_reset_2_assert: assert property (p_rxr_reset_2);

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


property TXR_ResetValue_v2;
  @(posedge wb_clk_i) (arst_i == ARST_LVL || wb_rst_i) |-> (txr == 8'h00);
endproperty
TXR_ResetValue_v2_assert: assert property (TXR_ResetValue_v2);


property TXR_Stability_v2;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  sr[3] |-> $stable(txr);
endproperty
TXR_Stability_v2_assert: assert property (TXR_Stability_v2);


property TXR_StabilityDuringTransfer;
  @(posedge wb_clk_i) disable iff (wb_rst_i || arst_i == ARST_LVL)
  (sr[3] && $past(sr[3])) |-> ($stable(txr));
endproperty
TXR_StabilityDuringTransfer_assert: assert property (TXR_StabilityDuringTransfer);


property ack_reset;
  @(posedge wb_clk_i) 
  (arst_i == ARST_LVL || wb_rst_i) |-> !wb_ack_o;
endproperty
ack_reset_assert: assert property (ack_reset);


property ack_reset_behavior;
  @(posedge wb_clk_i) 
  (arst_i == ARST_LVL || wb_rst_i) |-> ##[0:$] !wb_ack_o;
endproperty
ack_reset_behavior_assert: assert property (ack_reset_behavior);

// wb_dat_o

property reset_values;
  @(posedge wb_clk_i)
  (arst_i == ARST_LVL || wb_rst_i) |=> 
  (wb_dat_o == 8'hFF && wb_adr_i == 2'h00 ||  // PRERlo reset
   wb_dat_o == 8'hFF && wb_adr_i == 2'h01 ||  // PRERhi reset
   wb_dat_o == 8'h00);                        // Other registers
endproperty
reset_values_assert: assert property (reset_values);


property reset_values_1;
  @(posedge wb_clk_i) 
  (arst_i == ARST_LVL || wb_rst_i) |=> 
  ((wb_adr_i == 2'h00 && wb_dat_o == 8'hFF) ||  // PRERlo reset
   (wb_adr_i == 2'h01 && wb_dat_o == 8'hFF) ||  // PRERhi reset
   (wb_dat_o == 8'h00));                        // Other registers
endproperty
reset_values_1_assert: assert property (reset_values_1);


property inta_reset_stable;
  @(posedge wb_clk_i)
  (arst_i == ARST_LVL || wb_rst_i) |-> !wb_inta_o throughout (##[0:$] (arst_i == ARST_LVL && !wb_rst_i));
endproperty
inta_reset_stable_assert: assert property (inta_reset_stable);


property inta_iack_clear_fixed;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
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


property inta_reset_combined;
  @(posedge wb_clk_i or posedge arst_i)
  (arst_i == ARST_LVL || wb_rst_i) |-> !wb_inta_o;
endproperty
inta_reset_combined_assert: assert property (inta_reset_combined);


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


property wb_reset_block_p;
  @(posedge wb_clk_i) disable iff (wb_rst_i || arst_i == ARST_LVL)
  wb_rst_i |-> !(wb_cyc_i && wb_stb_i && wb_we_i && wb_ack_o);
endproperty
wb_reset_block_p_assert: assert property (wb_reset_block_p);


property wb_reset_write_ack_p;
  @(posedge wb_clk_i) disable iff (wb_rst_i || arst_i == ARST_LVL)
  wb_rst_i |-> !(wb_cyc_i && wb_stb_i && wb_we_i && wb_ack_o);
endproperty
wb_reset_write_ack_p_assert: assert property (wb_reset_write_ack_p);

endmodule