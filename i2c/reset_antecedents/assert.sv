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

// Reset values
property CR_ResetValue_Async;
  @(posedge wb_clk_i) (arst_i == ARST_LVL) |-> (cr == 8'h00);
endproperty
CR_ResetValue_Async_assert: assert property (CR_ResetValue_Async);

property CR_ResetValue_Sync;
  @(posedge wb_clk_i) wb_rst_i |=> (cr == 8'h00);
endproperty
CR_ResetValue_Sync_assert: assert property (CR_ResetValue_Sync);

// Asynchronous reset coverage
property AsyncResetValue;
  @(posedge wb_clk_i) 
  (ARST_LVL == 0 && $fell(arst_i)) || (ARST_LVL == 1 && $rose(arst_i)) |-> (cr == 8'h00);
endproperty
AsyncResetValue_assert: assert property (AsyncResetValue);

// Reset behavior checks
property p_ctr_reset_sync;
  @(posedge wb_clk_i) $rose(wb_rst_i) |=> (ctr == 8'h00);
endproperty
p_ctr_reset_sync_assert: assert property (p_ctr_reset_sync);

property p_ctr_reset_async;
  @(posedge wb_clk_i) $changed(arst_i) && (arst_i == ARST_LVL) |=> (ctr == 8'h00);
endproperty
p_ctr_reset_async_assert: assert property (p_ctr_reset_async);

// Reset behavior
property prer_reset;
  @(posedge wb_clk_i)
  (arst_i == ARST_LVL || wb_rst_i) |=> (prer == 16'hFFFF);
endproperty
prer_reset_assert: assert property (prer_reset);

// Not in vacuous passes
// Deep reset check
property prescale_reset_val;
  @(posedge wb_clk_i) 
  (arst_i == ARST_LVL || $past(wb_rst_i)) |=> (prer == 16'hFFFF);
endproperty
prescale_reset_val_assert: assert property (prescale_reset_val);

// Reset assertions
property p_rxr_reset;
  @(posedge wb_clk_i) disable iff (arst_i != ARST_LVL)
  (arst_i == ARST_LVL || wb_rst_i) |=> (rxr == 8'h00);
endproperty
p_rxr_reset_assert: assert property (p_rxr_reset);

// Not in vacuous passes
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

assert property (@(posedge wb_clk_i) $fell(arst_i) |=> (sr == 8'h00));

property TXR_ResetValue;
  @(posedge wb_clk_i) (arst_i == ARST_LVL || wb_rst_i) |=> (txr == 8'h00);
endproperty
TXR_ResetValue_assert: assert property (TXR_ResetValue);

property TXR_ResetValue_v2;
  @(posedge wb_clk_i) (arst_i == ARST_LVL || wb_rst_i) |-> (txr == 8'h00);
endproperty
TXR_ResetValue_v2_assert: assert property (TXR_ResetValue_v2);


property ack_reset;
  @(posedge wb_clk_i) 
  (arst_i == ARST_LVL || wb_rst_i) |-> !wb_ack_o;
endproperty
ack_reset_assert: assert property (ack_reset);

assert property (@(posedge wb_clk_i) wb_rst_i |-> !wb_ack_o);

property ack_reset_behavior;
  @(posedge wb_clk_i) 
  (arst_i == ARST_LVL || wb_rst_i) |-> ##[0:$] !wb_ack_o;
endproperty
ack_reset_behavior_assert: assert property (ack_reset_behavior);

// Cycle validity assertions

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
  (arst_i != ARST_LVL || wb_rst_i) |-> !wb_inta_o throughout (##[0:$] (arst_i == ARST_LVL && !wb_rst_i));
endproperty
inta_reset_stable_assert: assert property (inta_reset_stable);

property inta_reset_sync;
  @(posedge wb_clk_i) wb_rst_i |-> !wb_inta_o;
endproperty
inta_reset_sync_assert: assert property (inta_reset_sync);

property inta_reset_connectivity;
  @(posedge wb_clk_i) 
  (arst_i == ARST_LVL || wb_rst_i) |-> !wb_inta_o;
endproperty
inta_reset_connectivity_assert: assert property (inta_reset_connectivity);

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
// Not in vacuous passes
property wb_stb_reset_inactive;
  @(posedge wb_clk_i) (wb_rst_i || (arst_i ^ ARST_LVL)) |-> !wb_stb_i;
endproperty
wb_stb_reset_inactive_assert: assert property (wb_stb_reset_inactive);

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

