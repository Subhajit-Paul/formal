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



// Protocol condition assertions
property start_condition;
  @(posedge wb_clk_i)  disable iff (wb_rst_i || (arst_i == ARST_LVL))
  (cr[3] && scl_pad_o) |-> $fell(sda_pad_i);
endproperty
start_condition_assert: assert property (start_condition);

property TXR_Stability_v2;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  sr[3] |-> $stable(txr);
endproperty
TXR_Stability_v2_assert: assert property (TXR_Stability_v2);

property stop_condition;
  @(posedge wb_clk_i)  disable iff (wb_rst_i || (arst_i == ARST_LVL))
  (cr[2] && scl_pad_o) |-> $rose(sda_pad_i);
endproperty
stop_condition_assert: assert property (stop_condition);

// EN/IEN control checks
property p_en_clear_safety;
  @(posedge wb_clk_i) disable iff (wb_rst_i || (arst_i == ARST_LVL))
  ($fell(ctr[7]) && sr[3]) |-> ##[1:3] !sr[3];
endproperty
p_en_clear_safety_assert: assert property (p_en_clear_safety);

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


property inta_functionality_delayed;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  (ctr[1] && sr[4]) |=> wb_inta_o;
endproperty
inta_functionality_delayed_assert: assert property (inta_functionality_delayed);

property inta_arbitration_loss;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  $rose(sr[2]) && ctr[1] |=> ##[1:2] wb_inta_o;
endproperty
inta_arbitration_loss_assert: assert property (inta_arbitration_loss);
endmodule