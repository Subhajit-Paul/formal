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
  (cr[7] && scl_pad_o) |-> $fell(sda_pad_i);
endproperty
start_condition_assert: assert property (start_condition);

property stop_condition;
  @(posedge wb_clk_i)  disable iff (wb_rst_i || (arst_i == ARST_LVL))
  (cr[6] && scl_pad_o) |-> $rose(sda_pad_i);
endproperty
stop_condition_assert: assert property (stop_condition);




endmodule