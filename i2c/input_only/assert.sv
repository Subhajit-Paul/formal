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

// cr

// Reserved bits handling
property ReservedBitsZero;
  @(posedge wb_clk_i) (wb_adr_i == 4'h4 && wb_we_i && wb_cyc_i && wb_stb_i) |-> (wb_dat_i[2:1] == 2'b00);
endproperty
ReservedBitsZero_assert: assert property (ReservedBitsZero);


// Command conflicts
property NoRD_WR_Conflict;
  @(posedge wb_clk_i) (wb_adr_i == 4'h4 && wb_we_i && wb_cyc_i && wb_stb_i) |-> !(wb_dat_i[5] && wb_dat_i[4]);
endproperty
NoRD_WR_Conflict_assert: assert property (NoRD_WR_Conflict);

property NoSTA_STO_Conflict;
  @(posedge wb_clk_i) (wb_adr_i == 4'h4 && wb_we_i && wb_cyc_i && wb_stb_i) |-> !(wb_dat_i[7] && wb_dat_i[6]);
endproperty
NoSTA_STO_Conflict_assert: assert property (NoSTA_STO_Conflict);

// ctr

property p_ctr_reserved_write;
  @(posedge wb_clk_i) disable iff (wb_rst_i || arst_i == ARST_LVL)
  (wb_we_i && wb_stb_i && wb_cyc_i && (wb_adr_i == 2'h02))
  |-> (wb_dat_i[5:0] == 6'h0);
endproperty
p_ctr_reserved_write_assert: assert property (p_ctr_reserved_write);


// scl_pad_i

property scl_high_during_start;
  @(posedge wb_clk_i) $fell(sda_pad_i) |-> scl_pad_i;
endproperty
scl_high_during_start_assert: assert property (scl_high_during_start);

property scl_high_during_stop;
  @(posedge wb_clk_i) $rose(sda_pad_i) |-> scl_pad_i;
endproperty
scl_high_during_stop_assert: assert property (scl_high_during_stop);



// sr

property rxack_validation;
  @(posedge wb_clk_i) disable iff (wb_rst_i)
  $fell(sr[1]) ##1 scl_pad_i[->1] |-> sr[7] == $past(sda_pad_i, 2);
endproperty
rxack_validation_assert: assert property (rxack_validation);


// wb_adr_i

property valid_address_range;
  @(posedge wb_clk_i) disable iff (wb_rst_i || arst_i)
  (wb_stb_i && wb_cyc_i) |-> (wb_adr_i inside {0,1,2,3,4});
endproperty
valid_address_range_assert: assert property (valid_address_range);

property valid_address_range_1;
  @(posedge wb_clk_i) disable iff (arst_i || wb_rst_i)
  (wb_stb_i && wb_cyc_i) |-> (wb_adr_i inside {[0:4]});
endproperty
valid_address_range_1_assert: assert property (valid_address_range_1);

property unused_address_bits;
    @(posedge wb_clk_i) disable iff (arst_i || wb_rst_i)
    (wb_stb_i && wb_cyc_i) |-> (wb_adr_i[2:0] <= 3'h5);
endproperty
unused_address_bits_assert: assert property (unused_address_bits);

// wb_cyc_i

// Connectivity assertions
assert property (@(posedge wb_clk_i) disable iff (wb_rst_i) wb_stb_i |-> wb_cyc_i);
assert property (@(posedge wb_clk_i) wb_stb_i |-> wb_cyc_i);


property addr_stability;
  @(posedge wb_clk_i) disable iff (wb_rst_i)
  (wb_cyc_i && wb_stb_i) |-> ##[1:2] $stable(wb_adr_i);
endproperty
addr_stability_assert: assert property (addr_stability);

property data_stability;
  @(posedge wb_clk_i) disable iff (wb_rst_i)
  (wb_cyc_i && wb_stb_i) |-> ##[1:2] $stable(wb_dat_i);
endproperty
data_stability_assert: assert property (data_stability);

property we_stability;
  @(posedge wb_clk_i) disable iff (wb_rst_i)
  (wb_cyc_i && wb_stb_i) |-> ##[1:2] $stable(wb_we_i);
endproperty
we_stability_assert: assert property (we_stability);


// wb_dat_i

parameter CTRL_RESV_MASK = 8'hFC;
parameter CMD_RESV_MASK = 8'hE8;

property ctrl_reg_reserved_bits;
  @(posedge wb_clk_i) disable iff (arst_i != ARST_LVL || wb_rst_i)
  (wb_adr_i == 3'h2 && wb_we_i && wb_stb_i && wb_cyc_i) |->
    (wb_dat_i & 8'hFC) == 0;
endproperty
ctrl_reg_reserved_bits_assert: assert property (ctrl_reg_reserved_bits);

property cmd_reg_reserved_bits;
  @(posedge wb_clk_i) disable iff (arst_i != ARST_LVL || wb_rst_i)
  (wb_adr_i == 3'h4 && wb_we_i && wb_stb_i && wb_cyc_i) |->
    (wb_dat_i & 8'hE8) == 0;
endproperty
cmd_reg_reserved_bits_assert: assert property (cmd_reg_reserved_bits);


property wb_dat_i_stable_during_write;
  @(posedge wb_clk_i) disable iff (wb_rst_i)
  (wb_we_i && wb_stb_i && wb_cyc_i) |-> $stable(wb_dat_i);
endproperty
wb_dat_i_stable_during_write_assert: assert property (wb_dat_i_stable_during_write);

property ctrl_reg_reserved_bits_zero;
  @(posedge wb_clk_i) disable iff (wb_rst_i)
  (wb_adr_i == 3'h2 && wb_we_i && wb_stb_i && wb_cyc_i) |-> (wb_dat_i[7:2] == 6'b0);
endproperty
ctrl_reg_reserved_bits_zero_assert: assert property (ctrl_reg_reserved_bits_zero);

property cmd_reg_reserved_bits_zero;
  @(posedge wb_clk_i) disable iff (wb_rst_i)
  (wb_adr_i == 3'h4 && wb_we_i && wb_stb_i && wb_cyc_i) |-> (wb_dat_i[7:5] == 3'b0 && wb_dat_i[3] == 1'b0);
endproperty
cmd_reg_reserved_bits_zero_assert: assert property (cmd_reg_reserved_bits_zero);


property p_ctrl_reg_reserved;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  (wb_adr_i == 3'h2 && wb_cyc_i && wb_stb_i && wb_we_i) |-> 
  (wb_dat_i & CTRL_RESV_MASK) == 8'h0;
endproperty
p_ctrl_reg_reserved_assert: assert property (p_ctrl_reg_reserved);

property p_cmd_reg_reserved;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  (wb_adr_i == 3'h4 && wb_cyc_i && wb_stb_i && wb_we_i) |-> 
  (wb_dat_i & CMD_RESV_MASK) == 8'h0;
endproperty
p_cmd_reg_reserved_assert: assert property (p_cmd_reg_reserved);

// wb_stb_i

property wb_stb_reset_inactive;
  @(posedge wb_clk_i) (wb_rst_i || (arst_i ^ ARST_LVL)) |-> !wb_stb_i;
endproperty
wb_stb_reset_inactive_assert: assert property (wb_stb_reset_inactive);

property wb_stb_cyc_connectivity;
  @(posedge wb_clk_i) wb_stb_i |-> wb_cyc_i;
endproperty
wb_stb_cyc_connectivity_assert: assert property (wb_stb_cyc_connectivity);

// wb_we_i


property wb_we_stable_p_v2;
  @(posedge wb_clk_i) disable iff (wb_rst_i)
  (wb_cyc_i && wb_stb_i) |-> $stable(wb_we_i) throughout (wb_cyc_i && wb_stb_i)[->1];
endproperty
wb_we_stable_p_v2_assert: assert property (wb_we_stable_p_v2);

endmodule

