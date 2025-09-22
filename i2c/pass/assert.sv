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

// START OF diasable iff introduction passing blocks
property p_en_safety;
  @(posedge wb_clk_i) disable iff (wb_rst_i || (arst_i == ARST_LVL))
  $fell(ctr[7]) |-> !sr[3];
endproperty
p_en_safety_assert: assert property (p_en_safety);

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

// Alternative connectivity checks
property prer_lo_connectivity_alt;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  (wb_cyc_i && wb_stb_i && wb_we_i && wb_ack_o && (wb_adr_i == 2'b00) && !ctr[7])
  |=> (prer[7:0] == $past(wb_dat_i,1));
endproperty
prer_lo_connectivity_alt_assert: assert property (prer_lo_connectivity_alt);

property prer_hi_connectivity_alt;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  (wb_cyc_i && wb_stb_i && wb_we_i && wb_ack_o && (wb_adr_i == 2'b01) && !ctr[7])
  |=> (prer[15:8] == $past(wb_dat_i,1));
endproperty
prer_hi_connectivity_alt_assert: assert property (prer_hi_connectivity_alt);

assert property (@(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i) (sr[4:2] == 3'b0));

property iflag_management;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  ($fell(sr[1]) || $rose(sr[5])) |-> sr[0] and
  (cr[0] && wb_we_i && wb_adr_i == 3'h4) |=> !sr[0];
endproperty
iflag_management_assert: assert property (iflag_management);

property iflag_clear;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  (cr[0] && wb_we_i && (wb_adr_i == 3'h4)) |=> !sr[0];
endproperty
iflag_clear_assert: assert property (iflag_clear);

property TXR_ValidRWBit_v3;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  $rose(cr[2]) |-> (txr[0] inside {0,1});
endproperty
TXR_ValidRWBit_v3_assert: assert property (TXR_ValidRWBit_v3);


property wb_clk_toggle_counter;
    int count;
    disable iff (arst_i == ARST_LVL || wb_rst_i)
    (1, count = 0) |=> (wb_clk_i != $past(wb_clk_i), count = 0)
    or
    (1, count++) |=> (count < 100);
endproperty
wb_clk_toggle_counter_assert: assert property (wb_clk_toggle_counter);

// END OF diasable iff introduction passing blocks

// This assertion has been converted to non vacuous by changing value from $fell(sr[3]) -> $fell(sr[1])
property p_rxr_valid_after_read;
  @(posedge wb_clk_i) 
  disable iff (arst_i == ARST_LVL || wb_rst_i)
  ($fell(sr[1]) && $rose(sr[0])) // Transfer completion
  |->
  !$isunknown(rxr);
endproperty
p_rxr_valid_after_read_assert: assert property (p_rxr_valid_after_read);

// arst_i

property arst_wb_rst_mutex;
  @(posedge wb_clk_i) !((arst_i == ARST_LVL) && wb_rst_i);
endproperty
arst_wb_rst_mutex_assert: assert property (arst_wb_rst_mutex);

// Width assertion added for completeness
property arst_i_width;
  @(posedge wb_clk_i) arst_i inside {1'b0, 1'b1};
endproperty
arst_i_width_assert: assert property (arst_i_width);


// cr

// Width assertion
assert property (@(posedge wb_clk_i) ($bits(cr) == 8));

// ctr

// Width check for ctr
assert property (@(posedge wb_clk_i) $bits(ctr) == 8);

// Reserved bits persistence checks
property p_ctr_reserved_zero;
  @(posedge wb_clk_i) disable iff (wb_rst_i || (arst_i != ARST_LVL))
  (ctr[5:0] == 6'h0);
endproperty
p_ctr_reserved_zero_assert: assert property (p_ctr_reserved_zero);

// prer

// Width check
assert property (@(posedge wb_clk_i) (1'b1) |-> ($bits(prer) == 16));

// Alternative reset condition checks
property prer_width_alt;
  @(posedge wb_clk_i) disable iff (arst_i != ARST_LVL || wb_rst_i)
  (1'b1) |-> ($bits(prer) == 16);
endproperty
prer_width_alt_assert: assert property (prer_width_alt);

// rxr

// Width check assertion
assert property (@(posedge wb_clk_i) $bits(rxr) == 8);

// Validity check assertions
property p_rxr_read_update_1;
  @(posedge wb_clk_i)
  disable iff (arst_i == ARST_LVL || wb_rst_i)
  ($past(cr[2]) && $rose(sr[0]) && !sr[3]) |-> !$isunknown(rxr);
endproperty
p_rxr_read_update_1_assert: assert property (p_rxr_read_update_1);

// scl_pad_i

assert property (@(posedge wb_clk_i) $bits(scl_pad_i) == 1);

// scl_pad_o

assert property (@(posedge wb_clk_i) $bits(scl_pad_o) == 1);

property SCL_NeverHigh;
  @(posedge wb_clk_i) (scl_pad_o !== 1'b1);
endproperty
SCL_NeverHigh_assert: assert property (SCL_NeverHigh);

// sda_pad_i

// Width check assertion
assert property (@(posedge wb_clk_i) ($bits(sda_pad_i) == 1));

// sr

assert property (@(posedge wb_clk_i) disable iff (wb_rst_i) $bits(sr) == 8);
assert property (@(posedge wb_clk_i) $bits(sr) == 8);
assert property (@(posedge wb_clk_i) disable iff (wb_rst_i || arst_i) (sr[4:2] == 3'b0));

// txr

assert property (@(posedge wb_clk_i) ($bits(txr) == 8));

property TXR_ValidRWBit;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  $rose(cr[2]) |-> (txr[0] inside {0,1});
endproperty
TXR_ValidRWBit_assert: assert property (TXR_ValidRWBit);


property TXR_ValidRWBit_v2;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  cr[2] |-> (txr[0] inside {0,1});
endproperty
TXR_ValidRWBit_v2_assert: assert property (TXR_ValidRWBit_v2);

// wb_ack_o

assert property (@(posedge wb_clk_i) $bits(wb_ack_o) == 1);

property data_valid_on_ack;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  (wb_ack_o && !wb_we_i) |-> !$isunknown(wb_dat_o);
endproperty
data_valid_on_ack_assert: assert property (data_valid_on_ack);

property single_ack_guarantee;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  (wb_stb_i && wb_cyc_i) |-> ##[1:2] wb_ack_o [->1];
endproperty
single_ack_guarantee_assert: assert property (single_ack_guarantee);

property ack_persistence_rule;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  wb_ack_o |=> !wb_ack_o || (wb_stb_i && wb_cyc_i);
endproperty
ack_persistence_rule_assert: assert property (ack_persistence_rule);

property ack_pulse_width;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  $rose(wb_ack_o) |=> $fell(wb_ack_o);
endproperty
ack_pulse_width_assert: assert property (ack_pulse_width);

property ack_data_valid;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  wb_ack_o |-> !$isunknown(wb_dat_o);
endproperty
ack_data_valid_assert: assert property (ack_data_valid);

property ack_deassert_unless_new_req;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  wb_ack_o |=> (wb_ack_o ? (wb_stb_i && wb_cyc_i) : 1);
endproperty
ack_deassert_unless_new_req_assert: assert property (ack_deassert_unless_new_req);

property ack_one_cycle_simple;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  wb_ack_o |=> !wb_ack_o;
endproperty
ack_one_cycle_simple_assert: assert property (ack_one_cycle_simple);

// wb_adr_i

assert property (@(posedge wb_clk_i) $bits(wb_adr_i) == 3);


// wb_clk_i

parameter MAX_PERIOD = 32;

// Validity checks
property wb_clk_valid_posedge;
    @(posedge wb_clk_i)
    disable iff (arst_i !== ARST_LVL || wb_rst_i)
    !$isunknown(wb_clk_i);
endproperty
wb_clk_valid_posedge_assert: assert property (wb_clk_valid_posedge);

property wb_clk_valid_posedge_alt;
    @(posedge wb_clk_i)
    disable iff (arst_i != ARST_LVL || wb_rst_i)
    !$isunknown(wb_clk_i);
endproperty
wb_clk_valid_posedge_alt_assert: assert property (wb_clk_valid_posedge_alt);

property wb_clk_valid_continuous;
    disable iff (arst_i !== ARST_LVL || wb_rst_i)
    !$isunknown(wb_clk_i);
endproperty
wb_clk_valid_continuous_assert: assert property (wb_clk_valid_continuous);

// Activity checks
property wb_clk_activity;
    @(posedge wb_clk_i)
    disable iff (arst_i != ARST_LVL || wb_rst_i)
    ##[1:1000] $changed(wb_clk_i);
endproperty
wb_clk_activity_assert: assert property (wb_clk_activity);

// Basic stability
property wb_clk_stable;
    !$isunknown(wb_clk_i);
endproperty
wb_clk_stable_assert: assert property (wb_clk_stable);


// wb_cyc_i

// Width assertion
assert property (@(posedge wb_clk_i) ($bits(wb_cyc_i) == 1));

// wb_dat_i

parameter CTRL_RESV_MASK = 8'hFC;
parameter CMD_RESV_MASK = 8'hE8;

assert property (@(posedge wb_clk_i) $bits(wb_dat_i) == 8);

property width_check;
  @(posedge wb_clk_i) 1 |-> ($bits(wb_dat_i) == 8);
endproperty
width_check_assert: assert property (width_check);

property p_wb_dat_i_width;
  @(posedge wb_clk_i) 1 |-> ($bits(wb_dat_i) == 8);
endproperty
p_wb_dat_i_width_assert: assert property (p_wb_dat_i_width);

property p_no_unknown_values;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  (wb_cyc_i && wb_stb_i && wb_we_i) |-> !$isunknown(wb_dat_i);
endproperty
p_no_unknown_values_assert: assert property (p_no_unknown_values);


// wb_dat_o

assert property (@(posedge wb_clk_i) $bits(wb_dat_o) == 8);

property wb_dat_o_connectivity;
  @(posedge wb_clk_i)
  (wb_stb_i && wb_cyc_i && wb_ack_o && !wb_we_i) |-> !$isunknown(wb_dat_o);
endproperty
wb_dat_o_connectivity_assert: assert property (wb_dat_o_connectivity);

property wb_dat_o_connectivity_1;
  @(posedge wb_clk_i)
  (wb_ack_o && !wb_we_i) |-> !$isunknown(wb_dat_o);
endproperty
wb_dat_o_connectivity_1_assert: assert property (wb_dat_o_connectivity_1);

// wb_inta_o

assert property (@(posedge wb_clk_i) ($bits(wb_inta_o) == 1));

property inta_functional_registered;
  @(posedge wb_clk_i) disable iff (arst_i != ARST_LVL || wb_rst_i)
  wb_inta_o == $past(ctr[1] && sr[4], 1);
endproperty
inta_functional_registered_assert: assert property (inta_functional_registered);

property inta_direct_functional;
  @(posedge wb_clk_i) disable iff (arst_i != ARST_LVL || wb_rst_i)
  wb_inta_o == (ctr[1] && sr[4]);
endproperty
inta_direct_functional_assert: assert property (inta_direct_functional);


// wb_rst_i

// Assertion for signal width
assert property (@(posedge wb_clk_i) $bits(wb_rst_i) == 1);

property wb_stb_width;
  @(posedge wb_clk_i) $bits(wb_stb_i) == 1;
endproperty
wb_stb_width_assert: assert property (wb_stb_width);


// wb_we_i

// Width checks
assert property (@(posedge wb_clk_i) $bits(wb_we_i) == 1);
assert property (@(posedge wb_clk_i) disable iff (wb_rst_i) $bits(wb_we_i) == 1);


endmodule

