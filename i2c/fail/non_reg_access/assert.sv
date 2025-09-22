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


property ack_cyc_relationship;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  wb_ack_o |-> $past(wb_cyc_i, 1);
endproperty
ack_cyc_relationship_assert: assert property (ack_cyc_relationship);


property ack_causality;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  wb_ack_o |-> $past(wb_stb_i && wb_cyc_i, 2);
endproperty
ack_causality_assert: assert property (ack_causality);


// wb_adr_i

property address_stability;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  (wb_stb_i && wb_cyc_i) |-> $stable(wb_adr_i) until wb_ack_o;
endproperty
address_stability_assert: assert property (address_stability);


property address_stability_2;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  (wb_stb_i && wb_cyc_i) |-> ##[0:1] $stable(wb_adr_i) throughout (wb_cyc_i[->1] ##0 wb_ack_o);
endproperty
address_stability_2_assert: assert property (address_stability_2);


property address_stability_1;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
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


property wb_clk_toggle_window;
    @(wb_clk_i) 
    (wb_clk_i |-> ##[1:100] !wb_clk_i) and 
    (!wb_clk_i |-> ##[1:100] wb_clk_i);
endproperty
wb_clk_toggle_window_assert: assert property (wb_clk_toggle_window);


property wb_clk_toggle_period;
    @(posedge wb_clk_i) 
    disable iff (arst_i == ARST_LVL || wb_rst_i)
    (wb_clk_i |-> ##[1:MAX_PERIOD] !wb_clk_i) and
    (!wb_clk_i |-> ##[1:MAX_PERIOD] wb_clk_i);
endproperty
wb_clk_toggle_period_assert: assert property (wb_clk_toggle_period);


// wb_cyc_i


// Transaction timing assertions
assert property (@(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i) !wb_cyc_i |-> !wb_ack_o);


// Cycle validity assertions
property cyc_until_ack;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  (wb_cyc_i && wb_stb_i) |-> wb_cyc_i throughout (##[1:2] wb_ack_o);
endproperty
cyc_until_ack_assert: assert property (cyc_until_ack);


property no_cyc_toggle;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  $rose(wb_cyc_i) |-> wb_cyc_i until wb_ack_o;
endproperty
no_cyc_toggle_assert: assert property (no_cyc_toggle);


// Transaction timing properties
property exact_2cycle_txn;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  (wb_cyc_i && wb_stb_i) |-> ##2 wb_ack_o;
endproperty
exact_2cycle_txn_assert: assert property (exact_2cycle_txn);


property cyc_stb_until_ack;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  (wb_cyc_i && wb_stb_i) |=> (wb_cyc_i && wb_stb_i) ##1 wb_ack_o;
endproperty
cyc_stb_until_ack_assert: assert property (cyc_stb_until_ack);


// Stability properties
property input_stability;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  (wb_cyc_i && wb_stb_i) |-> 
    (wb_adr_i == $past(wb_adr_i,2)) and 
    (wb_dat_i == $past(wb_dat_i,2)) and
    (wb_we_i == $past(wb_we_i,2)) until wb_ack_o;
endproperty
input_stability_assert: assert property (input_stability);

parameter CTRL_RESV_MASK = 8'hFC;
parameter CMD_RESV_MASK = 8'hE8;

property wb_dat_stable_until_ack;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
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

property data_stability_3;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  !wb_ack_o |=> $stable(wb_dat_o);
endproperty
data_stability_3_assert: assert property (data_stability_3);

property data_stability_4;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  (!wb_ack_o && !wb_we_i) |=> $stable(wb_dat_o);
endproperty
data_stability_4_assert: assert property (data_stability_4);

property wb_stb_ack_response;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i) (wb_stb_i && wb_cyc_i) |-> ##2 wb_ack_o;
endproperty
wb_stb_ack_response_assert: assert property (wb_stb_ack_response);

property wb_input_stability;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i) 
  (wb_stb_i && wb_cyc_i) |-> 
    ($stable(wb_adr_i) && $stable(wb_dat_i) && $stable(wb_we_i)) throughout ##[0:2] wb_ack_o;
endproperty
wb_input_stability_assert: assert property (wb_input_stability);

property wb_stb_retention;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i) 
  (wb_stb_i && wb_cyc_i) |-> wb_stb_i throughout ##2 wb_ack_o;
endproperty
wb_stb_retention_assert: assert property (wb_stb_retention);

// wb_we_i

// Stability during transfers
property wb_we_stable_p;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i) 
  (wb_cyc_i && wb_stb_i) |-> $stable(wb_we_i) throughout (##1 wb_ack_o);
endproperty
wb_we_stable_p_assert: assert property (wb_we_stable_p);

property wb_we_stability_p;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i) 
  (wb_cyc_i && wb_stb_i) |-> $stable(wb_we_i) throughout (wb_cyc_i && wb_stb_i) until wb_ack_o;
endproperty
wb_we_stability_p_assert: assert property (wb_we_stability_p);

property wb_we_stable_p_v3;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i) 
  (wb_cyc_i && wb_stb_i) |-> $stable(wb_we_i) throughout (wb_cyc_i && wb_stb_i)[->1] ##0 wb_ack_o;
endproperty
wb_we_stable_p_v3_assert: assert property (wb_we_stable_p_v3);

// Write acknowledgment timing
property wb_write_ack_p;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i) 
  (wb_cyc_i && wb_stb_i && wb_we_i) |=> ##1 wb_ack_o;
endproperty
wb_write_ack_p_assert: assert property (wb_write_ack_p);

property wb_write_ack_p_v2;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i) 
  (wb_cyc_i && wb_stb_i && wb_we_i) |=> ##1 wb_ack_o;
endproperty
wb_write_ack_p_v2_assert: assert property (wb_write_ack_p_v2);

endmodule