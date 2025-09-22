import re

def signal_in_consequent(sv_code: str, signal: str) -> bool:

    op = '|->' if '|->' in sv_code else '|=>' 
    parts = sv_code.split(op)

    consequent = parts[1]
    if signal in consequent:
        return True

    return False


sv_example = """
property prer_lo_connectivity;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  (wb_cyc_i && wb_stb_i && wb_we_i && wb_ack_o && (wb_adr_i == 2'b00) && !ctr[7])
  |=> (prer[7:0] == $past(wb_dat_i,1));
endproperty
prer_lo_connectivity_assert: assert property (prer_lo_connectivity);
"""

print(signal_in_consequent(sv_example, "wb_dat_i"))
print(signal_in_consequent(sv_example, "prer"))
print(signal_in_consequent(sv_example, "wb_rst_i"))  
