import re

def extract_antecedent(assertion: str) -> str:
    assertion = re.sub(r"^\s*assert\s+property\s*\(", "", assertion)
    assertion = re.sub(r"\);\s*$", "", assertion).strip()
    assertion = re.sub(r"@\([^)]*\)", "", assertion)
    assertion = re.sub(r"disable\s+iff\s*\([^)]*\)", "", assertion)
    parts = re.split(r"\|\-\>|\|\=\>", assertion, maxsplit=1)
    
    if not parts:
        return ""
    
    return parts[0].strip()


def signal_in_antecedent(assertion: str, signal: str) -> bool:
    antecedent = extract_antecedent(assertion)
    return bool(re.search(rf"\b{re.escape(signal)}\b", antecedent))


a1 = "assert property (@(posedge clk) disable iff (!reset_n) req |-> ##1 gnt);"
a2 = "assert property (@(posedge clk) disable iff (reset || soft_reset) (req && valid) |-> ##1 gnt);"
a3 = """
property prer_lo_connectivity;
  @(posedge wb_clk_i) disable iff (arst_i == ARST_LVL || wb_rst_i)
  (wb_cyc_i && wb_stb_i && wb_we_i && wb_ack_o && (wb_adr_i == 2'b00) && !ctr[7])
  |=> (prer[7:0] == $past(wb_dat_i,1));
endproperty
prer_lo_connectivity_assert: assert property (prer_lo_connectivity);
"""

# print(signal_in_antecedent(a1, "req"))
# print(signal_in_antecedent(a1, "gnt"))
# print(signal_in_antecedent(a2, "valid")) 
# print(signal_in_antecedent(a2, "reset")) 
print(signal_in_antecedent(a3, "prer")) 
