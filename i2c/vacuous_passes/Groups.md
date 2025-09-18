### **Data Validity Checks**

* **`p_rxr_valid_after_read`**
  Ensures that after a transfer completes (`TIP` falls, `IF` rises), the receive register (`rxr`) contains a valid (non-unknown) value.

* **`assert property ($bits(wb_we_i) == 1);`**
  Checks that the WISHBONE `we` signal is always a single bit wide (no accidental multi-bit encoding).

---

### **Asynchronous Reset Behavior (`arst_i`)**

* **`arst_ctr_en`**
  On async reset, the enable bit (`ctr[7]`) must be cleared.

* **`arst_prer_reset`**
  Prescale register (`prer`) resets to `16'hFFFF`.

* **`arst_txr_reset`**
  Transmit register (`txr`) resets to `8'h00`.

* **`arst_rxr_reset`**
  Receive register (`rxr`) resets to `8'h00`.

* **`arst_status_bits`**
  Status register bits `BUSY`, `AL`, `TIP`, and `IF` all reset to 0.

* **`arst_inta`**
  Interrupt output (`wb_inta_o`) is de-asserted.

* **`arst_ctr_reset`**
  Control register resets to `8'h00`.

* **`arst_cr_reset`**
  Command register resets to `8'h00`.

* **`arst_status_reset`**
  Entire status register resets to `8'h00`.

* **`arst_scl_sda_default`**
  Both I²C bus outputs (`scl_pad_o` and `sda_pad_o`) default high (idle bus).

* **`arst_ctr_reset_1`**
  Control register resets with `EN` and `IEN` cleared, and reserved bits (`ctr[5:0]`) stable.

* **`CR_ResetValue_Async`**
  Command register resets to `8'h00` during async reset.

---

### **Synchronous Reset Behavior (`wb_rst_i`)**

* **`CR_ResetValue_Sync`**
  Command register clears to `8'h00` on sync reset.

* **`AsyncResetValue`**
  Verifies `cr` clears on either async reset edge (depending on active level).

* **`p_ctr_reset_sync`**
  Control register clears to `8'h00` on sync reset.

* **`p_ctr_reset_async`**
  Control register clears to `8'h00` on async reset assertion.

* **`prer_reset`**
  Prescale register resets to `16'hFFFF` on async or sync reset.

* **`p_rxr_reset` / `p_rxr_reset_2`**
  Receive register clears to `8'h00` on resets.

* **`TXR_ResetValue` / `TXR_ResetValue_v2`**
  Transmit register clears to `8'h00` on resets.

* **`ack_reset` / `ack_reset_behavior`**
  Acknowledge output (`wb_ack_o`) must be low immediately and stay low during resets.

---

### **Register Reserved Bits Checks**

* **`p_ctr_reserved_write`**
  Reserved bits in control register (`ctr[5:0]`) must always be written as `0`.

* **`p_ctrl_reg_reserved`**
  Writes to control register cannot set reserved bits (`CTRL_RESV_MASK`).

* **`p_cmd_reg_reserved`**
  Writes to command register cannot set reserved bits (`CMD_RESV_MASK`).

---

### **Command Register Auto-Clear Bits**

* **`STA_AutoClear`**
  Start bit (`cr[7]`) clears automatically after being issued.

* **`STO_AutoClear`**
  Stop bit (`cr[6]`) clears automatically after being issued.

* **`RD_AutoClear`**
  Read command (`cr[5]`) clears automatically after being issued.

---

### **Control Register Safety**

* **`p_en_clear_safety`**
  If the `EN` bit is cleared during a transfer (`TIP`=1), the transfer must finish within 1–3 cycles (avoiding bus hang).

---

### **Protocol Signal Validations**

* **`scl_high_during_start`**
  Start condition: SDA falling edge must happen when SCL is high.

* **`scl_high_during_stop`**
  Stop condition: SDA rising edge must happen when SCL is high.

* **`start_condition`**
  When software sets `cr[3]` (start), a falling edge on SDA while SCL is high must be generated.

* **`stop_condition`**
  When software sets `cr[2]` (stop), a rising edge on SDA while SCL is high must be generated.

---

### **Transmit Register Behavior**

* **`TXR_NoWriteDuringTIP`**
  No writes allowed to TXR while transfer-in-progress (`TIP=1`).

* **`TXR_Stability` / `TXR_Stability_v2` / `TXR_StabilityDuringTransfer`**
  TXR must remain stable while a transfer is active (`TIP=1`).

---

### **Reset Value Checks**

* **`reset_values` / `reset_values_1`**
  On reset, the data output (`wb_dat_o`) must reflect the correct register reset values:

  * `PRERlo` and `PRERhi` registers output `0xFF`
  * All other registers output `0x00`

* **`prer_stable_reset`**
  After sync reset is asserted, the prescale register (`prer`) must remain at `16'hFFFF` until reset is released.

* **`arbitration_lost_reset`**
  Arbitration lost flag (`sr[2]`) must be cleared during reset.

* **`wb_data_reset`**
  During reset (and no active Wishbone cycle), the data bus output (`wb_dat_o`) must be `0x00`.

* **`scl_data_reset` / `sda_data_reset`**
  On sync reset, the SCL and SDA outputs are forced low (`0`).

* **`CTR_Reset` / `PRER_Reset` / `SR_Reset` / `CR_Reset` / `TXR_Reset` / `RXR_Reset`**
  Each respective register must reset to its documented default value:

  * Control Register = `0x00`
  * Prescale Register = `0xFFFF`
  * Status Register = `0x00`
  * Command Register = `0x00`
  * Transmit Register = `0x00`
  * Receive Register = `0x00`

* **`p_reset_prescale_reg`**
  Reasserts that prescale register must reset to `16'hFFFF`.

* **`p_reset_busy_flag`**
  Busy flag (`sr[5]`) must be cleared on reset.

---

### **Interrupt (`wb_inta_o`) Handling**

* **`inta_reset_stable`**
  Interrupt output (`wb_inta_o`) must remain de-asserted for the entire duration of reset.

* **`inta_reset_sync` / `inta_reset_connectivity` / `inta_reset_combined`**
  Ensures interrupt output is cleared on synchronous reset, asynchronous reset, or both combined.

* **`inta_functionality`**
  If interrupt-enable (`ctr[1]`) is set and interrupt-flag (`sr[4]`) is set, then interrupt output must assert (`wb_inta_o=1`).

* **`inta_persistence`**
  Once interrupt is active (`ctr[1] && sr[4]`), the output interrupt (`wb_inta_o`) must stay high until the condition clears.

* **`arbitration_loss_interrupt`**
  If arbitration is lost (`sr[2]`=1), then interrupt flag (`sr[4]`) must also be set.

* **`inta_functionality_delayed`**
  Same as `inta_functionality`, but allows a one-cycle delay before `wb_inta_o` asserts.

* **`inta_iack_clear_fixed`**
  Writing to the command register with `IACK` bit set (and reserved bits cleared) must clear the interrupt flag (`sr[4]`) while keeping interrupt-enable (`ctr[1]`) intact.

* **`inta_iack_clear_timed`**
  Acknowledge write (`IACK=1`) must clear both `wb_inta_o` and `sr[4]` on the next acknowledged cycle.

* **`inta_arbitration_loss`**
  If arbitration-lost (`sr[2]`) rises while interrupts are enabled, the interrupt output (`wb_inta_o`) must assert within 1–2 cycles.

---

### **Wishbone Bus Behavior During Reset**

* **`wb_outputs_reset`**
  On sync reset, both `wb_ack_o` and `wb_inta_o` must be de-asserted.

* **`wb_reset_block_p` / `wb_reset_write_ack_p`**
  During reset, Wishbone must not generate acknowledges (`wb_ack_o`) for write cycles. Prevents bus activity while in reset.
