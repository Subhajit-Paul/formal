### **Transmit Register (TXR) Checks**

* **TXR_NoWriteDuringTIP**
  Prevents writes to the Transmit Register (`TXR`, addr 0x03) while a transfer is in progress (`TIP=1` in Status Register).

* **TXR_Stability**
  Ensures the contents of `TXR` remain stable as long as the transfer-in-progress (`TIP`) bit is set.

* **TXR_Stability_v2 / TXR_StabilityDuringTransfer**
  Variants of the above: `TXR` must not change while `TIP=1`.

* **TXR_WriteConnectivity / TXR_WriteConnectivity_v2 / TXR_Connectivity**
  Verifies correct data path: when software writes to `TXR`, the register must hold the written value (checked either immediately or after the bus acknowledge).

---

### **Command Register (CR) Checks**

* **ReservedBitsConnectivity**
  Reserved bits `[2:1]` of the Command Register must always remain `0` when written.

* **CommandAutoClear**
  Confirms that command bits (`STA, STO, RD, WR, IACK`) automatically clear themselves after being issued, as required by spec.

* **STA_AutoClear / STO_AutoClear / RD_AutoClear / WR_AutoClear / IACK_AutoClear**
  Each individual command bit (`STA, STO, RD, WR, IACK`) must automatically clear after use.

* **IACK_ClearsInterrupt**
  Writing `IACK=1` must clear the interrupt flag (`IF` in Status Register).

* **ACK_ValidDuringRead**
  When in a read operation (`RD=1`), the ACK bit in the Command Register must be valid and reflected in Status Register.

* **ACK_StableDuringRead**
  During an ongoing read (`RD=1`), the ACK bit setting must remain stable.

---

### **Control Register (CTR) Checks**

* **p_ctr_write_connectivity / p_ctr_write_connectivity_ack / p_ctr_write**
  Writing to Control Register (`CTR`, addr 0x02) correctly updates only `EN` and `IEN` bits (bits \[7:6]); reserved bits must stay `0`.

* **p_ien_interrupt**
  If interrupts are enabled (`IEN=1` in CTR) and the interrupt flag (`IF`) is set in SR, then the interrupt output (`wb_inta_o`) must assert.

---

### **Prescale Register (PRER) Checks**

* **prer_write_ignore_en**
  Writes to the Prescale Register (`PRER`, addr 0x00/0x01) must be ignored if the core is enabled (`EN=1`).

* **prer_stability**
  If not being explicitly written, `PRER` must hold its value (remain stable).

---

### **Receive Register (RXR) Checks**

* **p_rxr_write_protect / p_rxr_write_protect_1/2/3**
  Software writes to `RXR` (addr 0x03, read-only) must have no effect; its contents must not change.

* **p_rxr_update_after_read / p_rxr_update_after_read_1**
  `RXR` must update with new data after a read has completed (indicated by interrupt flag rising and no acknowledge condition).

* **p_rxr_read_update**
  After issuing a read command and completing a transfer, the new value in `RXR` must differ from its previous value.

---

### **Status Register (SR) Checks**

* **sr_connectivity / sr_connectivity_1 / sr_connectivity_2**
  Reading the Status Register (addr 0x04, read) must return the actual internal `SR` value.

* **tip_lifecycle / tip_lifecycle_1 / tip_lifecycle_2 / tip_active**
  Verifies correct lifecycle of the Transfer-In-Progress (`TIP`) bit:

  * It must assert when a transfer starts (`WR` or `RD` command issued).
  * It must remain high during the transfer.
  * It must clear when the transfer ends.

* **iflag_set / iflag_comprehensive / iflag_comprehensive_1**
  The Interrupt Flag (`IF`) in `SR` must be set when:

  * A transfer completes (`TIP` falls)
  * Or arbitration is lost (`AL` rises).
    It must stay set until explicitly cleared by `IACK`.

* **rxack_nack**
  At the end of a transfer, the RxACK bit in `SR` must correctly reflect the actual acknowledge from the slave (based on `SDA` line).

* **rxack_phase_aligned / rxack_phase_aligned_1**
  Confirms proper timing: the sampled acknowledge (`SDA`) from the slave must align correctly with the `RxACK` bit in `SR`.

---

### **ACK / Handshake Checks**

* **ack_after_request**
  Whenever a valid request (`wb_stb_i && wb_cyc_i`) is made, an acknowledge (`wb_ack_o`) must eventually follow.

* **ack_with_cyc**
  An acknowledge can only happen when a cycle is active (`wb_cyc_i=1`).

* **no_spurious_ack**
  No acknowledge should occur unless there was a request in the previous cycle.

* **ack_one_cycle**
  Each acknowledge pulse must be only **one cycle wide**; it cannot remain asserted across multiple cycles.

* **ack_cyc_relationship**
  Acknowledge must only happen if `wb_cyc_i` was active in the previous cycle.

* **ack_causality**
  Acknowledge must trace back to a valid bus request (`stb & cyc`) from two cycles earlier (fits with WISHBONE’s two-cycle access latency).

---

### **Cycle / Strobe Behavior**

* **cyc_until_ack**
  Once a cycle request is asserted (`cyc & stb`), the cycle signal must remain active until the acknowledge arrives.

* **no_cyc_toggle**
  After `cyc` is asserted, it cannot drop before the acknowledge arrives.

* **exact_2cycle_txn**
  Each transaction must last exactly **2 cycles** from request to acknowledge (per spec).

* **cyc_stb_until_ack**
  Both `cyc` and `stb` must stay asserted until the acknowledge is returned.

---

### **Address/Data/Control Stability**

* **address_stability**
  Once a request starts, the address must remain stable until acknowledge.

* **address_stability_1 / address_stability_2**
  Variants checking the same: no address changes in the request phase before `wb_ack_o`.

* **input_stability**
  During a request, not just the address but also `dat_i` and `we_i` must remain constant until acknowledge.

---

### **Clock Stability / Behavior**

* **wb_clk_toggle_stability**
  Ensures that `wb_clk_i` actually toggles — it must not get stuck at a constant level.

* **wb_clk_toggle_window**
  Enforces that the clock must toggle within a certain window (1–100 cycles between edges).

* **wb_clk_toggle_period**
  Constrains the clock period: each edge must occur within `MAX_PERIOD` cycles.

---

### **General Guard Checks**

* **assert property (!wb_cyc_i |-> !wb_ack_o)**
  If no cycle is active, no acknowledge should occur (prevents spurious ACK).

---

### **Write Data Stability**

* **wb_dat_stable_until_ack**
  During a write (`we=1`), the input data bus (`wb_dat_i`) must remain constant until the acknowledge is asserted.

* **p_data_stability**
  Variant of the above, scoped to the expected 2-cycle WISHBONE latency — write data must stay stable until `wb_ack_o`.

---

### **Read Data Stability**

* **data_stability_3 / data_stability_4**
  The output data bus (`wb_dat_o`) must remain stable while no acknowledge is active, i.e., data cannot glitch between valid read cycles.

---

### **Register Accessibility and Readback**

* **prer_accessibility / prer_accessibility_1**
  The Prescale Register (PRER, addresses `0x00/0x01`) is only accessible when the core is disabled (`ctr[0] == 0`). Reads must return the correct low/high byte.

* **PRERlo_read / PRERlo_read_1**
  Reading `0x00` (PRER low) must return `prer[7:0]`.

* **PRERhi_read / PRERhi_read_1**
  Reading `0x01` (PRER high) must return `prer[15:8]`.

* **CTR_read / CTR_read_1**
  Reading `0x02` must return the current Control Register value (`ctr`).

* **RXR_read / RXR_read_1**
  Reading `0x03` (RXR) must return the Receive Register contents.

* **SR_read / SR_read_1**
  Reading `0x04` must return the Status Register (`sr`).

* **PRERlo_read_2**
  A more comprehensive check: depending on the last address, the returned data must match the correct register value (`PRERlo`, `PRERhi`, `CTR`, `RXR`, or `SR`).

---

### **Interrupt Acknowledge / Deassert**

* **inta_iack_clear_fixed**
  Writing `IACK=1` to the Command Register must clear the interrupt flag (`IF` in `sr`).

* **inta_iack_clear_timed**
  Confirms that after writing `IACK`, on the next acknowledge cycle, both the interrupt output (`wb_inta_o`) and the interrupt flag (`sr[0]`) are deasserted.

* **inta_deassert**
  If either interrupt enable (`ctr[1]`) is cleared or the interrupt flag (`sr[0]`) is cleared, then the interrupt output must also deassert.

---

### **Timing of Acknowledge**

* **wb_stb_ack_response**
  Each Wishbone request (`stb & cyc`) must get an acknowledge exactly 2 cycles later.

---

### **Input Signal Stability**

* **wb_input_stability**
  During a bus transaction, address, data, and write-enable must remain stable until acknowledge.

* **wb_stb_retention**
  The strobe (`stb`) must remain asserted through to acknowledge.

* **wb_we_stable_p / wb_we_stability_p / wb_we_stable_p_v3**
  Variants of the same rule: the write-enable (`we`) signal must not change during an active transaction — it must remain constant until acknowledge.

---

### **Write Transaction Acknowledge**

* **wb_write_ack_p / wb_write_ack_p_v2**
  After a valid write transaction request, the acknowledge must be returned one cycle later.

---
