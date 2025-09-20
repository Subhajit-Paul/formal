### **Protocol condition assertions**

1. **`start_condition`**
   Checks that when a START command is issued (`cr[3]` = STA bit) and the clock line is high (`scl_pad_o`), the SDA line actually makes the required **high-to-low transition** → a valid START condition.

2. **`TXR_Stability_v2`**
   Ensures that when a transfer is in progress (`sr[3]` = TIP bit), the **transmit register (`txr`) does not change** unexpectedly. This guarantees data stability during transmission.

3. **`stop_condition`**
   Checks that when a STOP command is issued (`cr[2]` = STO bit) and the clock line is high (`scl_pad_o`), the SDA line makes the required **low-to-high transition** → a valid STOP condition.

---

### **EN/IEN control checks**

4. **`p_en_clear_safety`**
   When the **enable bit (`ctr[7]`) is cleared** while a transfer is in progress (`sr[3]` = TIP), the assertion ensures that the transfer is **terminated within 1–3 cycles** (TIP goes low). Prevents the core from hanging the bus.

5. **`inta_functionality`**
   If interrupts are enabled (`ctr[1]` = IEN) and an interrupt condition occurs (`sr[4]` = IF flag), then the **interrupt output (`wb_inta_o`) must be asserted**.

6. **`inta_persistence`**
   Once an interrupt is active (`ctr[1]` && `sr[4]`), the **interrupt output must remain asserted** as long as the condition holds. This prevents spurious de-assertion of the interrupt.

7. **`arbitration_loss_interrupt`**
   If arbitration is lost (`sr[2]` = AL), then the **interrupt flag (`sr[4]`) must also be set**. This ensures the CPU is notified of arbitration loss.

8. **`inta_functionality_delayed`**
   Similar to `inta_functionality`, but allows a **1-cycle delay** before the interrupt output (`wb_inta_o`) is asserted after an interrupt condition (`ctr[1] && sr[4]`).

9. **`inta_arbitration_loss`**
   When arbitration loss (`sr[2]`) occurs and interrupts are enabled (`ctr[1]`), the **interrupt output must be asserted within 1–2 cycles**. This checks the timing of arbitration loss interrupt generation.

