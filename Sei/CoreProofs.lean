/-
Proofs ABOUT the executable Lean core (the payoff of the FM-friendly design:
the same definitions the emulator runs are the ones we prove about). Building
this elaborates the theorems; a successful build is the proof check.
-/
import Sei.Core
namespace Sei.Core

/-! ### Structural simp lemmas for Machine field projections

    emitM changes only `trace` and `hasUnknown`; these lemmas let simp discharge
    projection goals without expanding the full if-then-else each time. -/

@[simp] theorem emitM_regions (m : Machine) (p : EffectMeta) (e : Effect) :
    (m.emitM p e).regions = m.regions := by
  unfold Machine.emitM; split <;> rfl
@[simp] theorem emitM_devices (m : Machine) (p : EffectMeta) (e : Effect) :
    (m.emitM p e).devices = m.devices := by
  unfold Machine.emitM; split <;> rfl
@[simp] theorem emitM_unknownRead (m : Machine) (p : EffectMeta) (e : Effect) :
    (m.emitM p e).unknownRead = m.unknownRead := by
  unfold Machine.emitM; split <;> rfl
@[simp] theorem emitM_unknownWrite (m : Machine) (p : EffectMeta) (e : Effect) :
    (m.emitM p e).unknownWrite = m.unknownWrite := by
  unfold Machine.emitM; split <;> rfl

@[simp] theorem regions_setDevices (m : Machine) (d : Array Device) :
    ({m with devices := d}).regions = m.regions := rfl

/-! ### Core theorems -/

/-- Emitting an effect appends exactly one entry to the trace — provided the fast-mode
    shortcut is not active (traceFull = true, or the effect is non-verbose). -/
theorem emit_trace_size (m : Machine) (e : Effect)
    (h : m.traceFull = true ∨ e.isVerbose = false) :
    (m.emit e).trace.size = m.trace.size + 1 := by
  simp only [Machine.emit, Machine.emitM]
  split
  · next hfast =>
    simp only [Bool.and_eq_true] at hfast
    rcases h with ht | hv
    · simp [ht] at hfast
    · simp [hv] at hfast
  · next => simp [Array.size_push]

/-- Emitting preserves the memory map and devices (effects are observations). -/
theorem emit_preserves_regions (m : Machine) (e : Effect) :
    (m.emit e).regions = m.regions := by simp [Machine.emit]
theorem emit_preserves_devices (m : Machine) (e : Effect) :
    (m.emit e).devices = m.devices := by simp [Machine.emit]

/-- The unknown-MMIO frontier effects are exactly the two `unknown*` constructors. -/
theorem unknownRead_isUnknown (a : Word) (w : Nat) (v : Word) :
    (Effect.unknownRead a w v).isUnknownMmio = true := rfl
theorem memRead_not_unknown (a : Word) (w : Nat) (v : Word) :
    (Effect.memRead a w v).isUnknownMmio = false := rfl

/-- Single-byte decode recovers the byte, for either endianness. -/
theorem decodeBytes_singleton (little : Bool) (b : Byte) :
    decodeBytes little [b] = b.toNat := by
  cases little <;> simp [decodeBytes]

/-- The UART IRQ line is exactly "RXNE pending and RXIE enabled". -/
theorem uartIrq_spec (sr cr : Word) :
    uartIrq sr cr = ((sr &&& UART_RXNE != 0) && (cr &&& UART_RXIE != 0)) := rfl

/-- A bus read never changes the shape of the memory map (it may update device
    state and append a trace effect, but the region set is invariant). -/
theorem busRead_preserves_regions (m : Machine) (a : Word) (w : Nat) (f : Bool) :
    (m.busRead a w f).2.regions = m.regions := by
  unfold Machine.busRead
  split
  · -- device window hit: inline `have d`, split on accessOk, then on Prod readReg
    next j =>
    dsimp only      -- ζ/ι-reduce let bindings and product match
    split           -- if ¬ accessOk
    · simp [emitM_regions]                        -- cross-boundary error
    · simp [emitM_regions, regions_setDevices]    -- mmio read (product already inlined)
  · -- no device: memory or unknown-MMIO path
    split
    · simp [Machine.emit]                          -- .ok v → emit one event
    · rfl                                          -- .error .perm
    · rfl                                          -- .error .cross
    · -- unmapped → rewrite inner.unknownRead to outer, then split the policy match
      simp only [emitM_unknownRead]; split <;> simp [emitM_regions]

/-- A read-only region (`permR` only) does not grant write permission — so a
    store to it is rejected as a permission fault by `memWrite`. -/
theorem rom_lacks_write_perm : hasPerm permR permW = false := by decide

/-! ### N0 audit proofs (over the executable definitions) -/

/-- A1: a successful `memWrite` preserves the number of regions — it never grows
    the backing store (the bug this fixes was a cross-region write extending it). -/
theorem memWrite_preserves_count (regions : Array Region) (a v : Word) (w : Nat)
    (regions' : Array Region)
    (h : memWrite regions a v w = Except.ok regions') :
    regions'.size = regions.size := by
  unfold memWrite at h
  cases hres : resolve regions a.toNat with
  | none => simp [hres] at h
  | some p =>
    obtain ⟨i, off⟩ := p
    simp only [hres] at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · simp only [Except.ok.injEq] at h
        rw [← h]; simp

/-- A3: two non-overlapping half-open windows never share an address. This is the
    interval lemma behind every `busWellFormed` clause — region-vs-region,
    device-vs-device, and device-vs-memory all reduce to it. -/
theorem overlaps_false_no_common (b1 s1 b2 s2 a : Nat)
    (hd : overlaps b1 s1 b2 s2 = false)
    (h1 : b1 ≤ a ∧ a < b1 + s1) (h2 : b2 ≤ a ∧ a < b2 + s2) : False := by
  simp only [overlaps, decide_eq_false_iff_not] at hd
  omega

/-- A non-overlapping pair of regions never both contain the same address (so a
    well-formed bus decodes every address to at most one region). -/
theorem disjoint_decode (r1 r2 : Region) (a : Nat)
    (hd : overlaps r1.base r1.size r2.base r2.size = false)
    (h1 : r1.contains a = true) (h2 : r2.contains a = true) : False := by
  simp only [Region.contains, decide_eq_true_eq] at h1 h2
  exact overlaps_false_no_common _ _ _ _ a hd h1 h2

/-- Device-vs-memory: a non-overlapping device window and region share no address
    (the executable form of point 1 — a device may not silently shadow memory). -/
theorem device_memory_disjoint (d : Device) (r : Region) (a : Nat)
    (hd : overlaps d.base d.size r.base r.size = false)
    (h1 : d.contains a = true) (h2 : r.contains a = true) : False := by
  simp only [Device.contains, Region.contains, decide_eq_true_eq] at h1 h2
  exact overlaps_false_no_common _ _ _ _ a hd h1 h2

/-- A5/UART: a write to the data register (`0x0`) only appends to the tx FIFO; the
    rx FIFO and the SR/CR registers are unchanged (field isolation). -/
theorem uart_dr_write_only_tx (tx rx : List Nat) (sr cr value : Word) :
    (Device.writeReg { name := "u", base := 0, size := 0x100, beh := .uart tx rx sr cr } 0x0 32 value).beh
      = .uart (tx ++ [(value &&& 0xff).toNat]) rx sr cr := by
  simp [Device.writeReg]

/-- A5/UART: a write to CR (`0x8`) keeps only the two writable bits — reserved
    bits `[31:2]` are dropped. -/
theorem uart_cr_write_masks_reserved (tx rx : List Nat) (sr cr value : Word) :
    (Device.writeReg { name := "u", base := 0, size := 0x100, beh := .uart tx rx sr cr } 0x8 32 value).beh
      = .uart tx rx sr (value &&& 0x3) := by
  simp [Device.writeReg]

/-- A5/UART: a write to SR (`0x4`) leaves tx/rx/cr untouched and only the OVR bit
    is affected, and it is write-1-to-clear. -/
theorem uart_sr_write_w1c (tx rx : List Nat) (sr cr value : Word) :
    (Device.writeReg { name := "u", base := 0, size := 0x100, beh := .uart tx rx sr cr } 0x4 32 value).beh
      = .uart tx rx (if value &&& UART_OVR != 0 then sr &&& ~~~ UART_OVR else sr) cr := by
  simp [Device.writeReg]

end Sei.Core
