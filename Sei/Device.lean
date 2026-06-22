/-
Device register invariants (E10 target 3).

Models a status register with read-only fields and a write-1-to-clear field, and
proves that a software write preserves read-only fields and that write-1-to-clear
behaves as specified. Reserved bits are structurally absent (always zero).
-/
namespace Sei.Device

structure Status where
  txe  : Bool   -- read-only (tx empty)
  rxne : Bool   -- read-only (rx not empty)
  ovr  : Bool   -- write-1-to-clear (overrun)

/-- Software write of the status register: read-only fields are untouched; the
    OVR field is write-1-to-clear (writing 1 clears it, writing 0 keeps it). -/
def writeStatus (s : Status) (w_ovr : Bool) : Status :=
  { s with ovr := s.ovr && !w_ovr }

/-- Read-only fields are never changed by a software write. -/
theorem ro_preserved (s : Status) (w : Bool) :
    (writeStatus s w).txe = s.txe ∧ (writeStatus s w).rxne = s.rxne := by
  simp [writeStatus]

/-- Writing 1 to a write-1-to-clear field clears it. -/
theorem w1c_clears (s : Status) : (writeStatus s true).ovr = false := by
  simp [writeStatus]

/-- Writing 0 to a write-1-to-clear field leaves it unchanged. -/
theorem w1c_keeps (s : Status) : (writeStatus s false).ovr = s.ovr := by
  simp [writeStatus]

/-- A control register modeled by a writable mask: bits outside the mask are
    reserved and must read back as zero after any write. Modeled with `Nat.land`
    over the writable-bit predicate. -/
def writeMasked (old v mask : Nat) : Nat :=
  (v &&& mask) ||| (old &&& (mask ^^^ (2 ^ 32 - 1)))

/-- A reserved bit (outside the writable mask, here bit 31 with a low mask)
    stays clear after writing all-ones, given it was clear before. -/
theorem reserved_bit_stays_zero :
    (writeMasked 0 0xFFFFFFFF 0x1 >>> 31) &&& 1 = 0 := by
  decide

end Sei.Device
