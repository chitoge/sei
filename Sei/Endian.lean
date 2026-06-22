/-
Endian load/store round-trip lemmas (E10 target 1).

Models little-endian byte encode/decode over `Nat` and proves that decoding the
encoding recovers the value modulo the width, at the fixed widths the emulator
uses (8/16/32 bits). Big-endian is the byte reversal of little-endian.
-/
namespace Sei.Endian

/-- Little-endian split of `v` into `n` bytes (each in `0..255`). -/
def encodeLE : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, v => (v % 256) :: encodeLE n (v / 256)

/-- Decode a little-endian byte list back to a `Nat`. -/
def decodeLE : List Nat → Nat
  | [] => 0
  | b :: bs => b + 256 * decodeLE bs

/-- Big-endian encoding is the reverse of the little-endian byte order. -/
def encodeBE (n v : Nat) : List Nat := (encodeLE n v).reverse

theorem be_is_reverse_le (n v : Nat) : encodeBE n v = (encodeLE n v).reverse := rfl

/-- 8-bit round trip. -/
theorem rt8 (v : Nat) : decodeLE (encodeLE 1 v) = v % 256 := by
  simp [encodeLE, decodeLE]

/-- 16-bit round trip. -/
theorem rt16 (v : Nat) : decodeLE (encodeLE 2 v) = v % 65536 := by
  simp [encodeLE, decodeLE]; omega

/-- 32-bit round trip. -/
theorem rt32 (v : Nat) : decodeLE (encodeLE 4 v) = v % 4294967296 := by
  simp [encodeLE, decodeLE]; omega

/-- Each encoded byte is a valid 8-bit value. -/
theorem encode_bytes_lt_256 (n v : Nat) : ∀ b ∈ encodeLE n v, b < 256 := by
  induction n generalizing v with
  | zero => intro b hb; simp [encodeLE] at hb
  | succ k ih =>
    intro b hb
    simp [encodeLE] at hb
    rcases hb with h | h
    · omega
    · exact ih (v / 256) b h

end Sei.Endian
