/-
Independent (Nat-based, flat-state) toy ISA backend for E09 differential.

This is the *Lean reference* for the toy ISA. It runs a fixed program and prints
a canonical event log, one event per line:

  F <addr> <word>     instruction fetch (hex, no 0x, unpadded)
  X <op>              execute opcode byte
  R <idx> <val>       register write
  W <addr> <val>      memory store (32-bit)

The independent Python "native" backend prints the same canonical log; E09 diffs
the two so the equivalence is checked against a genuine Lean reference (built and
run on remote execution via rules_lean4).

The toy ISA: 16 regs, 32-bit, word-encoded. Opcodes:
  0x00 HALT  0x01 MOVI  0x02 ADD  0x03 SUB  0x04 ADDI
  0x05 LDR   0x06 STR   0x07 BNZ  0x08 B     0x09 LDRB
-/

namespace Sei.Isa.ToyAlt

def WRAP : Nat := 4294967296  -- 2^32

def toHex (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

structure St where
  regs : Array Nat   -- 16 registers
  pc   : Nat
  halted : Bool

def initSt : St := { regs := (List.replicate 16 0).toArray, pc := 0, halted := false }

/-- Sign-extended 16-bit immediate added (mod 2^32) to a base value. -/
def addImm (base imm : Nat) : Nat :=
  let addend := if imm ≥ 32768 then WRAP - 65536 + imm else imm
  (base + addend) % WRAP

/-- Branch target for a signed 16-bit word offset relative to `pc`. -/
def branchTarget (pc imm : Nat) : Nat :=
  if imm ≥ 32768 then pc - (65536 - imm) * 4 else pc + imm * 4

/-- Execute one instruction, returning the new state and the emitted event lines
    (the leading F/X lines are added by the caller). -/
def stepOne (prog : Array Nat) (s : St) : St × List Nat × List String :=
  -- decode
  let word := prog.getD (s.pc / 4) 0
  let op  := (word >>> 24) &&& 0xff
  let rd  := (word >>> 20) &&& 0xf
  let rs  := (word >>> 16) &&& 0xf
  let imm := word &&& 0xffff
  let rt  := imm &&& 0xf
  let r := fun i => s.regs.getD i 0
  let fetch := [s4 s.pc word]
  let exec  := ["X " ++ toHex op]
  let nextpc := s.pc + 4
  match op with
  | 0x00 => -- HALT
    ({ s with halted := true, pc := nextpc }, [], fetch ++ exec)
  | 0x01 => -- MOVI rd, imm
    let v := imm
    ({ s with regs := s.regs.set! rd v, pc := nextpc }, [], fetch ++ exec ++ [rline rd v])
  | 0x02 => -- ADD rd, rs, rt
    let v := (r rs + r rt) % WRAP
    ({ s with regs := s.regs.set! rd v, pc := nextpc }, [], fetch ++ exec ++ [rline rd v])
  | 0x03 => -- SUB rd, rs, rt
    let v := (r rs + (WRAP - r rt % WRAP)) % WRAP
    ({ s with regs := s.regs.set! rd v, pc := nextpc }, [], fetch ++ exec ++ [rline rd v])
  | 0x04 => -- ADDI rd, rs, imm
    let v := addImm (r rs) imm
    ({ s with regs := s.regs.set! rd v, pc := nextpc }, [], fetch ++ exec ++ [rline rd v])
  | 0x06 => -- STR rd, [rs + imm]
    let addr := addImm (r rs) imm
    ({ s with pc := nextpc }, [], fetch ++ exec ++ [wline addr (r rd)])
  | 0x07 => -- BNZ rs, imm
    let tgt := if r rs ≠ 0 then branchTarget s.pc imm else nextpc
    ({ s with pc := tgt }, [], fetch ++ exec)
  | 0x08 => -- B imm
    ({ s with pc := branchTarget s.pc imm }, [], fetch ++ exec)
  | _ => -- unmodeled in this fixture
    ({ s with halted := true, pc := nextpc }, [], fetch ++ exec)
where
  s4 (addr word : Nat) : String := "F " ++ toHex addr ++ " " ++ toHex word
  rline (idx v : Nat) : String := "R " ++ toString idx ++ " " ++ toHex v
  wline (addr v : Nat) : String := "W " ++ toHex addr ++ " " ++ toHex v

partial def run (prog : Array Nat) (s : St) (acc : List String) (fuel : Nat) : List String :=
  match fuel with
  | 0 => acc
  | fuel + 1 =>
    if s.halted then acc
    else
      let (s', _, lines) := stepOne prog s
      run prog s' (acc ++ lines) fuel

/-- The fixed SUM program (matches the Python E09 driver exactly). -/
def sumProgram : Array Nat := #[
  0x01100007,  -- MOVI r1, 7
  0x01200000,  -- MOVI r2, 0
  0x01301000,  -- MOVI r3, 0x1000
  0x02220001,  -- ADD  r2, r2, r1
  0x0411ffff,  -- ADDI r1, r1, -1
  0x0701fffe,  -- BNZ  r1, -2
  0x06230000,  -- STR  r2, [r3]
  0x00000000   -- HALT
]

/-- Canonical event log of the SUM program (independent backend, for E09). -/
def canonLines : List String := run sumProgram initSt [] 1000

end Sei.Isa.ToyAlt
