/-
Toy ISA over the SEI Lean core (FM-friendly): a pure, total small-step function
producing typed effects. 16 × 32-bit registers, word-encoded instructions.

Opcodes (byte): 00 HALT  01 MOVI  02 ADD  03 SUB  04 ADDI
                05 LDR   06 STR   07 BNZ  08 B    09 LDRB

BitVec arithmetic wraps mod 2^32 automatically, so there is no manual masking —
which keeps the semantics clean and `bv_decide`-friendly.
-/
import Sei.Core
open Sei.Core

namespace Sei.Isa.Toy

structure Cpu where
  regs : Array Word := (List.replicate 16 (0 : Word)).toArray
  pc : Word := 0
  halted : Bool := false
  deriving Inhabited

abbrev St := Cpu × Machine

def Cpu.r (c : Cpu) (i : Nat) : Word := c.regs.getD i 0
def Cpu.setR (c : Cpu) (i : Nat) (v : Word) : Cpu := { c with regs := c.regs.setIfInBounds i v }

def mnem (op : Nat) : String :=
  match op with
  | 0x00 => "HALT" | 0x01 => "MOVI" | 0x02 => "ADD" | 0x03 => "SUB"
  | 0x04 => "ADDI" | 0x05 => "LDR"  | 0x06 => "STR" | 0x07 => "BNZ"
  | 0x08 => "B"    | 0x09 => "LDRB" | _ => "?"

/-- One instruction. Pure and total; returns the next state and `true` to keep
    running. Emits typed effects into the machine trace. -/
def step (c : Cpu) (m : Machine) : Cpu × Machine × Bool :=
  let pc := c.pc
  let (fres, m) := m.busRead pc 32 (fetch := true)
  match fres with
  | .error _ => (({ c with halted := true }), m.emit (.note "fetch_fault"), false)
  | .ok word =>
    let w := word.toNat
    let op := (w >>> 24) &&& 0xff
    let rd := (w >>> 20) &&& 0xf
    let rs := (w >>> 16) &&& 0xf
    let imm := w &&& 0xffff
    let rt := imm &&& 0xf
    let simm : Word := (BitVec.ofNat 16 imm).signExtend 32
    let m := m.emit (.exec pc (BitVec.ofNat 8 op) (mnem op))
    let next : Word := pc + 4
    let wr (c : Cpu) (m : Machine) (i : Nat) (v : Word) : Cpu × Machine :=
      (c.setR i v, m.emit (.reg i v))
    let bump (m : Machine) : Machine := { m with icount := m.icount + 1 }
    match op with
    | 0x00 => (({ c with halted := true, pc := next }), bump m, false)
    | 0x01 => let (c, m) := wr c m rd (BitVec.ofNat 32 imm)
              (({ c with pc := next }), bump m, true)
    | 0x02 => let (c, m) := wr c m rd (c.r rs + c.r rt)
              (({ c with pc := next }), bump m, true)
    | 0x03 => let (c, m) := wr c m rd (c.r rs - c.r rt)
              (({ c with pc := next }), bump m, true)
    | 0x04 => let (c, m) := wr c m rd (c.r rs + simm)
              (({ c with pc := next }), bump m, true)
    | 0x05 => -- LDR rd, [rs + simm]
      let addr := c.r rs + simm
      let (res, m) := m.busRead addr 32
      match res with
      | .ok v => let (c, m) := wr c m rd v; (({ c with pc := next }), bump m, true)
      | .error _ => (({ c with halted := true }), m.emit (.note "data_abort"), false)
    | 0x06 => -- STR rd, [rs + simm]
      let addr := c.r rs + simm
      let (res, m) := m.busWrite addr (c.r rd) 32
      match res with
      | .ok _ => (({ c with pc := next }), bump m, true)
      | .error _ => (({ c with halted := true }), bump (m.emit (.note "data_abort")), false)
    | 0x07 => -- BNZ rs, simm
      let tgt := if c.r rs ≠ 0 then pc + simm * 4 else next
      (({ c with pc := tgt }), bump m, true)
    | 0x08 => (({ c with pc := pc + simm * 4 }), bump m, true)  -- B
    | 0x09 => -- LDRB rd, [rs + simm]
      let addr := c.r rs + simm
      let (res, m) := m.busRead addr 8
      match res with
      | .ok v => let (c, m) := wr c m rd v; (({ c with pc := next }), bump m, true)
      | .error _ => (({ c with halted := true }), m.emit (.note "data_abort"), false)
    | _ => (({ c with halted := true }), m.emit (.unsupported pc op (mnem op)), false)

/-- Drive the machine to a halt or until `fuel` runs out. Pure ⇒ deterministic. -/
def runToy (fuel : Nat) (s : St) : St :=
  Sei.Core.run (fun (s : St) =>
    let (c, m) := s
    if c.halted then (s, false)
    else let (c', m', cont) := step c m; ((c', m'), cont)) fuel s

/-! ### Assembler (for fixtures) -/

def asm (op rd rs imm : Nat) : Word :=
  BitVec.ofNat 32 (((op &&& 0xff) <<< 24) ||| ((rd &&& 0xf) <<< 20) |||
                   ((rs &&& 0xf) <<< 16) ||| (imm &&& 0xffff))

def MOVI (rd imm : Nat) : Word := asm 0x01 rd 0 imm
def ADD (rd rs rt : Nat) : Word := asm 0x02 rd rs (rt &&& 0xf)
def SUB (rd rs rt : Nat) : Word := asm 0x03 rd rs (rt &&& 0xf)
def ADDI (rd rs imm : Nat) : Word := asm 0x04 rd rs imm
def LDR (rd rs imm : Nat) : Word := asm 0x05 rd rs imm
def STR (rd rs imm : Nat) : Word := asm 0x06 rd rs imm
def BNZ (rs imm : Nat) : Word := asm 0x07 0 rs imm
def B (imm : Nat) : Word := asm 0x08 0 0 imm
def HALT : Word := asm 0x00 0 0 0

/-- Assemble a program into a byte image with the given endianness. -/
def assemble (words : List Word) (little : Bool) : List Byte :=
  words.flatMap (fun w => encodeBytes little w.toNat 4)

end Sei.Isa.Toy
