/-
N4 (ARM fidelity): CPSR T-bit + actual Thumb execution. `BX` (A32) into Thumb
code; with `tbit = true` the interpreter fetches 16-bit and decodes a minimal
Thumb slice. The fixture runs A32 `MOVW r0,#0x9; BX r0` then Thumb
`MOVS r1,#5; ADDS r1,#3; B .`, ending with r1 = 8 in Thumb mode. Exit 0 = pass.
-/
import Sei.Core
import Sei.Isa.Arm
open Sei.Core Sei.Isa.Arm

def le (n width : Nat) : List Byte := encodeBytes true n width

-- 0x0: MOVW r0,#0x9 (A32)   0x4: BX r0 (A32)
-- 0x8: MOVS r1,#5 (T16)     0xA: ADDS r1,#3 (T16)   0xC: B . (T16)
def img : List Byte :=
  le 0xe3000009 4 ++ le 0xe12fff10 4 ++ le 0x2105 2 ++ le 0x3103 2 ++ le 0xe7fe 2
    ++ List.replicate (0x1000 - 14) 0

def machine : St :=
  (({} : Cpu), { regions := #[mkRegion "rom" 0 0x1000 Kind.rom (parsePerms "rx") true (bytesToBA img)] })

def final : St := runArm 12 machine
def cpu : Cpu := final.1

def checks : List (String × Bool) :=
  [ ("default_arm_mode", (({} : Cpu)).tbit == false),
    ("entered_thumb", cpu.tbit == true),
    ("thumb_movs_adds", cpu.regs.getD 1 0 == (8 : Word)),       -- 5 + 3
    ("cpsr_T_set", (packCpsr cpu >>> 5) &&& 1 == 1),
    ("thumb_executed", final.2.effects.any fun e =>
        match e with | .exec _ _ "thumb" => true | _ => false),
    ("reached_frontier", cpu.blocked) ]

def main : IO Unit := do
  let mut ok := true
  for (n, b) in checks do
    let tag := if b then "ok" else "FAIL"
    IO.println s!"{n}: {tag}"
    if !b then ok := false
  if !ok then throw (IO.userError "ARM Thumb execution checks failed")
  IO.println "ARM Thumb execution (N4): PASS"
