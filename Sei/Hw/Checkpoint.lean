/-
Save/load the full emulator state (Cpu + Machine) as a single JSON file,
enabling resumption between fast and trace modes.

  # Round-trip: fast run → checkpoint → trace run
  sei_cli fw.sei.json --fast --fuel 5000000 --checkpoint-out snap.json
  sei_cli fw.sei.json --checkpoint-in snap.json --fuel 100

When --checkpoint-in is given, the Machine and CPU come from the checkpoint;
the --fast flag is applied fresh so you can switch modes freely.
The trace is NOT saved — you get a clean trace from the resume point onward.
-/
import Lean.Data.Json
import Sei.Core
import Sei.Hw.Adapter
import Sei.Hw.Descriptor
import Sei.Isa.Arm
open Lean Sei.Core Sei.Hw Sei.Hw.Adapter
namespace Sei.Hw.Checkpoint

/-! ### Hex encode / decode for ByteArray region data -/

private def hexChar (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n)
  else Char.ofNat ('a'.toNat + n - 10)

private def hexEncodeBA (ba : ByteArray) : String :=
  -- Build char array first; avoids O(n²) string concatenation.
  let cs := ba.foldl (fun cs b =>
    cs.push (hexChar (b.toNat >>> 4)) |>.push (hexChar (b.toNat &&& 0xf))) (#[] : Array Char)
  String.mk cs.toList

private def hexDecodeBA (s : String) : Except String ByteArray := do
  if s.length % 2 != 0 then throw s!"hex data has odd length ({s.length})"
  -- Use toUTF8 for O(1) indexing; hex chars are ASCII so one byte each.
  let bs := s.toUTF8
  let bytes ← (List.range (s.length / 2)).mapM fun i => do
    let hi ← hexDigit (Char.ofNat bs[i * 2]!.toNat)
    let lo ← hexDigit (Char.ofNat bs[i * 2 + 1]!.toNat)
    pure (UInt8.ofNat (hi * 16 + lo))
  pure (ByteArray.mk bytes.toArray)

/-! ### JSON field readers (all return Except String to match Lean.Json conventions) -/

private def getS (j : Json) (k : String) : Except String String :=
  (j.getObjVal? k).bind (·.getStr?)
private def getB (j : Json) (k : String) : Except String Bool :=
  (j.getObjVal? k).bind (·.getBool?)
private def getA (j : Json) (k : String) : Except String (Array Json) :=
  (j.getObjVal? k).bind (·.getArr?)
private def getO (j : Json) (k : String) : Except String Json :=
  j.getObjVal? k
private def getN (j : Json) (k : String) : Except String Nat :=
  (j.getObjVal? k).bind fun v => match v with
    | .num n => .ok n.mantissa.toNat
    | _ => .error s!"field '{k}' is not a number"
private def getW (j : Json) (k : String) : Except String Word :=
  (getS j k).bind (parseHexNat ·) |>.map (BitVec.ofNat 32)

/-! ### Serializers -/

private def jb (b : Bool) : Json := Json.bool b
private def jw (w : Word) : Json := jstr w.hex
private def jn (n : Nat) : Json := jnum n 0
private def jv64 (v : BitVec 64) : Json := jstr (hexv v.toNat 64)

private def policyStr : UnknownPolicy → String
  | .defaultValue => "default-value" | .fault => "fault"
private def kindStr : Kind → String
  | .rom => "rom" | .ram => "ram" | .alias => "alias"

private def serRegCell (c : RegCell) : Json :=
  jobj [("offset", jn c.offset), ("value", jw c.value),
        ("roMask", jw c.roMask), ("w1cMask", jw c.w1cMask),
        ("corMask", jw c.corMask), ("resvMask", jw c.resvMask)]

private def serBeh : DevBehavior → Json
  | .uart tx rx sr cr =>
    jobj [("tag", jstr "uart"), ("tx", jarr (tx.map jn)), ("rx", jarr (rx.map jn)),
          ("sr", jw sr), ("cr", jw cr)]
  | .regStub regs =>
    jobj [("tag", jstr "regStub"),
          ("regs", jarr (regs.map fun (o, v) => jarr [jn o, jw v]))]
  | .regfile cells =>
    jobj [("tag", jstr "regfile"), ("cells", jarr (cells.map serRegCell))]
  | .statusModel count readyAfter readyValue =>
    jobj [("tag", jstr "statusModel"), ("count", jn count),
          ("readyAfter", match readyAfter with | none => Json.null | some k => jn k),
          ("readyValue", jw readyValue)]
  | .traceReplay script pos =>
    jobj [("tag", jstr "traceReplay"),
          ("script", jarr (script.map fun (o, v) => jarr [jn o, jw v])),
          ("pos", jn pos)]
  | .external name counter incr =>
    jobj [("tag", jstr "external"), ("name", jstr name),
          ("counter", jw counter), ("incr", jw incr)]
  | .ddr ready gates =>
    jobj [("tag", jstr "ddr"), ("ready", jb ready), ("gates", jstr gates)]
  | .flash backing cmd addr xip =>
    jobj [("tag", jstr "flash"), ("backing", jarr (backing.map jw)),
          ("cmd", jn cmd), ("addr", jn addr), ("xip", jb xip)]
  | .watchdog count timeout policy =>
    jobj [("tag", jstr "watchdog"), ("count", jn count),
          ("timeout", jn timeout), ("policy", jstr policy)]

private def serDevice (d : Device) : Json :=
  jobj [("name", jstr d.name), ("base", jn d.base), ("size", jn d.size),
        ("irq", jb d.irq), ("beh", serBeh d.beh),
        ("sem", jobj [("id", jstr d.sem.id), ("cls", jstr (reprStr d.sem.cls))])]

private def serRegion (r : Region) : Json :=
  jobj ([("name", jstr r.name), ("base", jn r.base), ("size", jn r.size),
         ("kind", jstr (kindStr r.kind)), ("perms", jn r.perms),
         ("little", jb r.little), ("data", jstr (hexEncodeBA r.data)),
         ("enabled", jb r.enabled)]
        ++ match r.aliasOf with | none => [] | some s => [("aliasOf", jstr s)])

private def serMachine (m : Machine) : Json :=
  jobj [("icount", jn m.icount), ("traceFull", jb m.traceFull),
        ("unknownDefault", jw m.unknownDefault),
        ("unknownRead", jstr (policyStr m.unknownRead)),
        ("unknownWrite", jstr (policyStr m.unknownWrite)),
        ("hasUnknown", jb m.hasUnknown),
        ("regions", jarr (m.regions.toList.map serRegion)),
        ("devices", jarr (m.devices.toList.map serDevice))]

def serArmCpu (cpu : Sei.Isa.Arm.Cpu) : Json :=
  jobj [("regs", jarr (cpu.regs.toList.map jw)),
        ("pc", jw cpu.pc),
        ("n", jb cpu.n), ("z", jb cpu.z), ("c", jb cpu.c), ("v", jb cpu.v),
        ("mode", jn cpu.mode),
        ("iMask", jb cpu.iMask), ("fMask", jb cpu.fMask), ("tbit", jb cpu.tbit),
        ("highVectors", jb cpu.highVectors),
        ("haltOnSelfBranch", jb cpu.haltOnSelfBranch),
        ("spsr", jarr (cpu.spsr.map fun (m, w) => jarr [jn m, jw w])),
        ("banked", jarr (cpu.banked.map fun ((m, r), w) => jarr [jn m, jn r, jw w])),
        ("cp15", jarr (cpu.cp15.map fun ((crn, opc1, crm, opc2), w) =>
            jarr [jn crn, jn opc1, jn crm, jn opc2, jw w])),
        ("vreg", jarr (cpu.vreg.toList.map jv64)),
        ("fpscr", jw cpu.fpscr), ("fpexc", jw cpu.fpexc),
        ("irqPending", jb cpu.irqPending), ("fiqPending", jb cpu.fiqPending),
        ("halted", jb cpu.halted), ("blocked", jb cpu.blocked)]

def checkpointJson (arch : String) (cpu : Json) (m : Machine) : Json :=
  jobj [("version", jn 1), ("arch", jstr arch), ("cpu", cpu), ("machine", serMachine m)]

/-! ### Deserializers -/

private def parsePol : String → UnknownPolicy
  | "fault" => .fault | _ => .defaultValue

private def parseKindS : String → Except String Kind
  | "rom" => .ok .rom | "ram" => .ok .ram | "alias" => .ok .alias
  | s => .error s!"unknown region kind '{s}'"

private def deserRegCell (j : Json) : Except String RegCell := do
  let offset ← getN j "offset"; let value ← getW j "value"
  let roMask ← getW j "roMask"; let w1cMask ← getW j "w1cMask"
  let corMask ← getW j "corMask"; let resvMask ← getW j "resvMask"
  pure { offset, value, roMask, w1cMask, corMask, resvMask }

private def deserNatWord (e : Json) : Except String (Nat × Word) :=
  match e with
  | .arr #[.num o, .str v] => parseHexNat v |>.map fun n =>
      (o.mantissa.toNat, BitVec.ofNat 32 n)
  | _ => .error "expected [nat, \"0xHH\"]"

private def deserBeh (j : Json) : Except String DevBehavior := do
  match ← getS j "tag" with
  | "uart" =>
    let tx ← (← getA j "tx").toList.mapM fun e =>
        match e with | .num n => .ok n.mantissa.toNat | _ => .error "bad uart byte"
    let rx ← (← getA j "rx").toList.mapM fun e =>
        match e with | .num n => .ok n.mantissa.toNat | _ => .error "bad uart byte"
    let sr ← getW j "sr"; let cr ← getW j "cr"
    pure (.uart tx rx sr cr)
  | "regStub" =>
    pure (.regStub (← (← getA j "regs").toList.mapM deserNatWord))
  | "regfile" =>
    pure (.regfile (← (← getA j "cells").toList.mapM deserRegCell))
  | "statusModel" =>
    let count ← getN j "count"; let readyValue ← getW j "readyValue"
    let ra := match j.getObjVal? "readyAfter" with
              | .ok (.num n) => some n.mantissa.toNat | _ => none
    pure (.statusModel count ra readyValue)
  | "traceReplay" =>
    pure (.traceReplay (← (← getA j "script").toList.mapM deserNatWord) (← getN j "pos"))
  | "external" =>
    let name ← getS j "name"; let counter ← getW j "counter"; let incr ← getW j "incr"
    pure (.external name counter incr)
  | "ddr" =>
    pure (.ddr (← getB j "ready") (← getS j "gates"))
  | "flash" =>
    let backing ← (← getA j "backing").toList.mapM fun e => match e with
        | .str v => parseHexNat v |>.map (BitVec.ofNat 32) | _ => .error "bad flash word"
    let cmd ← getN j "cmd"; let addr ← getN j "addr"; let xip ← getB j "xip"
    pure (.flash backing cmd addr xip)
  | "watchdog" =>
    let count ← getN j "count"; let timeout ← getN j "timeout"; let policy ← getS j "policy"
    pure (.watchdog count timeout policy)
  | t => .error s!"unknown device behavior tag '{t}'"

private def deserDevice (j : Json) : Except String Device := do
  let name ← getS j "name"; let base ← getN j "base"; let size ← getN j "size"
  let irq ← getB j "irq"
  let beh ← deserBeh (← getO j "beh")
  let semJ := (j.getObjVal? "sem").toOption.getD (Json.mkObj [])
  let semId := ((semJ.getObjVal? "id").toOption.bind (·.getStr?.toOption)).getD ""
  pure { name, base, size, irq, beh, sem := { id := semId, cls := .unknown } }

private def deserRegion (j : Json) : Except String Region := do
  let name ← getS j "name"; let base ← getN j "base"; let size ← getN j "size"
  let kind ← parseKindS (← getS j "kind")
  let perms ← getN j "perms"; let little ← getB j "little"
  let data ← hexDecodeBA (← getS j "data")
  let enabled ← getB j "enabled"
  let aliasOf := ((j.getObjVal? "aliasOf").toOption.bind (·.getStr?.toOption))
  pure { name, base, size, kind, perms, little, data, enabled, aliasOf }

def deserMachine (j : Json) : Except String Machine := do
  let mj ← getO j "machine"
  let icount ← getN mj "icount"; let traceFull ← getB mj "traceFull"
  let unknownDefault ← getW mj "unknownDefault"
  let unknownRead := parsePol ((getS mj "unknownRead").toOption.getD "")
  let unknownWrite := parsePol ((getS mj "unknownWrite").toOption.getD "")
  let hasUnknown ← getB mj "hasUnknown"
  let regions ← (← getA mj "regions").toList.mapM deserRegion
  let devices ← (← getA mj "devices").toList.mapM deserDevice
  pure { regions := regions.toArray, devices := devices.toArray,
         icount, traceFull, unknownDefault, unknownRead, unknownWrite, hasUnknown }

def deserArmCpu (j : Json) : Except String Sei.Isa.Arm.Cpu := do
  let cj ← getO j "cpu"
  let regs ← (← getA cj "regs").toList.mapM fun e => match e with
    | .str s => parseHexNat s |>.map (BitVec.ofNat 32) | _ => .error "bad reg"
  let pc ← getW cj "pc"
  let n ← getB cj "n"; let z ← getB cj "z"
  let c ← getB cj "c"; let v ← getB cj "v"
  let mode ← getN cj "mode"
  let iMask ← getB cj "iMask"; let fMask ← getB cj "fMask"
  let tbit ← getB cj "tbit"; let highVectors ← getB cj "highVectors"
  let haltOnSelfBranch ← getB cj "haltOnSelfBranch"
  let spsr ← (← getA cj "spsr").toList.mapM fun e => match e with
    | .arr #[.num m, .str w] => parseHexNat w |>.map fun n =>
        (m.mantissa.toNat, BitVec.ofNat 32 n)
    | _ => .error "bad spsr entry"
  let banked ← (← getA cj "banked").toList.mapM fun e => match e with
    | .arr #[.num m, .num r, .str w] => parseHexNat w |>.map fun n =>
        ((m.mantissa.toNat, r.mantissa.toNat), BitVec.ofNat 32 n)
    | _ => .error "bad banked entry"
  let cp15 ← (← getA cj "cp15").toList.mapM fun e => match e with
    | .arr #[.num n', .num o1, .num crm, .num o2, .str w] => parseHexNat w |>.map fun n =>
        ((n'.mantissa.toNat, o1.mantissa.toNat, crm.mantissa.toNat, o2.mantissa.toNat),
         BitVec.ofNat 32 n)
    | _ => .error "bad cp15 entry"
  let vreg ← (← getA cj "vreg").toList.mapM fun e => match e with
    | .str s => parseHexNat s |>.map (BitVec.ofNat 64) | _ => .error "bad vreg"
  let fpscr ← getW cj "fpscr"; let fpexc ← getW cj "fpexc"
  let irqPending ← getB cj "irqPending"; let fiqPending ← getB cj "fiqPending"
  let halted ← getB cj "halted"; let blocked ← getB cj "blocked"
  pure { regs := regs.toArray, pc, n, z, c, v, mode, iMask, fMask, tbit,
         highVectors, haltOnSelfBranch, spsr, banked, cp15,
         vreg := vreg.toArray, fpscr, fpexc, irqPending, fiqPending, halted, blocked }

/-! ### IO entry points -/

def saveArmCheckpoint (path : String) (cpu : Sei.Isa.Arm.Cpu) (m : Machine) : IO Unit := do
  IO.FS.writeFile path (checkpointJson "arm" (serArmCpu cpu) m).pretty
  IO.println s!"checkpoint: {path} (icount={m.icount} regions={m.regions.size} devices={m.devices.size})"

def loadArmCheckpoint (path : String) : IO (Sei.Isa.Arm.Cpu × Machine) := do
  let text ← IO.FS.readFile path
  let j ← IO.ofExcept (Json.parse text)
  let arch ← IO.ofExcept (getS j "arch")
  if arch != "arm" then throw (IO.userError s!"checkpoint arch is '{arch}', expected 'arm'")
  let cpu ← IO.ofExcept (deserArmCpu j)
  let m   ← IO.ofExcept (deserMachine j)
  IO.println s!"checkpoint loaded: {path} (icount={m.icount} regions={m.regions.size})"
  pure (cpu, m)

end Sei.Hw.Checkpoint
