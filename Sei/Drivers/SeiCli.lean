/-
L6/B-ladder CLI: `sei_cli <descriptor.sei.json> [--fuel N] [--image name=path ...]`
loads a descriptor with its declared backing images, runs it under a fuel bound,
and emits report / trace-summary / frontier artifacts. Declared images are
mandatory (#3): a missing image fails before the first instruction.
-/
import Sei.Api
import Sei.Hw.Checkpoint
open Sei.Core Sei.Hw Sei.Api Sei.Hw.Adapter Sei.Hw.Checkpoint

structure CliArgs where
  desc : String := ""
  fuel : Nat := 100000
  traceTail : Nat := 0
  fast : Bool := false           -- --fast: skip verbose trace events for speed
  report : String := ""          -- #8: write report+frontier JSON here
  snapshotOut : String := ""     -- #9: write a snapshot-identity manifest here
  checkpointOut : String := ""   -- write full CPU+Machine checkpoint here
  checkpointIn : String := ""    -- resume from a prior checkpoint (skip descriptor init)
  out : String := ""             -- #6: import output descriptor path
  images : List (String × String) := []   -- name, path

partial def parseArgs : List String → CliArgs → CliArgs
  | [], a => a
  | "--fuel" :: n :: rest, a => parseArgs rest { a with fuel := (n.toNat?).getD a.fuel }
  | "--trace-tail" :: n :: rest, a => parseArgs rest { a with traceTail := (n.toNat?).getD 0 }
  | "--fast" :: rest, a => parseArgs rest { a with fast := true }
  | "--report" :: p :: rest, a => parseArgs rest { a with report := p }
  | "--out" :: p :: rest, a => parseArgs rest { a with out := p }
  | "--source" :: _ :: rest, a => parseArgs rest a
  | "--snapshot-out" :: p :: rest, a => parseArgs rest { a with snapshotOut := p }
  | "--checkpoint-out" :: p :: rest, a => parseArgs rest { a with checkpointOut := p }
  | "--checkpoint-in" :: p :: rest, a => parseArgs rest { a with checkpointIn := p }
  | "--image" :: spec :: rest, a =>
    match spec.splitOn "=" with
    | [name, path] => parseArgs rest { a with images := a.images ++ [(name, path)] }
    | _ => parseArgs rest a
  | arg :: rest, a => parseArgs rest (if a.desc.isEmpty then { a with desc := arg } else a)

def loadImage (path : String) : IO ByteArray :=
  IO.FS.readBinFile path

/-- #6: `sei_cli import <evidence.json> [--source S] [--out descriptor.json]` —
    turn an evidence model into a hardware-entry descriptor (via the adapter). -/
def importCmd (evPath : String) (rest : List String) : IO Unit := do
  let a := parseArgs rest {}
  let out := if a.out != "" then a.out else "bro1.sei.json"
  let modelText ← IO.FS.readFile evPath
  match Sei.Hw.Adapter.adaptText modelText evPath with
  | .error e => throw (IO.userError s!"import: {e}")
  | .ok descText =>
    match parseDescriptor (← (Lean.Json.parse descText |> IO.ofExcept)) with
    | .error e => throw (IO.userError s!"import produced an invalid descriptor: {e}")
    | .ok h =>
      IO.FS.writeFile out descText
      IO.println s!"imported: {out} (arch={h.arch} entry={h.resetPc} regions={h.regions.length} devices={h.devices.length})"
      IO.println "sei_cli import: PASS"

def runAndReport (rep : RunReport) (m : Machine) (a : CliArgs) : IO Unit := do
  IO.println s!"report: arch={rep.arch} endian={rep.endian} entry={rep.entry} sp={rep.entrySp} highVectors={rep.highVectors} overrides={rep.regOverrides}"
  IO.println s!"  regions={rep.regions} devices={rep.devices} fuel={rep.fuel} stop={reprStr rep.stop} lastPc={rep.lastPc} events={rep.events} hash={rep.traceHash}"
  IO.println s!"unsupported: {rep.unsupported.length}"
  for (pc, op, mn) in rep.unsupported.take 8 do IO.println s!"  unsupported @{pc} op={op} {mn}"
  let fr := exportFrontier m
  IO.println s!"frontier windows: {fr.length}"
  for t in fr.take 8 do IO.println s!"  frontier @{t.address} polls={t.pollCount} class={reprStr t.candidateClass}"
  let tr := exportTrace m
  IO.println s!"trace lines: {tr.length}"
  if a.traceTail > 0 then
    IO.println s!"--- last {a.traceTail} trace lines ---"
    for line in tr.toArray.toList.drop (tr.length - a.traceTail) do IO.println s!"  {line}"
  if a.report != "" then
    IO.FS.writeFile a.report (reportJson rep m).pretty
    IO.println s!"report written: {a.report}"
  if a.snapshotOut != "" then
    let snap := jobj [("label", jstr "cli"), ("traceHash", jnum rep.traceHash 0),
      ("lastPc", jnum rep.lastPc 0), ("regions", jnum rep.regions 0), ("devices", jnum rep.devices 0),
      ("stop", jstr (reprStr rep.stop))]
    IO.FS.writeFile a.snapshotOut snap.pretty
    IO.println s!"snapshot written: {a.snapshotOut}"

/-- Build a RunReport from the result of a direct runArm call. -/
def armReport (arch endian : String) (entryPc : Nat) (entrySp : Nat) (highVec : Bool)
    (fuel : Nat) (descId : String) (initM : Machine)
    (c : Sei.Isa.Arm.Cpu) (m : Machine) : RunReport :=
  let stop : StopReason :=
    if c.blocked then .blockedFrontier else if c.halted then .halted
    else if m.hasUnknown then .unknownMmio else .fuelExhausted
  let unsup := unsupportedEvents m
  { arch, endian, entry := entryPc, regions := initM.regions.size, devices := initM.devices.size,
    fuel, stop := if !unsup.isEmpty then .unsupportedInstr else stop,
    lastPc := c.pc.toNat, events := m.trace.size, traceHash := traceHash m,
    descriptorId := descId, unsupported := unsup,
    entrySp, highVectors := highVec, regOverrides := 0 }

def main (argv : List String) : IO Unit := do
  match argv with
  | "import" :: ev :: rest => importCmd ev rest
  | _ =>
  let a := parseArgs argv {}
  if a.desc.isEmpty then throw (IO.userError "usage: sei_cli <descriptor.sei.json> [--fuel N] [--image name=path ...]")
  let text ← IO.FS.readFile a.desc
  let images ← a.images.mapM fun (n, p) => do pure (n, ← loadImage p)
  if a.checkpointIn != "" then
    -- Resume from a prior ARM checkpoint: load (Cpu × Machine), apply fresh --fast flag.
    let (cpu0, m0) ← loadArmCheckpoint a.checkpointIn
    let m0 := { m0 with traceFull := !a.fast }
    let (finalCpu, mFinal) := Sei.Isa.Arm.runArm a.fuel (cpu0, m0)
    let rep := armReport "arm" "little" cpu0.pc.toNat 0 cpu0.highVectors
                 a.fuel a.checkpointIn m0 finalCpu mFinal
    runAndReport rep mFinal a
    if a.checkpointOut != "" then saveArmCheckpoint a.checkpointOut finalCpu mFinal
    IO.println "sei_cli: PASS"
  else
    -- Fresh run: parse descriptor, build machine, run.
    -- For ARM we call runArm directly so we can capture the CPU for --checkpoint-out.
    let h ← IO.ofExcept (parseDescriptor (← IO.ofExcept (Lean.Json.parse text)))
    -- required images check (#3)
    for r in h.regions do
      match r.image with
      | some name => if ¬ images.any (·.1 == name) then
          throw (IO.userError s!"region {r.name} declares image '{name}' but no --image provided")
      | none => pure ()
    let m0 ← IO.ofExcept (loadMachine h images)
    let traceFull := !a.fast
    let m0 := { m0 with traceFull }
    let endian := if h.little then "little" else "big"
    let descId := a.desc
    match h.arch with
    | "mips32" =>
      -- MIPS: no checkpoint-out support yet; fall back to Api.run
      match Sei.Api.run text images a.fuel (traceFull := !a.fast) with
      | .error e => throw (IO.userError s!"sei: {e}")
      | .ok (rep, m) =>
        runAndReport rep m a
        if a.checkpointOut != "" then
          IO.println "checkpoint-out: MIPS checkpoints not yet supported"
        IO.println "sei_cli: PASS"
    | _ =>
      -- ARM (or Thumb): call runArm directly to retain the Cpu
      let baseCpu : Sei.Isa.Arm.Cpu :=
        { pc := BitVec.ofNat 32 h.resetPc,
          tbit := h.arch == "thumb" || h.exceptionState == "thumb",
          highVectors := h.highVectors,
          regs := (default : Sei.Isa.Arm.Cpu).regs.setIfInBounds 13 (BitVec.ofNat 32 h.sp) }
      let cpu0 := h.regOverrides.foldl (fun c (i, v) =>
          { c with regs := c.regs.setIfInBounds i v }) baseCpu
      let (finalCpu, mFinal) := Sei.Isa.Arm.runArm a.fuel (cpu0, m0)
      let rep := armReport h.arch endian h.resetPc h.sp h.highVectors
                   a.fuel descId m0 finalCpu mFinal
      runAndReport rep mFinal a
      if a.checkpointOut != "" then saveArmCheckpoint a.checkpointOut finalCpu mFinal
      IO.println "sei_cli: PASS"
