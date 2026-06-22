# Lean API

SEI is a Lean 4 library. If you're writing a Lean program and want to run
firmware, query its trace, or prove something about its behaviour, this is
the surface you use.

Everything in `Sei.Api` operates on plain immutable Lean values — no
handles, no callbacks, no mutable state. The machine is just a value you
pass around.

## Loading a machine

```lean
import Sei.Api
open Sei.Api Sei.Core

-- Parse a descriptor string and supply backing images.
-- Returns an error string if the descriptor is invalid (overlapping
-- regions, missing image, dangling alias, etc.).
def load (descText : String) (images : List (String × ByteArray) := [])
    : Except String Machine
```

Example:

```lean
def descJson : String := "{\"cpu\":{\"arch\":\"arm\",\"endian\":\"little\"},
  \"entry\":{\"reset_pc\":\"0x0\"}, ...}"

def main : IO Unit := do
  let img ← IO.FS.readBinFile "firmware.bin"
  match load descJson [("firmware.bin", img)] with
  | .error e => IO.println s!"load failed: {e}"
  | .ok m    => IO.println s!"loaded: {m.regions.size} regions"
```

## Running firmware

```lean
-- Run a descriptor + images under a fuel bound.
-- Returns the run report and the final machine state.
def run (descText : String) (images : List (String × ByteArray)) (fuel : Nat)
        (traceFull : Bool := true)
    : Except String (RunReport × Machine)
```

`traceFull := false` omits per-instruction events (fetch/exec/reg/mem) from
the trace for speed. Only MMIO, exceptions, and frontier events are kept.

### Stop reasons

The run always terminates. `RunReport.stop` tells you why:

| `StopReason` | What happened |
|---|---|
| `fuelExhausted` | Hit the instruction limit — the normal outcome for bounded runs |
| `halted` | CPU reached a self-branch (spin loop) or explicit halt |
| `blockedFrontier` | Stalled waiting on an unknown MMIO window |
| `unsupportedInstr` | Reached an instruction SEI doesn't implement yet |
| `unknownMmio` | Unmapped access under a `"fault"` unknown policy |
| `controllerWait` | Waiting for a DDR or flash controller to become ready |
| `timerWait` | Waiting on a hardware timer |
| `exceptionLoop` | Exception handler cycling without forward progress |

`rep.unsupported` is a list of `(PC, opcode, mnemonic)` for every unimplemented
instruction encountered. If the list is non-empty, `stop` will be
`unsupportedInstr`.

## Reading and writing memory

```lean
-- Read width bytes at addr. Returns a fault or the value, plus updated machine.
def memRead  (m : Machine) (addr : Nat) (width : Nat := 32)
    : Except Fault Word × Machine

-- Write val to addr. Returns a fault or unit, plus updated machine.
def memWrite (m : Machine) (addr : Nat) (val : Word) (width : Nat := 32)
    : Except Fault Unit × Machine
```

`Fault` has four constructors: `unmapped`, `perm`, `cross` (access spans a
region boundary), and `unknown` (unmapped under strict policy).

## Adding and removing regions and devices

```lean
-- Add a region; fails if it overlaps an existing one.
def addRegion    (m : Machine) (r : Region)      : Except String Machine

-- Add a device; fails if its window overlaps.
def addDevice    (m : Machine) (d : Device)      : Except String Machine

-- Remove a device by name (silent no-op if not found).
def removeDevice (m : Machine) (name : String)   : Machine
```

These are the right way to build up a machine incrementally in code, rather
than always going through a descriptor JSON string.

## Snapshot, restore, fork

```lean
def snapshot (m : Machine) : Machine            -- returns m unchanged
def restore  (snap : Machine) : Machine         -- returns snap unchanged
def fork     (m : Machine) : Machine × Machine  -- returns (m, m)
```

These look trivial because the machine is an immutable value. There is no
copying — "taking a snapshot" just means binding the current machine to a
name. You can run two forks down different paths for free:

```lean
let (branchA, branchB) := fork m
let (_, mA) := runArm 10000 (cpuA, branchA)
let (_, mB) := runArm 10000 (cpuB, branchB)
-- mA and mB diverged from the same machine state
```

## Querying the trace

SEI doesn't have live callbacks. Instead, every step appends a typed `Effect`
to the machine's trace. After the run, you filter the trace:

```lean
-- General filter — returns all events matching pred.
def hookEvents (m : Machine) (pred : Effect → Bool) : List Effect

-- Shorthand: all PCs of executed instructions.
def codeHook (m : Machine) : List Word

-- Shorthand: all addresses of MMIO accesses (reads or writes).
def mmioHook (m : Machine) : List Word
```

The `Effect` type covers everything the CPU and bus can do:

```lean
inductive Effect where
  | fetch        (addr word : Word)
  | exec         (pc : Word) (op : Byte) (mnem : String)
  | reg          (idx : Nat) (val : Word)
  | memRead      (addr : Word) (width : Nat) (val : Word)
  | memWrite     (addr : Word) (width : Nat) (val : Word)
  | mmioRead     (dev : String) (addr : Word) (width : Nat) (val : Word)
  | mmioWrite    (dev : String) (addr : Word) (width : Nat) (val : Word)
  | unknownRead  (addr : Word) (width : Nat) (val : Word)
  | unknownWrite (addr : Word) (width : Nat) (val : Word)
  | cp15         (op : String) (crn opc1 crm opc2 rt : Nat) (val : Word)
  | exception    (kind : String) (vector : Word) (info : Nat)
  | irqLine      (line : String) (level : Bool)
  | timer        (msg : String) (count : Word)
  | note         (msg : String)
  | unsupported  (pc : Word) (op : Nat) (mnem : String)
```

A few real examples:

```lean
-- Did the firmware touch a specific MMIO window?
let ddrHits := hookEvents m fun e => match e with
  | .mmioRead _ addr _ _ | .mmioWrite _ addr _ _ =>
      addr.toNat >= 0x10004000 && addr.toNat < 0x10005000
  | _ => false

-- Did any exception fire?
let exceptions := hookEvents m fun e => match e with
  | .exception .. => true | _ => false

-- What CP15 registers did the firmware read?
let cp15reads := hookEvents m fun e => match e with
  | .cp15 "read" .. => true | _ => false
```

## Frontier tasks

When the firmware accesses an address that doesn't belong to any modelled
region or device, SEI records it as a frontier event and accumulates it into
a `FrontierTask`:

```lean
structure FrontierTask where
  address        : Nat          -- the unmapped address
  widths         : List Nat     -- access widths seen (1, 2, or 4 bytes)
  pollCount      : Nat          -- how many times the firmware touched this window
  candidateClass : FrontierClass
```

`FrontierClass` gives a hint about what kind of peripheral this might be:
`mmio` (arbitrary register), `controller` (polled for a ready bit),
`timer` (value increases on each read), or `unknown`.

```lean
def exportFrontier (m : Machine) : List FrontierTask
```

The frontier is the most actionable output of a run — it tells you exactly
what to model next to make the firmware go further.

## Exporting results

```lean
-- The full trace as rendered text lines (one Effect per line).
def exportTrace (m : Machine) : List String

-- Machine-readable JSON report + frontier.
def reportJson (rep : RunReport) (m : Machine) : Json
```

`reportJson` produces the same JSON that `--report` writes from the CLI.

## Writing proofs

Because `runArm` and `runMips` are ordinary pure Lean functions, you can
reason about them with Lean's proof tools. `Sei/CoreProofs.lean` has examples:

```lean
-- busRead never changes the region list.
theorem busRead_preserves_regions (m : Machine) (a : Word) (w : Nat) :
    (m.busRead a w).2.regions = m.regions := by ...

-- Two independent backends agree on all inputs (E09).
theorem toyEquiv (prog : List Word) (n : Nat) :
    runToy n prog = runToyAlt n prog := by ...
```

The fuel argument is a plain `Nat`, so you can induct on it:

```lean
theorem run_terminates (fuel : Nat) (c : Cpu) (m : Machine) :
    ∃ c' m', runArm fuel (c, m) = (c', m') := ⟨_, _, rfl⟩
```

## Source files

| File | Role |
|------|------|
| `Sei/Api.lean` | The public API surface (`load`, `run`, `memRead`, hooks, export) |
| `Sei/Core.lean` | `Word`, `Byte`, `Effect`, `Region`, `Fault`, `Machine`, the bus |
| `Sei/CoreProofs.lean` | Proofs about the core definitions |
| `Sei/Isa/Arm.lean` | ARM A32/T16/T32, VFP, NEON implementation |
| `Sei/Isa/Mips.lean` | MIPS32r2 and MIPS16e implementation |
| `Sei/Hw/Runner.lean` | Bounded run loop, `StopReason`, `RunReport` |
| `Sei/Hw/Frontier.lean` | `FrontierTask` accumulation |
| `Sei/Hw/Descriptor.lean` | Parse and validate `.sei.json` |
| `Sei/Float.lean` | IEEE-754 soft-float (f16/f32/f64) |
| `Sei/Simd.lean` | NEON / Advanced SIMD substrate |
| `Sei/IR.lean` | Typed effect IR (for future Sail/SLEIGH importers) |
| `Sei/Equiv.lean` | Equivalence proof infrastructure |
