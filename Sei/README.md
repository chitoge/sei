# SEI semantic core in Lean

The "core idea" — the SEI emulator semantics — implemented directly in **Lean 4**,
built and run on **remote execution** via [`rules_lean4`](../MODULE.bazel). There
is **no Python in the semantic core**: memory, bus, devices, traces, snapshots,
and the toy/ARM/MIPS interpreters are all Lean.

```bash
bazel test //:all      # builds + runs every target below on RBE
```

## Design (built for formal methods, not a verbatim port)

- **Typed `BitVec` words** (`Word = BitVec 32`, `Byte = BitVec 8`). Arithmetic
  wraps mod 2^n automatically and is `bv_decide`-friendly — no manual masking.
- **Effects as data.** The trace is `Array Effect` for a typed `Effect`
  inductive, so trace properties are stateable and provable. Serialization
  (`Effect.render`) is separated from semantics.
- **Pure, total functions.** Bus and CPU steps are `… → α × Machine` — no
  `StateM`, no `partial`, no `panic!`. `run` is structural on `Nat` fuel, so runs
  have an induction principle.
- **Nat addresses** keep region interval/overlap goals in `omega`'s reach.

## Files

| File | What |
|------|------|
| `Sei/Core.lean` | substrate: `Word`/`Byte`, `Effect`, memory regions + faults, bus + unknown-MMIO frontier, devices (status model + UART), `Machine`, total `run` |
| `Sei/Isa/Toy.lean` | toy ISA (pure small-step) |
| `Sei/Isa/Arm.lean` | classic ARM A32 slice (reset + exceptions) |
| `Sei/Isa/Mips.lean` | MIPS32 slice (CP0, timer, TLB, delay slots) |
| `Sei/Drivers/*.lean` | the experiments as Lean executables (asserting success signals) |
| `Sei/{Endian,Bus,Device,Equiv}.lean` | standalone proofs (E10) |
| `Sei/CoreProofs.lean` | proofs **about** the executable core |

## Experiment → Lean target

| Experiment | Lean target |
|---|---|
| E01 endian memory/traces | `//:core_smoke_test` (LE/BE) + `decodeBytes_singleton` proof |
| E02 ARM reset slice | `//:arm_exp_test` |
| E03 ARM exceptions / high vectors | `//:arm_exp_test` |
| E04 unknown-MMIO frontier loop | `//:toy_exp_test` |
| E05 MIPS32 CP0/timer/TLB | `//:mips_exp_test` |
| E07 device DSL + behavior overlay | `//:device_exp_test` |
| E08 snapshot determinism + fork | `//:toy_exp_test` (pure ⇒ near-trivial) |
| E09 two-backend equivalence | `//:toy_equiv_test` (core-backed vs `Sei.Isa.ToyAlt`) |
| E10 formal checks | `//:proofs_test`, `//:core_proofs_test` |
| E00/E06 descriptor ingestion | `//:hw_exp_test` (`Sei/Hw/Descriptor.lean`) |
| E06 adapter producer | `//:adapter_test` (`Sei/Hw/Adapter.lean`) |
| E18 external boundary | `//:external_test` |
| E19 multi-source import smoke | `//:multi_test` |
| E20 register-source ingestion | `//:reg_test` |
| E21 topology-source ingestion | `//:topo_test` |
| E22 raw P-code -> SEI IR slice | `//:pcode_test` |
| E23 trace/HIL replay model | `//:trace_test` |
| E24 DDR controller (gated memory) | `//:ddr_test` (memory-provider readiness gate) |
| E25 flash controller | `//:flash_test` (backing image, XIP/indirect, fail-closed) |
| N4 ARM/MIPS fidelity | `//:arm_bank_test` (banked SP/LR), `//:arm_thumb_test` (Thumb exec), `//:mips_bd_test`, `//:mips_tlb_test` |
| contract hardening | `//:store_fault_test` (no swallowed write faults); fail-closed parsers/bounds in `//:hw_exp_test`/`//:reg_test` |

**Descriptor ingestion (E00/E06) is now in Lean** (`Sei/Hw/Descriptor.lean`):
`loadJson` parses a `.sei.json` (via `Lean.Data.Json`), validates it, and builds
a `Machine`, **failing closed** on a dangling alias or an overlapping
(ambiguous) bus (audit A3) and honoring the unknown-MMIO fault policy (A2).
`//:hw_exp_test` ingests several committed descriptor fixtures
and runs negative tests (overlapping regions, dangling alias, alias overlap,
device shadowing memory, cross-window device accesses, and strict fault policy).
`busWellFormed` rejects ambiguous memory/device/alias decode.

**Descriptor-driven CPU bring-up** (`//:hw_bringup_test`): a descriptor plus a
firmware image instantiate a `Machine`, and the ARM interpreter runs from the
descriptor's `reset_pc`, reproducing the E02 reset-slice signals (stack, CP15
write/MIDR, MMIO frontier, stack store, branch-to-self) through the descriptor
path. The shadowrealm `model-*.json` -> descriptor adapter producer is also
ported to Lean (`Sei/Hw/Adapter.lean`, `//:adapter_test`). RISC-V (E11) is
deferred by design.

The descriptor/IR audit findings are resolved: store-fault propagation in Toy/IR/MIPS (`//:store_fault_test`),
fail-closed imported-field parsing (`Except` enum/range parsers + negatives), true
memory-provider gating for DDR/flash (a region is off the bus until its controller
is ready), and actual Thumb execution (16-bit fetch + minimal T16 slice). The
remaining large items are a full Thumb decoder, a Cortex-M ISA, and a complete
Sail/SLEIGH importer.

Notes:
- Traces are produced as typed `Effect` logs and **verified inside each driver**
  (via typed predicates over `Machine.trace`) rather than written to `.jsonl`
  files; `Effect.render` is available for serialization if disk artifacts are
  wanted.
- The ARM/MIPS assemblers are checked against **known-hardware encoding
  constants** (`enc_*` goldens in `ArmExp`/`MipsExp`), so they are not merely
  self-consistent with their decoders. E09's toy equivalence is between two
  independent **Lean** backends — the core-backed `Sei.Isa.Toy` over the real
  bus/typed effects, and the Nat-based flat-state `Sei.Isa.ToyAlt`.

## Why the pure design pays off

- **Determinism** (E08) is definitional: `runToy` is a function, so two runs are
  equal by construction; a "snapshot" is just a value, so fork independence needs
  no copying.
- **Proofs run on the real definitions** (`Sei/CoreProofs.lean`): e.g.
  `busRead_preserves_regions` is discharged on the same `Machine.busRead` the
  emulator executes — found real bugs along the way (the typed effect log made
  the MIPS timer/branch bugs obvious).
