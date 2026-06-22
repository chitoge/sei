# SEI

SEI runs bare-metal firmware and records everything it does.

You give it a description of the hardware — memory map, entry point, peripherals
— and a firmware binary. SEI executes the firmware under a configurable
instruction limit, logs every memory access, register write, MMIO touch, and
exception as a typed event, then tells you exactly where and why it stopped.

It's built entirely in [Lean 4](https://lean-lang.org). The ISA implementations
are real Lean functions, which means you can run firmware through them *and*
write proofs about their behavior — something you can't do with a C emulator.

## When would you use this?

- **Boot tracing** — you have a firmware binary and want to see what it does
  before an OS loads: which registers it touches, which exceptions fire, where
  it gets stuck.
- **Peripheral discovery** — you want to know which MMIO windows the firmware
  polls, and in what order, so you know what to model next.
- **ISA validation** — you want to check that your instruction model agrees
  with real hardware on specific encodings, using Unicorn-generated test vectors.
- **Formal reasoning** — you want to state and prove properties about ISA
  semantics in Lean, using the same definitions that actually run the firmware.

## How it works in one minute

Write a hardware descriptor (`firmware.sei.json`) that says what memory your
device has and where it starts:

```json
{
  "cpu": { "arch": "arm", "endian": "little" },
  "entry": { "reset_pc": "0x0" },
  "memory": [
    { "name": "flash", "base": "0x0",          "size": "0x40000", "kind": "rom", "perms": "rx", "image": "firmware.bin" },
    { "name": "ram",   "base": "0x20000000",   "size": "0x20000", "kind": "ram", "perms": "rw" }
  ],
  "mmio": { "default_unknown_policy": { "on_read": "default-value", "value": "0x0", "on_write": "log-drop" } }
}
```

Run it:

```bash
./bazel-bin/sei_cli firmware.sei.json \
  --image firmware.bin=path/to/firmware.bin \
  --fuel 500000 \
  --report run.json
```

You'll get back a stop reason (`fuelExhausted`, `halted`, `blockedFrontier`, …),
a count of instructions executed, and a list of unknown MMIO windows the firmware
hit — the **frontier**, which tells you what peripherals to model next.

```
stop=fuelExhausted  lastPc=0x1234  events=498210
frontier @0x40000000  polls=12   class=mmio
frontier @0x40001000  polls=4    class=mmio
```

## ISA support

| Architecture | Status |
|---|---|
| ARM A32 | Complete: ALU, load/store, LDM/STM, branches, exceptions, CP15, LDREX/STREX |
| ARM Thumb (T16/T32) | Core subset: 16-bit ALU/branch/load-store, 32-bit LDM/STM |
| VFP (f16/f32/f64) | Complete: all arithmetic, FMA, VCVT, VCMP; IEEE-754 bit-exact vs Unicorn |
| NEON / Advanced SIMD | Integer and float: bitwise, arithmetic, compare, shift; bit-exact vs Unicorn |
| MIPS32r2 | Complete: ALU, branches, load/store, CP0, TLB, COP1/COP1X, MIPS16e interop |
| MIPS16e | Full decoder: ALU, load/store, branches, EXTEND prefix, JAL/JALX, SAVE/RESTORE |

Every implemented instruction is covered by Unicorn-generated test vectors that
SEI replays byte-for-byte as part of its test suite.

## Building

```bash
# aarch64 host (local build, no remote execution):
bazel build //:sei_cli --config=local --remote_executor=

# x86_64 host (BuildBuddy RBE, the default):
bazel build //:sei_cli

# Run all tests:
bazel test //:all --config=local --remote_executor=
```

No system Lean installation needed — the build pins its own toolchain via
`lean-toolchain` and `rules_lean4`.

## Go deeper

- [Descriptor format](docs/descriptor.md) — the full `.sei.json` field reference
- [ISA coverage](docs/isa.md) — instruction tables and test corpus details
- [Lean API](docs/api.md) — driving SEI from Lean code, trace queries, proofs
