# Descriptor format (`.sei.json`)

A SEI descriptor is a JSON file that describes the hardware your firmware runs
on. It tells SEI where memory lives, where the CPU starts, and what to do when
the firmware accesses an address that doesn't map to anything you've modelled.

You pass it to `sei_cli` as the first argument. Backing images (ROM contents,
flash dumps) are supplied separately with `--image name=path` — the descriptor
just names them.

## Minimal example

This is enough to run most simple bare-metal ARM firmware:

```json
{
  "cpu": { "arch": "arm", "endian": "little" },
  "entry": { "reset_pc": "0x0" },
  "memory": [
    {
      "name": "flash",
      "base": "0x0",
      "size": "0x40000",
      "kind": "rom",
      "perms": "rx",
      "image": "firmware.bin"
    },
    {
      "name": "ram",
      "base": "0x20000000",
      "size": "0x20000",
      "kind": "ram",
      "perms": "rw"
    }
  ],
  "mmio": {
    "default_unknown_policy": {
      "on_read":  "default-value",
      "value":    "0x0",
      "on_write": "log-drop"
    }
  }
}
```

Run it:

```bash
./bazel-bin/sei_cli firmware.sei.json \
  --image firmware.bin=build/out.bin \
  --fuel 200000 \
  --report report.json
```

## `cpu`

```json
"cpu": { "arch": "arm", "endian": "little" }
```

| Field | Values | Notes |
|-------|--------|-------|
| `arch` | `"arm"`, `"thumb"`, `"mips32"` | `"thumb"` starts the CPU in Thumb state |
| `endian` | `"little"`, `"big"` | Applies to all memory regions |

## `entry`

```json
"entry": {
  "reset_pc":        "0x08000000",
  "sp":              "0x20020000",
  "exception_state": "thumb",
  "reg_overrides":   [[0, "0x1"], [1, "0x2"]]
}
```

| Field | Required | Notes |
|-------|----------|-------|
| `reset_pc` | yes | Where the CPU starts (hex string) |
| `sp` | no | Initial stack pointer |
| `exception_state` | no | `"thumb"` to start executing Thumb instructions |
| `reg_overrides` | no | `[[register_index, value], …]` — pre-load registers before reset |

All addresses are hex strings (`"0x..."`) or plain decimal numbers.

## `memory`

Each entry in the `memory` array defines one region on the address bus.

```json
{
  "name":  "sram",
  "base":  "0x20000000",
  "size":  "0x20000",
  "kind":  "ram",
  "perms": "rw"
}
```

| Field | Required | Notes |
|-------|----------|-------|
| `name` | yes | Unique identifier for this region |
| `base` | yes | Start address (hex string) |
| `size` | yes | Size in bytes (hex string) |
| `kind` | yes | `"rom"` (read-only, backed by image), `"ram"` (read-write), `"alias"` (mirror of another region) |
| `perms` | yes | Any combination of `r`, `w`, `x` — e.g. `"rx"`, `"rw"`, `"rwx"` |
| `image` | no | Name of the backing image, supplied via `--image name=path` |

**Images are mandatory when declared.** If a region has `"image": "firmware.bin"`
and you don't pass `--image firmware.bin=...`, SEI refuses to start rather than
silently zero-filling the region.

**Alias regions** mirror another region by name:

```json
{ "name": "boot-alias", "base": "0x0", "size": "0x40000", "kind": "alias", "aliasOf": "flash", "perms": "rx" }
```

**Overlapping regions are rejected.** SEI validates the bus on load; ambiguous
decode (two regions claiming the same address) is an error, not a silent
priority race.

## `mmio`

The `mmio` section controls what happens when the firmware reads or writes an
address that doesn't belong to any region or device.

```json
"mmio": {
  "default_unknown_policy": {
    "on_read":  "default-value",
    "value":    "0x0",
    "on_write": "log-drop"
  }
}
```

| `on_read` / `on_write` | Behaviour |
|------------------------|-----------|
| `"default-value"` | Return `value` (reads) or silently drop (writes); log the access as a frontier event |
| `"log-drop"` | Log and drop without faulting |
| `"fault"` | Halt the run with `stop=unknownMmio` |

The frontier events accumulate in the run report as `FrontierTask` entries,
telling you which MMIO windows the firmware touches so you know what to model
next.

## `devices`

Devices let you attach lightweight peripheral models to specific address windows.
SEI ships a handful of built-in device types:

| `type` | What it does |
|--------|-------------|
| `ddr` | DDR controller — gates a RAM region until initialised; firmware polls it until the ready bit is set |
| `watchdog` | Watchdog timer — configured with `timeout` (poll count) and `policy` (`"disabled"`, `"serviced"`, `"reset"`) |
| `uart` | UART stub — swallows writes, returns 0xFF on reads (TX-ready bit set) |
| `timer` | Increasing timer — each read returns the previous value plus `step` |

```json
"devices": [
  {
    "name":  "ddr-ctrl",
    "base":  "0x10004000",
    "size":  "0x1000",
    "type":  "ddr",
    "gates": "dram",
    "sem": { "id": "ddr-ctrl", "class": "observational" }
  }
]
```

The `"sem"` object declares the fidelity of this peripheral model: `"spec"` for
models derived from a datasheet, `"observational"` for models inferred from
firmware behaviour, `"unknown"` for stubs where you're not sure yet.

## `--fast` and `--trace-tail`

Two CLI flags are worth knowing:

- `--fast` suppresses per-instruction events (fetch, exec, register writes,
  memory reads/writes) from the trace. Only MMIO, exceptions, and frontier
  events are kept. Useful when you're running millions of instructions and don't
  need the full log.
- `--trace-tail N` prints the last N lines of the trace after the run, without
  writing the full log to disk.

## Checkpoint save and resume (ARM)

For long runs, you can save the CPU and memory state mid-way and resume later:

```bash
# Run 100k instructions, save state:
./bazel-bin/sei_cli firmware.sei.json --image firmware.bin=... \
  --fuel 100000 --checkpoint-out ckpt.json

# Resume where you left off:
./bazel-bin/sei_cli firmware.sei.json \
  --checkpoint-in ckpt.json --fuel 500000 --report run2.json
```

The checkpoint contains the full CPU register file and all RAM contents.
Resuming skips descriptor parsing and goes straight back to execution.
