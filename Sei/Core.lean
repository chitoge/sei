/-
SEI semantic core, in Lean — designed for formal methods, not a verbatim port.

Design choices that make proofs easy later:

* **Typed machine words.** `Word := BitVec 32`, `Byte := BitVec 8`. BitVec
  arithmetic wraps mod 2^n automatically (no manual `% 2^32`), is decidable, and
  is supported by `bv_decide`/bitblasting — the right substrate for hardware
  semantics.
* **Effects as data.** The trace is `Array Effect` for a typed `Effect` inductive,
  not stringly-typed dicts — so trace properties are stateable/provable.
  Serialization (`Effect.render`) is a separate, non-semantic concern.
* **Pure, total functions.** The bus and (later) CPU steps are ordinary total
  functions `… → α × Machine` — no `StateM`, no `partial`, no `panic!`. `run`
  is structural on a `Nat` fuel, so runs have an induction principle.
* **Nat addresses** for region arithmetic (so `omega` discharges interval/overlap
  goals — cf. the non-overlap proofs in `Sei/Bus.lean`), `BitVec` for values.

Pure Lean core only (no batteries/mathlib).
-/
namespace Sei.Core

abbrev Word := BitVec 32
abbrev Byte := BitVec 8

/-! ### Fidelity metadata (fidelity-and-semantics-plan; spec-ingestion-workflow)

Every behavior-bearing unit carries a *declared* fidelity class and proof-use,
and every emitted event carries the producing unit's id + class. The class is
declared by the source (not inferred from shape), so an ingested SVD stub
(`spec` layout), a trace-replay model, and a hand-written model can share an
implementation shape yet differ in class. -/

inductive SemClass
  | spec | derived | observational | traceReplay | external | unknown
  deriving DecidableEq, Repr, Inhabited

inductive ProofUse
  | full | local | translationValidation | none
  deriving DecidableEq, Repr, Inhabited

/-- No-gloss enforcement (fidelity plan §Enforcement / workflow no-gloss gates):
    `unknown` is never proof-eligible; non-`spec` classes may not claim
    `proof_use: full`. -/
def validCombo : SemClass → ProofUse → Bool
  | .unknown, pu => pu == ProofUse.none
  | .spec, _ => true
  | _, pu => pu != ProofUse.full

structure SemanticsMeta where
  id : String
  cls : SemClass := .unknown
  proofUse : ProofUse := .none
  source : String := ""
  assumptions : List String := []
  validation : List String := []
  semanticHash : String := ""
  deterministic : Bool := true
  deriving Inhabited

def SemanticsMeta.valid (s : SemanticsMeta) : Bool := validCombo s.cls s.proofUse

/-- Provenance carried on every emitted event. -/
structure EffectMeta where
  semId : Option String
  cls : SemClass
  deriving DecidableEq, Repr, Inhabited

/-- An event's metadata is well-formed (no gloss) when it identifies its
    producing unit, or is an explicit `unknown` frontier event. -/
def EffectMeta.ok (e : EffectMeta) : Bool := e.semId.isSome || e.cls == SemClass.unknown

def coreMeta : EffectMeta := { semId := some "core", cls := .spec }
def unknownMeta : EffectMeta := { semId := none, cls := .unknown }

/-! ### Permissions -/

def permR : Nat := 1
def permW : Nat := 2
def permX : Nat := 4
def hasPerm (perms need : Nat) : Bool := (perms &&& need) == need

def parsePerms (s : String) : Nat :=
  (if s.contains 'r' then permR else 0) |||
  (if s.contains 'w' then permW else 0) |||
  (if s.contains 'x' then permX else 0)

/-! ### Hex rendering (serialization only) -/

def hexv (value width : Nat) : String :=
  let digits := (width + 3) / 4
  let raw := String.ofList (Nat.toDigits 16 (value % (2 ^ width)))
  "0x" ++ String.ofList (List.replicate (digits - raw.length) '0') ++ raw

def Word.hex (w : Word) : String := hexv w.toNat 32

/-! ### Endian byte codec -/

def decodeBytes (little : Bool) (bs : List Byte) : Nat :=
  if little then bs.foldr (fun b acc => b.toNat + 256 * acc) 0
  else bs.foldl (fun acc b => acc * 256 + b.toNat) 0

def encodeBytes (little : Bool) (v width : Nat) : List Byte :=
  let rec go (k val : Nat) : List Byte :=
    match k with
    | 0 => []
    | k + 1 => (BitVec.ofNat 8 (val % 256)) :: go k (val / 256)
  let le := go width v
  if little then le else le.reverse

/-! ### Effects (the typed trace alphabet) -/

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
  | unsupported  (pc : Word) (op : Nat) (mnem : String)   -- coverage: an undecoded instruction
  deriving Repr, DecidableEq, Inhabited

namespace Effect

/-- True for any of the unknown-MMIO frontier effects (used by E04 checks). -/
def isUnknownMmio : Effect → Bool
  | .unknownRead .. | .unknownWrite .. => true
  | _ => false

/-- Verbose diagnostic events that can be suppressed in fast-run mode.
    Mutually exclusive with isUnknownMmio (frontier events are never verbose). -/
def isVerbose : Effect → Bool
  | .fetch .. | .exec .. | .reg .. | .memRead .. | .memWrite .. => true
  | _ => false

def render : Effect → String
  | .fetch a w        => s!"fetch {a.hex} {w.hex}"
  | .exec pc op m     => s!"exec {pc.hex} {hexv op.toNat 8} {m}"
  | .reg i v          => s!"reg r{i} {v.hex}"
  | .memRead a w v    => s!"memRead {a.hex} {w} {v.hex}"
  | .memWrite a w v   => s!"memWrite {a.hex} {w} {v.hex}"
  | .mmioRead d a w v => s!"mmioRead {d} {a.hex} {w} {v.hex}"
  | .mmioWrite d a w v=> s!"mmioWrite {d} {a.hex} {w} {v.hex}"
  | .unknownRead a w v=> s!"unknownRead {a.hex} {w} {v.hex}"
  | .unknownWrite a w v => s!"unknownWrite {a.hex} {w} {v.hex}"
  | .cp15 op n o1 m o2 rt v => s!"cp15 {op} c{n} {o1} c{m} {o2} r{rt} {v.hex}"
  | .exception k vec i => s!"exception {k} {vec.hex} {i}"
  | .irqLine l lvl    => s!"irq {l} {if lvl then 1 else 0}"
  | .timer msg c      => s!"timer {msg} {c.hex}"
  | .note m           => s!"note {m}"
  | .unsupported pc op mn => s!"unsupported {pc.hex} {hexv op 32} {mn}"

end Effect

/-- A trace entry: an effect plus its provenance metadata (fidelity carry). -/
structure Event where
  prov : EffectMeta
  effect : Effect
  deriving DecidableEq, Inhabited

/-! ### Memory -/

inductive Kind where
  | rom | ram | alias
  deriving Inhabited, Repr, BEq

structure Region where
  name : String
  base : Nat
  size : Nat
  kind : Kind
  perms : Nat
  little : Bool
  data : ByteArray := ByteArray.empty
  aliasOf : Option String := none
  /-- A controller-gated region is invisible on the bus until its provider device
      enables it (memory-provider readiness gate). Ordinary RAM/ROM stay `true`. -/
  enabled : Bool := true
  deriving Inhabited

def Region.contains (r : Region) (addr : Nat) : Bool :=
  r.base ≤ addr ∧ addr < r.base + r.size

inductive Fault where
  | unmapped    -- no region contains the address (→ unknown-MMIO frontier)
  | perm        -- in a region, but lacking the needed permission
  | cross       -- starts in a region but runs past its end (audit A1)
  | unknown     -- unmapped access under a strict-fault unknown policy (audit A2)
  deriving Inhabited, Repr, DecidableEq

/-- Shared access-validity predicate (audit A1): the whole `n`-byte access lies
    inside `[0, size)` of the backing region. -/
def accessOk (off n size : Nat) : Bool := 0 < n ∧ off + n ≤ size

/-- Resolve an address to (backing region index, local offset), following an
    alias to its target. Total; returns `none` when unmapped. -/
def resolve (regions : Array Region) (addr : Nat) : Option (Nat × Nat) := Id.run do
  for i in [0:regions.size] do
    let r := regions.getD i default
    if r.contains addr && r.enabled then        -- a gated (disabled) region is invisible
      match r.aliasOf with
      | none => return some (i, addr - r.base)
      | some tgt =>
        match regions.findIdx? (·.name == tgt) with
        | some j => return some (j, addr - r.base)
        | none => return none
  return none

/-- Endian-aware read of `width` bits (8/16/32). Returns value as a `Word` (zero-extended).
    Inlined byte decode: no List allocation and no closure allocation on the hot path. -/
def memRead (regions : Array Region) (addr : Word) (width : Nat) (fetch : Bool := false)
    : Except Fault Word :=
  match resolve regions addr.toNat with
  | none => .error .unmapped
  | some (i, off) =>
    let r := regions.getD i default
    let n := width / 8
    if ¬ hasPerm r.perms (if fetch then permX else permR) then .error .perm
    else if ¬ accessOk off n r.data.size then .error .cross
    else
      -- All reads are bounds-safe: accessOk verified off + n ≤ data.size.
      -- Extra high bytes default to 0 when n < 4 (via Option.getD).
      let v :=
        if r.little then
          match n with
          | 1 => (r.data[off]?.getD 0).toNat
          | 2 => (r.data[off]?.getD 0).toNat ||| ((r.data[off + 1]?.getD 0).toNat <<< 8)
          | _ => (r.data[off]?.getD 0).toNat ||| ((r.data[off + 1]?.getD 0).toNat <<< 8) |||
                 ((r.data[off + 2]?.getD 0).toNat <<< 16) ||| ((r.data[off + 3]?.getD 0).toNat <<< 24)
        else
          match n with
          | 1 => (r.data[off]?.getD 0).toNat
          | 2 => ((r.data[off]?.getD 0).toNat <<< 8) ||| (r.data[off + 1]?.getD 0).toNat
          | _ => ((r.data[off]?.getD 0).toNat <<< 24) ||| ((r.data[off + 1]?.getD 0).toNat <<< 16) |||
                 ((r.data[off + 2]?.getD 0).toNat <<< 8) ||| (r.data[off + 3]?.getD 0).toNat
      .ok (BitVec.ofNat 32 v)

/-- Endian-aware write of the low `width` bits of `value`.
    Inlined byte encode avoids List allocation on the hot path. -/
def memWrite (regions : Array Region) (addr value : Word) (width : Nat)
    : Except Fault (Array Region) :=
  match resolve regions addr.toNat with
  | none => .error .unmapped
  | some (i, off) =>
    let r := regions.getD i default
    let n := width / 8
    if ¬ hasPerm r.perms permW then .error .perm
    else if ¬ accessOk off n r.data.size then .error .cross
    else
      let val := value.toNat
      let data := Id.run do
        let mut ba := r.data
        for k in [0:n] do
          let byte := if r.little then (val >>> (k * 8)) &&& 0xFF
                      else (val >>> ((n - 1 - k) * 8)) &&& 0xFF
          ba := ba.set! (off + k) byte.toUInt8
        return ba
      .ok (regions.setIfInBounds i { r with data := data })

/-! ### Devices -/

/-- A register-file cell with a per-bit access policy (E20). Bits not in any
    mask are plain read/write. -/
structure RegCell where
  offset : Nat
  value : Word
  roMask : Word := 0      -- read-only bits (writes ignored)
  w1cMask : Word := 0     -- write-1-to-clear bits
  corMask : Word := 0     -- clear-on-read bits
  resvMask : Word := 0    -- reserved bits (read as 0, writes ignored)
  deriving Inhabited, Repr, DecidableEq

/-- Apply a register write under the cell's access policy. Writable bits take the
    written value; read-only/reserved bits are kept; w1c bits are cleared where
    the write has a 1. -/
def regWrite (c : RegCell) (value : Word) : Word :=
  let writable := ~~~ (c.roMask ||| c.resvMask ||| c.w1cMask)
  (value &&& writable) ||| (c.value &&& (c.roMask ||| c.resvMask))
    ||| (c.value &&& c.w1cMask &&& ~~~ value)

/-- The value a read returns: reserved bits read as 0. -/
def regRead (c : RegCell) : Word := c.value &&& ~~~ c.resvMask

/-- Explicit sentinel a trace-replay model returns outside its captured envelope
    (E23) — distinguishable from any real fabricated value. -/
def traceFrontier : Word := 0xBADC0DE0

inductive DevBehavior where
  /-- Status register hypothesis: 0 for the first `readyAfter` reads, then
      `readyValue` (cf. E04/E08 unknown-MMIO synthesis). -/
  | statusModel (count : Nat) (readyAfter : Option Nat) (readyValue : Word)
  /-- UART (E07): DR@0x0, SR@0x4 (TXE bit0 ro, RXNE bit1 ro, OVR bit3 w1c),
      CR@0x8 (RXIE bit0, TXIE bit1; bits[31:2] reserved). `tx`/`rx` are byte
      FIFOs. IRQ asserts when RXNE & RXIE. -/
  | uart (tx rx : List Nat) (sr cr : Word)
  /-- Generic register stub: each `(offset, value)` reads back its current value
      and a write updates it. Used to instantiate descriptor `devices[]` whose
      register schema has no modeled behavior yet. -/
  | regStub (regs : List (Nat × Word))
  /-- A register file with per-bit access policy (ingested from SVD/SystemRDL —
      experiment E20). -/
  | regfile (cells : List RegCell)
  /-- Trace-replay (E23): a captured `(offset, value)` response script consumed in
      order (`pos`). A read whose offset doesn't match the next scripted response
      (or past the end) fails closed — it returns the explicit frontier sentinel
      `traceFrontier` and does not advance, never fabricating a plausible value. -/
  | traceReplay (script : List (Nat × Word)) (pos : Nat)
  /-- External/co-sim boundary (E18): a mock external model (e.g. a free-running
      co-sim timer) with a typed read interface and explicit `counter`/`incr`
      state. Pure ⇒ deterministic and snapshot/restorable; not proof-eligible
      beyond boundary-wrapper properties. -/
  | external (name : String) (counter incr : Word)
  /-- DDR/flash-controller model with a readiness gate (lean-descriptor-ir audit
      §DDR / memory-provider). STATUS@0x0 reads ready; a write of `1` to CTRL@0x4
      accepts the init sequence and sets ready, which enables the gated DRAM
      region named `gates` (kept off the bus until then). Observational. -/
  | ddr (ready : Bool) (gates : String)
  /-- Flash controller over a `backing` image (audit §flash). Indirect mode:
      CMD@0x0 selects READ_ID/READ_STATUS/READ; ADDR@0x4 sets the address;
      DATA@0x8 reads the result (READ advances). XIP mode (entered by CMD 0xB7,
      left by 0xFF) reads the backing directly. Unsupported commands fail closed
      (read `traceFrontier`). Pure ⇒ deterministic replay. -/
  | flash (backing : List Word) (cmd addr : Nat) (xip : Bool)
  /-- Watchdog (L4): STATUS@0x0 reads fired (1) once `count` (incremented per
      status read, a time proxy) exceeds `timeout`; SERVICE@0x4 resets the count
      under policy `"serviced"`. Policy `"disabled"` never fires; `"reset"` fires
      after the timeout with no service. -/
  | watchdog (count timeout : Nat) (policy : String)
  deriving Inhabited

structure Device where
  name : String
  base : Nat
  size : Nat
  beh : DevBehavior
  irq : Bool := false
  /-- Declared fidelity metadata (set by the descriptor loader / driver, not
      inferred from `beh`). -/
  sem : SemanticsMeta := { id := "", cls := .unknown }
  deriving Inhabited

/-- Provenance metadata for an effect this device produced. -/
def Device.prov (d : Device) : EffectMeta := { semId := some d.sem.id, cls := d.sem.cls }

def Device.contains (d : Device) (addr : Nat) : Bool :=
  d.base ≤ addr ∧ addr < d.base + d.size

-- UART register field bits.
def UART_TXE  : Word := 1   -- SR bit0
def UART_RXNE : Word := 2   -- SR bit1
def UART_OVR  : Word := 8   -- SR bit3
def UART_RXIE : Word := 1   -- CR bit0

def uartIrq (sr cr : Word) : Bool := (sr &&& UART_RXNE != 0) && (cr &&& UART_RXIE != 0)

def Device.readReg (d : Device) (off _width : Nat) : Word × Device :=
  match d.beh with
  | .statusModel count readyAfter readyValue =>
    let count := count + 1
    let v := match readyAfter with
      | some k => if count > k then readyValue else 0
      | none => 0
    (v, { d with beh := .statusModel count readyAfter readyValue })
  | .uart tx rx sr cr =>
    if off == 0x0 then            -- DR: pop the rx FIFO, update RXNE
      let (v, rx') := match rx with | [] => (0, []) | h :: t => (h, t)
      let sr' := if rx'.isEmpty then sr &&& ~~~ UART_RXNE else sr ||| UART_RXNE
      (BitVec.ofNat 32 v, { d with beh := .uart tx rx' sr' cr, irq := uartIrq sr' cr })
    else if off == 0x4 then (sr, d)
    else if off == 0x8 then (cr, d)
    else (0, d)
  | .regStub regs =>
    ((regs.find? (·.1 == off)).map (·.2) |>.getD 0, d)
  | .regfile cells =>
    match cells.find? (·.offset == off) with
    | some c =>
      -- reserved bits read 0; clear-on-read bits clear after the read
      let cells := cells.map fun c2 =>
        if c2.offset == off then { c2 with value := c2.value &&& ~~~ c2.corMask } else c2
      (regRead c, { d with beh := .regfile cells })
    | none => (0, d)
  | .traceReplay script pos =>
    match script[pos]? with
    | some (o, v) =>
      if o == off then (v, { d with beh := .traceReplay script (pos + 1) })
      else (traceFrontier, d)          -- out of envelope: fail closed
    | none => (traceFrontier, d)        -- script exhausted: fail closed
  | .external nm counter incr =>
    (counter, { d with beh := .external nm (counter + incr) incr })
  | .ddr ready _ =>
    if off == 0x0 then (if ready then 1 else 0, d) else (0, d)        -- STATUS.ready
  | .flash backing cmd addr xip =>
    if off == 0x8 then                                                -- DATA
      if xip then ((backing[addr]?).getD 0, d)
      else match cmd with
        | 0x9F => (0xC2, d)                                           -- READ_ID
        | 0x05 => (1, d)                                              -- READ_STATUS (ready)
        | 0x03 => ((backing[addr]?).getD 0, { d with beh := .flash backing cmd (addr + 1) xip })
        | _ => (traceFrontier, d)                                    -- unsupported: fail closed
    else (0, d)
  | .watchdog count timeout policy =>
    if off == 0x0 then                                              -- STATUS (advances the timer)
      let count := count + 1
      (if policy != "disabled" && count > timeout then 1 else 0,
       { d with beh := .watchdog count timeout policy })
    else (0, d)

def Device.writeReg (d : Device) (off _width : Nat) (value : Word) : Device :=
  match d.beh with
  | .statusModel .. => d
  | .regStub regs =>
    { d with beh := .regStub (regs.map (fun p => if p.1 == off then (p.1, value) else p)) }
  | .regfile cells =>
    { d with beh := .regfile (cells.map fun c =>
        if c.offset == off then { c with value := regWrite c value } else c) }
  | .traceReplay .. => d                  -- replay is read-driven; writes ignored
  | .external .. => d                     -- external boundary: writes are a no-op here
  | .ddr ready gates =>                     -- CTRL@0x4 = 1 accepts the init sequence
    if off == 0x4 && value == 1 then { d with beh := .ddr true gates } else { d with beh := .ddr ready gates }
  | .flash backing cmd addr xip =>
    if off == 0x0 then                       -- CMD (0xB7 enter XIP, 0xFF exit XIP)
      let v := value.toNat
      { d with beh := .flash backing v addr (if v == 0xB7 then true else if v == 0xFF then false else xip) }
    else if off == 0x4 then { d with beh := .flash backing cmd value.toNat xip }  -- ADDR
    else d
  | .watchdog count timeout policy =>          -- SERVICE@0x4 kicks the dog (policy "serviced")
    if off == 0x4 && policy == "serviced" then { d with beh := .watchdog 0 timeout policy } else d
  | .uart tx rx sr cr =>
    if off == 0x0 then            -- DR: transmit
      { d with beh := .uart (tx ++ [(value &&& 0xff).toNat]) rx sr cr }
    else if off == 0x4 then       -- SR: write-1-to-clear OVR; TXE/RXNE read-only
      let sr' := if value &&& UART_OVR != 0 then sr &&& ~~~ UART_OVR else sr
      { d with beh := .uart tx rx sr' cr }
    else if off == 0x8 then       -- CR: only RXIE/TXIE writable; reserved ignored
      let cr' := value &&& 0x3
      { d with beh := .uart tx rx sr cr', irq := uartIrq sr cr' }
    else d

/-- Host-side RX delivery (a byte arriving on the wire); not a bus access. -/
def Device.uartRxPush (d : Device) (byte : Nat) : Device :=
  match d.beh with
  | .uart tx rx sr cr =>
    let sr := if sr &&& UART_RXNE != 0 then sr ||| UART_OVR else sr   -- overrun if unread
    let sr := sr ||| UART_RXNE
    { d with beh := .uart tx (rx ++ [byte &&& 0xff]) sr cr, irq := uartIrq sr cr }
  | _ => d

/-! ### Machine (pure substrate) -/

/-- Unknown-MMIO policy (audit A2): return the configured default, or fault. -/
inductive UnknownPolicy where
  | defaultValue | fault
  deriving Inhabited, Repr, DecidableEq

structure Machine where
  regions : Array Region := #[]
  devices : Array Device := #[]
  trace : Array Event := #[]
  icount : Nat := 0
  unknownDefault : Word := 0
  unknownRead : UnknownPolicy := .defaultValue
  unknownWrite : UnknownPolicy := .defaultValue
  /-- Set when any unknownRead/unknownWrite has been emitted; O(1) frontier check. -/
  hasUnknown : Bool := false
  /-- When false, verbose events (fetch/exec/reg/memRead/memWrite) are dropped from
      the trace — only frontier and MMIO events are kept. Enables fast CLI runs. -/
  traceFull : Bool := true
  deriving Inhabited

/-- Emit an effect with explicit provenance metadata.
    In fast mode (!traceFull), verbose events are dropped to avoid trace allocation. -/
def Machine.emitM (m : Machine) (prov : EffectMeta) (e : Effect) : Machine :=
  if !m.traceFull && e.isVerbose then m  -- fast path: no alloc, no push
  else
    { m with trace := m.trace.push { prov := prov, effect := e },
             hasUnknown := m.hasUnknown || e.isUnknownMmio }

/-- Emit a core (memory / CPU) effect: provenance is the trusted core (`spec`). -/
def Machine.emit (m : Machine) (e : Effect) : Machine := m.emitM coreMeta e

/-- The effects only (drops metadata) — for predicates/proofs that match on
    `Effect` shape rather than provenance. -/
def Machine.effects (m : Machine) : Array Effect := m.trace.map (·.effect)

def Machine.findDev (m : Machine) (addr : Nat) : Option Nat :=
  m.devices.findIdx? (·.contains addr)

/-- Bus read: device window → memory → unknown-MMIO frontier. Returns the result
    (faults propagate; the CPU turns `perm` into a data abort) and the updated
    machine (device state + emitted effect). Pure and total. -/
def Machine.busRead (m : Machine) (addr : Word) (width : Nat) (fetch : Bool := false)
    : Except Fault Word × Machine :=
  match m.findDev addr.toNat with
  | some di =>
    let d := m.devices.getD di default
    if ¬ accessOk (addr.toNat - d.base) (width / 8) d.size then
      (.error .cross, m.emitM d.prov (.note "device access crosses window end"))  -- finding 4
    else
    let (v, d') := d.readReg (addr.toNat - d.base) width
    let m := { m with devices := m.devices.setIfInBounds di d' }
    (.ok v, m.emitM d.prov (.mmioRead d.name addr width v))
  | none =>
    match memRead m.regions addr width fetch with
    | .ok v =>
      (.ok v, m.emit (if fetch then .fetch addr v else .memRead addr width v))
    | .error .perm => (.error .perm, m)
    | .error .cross => (.error .cross, m)          -- A1: propagate, never frontier
    | .error _ =>                                  -- unmapped → unknown-MMIO frontier
      let v := BitVec.ofNat 32 (m.unknownDefault.toNat % (2 ^ width))
      let m := m.emitM unknownMeta (.unknownRead addr width v)
      match m.unknownRead with
      | .defaultValue => (.ok v, m)
      | .fault => (.error .unknown, m)             -- A2: strict-fault mode faults

def Machine.busWrite (m : Machine) (addr value : Word) (width : Nat)
    : Except Fault Unit × Machine :=
  match m.findDev addr.toNat with
  | some di =>
    let d := m.devices.getD di default
    if ¬ accessOk (addr.toNat - d.base) (width / 8) d.size then
      (.error .cross, m.emitM d.prov (.note "device access crosses window end"))  -- finding 4
    else
    let d' := d.writeReg (addr.toNat - d.base) width value
    let m := { m with devices := m.devices.setIfInBounds di d' }
    -- memory-provider: a controller that just became ready enables its gated region
    let m := match d'.beh with
      | .ddr true gates =>
        { m with regions := m.regions.map (fun (r : Region) => if r.name == gates then { r with enabled := true } else r) }
      | _ => m
    (.ok (), m.emitM d.prov (.mmioWrite d.name addr width value))
  | none =>
    match memWrite m.regions addr value width with
    | .ok regions => (.ok (), { m with regions := regions }.emit (.memWrite addr width value))
    | .error .perm => (.error .perm, m)
    | .error .cross => (.error .cross, m)          -- A1: propagate, never frontier
    | .error _ =>                                  -- unmapped → unknown-MMIO frontier
      let m := m.emitM unknownMeta (.unknownWrite addr width value)
      match m.unknownWrite with
      | .defaultValue => (.ok (), m)               -- "log-drop"
      | .fault => (.error .unknown, m)             -- A2: strict-fault mode faults

/-! ### Builders -/

/-- Convert a `List Byte` to a `ByteArray` (for small instruction/program images). -/
def bytesToBA (l : List Byte) : ByteArray :=
  l.foldl (fun ba b => ba.push b.toNat.toUInt8) ByteArray.empty

def mkRegion (name : String) (base size : Nat) (kind : Kind) (perms : Nat)
    (little : Bool) (image : ByteArray := ByteArray.empty) (aliasOf : Option String := none) : Region :=
  let data := if kind == Kind.alias then ByteArray.empty
              else
                let n := min image.size size
                (image.extract 0 n).append (ByteArray.mk (Array.replicate (size - n) (0 : UInt8)))
  { name, base, size, kind, perms, little, data, aliasOf }

/-! ### Well-formed bus (audit A3): non-overlapping decode -/

/-- Half-open windows `[b1,b1+s1)` and `[b2,b2+s2)` overlap. -/
def overlaps (b1 s1 b2 s2 : Nat) : Bool := decide (b1 < b2 + s2 ∧ b2 < b1 + s1)

/-- Memory regions are pairwise non-overlapping. Aliases ARE included: `resolve`
    treats an alias window as an addressable decode range, so an alias that
    overlaps another region (or alias) is an ambiguous decode and is rejected. -/
def regionsNonOverlap (regions : Array Region) : Bool := Id.run do
  for i in [0:regions.size] do
    for j in [0:regions.size] do
      if i < j then
        let a := regions.getD i default
        let b := regions.getD j default
        if overlaps a.base a.size b.base b.size then return false
  return true

/-- Device MMIO windows are pairwise non-overlapping. -/
def devicesNonOverlap (devices : Array Device) : Bool := Id.run do
  for i in [0:devices.size] do
    for j in [0:devices.size] do
      if i < j then
        if overlaps (devices.getD i default).base (devices.getD i default).size
                    (devices.getD j default).base (devices.getD j default).size then return false
  return true

/-- No device MMIO window overlaps any memory region (including alias decode
    windows). By default a device may not shadow memory; an explicit overlay
    would have to opt in. -/
def devicesVsMemoryDisjoint (regions : Array Region) (devices : Array Device) : Bool := Id.run do
  for d in devices do
    for r in regions do
      if overlaps d.base d.size r.base r.size then return false
  return true

/-- A machine has an unambiguous bus decode when memory regions, device windows,
    and device-vs-memory windows are pairwise non-overlapping. Constructors and
    loaders reject machines that fail this (executable counterpart of descriptor
    A3 validation; the device-vs-memory clause closes the "device shadows memory"
    case). -/
def Machine.busWellFormed (m : Machine) : Bool :=
  regionsNonOverlap m.regions && devicesNonOverlap m.devices &&
  devicesVsMemoryDisjoint m.regions m.devices

/-- A total `run`: iterate `step` until it reports termination or `fuel` runs out.
    Structural on `fuel`, so runs are amenable to induction. `step` returns the
    next state and `none` to stop. -/
def run {σ : Type} (step : σ → σ × Bool) : Nat → σ → σ
  | 0, s => s
  | fuel + 1, s =>
    let (s', cont) := step s
    if cont then run step fuel s' else s'

end Sei.Core
