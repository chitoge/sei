/-
L7 test: promotion & regression discipline. A complete observational artifact is
promotable; the same record over-claiming proof_use: full, or missing source /
validation, is rejected. Semantic hashes are deterministic, and a descriptor-
backed firmware run has a stable hash across re-runs (regression). Exit 0 = pass.
-/
import Sei.Core
import Sei.Api
import Sei.Hw.Promotion
import Sei.Isa.Arm
open Sei.Core Sei.Hw Sei.Api Sei.Isa.Arm

def q (s : String) : String := s.replace "'" "\""

def good : PromotionRecord :=
  { id := "synth.uart", source := "trace dump @0x40000000", cls := .observational, proofUse := .local,
    validation := "advances boot past the UART status poll; does not prove timing/parity",
    unsupported := ["parity", "break-detect"], semanticHash := semanticHash "synth.uart|observational|local" }
def overclaim : PromotionRecord := { good with proofUse := .full }
def noSource : PromotionRecord := { good with source := "" }
def noValidation : PromotionRecord := { good with validation := "" }

-- regression: a descriptor-backed firmware run has a stable semantic hash
def desc : String := q
  "{'cpu':{'arch':'arm','endian':'little'},'entry':{'reset_pc':'0x0'},'memory':[{'name':'rom','base':'0x0','size':'0x1000','kind':'rom','perms':'rx','image':'fw'},{'name':'ram','base':'0x1000','size':'0x1000','kind':'ram','perms':'rw'}],'mmio':{'default_unknown_policy':{'on_read':'default-value','value':'0x0','on_write':'log-drop'}}}"
def fw : ByteArray := bytesToBA (assemble [MOVW 1 0x42, B 0x4 0x4] true)
def runHash : Option Nat := (run desc [("fw", fw)] 30).toOption.map (·.1.traceHash)

def isErr {α} : Except String α → Bool | .error _ => true | .ok _ => false

def checks : List (String × Bool) :=
  [ ("valid_promotion_ok", (promotable good).toOption.isSome),
    ("observational_cannot_be_full", isErr (promotable overclaim)),
    ("missing_source_rejected", isErr (promotable noSource)),
    ("missing_validation_rejected", isErr (promotable noValidation)),
    ("required_fields_present", !good.source.isEmpty && !good.validation.isEmpty && good.unsupported.length > 0),
    ("semantic_hash_deterministic", semanticHash "x" == semanticHash "x" && semanticHash "x" != semanticHash "y"),
    ("regression_hash_stable", runHash.isSome && runHash == (run desc [("fw", fw)] 30).toOption.map (·.1.traceHash)) ]

def main : IO Unit := do
  let mut ok := true
  for (n, b) in checks do
    let tag := if b then "ok" else "FAIL"
    IO.println s!"{n}: {tag}"
    if !b then ok := false
  if !ok then throw (IO.userError "promotion checks failed")
  IO.println "promotion & regression discipline (L7): PASS"
