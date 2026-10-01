/-
  File:      Grammatik/X86/ValidationBudget.lean
  Subject:   Fail-closed fuel/resource-limited decode and entry traversal.

  Lane 431 (Lean-first reserve): bounded validation helpers over the
  canonical decoder (`Codec.decode`) and the canonical image checks
  (`Bild.eintragEnthalten`). A timed-out or refused traversal answers
  `none`/`false`, never acceptance; an accepted prefix never bypasses
  remaining bytes or entries. No timing, cost or full-validator claim.
-/
import Grammatik.X86.Codec
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Bild

namespace Gabbro.Grammatik.X86

/-- Fuel-bounded decode traversal over actual canonical bytes. -/
def decodeFuel : Nat → List Byte → Option (List Decodiert × List Byte)
  | 0, _ => none
  | _ + 1, [] => some ([], [])
  | n + 1, bs =>
    match decode bs with
    | none => none
    | some (d, rest) =>
      if d.laenge + rest.length == bs.length && laengeOk d.laenge then
        match decodeFuel n rest with
        | none => none
        | some (ins, rest') => some (d :: ins, rest')
      else none

/-- Full acceptance under fuel: traversal succeeds with no rest. -/
def validAllFuel (fuel : Nat) (bs : List Byte) : Bool :=
  match decodeFuel fuel bs with
  | some (_, []) => true
  | _ => false

/-- Fuel-bounded entry check: every entry must satisfy `ok`. -/
def entriesOkFuel : Nat → List Nat → (Nat → Bool) → Bool
  | 0, [], _ => true
  | 0, _ :: _, _ => false
  | _ + 1, [], _ => true
  | n + 1, e :: es, ok => ok e && entriesOkFuel n es ok

end Gabbro.Grammatik.X86
