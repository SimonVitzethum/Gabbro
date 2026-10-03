/-
  File:      Grammatik/X86/ComposeFpLedger.lean
  Subject:   FP-ledger closing: every FP operation runs under its site ledger.

  Lane 839: compose the accepted FP producers (Gleitprofil ledger data,
  ScalarFloat step, ScalarFloatCodec fetched bytes, FpControlHardwareForms
  control-word change) into one checked closing step. The ledger entry of a
  scope is its admitted control word; a step runs only when the state word
  matches the ledger entry and the ledger admits it (RNE, masks, no FTZ/DAZ).
  Scope crossing refuses. Nothing here re-proves producer internals and no
  interpreter or executor is duplicated: all facts travel through the
  accepted definitions by name.
-/
import Grammatik.X86.ScalarFloat
import Grammatik.X86.ScalarFloatCodec
import Grammatik.X86.Gleitprofil
import Grammatik.X86.FpControlHardwareForms

namespace Gabbro.Grammatik.X86

/-- The control-state ledger of one scope: the admitted word every FP
    operation at this site runs under. The state word must equal it. -/
abbrev FpLedger := FPKontext

/-- Ledger-guarded single step: admit (RNE, masks, no FTZ/DAZ) AND scope
    match at entry, the accepted `fpSchritt`, then ledger still holds.
    `none` is an explicit refusal (bad ledger, scope crossing, or the
    accepted step's own refusal). -/
def fpLedgerSchritt (k : FpLedger) (d : FpDecodiert)
    (t : FpZustand) : Option FpZustand :=
  match fpEintritt t.fp with
  | false => none
  | true =>
    match decide (t.fp = k) with
    | false => none
    | true =>
      match fpSchritt d t with
      | none => none
      | some t' =>
        match decide (t'.fp = k) with
        | false => none
        | true => some t'

/- CUTS: skeleton only; closing theorems follow.
-/

#print axioms fpEintritt_reset

end Gabbro.Grammatik.X86
