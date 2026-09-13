/-
  File:     Grammatik/ZeugnisIdent.lean
  Subject:  Term identity for expression certificates (Lean side).

  Lane 146 found that nothing proves the printed certificate describes the
  SAME term the checker checked (`certemit.rs` books
  "printer-prints-what-was-checked is trust base there"). This file closes
  the Lean half: a Lean-side `printInt` from typed `Expr` terms (the int
  fragment covered by `CertExpr` in `Zeugnis.lean`) to certificates, a
  computational `elabInt` (Option-returning, no choice inside), and
  `print_elab` -- print then elab round-trips to the same term, proved by
  induction over every `Expr` constructor (the 17 `CertExpr` shapes
  round-trip; the shapes with no `CertExpr` print state `True`).
  The converse `elab_valid` links elaboration back to the existing
  soundness: `elabInt c = some e` implies `GueltigAbleitung`.

  The Rust residue (trust base left): `certemit.rs` must print
  `printInt e` for the CHECKED `e` -- that implication is not in Lean.

  CHECK
    ./lean-probe grammatik/Grammatik/ZeugnisIdent.lean
-/
import Grammatik.Zeugnis
import Grammatik.ReferenzB

namespace Gabbro.Grammatik

/-- De Bruijn index of a variable: the position `CertExpr.var` names. -/
def varIdx : Var Γ τ → Nat
  | .hier => 0
  | .dort x => varIdx x + 1

/-- Rebuild a variable from its index: the computational inverse of
    `varIdx` at int type. Bounds are READ from the context, never trusted
    from a print (mirror of `ctxTyp_var`, but returning the witness). -/
def varOf : (Γ : Ctx) → (k : Nat) → Option (Σ lo hi : Int, Var Γ (.int lo hi))
  | τ :: _, 0 =>
    match τ with
    | .int lo hi => some ⟨lo, hi, .hier⟩
    | _ => none
  | _ :: Γ, k + 1 =>
    match varOf Γ k with
    | some ⟨lo, hi, x⟩ => some ⟨lo, hi, .dort x⟩
    | none => none
  | [], _ => none

/-
  CUTS:
  - `printInt`/`elabInt`/`print_elab`/`elab_valid` are being added piece by
    piece (rule 10); only `varIdx`/`varOf` stand so far.
-/
