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
module

public import Grammatik.Korpus.Zeugnis.ZeugnisIdent.Teil1
public import Grammatik.Korpus.Zeugnis.ZeugnisIdent.Teil2
public import Grammatik.Korpus.Zeugnis.ZeugnisIdent.Teil3
public import Grammatik.Korpus.Zeugnis.ZeugnisIdent.Teil4
