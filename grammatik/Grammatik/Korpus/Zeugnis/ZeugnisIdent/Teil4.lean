module

public import Grammatik.Korpus.Zeugnis.Zeugnis
public import Grammatik.Korpus.Referenz.ReferenzB
public import Grammatik.Korpus.Zeugnis.ZeugnisIdent.Teil3

@[expose] public section

namespace Gabbro.Grammatik

/-- Witness for `print_elab` (rule 13): the int-typed target instantiated
    at `refHundert` (the cap value `100` widened to `0 .. 100` in the
    `einzahlen` context), with the fixture's write as non-degeneracy. -/
theorem print_elab_zeuge :
    ∃ (e : Expr refD [.int 0 10] [Res.held (D := refD) ()] (.int 0 100)),
      (match printInt e with
       | some c =>
         elabInt (D := refD) (Γ := [.int 0 10]) (Λ := [Res.held (D := refD) ()])
           c = some ⟨.int 0 100, e⟩
       | none => True) ∧
      (vertragVon refD refEin).schreibt () = true := by
  refine ⟨refHundert, ?_, refEin_schreibt ()⟩
  exact print_elab refHundert

/-- Witness for `elab_valid` (rule 13): the elaboration premise proved by
    computation (`rfl`: `elabInt` reduces on the concrete print, proofs
    agreeing by irrelevance) and the validity by `decide` (the table
    recomputes `(0, 100)`), on the same non-degenerate fixture. -/
theorem elab_valid_zeuge :
    ∃ (e : Expr refD [.int 0 10] [Res.held (D := refD) ()] (.int 0 100)),
      elabInt (D := refD) (Γ := [.int 0 10]) (Λ := [Res.held (D := refD) ()])
        (.wide 0 100 (.lit 100)) = some ⟨.int 0 100, e⟩ ∧
      GueltigAbleitung refD [.int 0 10] [Res.held (D := refD) ()]
        (.wide 0 100 (.lit 100)) 0 100 ∧
      (vertragVon refD refEin).schreibt () = true :=
  ⟨refHundert, rfl, by decide, refEin_schreibt ()⟩

/-
  CUTS: what is not proved here.
  - `printInt` answers `none` for `durch`, `altGlob`/`altSlot`,
    `leseBytes`, and every non-`int` constructor: those shapes have no
    `CertExpr` print in `Zeugnis.lean`, so there is no Lean-side roundtrip
    for them (the `none`-branch of `print_elab_all`/`print_elab` states
    `True`). Covering them needs certificate shapes that do not exist yet
    (same remainder as `Zeugnis.lean` CUT-4/`altGlob`/`altSlot`, the CUT-3
    bool/float/option/sum/ground/quantifier/`reaches` rows, and the
    `leseBytes` shape, which has no certificate row at all).
  - The Rust residue (trust base left, not in Lean): `certemit.rs` must
    print `printInt e` for the CHECKED `e` -- i.e. its `emit` must take
    the typed term the checker derived (not the raw AST) and its
    `cert_range` must agree with `certRange` on every arm (today it covers
    only `lit`/`add`/`div`/bitwise/`wide`/reads: `sub`/`neg`/`mul`/`rem`/
    `sdiv`/`srem` prints are missing there, and its `Shl`/`Shr` carry no
    width while `CertExpr.shl/shr` do). The Lean half proved here applies
    exactly where the Rust print equals `printInt e`.
-/

#print axioms Gabbro.Grammatik.print_elab_all
#print axioms Gabbro.Grammatik.print_elab
#print axioms Gabbro.Grammatik.elab_valid
#print axioms Gabbro.Grammatik.print_elab_all_zeuge
#print axioms Gabbro.Grammatik.print_elab_zeuge
#print axioms Gabbro.Grammatik.elab_valid_zeuge

end Gabbro.Grammatik
