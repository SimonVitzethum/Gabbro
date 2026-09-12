/-
  Audit probe F6: `atomarAusgenommen_entlaedt` / `paarungAusgenommen_entlaedt`
  take dummy propositions `S P` / `S A` that never occur meaningfully.

  Claim (pattern b/d): the theorems conclude
    `Geteilt c = true ∧ (S ∨ AtomarAusgenommen c ∨ P)`
  from `(hT : Geteilt c = true)` and `(hA : AtomarAusgenommen c)`. The
  arbitrary `S P : Prop` are instantiable with `False`: the "discharge"
  proves nothing about the lock side `S` or the pairing side `P` -- it just
  picks the middle disjunct. The docstring "gleichgueltig was links/rechts
  stuende" admits this: the conclusion is `hA` repackaged, not a discharge
  of an obligation.
-/
import Grammatik.InterferenzAllgemein

namespace Gabbro.Grammatik

open Gabbro.Grammatik

variable {D : Deklaration}

/-- Instantiation at `False`: the dummy sides contribute nothing. -/
example (c : D.Tab ⊕ D.Glob)
    (hT : Geteilt c = true) (hA : AtomarAusgenommen (D := D) c) :
    Geteilt c = true ∧
      (False ∨ AtomarAusgenommen (D := D) c ∨ False) :=
  atomarAusgenommen_entlaedt c hT hA False False

/-- Same for the pairing side. -/
example (c : D.Tab ⊕ D.Glob)
    (hT : Geteilt c = true) (hP : PaarungAusgenommen (D := D) c) :
    Geteilt c = true ∧
      (False ∨ False ∨ PaarungAusgenommen (D := D) c) :=
  paarungAusgenommen_entlaedt c hT hP False False

/-- The content is exactly `⟨hT, Or.inr (Or.inl hA)⟩`: rebuilding it shows
    `S`/`P` never constrain anything. -/
example (c : D.Tab ⊕ D.Glob)
    (hT : Geteilt c = true) (hA : AtomarAusgenommen (D := D) c)
    (S P : Prop) :
    Geteilt c = true ∧ (S ∨ AtomarAusgenommen (D := D) c ∨ P) :=
  ⟨hT, Or.inr (Or.inl hA)⟩

/-
CUTS:
- Not claimed: the exception predicates themselves are meaningless; only that
  these two "discharge" theorems discharge nothing (their extra premises are
  place-holders any proposition, including `False`, can fill).
-/
#print axioms Gabbro.Grammatik.atomarAusgenommen_entlaedt
#print axioms Gabbro.Grammatik.paarungAusgenommen_entlaedt
