module

public import Grammatik.Kern.Syntax.Syntax.Teil1

@[expose] public section

namespace Gabbro.Grammatik

/-! ## C11 scoped return: exact return is the empty cleanup

    `RueckRessourcen` (Syntax/Teil1) carries the exact residual `V.ende`
    plus the scopes to close. The two directions below say the old bare
    `Λ.Perm V.ende` evidence is exactly the empty-scopes case; one return
    API is kept by using the same shape with `scopes = []`. The check that a
    nonempty `scopes` is exactly the crossed lexical scopes in reverse
    order, the scope-indexed `cleanupB` traversal, the saved result span,
    per-scope invariant restoration and the machine unwinding
    (`GRest.rueckBereit` rules, sequential/replay equality,
    `anRueck_perm`/`istRueck_perm` generalization) are OPEN. -/

variable {D : Deklaration} {V : Vertrag D} {Λ : List (Res D)}

/-- Old exact evidence embeds as the empty cleanup. -/
def RueckRessourcen.vonGenau (h : Λ.Perm V.ende) : RueckRessourcen D V Λ :=
  ⟨[], by simpa using h⟩

/-- An empty cleanup is the old exact evidence. -/
theorem RueckRessourcen.genauVon (R : RueckRessourcen D V Λ) (hempty : R.scopes = []) :
    Λ.Perm V.ende := by
  simpa [hempty] using R.genau

#print axioms RueckRessourcen.vonGenau
#print axioms RueckRessourcen.genauVon

end Gabbro.Grammatik
