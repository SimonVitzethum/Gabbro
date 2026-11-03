module

public import Grammatik.Kern.Syntax.Extensions.Geist.T1.Teil3

@[expose] public section

namespace Gabbro.Grammatik.Geist
open Gabbro.Grammatik
variable {D : Deklaration} {V : Vertrag D}


set_option linter.unusedSectionVars false in
theorem g001End_korrekt_retWhyScoped {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (zz1)
    (R)
    (zr_h : g001End (.retWhyScoped zz1 R : Endblock D V l Γ Λ) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.endblockOrte (.retWhyScoped zz1 R : Endblock D V l Γ Λ))
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have ho' : o ∈ ([] : List (D.Tab ⊕ D.Glob)) := by simpa [Extraktion.endblockOrte] using ho
  exact (List.not_mem_nil ho').elim

set_option linter.unusedSectionVars false in
theorem g001End_korrekt_leave {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (zz1)
    (zr_h : g001End (.leave zz1 : Endblock D V l Γ Λ) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.endblockOrte (.leave zz1 : Endblock D V l Γ Λ))
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have ho' : o ∈ ([] : List (D.Tab ⊕ D.Glob)) := by simpa [Extraktion.endblockOrte] using ho
  exact (List.not_mem_nil ho').elim

end Gabbro.Grammatik.Geist
