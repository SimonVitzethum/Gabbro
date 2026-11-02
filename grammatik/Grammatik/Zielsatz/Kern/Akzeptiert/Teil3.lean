module

public import Grammatik.Zielsatz.Kern.Spec
public import Grammatik.Bausteine.Arena.ArenaStaticReset
public import Grammatik.Bausteine.Arena.ArenaPageReturn

@[expose] public section

namespace Gabbro.Grammatik

open Zielsatz

variable {D : Deklaration}

section ResetAdmission

/-- **Reset admission for one static global (C18).** The global is a
    static array of known length over a zero-admitting element type
    (`ZeroAdmitting`: no `fnptr`/`ref`/`ptr` zero, no floats). The range
    itself (`0 ≤ i`, `n ≤ len`, `i ≤ len - n`), the write guard and mode,
    the complete alias and resource scope and the service identity are
    duties at the use site, not fields here: they depend on the caller's
    resources, while this predicate depends only on the declaration. -/
def ResetAdmission (g : D.Glob) : Prop :=
  ∃ len elem, D.gtyp g = .arr elem len ∧ ZeroAdmitting elem

/-- The same admission, decided. -/
def resetAdmissionB (g : D.Glob) : Bool :=
  match D.gtyp g with
  | .arr elem _ => zeroAdmittingB elem
  | _ => false

/-- The Bool decides the admission. -/
theorem resetAdmissionB_iff {g : D.Glob} :
    resetAdmissionB g = true ↔ ResetAdmission g := by
  cases h : D.gtyp g with
  | int lo hi =>
    simp only [resetAdmissionB, h]
    constructor
    · intro hc; exact absurd hc Bool.false_ne_true
    · rintro ⟨_, _, harr, _⟩; exact Ty.noConfusion harr
  | bool =>
    simp only [resetAdmissionB, h]
    constructor
    · intro hc; exact absurd hc Bool.false_ne_true
    · rintro ⟨_, _, harr, _⟩; exact Ty.noConfusion harr
  | opt n =>
    simp only [resetAdmissionB, h]
    constructor
    · intro hc; exact absurd hc Bool.false_ne_true
    · rintro ⟨_, _, harr, _⟩; exact Ty.noConfusion harr
  | sum cs =>
    simp only [resetAdmissionB, h]
    constructor
    · intro hc; exact absurd hc Bool.false_ne_true
    · rintro ⟨_, _, harr, _⟩; exact Ty.noConfusion harr
  | why n =>
    simp only [resetAdmissionB, h]
    constructor
    · intro hc; exact absurd hc Bool.false_ne_true
    · rintro ⟨_, _, harr, _⟩; exact Ty.noConfusion harr
  | never =>
    simp only [resetAdmissionB, h]
    constructor
    · intro hc; exact absurd hc Bool.false_ne_true
    · rintro ⟨_, _, harr, _⟩; exact Ty.noConfusion harr
  | fl _ =>
    simp only [resetAdmissionB, h]
    constructor
    · intro hc; exact absurd hc Bool.false_ne_true
    · rintro ⟨_, _, harr, _⟩; exact Ty.noConfusion harr
  | fnptr s =>
    simp only [resetAdmissionB, h]
    constructor
    · intro hc; exact absurd hc Bool.false_ne_true
    · rintro ⟨_, _, harr, _⟩; exact Ty.noConfusion harr
  | ptr t rw =>
    simp only [resetAdmissionB, h]
    constructor
    · intro hc; exact absurd hc Bool.false_ne_true
    · rintro ⟨_, _, harr, _⟩; exact Ty.noConfusion harr
  | ref t =>
    simp only [resetAdmissionB, h]
    constructor
    · intro hc; exact absurd hc Bool.false_ne_true
    · rintro ⟨_, _, harr, _⟩; exact Ty.noConfusion harr
  | arr elem n =>
    simp only [resetAdmissionB, h, zeroAdmittingB_iff]
    constructor
    · intro hn; exact ⟨n, elem, rfl, hn⟩
    · rintro ⟨_, _, harr, hn⟩
      cases harr
      exact hn
  | str n =>
    simp only [resetAdmissionB, h]
    constructor
    · intro hc; exact absurd hc Bool.false_ne_true
    · rintro ⟨_, _, harr, _⟩; exact Ty.noConfusion harr

/-- The joint reset and page-return admission for one static global: the
    checked array derivation, the return binding, and a resident backing
    at admission. The pending authority, the exclusive scope and the
    zero-on-next-read contract travel with the admitted use, not with
    this declaration-level predicate. Deliberately NOT yet conjoined into
    `AkzeptiertSpec`/`Akzeptiert`: that wiring re-proves `akzeptiert_iff`
    and the goal legs, which the integration build owns. -/
structure PageAdmission (g : D.Glob) where
  range : ResetAdmission g
  contract : PageReturnContract D g
  state : BackingState
  startResident : state = .resident

/-- The admission is inhabited wherever a declaration types a global as
    a zero-initialized static array: the fixture the generic lowering
    proof will instantiate. A closed fixture needs a concrete
    array-static declaration, which the lowering proof owns. -/
theorem resetAdmission_zeuge {g : D.Glob}
    (harr : D.gtyp g = .arr (.int 0 255) 4) :
    ResetAdmission g :=
  ⟨4, .int 0 255, harr, .intZero (by omega) (by omega)⟩

#print axioms resetAdmissionB_iff

end ResetAdmission
end Gabbro.Grammatik
