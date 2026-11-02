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

section ResetKomponente

/-- **The reset component** (C18): every static-array carrier of the list admits zero.
    Non-array globals and tables pass; an array over a zero-less element type refuses. -/
def resetCarrierB : D.Tab ⊕ D.Glob → Bool
  | .inl _ => true
  | .inr g =>
    match D.gtyp g with
    | .arr elem _ => zeroAdmittingB elem
    | _ => true

/-- The reset component over a carrier list. -/
def resetB (cs : List (D.Tab ⊕ D.Glob)) : Bool :=
  cs.all resetCarrierB

/-- One carrier decides its reset admission. -/
theorem resetCarrierB_iff {g : D.Glob} :
    resetCarrierB (.inr g) = true ↔
      ∀ (elem : Ty) (len : Nat), D.gtyp g = .arr elem len → ZeroAdmitting elem := by
  cases h : D.gtyp g with
  | int lo hi =>
    simp only [resetCarrierB, h]
    constructor
    · intro _ elem len harr
      rw [h] at harr
      exact Ty.noConfusion harr
    · intro _
      trivial
  | bool =>
    simp only [resetCarrierB, h]
    constructor
    · intro _ elem len harr
      rw [h] at harr
      exact Ty.noConfusion harr
    · intro _
      trivial
  | opt n =>
    simp only [resetCarrierB, h]
    constructor
    · intro _ elem len harr
      rw [h] at harr
      exact Ty.noConfusion harr
    · intro _
      trivial
  | sum cs =>
    simp only [resetCarrierB, h]
    constructor
    · intro _ elem len harr
      rw [h] at harr
      exact Ty.noConfusion harr
    · intro _
      trivial
  | why n =>
    simp only [resetCarrierB, h]
    constructor
    · intro _ elem len harr
      rw [h] at harr
      exact Ty.noConfusion harr
    · intro _
      trivial
  | never =>
    simp only [resetCarrierB, h]
    constructor
    · intro _ elem len harr
      rw [h] at harr
      exact Ty.noConfusion harr
    · intro _
      trivial
  | fl _ =>
    simp only [resetCarrierB, h]
    constructor
    · intro _ elem len harr
      rw [h] at harr
      exact Ty.noConfusion harr
    · intro _
      trivial
  | fnptr s =>
    simp only [resetCarrierB, h]
    constructor
    · intro _ elem len harr
      rw [h] at harr
      exact Ty.noConfusion harr
    · intro _
      trivial
  | ptr t rw =>
    simp only [resetCarrierB, h]
    constructor
    · intro _ elem len harr
      rw [h] at harr
      exact Ty.noConfusion harr
    · intro _
      trivial
  | ref t =>
    simp only [resetCarrierB, h]
    constructor
    · intro _ elem len harr
      rw [h] at harr
      exact Ty.noConfusion harr
    · intro _
      trivial
  | arr elem n =>
    simp only [resetCarrierB, h, zeroAdmittingB_iff]
    constructor
    · intro hn e l harr
      rw [h] at harr
      cases harr
      exact hn
    · intro hh
      exact hh elem n h
  | str n =>
    simp only [resetCarrierB, h]
    constructor
    · intro _ elem len harr
      rw [h] at harr
      exact Ty.noConfusion harr
    · intro _
      trivial

/-- **The reset component decides its field** (`AkzeptiertSpec.reset`, C18). -/
theorem resetB_iff {cs : List (D.Tab ⊕ D.Glob)} (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs) :
    resetB cs = true ↔
      ∀ (g : D.Glob) (elem : Ty) (len : Nat),
        D.gtyp g = .arr elem len → ZeroAdmitting elem := by
  unfold resetB
  rw [List.all_eq_true]
  constructor
  · intro h g elem len harr
    exact (resetCarrierB_iff.mp (h _ (hcs _)) elem len harr)
  · intro h c hmem
    cases c with
    | inl t => rfl
    | inr g =>
      rw [resetCarrierB_iff]
      intro elem len harr
      exact h g elem len harr

end ResetKomponente
end Gabbro.Grammatik
