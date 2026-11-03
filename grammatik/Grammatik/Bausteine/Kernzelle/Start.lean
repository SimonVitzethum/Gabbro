module

public import Grammatik.Bausteine.Kernzelle.Zulassung
public import Grammatik.Zielsatz.Kern.Spec.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Kernzelle

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz

variable {D : Deklaration} [DecidableEq D.Fn]

/-! ## 7. Neutral initialization at the start memory -/

/-- A cell value at the start memory, checked against the accumulator's
    type and neutral element (refused outside the declared type). -/
def spGlobIntB (sp : Speicher D) (g : D.Glob) (op : AccOperator) (lo hi : Int)
    (w : Nat) : Bool :=
  if h : D.gtyp g = Ty.int lo hi then
    decide ((h ▸ sp.globs g).n = neutralInt op lo hi w)
  else false

/-- **Neutral initialization**: every cell holds the neutral element in the
    declared start memory (checked beside `AkzeptiertSpecX`, like
    `BesitzStart`). -/
def AkkuStart (E : Einheit D) (A : List (AccumulatorDecl D)) : Prop :=
  ∀ a ∈ A, ∀ hok : akkuOk D a, ∀ i : Fin a.kernZahl,
    (akkuZellTyp hok i ▸ E.sp0.globs (a.zellen i)).n =
      neutralInt a.op a.lo a.hi a.breite

/-- Neutral initialization, decided. -/
def akkuStartB (E : Einheit D) (A : List (AccumulatorDecl D)) : Bool :=
  A.all fun a => akkuOkB a &&
    (List.finRange a.kernZahl).all fun i =>
      spGlobIntB E.sp0 (a.zellen i) a.op a.lo a.hi a.breite

/-- The Bool decides neutral initialization. -/
theorem akkuStartB_sound {E : Einheit D} {A : List (AccumulatorDecl D)}
    (h : akkuStartB E A = true) : AkkuStart E A := by
  intro a ha hok i
  have h1 := (List.all_eq_true.mp h) a ha
  simp only [Bool.and_eq_true] at h1
  obtain ⟨_, hcells⟩ := h1
  have h2 := (finRangeAll_iff).mp hcells i
  unfold spGlobIntB at h2
  rw [dite_eq_left (akkuZellTyp hok i)] at h2
  simp only [decide_eq_true_eq] at h2
  exact h2

/-- On the empty list, neutral initialization holds vacuously. -/
theorem akkuStartB_leer (E : Einheit D) : akkuStartB E [] = true := by
  simp only [akkuStartB, List.all_nil]

#print axioms Gabbro.Grammatik.Kernzelle.akkuStartB_sound
#print axioms Gabbro.Grammatik.Kernzelle.akkuStartB_leer

end Gabbro.Grammatik.Kernzelle
