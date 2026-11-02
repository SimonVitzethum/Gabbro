module

public import Grammatik.Bausteine.Arena.ArenaDyn

@[expose] public section



namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn

variable {D : Deklaration}

/-! ## 1. What a declaration must carry -/

/-- **A dynamic arena with slot release.** The dynamic arena, the head word and the link field. -/
structure FreiForm (D : Deklaration) extends DynForm D where
  /-- The head of the free list; `count` is the empty marker. -/
  kopf : D.Glob
  hkopf : D.gtyp kopf = Ty.int 0 (D.count tab)
  /-- The link field of a freed slot. -/
  nxt : D.Feld tab
  hnxt : D.typ tab nxt = Ty.int 0 (D.count tab)
  /-- Three words, never fewer: every frame lemma below rests on it. -/
  hk1 : kopf ≠ zaehl
  hk2 : kopf ≠ komm
  /-- The link is not the payload. -/
  hf : nxt ≠ feld

namespace FreiForm

/-- The head of the list, read out of a world. -/
def kopfSt (A : FreiForm D) (σ : World D) : Int := (Wert.umTyp A.hkopf (σ.globs A.kopf)).n

/-- The link of slot `k`, read out of a world. -/
def naechst (A : FreiForm D) (σ : World D) (k : Int) : Int :=
  (Wert.umTyp A.hnxt (σ.slots A.tab k A.nxt)).n

theorem kopfSt_le (A : FreiForm D) (σ : World D) : A.kopfSt σ ≤ D.count A.tab :=
  (Wert.umTyp A.hkopf (σ.globs A.kopf)).le_hi

theorem kopfSt_nonneg (A : FreiForm D) (σ : World D) : 0 ≤ A.kopfSt σ :=
  (Wert.umTyp A.hkopf (σ.globs A.kopf)).lo_le

theorem naechst_le (A : FreiForm D) (σ : World D) (k : Int) : A.naechst σ k ≤ D.count A.tab :=
  (Wert.umTyp A.hnxt (σ.slots A.tab k A.nxt)).le_hi

theorem naechst_nonneg (A : FreiForm D) (σ : World D) (k : Int) : 0 ≤ A.naechst σ k :=
  (Wert.umTyp A.hnxt (σ.slots A.tab k A.nxt)).lo_le

@[simp] theorem kopfSt_lese (A : FreiForm D) (σ : World D) (Λ : List (Res D))
    (o : List (D.Tab ⊕ D.Glob)) : A.kopfSt (σ.lese Λ o) = A.kopfSt σ := by rfl

@[simp] theorem naechst_lese (A : FreiForm D) (σ : World D) (Λ : List (Res D))
    (o : List (D.Tab ⊕ D.Glob)) (k : Int) : A.naechst (σ.lese Λ o) k = A.naechst σ k := by rfl

/-! ## 2. The chain -/

/-- `Kette σ k L`: following the links from `k` visits exactly `L` and ends at the empty marker. -/
inductive Kette (A : FreiForm D) (σ : World D) : Int → List Int → Prop where
  | nil : Kette A σ (D.count A.tab) []
  | cons (k : Int) (h0 : 0 ≤ k) (hk : k < D.count A.tab) (L : List Int)
      (h : Kette A σ (A.naechst σ k) L) : Kette A σ k (k :: L)

/-- **The invariant of the free list.** -/
def FreiOk (A : FreiForm D) (σ : World D) : Prop :=
  ∃ L : List Int, Kette A σ (A.kopfSt σ) L ∧ L.Nodup ∧ ∀ i ∈ L, 0 ≤ i ∧ i < A.stand σ

/-- The chain from a head is unique. -/
theorem Kette.eindeutig {A : FreiForm D} {σ : World D} {k : Int} {L L' : List Int}
    (h : Kette A σ k L) (h' : Kette A σ k L') : L = L' := by
  induction h generalizing L' with
  | nil =>
    cases h' with
    | nil => rfl
    | cons k0 h0 hk _ _ => exact absurd hk (Int.lt_irrefl _)
  | cons k h0 hk L h ih =>
    cases h' with
    | nil => exact absurd hk (Int.lt_irrefl _)
    | cons _ _ _ L' h' => exact congrArg (k :: ·) (ih h')

/-- Every visited slot is a slot of the table. -/
theorem Kette.mem_bereich {A : FreiForm D} {σ : World D} {k : Int} {L : List Int}
    (h : Kette A σ k L) : ∀ i ∈ L, 0 ≤ i ∧ i < D.count A.tab := by
  induction h with
  | nil => intro i hi; simp only [List.not_mem_nil] at hi
  | cons k h0 hk L h ih =>
    intro i hi
    simp only [List.mem_cons] at hi
    rcases hi with rfl | hi
    · exact ⟨h0, hk⟩
    · exact ih i hi

/-- A world that has the same links at every visited slot has the same chain. -/
theorem Kette.uebertragen {A : FreiForm D} {σ σ' : World D} {k : Int} {L : List Int}
    (h : Kette A σ k L) (g : ∀ j ∈ L, A.naechst σ' j = A.naechst σ j) : Kette A σ' k L := by
  induction h with
  | nil => exact Kette.nil
  | cons k h0 hk L h ih =>
    have hk' : A.naechst σ' k = A.naechst σ k := g k (by simp only [List.mem_cons, true_or])
    refine Kette.cons k h0 hk L ?_
    rw [hk']
    exact ih (fun j hj => g j (by simp only [List.mem_cons, hj, or_true]))

end FreiForm


end Gabbro.Grammatik
