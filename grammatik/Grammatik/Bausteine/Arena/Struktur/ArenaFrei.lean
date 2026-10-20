/-
  File:      Grammatik/ArenaFrei.lean
  Subject:   `free A[i];` AND THE FREE LIST AS A FORM OF MACHINE G, with the invariant of the list
             preserved by `free` and by `alloc` from the list (PLAN-DYNAMIC.md section 8a, phase 1).

  THE SHAPE (sugar, as `ArenaZucker.lean` and `ArenaDyn.lean`: no new `Stmt` constructor, `World`
  does not grow). A dynamic arena with slot release is, in the specification, the dynamic arena
  of `ArenaDyn.lean` plus

    * a global `kopf` of type `int 0 count` -- the head of the free list; the value `count` means
      EMPTY (an index never reaches it);
    * a field `nxt` of the SAME table of type `int 0 count` -- the link of a freed slot.

  The runtime writes the link into the freed payload (`LLVM-BACKEND.md` section 4); the model keeps
  it as its own field, so a freed slot's payload is untouched. The two readings agree on everything
  a program can observe, because the static death of the name (`N586`) means no program reads a
  freed slot's payload.

    `free A[i];`   =  `nxt[i] = kopf;  kopf = i;`
    `alloc` from the list  =  `i = kopf; kopf = nxt[i]; slot[i] = v`   (when `kopf < count`)

  THE INVARIANT. `FreiOk`: the chain from `kopf` along `nxt` ends at `count`, visits each slot at most
  once, and only slots below the arena's used counter. It is a PREDICATE over a world, not a new
  carrier. Two preservation theorems, both on the executed form:

    * `frei_erhaelt`  -- `free` of a slot that is live, below the used counter and not already on the
      list leaves `FreiOk` true. The hypothesis is exactly what the checker's `N586` establishes
      statically (single release, no release of a foreign slot); without it the claim is false
      (`doppelt_bricht`), which is the model's reading of why the refusal exists.
    * `abheben_erhaelt` -- taking the head off the list leaves `FreiOk` true.

  Memory safety does not depend on the invariant (every access is bounds-checked by the index type);
  what it carries is the LOGICAL correctness of reuse: no slot is handed out twice while live.
-/
import Grammatik.Bausteine.Arena.ArenaDyn

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
    (o : List (D.Tab ⊕ D.Glob)) : A.kopfSt (σ.lese Λ o) = A.kopfSt σ := rfl

@[simp] theorem naechst_lese (A : FreiForm D) (σ : World D) (Λ : List (Res D))
    (o : List (D.Tab ⊕ D.Glob)) (k : Int) : A.naechst (σ.lese Λ o) k = A.naechst σ k := rfl

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
  | nil => intro i hi; simp at hi
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
    have hk' : A.naechst σ' k = A.naechst σ k := g k (by simp)
    refine Kette.cons k h0 hk L ?_
    rw [hk']
    exact ih (fun j hj => g j (by simp [hj]))

end FreiForm

/-! ## 3. The two moves on a world -/

namespace FreiForm

/-- The link value `x`, at the link field's declared type. -/
def nxtWert (A : FreiForm D) (x : Int) (h0 : 0 ≤ x) (h1 : x ≤ D.count A.tab) :
    Wert D (D.typ A.tab A.nxt) :=
  Wert.umTyp A.hnxt.symm (⟨x, h0, h1⟩ : Wert D (Ty.int 0 (D.count A.tab)))

/-- The head value `x`, at the head word's declared type. -/
def kopfWert (A : FreiForm D) (x : Int) (h0 : 0 ≤ x) (h1 : x ≤ D.count A.tab) :
    Wert D (D.gtyp A.kopf) :=
  Wert.umTyp A.hkopf.symm (⟨x, h0, h1⟩ : Wert D (Ty.int 0 (D.count A.tab)))

/-- **`free A[i];`**, as the world it leaves: the link of `i` takes the old head, the head becomes `i`. -/
def freiWelt (A : FreiForm D) (σ : World D) (Λ : List (Res D)) (i : Int)
    (h0 : 0 ≤ i) (h1 : i ≤ D.count A.tab) : World D :=
  (σ.schreibSlot A.tab Λ i A.nxt
      (A.nxtWert (A.kopfSt σ) (A.kopfSt_nonneg σ) (A.kopfSt_le σ))).schreibGlob A.kopf Λ
    (A.kopfWert i h0 h1)

/-- **Taking the head off**, as the world it leaves: the head becomes the link of the old head. -/
def abhebWelt (A : FreiForm D) (σ : World D) (Λ : List (Res D)) : World D :=
  σ.schreibGlob A.kopf Λ
    (A.kopfWert (A.naechst σ (A.kopfSt σ)) (A.naechst_nonneg σ _) (A.naechst_le σ _))

theorem kopfWert_n (A : FreiForm D) (x : Int) (h0 : 0 ≤ x) (h1 : x ≤ D.count A.tab) :
    (Wert.umTyp A.hkopf (A.kopfWert x h0 h1)).n = x := by
  exact congrArg (fun w : Wert D (Ty.int 0 (D.count A.tab)) => (show Zahl 0 (D.count A.tab) from w).n)
    (Wert.umTyp_hin_her (D := D) A.hkopf ⟨x, h0, h1⟩)

theorem nxtWert_n (A : FreiForm D) (x : Int) (h0 : 0 ≤ x) (h1 : x ≤ D.count A.tab) :
    (Wert.umTyp A.hnxt (A.nxtWert x h0 h1)).n = x := by
  exact congrArg (fun w : Wert D (Ty.int 0 (D.count A.tab)) => (show Zahl 0 (D.count A.tab) from w).n)
    (Wert.umTyp_hin_her (D := D) A.hnxt ⟨x, h0, h1⟩)

@[simp] theorem naechst_schreibGlob (A : FreiForm D) (σ : World D) (Λ : List (Res D))
    (g : D.Glob) (v : Wert D (D.gtyp g)) (k : Int) :
    A.naechst (σ.schreibGlob g Λ v) k = A.naechst σ k := by
  simp only [naechst, World.schreibGlob, World.merke, World.storeGlob]

@[simp] theorem kopfSt_schreibGlob_kopf (A : FreiForm D) (σ : World D) (Λ : List (Res D))
    (v : Wert D (D.gtyp A.kopf)) :
    A.kopfSt (σ.schreibGlob A.kopf Λ v) = (Wert.umTyp A.hkopf v).n := by
  simp only [kopfSt, World.schreibGlob, World.merke, World.storeGlob, dif_pos]

@[simp] theorem kopfSt_schreibGlob_zaehl (A : FreiForm D) (σ : World D) (Λ : List (Res D))
    (v : Wert D (D.gtyp A.zaehl)) : A.kopfSt (σ.schreibGlob A.zaehl Λ v) = A.kopfSt σ := by
  simp only [kopfSt, World.schreibGlob, World.merke, World.storeGlob,
    dif_neg (fun h : A.kopf = A.zaehl => A.hk1 h)]

@[simp] theorem kopfSt_schreibSlot (A : FreiForm D) (σ : World D) (Λ : List (Res D))
    (t : D.Tab) (k : Int) (f : D.Feld t) (v : Wert D (D.typ t f)) :
    A.kopfSt (σ.schreibSlot t Λ k f v) = A.kopfSt σ := rfl

@[simp] theorem stand_schreibGlob_kopf (A : FreiForm D) (σ : World D) (Λ : List (Res D))
    (v : Wert D (D.gtyp A.kopf)) :
    A.stand (σ.schreibGlob A.kopf Λ v) = A.stand σ := by
  simp only [ArenaForm.stand, World.schreibGlob, World.merke, World.storeGlob,
    dif_neg (fun h : A.zaehl = A.kopf => A.hk1 h.symm)]

/-- The link of the slot that was written is the value written; every other link stays. -/
theorem naechst_schreibSlot (A : FreiForm D) (σ : World D) (Λ : List (Res D)) (i j : Int)
    (v : Wert D (D.typ A.tab A.nxt)) :
    A.naechst (σ.schreibSlot A.tab Λ i A.nxt v) j =
      if j = i then (Wert.umTyp A.hnxt v).n else A.naechst σ j := by
  by_cases h : j = i
  · subst h
    simp only [naechst, World.schreibSlot, World.merke, World.storeSlot, dif_pos, if_pos]
  · simp only [naechst, World.schreibSlot, World.merke, World.storeSlot, dif_pos, if_neg h]

/-! ## 4. The two preservation theorems -/

/-- A slot is ON the list. -/
def AufListe (A : FreiForm D) (σ : World D) (i : Int) : Prop :=
  ∃ L : List Int, Kette A σ (A.kopfSt σ) L ∧ i ∈ L

/-- **`free` keeps the list well formed** -- for a slot that is below the used counter and not on the
    list. That hypothesis is what the checker's `N586` (single release, no foreign slot) establishes. -/
theorem frei_erhaelt (A : FreiForm D) (σ : World D) (Λ : List (Res D)) (i : Int)
    (h0 : 0 ≤ i) (h1 : i < A.stand σ) (hn : ¬ A.AufListe σ i) (hok : A.FreiOk σ) :
    A.FreiOk (A.freiWelt σ Λ i h0 (by have := A.stand_le σ; omega)) := by
  obtain ⟨L, hk, hnd, hlt⟩ := hok
  have hiL : i ∉ L := fun hm => hn ⟨L, hk, hm⟩
  have hcount : i < D.count A.tab := by have := A.stand_le σ; omega
  refine ⟨i :: L, ?_, ?_, ?_⟩
  · have hkopf : A.kopfSt (A.freiWelt σ Λ i h0 (by omega)) = i := by
      simp [freiWelt, kopfWert_n]
    rw [hkopf]
    refine Kette.cons i h0 hcount L ?_
    have hnx : A.naechst (A.freiWelt σ Λ i h0 (by omega)) i = A.kopfSt σ := by
      simp [freiWelt, naechst_schreibSlot, nxtWert_n]
    rw [hnx]
    refine Kette.uebertragen hk ?_
    intro j hj
    have hji : j ≠ i := fun h => hiL (h ▸ hj)
    simp [freiWelt, naechst_schreibSlot, hji]
  · exact List.nodup_cons.mpr ⟨hiL, hnd⟩
  · intro j hj
    simp only [List.mem_cons] at hj
    have hs : A.stand (A.freiWelt σ Λ i h0 (by omega)) = A.stand σ := by
      simp [freiWelt]
    rw [hs]
    rcases hj with rfl | hj
    · exact ⟨h0, h1⟩
    · exact hlt j hj

/-- **Taking the head off keeps the list well formed.** -/
theorem abheben_erhaelt (A : FreiForm D) (σ : World D) (Λ : List (Res D))
    (hne : A.kopfSt σ < D.count A.tab) (hok : A.FreiOk σ) : A.FreiOk (A.abhebWelt σ Λ) := by
  obtain ⟨L, hk, hnd, hlt⟩ := hok
  generalize hg : A.kopfSt σ = kk at hk hne
  cases hk with
  | nil => exact absurd hne (Int.lt_irrefl _)
  | cons k h0 hk' L1 h1 =>
    refine ⟨L1, ?_, ?_, ?_⟩
    · have : A.kopfSt (A.abhebWelt σ Λ) = A.naechst σ kk := by
        simp [abhebWelt, kopfWert_n, hg]
      rw [this]
      exact Kette.uebertragen h1 (fun j _ => by simp [abhebWelt])
    · exact (List.nodup_cons.mp hnd).2
    · intro j hj
      have hs : A.stand (A.abhebWelt σ Λ) = A.stand σ := by simp [abhebWelt]
      rw [hs]
      exact hlt j (List.mem_cons_of_mem _ hj)

/-- **`free` keeps the list well formed**, from the four facts the executed statements give about the
    world they leave (the head is the slot, its link the old head, every other link and the used
    counter as before). The proof of `frei_erhaelt` and of the block theorem is this one. -/
theorem frei_erhaelt_von (A : FreiForm D) (σ σ' : World D) (i : Int)
    (h0 : 0 ≤ i) (h1 : i < A.stand σ) (hn : ¬ A.AufListe σ i) (hok : A.FreiOk σ)
    (hk' : A.kopfSt σ' = i) (hl : A.naechst σ' i = A.kopfSt σ)
    (ho : ∀ j, j ≠ i → A.naechst σ' j = A.naechst σ j) (hs : A.stand σ' = A.stand σ) :
    A.FreiOk σ' := by
  obtain ⟨L, hk, hnd, hlt⟩ := hok
  have hiL : i ∉ L := fun hm => hn ⟨L, hk, hm⟩
  have hcount : i < D.count A.tab := by have := A.stand_le σ; omega
  refine ⟨i :: L, ?_, List.nodup_cons.mpr ⟨hiL, hnd⟩, ?_⟩
  · rw [hk']
    refine Kette.cons i h0 hcount L ?_
    rw [hl]
    refine Kette.uebertragen hk ?_
    intro j hj
    exact ho j (fun h => hiL (h ▸ hj))
  · intro j hj
    rw [hs]
    simp only [List.mem_cons] at hj
    rcases hj with rfl | hj
    · exact ⟨h0, h1⟩
    · exact hlt j hj

/-- A store into the PAYLOAD field leaves every link where it was (`hf`: the link is not the payload). -/
theorem naechst_schreibSlot_feld (A : FreiForm D) (σ : World D) (Λ : List (Res D)) (i j : Int)
    (v : Wert D (D.typ A.tab A.feld)) :
    A.naechst (σ.schreibSlot A.tab Λ i A.feld v) j = A.naechst σ j := by
  have hne : ¬ (A.nxt = A.feld) := A.hf
  simp only [naechst, World.schreibSlot, World.merke, World.storeSlot, dif_pos]
  by_cases h : j = i
  · subst h
    simp only [if_true]
    rw [dif_neg hne]
  · simp only [if_neg h]

/-- A store into the payload field does not move the head. -/
@[simp] theorem kopfSt_schreibSlot_feld (A : FreiForm D) (σ : World D) (Λ : List (Res D)) (i : Int)
    (v : Wert D (D.typ A.tab A.feld)) : A.kopfSt (σ.schreibSlot A.tab Λ i A.feld v) = A.kopfSt σ := rfl

/-- **Taking the head off hands out a slot that is no longer on the list.** From the facts the executed form gives
    (the head becomes the old head's link, links and counter as before): the list stays well formed, and the slot
    handed out is not on it -- it cannot be handed out twice. -/
theorem abheben_sicher (A : FreiForm D) (σ σ' : World D)
    (hne : A.kopfSt σ < D.count A.tab) (hok : A.FreiOk σ)
    (hk' : A.kopfSt σ' = A.naechst σ (A.kopfSt σ))
    (ho : ∀ j, A.naechst σ' j = A.naechst σ j) (hs : A.stand σ' = A.stand σ) :
    A.FreiOk σ' ∧ ¬ A.AufListe σ' (A.kopfSt σ) := by
  obtain ⟨L, hk, hnd, hlt⟩ := hok
  generalize hg : A.kopfSt σ = kk at hk hne hk'
  cases hk with
  | nil => exact absurd hne (Int.lt_irrefl _)
  | cons k h0 hk1 L1 h1 =>
    have hch : A.Kette σ' (A.kopfSt σ') L1 := by
      rw [hk']
      exact Kette.uebertragen h1 (fun j _ => ho j)
    refine ⟨⟨L1, hch, (List.nodup_cons.mp hnd).2, fun j hj => ?_⟩, ?_⟩
    · rw [hs]; exact hlt j (List.mem_cons_of_mem _ hj)
    · rintro ⟨L', hL', hmem⟩
      have : L' = L1 := Kette.eindeutig hL' hch
      subst this
      exact (List.nodup_cons.mp hnd).1 hmem

/-- **A fresh slot from the high-water mark is not on the list** (every listed slot is below the used counter), and
    the list stays well formed when the counter grows by one and no link moves. -/
theorem bump_sicher (A : FreiForm D) (σ σ' : World D) (hok : A.FreiOk σ)
    (hk' : A.kopfSt σ' = A.kopfSt σ) (ho : ∀ j, A.naechst σ' j = A.naechst σ j)
    (hs : A.stand σ' = A.stand σ + 1) :
    A.FreiOk σ' ∧ ¬ A.AufListe σ' (A.stand σ) := by
  obtain ⟨L, hk, hnd, hlt⟩ := hok
  have hch : A.Kette σ' (A.kopfSt σ') L := by
    rw [hk']; exact Kette.uebertragen hk (fun j _ => ho j)
  refine ⟨⟨L, hch, hnd, fun j hj => ?_⟩, ?_⟩
  · rw [hs]; have := hlt j hj; omega
  · rintro ⟨L', hL', hmem⟩
    have : L' = L := Kette.eindeutig hL' hch
    subst this
    have := hlt _ hmem
    omega

/-- Without the hypothesis the claim is FALSE: freeing a slot that is already the head makes the head's
    link point at itself. The model's reading of why `N586` refuses a double release. -/
theorem doppelt_bricht (A : FreiForm D) (σ : World D) (Λ : List (Res D)) (i : Int)
    (h0 : 0 ≤ i) (h1 : i < A.stand σ) (hkopf : A.kopfSt σ = i) :
    A.naechst (A.freiWelt σ Λ i h0 (by have := A.stand_le σ; omega)) i = i := by
  simp [freiWelt, naechst_schreibSlot, nxtWert_n, hkopf]

end FreiForm

/-! ## 5. The two forms in the syntax -/

namespace Block
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}

/-- The new head `i`, at the head word's declared type, under the binder that names the slot. -/
def freiKopfNeu (A : FreiForm D) :
    Expr D (Ty.index (D.count A.tab) :: Γ) Λ (D.gtyp A.kopf) :=
  Expr.umTyp A.hkopf.symm
    (Expr.widen (lo := 0) (hi := D.count A.tab - 1) (lo' := 0) (hi' := D.count A.tab)
      (by omega) (by omega) (Expr.var .here))

/-- The old head, at the link field's declared type. -/
def freiKopfAlt (A : FreiForm D) (hLK : gdarf D A.kopf Λ) :
    Expr D Γ Λ (D.typ A.tab A.nxt) :=
  Expr.umTyp (A.hkopf.trans A.hnxt.symm) (Expr.glob A.kopf hLK)

/-- **`free A[i]; …`** with the slot `i` bound by the binder in front: the link of `i` takes the old
    head, the head becomes `i`. Two existing statements; no new constructor. -/
def freiRumpf (A : FreiForm D)
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwK : V.gschreibt A.kopf = true) (hLK : gdarf D A.kopf Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') :
    Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ' :=
  .cons (.assignSlot A.tab A.nxt (Expr.var .here) (freiKopfAlt A hLK) hwT hLT)
    (.cons (.assignGlob A.kopf (freiKopfNeu A) hwK hLK) rest)

/-- The head's link as the new head, at the head word's declared type: `kopf = nxt[i]`. -/
def freiKopfWeiter (A : FreiForm D) (hLT : darf D A.tab Λ) :
    Expr D (Ty.index (D.count A.tab) :: Γ) Λ (D.gtyp A.kopf) :=
  Expr.umTyp (A.hnxt.trans A.hkopf.symm) (Expr.slot A.tab A.nxt (Expr.var .here) hLT)

/-- **`let i = alloc A (v) else B;` from the free list** (the list is non-empty): `i = kopf; kopf = nxt[i];
    slot[i].feld = v`. `narrow` of the head into the index range: it fits when the list is non-empty. -/
def freiNimm (A : FreiForm D)
    (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwK : V.gschreibt A.kopf = true) (hLK : gdarf D A.kopf Λ)
    (voll : Endblock D V l Γ Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') :
    Block D V l Γ Λ Λ' :=
  .narrow (Expr.umTyp A.hkopf (Expr.glob A.kopf hLK)) 0 (D.count A.tab - 1) voll
    (.cons (.assignGlob A.kopf (freiKopfWeiter A hLT) hwK hLK)
      (.cons (.assignSlot A.tab A.feld (Expr.var .here) (Expr.weaken v) hwT hLT) rest))

end Block

/-! ## 6. What the form DOES -/

/-- Two casts there and back leave an integer where it was (stated for the integer case, where
    `Wert` is a `Zahl`; `simp` cannot see through the unfolding, `exact` can). -/
theorem umTyp_rund_n {τ : Ty} {a b : Int} (h : τ = Ty.int a b) (z : Zahl a b) :
    (Wert.umTyp (D := D) h (Wert.umTyp (D := D) h.symm z)).n = z.n := by
  subst h; rfl

/-- Two casts in a row are the one cast along the composite equation. -/
theorem umTyp_trans_n {τ σ : Ty} {a b : Int} (h1 : τ = σ) (h2 : σ = Ty.int a b) (v : Wert D τ) :
    (Wert.umTyp (D := D) h2 (Wert.umTyp (D := D) h1 v)).n = (Wert.umTyp (D := D) (h1.trans h2) v).n := by
  subst h1; subst h2; rfl

section Bedeutung
variable (O : Orakel D) (passes : Nat)
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

/-- **What `free A[i]` leaves, read off the executed statements.** After the two stores: the head is
    the slot, its link is the old head, every other link and the used counter are as before. -/
theorem freiRumpf_fakten (A : FreiForm D)
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwK : V.gschreibt A.kopf = true) (hLK : gdarf D A.kopf Λ)
    (σ : World D) (k : Wert D (Ty.index (D.count A.tab))) (ρ : Env D Γ) :
    ∃ σ' : World D,
      execBlock (V := V) O passes R
          (Block.freiRumpf (l := l) (Λ' := Λ) A hwT hLT hwK hLK (.nil)) σ (.cons k ρ)
        = .ok σ' (.cons k ρ) ∧
      A.kopfSt σ' = k.n ∧ A.naechst σ' k.n = A.kopfSt σ ∧
      (∀ j, j ≠ k.n → A.naechst σ' j = A.naechst σ j) ∧ A.stand σ' = A.stand σ := by
  refine ⟨_, rfl, ?_⟩
  simp only [eval, Env.get, Block.freiKopfNeu, Block.freiKopfAlt, eval_umTyp, Expr.orte, orte_umTyp,
    List.nil_append, FreiForm.kopfSt_schreibGlob_kopf, FreiForm.kopfSt_schreibSlot,
    FreiForm.naechst_schreibGlob, FreiForm.naechst_schreibSlot, FreiForm.naechst_lese,
    FreiForm.kopfSt_lese, ArenaForm.stand_lese, FreiForm.stand_schreibGlob_kopf,
    ArenaForm.stand_schreibSlot]
  refine ⟨umTyp_rund_n A.hkopf _, ?_, ?_, trivial⟩
  · simp only [if_true]
    exact umTyp_trans_n _ _ _
  · intro j hj
    simp only [if_neg hj]

/-- **`free A[i]` keeps the free list well formed**, on the executed form. The hypotheses are the
    static facts `N586` gives: the slot is a live one (below the used counter) and not already freed. -/
theorem freiRumpf_erhaelt (A : FreiForm D)
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwK : V.gschreibt A.kopf = true) (hLK : gdarf D A.kopf Λ)
    (σ : World D) (k : Wert D (Ty.index (D.count A.tab))) (ρ : Env D Γ)
    (h1 : k.n < A.stand σ) (hn : ¬ A.AufListe σ k.n) (hok : A.FreiOk σ) :
    ∃ σ' : World D,
      execBlock (V := V) O passes R
          (Block.freiRumpf (l := l) (Λ' := Λ) A hwT hLT hwK hLK (.nil)) σ (.cons k ρ)
        = .ok σ' (.cons k ρ) ∧ A.FreiOk σ' := by
  obtain ⟨σ', he, h1', h2', h3', h4'⟩ := freiRumpf_fakten O passes R (l := l) A hwT hLT hwK hLK σ k ρ
  exact ⟨σ', he, A.frei_erhaelt_von σ σ' k.n k.lo_le h1 hn hok h1' h2' h3' h4'⟩

/-- **Taking a slot off the free list**, read off the executed form: it hands out the old head, the head becomes the
    head's link, no other link moves and the used counter stays. -/
theorem freiNimm_fakten (A : FreiForm D) (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwK : V.gschreibt A.kopf = true) (hLK : gdarf D A.kopf Λ)
    (voll : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hne : A.kopfSt σ < D.count A.tab) :
    ∃ σ' : World D,
      execBlock (V := V) O passes R
          (Block.freiNimm (Λ' := Λ) A v hwT hLT hwK hLK voll .nil) σ ρ = .ok σ' ρ ∧
      A.kopfSt σ' = A.naechst σ (A.kopfSt σ) ∧
      (∀ j, A.naechst σ' j = A.naechst σ j) ∧ A.stand σ' = A.stand σ := by
  have hk : (0 : Int) ≤ A.kopfSt σ ∧ A.kopfSt σ ≤ D.count A.tab - 1 :=
    ⟨A.kopfSt_nonneg σ, by omega⟩
  simp only [Block.freiNimm, execBlock, eval_umTyp, orte_umTyp, eval, Expr.orte, World.globs_lese]
  rw [dif_pos (by exact hk)]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  all_goals simp only [eval, Block.freiKopfWeiter, eval_umTyp, Expr.orte, orte_umTyp, List.nil_append,
    List.cons_append, List.append_nil, FreiForm.kopfSt_schreibGlob_kopf, FreiForm.kopfSt_schreibSlot_feld,
    FreiForm.naechst_schreibGlob, FreiForm.naechst_schreibSlot_feld, FreiForm.naechst_lese, FreiForm.kopfSt_lese,
    ArenaForm.stand_lese, FreiForm.stand_schreibGlob_kopf, ArenaForm.stand_schreibSlot]
  all_goals first | trivial | (intro j; trivial) | exact umTyp_trans_n _ _ _

/-- **`alloc` from the free list keeps the list well formed and never hands out a listed slot** -- on the executed form. -/
theorem freiNimm_erhaelt (A : FreiForm D) (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwK : V.gschreibt A.kopf = true) (hLK : gdarf D A.kopf Λ)
    (voll : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hne : A.kopfSt σ < D.count A.tab) (hok : A.FreiOk σ) :
    ∃ σ' : World D,
      execBlock (V := V) O passes R
          (Block.freiNimm (Λ' := Λ) A v hwT hLT hwK hLK voll .nil) σ ρ = .ok σ' ρ ∧
      A.FreiOk σ' ∧ ¬ A.AufListe σ' (A.kopfSt σ) := by
  obtain ⟨σ', he, h1, h2, h3⟩ := freiNimm_fakten O passes R (l := l) A v hwT hLT hwK hLK voll σ ρ hne
  exact ⟨σ', he, (A.abheben_sicher σ σ' hne hok h1 h2 h3).1, (A.abheben_sicher σ σ' hne hok h1 h2 h3).2⟩

/-- **A fresh slot from the used counter** (the list is empty or ignored): `dynAlloc`'s rest stores the payload and
    bumps the counter. The facts about the world it leaves: the head and every link stay, the counter grows by one. -/
theorem frischRumpf_fakten (A : FreiForm D) (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt A.zaehl = true) (hLG : gdarf D A.zaehl Λ)
    (σ : World D) (k : Wert D (Ty.index (D.count A.tab))) (ρ : Env D Γ) :
    ∃ σ' : World D,
      execBlock (V := V) O passes R
          (Block.arenaRumpf (l := l) (Λ' := Λ) A.toArenaForm v hwT hLT hwG hLG .nil) σ (.cons k ρ)
        = .ok σ' (.cons k ρ) ∧
      A.kopfSt σ' = A.kopfSt σ ∧ (∀ j, A.naechst σ' j = A.naechst σ j) ∧ A.stand σ' = k.n + 1 := by
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  all_goals simp only [eval, Block.arenaRumpf, Block.arenaBump, eval_umTyp, orte_umTyp, Expr.orte,
    List.nil_append, FreiForm.kopfSt_schreibGlob_zaehl, FreiForm.kopfSt_schreibSlot_feld,
    FreiForm.naechst_schreibGlob, FreiForm.naechst_schreibSlot_feld, FreiForm.naechst_lese,
    FreiForm.kopfSt_lese, ArenaForm.stand_lese, ArenaForm.stand_schreibGlob, Wert.umTyp_hin_her]
  all_goals first | trivial | (intro j; trivial) | exact umTyp_trans_n _ _ _ | rfl

end Bedeutung

end Gabbro.Grammatik
