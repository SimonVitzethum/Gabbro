/-
  File:      Grammatik/ArenaLebt.lean
  Subject:   LIVE SLOTS of an arena with slot release, and what `alloc` and `free` leave of the places
             that are not theirs (PLAN-DYNAMIC.md section 8a, phase 2, world half).

  A slot is LIVE when it is below the used counter and not on the free list. `alloc` (from the list or
  from the counter) turns one slot live, `free` turns one dead; every other slot keeps its state.
  `Fremd A σ σ'` says that a run wrote only the places the allocator owns (the counter, the head of the
  free list, the payload and the free-list link); the three executed forms of `ArenaFrei.lean`
  (`freiRumpf`, `freiNimm`, `arenaRumpf` over a `FreiForm`) satisfy it. The link structures of
  `ArenaListe.lean` and `ArenaBaumWelt.lean` live in OTHER fields, so they survive every allocator move
  untouched.
-/
import Grammatik.Bausteine.Arena.Struktur.ArenaFrei

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn

variable {D : Deklaration}

/-! ## 1. Raw frames of the two stores -/

@[simp] theorem World.globs_schreibGlob_ne (σ : World D) (g g' : D.Glob) (Λ : List (Res D))
    (v : Wert D (D.gtyp g')) (h : g ≠ g') : (σ.schreibGlob g' Λ v).globs g = σ.globs g := by
  simp only [World.schreibGlob, World.merke, World.storeGlob, dif_neg h]

@[simp] theorem World.globs_schreibSlot (σ : World D) (t : D.Tab) (Λ : List (Res D)) (k : Int)
    (f : D.Feld t) (v : Wert D (D.typ t f)) : (σ.schreibSlot t Λ k f v).globs = σ.globs := rfl

@[simp] theorem World.slots_schreibGlob (σ : World D) (g : D.Glob) (Λ : List (Res D))
    (v : Wert D (D.gtyp g)) : (σ.schreibGlob g Λ v).slots = σ.slots := rfl

@[simp] theorem World.slots_lese (σ : World D) (Λ : List (Res D)) (o : List (D.Tab ⊕ D.Glob)) :
    (σ.lese Λ o).slots = σ.slots := rfl

theorem World.slots_schreibSlot_ne (σ : World D) (t : D.Tab) (Λ : List (Res D)) (k : Int)
    (f : D.Feld t) (v : Wert D (D.typ t f)) (k' : Int) (f' : D.Feld t) (h : f' ≠ f) :
    (σ.schreibSlot t Λ k f v).slots t k' f' = σ.slots t k' f' := by
  simp only [World.schreibSlot, World.merke, World.storeSlot, dif_pos]
  by_cases hk : k' = k
  · subst hk; simp only [if_true]; rw [dif_neg h]
  · simp only [if_neg hk]

/-! ## 2. Live slots -/

namespace FreiForm

/-- Same free-list head and same links: the same slots are on the list. -/
theorem aufListe_gleich (A : FreiForm D) {σ σ' : World D} (hk : A.kopfSt σ' = A.kopfSt σ)
    (ho : ∀ j, A.naechst σ' j = A.naechst σ j) (i : Int) : A.AufListe σ' i ↔ A.AufListe σ i := by
  constructor
  · rintro ⟨L, hL, hm⟩
    rw [hk] at hL
    exact ⟨L, Kette.uebertragen hL (fun j _ => (ho j).symm), hm⟩
  · rintro ⟨L, hL, hm⟩
    refine ⟨L, ?_, hm⟩
    rw [hk]
    exact Kette.uebertragen hL (fun j _ => ho j)

/-- The free list is well formed in a world that has the same head, links and counter. -/
theorem freiOk_gleich (A : FreiForm D) {σ σ' : World D} (hk : A.kopfSt σ' = A.kopfSt σ)
    (ho : ∀ j, A.naechst σ' j = A.naechst σ j) (hs : A.stand σ' = A.stand σ) (h : A.FreiOk σ) :
    A.FreiOk σ' := by
  obtain ⟨L, hL, hnd, hlt⟩ := h
  refine ⟨L, ?_, hnd, fun i hi => by rw [hs]; exact hlt i hi⟩
  rw [hk]; exact Kette.uebertragen hL (fun j _ => ho j)

/-- **A LIVE slot:** below the used counter and not on the free list. -/
def Lebt (A : FreiForm D) (σ : World D) (i : Int) : Prop :=
  0 ≤ i ∧ i < A.stand σ ∧ ¬ A.AufListe σ i

/-- A run that leaves the free list and the counter alone leaves every liveness alone. -/
theorem lebt_gleich (A : FreiForm D) {σ σ' : World D} (hk : A.kopfSt σ' = A.kopfSt σ)
    (ho : ∀ j, A.naechst σ' j = A.naechst σ j) (hs : A.stand σ' = A.stand σ) (i : Int) :
    A.Lebt σ' i ↔ A.Lebt σ i := by
  unfold Lebt
  rw [hs, A.aufListe_gleich hk ho]

/-- **`alloc` from the used counter** (counter up by one, list untouched): every live slot stays live, and the
    new slot is live and was not on the list. -/
theorem lebt_bump (A : FreiForm D) {σ σ' : World D} (hok : A.FreiOk σ)
    (hk' : A.kopfSt σ' = A.kopfSt σ) (ho : ∀ j, A.naechst σ' j = A.naechst σ j)
    (hs : A.stand σ' = A.stand σ + 1) :
    A.FreiOk σ' ∧ (∀ j, A.Lebt σ j → A.Lebt σ' j) ∧ A.Lebt σ' (A.stand σ) := by
  obtain ⟨hok', hnot⟩ := A.bump_sicher σ σ' hok hk' ho hs
  exact ⟨hok', fun j ⟨h0, h1, h2⟩ => ⟨h0, by omega, fun hm => h2 ((A.aufListe_gleich hk' ho j).mp hm)⟩,
    A.stand_nonneg σ, by omega, hnot⟩

/-- **`alloc` from the free list**: the head slot turns live; every live slot stays live. -/
theorem lebt_abheb (A : FreiForm D) {σ σ' : World D} (hne : A.kopfSt σ < D.count A.tab) (hok : A.FreiOk σ)
    (hk' : A.kopfSt σ' = A.naechst σ (A.kopfSt σ)) (ho : ∀ j, A.naechst σ' j = A.naechst σ j)
    (hs : A.stand σ' = A.stand σ) :
    A.FreiOk σ' ∧ (∀ j, A.Lebt σ j → A.Lebt σ' j) ∧ A.Lebt σ' (A.kopfSt σ) := by
  obtain ⟨hok', hnot⟩ := A.abheben_sicher σ σ' hne hok hk' ho hs
  obtain ⟨L, hk, hnd, hlt⟩ := hok
  have hsub : ∀ j, A.AufListe σ' j → A.AufListe σ j := by
    rintro j ⟨L', hL', hm⟩
    generalize hg : A.kopfSt σ = kk at hk hk' hne
    cases hk with
    | nil => exact absurd hne (Int.lt_irrefl _)
    | cons k h0 hk1 L1 h1 =>
      have hch : A.Kette σ' (A.kopfSt σ') L1 := by
        rw [hk']; exact Kette.uebertragen h1 (fun j _ => ho j)
      have := Kette.eindeutig hL' hch
      subst this
      refine ⟨kk :: L', ?_, List.mem_cons_of_mem _ hm⟩
      rw [hg]; exact Kette.cons kk h0 hk1 L' h1
  have hkk : A.kopfSt σ ∈ L := by
    generalize hg : A.kopfSt σ = kk at hk hne ⊢
    cases hk with
    | nil => exact absurd hne (Int.lt_irrefl _)
    | cons k h0 hk1 L1 h1 => exact List.mem_cons_self
  refine ⟨hok', ?_, ?_⟩
  · exact fun j ⟨h0, h1, h2⟩ => ⟨h0, by omega, fun hm => h2 (hsub j hm)⟩
  · have := hlt _ hkk
    exact ⟨this.1, by omega, hnot⟩

/-- **`free`**: every live slot other than the released one stays live, the released one is dead, and the free list
    stays well formed. The released slot must be live (the checker's single-release rule, `N586`). -/
theorem lebt_frei (A : FreiForm D) {σ σ' : World D} (i : Int) (hi : A.Lebt σ i) (hok : A.FreiOk σ)
    (hk' : A.kopfSt σ' = i) (hl : A.naechst σ' i = A.kopfSt σ)
    (ho : ∀ j, j ≠ i → A.naechst σ' j = A.naechst σ j) (hs : A.stand σ' = A.stand σ) :
    A.FreiOk σ' ∧ (∀ j, A.Lebt σ j → j ≠ i → A.Lebt σ' j) ∧ ¬ A.Lebt σ' i := by
  obtain ⟨h0, h1, h2⟩ := hi
  have hok' := A.frei_erhaelt_von σ σ' i h0 h1 h2 hok hk' hl ho hs
  obtain ⟨L, hk, _, _⟩ := hok
  have hch : A.Kette σ' (A.kopfSt σ') (i :: L) := by
    rw [hk']
    refine Kette.cons i h0 (by have := A.stand_le σ; omega) L ?_
    rw [hl]
    exact Kette.uebertragen hk (fun j hj => ho j (fun e => h2 ⟨L, hk, e ▸ hj⟩))
  refine ⟨hok', fun j ⟨hj0, hj1, hj2⟩ hji => ⟨hj0, by omega, fun hm => hj2 ?_⟩,
    fun hh => hh.2.2 ⟨i :: L, hch, List.mem_cons_self⟩⟩
  obtain ⟨L', hL', hm'⟩ := hm
  have := Kette.eindeutig hL' hch
  subst this
  rcases List.mem_cons.mp hm' with e | e
  · exact absurd e hji
  · exact ⟨L, hk, e⟩

end FreiForm

end Gabbro.Grammatik
