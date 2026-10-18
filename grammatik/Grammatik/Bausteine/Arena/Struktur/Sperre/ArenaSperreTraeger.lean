/-
  File:      Grammatik/ArenaSperreTraeger.lean
  Subject:   A SHARED ARENA IS A LOCK INVARIANT (PLAN-DYNAMISCH.md section 8a.2, phase 3, step 1): the carriers the
             arena invariant `Dekl.Ok` reads, the proof that it reads nothing else, and the lock family `K.sperr L0`
             whose invariant of `L0` IS `Dekl.Ok` (and whose protected carriers are exactly those words).

  The carriers of an arena (`Dekl.orte`): its table (every field: payload, free link, list link, child links), the
  used counter, the free head, the committed word, the list head and the tree root. `Dekl.Ok` reads all of them but
  the committed word; the committed word is listed anyway, because `grow` writes it and the lock must guard it
  (`sperrSicht` then says it is accessed by the holder alone).

    * `ok_gleich_wort`  -- `Dekl.Ok` moves with nothing but those words (the premise `dekl_ok_traeger` of 8a.3).
    * `Dekl.sperr`      -- the lock family: `inv L0 = Ok`, `orte L0 = K.orte`, every other lock `true` / no carrier.
    * `sperr_lokal`     -- the invariant reads only the protected carriers (`SperrInvLokal`).
    * `sperr_ok`        -- `SperrInvOk` / `AkzeptiertSpec.sperrOrte`, from the declaration's `protects`.
-/
import Grammatik.Bausteine.Arena.Struktur.Erkenner.ArenaDekl
import Grammatik.Zielsatz.Kern.Spec

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette Gabbro.Grammatik.Zielsatz

variable {D : Deklaration}

namespace Dekl
variable {A : FreiForm D} (K : Dekl A)

/-- The globals the structures of the arena read through: counter, free head, list head, tree root. -/
def lesGlobs : List D.Glob :=
  [A.zaehl, A.kopf] ++ (K.liste.map fun d => d.G.g).toList ++ (K.baum.map fun b => b.Wz.g).toList

/-- **The carriers of an arena:** its table, the committed word, and the words `lesGlobs` reads. -/
def orte : List (D.Tab ⊕ D.Glob) :=
  Sum.inl A.tab :: Sum.inr A.komm :: K.lesGlobs.map Sum.inr

variable {K}

theorem mem_lesGlobs {g : D.Glob} : g ∈ K.lesGlobs ↔
    g = A.zaehl ∨ g = A.kopf ∨ (∃ d, K.liste = some d ∧ g = d.G.g) ∨ (∃ b, K.baum = some b ∧ g = b.Wz.g) := by
  simp only [lesGlobs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, Option.mem_toList,
    Option.map_eq_some_iff]
  constructor
  · rintro (((h | h) | ⟨d, hd, rfl⟩) | ⟨b, hb, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨d, hd, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨b, hb, rfl⟩))
  · rintro (h | h | ⟨d, hd, rfl⟩ | ⟨b, hb, rfl⟩)
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr ⟨d, hd, rfl⟩)
    · exact Or.inr ⟨b, hb, rfl⟩

theorem tab_mem_orte : Sum.inl A.tab ∈ K.orte := List.mem_cons_self

theorem komm_mem_orte : Sum.inr A.komm ∈ K.orte := by
  simp [orte]

theorem glob_mem_orte {g : D.Glob} (h : g ∈ K.lesGlobs) : Sum.inr g ∈ K.orte := by
  simp only [orte, List.mem_cons, List.mem_map]
  exact Or.inr (Or.inr ⟨g, h, rfl⟩)

/-- **`dekl_ok_traeger`: the arena invariant reads only the words of `Dekl.orte`.** A world that has the same table and
    the same `lesGlobs` meets the invariant as soon as the first one does. -/
theorem ok_gleich_wort {σ σ' : World D} (hs : σ'.slots A.tab = σ.slots A.tab)
    (hg : ∀ g ∈ K.lesGlobs, σ'.globs g = σ.globs g) (h : K.Ok σ) : K.Ok σ' := by
  have hz : A.stand σ' = A.stand σ :=
    congrArg (fun w => (Wert.umTyp A.hz w).n) (hg A.zaehl (mem_lesGlobs.mpr (Or.inl rfl)))
  have hk : A.kopfSt σ' = A.kopfSt σ :=
    congrArg (fun w => (Wert.umTyp A.hkopf w).n) (hg A.kopf (mem_lesGlobs.mpr (Or.inr (Or.inl rfl))))
  have ho : ∀ j, A.naechst σ' j = A.naechst σ j := fun j => by simp only [FreiForm.naechst, hs]
  refine Ok.gleich ?_ ?_ (A.freiOk_gleich hk ho hz h.1) (fun j hj => (A.lebt_gleich hk ho hz j).mpr ?_) h
  · refine ⟨fun d hd => ⟨fun j => by simp only [LinkFeld.wert, hs], ?_⟩⟩
    exact congrArg (fun w => (Wert.umTyp d.G.hg w).n)
      (hg d.G.g (mem_lesGlobs.mpr (Or.inr (Or.inr (Or.inl ⟨d, hd, rfl⟩)))))
  · refine ⟨fun b hb => ⟨fun j => by simp only [LinkFeld.wert, hs], fun j => by simp only [LinkFeld.wert, hs], ?_⟩⟩
    exact congrArg (fun w => (Wert.umTyp b.Wz.hg w).n)
      (hg b.Wz.g (mem_lesGlobs.mpr (Or.inr (Or.inr (Or.inr ⟨b, hb, rfl⟩)))))
  · rcases hj with hj | hj
    · exact Dekl.InL.lebt h.2.1 hj
    · exact Dekl.InB.lebt h.2.2.1 hj

theorem ok_gleich_wort_iff {σ σ' : World D} (hs : σ'.slots A.tab = σ.slots A.tab)
    (hg : ∀ g ∈ K.lesGlobs, σ'.globs g = σ.globs g) : K.Ok σ' ↔ K.Ok σ :=
  ⟨ok_gleich_wort hs.symm (fun g hg' => (hg g hg').symm), ok_gleich_wort hs hg⟩

/-- The invariant does not read the trace. -/
theorem ok_spur (σ : World D) (sp : List (Ereignis D)) : K.Ok (σ.speicher.welt sp) ↔ K.Ok σ :=
  ok_gleich_wort_iff (σ := σ) (σ' := σ.speicher.welt sp) rfl (fun _ _ => rfl)

end Dekl

/-! ## The lock family of a shared arena -/

section Sperre
open Classical

variable {A : FreiForm D} (K : Dekl A) (L0 : D.Lock)

/-- **The lock family of a shared arena:** the lock `L0` protects the arena's carriers and its invariant is the arena's
    structure invariant; every other lock protects nothing and has the invariant `true`. -/
noncomputable def Dekl.sperr : SperrInv D where
  orte := fun L => if L = L0 then K.orte else []
  inv := fun L s => if L = L0 then decide (K.Ok (s.welt [])) else true

variable {K L0}

theorem Dekl.sperr_inv_iff (s : Speicher D) : (K.sperr L0).inv L0 s = true ↔ K.Ok (s.welt []) := by
  simp [Dekl.sperr]

theorem Dekl.sperr_inv_iff' (σ : World D) : (K.sperr L0).inv L0 σ.speicher = true ↔ K.Ok σ := by
  rw [Dekl.sperr_inv_iff, Dekl.ok_spur]

theorem Dekl.sperr_inv_andere {L : D.Lock} (h : L ≠ L0) (s : Speicher D) : (K.sperr L0).inv L s = true := by
  simp [Dekl.sperr, h]

theorem Dekl.sperr_orte_andere {L : D.Lock} (h : L ≠ L0) : (K.sperr L0).orte L = [] := by
  simp [Dekl.sperr, h]

theorem Dekl.sperr_orte_self : (K.sperr L0).orte L0 = K.orte := by
  simp [Dekl.sperr]

/-- **The invariant reads only the protected carriers** (`SperrInvLokal`, the user's duty in (b), discharged here
    once for every arena). -/
theorem Dekl.sperr_lokal : SperrInvLokal (K.sperr L0) := by
  intro L s s' h
  by_cases hL : L = L0
  · subst hL
    have hs : (s'.welt []).slots A.tab = (s.welt []).slots A.tab := (h (Sum.inl A.tab) (by
      rw [Dekl.sperr_orte_self]; exact Dekl.tab_mem_orte)).symm
    have hg : ∀ g ∈ K.lesGlobs, (s'.welt []).globs g = (s.welt []).globs g := fun g hg =>
      (h (Sum.inr g) (by rw [Dekl.sperr_orte_self]; exact Dekl.glob_mem_orte hg)).symm
    have := Dekl.ok_gleich_wort_iff (K := K) hs hg
    simp only [Dekl.sperr, if_true]
    exact decide_eq_decide.mpr this.symm
  · simp [Dekl.sperr, hL]

/-- **`SperrInvOk` of the arena family**, from the one declaration fact: every carrier of the arena is guarded by `L0`
    (`protects`; the checker's `sperrOrte`). -/
theorem Dekl.sperr_ok (hB : ∀ c ∈ K.orte, Bewacht c L0) : SperrInvOk (K.sperr L0) :=
  ⟨fun L c hc => by
    by_cases hL : L = L0
    · subst hL; rw [Dekl.sperr_orte_self] at hc; exact hB c hc
    · rw [Dekl.sperr_orte_andere hL] at hc; exact absurd hc List.not_mem_nil,
   fun L s s' h => Dekl.sperr_lokal L s s' h⟩

end Sperre

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.Dekl.ok_gleich_wort
#print axioms Gabbro.Grammatik.Dekl.sperr_ok
