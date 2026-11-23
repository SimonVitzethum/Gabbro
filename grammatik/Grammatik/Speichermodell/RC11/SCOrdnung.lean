/-
  File:      Grammatik/Speichermodell/RC11/SCOrdnung.lean
  Subject:   WHAT "SEQUENTIALLY CONSISTENT" MEANS for an execution graph: `SCKonsistent` (Shasha–Snir
             acyclicity) gives ONE total order of all events -- an interleaving -- that extends program
             order and modification order and in which every read reads the LAST write to its
             location before it (`sc_verschraenkung`). With `drf_sc` (DRFSC.lean): a race-free
             program with only `seq_cst` atomics behaves as an interleaving on one memory.
-/
module

public import Grammatik.Speichermodell.RC11.Konsistent
public import Mathlib.Order.Extension.Linear

@[expose] public section

namespace Gabbro.Grammatik.Speichermodell.RC11

section Linear

variable {E : Type}

/-- The reflexive-transitive closure, written as equality or a closure path. -/
def reflAbschluss (r : E → E → Prop) (a b : E) : Prop := a = b ∨ Relation.TransGen r a b

theorem reflAbschluss_teilordnung {r : E → E → Prop} (h : Azyklisch r) :
    IsPartialOrder E (reflAbschluss r) where
  refl := fun _ => Or.inl rfl
  trans := fun _ _ _ hab hbc => by
    rcases hab with rfl | hab
    · exact hbc
    · rcases hbc with rfl | hbc
      · exact Or.inr hab
      · exact Or.inr (hab.trans hbc)
  antisymm := fun a _ hab hba => by
    rcases hab with rfl | hab
    · rfl
    · rcases hba with rfl | hba
      · rfl
      · exact absurd (hab.trans hba) (h a)

/-- **Szpilrajn for an acyclic relation**: a strict total order that contains it. -/
theorem lineare_erweiterung {r : E → E → Prop} (h : Azyklisch r) :
    ∃ T : E → E → Prop, (∀ a b c, T a b → T b c → T a c) ∧ (∀ a, ¬ T a a) ∧
      (∀ a b, a ≠ b → T a b ∨ T b a) ∧ (∀ a b, r a b → T a b) := by
  haveI := reflAbschluss_teilordnung h
  obtain ⟨s, hs, hRs⟩ := extend_partialOrder (reflAbschluss r)
  haveI := hs
  refine ⟨fun a b => s a b ∧ a ≠ b, ?_, ?_, ?_, ?_⟩
  · intro a b c hab hbc
    refine ⟨IsTrans.trans (r := s) _ _ _ hab.1 hbc.1, ?_⟩
    rintro rfl
    exact hab.2 (Std.Antisymm.antisymm (r := s) _ _ hab.1 hbc.1)
  · intro a ha
    exact ha.2 rfl
  · intro a b hne
    rcases Std.Total.total (r := s) a b with h1 | h1
    · exact Or.inl ⟨h1, hne⟩
    · exact Or.inr ⟨h1, fun e => hne e.symm⟩
  · intro a b hab
    refine ⟨hRs a b (Or.inr (.single hab)), ?_⟩
    rintro rfl
    exact h a (.single hab)

end Linear

namespace Graph

variable {E Ort Wert : Type} {G : Graph E Ort Wert}

/-- **A sequentially consistent graph is an interleaving on one memory.** There is a strict total
    order `T` of all events that extends program order and modification order, puts every read
    after the write it reads, and in which no other write to the read's location lies between
    the two: every read reads the last write before it. -/
theorem sc_verschraenkung (hw : G.Wohlgeformt) (hsc : G.SCKonsistent) :
    ∃ T : E → E → Prop, (∀ a b c, T a b → T b c → T a c) ∧ (∀ a, ¬ T a a) ∧
      (∀ a b, a ≠ b → T a b ∨ T b a) ∧ (∀ a b, G.po a b → T a b) ∧
      (∀ a b, G.mo a b → T a b) ∧
      (∀ w r, G.rf w r → T w r ∧
        ∀ w', G.schreibt w' → G.ort w' = G.ort r → T w' r → w' = w ∨ T w' w) := by
  obtain ⟨T, htr, hirr, htot, hext⟩ := lineare_erweiterung hsc
  refine ⟨T, htr, hirr, htot, fun a b h => hext a b (Or.inl h),
    fun a b h => hext a b (Or.inr (Or.inr (Or.inl h))), ?_⟩
  intro w r hrf
  refine ⟨hext w r (Or.inr (Or.inl hrf)), ?_⟩
  intro w' hw' ho hT
  by_cases he : w' = w
  · exact Or.inl he
  · have hort : G.ort w' = G.ort w := ho.trans (hw.rf_ort _ _ hrf).symm
    rcases hw.mo_total w' w hw' (hw.rf_schreibt _ _ hrf) hort he with hmo | hmo
    · exact Or.inr (hext _ _ (Or.inr (Or.inr (Or.inl hmo))))
    · have hne : r ≠ w' := by
        rintro rfl
        exact hirr _ hT
      have hrb : G.rb r w' := ⟨w, hrf, hmo, hne⟩
      exact absurd (htr _ _ _ hT (hext _ _ (Or.inr (Or.inr (Or.inr hrb))))) (hirr _)

end Graph

end Gabbro.Grammatik.Speichermodell.RC11
