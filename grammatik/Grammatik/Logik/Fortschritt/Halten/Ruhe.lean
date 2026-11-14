/- The source program's checked bounds also hold in the runtime program. The idle root
   holds no signature lock and its body is only `return`: it has no section and no call. -/
module
public import Grammatik.Logik.Fortschritt.Halten.RuhePruefung
@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

/-- **The hold-bound check lifts to the runtime's idle root.** Only user functions enter the
    cost-checked list; the idle root calls nothing and contains no section. Costs and bounds
    of every user function/lock are unchanged. -/
theorem haltPasst_mitRuhe [DecidableEq D.Fn] (P : Programm D) (passes : Nat)
    (N : D.Lock → Nat) (decl : D.Fn → Nat) (fs ks : List D.Fn)
    (h : haltPasst P passes N decl fs ks = true) :
    haltPasst P.mitRuhe passes N (fun g => g.elim 0 decl) (fsRuhe fs) (ks.map some) = true := by
  have members : (fun g : Option D.Fn => @List.contains _ instBEqOfDecidableEq (ks.map some) g) =
      (fun g => g.elim false (ks.contains ·)) := by
    funext g
    rw [Bool.eq_iff_iff]
    cases g <;> simp [Option.elim, List.contains_iff_mem]
  unfold haltPasst at h ⊢
  obtain ⟨costs, sections⟩ := Bool.and_eq_true_iff.mp h
  apply Bool.and_eq_true_iff.mpr
  constructor
  · unfold kostenPasst at costs ⊢
    apply List.all_eq_true.mpr
    intro g hg
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hg
    have row := List.all_eq_true.mp costs f hf
    erw [members, HaltRuhe.kostenEpilog_mitRuhe]
    dsimp only [Programm.mitRuhe]
    erw [HaltRuhe.kostenEnd_umΛ, HaltRuhe.kostenEnd_ru,
      HaltRuhe.rufeE_umΛ, HaltRuhe.rufeE_ru]
    exact row
  · apply List.all_eq_true.mpr
    intro g hg
    rcases List.mem_cons.mp hg with root | user
    · subst g
      rfl
    · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp user
      have row := List.all_eq_true.mp sections f hf
      erw [members, HaltRuhe.kostenEpilog_mitRuhe]
      dsimp only [Programm.mitRuhe]
      erw [HaltRuhe.haltE_umΛ, HaltRuhe.haltE_ru]
      exact row

end Gabbro.Grammatik
