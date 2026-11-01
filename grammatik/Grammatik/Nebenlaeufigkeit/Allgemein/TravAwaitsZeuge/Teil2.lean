module

public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiVoll
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraetZeuge
public import Grammatik.Nebenlaeufigkeit.Allgemein.TravAwaitsZeuge.Teil1

@[expose] public section

namespace Gabbro.Grammatik

theorem taP_koerper_haupt1 : KoerperGutG taP 0 taHaupt1 := by
  intro O' _ _ R _ hOV σ ρ _
  refine ⟨fun _ _ _ => rfl, fun g hrun => ?_⟩
  have hr : taP.rumpf taHaupt1 = taRumpfHaupt1 := rfl
  have ht : ∀ σ1 ρ1, torRuf taP R taWarte σ1 ρ1 = R taWarte σ1 ρ1 := fun _ _ => if_pos rfl
  rw [hr] at hrun
  rcases execEnd_cons_logikV _ _ _ _ _ _ _ _ hrun with h1 | ⟨σ1, ρ1, _, h1⟩
  · simp only [taLocksH, execStmt] at h1
    have h2 := execBlock_eins_logikV _ _ _ _ _ _ (mapWelt_logikV h1)
    simp only [taRufWarte, execStmt, ht] at h2
    split at h2
    · cases h2
    · rename_i r _
      exact nomatch r
    · rename_i e hR
      cases h2
      exact hOV _ _ _ _ hR g rfl
    · cases h2
  · simp only [taRetH1, execEnd] at h1
    cases h1

theorem taP_koerper_ruhe : KoerperGutG taP 0 taRuhe := by
  intro O' _ _ R _ _ σ ρ _
  refine ⟨fun _ _ _ => rfl, fun g hrun => ?_⟩
  have hr : taP.rumpf taRuhe = taRumpfRuhe := rfl
  rw [hr] at hrun
  simp only [taRumpfRuhe, execEnd] at hrun
  cases hrun

theorem taP_koerper : ∀ f, KoerperGutG taP 0 f := by
  intro f
  cases f
  · exact taP_koerper_haupt0
  · exact taP_koerper_fuelle
  · exact taP_koerper_haupt1
  · exact taP_koerper_warte
  · exact taP_koerper_ruhe

def taE0 : Ereignis taD := .gibt TaLock.k

/-- **All premises of `ziel_ort_geraet` hold jointly on `taP`.** -/
theorem taP_vertragAmOrt : ∀ M : RufMaschineG taD,
    RufErreichbarG taP taO 0 (RufStartG taP taSp taInit) M → VertragAmOrtG taP M :=
  ziel_ort_geraet taP taO 0 taFs taSp taInit taE0 taO_gut taO_lokal taFs_voll taP_fragment
    taP_fuss taP_koerper taP_start taInit_exklusiv

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.taP_vertragAmOrt
