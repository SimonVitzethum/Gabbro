module
public import Bruecke.Teil.Start
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {C : Fin u.fns.length → Prop}

/-- Lowering equations only for carried functions; open functions keep their contracts. -/
structure GesenktC (u : UProg) (C : Fin u.fns.length → Prop) (P : Programm (declOf u)) : Prop where
  req : ∀ f, C f → P.requires f = .tru
  ens : ∀ f, C f → ∃ e0, lowEnsList u (ErgCtx (ctxOf u f) (verOf u f).erg) (verOf u f).ende (fnAt u f)
      (fnAt u f).ergTy (fnAt u f).gives = .ok e0 ∧ HEq (P.ensures f) e0
  rumpf : ∀ f, C f → ∃ b0, lowBody u f (fnAt u f).body (fnAt u f).ret = .ok b0 ∧ HEq (P.rumpf f) b0

theorem gesenkt_of_teil {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (S : Getragen u C)
    (h : lowerAllg u = .ok (P, fs)) : GesenktC u C P := by
  have hreq := fun f hf => requires_tru_of_needs_leer h f (S.ohneReq f hf)
  unfold lowerAllg at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i hall
      split at h
      ·
        obtain ⟨rfl, -⟩ := Gabbro.Grammatik.Parser.Measures.checkedProgram_eq h
        refine ⟨hreq, fun f hf => ?_, fun f hf => ?_⟩
        · have w := lowerEach_all_ok u (List.finRange u.fns.length) f (List.mem_finRange f) hall
          obtain ⟨v, hv⟩ := w
          obtain ⟨e0, b0, he, hb, he', _⟩ := lowerFnAt_ok f (S.ohneTransition f hf) hv
          refine ⟨e0, he, ?_⟩
          show HEq (lowerAtPair u f _).1 e0
          rw [lowerAtPair_eq f _ hv]
          exact he'
        · have w := lowerEach_all_ok u (List.finRange u.fns.length) f (List.mem_finRange f) hall
          obtain ⟨v, hv⟩ := w
          obtain ⟨e0, b0, he, hb, _, hb'⟩ := lowerFnAt_ok f (S.ohneTransition f hf) hv
          refine ⟨b0, hb, ?_⟩
          show HEq (lowerAtPair u f _).2.1 b0
          rw [lowerAtPair_eq f _ hv]
          exact hb'

      · cases h

theorem post_iff_teil {P : Programm (declOf u)} (G : GesenktC u C P) (f : Fin u.fns.length) (hf : C f)
    (hA : ArtStimmt (fnAt u f)) (hT : TabEindeutig u) (hN : NamenFrei (fnAt u f))
    (hO : OldsKurz u (fnAt u f)) (hD : PostDef u (fnAt u f))
    (hBE : ErgSchlicht (fnAt u f)) (hBT : ∀ t : Fin u.tabs.length, (tabAt u t).bools = [] ∧ (tabAt u t).opts = [] ∧ (tabAt u t).werte = [])
    (σ₀ σ' : World (declOf u)) (ρ : Env (declOf u) ((declOf u).params f))
    (v : ErgVal (declOf u) ((declOf u).erg f)) (s s' : Gabbro.Body.State)
    (hW₀ : WRel u σ₀ s.world) (hL₀ : LRel (fnAt u f) 0 ρ s.local') (hW : WRel u σ' s'.world) :
    (postU u (wfU u) (fnAt u f) s s' (ergValOf ((declOf u).erg f) v)).getD False ↔
      EnsAmRueck P f σ₀ σ' ρ v := by
  obtain ⟨cs, hcs⟩ := ensList_some (fnAt u f) s s' (ergValOf ((declOf u).erg f) v) _ hD
  obtain ⟨e0, he0, hPe⟩ := G.ens f hf
  let E := ergEnv ((declOf u).erg f) v ρ
  let E₀ : Env (declOf u) (ErgCtx (ctxOf u f) (verOf u f).erg) :=
    cast (congrArg (Env (declOf u)) (ensCtx_eq u f).symm) E
  have hE : HEq E₀ E := cast_heq _ _
  have hL : LRel (fnAt u f) (if (fnAt u f).ergTy.isSome then 1 else 0) E₀ s.local' := by
    intro p j hj
    rw [nthVal_heq (ensCtx_eq u f) E₀ E hE, ← isSome_erg f, nthVal_ergEnv]
    exact (hL₀ p j hj).trans (by rw [Nat.zero_add])
  have her : (fnAt u f).ergTy.isSome = true →
      ergValOf ((declOf u).erg f) v = some (nthVal E₀ 0) := by
    intro h
    rw [nthVal_heq (ensCtx_eq u f) E₀ E hE]
    exact ergValOf_nth _ v ρ (by rw [isSome_erg f]; exact h)
  have hcl := ensList_iff hA hT hN σ₀ σ' E₀ s s' hW₀ hL hW _ her (fnAt u f).gives cs e0
    hO hcs he0
  have hev : eval σ₀ (P.ensures f) σ' E = eval σ₀ e0 σ' E₀ :=
    eval_heq2 (ensCtx_eq u f).symm rfl _ _ hPe E E₀ hE.symm σ₀ σ'
  unfold EnsAmRueck
  rw [show ergEnv ((declOf u).erg f) v ρ = E from rfl, hev, ← hcl]
  simp only [postU, hcs, Option.getD_some]
  rw [chain_iff]
  have hrc := resultClause_wahr f hBE v
  constructor
  · intro ⟨_, hall⟩ q hq
    exact hall q (List.mem_append_right _ hq)
  · intro hall
    refine ⟨wf_of_wrel u hBT hW, fun q hq => ?_⟩
    rcases List.mem_append.mp hq with hq | hq
    · exact hrc q hq
    · exact hall q hq

end Gabbro.Bruecke
