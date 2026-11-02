module

public import Grammatik.Zielsatz.Kern.Spec
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSperre

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

theorem ptrPre_mitRuhe_iff (S : Signatur D.Tab D.Glob D.Lock D.Marke)
    (C : CallContract D S) (s : World D) (ρ : Env D S.params) :
    (ruCallContract S C).preHolds (worldR s) (envR ρ) ↔ C.preHolds s ρ := by
  unfold CallContract.preHolds
  change wahr? (eval (worldR s) (Expr.umΛ _ (ruE C.pre)) (worldR s) (envR ρ)) = true ↔ _
  rw [eval_umΛ', eval_ru]
  rfl

theorem ptrPost_mitRuhe_iff (S : Signatur D.Tab D.Glob D.Lock D.Marke)
    (C : CallContract D S) (s0 s1 : World D) (ρ : Env D S.params)
    (v : ErgVal D S.erg) :
    (ruCallContract S C).postHolds (worldR s0) (worldR s1) (envR ρ) (ergR S.erg v) ↔
      C.postHolds s0 s1 ρ v := by
  unfold CallContract.postHolds
  have e : eval (worldR s0) (ruCallContract S C).post (worldR s1)
      (ergEnv (S.erg.map tyR) (ergR S.erg v) (envR ρ)) = eval s0 C.post s1 (ergEnv S.erg v ρ) :=
    (eval_umΓ_ergEnv S.erg _ _ _ _ v ρ).trans
      ((eval_umΛ' _ _ _ _ _).trans (eval_ru s0 s1 C.post (ergEnv S.erg v ρ)))
  exact Iff.of_eq (congrArg (fun x => wahr? x = true) e)

private theorem ergR_cast (a b : Option Ty) (e : a = b)
    (e' : a.map tyR = b.map tyR) (v : ErgVal D a) :
    cast (congrArg (ErgVal D.mitRuhe) e') (ergR a v) =
      ergR b (cast (congrArg (ErgVal D) e) v) := by
  subst b
  rfl

theorem ptrVerfeinert_mitRuhe {P : Programm D} (h : PtrVerfeinert P) :
    PtrVerfeinert P.mitRuhe := by
  intro f n hf
  cases f with
  | none =>
      cases n with
      | zero => exact ⟨fun _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩
      | succ n => cases hf
  | some f =>
      cases n with
      | zero => cases hf
      | succ n =>
          have hf0 : D.passt f n = true := hf
          have hu := umsig_ru hf0 hf
          have hv : ∀ v : ErgVal D (D.erg f),
              ptrResult hf (ergR (D.erg f) v) =
                ergR (D.sigNr n).erg (ptrResult hf0 v) := by
            intro v
            exact ergR_cast _ _ (D.passt_sig hf0).erg (congrArg (Option.map tyR) (D.passt_sig hf0).erg) v
          refine ⟨?_, ?_⟩
          · intro s ρ hp
            obtain ⟨s, rfl⟩ : ∃ s', s = worldR s' := ⟨worldZ s, (worldR_worldZ s).symm⟩
            obtain ⟨ρ, rfl⟩ : ∃ r, ρ = envR r := ⟨envZ ρ, (envR_envZ ρ).symm⟩
            rw [hu]
            exact (req_mitRuhe_iff P f s _).mpr
              ((h f n hf0).1 s ρ ((ptrPre_mitRuhe_iff _ _ _ _).mp hp))
          · intro s0 s1 ρ v hp he
            obtain ⟨s0, rfl⟩ : ∃ s', s0 = worldR s' := ⟨worldZ s0, (worldR_worldZ s0).symm⟩
            obtain ⟨s1, rfl⟩ : ∃ s', s1 = worldR s' := ⟨worldZ s1, (worldR_worldZ s1).symm⟩
            obtain ⟨ρ, rfl⟩ : ∃ r, ρ = envR r := ⟨envZ ρ, (envR_envZ ρ).symm⟩
            obtain ⟨v, rfl⟩ : ∃ w, v = ergR (D.erg f) w := ⟨ergZ (D.erg f) v, (ergR_ergZ (D.erg f) v).symm⟩
            rw [hu] at he
            have he0 : EnsAmRueck P f s0 s1 (umsig hf0 ρ) v := by
              unfold EnsAmRueck at he ⊢
              rw [← ens_mitRuhe_eval P f s0 s1 v (umsig hf0 ρ)]
              exact he
            rw [hv]
            exact (ptrPost_mitRuhe_iff _ _ _ _ _ _).mpr
              ((h f n hf0).2 s0 s1 ρ v ((ptrPre_mitRuhe_iff _ _ _ _).mp hp) he0)

end Gabbro.Grammatik
