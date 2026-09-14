/-
  File:      Grammatik/Zielsatz/RuheZeuge.lean
  Subject:   witnesses for the runtime's idle root (A4): the programs that
             had NO admissible start before have one on `P.mitRuhe`.

  * The export of `beispiele/104` (`gP_start_leer`: no start of `gP`
    itself): on `gP.mitRuhe` the root on every thread is admissible
    (`gP_mitRuhe_start`), and the checker's Bool holds there
    (`gP_mitRuhe_akzeptiert`, from the Bool on `gP` by
    `akzeptiert_mitRuhe`).
  * Probes B/C (`zPB`, `zPC` over `zD`, no idle function): admissible starts
    on `zPB.mitRuhe`, `zPC.mitRuhe` (`probeB_start`, `probeC_start`).
  * The two-thread fixture `mP`: its declared starts `hauptA`, `hauptB` on
    threads 0 and 1 and the root everywhere else (`mP_mitRuhe_start`, by
    `startZulaessig_mitRuhe`), and the Bool on `mP.mitRuhe`.
-/
import Grammatik.Zielsatz.Ruhe
import Grammatik.Zielsatz.AkzeptiertZeuge
import Grammatik.ZielOrtSperreZeuge

namespace Gabbro.Grammatik

open Zielsatz

variable {D : Deklaration}

theorem eval_umΛ {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty} (h : Λ = Λ') (e : Expr D Γ Λ τ)
    (σ₀ σ : World D) (ρ : Env D Γ) : eval σ₀ (Expr.umΛ h e) σ ρ = eval σ₀ e σ ρ := by
  subst h; rfl

/-- A `requires true` of `P` stays `true` on `P.mitRuhe`. -/
theorem req_mitRuhe_wahr (P : Programm D) (f : D.Fn) (hf : P.requires f = .wahr)
    (σ : World D.mitRuhe) (ρ : Env D.mitRuhe (D.mitRuhe.params (some f))) :
    ReqAmEintritt P.mitRuhe (some f) σ ρ := by
  refine (congrArg wahr? (eval_umΛ (anfang_map (D.signatur f)) (ruE (P.requires f)) σ σ ρ)).trans ?_
  have e : ruE (P.requires f) = ruE (Expr.wahr (D := D)) := by rw [hf]
  rw [e]
  rfl

/-! ## 1. The export of `beispiele/104` -/

/-- A memory of the export: every balance `0`. -/
def x104Sp : Speicher x104D :=
  ⟨fun t _ f => match t, f with
    | .Konto, .stand => ⟨0, by decide, by decide⟩, fun g => nomatch g⟩

/-- **The checker's Bool holds on the export with the runtime's root.** -/
theorem gP_mitRuhe_akzeptiert :
    Akzeptiert x104P.mitRuhe x104S.mitRuhe (fsRuhe x104Fs) x104Ls x104Cs (wsRuhe []) = true :=
  akzeptiert_mitRuhe x104P x104Fs_voll x104Ls_voll x104Cs_voll gP_akzeptiert

/-- **An admissible start of `gP.mitRuhe`** -- the export itself has none
    (`gP_start_leer`). -/
theorem gP_mitRuhe_start :
    ∃ (sp : Speicher x104D.mitRuhe)
      (init : Faden → Σ f : x104D.mitRuhe.Fn, Env x104D.mitRuhe (x104D.mitRuhe.params f)),
      StartZulaessig x104P.mitRuhe x104S.mitRuhe (fsRuhe x104Fs) (wsRuhe []) sp init :=
  ⟨speicherR x104Sp, ruheInit _, startZulaessig_ruhe x104P _ (fun _ => rfl)⟩

/-! ## 2. Probes B and C -/

/-- **An admissible start of probe B on `zPB.mitRuhe`.** -/
theorem probeB_start :
    ∃ (sp : Speicher zD.mitRuhe)
      (init : Faden → Σ f : zD.mitRuhe.Fn, Env zD.mitRuhe (zD.mitRuhe.params f)),
      StartZulaessig zPB.mitRuhe zS.mitRuhe (fsRuhe zFs) (wsRuhe []) sp init :=
  ⟨speicherR zSp, ruheInit _, startZulaessig_ruhe zPB _ (fun _ => rfl)⟩

/-- **An admissible start of probe C on `zPC.mitRuhe`.** -/
theorem probeC_start :
    ∃ (sp : Speicher zD.mitRuhe)
      (init : Faden → Σ f : zD.mitRuhe.Fn, Env zD.mitRuhe (zD.mitRuhe.params f)),
      StartZulaessig zPC.mitRuhe zS.mitRuhe (fsRuhe zFs) (wsRuhe []) sp init :=
  ⟨speicherR zSp, ruheInit _, startZulaessig_ruhe zPC _ (fun _ => rfl)⟩

/-! ## 3. The two-thread fixture with its declared starts -/

theorem mP_mitRuhe_akzeptiert :
    Akzeptiert mP.mitRuhe mSI.mitRuhe (fsRuhe mFs) [()] mCs (wsRuhe [mHauptA, mHauptB]) = true :=
  akzeptiert_mitRuhe mP mFs_voll mLocks_voll mCs_voll mP_akzeptiert

/-- **`hauptA` on thread 0, `hauptB` on thread 1, the root everywhere
    else, is admissible on `mP.mitRuhe`.** -/
theorem mP_mitRuhe_start :
    StartZulaessig mP.mitRuhe mSI.mitRuhe (fsRuhe mFs) (wsRuhe [mHauptA, mHauptB])
      (speicherR mSp) (initRuhe [⟨mHauptA, .nil⟩, ⟨mHauptB, .nil⟩]) := by
  refine startZulaessig_mitRuhe mP _ _ ?_ (by decide) ?_ ?_
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact req_mitRuhe_wahr mP mHauptA rfl _ _
    · exact req_mitRuhe_wahr mP mHauptB rfl _ _
  · intro L
    rw [speicherZ_speicherR]
    cases L
    decide

#print axioms Gabbro.Grammatik.gP_mitRuhe_akzeptiert
#print axioms Gabbro.Grammatik.gP_mitRuhe_start
#print axioms Gabbro.Grammatik.probeB_start
#print axioms Gabbro.Grammatik.probeC_start
#print axioms Gabbro.Grammatik.mP_mitRuhe_akzeptiert
#print axioms Gabbro.Grammatik.mP_mitRuhe_start

end Gabbro.Grammatik
