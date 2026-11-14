/- C08 integration blockers: recorded keys and the independent declared Q.

   These witnesses isolate two missing premises of the proposed integration.
   A real replay record is answered at its stored key, not at a second question.
   The software interface post also needs an explicit refinement into E.Q.
   No goal statement is changed until these obligations can be discharged.
-/
module

public import Grammatik.Logik.Ruf.FremdRuf.T10RunZeuge

@[expose] public section

namespace Gabbro.Grammatik

open Zielsatz

namespace CallSiteBlocker

open CallSiteZeuge

/-- A binding with no writes preserves the input world, including its trace.
    This binding supplies no added events and satisfies GutO. -/
def traceOracle : Orakel decl where
  wirktL := fun _ σ _ => ({ σ with spur := [] }, 0)
  regLiesL := fun e => nomatch e
  regSchreib := fun e => nomatch e
  sichtbarL := fun e => nomatch e

theorem traceOracle_gut : GutO traceOracle := by
  intro a σ ρ
  refine ⟨rahmen_gleich rfl rfl, rfl, ?_⟩
  intro hgt hgg
  refine ⟨[], [], [], ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · intro t
    exact nomatch t
  · intro g
    exact nomatch g
  · intro t
    exact nomatch t
  · intro g
    exact nomatch g
  · intro m
    exact nomatch m
  · intro L
    exact nomatch L

/-- A singleton real replay record, keyed by its already recorded question. -/
def actualHistory (σ : World decl) : List (AxEintrag decl) :=
  [⟨(), σ.fragt (.inl ()), rho true,
    traceOracle.wirkt () (σ.fragt (.inl ())) (rho true)⟩]

/-- Replay's existing direct-key linkage holds for the actual binding. -/
theorem actualHistory_passt (σ : World decl) : PasstA traceOracle (actualHistory σ) := by
  intro a τ ρ x hm
  have he : (⟨a, τ, ρ, x⟩ : AxEintrag decl) =
      ⟨(), σ.fragt (.inl ()), rho true,
        traceOracle.wirkt () (σ.fragt (.inl ())) (rho true)⟩ := by
    simpa only [actualHistory, List.mem_singleton] using hm
  cases a
  have hτ := congrArg (fun e : AxEintrag decl => e.2.1) he
  have hx := congrArg (fun e : AxEintrag decl => e.2.2.2) he
  change τ = σ.fragt (.inl ()) at hτ
  change (τ, 0) = x
  rw [hτ]
  exact hx.symm

/-- The stored key is a question world, rather than a second oracle query. -/
theorem actualHistory_provenance (σ : World decl) : SchluesselHerkunft (actualHistory σ) := by
  intro e hm
  have he : e = ⟨(), σ.fragt (.inl ()), rho true,
      traceOracle.wirkt () (σ.fragt (.inl ())) (rho true)⟩ := by
    simpa only [actualHistory, List.mem_singleton] using hm
  subst e
  exact ⟨σ, rfl⟩

theorem actualHistory_good (σ : World decl) :
    CallSitePflichtFremd unit.P.axVertrag (actualHistory σ) := by
  intro a τ ρ x hm hsw
  have he : (⟨a, τ, ρ, x⟩ : AxEintrag decl) =
      ⟨(), σ.fragt (.inl ()), rho true,
        traceOracle.wirkt () (σ.fragt (.inl ())) (rho true)⟩ := by
    simpa only [actualHistory, List.mem_singleton] using hm
  cases a
  have hr := congrArg
    (fun p : World decl × Env decl (decl.aparams ()) × (World decl × Int) => p.2.1)
    (eq_of_heq (Sigma.mk.inj he).2)
  change ρ = rho true at hr
  rw [hr]
  exact pre_true τ

theorem foreign_trace : ForeignPflicht unit traceOracle [] where
  vertrag := by
    intro a hsw σ ρ hpre v hv
    rfl
  dekodiert := by
    intro a hsw σ ρ
    change some (Sum.inl ()) ≠ none
    intro h
    cases h
  klauseln := by
    intro n
    exact Fin.elim0 n
  anbieter := providerRealisiert_nil traceOracle

/-- The corrected transports apply to the same trace-faithful oracle that
    refutes the double-question linkage below. -/
theorem actualHistory_posts (σ : World decl) :
    AxNach unit.P.axVertrag () (σ.fragt (.inl ())) (rho true) (σ.fragt (.inl ())) () ∧
    unit.Q () (σ.fragt (.inl ())) () = true := by
  have hm : (⟨(), σ.fragt (.inl ()), rho true, (σ.fragt (.inl ()), 0)⟩ : AxEintrag decl) ∈
      actualHistory σ := by
    simp only [actualHistory, List.mem_singleton, Orakel.wirkt, traceOracle, World.auf_leer]
  have hv : einpassenErg traceOracle.zeiger (decl.aerg ()) (0 : Int) = some () := rfl
  exact ⟨vertragANeu_sw_of_foreign foreign_trace (actualHistory_good σ)
      (actualHistory_passt σ) (actualHistory_provenance σ) hm rfl hv,
    qAmDatensatz_of_foreign foreign_trace (actualHistory_good σ)
      (actualHistory_passt σ) (actualHistory_provenance σ)
      (fun _ _ _ _ _ _ _ => rfl) hm rfl hv⟩

/-- T10's extra question changes the answer world, even for a good binding.
    Thus its hlink cannot be a generic consequence of machine recording. -/
theorem recorded_key_not_twice (σ : World decl) :
    ¬ (∀ (a : decl.Ax) (τ : World decl) (ρ : Env decl (decl.aparams a))
        (x : World decl × Int),
      (⟨a, τ, ρ, x⟩ : AxEintrag decl) ∈ actualHistory σ →
      decl.axHerkunft a = some AxOrigin.software →
      traceOracle.wirkt a (τ.fragt (.inl a)) ρ = x) := by
  intro h
  have he := h () (σ.fragt (.inl ())) (rho true)
    (traceOracle.wirkt () (σ.fragt (.inl ())) (rho true))
    (by simp only [actualHistory, List.mem_singleton]) rfl
  have hn := congrArg (fun x : World decl × Int => x.1.spur.length) he
  change (σ.spur.length + 1) + 1 = σ.spur.length + 1 at hn
  omega

/-- Q is independent data in Einheit, not computed from the interface post. -/
def falseQUnit : Einheit decl :=
  { unit with Q := fun _ _ _ => false }

theorem foreign_falseQ : ForeignPflicht falseQUnit traceOracle [] where
  vertrag := by
    intro a hsw σ ρ hpre v hv
    rfl
  dekodiert := by
    intro a hsw σ ρ
    change some (Sum.inl ()) ≠ none
    intro h
    cases h
  klauseln := by
    intro n
    exact Fin.elim0 n
  anbieter := providerRealisiert_nil traceOracle

/-- A nontrivial passing pre and a proved interface post do not imply Q.
    This is precisely the hdeckt obligation in qAmDatensatz_of_foreign. -/
theorem software_post_does_not_imply_Q (σ : World decl) :
    AxVor falseQUnit.P.axVertrag () σ (rho true) ∧
    AxNach falseQUnit.P.axVertrag () σ (rho true) σ () ∧
    falseQUnit.Q () σ () = false :=
  ⟨pre_true σ, rfl, rfl⟩

end CallSiteBlocker

/-- The run duty is conditional on binding evidence; it cannot supply that
    evidence for the actual oracle of a hardware-only goal premise. -/
theorem callSitePflicht_of_no_foreign {D : Deklaration} [DecidableEq D.Fn]
    (E : Einheit D)
    (h : ∀ (O : Orakel D) (H : List (BoundaryRecord D)), ¬ ForeignPflicht E O H) :
    CallSitePflicht E := by
  intro O H hh hf
  exact False.elim (h O H hf)

end Gabbro.Grammatik
