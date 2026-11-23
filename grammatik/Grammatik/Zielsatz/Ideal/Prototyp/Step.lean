/-
  File:      Grammatik/Zielsatz/Ideal/Prototyp/Step.lean
  Subject:   PROTOTYPE of S7: the step theorem of the refinement -- every implementation step is a STUTTER of `I`
             (the stepping context is inside its unit afterwards, or it is the device) or a COMMIT, one step of
             `I` by the same context with all answers of the unit -- and the bound on stutter.

  `Rest s c` counts the implementation steps context `c` still needs to finish its running unit (0 between
  units). A step of `c` is a commit exactly when `Rest` of `c` is 0 afterwards; a stutter step of `c` lowers the
  potential `psi` (`Rest`, or `maxLen P + 2` between units), steps of other contexts leave it alone, and `psi` is
  at most `maxLen P + 2`: between two ideal steps of a context, the context takes at most `maxLen P + 1`
  implementation steps (`Run.lean`). `maxLen P` is the longest body of the program text.
-/
module

public import Grammatik.Zielsatz.Ideal.Prototyp.StepEnd

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz.Ideal.Prototyp

/-- The implementation steps context `c` still needs to finish its running unit. -/
def Rest (s : S) : Ctx → Nat
  | .thr t => match (s.th t).cur with
    | some (.lk _ r) => r.length + 1
    | some (.mk r) => r.length + 1
    | none => 0
  | .irq => match s.hd with
    | some (r, _) => r.length + 1
    | none => 0
  | .dma => 0

/-- The body length of a unit. -/
def segLen : Seg → Nat
  | .lock _ b => b.length
  | .masked b => b.length
  | .atom _ _ => 0
  | .lend _ => 0
  | .takeBack _ => 0
  | .set _ _ => 0

/-- The longest body of a thread program. -/
def maxSeg (us : List Seg) : Nat := us.foldr (fun u n => max (segLen u) n) 0

/-- The longest body of the program text, the handler included. -/
def maxLen (P : Prog) : Nat := max P.handler.length (max (maxSeg (P.thread 0)) (maxSeg (P.thread 1)))

theorem segLen_le_maxSeg : ∀ {us : List Seg} {u : Seg}, u ∈ us → segLen u ≤ maxSeg us
  | _ :: _, _, .head _ => Nat.le_max_left _ _
  | _ :: _, _, .tail _ h => Nat.le_trans (segLen_le_maxSeg h) (Nat.le_max_right _ _)

theorem maxSeg_le_maxLen (P : Prog) (t : Fin 2) : maxSeg (P.thread t) ≤ maxLen P := by
  rcases t with ⟨_ | _ | n, hn⟩
  · exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  · exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  · omega

theorem replay_len {K : Nat → Prop} {body rest : List Op} {pa : List Int} {ρ₀ ρ : Regs} {mI mS : Mem}
    (h : Replay K body rest pa ρ₀ mI ρ mS) : rest.length ≤ body.length := by
  obtain ⟨done, hb, _⟩ := h
  rw [hb, List.length_append]; omega

/-- In the relation, every running unit needs at most `maxLen P + 1` more steps. -/
theorem rest_le {P : Prog} {s : S} {i : IS} {pa : Ctx → List Int} (hR : R P s i pa) (c : Ctx) :
    Rest s c ≤ maxLen P + 1 := by
  cases c with
  | thr t =>
      have ht := hR.thr t
      have hsuf := hR.suf t
      unfold Rest
      unfold ThR at ht
      cases hc : (s.th t).cur with
      | none => simp [hc]
      | some cu =>
          cases cu with
          | lk k rest =>
              simp only [hc] at ht ⊢
              obtain ⟨body, hp, _, hrp, _⟩ := ht
              rw [hp] at hsuf
              have h1 := segLen_le_maxSeg (hsuf.subset List.mem_cons_self)
              have h2 := maxSeg_le_maxLen P t
              have h3 := replay_len hrp
              simp only [segLen] at h1
              omega
          | mk rest =>
              simp only [hc] at ht ⊢
              obtain ⟨_, body, hp, _, hrp, _⟩ := ht
              rw [hp] at hsuf
              have h1 := segLen_le_maxSeg (hsuf.subset List.mem_cons_self)
              have h2 := maxSeg_le_maxLen P t
              have h3 := replay_len hrp
              simp only [segLen] at h1
              omega
  | irq =>
      have hh := hR.hd
      unfold Rest
      unfold HdR at hh
      cases hc : s.hd with
      | none => simp
      | some x =>
          obtain ⟨rest, ρ⟩ := x
          simp only [hc] at hh ⊢
          have h3 := replay_len hh.1
          have : P.handler.length ≤ maxLen P := Nat.le_max_left _ _
          omega
  | dma => simp [Rest]

/-- One step of the refinement, from a pair (ideal state, pending answers) to the next. A stutter leaves `I` and
    makes the answer pending; a commit is one step of `I` by the same context with all pending answers. -/
def Folgt (P : Prog) (s' : S) (c : Ctx) (a : Option Int) (x y : IS × (Ctx → List Int)) : Prop :=
  ((c = .dma ∨ Rest s' c ≠ 0) ∧ y.1 = x.1 ∧ y.2 = upd x.2 c (x.2 c ++ a.toList)) ∨
  (c ≠ .dma ∧ Rest s' c = 0 ∧ ∃ w, IStep P x.1 c (x.2 c ++ a.toList) w y.1 ∧ y.2 = upd x.2 c [])

/-- **The step theorem.** In the relation, every implementation step is a stutter or a commit of `I`, and the
    relation holds afterwards. -/
theorem sim_step {P : Prog} {s s' : S} {c : Ctx} {a : Option Int} {x : IS × (Ctx → List Int)} (hD : Disc P)
    (hR : R P s x.1 x.2) (h : SStep P s c a s') : ∃ y, Folgt P s' c a x y ∧ R P s' y.1 y.2 := by
  obtain ⟨i, pa⟩ := x
  have stut : ∀ (hc : c = .dma ∨ Rest s' c ≠ 0), R P s' i (upd pa c (pa c ++ a.toList)) →
      ∃ y, Folgt P s' c a (i, pa) y ∧ R P s' y.1 y.2 :=
    fun hc hR' => ⟨(i, upd pa c (pa c ++ a.toList)), Or.inl ⟨hc, rfl, rfl⟩, hR'⟩
  have comm : c ≠ .dma → Rest s' c = 0 →
      (∃ w i', IStep P i c (pa c ++ a.toList) w i' ∧ R P s' i' (upd pa c [])) →
      ∃ y, Folgt P s' c a (i, pa) y ∧ R P s' y.1 y.2 :=
    fun hd hc ⟨w, i', hs, hR'⟩ => ⟨(i', upd pa c []), Or.inr ⟨hd, hc, w, hs, rfl⟩, hR'⟩
  cases h with
  | acq hc hp ho _ => exact stut (Or.inr (by simp [Rest, S.setTh])) (sim_acq hD hR hc hp ho)
  | lkOp hc _ hs => exact stut (Or.inr (by simp [Rest, S.setTh])) (sim_lkOp hD hR hc hs)
  | rel hc _ => exact comm (by simp) (by simp [Rest, S.setTh]) (sim_rel hD hR hc)
  | msk hc hp hhd => exact stut (Or.inr (by simp [Rest, S.setTh])) (sim_msk hD hR hc hp hhd)
  | mkOp hc _ hs => exact stut (Or.inr (by simp [Rest, S.setTh])) (sim_mkOp hD hR hc hs)
  | umsk hc _ => exact comm (by simp) (by simp [Rest, S.setTh]) (sim_umsk hD hR hc)
  | atom hc hp _ ha => exact comm (by simp) (by simp [Rest, S.setTh, hc]) (sim_atom hD hR hc hp ha)
  | lend hc hp _ => exact comm (by simp) (by simp [Rest, S.setTh, hc]) (sim_lend hD hR hc hp)
  | take hc hp _ => exact comm (by simp) (by simp [Rest, S.setTh, hc]) (sim_take hD hR hc hp)
  | set hc hp _ => exact comm (by simp) (by simp [Rest, S.setTh, hc]) (sim_set hD hR hc hp)
  | irqIn hhd hm => exact stut (Or.inr (by simp [Rest])) (sim_irqIn hR hhd hm)
  | hOp hhd hs => exact stut (Or.inr (by simp [Rest])) (sim_hOp hD hR hhd hs)
  | hEnd hhd => exact comm (by simp) (by simp [Rest]) (sim_hEnd hD hR hhd)
  | dma hx => exact stut (Or.inl rfl) (sim_dma hD hR hx)

/-! ## Stutter is bounded -/

/-- The potential of context `c`: its remaining steps inside a unit, `maxLen P + 2` between units. -/
def psi (P : Prog) (s : S) (c : Ctx) : Nat := if Rest s c = 0 then maxLen P + 2 else Rest s c

/-- A step of one context leaves the remaining steps of every other context unchanged. -/
theorem rest_other {P : Prog} {s s' : S} {c c' : Ctx} {a : Option Int} (h : SStep P s c a s') (hc : c' ≠ c) :
    Rest s' c' = Rest s c' := by
  cases h <;> cases c' <;> first
    | rfl
    | (rename_i u; simp only [Rest, S.setTh]; rw [upd_ne _ _ (fun he => hc (by rw [he]))])
    | exact absurd rfl hc

/-- Every step of `c` starts a unit, advances inside it, finishes it, or is the device. -/
theorem rest_step {P : Prog} {s s' : S} {c : Ctx} {a : Option Int} (h : SStep P s c a s') :
    Rest s c = 0 ∨ Rest s' c < Rest s c ∨ Rest s' c = 0 ∨ c = .dma := by
  cases h with
  | acq hc => exact Or.inl (by simp [Rest, hc])
  | lkOp hc => exact Or.inr (Or.inl (by simp [Rest, S.setTh, hc]))
  | rel => exact Or.inr (Or.inr (Or.inl (by simp [Rest, S.setTh])))
  | msk hc => exact Or.inl (by simp [Rest, hc])
  | mkOp hc => exact Or.inr (Or.inl (by simp [Rest, S.setTh, hc]))
  | umsk => exact Or.inr (Or.inr (Or.inl (by simp [Rest, S.setTh])))
  | atom hc => exact Or.inr (Or.inr (Or.inl (by simp [Rest, S.setTh, hc])))
  | lend hc => exact Or.inr (Or.inr (Or.inl (by simp [Rest, S.setTh, hc])))
  | take hc => exact Or.inr (Or.inr (Or.inl (by simp [Rest, S.setTh, hc])))
  | set hc => exact Or.inr (Or.inr (Or.inl (by simp [Rest, S.setTh, hc])))
  | irqIn hhd => exact Or.inl (by simp [Rest, hhd])
  | hOp hhd => exact Or.inr (Or.inl (by simp [Rest, hhd]))
  | hEnd => exact Or.inr (Or.inr (Or.inl (by simp [Rest])))
  | dma => exact Or.inr (Or.inr (Or.inr rfl))

/-- A stutter step of `c` lowers its potential (the relation afterwards bounds the new unit). -/
theorem psi_lt {P : Prog} {s s' : S} {c : Ctx} {a : Option Int} {i : IS} {pa : Ctx → List Int}
    (h : SStep P s c a s') (hR' : R P s' i pa) (hd : c ≠ .dma) (hst : Rest s' c ≠ 0) : psi P s' c < psi P s c := by
  have hle := rest_le hR' c
  unfold psi
  rcases rest_step h with h0 | hlt | h0 | hc
  · rw [ite_eq_left h0, ite_eq_right hst]; omega
  · rw [ite_eq_right hst, ite_eq_right (by omega)]; exact hlt
  · exact absurd h0 hst
  · exact absurd hc hd

theorem psi_le {P : Prog} {s : S} {i : IS} {pa : Ctx → List Int} (hR : R P s i pa) (c : Ctx) :
    psi P s c ≤ maxLen P + 2 := by
  have := rest_le hR c
  unfold psi; split <;> omega

theorem psi_pos (P : Prog) (s : S) (c : Ctx) : 1 ≤ psi P s c := by
  unfold psi; split <;> omega

end Gabbro.Grammatik.Zielsatz.Ideal.Prototyp
