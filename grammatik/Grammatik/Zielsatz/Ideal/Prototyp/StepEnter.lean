/-
  File:      Grammatik/Zielsatz/Ideal/Prototyp/StepEnter.lean
  Subject:   PROTOTYPE of S7: the STUTTER steps of a thread -- entering a lock or masked section and running one
             body operation. `I` does not move; the answer of the step (if any) becomes pending.
-/
module

public import Grammatik.Zielsatz.Ideal.Prototyp.Sim

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz.Ideal.Prototyp

theorem upd_eq_self {α β : Type} [DecidableEq α] (f : α → β) (a : α) : upd f a (f a) = f := by
  funext x; by_cases h : x = a
  · subst h; simp
  · simp [upd_ne _ _ h]

theorem curK_lk {P : Prog} {t : Fin 2} {th : Th} {k : Nat} {r : List Op} (h : th.cur = some (.lk k r)) :
    CurK P t th = KLk P t k th.lent := by simp [CurK, h]

theorem curK_mk {P : Prog} {t : Fin 2} {th : Th} {r : List Op} (h : th.cur = some (.mk r)) :
    CurK P t th = KMk P t th.lent := by simp [CurK, h]

theorem curK_none {P : Prog} {t : Fin 2} {th : Th} (h : th.cur = none) (l : Nat) : ¬ CurK P t th l := by
  simp [CurK, h]

theorem replay_mem_head {K : Nat → Prop} {body rest : List Op} {op : Op} {pa : List Int} {ρ₀ ρ : Regs}
    {mI mS : Mem} (h : Replay K body (op :: rest) pa ρ₀ mI ρ mS) : op ∈ body := by
  obtain ⟨done, hb, _⟩ := h
  rw [hb]; exact List.mem_append_right _ List.mem_cons_self

theorem ctx_thr_ne {t u : Fin 2} (h : u ≠ t) : Ctx.thr u ≠ Ctx.thr t := fun he => h (Ctx.thr.inj he)

/-- The ideal memory agrees with the implementation on every location that no running unit holds and that is not
    lent. -/
theorem agree_free {P : Prog} {s : S} {i : IS} {pa : Ctx → List Int} (hR : R P s i pa) {K : Nat → Prop}
    (hfree : ∀ l, K l → (∀ t, ¬ CurK P t (s.th t) l) ∧ ¬ HdK P s l ∧ ∀ t, (s.th t).lent l = false) :
    Agree K i.mem s.mem := fun l hl => hR.mem l (hfree l hl).1 (hfree l hl).2.1 (hfree l hl).2.2

/-- Entering a lock section. -/
theorem sim_acq {P : Prog} {s : S} {i : IS} {pa : Ctx → List Int} {t : Fin 2} {k : Nat} {body : List Op}
    {ps : List Seg} (hD : Disc P) (hR : R P s i pa) (hc : (s.th t).cur = none)
    (hp : (s.th t).prog = .lock k body :: ps)
    (ho : s.owner k = none) :
    R P { (s.setTh t ⟨ps, some (.lk k body), (s.th t).regs, vjoin (s.th t).view (s.lview k), (s.th t).lent⟩) with
      owner := upd s.owner k (some t) } i (upd pa (.thr t) (pa (.thr t) ++ (none : Option Int).toList)) := by
  simp only [Option.toList, List.append_nil, upd_eq_self]
  have ht := hR.thr t
  simp only [ThR, hc] at ht
  obtain ⟨hit, hpa⟩ := ht
  have hpo := hR.prog t
  rw [hp] at hpo
  have hfree : ∀ l, KLk P t k (s.th t).lent l →
      (∀ u, ¬ CurK P u (s.th u) l) ∧ ¬ HdK P s l ∧ ∀ u, (s.th u).lent l = false := by
    intro l hl
    refine ⟨fun u hu => ?_, fun hh => ?_, fun u => ?_⟩
    · by_cases hut : u = t
      · subst hut; exact curK_none hc l hu
      · rcases curK_prot (hR.thr u) hu with ⟨k', hk', ho'⟩ | ho' | ⟨hi, _, _⟩ <;> rcases hl with hl | ⟨hl, _⟩
        · rw [hl] at hk'; cases hk'; rw [ho] at ho'; cases ho'
        · rw [hl] at hk'; cases hk'
        · rw [hl] at ho'; cases ho'
        · rw [hl] at ho'; cases ho'; exact hut rfl
        · rw [hl] at hi; cases hi
        · rw [hl] at hi; cases hi
    · have := (hdK_prot hh).1
      rcases hl with hl | ⟨hl, _⟩ <;> (rw [hl] at this; cases this)
    · cases hlu : (s.th u).lent l
      · rfl
      · have hpu := hR.lentOwn u l hlu
        rcases hl with hl | ⟨hl, hlt⟩
        · rw [hl] at hpu; cases hpu
        · rw [hl] at hpu; cases hpu; rw [hlt] at hlu; cases hlu
  refine ⟨fun u => ?_, ?_, hR.dma, fun l hl hh hlt => ?_, hR.lview, hR.am, fun u x hx => ?_, fun u => ?_, hR.suf⟩
  · by_cases hut : u = t
    · subst hut
      simp only [ThR, S.setTh, upd_same]
      refine ⟨body, by rw [hit]; exact hp, hpo.1, ?_, by rw [hit, hR.lview], by rw [hit], by simp⟩
      rw [hpa, hit]
      exact replay_start (agree_free hR hfree)
    · refine thR_frame (hR.thr u) (by simp [S.setTh, upd_ne _ _ hut]) rfl (fun _ _ => rfl) (fun _ _ => rfl)
        (fun k' r hc' => ⟨rfl, ?_⟩) (fun _ _ => ⟨rfl, rfl⟩)
      have hu := hR.thr u
      simp only [ThR, hc'] at hu
      obtain ⟨_, _, _, _, _, _, ho'⟩ := hu
      have hkk : k' ≠ k := fun he => by rw [he, ho] at ho'; cases ho'
      exact upd_ne _ _ hkk
  · exact hdR_frame hD.2 hR.hd rfl (fun _ => ⟨fun _ _ => rfl, fun _ _ => rfl, rfl⟩)
  · refine hR.mem l (fun u hu => ?_) hh (fun u => ?_)
    · by_cases hut : u = t
      · subst hut; exact curK_none hc l hu
      · exact hl u (by simp only [S.setTh, upd_ne _ _ hut]; exact hu)
    · have := hlt u
      by_cases hut : u = t
      · subst hut; simpa [S.setTh] using this
      · simpa [S.setTh, upd_ne _ _ hut] using this
  · by_cases hut : u = t
    · subst hut; simp only [S.setTh, upd_same] at hx; exact hR.lentOwn u x hx
    · simp only [S.setTh, upd_ne _ _ hut] at hx; exact hR.lentOwn u x hx
  · by_cases hut : u = t
    · subst hut; simp only [S.setTh, upd_same]; exact hpo.2
    · simp only [S.setTh, upd_ne _ _ hut]; exact hR.prog u

/-- One body operation of a running thread unit, generic in the kind of unit: the replay advances, the memory
    changes only on the unit's carriers. -/
theorem sim_bodyOp {P : Prog} {s : S} {i : IS} {pa : Ctx → List Int} {t : Fin 2} {cu cu' : Cur} {op : Op}
    {a : Option Int} {ρ' : Regs} {m' : Mem} (hD : Disc P) (hR : R P s i pa) (hc : (s.th t).cur = some cu)
    (hstep : opStep op a ((s.th t).regs, s.mem) = some (ρ', m'))
    (hok : OpOk (CurK P t (s.th t)) op)
    (hown : ThR P s i (pa (.thr t)) t → ThR P { (s.setTh t { s.th t with cur := some cu', regs := ρ' }) with mem := m' } i
        (pa (.thr t) ++ a.toList) t)
    (hK : CurK P t { s.th t with cur := some cu', regs := ρ' } = CurK P t (s.th t))
    (hout : ∀ l, ¬ CurK P t (s.th t) l → m' l = s.mem l)
    (hmk : ∀ r, (s.th t).cur = some (.mk r) → ∃ r', cu' = .mk r') :
    R P { (s.setTh t { s.th t with cur := some cu', regs := ρ' }) with mem := m' } i
      (upd pa (.thr t) (pa (.thr t) ++ a.toList)) := by
  have hdisj : ∀ u, u ≠ t → Agree (CurK P u (s.th u)) s.mem m' := fun u hut l hl =>
    (hout l (fun hlt => acc_disj_thr (Ne.symm hut) (hR.thr t) (hR.thr u) hlt hl)).symm
  refine ⟨fun u => ?_, ?_, ?_, fun l hl hh hlt => ?_, hR.lview, hR.am, fun u x hx => ?_, fun u => ?_, hR.suf⟩
  · by_cases hut : u = t
    · subst hut; simp only [upd_same]; exact hown (hR.thr u)
    · rw [upd_ne _ _ (ctx_thr_ne hut)]
      refine thR_frame (hR.thr u) (by simp [S.setTh, upd_ne _ _ hut]) rfl (hdisj u hut) (fun _ _ => rfl)
        (fun _ _ _ => ⟨rfl, rfl⟩) (fun _ _ => ⟨rfl, rfl⟩)
  · rw [upd_ne _ _ (by intro h; cases h)]
    exact hdR_frame hD.2 hR.hd rfl (fun hn => ⟨fun l hl => (hout l (fun hlt =>
      acc_disj_hd (hR.thr t) hlt (by unfold HdK; cases hhd : s.hd with
        | none => exact absurd hhd hn
        | some _ => simpa using hl))).symm, fun _ _ => rfl, rfl⟩)
  · rw [upd_ne _ _ (by intro h; cases h)]; exact hR.dma
  · have hlt' : ¬ CurK P t (s.th t) l := by
      have := hl t; simp only [S.setTh, upd_same] at this; rwa [hK] at this
    show i.mem l = m' l
    rw [hout l hlt']
    refine hR.mem l (fun u hu => ?_) hh (fun u => ?_)
    · by_cases hut : u = t
      · subst hut; exact hlt' hu
      · exact hl u (by simp only [S.setTh, upd_ne _ _ hut]; exact hu)
    · have := hlt u
      by_cases hut : u = t
      · subst hut; simpa [S.setTh] using this
      · simpa [S.setTh, upd_ne _ _ hut] using this
  · by_cases hut : u = t
    · subst hut; simp only [S.setTh, upd_same] at hx; exact hR.lentOwn u x hx
    · simp only [S.setTh, upd_ne _ _ hut] at hx; exact hR.lentOwn u x hx
  · by_cases hut : u = t
    · subst hut; simp only [S.setTh, upd_same]; exact hR.prog u
    · simp only [S.setTh, upd_ne _ _ hut]; exact hR.prog u

/-- One body operation of a lock section. -/
theorem sim_lkOp {P : Prog} {s : S} {i : IS} {pa : Ctx → List Int} {t : Fin 2} {k : Nat} {op : Op}
    {rest : List Op} {a : Option Int} {ρ' : Regs} {m' : Mem} (hD : Disc P) (hR : R P s i pa)
    (hc : (s.th t).cur = some (.lk k (op :: rest))) (hstep : opStep op a ((s.th t).regs, s.mem) = some (ρ', m')) :
    R P { (s.setTh t { s.th t with cur := some (.lk k rest), regs := ρ' }) with mem := m' } i
      (upd pa (.thr t) (pa (.thr t) ++ a.toList)) := by
  have ht := hR.thr t
  simp only [ThR, hc] at ht
  obtain ⟨body, hp, hok, hrp, hv, hl, ho⟩ := ht
  obtain ⟨hrp', hout⟩ := replay_step hrp (hok op (replay_mem_head hrp)) hstep
  refine sim_bodyOp hD hR hc hstep (by rw [curK_lk hc]; exact hok op (replay_mem_head hrp)) (fun _ => ?_)
    (by simp [CurK, hc]) (by rw [curK_lk hc]; exact hout) (fun r h => by rw [hc] at h; cases h)
  simp only [ThR, S.setTh, upd_same]
  exact ⟨body, hp, hok, hrp', hv, hl, ho⟩

/-- One body operation of a masked section. -/
theorem sim_mkOp {P : Prog} {s : S} {i : IS} {pa : Ctx → List Int} {op : Op}
    {rest : List Op} {a : Option Int} {ρ' : Regs} {m' : Mem} (hD : Disc P) (hR : R P s i pa)
    (hc : (s.th 0).cur = some (.mk (op :: rest))) (hstep : opStep op a ((s.th 0).regs, s.mem) = some (ρ', m')) :
    R P { (s.setTh 0 { s.th 0 with cur := some (.mk rest), regs := ρ' }) with mem := m' } i
      (upd pa (.thr 0) (pa (.thr 0) ++ a.toList)) := by
  have ht := hR.thr 0
  simp only [ThR, hc] at ht
  obtain ⟨h0, body, hp, hok, hrp, hv, hl, hm, hhd⟩ := ht
  obtain ⟨hrp', hout⟩ := replay_step hrp (hok op (replay_mem_head hrp)) hstep
  refine sim_bodyOp hD hR hc hstep (by rw [curK_mk hc]; exact hok op (replay_mem_head hrp)) (fun _ => ?_)
    (by simp [CurK, hc]) (by rw [curK_mk hc]; exact hout) (fun r _ => ⟨rest, rfl⟩)
  simp only [ThR, S.setTh, upd_same]
  exact ⟨h0, body, hp, hok, hrp', hv, hl, hm, hhd⟩

end Gabbro.Grammatik.Zielsatz.Ideal.Prototyp
