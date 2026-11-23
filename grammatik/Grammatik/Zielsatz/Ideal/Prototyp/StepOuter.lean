/-
  File:      Grammatik/Zielsatz/Ideal/Prototyp/StepOuter.lean
  Subject:   PROTOTYPE of S7: the remaining STUTTER steps -- masking (entering a masked section), the interrupt
             entering (it may preempt a lock section of thread 0), one handler operation, and the device writing a
             lent buffer (the arbitrary-change rely of the outside, §4).
-/
module

public import Grammatik.Zielsatz.Ideal.Prototyp.StepEnter

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz.Ideal.Prototyp

/-- A thread holding a mask location is inside its masked section, so the mask is set. -/
theorem curK_irq_mask {P : Prog} {s : S} {i : IS} {pa : List Int} {t : Fin 2} {l : Nat} (h : ThR P s i pa t)
    (hl : CurK P t (s.th t) l) (hi : P.prot l = .irq) : s.mask = true := by
  unfold ThR at h
  unfold CurK at hl
  cases hc : (s.th t).cur with
  | none => simp only [hc] at hl
  | some cu =>
      cases cu with
      | lk k rest =>
          simp only [hc, KLk] at hl
          rcases hl with hl | ⟨hl, _⟩ <;> (rw [hi] at hl; cases hl)
      | mk rest =>
          simp only [hc] at h
          obtain ⟨_, _, _, _, _, _, _, hm, _⟩ := h; exact hm

/-- Thread 1 is never inside a masked section, and a masking thread 0 sees no running handler. -/
theorem thR_mk {P : Prog} {s : S} {i : IS} {pa : List Int} {t : Fin 2} {r : List Op} (h : ThR P s i pa t)
    (hc : (s.th t).cur = some (.mk r)) : t = 0 ∧ s.mask = true ∧ s.hd = none := by
  simp only [ThR, hc] at h
  obtain ⟨h0, _, _, _, _, _, _, hm, hhd⟩ := h
  exact ⟨h0, hm, hhd⟩

/-- Entering a masked section (thread 0). -/
theorem sim_msk {P : Prog} {s : S} {i : IS} {pa : Ctx → List Int} {body : List Op} {ps : List Seg}
    (hD : Disc P) (hR : R P s i pa) (hc : (s.th 0).cur = none) (hp : (s.th 0).prog = .masked body :: ps)
    (hhd : s.hd = none) :
    R P { (s.setTh 0 { s.th 0 with prog := ps, cur := some (.mk body) }) with mask := true } i
      (upd pa (.thr 0) (pa (.thr 0) ++ (none : Option Int).toList)) := by
  simp only [Option.toList, List.append_nil, upd_eq_self]
  have ht := hR.thr 0
  simp only [ThR, hc] at ht
  obtain ⟨hit, hpa⟩ := ht
  have hpo := hR.prog 0
  rw [hp] at hpo
  have hfree : ∀ l, KMk P 0 (s.th 0).lent l →
      (∀ u, ¬ CurK P u (s.th u) l) ∧ ¬ HdK P s l ∧ ∀ u, (s.th u).lent l = false := by
    intro l hl
    refine ⟨fun u hu => ?_, fun hh => ?_, fun u => ?_⟩
    · by_cases hut : u = 0
      · subst hut; exact curK_none hc l hu
      · rcases curK_prot (hR.thr u) hu with ⟨k', hk', _⟩ | ho' | ⟨_, hu0, _⟩ <;> rcases hl with hl | ⟨hl, _⟩
        · rw [hl] at hk'; cases hk'
        · rw [hl] at hk'; cases hk'
        · rw [hl] at ho'; cases ho'
        · rw [hl] at ho'; cases ho'; exact hut rfl
        · exact hut hu0
        · exact hut hu0
    · have := (hdK_prot hh).2; exact this hhd
    · cases hlu : (s.th u).lent l
      · rfl
      · have hpu := hR.lentOwn u l hlu
        rcases hl with hl | ⟨hl, hlt⟩
        · rw [hl] at hpu; cases hpu
        · rw [hl] at hpu; cases hpu; rw [hlt] at hlu; cases hlu
  refine ⟨fun u => ?_, ?_, hR.dma, fun l hl hh hlt => ?_, hR.lview, hR.am, fun u x hx => ?_, fun u => ?_, hR.suf⟩
  · by_cases hut : u = 0
    · subst hut
      simp only [ThR, S.setTh, upd_same]
      refine ⟨trivial, body, by rw [hit]; exact hp, hpo.2.1, ?_, by rw [hit], by rw [hit], trivial, hhd⟩
      rw [hpa, hit]
      exact replay_start (agree_free hR hfree)
    · refine thR_frame (hR.thr u) (by simp [S.setTh, upd_ne _ _ hut]) rfl (fun _ _ => rfl) (fun _ _ => rfl)
        (fun _ _ _ => ⟨rfl, rfl⟩) (fun r hc' => absurd (thR_mk (hR.thr u) hc').1 hut)
  · exact hdR_frame hD.2 hR.hd rfl (fun hn => absurd hhd hn)
  · refine hR.mem l (fun u hu => ?_) hh (fun u => ?_)
    · by_cases hut : u = 0
      · subst hut; exact curK_none hc l hu
      · exact hl u (by simp only [S.setTh, upd_ne _ _ hut]; exact hu)
    · have := hlt u
      by_cases hut : u = 0
      · subst hut; simpa [S.setTh] using this
      · simpa [S.setTh, upd_ne _ _ hut] using this
  · by_cases hut : u = 0
    · subst hut; simp only [S.setTh, upd_same] at hx; exact hR.lentOwn 0 x hx
    · simp only [S.setTh, upd_ne _ _ hut] at hx; exact hR.lentOwn u x hx
  · by_cases hut : u = 0
    · subst hut; simp only [S.setTh, upd_same]; exact hpo.2.2
    · simp only [S.setTh, upd_ne _ _ hut]; exact hR.prog u

/-- The interrupt enters; it may preempt a running lock section of thread 0. -/
theorem sim_irqIn {P : Prog} {s : S} {i : IS} {pa : Ctx → List Int} (hR : R P s i pa)
    (hhd : s.hd = none) (hm : s.mask = false) :
    R P { s with hd := some (P.handler, fun _ => 0), mask := true } i
      (upd pa .irq (pa .irq ++ (none : Option Int).toList)) := by
  simp only [Option.toList, List.append_nil, upd_eq_self]
  have hfree : ∀ l, KIrq P l → (∀ u, ¬ CurK P u (s.th u) l) ∧ ¬ HdK P s l ∧ ∀ u, (s.th u).lent l = false := by
    intro l hl
    refine ⟨fun u hu => ?_, fun hh => (hdK_prot hh).2 hhd, fun u => ?_⟩
    · rw [curK_irq_mask (hR.thr u) hu hl] at hm; cases hm
    · cases hlu : (s.th u).lent l
      · rfl
      · have := hR.lentOwn u l hlu; unfold KIrq at hl; rw [hl] at this; cases this
  have hpa : pa .irq = [] := by have := hR.hd; simp only [HdR, hhd] at this; exact this
  refine ⟨fun u => ?_, ?_, hR.dma, fun l hl hh hlt => ?_, hR.lview, hR.am, hR.lentOwn, hR.prog, hR.suf⟩
  · refine thR_frame (hR.thr u) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => ⟨rfl, rfl⟩)
      (fun r hc' => ?_)
    rw [(thR_mk (hR.thr u) hc').2.1] at hm; cases hm
  · simp only [HdR]
    rw [hpa]
    exact ⟨replay_start (agree_free hR hfree), trivial⟩
  · exact hR.mem l hl (fun h => by simp [HdK, hhd] at h) hlt

/-- One operation of the running handler. -/
theorem sim_hOp {P : Prog} {s : S} {i : IS} {pa : Ctx → List Int} {op : Op} {rest : List Op} {ρ ρ' : Regs}
    {a : Option Int} {m' : Mem} (hD : Disc P) (hR : R P s i pa) (hhd : s.hd = some (op :: rest, ρ))
    (hstep : opStep op a (ρ, s.mem) = some (ρ', m')) :
    R P { s with hd := some (rest, ρ'), mem := m' } i (upd pa .irq (pa .irq ++ a.toList)) := by
  have hh := hR.hd
  simp only [HdR, hhd] at hh
  obtain ⟨hrp, hmask⟩ := hh
  obtain ⟨hrp', hout⟩ := replay_step hrp (hD.2 op (replay_mem_head hrp)) hstep
  have hHdK : HdK P s = KIrq P := by simp [HdK, hhd]
  have hdisj : ∀ u, Agree (CurK P u (s.th u)) s.mem m' := fun u l hl =>
    (hout l (fun hi => acc_disj_hd (hR.thr u) hl (by rw [hHdK]; exact hi))).symm
  refine ⟨fun u => ?_, ?_, ?_, fun l hl hh hlt => ?_, hR.lview, hR.am, hR.lentOwn, hR.prog, hR.suf⟩
  · rw [upd_ne _ _ (by intro h; cases h)]
    refine thR_frame (hR.thr u) rfl rfl (hdisj u) (fun _ _ => rfl) (fun _ _ _ => ⟨rfl, rfl⟩) (fun r hc' => ?_)
    rw [(thR_mk (hR.thr u) hc').2.2] at hhd; cases hhd
  · simp only [HdR, upd_same]
    exact ⟨hrp', hmask⟩
  · rw [upd_ne _ _ (by intro h; cases h)]; exact hR.dma
  · have hi : ¬ KIrq P l := fun hi => hh (by simp [HdK]; exact hi)
    show i.mem l = m' l
    rw [hout l hi]
    exact hR.mem l hl (by rw [hHdK]; exact hi) hlt

/-- The device writes a lent buffer: no running unit holds it, so nothing the relation speaks of changes. -/
theorem sim_dma {P : Prog} {s : S} {i : IS} {pa : Ctx → List Int} {t : Fin 2} {x : Nat} {v : Int}
    (hD : Disc P) (hR : R P s i pa) (hx : (s.th t).lent x = true) :
    R P { s with mem := upd s.mem x v } i (upd pa .dma (pa .dma ++ (none : Option Int).toList)) := by
  simp only [Option.toList, List.append_nil, upd_eq_self]
  have hne : ∀ l, l ≠ x → upd s.mem x v l = s.mem l := fun l h => upd_ne _ _ h
  have hdisj : ∀ u, Agree (CurK P u (s.th u)) s.mem (upd s.mem x v) := fun u l hl =>
    (hne l (fun he => lent_not_curK hR.lentOwn (hR.thr u) hx (he ▸ hl))).symm
  refine ⟨fun u => ?_, ?_, hR.dma, fun l hl hh hlt => ?_, hR.lview, hR.am, hR.lentOwn, hR.prog, hR.suf⟩
  · exact thR_frame (hR.thr u) rfl rfl (hdisj u) (fun _ _ => rfl) (fun _ _ _ => ⟨rfl, rfl⟩)
      (fun _ _ => ⟨rfl, rfl⟩)
  · refine hdR_frame hD.2 hR.hd rfl (fun hn => ⟨fun l hl => (hne l (fun he => ?_)).symm, fun _ _ => rfl, rfl⟩)
    subst he
    have := hR.lentOwn t l hx; unfold KIrq at hl; rw [hl] at this; cases this
  · have hlx : l ≠ x := fun he => by have := hlt t; rw [he, hx] at this; cases this
    show i.mem l = upd s.mem x v l
    rw [hne l hlx]
    exact hR.mem l hl hh hlt

end Gabbro.Grammatik.Zielsatz.Ideal.Prototyp
