/-
  File:      Grammatik/Zielsatz/Ideal/Prototyp/StepEnd.lean
  Subject:   PROTOTYPE of S7: the COMMIT steps that end a multi-step unit -- release of a lock, unmask, end of the
             handler. Here `I` takes the WHOLE unit at once, from the memory the ideal run has at this moment and
             with all answers the unit received; the replay shows it ends where the implementation is.
-/
module

public import Grammatik.Zielsatz.Ideal.Prototyp.StepCommit

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz.Ideal.Prototyp

/-- The generic end of a thread unit: thread `t` leaves its unit with carriers `K`; `I` writes the memory `m'` of
    the whole body, which agrees with the implementation on `K` and with the old ideal memory elsewhere. -/
theorem sim_unitEnd {P : Prog} {s s' : S} {i i' : IS} {pa : Ctx → List Int} {t : Fin 2} {m' : Mem}
    (hD : Disc P) (hR : R P s i pa)
    (hA : Agree (CurK P t (s.th t)) m' s.mem) (hout : ∀ l, ¬ CurK P t (s.th t) l → m' l = i.mem l)
    (hsth : s'.th = upd s.th t { s.th t with cur := none }) (hsm : s'.mem = s.mem) (hshd : s'.hd = s.hd)
    (hsam : s'.am = s.am)
    (hsmask : (∃ r, (s.th t).cur = some (.mk r)) ∨ s'.mask = s.mask)
    (hsown : ∀ k, (∀ r, (s.th t).cur ≠ some (.lk k r)) → s'.owner k = s.owner k)
    (hith : i'.th = upd i.th t ⟨(s.th t).prog, (s.th t).regs, (s.th t).view, (s.th t).lent⟩) (him : i'.mem = m')
    (hilv : i'.lview = s'.lview) (hilvk : ∀ k, (∀ r, (s.th t).cur ≠ some (.lk k r)) → i'.lview k = i.lview k)
    (hiam : i'.am = i.am) (hsuf : (i.th t).prog <:+ P.thread t → (s.th t).prog <:+ P.thread t) :
    R P s' i' (upd pa (.thr t) []) := by
  have hagI : ∀ K : Nat → Prop, (∀ l, K l → ¬ CurK P t (s.th t) l) → Agree K i.mem i'.mem :=
    fun K hK l hl => by rw [him, hout l (hK l hl)]
  have hnotlk : ∀ u, u ≠ t → ∀ k r, (s.th u).cur = some (.lk k r) → ∀ r', (s.th t).cur ≠ some (.lk k r') :=
    fun u hut k r hc r' hc' => by
      have hu := hR.thr u; simp only [ThR, hc] at hu
      have ht := hR.thr t; simp only [ThR, hc'] at ht
      obtain ⟨_, _, _, _, _, _, ho⟩ := hu
      obtain ⟨_, _, _, _, _, _, ho'⟩ := ht
      rw [ho] at ho'; cases ho'; exact hut rfl
  refine ⟨fun v => ?_, ?_, ?_, fun l hl hh hlt => ?_, hilv, ?_, fun v x hx => ?_, fun v => ?_, fun v => ?_⟩
  · by_cases hvt : v = t
    · subst hvt
      simp only [ThR, hsth, upd_same, hith]
      exact ⟨trivial, trivial⟩
    · rw [upd_ne _ _ (ctx_thr_ne hvt)]
      refine thR_frame (hR.thr v) (by rw [hsth, upd_ne _ _ hvt]) (by rw [hith, upd_ne _ _ hvt])
        (by rw [hsm]; exact fun _ _ => rfl)
        (hagI _ (fun l hl hlt => acc_disj_thr hvt (hR.thr v) (hR.thr t) hl hlt))
        (fun k r hc => ⟨hilvk k (hnotlk v hvt k r hc), hsown k (hnotlk v hvt k r hc)⟩) (fun r hc => ?_)
      have h0 := (thR_mk (hR.thr v) hc).1
      refine ⟨?_, hshd⟩
      rcases hsmask with ⟨r', hc'⟩ | hm
      · exact absurd ((thR_mk (hR.thr t) hc').1.trans h0.symm) (Ne.symm hvt)
      · exact hm
  · rw [upd_ne _ _ (by intro h; cases h)]
    refine hdR_frame hD.2 hR.hd hshd (fun hn => ⟨by rw [hsm]; exact fun _ _ => rfl,
      hagI _ (fun l hl hlt => acc_disj_hd (hR.thr t) hlt (by
        unfold HdK; cases hc : s.hd with
        | none => exact absurd hc hn
        | some _ => simpa using hl)), ?_⟩)
    rcases hsmask with ⟨r', hc'⟩ | hm
    · exact absurd (thR_mk (hR.thr t) hc').2.2 hn
    · exact hm
  · rw [upd_ne _ _ (by intro h; cases h)]; exact hR.dma
  · rw [hsm, him]
    by_cases hK : CurK P t (s.th t) l
    · exact hA l hK
    · rw [hout l hK]
      refine hR.mem l (fun v hv => ?_) (by unfold HdK at hh ⊢; rw [hshd] at hh; exact hh) (fun v => ?_)
      · by_cases hvt : v = t
        · subst hvt; exact hK hv
        · exact hl v (by rw [hsth, upd_ne _ _ hvt]; exact hv)
      · have := hlt v
        by_cases hvt : v = t
        · subst hvt; rw [hsth, upd_same] at this; exact this
        · rwa [hsth, upd_ne _ _ hvt] at this
  · rw [hiam, hsam]; exact hR.am
  · by_cases hvt : v = t
    · subst hvt; rw [hsth, upd_same] at hx; exact hR.lentOwn v x hx
    · rw [hsth, upd_ne _ _ hvt] at hx; exact hR.lentOwn v x hx
  · by_cases hvt : v = t
    · subst hvt; rw [hsth, upd_same]; exact hR.prog v
    · rw [hsth, upd_ne _ _ hvt]; exact hR.prog v
  · by_cases hvt : v = t
    · subst hvt; rw [hith, upd_same]; exact hsuf (hR.suf v)
    · rw [hith, upd_ne _ _ hvt]; exact hR.suf v

/-- Release: `I` takes the whole lock section. -/
theorem sim_rel {P : Prog} {s : S} {i : IS} {pa : Ctx → List Int} {t : Fin 2} {k : Nat} (hD : Disc P)
    (hR : R P s i pa) (hc : (s.th t).cur = some (.lk k [])) :
    ∃ w i', IStep P i (.thr t) (pa (.thr t) ++ (none : Option Int).toList) w i' ∧
      R P { (s.setTh t { s.th t with cur := none }) with
        owner := upd s.owner k none, lview := upd s.lview k (s.th t).view } i' (upd pa (.thr t) []) := by
  have ht := hR.thr t
  simp only [ThR, hc] at ht
  obtain ⟨body, hp, hok, hrp, hv, hl, ho⟩ := ht
  obtain ⟨m', he, hA, hout⟩ := replay_done hrp hok
  simp only [Option.toList, List.append_nil]
  refine ⟨0, _, IStep.lock hp he, sim_unitEnd hD hR (by rw [curK_lk hc]; exact hA)
    (by rw [curK_lk hc]; exact hout) rfl rfl rfl rfl (Or.inr rfl) (fun k' hk => upd_ne _ _ (fun he => hk [] (by
      rw [he]; exact hc))) (by simp only [IS.setTh, hv, hl]) rfl ?_ (fun k' hk => upd_ne _ _ (fun he => hk []
      (by rw [he]; exact hc))) rfl (fun h => by rw [hp] at h; exact List.IsSuffix.trans (List.suffix_cons _ _) h)⟩
  show upd i.lview k _ = upd s.lview k _
  rw [hR.lview, hv, hR.lview]

/-- Unmask: `I` takes the whole masked section. -/
theorem sim_umsk {P : Prog} {s : S} {i : IS} {pa : Ctx → List Int} (hD : Disc P) (hR : R P s i pa)
    (hc : (s.th 0).cur = some (.mk [])) :
    ∃ w i', IStep P i (.thr 0) (pa (.thr 0) ++ (none : Option Int).toList) w i' ∧
      R P { (s.setTh 0 { s.th 0 with cur := none }) with mask := false } i' (upd pa (.thr 0) []) := by
  have ht := hR.thr 0
  simp only [ThR, hc] at ht
  obtain ⟨_, body, hp, hok, hrp, hv, hl, _, _⟩ := ht
  obtain ⟨m', he, hA, hout⟩ := replay_done hrp hok
  simp only [Option.toList, List.append_nil]
  refine ⟨0, _, IStep.masked hp he, sim_unitEnd hD hR (by rw [curK_mk hc]; exact hA)
    (by rw [curK_mk hc]; exact hout) rfl rfl rfl rfl (Or.inl ⟨[], hc⟩) (fun _ _ => rfl)
    (by simp only [IS.setTh, hv, hl]) rfl hR.lview (fun _ _ => rfl) rfl
    (fun h => by rw [hp] at h; exact List.IsSuffix.trans (List.suffix_cons _ _) h)⟩

/-- End of the handler: `I` takes the whole handler run. -/
theorem sim_hEnd {P : Prog} {s : S} {i : IS} {pa : Ctx → List Int} {ρ : Regs} (hD : Disc P) (hR : R P s i pa)
    (hhd : s.hd = some ([], ρ)) :
    ∃ w i', IStep P i .irq (pa .irq ++ (none : Option Int).toList) w i' ∧
      R P { s with hd := none, mask := false } i' (upd pa .irq []) := by
  have hh := hR.hd
  simp only [HdR, hhd] at hh
  obtain ⟨m', he, hA, hout⟩ := replay_done hh.1 hD.2
  simp only [Option.toList, List.append_nil]
  have hHdK : HdK P s = KIrq P := by simp [HdK, hhd]
  have hagI : ∀ u, Agree (CurK P u (s.th u)) i.mem m' := fun u l hl =>
    (hout l (fun hi => acc_disj_hd (hR.thr u) hl (by rw [hHdK]; exact hi))).symm
  refine ⟨0, _, IStep.handler he, fun u => ?_, ?_, ?_, fun l hl _ hlt => ?_, hR.lview, hR.am, hR.lentOwn,
    hR.prog, hR.suf⟩
  · rw [upd_ne _ _ (by intro h; cases h)]
    refine thR_frame (hR.thr u) rfl rfl (fun _ _ => rfl) (hagI u) (fun _ _ _ => ⟨rfl, rfl⟩) (fun r hc => ?_)
    rw [(thR_mk (hR.thr u) hc).2.2] at hhd; cases hhd
  · simp only [HdR, upd_same]
  · rw [upd_ne _ _ (by intro h; cases h)]; exact hR.dma
  · show m' l = s.mem l
    by_cases hi : KIrq P l
    · exact hA l hi
    · rw [hout l hi]; exact hR.mem l hl (by rw [hHdK]; exact hi) hlt

end Gabbro.Grammatik.Zielsatz.Ideal.Prototyp
