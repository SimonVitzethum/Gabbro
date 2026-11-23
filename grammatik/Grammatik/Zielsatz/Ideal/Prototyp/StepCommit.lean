/-
  File:      Grammatik/Zielsatz/Ideal/Prototyp/StepCommit.lean
  Subject:   PROTOTYPE of S7: the COMMIT steps of one-step units -- an atomic operation (the same RC11 step in
             both machines, with the same choice), `lend`, `takeBack` (its answer is the buffer's content, which
             the device may have changed while it was lent) and a local assignment. `I` takes the same unit.
-/
module

public import Grammatik.Zielsatz.Ideal.Prototyp.StepOuter

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz.Ideal.Prototyp

/-- The generic one-step commit: thread `t` is between units before and after; only its thread, the atomic memory
    and (for `takeBack`) one owned location of the ideal memory change. -/
theorem sim_idle {P : Prog} {s s' : S} {i i' : IS} {pa : Ctx → List Int} {t : Fin 2} {X : Th} {u : Seg}
    (hD : Disc P) (hR : R P s i pa) (hc : (s.th t).cur = none) (hX : X.cur = none)
    (hp : (s.th t).prog = u :: X.prog) (hok : ProgOk P t X.lent X.prog)
    (hlo : ∀ x, X.lent x = true → P.prot x = .own t)
    (hsth : s'.th = upd s.th t X) (hsm : s'.mem = s.mem) (hshd : s'.hd = s.hd) (hsmask : s'.mask = s.mask)
    (hsown : s'.owner = s.owner) (hslv : s'.lview = s.lview) (hsam : s'.am = i'.am)
    (hith : i'.th = upd i.th t ⟨X.prog, X.regs, X.view, X.lent⟩) (hilv : i'.lview = i.lview)
    (himem : ∀ l, (i'.mem l = s.mem l ∧ P.prot l = .own t) ∨
      (i'.mem l = i.mem l ∧ (X.lent l = false → (s.th t).lent l = false))) :
    R P s' i' (upd pa (.thr t) []) := by
  have hown : ∀ u l, u ≠ t → CurK P u (s.th u) l → P.prot l ≠ .own t := fun u l hut hl he => by
    rcases curK_prot (hR.thr u) hl with ⟨k, hk, _⟩ | ho | ⟨hi, _, _⟩
    · rw [he] at hk; cases hk
    · rw [he] at ho; cases ho; exact hut rfl
    · rw [he] at hi; cases hi
  have hagI : ∀ K : Nat → Prop, (∀ l, K l → P.prot l ≠ .own t) → Agree K i.mem i'.mem := fun K hK l hl => by
    rcases himem l with ⟨_, ho⟩ | ⟨he, _⟩
    · exact absurd ho (hK l hl)
    · exact he.symm
  refine ⟨fun v => ?_, ?_, ?_, fun l hl hh hlt => ?_, ?_, ?_, fun v x hx => ?_, fun v => ?_, fun v => ?_⟩
  · by_cases hvt : v = t
    · subst hvt
      simp only [ThR, hsth, upd_same, hX, hith]
      exact ⟨trivial, trivial⟩
    · rw [upd_ne _ _ (ctx_thr_ne hvt)]
      refine thR_frame (hR.thr v) (by rw [hsth, upd_ne _ _ hvt]) (by rw [hith, upd_ne _ _ hvt])
        (by rw [hsm]; exact fun _ _ => rfl) (hagI _ (hown v · hvt)) (fun _ _ _ => ⟨by rw [hilv], by rw [hsown]⟩)
        (fun _ _ => ⟨hsmask, hshd⟩)
  · rw [upd_ne _ _ (by intro h; cases h)]
    exact hdR_frame hD.2 hR.hd hshd (fun _ => ⟨by rw [hsm]; exact fun _ _ => rfl,
      hagI _ (fun l hl he => by unfold KIrq at hl; rw [hl] at he; cases he), hsmask⟩)
  · rw [upd_ne _ _ (by intro h; cases h)]; exact hR.dma
  · rw [hsm]
    rcases himem l with ⟨he, _⟩ | ⟨he, hlx⟩
    · exact he
    · rw [he]
      refine hR.mem l (fun v hv => ?_) (by unfold HdK at hh ⊢; rw [hshd] at hh; exact hh) (fun v => ?_)
      · by_cases hvt : v = t
        · subst hvt; exact curK_none hc l hv
        · exact hl v (by rw [hsth, upd_ne _ _ hvt]; exact hv)
      · by_cases hvt : v = t
        · subst hvt; exact hlx (by have := hlt v; rwa [hsth, upd_same] at this)
        · have := hlt v; rwa [hsth, upd_ne _ _ hvt] at this
  · rw [hilv, hslv]; exact hR.lview
  · exact hsam.symm
  · by_cases hvt : v = t
    · subst hvt; rw [hsth, upd_same] at hx; exact hlo x hx
    · rw [hsth, upd_ne _ _ hvt] at hx; exact hR.lentOwn v x hx
  · by_cases hvt : v = t
    · subst hvt; rw [hsth, upd_same]; exact hok
    · rw [hsth, upd_ne _ _ hvt]; exact hR.prog v
  · by_cases hvt : v = t
    · subst hvt
      rw [hith, upd_same]
      have hit := hR.thr v
      simp only [ThR, hc] at hit
      have := hR.suf v
      rw [hit.1, hp] at this
      exact List.IsSuffix.trans (List.suffix_cons u _) this
    · rw [hith, upd_ne _ _ hvt]; exact hR.suf v

/-- A thread between units is equal to its ideal thread and has nothing pending. -/
theorem thR_none {P : Prog} {s : S} {i : IS} {pa : Ctx → List Int} {t : Fin 2} (hR : R P s i pa)
    (hc : (s.th t).cur = none) :
    i.th t = ⟨(s.th t).prog, (s.th t).regs, (s.th t).view, (s.th t).lent⟩ ∧ pa (.thr t) = [] := by
  have h := hR.thr t
  simp only [ThR, hc] at h
  exact h

/-- An atomic operation commits as the same atomic step of `I`, with the same choice. -/
theorem sim_atom {P : Prog} {s : S} {i : IS} {pa : Ctx → List Int} {t : Fin 2} {o : Ord} {op : AOp}
    {ps : List Seg} {w : Nat} {ρ' : Regs} {V' : View} {A' : AMem} (hD : Disc P) (hR : R P s i pa)
    (hc : (s.th t).cur = none) (hp : (s.th t).prog = .atom o op :: ps)
    (ha : AStep o op (s.th t).regs (s.th t).view s.am w ρ' V' A') :
    ∃ w i', IStep P i (.thr t) (pa (.thr t) ++ (none : Option Int).toList) w i' ∧
      R P { (s.setTh t { s.th t with prog := ps, regs := ρ', view := V' }) with am := A' } i'
        (upd pa (.thr t) []) := by
  obtain ⟨hit, hpa⟩ := thR_none hR hc
  have hpo := hR.prog t
  rw [hp] at hpo
  refine ⟨w, { (i.setTh t ⟨ps, ρ', V', (i.th t).lent⟩) with am := A' }, ?_, sim_idle (X := { s.th t with prog := ps, regs := ρ', view := V' }) hD hR hc hc hp hpo
    (hR.lentOwn t) rfl rfl rfl rfl rfl rfl rfl (by show upd i.th t _ = _; rw [hit]) rfl (fun _ => Or.inr ⟨rfl, id⟩)⟩
  rw [hpa]
  exact IStep.atom (by rw [hit]; exact hp) (by rw [hit, hR.am]; exact ha)

/-- `lend` commits as `lend` of `I`. -/
theorem sim_lend {P : Prog} {s : S} {i : IS} {pa : Ctx → List Int} {t : Fin 2} {x : Nat} {ps : List Seg}
    (hD : Disc P) (hR : R P s i pa) (hc : (s.th t).cur = none) (hp : (s.th t).prog = .lend x :: ps) :
    ∃ w i', IStep P i (.thr t) (pa (.thr t) ++ (none : Option Int).toList) w i' ∧
      R P (s.setTh t { s.th t with prog := ps, lent := upd (s.th t).lent x true }) i' (upd pa (.thr t) []) := by
  obtain ⟨hit, hpa⟩ := thR_none hR hc
  have hpo := hR.prog t
  rw [hp] at hpo
  have hlo : ∀ y, upd (s.th t).lent x true y = true → P.prot y = .own t := fun y hy => by
    by_cases hyx : y = x
    · subst hyx; exact hpo.1
    · rw [upd_ne _ _ hyx] at hy; exact hR.lentOwn t y hy
  refine ⟨0, i.setTh t { i.th t with prog := ps, lent := upd (i.th t).lent x true }, ?_, sim_idle (X := { s.th t with prog := ps, lent := upd (s.th t).lent x true }) hD hR hc hc hp
    hpo.2 hlo rfl rfl rfl rfl rfl rfl hR.am.symm (by show upd i.th t _ = _; rw [hit]) rfl
    (fun l => Or.inr ⟨rfl, fun h => ?_⟩)⟩
  · rw [hpa]; exact IStep.lend (by rw [hit]; exact hp)
  · by_cases hlx : l = x
    · subst hlx; simp only [upd_same] at h; cases h
    · have h' : upd (s.th t).lent x true l = false := h
      rwa [upd_ne _ _ hlx] at h'

/-- `takeBack` commits as `takeBack` of `I` with the buffer's content as its answer. -/
theorem sim_take {P : Prog} {s : S} {i : IS} {pa : Ctx → List Int} {t : Fin 2} {x : Nat} {ps : List Seg}
    (hD : Disc P) (hR : R P s i pa) (hc : (s.th t).cur = none) (hp : (s.th t).prog = .takeBack x :: ps) :
    ∃ w i', IStep P i (.thr t) (pa (.thr t) ++ (some (s.mem x)).toList) w i' ∧
      R P (s.setTh t { s.th t with prog := ps, lent := upd (s.th t).lent x false }) i'
        (upd pa (.thr t) []) := by
  obtain ⟨hit, hpa⟩ := thR_none hR hc
  have hpo := hR.prog t
  rw [hp] at hpo
  have hlo : ∀ y, upd (s.th t).lent x false y = true → P.prot y = .own t := fun y hy => by
    by_cases hyx : y = x
    · subst hyx; simp at hy
    · rw [upd_ne _ _ hyx] at hy; exact hR.lentOwn t y hy
  refine ⟨0, { (i.setTh t { i.th t with prog := ps, lent := upd (i.th t).lent x false }) with
      mem := upd i.mem x (s.mem x) }, ?_, sim_idle (X := { s.th t with prog := ps, lent := upd (s.th t).lent x false }) hD hR hc hc hp
    hpo.2 hlo rfl rfl rfl rfl rfl rfl hR.am.symm (by show upd i.th t _ = _; rw [hit]) rfl (fun l => ?_)⟩
  · rw [hpa]; exact IStep.take (by rw [hit]; exact hp)
  · by_cases hlx : l = x
    · subst hlx; exact Or.inl ⟨by simp, hpo.1⟩
    · exact Or.inr ⟨upd_ne _ _ hlx, fun h => by
        have h' : upd (s.th t).lent x false l = false := h
        rwa [upd_ne _ _ hlx] at h'⟩

/-- A local assignment commits as the same assignment of `I`. -/
theorem sim_set {P : Prog} {s : S} {i : IS} {pa : Ctx → List Int} {t : Fin 2} {r : Nat} {e : Ex}
    {ps : List Seg} (hD : Disc P) (hR : R P s i pa) (hc : (s.th t).cur = none) (hp : (s.th t).prog = .set r e :: ps) :
    ∃ w i', IStep P i (.thr t) (pa (.thr t) ++ (none : Option Int).toList) w i' ∧
      R P (s.setTh t { s.th t with prog := ps, regs := upd (s.th t).regs r (e.eval (s.th t).regs) }) i'
        (upd pa (.thr t) []) := by
  obtain ⟨hit, hpa⟩ := thR_none hR hc
  have hpo := hR.prog t
  rw [hp] at hpo
  refine ⟨0, i.setTh t { i.th t with prog := ps, regs := upd (i.th t).regs r (e.eval (i.th t).regs) },
    ?_, sim_idle (X := { s.th t with prog := ps, regs := upd (s.th t).regs r (e.eval (s.th t).regs) })
    hD hR hc hc hp hpo (hR.lentOwn t) rfl rfl rfl rfl rfl rfl hR.am.symm (by show upd i.th t _ = _; rw [hit]) rfl
    (fun _ => Or.inr ⟨rfl, id⟩)⟩
  rw [hpa]; exact IStep.set (by rw [hit]; exact hp)

end Gabbro.Grammatik.Zielsatz.Ideal.Prototyp
