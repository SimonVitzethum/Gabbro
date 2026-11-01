module

public import Grammatik.Logik.Fortschritt.Folge
public import Grammatik.Logik.Fortschritt.FolgeBeweis.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section Schritt
variable {P : Programm D} {O : Orakel D} {pa : Nat} (Φ : Folge D)

set_option maxHeartbeats 4000000 in
/-- **Every rule of G keeps the order invariant.** -/
theorem folgeInvG_schritt (hΦ : FolgeOk P Φ) {M M' : RufMaschineG D} {f : Faden}
    (hs : RufSchrittG P O pa M f M') (h : FolgeInvG Φ (M.faeden f)) :
    FolgeInvG Φ (M'.faeden f) := by
  obtain ⟨hk, hst, hlog⟩ := h
  generalize hw : Armiert Φ (M.faeden f).log = w at hk
  cases hs with
  | g1 hs =>
    cases hs with
    | blatt l Γ Λ Λ' s rest ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
      dsimp only; rw [rufUpdateG_self]
      refine ⟨?_, hst, hlog⟩
      dsimp only; rw [hw]
      rw [hhead] at hk
      simp only [GRest.fR, fE, Bool.and_eq_true] at hk ⊢
      rw [fNach_blatt Φ w s hleaf] at hk
      exact hk.2
    | dannBlatt l Γ Λ Λ' Λ'' s rest k ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
      dsimp only; rw [rufUpdateG_self]
      refine ⟨?_, hst, hlog⟩
      dsimp only; rw [hw]
      rw [hhead] at hk
      simp only [GRest.fR, fB, Bool.and_eq_true] at hk ⊢
      rw [fNach_blatt Φ w s hleaf] at hk
      exact ⟨hk.1.2, hk.2⟩
    | ruf l Γ Λ g args hp hr rest ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      dsimp only; rw [rufUpdateG_self]
      rw [hhead] at hk
      simp only [GRest.fR, fE, fS, fNach, Bool.and_eq_true, Bool.or_eq_true,
        Bool.not_eq_true'] at hk
      refine ⟨hΦ.1 g, ⟨hk.2, hst⟩, fun _ hp => ?_, hlog⟩
      rw [hw]
      exact armiert_aus hk.1 (by simpa [Pflichtig] using hp)
    | rueck caller rst hpop Γ Λ e hperm ρ hh g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu hnw =>
      subst hfg
      dsimp only; rw [rufUpdateG_self]
      rw [hpop] at hst
      obtain ⟨hc, hr⟩ := hst
      rw [hh] at hk
      simp only [GRest.fR, fE, Bool.or_eq_true, Bool.not_eq_true'] at hk
      refine ⟨hc, hr, fun _ hp => ?_, hlog⟩
      rw [hw]
      exact armiert_aus hk (by simpa [Pflichtig] using hp)
    | dannOnTagSome l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ lo hi b nutz hwahl =>
      kopfF
      have h := fB_armWahlG Φ _ arms (eval σ₁ v σ₁ ρ) hk.1.1
      rw [hwahl] at h
      exact ⟨fB_von_false Φ _ b w h, hk.1.2, hk.2⟩
    | dannOnTagNone l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ b nutz hwahl =>
      kopfF
      have h := fB_armWahlG Φ _ arms (eval σ₁ v σ₁ ρ) hk.1.1
      rw [hwahl] at h
      exact ⟨fB_von_false Φ _ b w h, hk.1.2, hk.2⟩
    | dannOnGrund l Γ Λ Λ' Λ'' n r arms rest k ρ hhead σ₁ hs₁ b hwahl =>
      kopfF
      have h := fB_grundWahlG Φ _ arms (eval σ₁ r σ₁ ρ) hk.1.1
      rw [hwahl] at h
      exact ⟨fB_von_false Φ _ b w h, hk.1.2, hk.2⟩
    | endeEntf l Γ Λ Λ' s rest ρ hent hhead =>
      dsimp only; rw [rufUpdateG_self]
      refine ⟨?_, hst, hlog⟩
      dsimp only; rw [hw]
      rw [hhead] at hk
      simp only [GRest.fR, fE, fB, Bool.and_eq_true] at hk ⊢
      rw [fNach_entf Φ w s hent] at hk
      exact ⟨⟨hk.1, trivial⟩, hk.2⟩
    | endeForm l Γ Λ e ρ hl hent hhead =>
      dsimp only; rw [rufUpdateG_self]
      refine ⟨?_, hst, hlog⟩
      dsimp only; rw [hw]
      rw [hhead] at hk
      simp only [GRest.fR, fB_alsBlock] at hk ⊢
      exact ⟨hk, trivial⟩
    | _ =>
      kopfF
      all_goals (simp_all [fB_von_false, fR_von_false]; done)
  | g2 hs =>
    cases hs with
    | rufDann l Γ Λ Λ' Λ'' g args hp hr rest k ρ hhead hΛ s0 hs0 rho =>
      dsimp only; rw [rufUpdateG_self]
      rw [hhead] at hk
      simp only [GRest.fR, fB, fS, fNach, Bool.and_eq_true, Bool.or_eq_true,
        Bool.not_eq_true'] at hk
      refine ⟨hΦ.1 g, ⟨⟨hk.1.2, hk.2⟩, hst⟩, fun _ hp => ?_, hlog⟩
      rw [hw]
      exact armiert_aus hk.1.1 (by simpa [Pflichtig] using hp)
    | dannNarrowElse =>
      kopfF
      exact ⟨fE_mono Φ _ _ false w (fun h => absurd h Bool.false_ne_true) hk.1.1, hk.2⟩
    | dannPruefFalsch =>
      kopfF
      exact ⟨fE_mono Φ _ _ false w (fun h => absurd h Bool.false_ne_true) hk.1.1, hk.2⟩
    | _ =>
      kopfF
      all_goals (simp_all [fB_von_false, fR_von_false]; done)
  | g3 hs =>
    cases hs with
    | dannBindCall l Γ Λ Λ' Λ'' τ g args he hp hr rest k ρ hhead hΛ s0 hs0 rho =>
      dsimp only; rw [rufUpdateG_self]
      rw [hhead] at hk
      simp only [GRest.fR, fB, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hk
      refine ⟨hΦ.1 g, ⟨⟨hk.1.2, hk.2⟩, hst⟩, fun _ hp => ?_, hlog⟩
      rw [hw]
      exact armiert_aus hk.1.1 (by simpa [Pflichtig] using hp)
    | dannBindCallElse l Γ Λ Λ' Λ'' τ g args he hp hr err rest k ρ hhead hΛ s0 hs0 rho =>
      dsimp only; rw [rufUpdateG_self]
      rw [hhead] at hk
      simp only [GRest.fR, fB, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hk
      refine ⟨hΦ.1 g, ⟨⟨hk.1.1.2, hk.1.2, hk.2⟩, hst⟩, fun _ hp => ?_, hlog⟩
      rw [hw]
      exact armiert_aus hk.1.1.1 (by simpa [Pflichtig] using hp)
    | dannCallInd l Γ Λ Λ' Λ'' n p args hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho =>
      dsimp only; rw [rufUpdateG_self]
      rw [hhead] at hk
      simp only [GRest.fR, fB, fS, fNach, Bool.and_eq_true, Bool.or_eq_true,
        Bool.not_eq_true'] at hk
      refine ⟨hΦ.1 g, ⟨⟨fB_von_false Φ _ rest _ hk.1.2, hk.2⟩, hst⟩, fun _ hp => ?_, hlog⟩
      rw [hw]
      exact armiert_aus hk.1.1 (hΦ.2 g _ (by simpa [Pflichtig] using hp) hg)
    | rufCallInd l Γ Λ n p args hp hr rest ρ hhead hΛ s0 hs0 g hg hv rho =>
      dsimp only; rw [rufUpdateG_self]
      rw [hhead] at hk
      simp only [GRest.fR, fE, fS, fNach, Bool.and_eq_true, Bool.or_eq_true,
        Bool.not_eq_true'] at hk
      refine ⟨hΦ.1 g, ⟨fE_mono Φ _ rest false _ (fun h => absurd h Bool.false_ne_true) hk.2, hst⟩,
        fun _ hp => ?_, hlog⟩
      rw [hw]
      exact armiert_aus hk.1 (hΦ.2 g _ (by simpa [Pflichtig] using hp) hg)
    | dannBindCallInd l Γ Λ Λ' Λ'' τ n p args he hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho =>
      dsimp only; rw [rufUpdateG_self]
      rw [hhead] at hk
      simp only [GRest.fR, fB, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hk
      refine ⟨hΦ.1 g, ⟨⟨fB_von_false Φ _ rest _ hk.1.2, hk.2⟩, hst⟩, fun _ hp => ?_, hlog⟩
      rw [hw]
      exact armiert_aus hk.1.1 (hΦ.2 g _ (by simpa [Pflichtig] using hp) hg)
    | rueckBind caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller Γc Λc e hperm ρ hh g hfg rho hrho
        s0 hs0 hΛ s1 hs1 v hv he neu hneu =>
      subst hfg
      dsimp only; rw [rufUpdateG_self]
      rw [hpop] at hst
      obtain ⟨hc, hr⟩ := hst
      rw [hh] at hk
      simp only [GRest.fR, fE, Bool.or_eq_true, Bool.not_eq_true'] at hk
      refine ⟨?_, hr, fun _ hp => ?_, hlog⟩
      · rcases hcaller with hcc | ⟨n, err, hcc⟩ <;> rw [hcc] at hc <;>
          simp only [GRest.fR, Armiert] at hc ⊢
        · exact hc
        · exact ⟨hc.2.1, hc.2.2⟩
      · rw [hw]
        exact armiert_aus hk (by simpa [Pflichtig] using hp)
    | _ =>
      kopfF
      all_goals (simp_all [fB_von_false, fR_von_false]; done)
  | g4 hs =>
    cases hs with
    | rueckCons caller rst hpop Γ Λ e hperm rest ρ hh g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu
        hneu hnw =>
      subst hfg
      dsimp only; rw [rufUpdateG_self]
      rw [hpop] at hst
      obtain ⟨hc, hr⟩ := hst
      rw [hh] at hk
      simp only [GRest.fR, fE, fS, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hk
      refine ⟨hc, hr, fun _ hp => ?_, hlog⟩
      rw [hw]
      exact armiert_aus hk.1 (by simpa [Pflichtig] using hp)
    | dannRet l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop hΛ s1 hs1 g hfg rho hrho s0 hs0 v
        hv neu hneu hnw =>
      subst hfg
      dsimp only; rw [rufUpdateG_self]
      rw [hpop] at hst
      obtain ⟨hc, hr⟩ := hst
      rw [hhead] at hk
      simp only [GRest.fR, fB, fS, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hk
      refine ⟨hc, hr, fun _ hp => ?_, hlog⟩
      rw [hw]
      exact armiert_aus hk.1.1 (by simpa [Pflichtig] using hp)
    | dannRetBind lk Γk Λk Λk'' e hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc
        hcaller hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
      subst hfg
      dsimp only; rw [rufUpdateG_self]
      rw [hpop] at hst
      obtain ⟨hc, hr⟩ := hst
      rw [hhead] at hk
      simp only [GRest.fR, fB, fS, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hk
      refine ⟨?_, hr, fun _ hp => ?_, hlog⟩
      · rcases hcaller with hcc | ⟨n, err, hcc⟩ <;> rw [hcc] at hc <;>
          simp only [GRest.fR, Armiert] at hc ⊢
        · exact hc
        · exact ⟨hc.2.1, hc.2.2⟩
      · rw [hw]
        exact armiert_aus hk.1.1 (by simpa [Pflichtig] using hp)
    | rueckConsBind lk Γk Λk e hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller
        hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
      subst hfg
      dsimp only; rw [rufUpdateG_self]
      rw [hpop] at hst
      obtain ⟨hc, hr⟩ := hst
      rw [hhead] at hk
      simp only [GRest.fR, fE, fS, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hk
      refine ⟨?_, hr, fun _ hp => ?_, hlog⟩
      · rcases hcaller with hcc | ⟨n, err, hcc⟩ <;> rw [hcc] at hc <;>
          simp only [GRest.fR, Armiert] at hc ⊢
        · exact hc
        · exact ⟨hc.2.1, hc.2.2⟩
      · rw [hw]
        exact armiert_aus hk.1 (by simpa [Pflichtig] using hp)
    | rueckGrund r hperm ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g hfg rho
        hrho s0 hs0 rg hrg hn =>
      subst hfg
      dsimp only; rw [rufUpdateG_self]
      rw [hpop] at hst
      obtain ⟨hc, hr⟩ := hst
      rw [hcaller] at hc
      rw [hhead] at hk
      simp only [GRest.fR, fE, Bool.or_eq_true, Bool.not_eq_true'] at hk
      simp only [GRest.fR] at hc
      refine ⟨?_, hr, fun _ hp => ?_, hlog⟩
      · simp only [GRest.fR, Armiert, fB_alsBlock]
        exact ⟨hc.1, hc.2.2⟩
      · rw [hw]
        exact armiert_aus hk (by simpa [Pflichtig] using hp)
    | _ =>
      kopfF
      all_goals (simp_all [fB_von_false, fR_von_false]; done)
  | g5 hs =>
    cases hs with
    | rueckConsGrund r hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ
        g hfg rho hrho s0 hs0 rg hrg hn =>
      subst hfg
      dsimp only; rw [rufUpdateG_self]
      rw [hpop] at hst
      obtain ⟨hc, hr⟩ := hst
      rw [hcaller] at hc
      rw [hhead] at hk
      simp only [GRest.fR, fE, fS, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hk
      simp only [GRest.fR] at hc
      refine ⟨?_, hr, fun _ hp => ?_, hlog⟩
      · simp only [GRest.fR, Armiert, fB_alsBlock]
        exact ⟨hc.1, hc.2.2⟩
      · rw [hw]
        exact armiert_aus hk.1 (by simpa [Pflichtig] using hp)
    | dannRetGrund r hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller
        hΛ g hfg rho hrho s0 hs0 rg hrg hn =>
      subst hfg
      dsimp only; rw [rufUpdateG_self]
      rw [hpop] at hst
      obtain ⟨hc, hr⟩ := hst
      rw [hcaller] at hc
      rw [hhead] at hk
      simp only [GRest.fR, fB, fS, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hk
      simp only [GRest.fR] at hc
      refine ⟨?_, hr, fun _ hp => ?_, hlog⟩
      · simp only [GRest.fR, Armiert, fB_alsBlock]
        exact ⟨hc.1, hc.2.2⟩
      · rw [hw]
        exact armiert_aus hk.1.1 (by simpa [Pflichtig] using hp)
    | dannRegLiesElseFalsch =>
      kopfF
      exact ⟨fE_mono Φ _ _ false w (fun h => absurd h Bool.false_ne_true) hk.1.1, hk.2⟩
    | dannGleitNarrowElse =>
      kopfF
      exact ⟨fE_mono Φ _ _ false w (fun h => absurd h Bool.false_ne_true) hk.1.1, hk.2⟩
    | dannBindAxiomElseGrund =>
      kopfF
      first
        | exact ⟨fE_mono Φ _ _ false w (fun h => absurd h Bool.false_ne_true) hk.1.1, hk.2⟩
        | exact fE_mono Φ _ _ false w (fun h => absurd h Bool.false_ne_true) hk.1.1
    | _ =>
      kopfF
      all_goals (simp_all [fB_von_false, fR_von_false]; done)
  | g6 hs =>
    cases hs with
    | endeBindAxiomElseGrund =>
      kopfF
      exact fE_mono Φ _ _ false w (fun h => absurd h Bool.false_ne_true) hk.1
    | _ =>
      kopfF
      all_goals (simp_all [fB_von_false, fR_von_false]; done)

end Schritt

/-! ## 4. On every reachable machine -/

section Erreichbar

variable {P : Programm D} {O : Orakel D} {pa : Nat}

theorem folgeInvG_start (Φ : Folge D) (hΦ : FolgeOk P Φ) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (t : Faden) :
    FolgeInvG Φ ((RufStartG P sp init).faeden t) := by
  have e : (RufStartG P sp init).faeden t =
      ⟨[], ⟨(init t).1, (init t).2, sp.welt [], ⟨false, D.params (init t).1,
        Signatur.anfang D (D.signatur (init t).1), (init t).2, .ende (P.rumpf (init t).1)⟩⟩,
        startSpur (init t).1, [RufEreignisF.eintritt (init t).1 (init t).2 (sp.welt [])]⟩ := by
    show (match init t with
      | ⟨g, rho⟩ => (⟨[], ⟨g, rho, sp.welt [], ⟨false, D.params g,
          Signatur.anfang D (D.signatur g), rho, .ende (P.rumpf g)⟩⟩, startSpur g,
          [RufEreignisF.eintritt g rho (sp.welt [])]⟩ : RufFadenG D)) = _
    cases init t
    rfl
  rw [e]
  exact ⟨hΦ.1 _, trivial, fun h => absurd rfl h, trivial⟩

/-- **The order invariant on every reachable machine.** -/
theorem folgeInvG_erreichbar (Φ : Folge D) (hΦ : FolgeOk P Φ) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) {M : RufMaschineG D}
    (hr : RufErreichbarG P O pa (RufStartG P sp init) M) : ∀ t, FolgeInvG Φ (M.faeden t) := by
  induction hr with
  | start => exact folgeInvG_start Φ hΦ sp init
  | schritt M M' u _ hs ih =>
      intro t
      by_cases htu : t = u
      · subst htu
        exact folgeInvG_schritt Φ hΦ hs (ih t)
      · rw [rufSchrittG_fremd hs t htu]
        exact ih t

/-- **THE ORDER LEG** (`FolgeG`, Folge.lean) on every reachable machine of G: for every order
    specification the program passes, every thread's call log is ordered, and a finished
    thread whose start function is an `ende` function ended directly behind a return of a
    `vor` function. No premise beyond reachability: the order is carried by the language. -/
theorem folgeG_erreichbar (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    {M : RufMaschineG D} (hr : RufErreichbarG P O pa (RufStartG P sp init) M) : FolgeG P M := by
  intro Φ hΦ t
  have hI := folgeInvG_erreichbar Φ hΦ sp init hr t
  exact ⟨hI.2.2, fun _ ha he => fR_anRueck Φ _ _ _ ha hI.1 he⟩

end Erreichbar

/-! ## 5. The order is not the conjunction -/

/-- **`FolgeLog` is strictly stronger than "both happened".** A log in which the ordered event
    and a return of a `vor` function both occur, but the ordered event is not DIRECTLY behind
    it, is not ordered -- `flush ∧ reply` holds of it, the order does not. -/
theorem folgeLog_nicht_schwach (Φ : Folge D) (ev a : RufEreignisF D)
    (rest : List (RufEreignisF D)) (hp : Pflichtig Φ ev = true)
    (ha : Armiert Φ [a] = true) (hn : Armiert Φ (rest ++ [a]) = false) (hr : rest ≠ []) :
    (∃ x ∈ ev :: rest ++ [a], Pflichtig Φ x = true) ∧ (∃ x ∈ ev :: rest ++ [a], Armiert Φ [x] = true) ∧
      ¬ FolgeLog Φ (ev :: (rest ++ [a])) := by
  refine ⟨⟨ev, List.mem_cons_self, hp⟩, ⟨a, by simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false, or_true], ha⟩, fun h => ?_⟩
  have := h.1 (by cases rest with | nil => exact absurd rfl hr | cons _ _ => simp only [List.cons_append, ne_eq, reduceCtorEq, not_false_eq_true]) hp
  rw [hn] at this
  exact Bool.false_ne_true this

#print axioms Gabbro.Grammatik.folgeInvG_schritt
#print axioms Gabbro.Grammatik.folgeG_erreichbar
#print axioms Gabbro.Grammatik.folgeLog_nicht_schwach

end Gabbro.Grammatik
