/-
  File:      Grammatik/FolgeBeweis.lean
  Subject:   THE ORDER OF EFFECTS IS CARRIED BY MACHINE G (OFFEN O1, Opus agent G,
             2026-09-26): `folgeG_erreichbar`.

  For every order specification `Φ` a program passes (`FolgeOk`, Folge.lean), every reachable
  machine of G has, in every thread's call log, every entry of a `ruf` function and every
  return of an `ende` function DIRECTLY behind a return of a `vor` function, and a finished
  thread whose start function is an `ende` function ended directly behind one.

  THE INVARIANT (`FolgeInvG`), per thread:
  * the head frame's residue passes the check with the armed bit read off the log
    (`Armiert`: the newest log event is a return of a `vor` function);
  * every suspended caller's residue passes it with the bit `vor g` of the callee `g` above it
    (`FolgeStapel`): that is the bit the caller resumes with when `g` pops;
  * the log is ordered (`FolgeLog`).
  Every rule of G keeps it (`folgeInvG_schritt`): a head-local step logs nothing and moves the
  residue along the checked text (a leaf keeps the bit, an unfold starts a sub-block unarmed,
  which the check allows since it is monotone in the bit, `fB_mono`); a push logs the entry
  of a callee, which the residue demanded armed if the callee is ordered, and suspends the
  caller at the bit `vor g`; a pop logs the return of the head function, which the residue
  demanded armed if it is ordered, and resumes the caller at exactly the bit its suspended
  residue was checked at.
-/
import Grammatik.Folge

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The check: monotone in the bit, stable under selection -/

section Hilfen

variable (Φ : Folge D) {V : Vertrag D}

theorem fNach_blatt {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (w : Bool)
    (s : Stmt D V l Γ Λ Λ') (h : s.istBlatt = true) : fNach Φ w s = w := by
  cases s <;> simp_all [Stmt.istBlatt, fNach]

theorem fNach_entf {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (w : Bool)
    (s : Stmt D V l Γ Λ Λ') (h : GEntfaltbar s = true) : fNach Φ w s = false := by
  cases s <;> simp_all [GEntfaltbar, fNach]

theorem fS_mono {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (e w : Bool)
    (s : Stmt D V l Γ Λ Λ') (h : fS Φ e false s = true) : fS Φ e w s = true := by
  cases s <;> simp_all [fS]

theorem fNach_mono {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (w : Bool)
    (s : Stmt D V l Γ Λ Λ') (h : fNach Φ false s = true) : fNach Φ w s = true := by
  cases s <;> simp_all [fNach]

/-- The check of a block is monotone in the armed bit. -/
theorem fB_mono {l : Bool} {Γ : Ctx} :
    ∀ {Λ Λ' : List (Res D)} (e : Bool) (b : Block D V l Γ Λ Λ') (w w' : Bool),
      (w = true → w' = true) → fB Φ e w b = true → fB Φ e w' b = true
  | _, _, _, .nil, _, _, _, _ => rfl
  | _, _, e, .cons s rest, w, w', hw, h => by
      simp only [fB, Bool.and_eq_true] at h ⊢
      refine ⟨?_, fB_mono e rest _ _ ?_ h.2⟩
      · cases s <;> simp_all [fS] <;> (cases w <;> cases w' <;> simp_all)
      · cases s <;> simp_all [fNach]
  | _, _, e, .bind _ rest, w, w', hw, h => by
      simp only [fB] at h ⊢; exact fB_mono e rest _ _ hw h
  | _, _, e, .bindCall g _ _ _ _ rest, w, w', hw, h => by
      simp only [fB, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h ⊢
      exact ⟨h.1.imp id hw, h.2⟩
  | _, _, e, .bindCallInd _ _ _ _ _ rest, w, w', hw, h => by
      simp only [fB, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h ⊢
      exact ⟨h.1.imp id hw, h.2⟩
  | _, _, e, .bindCallElse g _ _ _ _ err rest, w, w', hw, h => by
      simp only [fB, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h ⊢
      exact ⟨⟨h.1.1.imp id hw, h.1.2⟩, h.2⟩
  | _, _, e, .bindAxiom _ _ _ _ _ _ _ rest, w, w', hw, h => by
      simp only [fB] at h ⊢; exact fB_mono e rest _ _ hw h
  | _, _, e, .regLies _ _ rest, w, w', hw, h => by
      simp only [fB] at h ⊢; exact fB_mono e rest _ _ hw h
  | _, _, e, .regLiesElse _ _ _ sonst rest, w, w', hw, h => by
      simp only [fB, Bool.and_eq_true] at h ⊢; exact ⟨h.1, fB_mono e rest _ _ hw h.2⟩
  | _, _, e, .awaits _ _ _ _ rest, w, w', hw, h => by
      simp only [fB] at h ⊢; exact fB_mono e rest _ _ hw h
  | _, _, e, .exchange _ _ _ _ rest, w, w', hw, h => by
      simp only [fB] at h ⊢; exact fB_mono e rest _ _ hw h
  | _, _, e, .narrow _ _ _ sonst rest, w, w', hw, h => by
      simp only [fB, Bool.and_eq_true] at h ⊢; exact ⟨h.1, fB_mono e rest _ _ hw h.2⟩
  | _, _, e, .pruefung _ sonst rest, w, w', hw, h => by
      simp only [fB, Bool.and_eq_true] at h ⊢; exact ⟨h.1, fB_mono e rest _ _ hw h.2⟩
  | _, _, e, .gleit _ _ _ _ _ rest, w, w', hw, h => by
      simp only [fB] at h ⊢; exact fB_mono e rest _ _ hw h
  | _, _, e, .gleitLit _ _ _ rest, w, w', hw, h => by
      simp only [fB] at h ⊢; exact fB_mono e rest _ _ hw h
  | _, _, e, .gleitVon _ _ _ rest, w, w', hw, h => by
      simp only [fB] at h ⊢; exact fB_mono e rest _ _ hw h
  | _, _, e, .gleitNarrow _ _ _ sonst rest, w, w', hw, h => by
      simp only [fB, Bool.and_eq_true] at h ⊢; exact ⟨h.1, fB_mono e rest _ _ hw h.2⟩

/-- The check of an end block is monotone in the armed bit. -/
theorem fE_mono {l : Bool} :
    ∀ {Γ : Ctx} {Λ : List (Res D)} (e : Bool) (b : Endblock D V l Γ Λ) (w w' : Bool),
      (w = true → w' = true) → fE Φ e w b = true → fE Φ e w' b = true
  | _, _, e, .ret _ _, w, w', hw, h => by
      simp only [fE, Bool.or_eq_true, Bool.not_eq_true'] at h ⊢; exact h.imp id hw
  | _, _, e, .retGrund _ _, w, w', hw, h => by
      simp only [fE, Bool.or_eq_true, Bool.not_eq_true'] at h ⊢; exact h.imp id hw
  | _, _, _, .leave _, _, _, _, _ => rfl
  | _, _, _, .next _, _, _, _, _ => rfl
  | _, _, e, .cons s rest, w, w', hw, h => by
      simp only [fE, Bool.and_eq_true] at h ⊢
      refine ⟨?_, fE_mono e rest _ _ ?_ h.2⟩
      · cases s <;> simp_all [fS] <;> (cases w <;> cases w' <;> simp_all)
      · cases s <;> simp_all [fNach]
  | _, _, e, .bind _ rest, w, w', hw, h => by
      simp only [fE] at h ⊢; exact fE_mono e rest _ _ hw h

/-- The residue predicate is monotone in the armed bit. -/
theorem fR_mono (e : Bool) :
    ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (k : GRest D V l Γ Λ) (w w' : Bool),
      (w = true → w' = true) → k.fR Φ e w → k.fR Φ e w'
  | _, _, _, .ende b, w, w', hw, h => fE_mono Φ e b w w' hw h
  | _, _, _, .dann b k, w, w', hw, h => ⟨fB_mono Φ e b w w' hw h.1, h.2⟩
  | _, _, _, .schrumpf k, w, w', hw, h => fR_mono e k w w' hw h
  | _, _, _, .frei _ k, w, w', hw, h => fR_mono e k w w' hw h
  | _, _, _, .trav .., _, _, _, h => h
  | _, _, _, .travRest .., _, _, _, h => h
  | _, _, _, .wieder .., _, _, _, h => h
  | _, _, _, .wiederRest .., _, _, _, h => h
  | _, _, _, .ewig .., _, _, _, h => h
  | _, _, _, .ewigRest .., _, _, _, h => h
  | _, _, _, .wartet b k, w, w', hw, h => ⟨fB_mono Φ e b w w' hw h.1, h.2⟩
  | _, _, _, .wartetSonst _ err b k, w, w', hw, h => ⟨h.1, fB_mono Φ e b w w' hw h.2.1, h.2.2⟩
  | _, _, _, .abbruch _, _, _, _, h => h

theorem fR_von_false (e : Bool) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (k : GRest D V l Γ Λ) (w : Bool) (h : k.fR Φ e false) : k.fR Φ e w :=
  fR_mono Φ e k false w (fun h => absurd h Bool.false_ne_true) h

theorem fB_von_false (e : Bool) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D V l Γ Λ Λ') (w : Bool) (h : fB Φ e false b = true) : fB Φ e w b = true :=
  fB_mono Φ e b false w (fun h => absurd h Bool.false_ne_true) h

/-- An end block run as a block is checked as the end block. -/
theorem fB_alsBlock (e : Bool) {l : Bool} :
    ∀ {Γ : Ctx} {Λ : List (Res D)} (b : Endblock D V l Γ Λ) (w : Bool),
      fB Φ e w b.alsBlock.2 = fE Φ e w b
  | _, _, .ret _ _, w => by simp [Endblock.alsBlock, fB, fS, fE, fNach]
  | _, _, .retGrund _ _, w => by simp [Endblock.alsBlock, fB, fS, fE, fNach]
  | _, _, .leave _, w => by simp [Endblock.alsBlock, fB, fS, fE]
  | _, _, .next _, w => by simp [Endblock.alsBlock, fB, fS, fE]
  | _, _, .cons s rest, w => by
      simp only [Endblock.alsBlock, fB, fE, fB_alsBlock e rest]
  | _, _, .bind _ rest, w => by
      simp only [Endblock.alsBlock, fB, fE, fB_alsBlock e rest]

theorem fB_armWahlG (e : Bool) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    ∀ {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs)),
    fArms Φ e arms = true → fB Φ e false (armWahlG arms v).2.1 = true
  | _, .nil, ⟨⟨k, hk⟩, _⟩, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons b rest, ⟨⟨0, _⟩, _⟩, h => by
      simp only [fArms, Bool.and_eq_true] at h
      exact h.1
  | _, .cons b rest, ⟨⟨n + 1, hn⟩, nutz⟩, h => by
      simp only [fArms, Bool.and_eq_true] at h
      exact fB_armWahlG e rest _ h.2

theorem fB_grundWahlG (e : Bool) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    ∀ {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n),
    fGArms Φ e arms = true → fB Φ e false (grundWahlG arms r) = true
  | _, .nil, ⟨k, hk⟩, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons b rest, ⟨0, _⟩, h => by
      simp only [fGArms, Bool.and_eq_true] at h
      exact h.1
  | _, .cons b rest, ⟨k + 1, hk⟩, h => by
      simp only [fGArms, Bool.and_eq_true] at h
      exact fB_grundWahlG e rest _ h.2

/-- A residue standing at a return, checked at bit `w`, demands `w` if its frame's returns
    are ordered. -/
theorem fR_anRueck (e : Bool) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (r : GRest D V l Γ Λ) (w : Bool) (ha : r.anRueck = true) (h : r.fR Φ e w)
    (he : e = true) : w = true := by
  subst he
  cases r with
  | ende b =>
      cases b with
      | ret _ _ => simpa [GRest.fR, fE] using h
      | retGrund _ _ => simpa [GRest.fR, fE] using h
      | cons s _ =>
          cases s <;> simp_all [GRest.anRueck, Endblock.istRueck, Stmt.istRueck, GRest.fR, fE, fS]
      | _ => simp [GRest.anRueck, Endblock.istRueck] at ha
  | dann b _ =>
      cases b with
      | cons s _ =>
          cases s <;> simp_all [GRest.anRueck, Block.istRueck, Stmt.istRueck, GRest.fR, fB, fS]
      | _ => simp [GRest.anRueck, Block.istRueck] at ha
  | _ => simp [GRest.anRueck] at ha

end Hilfen

/-! ## 2. The thread invariant -/

/-- Every suspended caller passes the check at the bit its callee's return will give it. -/
def FolgeStapel (Φ : Folge D) : D.Fn → List (RufRahmenG D) → Prop
  | _, [] => True
  | oben, F :: rest => F.rest.2.2.2.2.fR Φ (Φ.ende F.f) (Φ.vor oben) ∧ FolgeStapel Φ F.f rest

/-- **The thread invariant of the order leg.** -/
def FolgeInvG (Φ : Folge D) (z : RufFadenG D) : Prop :=
  z.kopf.rest.2.2.2.2.fR Φ (Φ.ende z.kopf.f) (Armiert Φ z.log) ∧
    FolgeStapel Φ z.kopf.f z.stapel ∧ FolgeLog Φ z.log

/-! ## 3. Every rule keeps the invariant -/

theorem armiert_aus {b w : Bool} (hk : b = false ∨ w = true) (hb : b = true) : w = true := by
  rcases hk with h | h
  · rw [h] at hb; exact absurd hb Bool.false_ne_true
  · exact h

section Schritt

variable {P : Programm D} {O : Orakel D} {pa : Nat} (Φ : Folge D)

set_option hygiene false in
/-- A head-local step: stack and log unchanged, the residue moves. -/
macro "kopfF" : tactic => `(tactic| (
  dsimp only; rw [rufUpdateG_self]
  refine ⟨?_, hst, hlog⟩
  dsimp only; rw [hw]
  rw [‹(M.faeden f).kopf.rest = _›] at hk
  dsimp only at hk ⊢
  simp only [GRest.fR, fE, fB, fS, fNach, fB_alsBlock, Bool.and_eq_true] at hk ⊢))

set_option maxHeartbeats 4000000 in
/-- **Every rule of G keeps the order invariant.** -/
theorem folgeInvG_schritt (hΦ : FolgeOk P Φ) {M M' : RufMaschineG D} {f : Faden}
    (hs : RufSchrittG P O pa M f M') (h : FolgeInvG Φ (M.faeden f)) :
    FolgeInvG Φ (M'.faeden f) := by
  obtain ⟨hk, hst, hlog⟩ := h
  generalize hw : Armiert Φ (M.faeden f).log = w at hk
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
  | rufDann l Γ Λ Λ' Λ'' g args hp hr rest k ρ hhead hΛ s0 hs0 rho =>
    dsimp only; rw [rufUpdateG_self]
    rw [hhead] at hk
    simp only [GRest.fR, fB, fS, fNach, Bool.and_eq_true, Bool.or_eq_true,
      Bool.not_eq_true'] at hk
    refine ⟨hΦ.1 g, ⟨⟨hk.1.2, hk.2⟩, hst⟩, fun _ hp => ?_, hlog⟩
    rw [hw]
    exact armiert_aus hk.1.1 (by simpa [Pflichtig] using hp)
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
    exact armiert_aus hk.1.1 (hg ▸ hΦ.2 g (by simpa [Pflichtig] using hp))
  | rufCallInd l Γ Λ n p args hp hr rest ρ hhead hΛ s0 hs0 g hg hv rho =>
    dsimp only; rw [rufUpdateG_self]
    rw [hhead] at hk
    simp only [GRest.fR, fE, fS, fNach, Bool.and_eq_true, Bool.or_eq_true,
      Bool.not_eq_true'] at hk
    refine ⟨hΦ.1 g, ⟨fE_mono Φ _ rest false _ (fun h => absurd h Bool.false_ne_true) hk.2, hst⟩,
      fun _ hp => ?_, hlog⟩
    rw [hw]
    exact armiert_aus hk.1 (hg ▸ hΦ.2 g (by simpa [Pflichtig] using hp))
  | dannBindCallInd l Γ Λ Λ' Λ'' τ n p args he hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho =>
    dsimp only; rw [rufUpdateG_self]
    rw [hhead] at hk
    simp only [GRest.fR, fB, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hk
    refine ⟨hΦ.1 g, ⟨⟨fB_von_false Φ _ rest _ hk.1.2, hk.2⟩, hst⟩, fun _ hp => ?_, hlog⟩
    rw [hw]
    exact armiert_aus hk.1.1 (hg ▸ hΦ.2 g (by simpa [Pflichtig] using hp))
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
  | dannNarrowElse =>
    kopfF
    exact ⟨fE_mono Φ _ _ false w (fun h => absurd h Bool.false_ne_true) hk.1.1, hk.2⟩
  | dannPruefFalsch =>
    kopfF
    exact ⟨fE_mono Φ _ _ false w (fun h => absurd h Bool.false_ne_true) hk.1.1, hk.2⟩
  | dannRegLiesElseFalsch =>
    kopfF
    exact ⟨fE_mono Φ _ _ false w (fun h => absurd h Bool.false_ne_true) hk.1.1, hk.2⟩
  | dannGleitNarrowElse =>
    kopfF
    exact ⟨fE_mono Φ _ _ false w (fun h => absurd h Bool.false_ne_true) hk.1.1, hk.2⟩
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
  refine ⟨⟨ev, List.mem_cons_self, hp⟩, ⟨a, by simp, ha⟩, fun h => ?_⟩
  have := h.1 (by cases rest with | nil => exact absurd rfl hr | cons _ _ => simp) hp
  rw [hn] at this
  exact Bool.false_ne_true this

#print axioms Gabbro.Grammatik.folgeInvG_schritt
#print axioms Gabbro.Grammatik.folgeG_erreichbar
#print axioms Gabbro.Grammatik.folgeLog_nicht_schwach

end Gabbro.Grammatik
