/- Part 6 of 10 of `RufAdaequatRufG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufAdaequatRufG.lean` imports all parts). -/
import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T5

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 7. Under a `locks` body the frame never ends

    A `locks` body is covered at `mr = false`: no `ret`, no `retGrund`, no
    `let … else`. So it never ends the frame (no `zurueck`, no `grund`) --
    the machine could not release the lock on such a pop. -/

section KeinRueck

variable (O : Orakel D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D}
  (A : D.Lock → Prop) (C : D.Fn → Prop)

/-- A block never ends the frame. -/
def KeinRueckBR {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') : Prop :=
  ∀ (σ : World D) (ρ : Env D Γ), (execBlock O passes R b σ ρ).ende? = none

mutual

theorem stmtKeinR : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ'), StmtR A C false s →
    ∀ (σ : World D) (ρ : Env D Γ), (execStmt O passes R s σ ρ).ende? = none
  | _, _, _, _, .assignSlot t f' i e hw hL, _ =>
      BlattG.ende_none O passes R (.assignSlot t f' i e hw hL)
  | _, _, _, _, .assignThru p t ht f' i e hw hL, _ =>
      BlattG.ende_none O passes R (.assignThru _ p t ht f' i e hw hL)
  | _, _, _, _, .assignGlob g e hw hL, _ =>
      BlattG.ende_none O passes R (.assignGlob g e hw hL)
  | _, _, _, _, .putBytes t f' hf n i hlo hhi e hw hL, _ =>
      BlattG.ende_none O passes R (.putBytes t f' hf n i hlo hhi e hw hL)
  | _, _, _, _, .assignVar x e, _ =>
      BlattG.ende_none O passes R (.assignVar x e)
  | _, _, _, _, .shift t f' hτ i von nach hn he hw hL, _ =>
      BlattG.ende_none O passes R (.shift t f' hτ i von nach hn he hw hL)
  | _, _, _, _, .regWrite r hk e, _ =>
      BlattG.ende_none O passes R (.regWrite r hk e)
  | _, _, _, _, .transition r hk m hm hl maske bits, _ =>
      BlattG.ende_none O passes R (.transition r hk m hm hl maske bits)
  | _, _, _, _, .publish g e payload hp hw hL, _ =>
      BlattG.ende_none O passes R (.publish g e payload hp hw hL)
  | _, _, _, _, .advances m a h hs, _ =>
      BlattG.ende_none O passes R (.advances m a h hs)
  | _, _, _, _, .retires m s h a, _ =>
      BlattG.ende_none O passes R (.retires m s h a)
  | _, _, _, _, .ite c t e, hs => by
      intro σ ρ
      obtain ⟨ht, he⟩ := hs.ite_inv
      simp only [execStmt]
      split
      · exact blockKeinR t ht _ _
      · exact blockKeinR e he _ _
  | _, _, _, _, .onOption o p a, hs => by
      intro σ ρ
      obtain ⟨hp, ha⟩ := hs.onOption_inv
      simp only [execStmt]
      split
      · rw [ende_schrumpf]; exact blockKeinR p hp _ _
      · exact blockKeinR a ha _ _
  | _, _, Λ₀, _, .onTag w arms, hs => by
      intro σ ρ
      have ha := hs.onTag_inv
      simp only [execStmt]
      rw [execArms_wahl, ende_schrumpfArm]
      exact armsKeinR arms ha _ _ _
  | _, _, _, _, .onWhy r arms, hs => by
      intro σ ρ
      have ha := hs.onGrund_inv
      simp only [execStmt]
      rw [execGrund_wahlW O passes R arms]
      exact grundKeinR arms ha _ _ _
  | _, _, _, _, .call g args hp hr, _ => by
      intro σ ρ
      simp only [execStmt]
      split
      · rfl
      · exact (Fin.cast hr ‹_›).elim0
      · rfl
      · rfl
  | _, _, _, _, .callInd .., hs => absurd hs.art (by simp [Stmt.rArt, Stmt.blattArt])
  | _, _, _, _, .locks L hr body, hs => by
      intro σ ρ
      obtain ⟨_, hb, _⟩ := hs.locks_inv
      simp only [execStmt]
      exact ende_mapWelt_none _ (blockKeinR body hb _ _)
  | _, _, _, _, .breaking i body, hs => by
      intro σ ρ
      simp only [execStmt]
      exact blockKeinR body hs.breaking_inv _ _
  | _, _, _, _, .traverse t inv body, hs => by
      intro σ ρ
      simp only [execStmt]
      exact traverseLauf_ende_none _ _ (fun σ ρ => blockKeinR body hs.traverse_inv σ ρ) _ _ _
  | _, _, _, _, .retry n bis body ueber, hs => by
      intro σ ρ
      simp only [execStmt]
      exact retryLauf_ende_none _ _ _ (fun σ ρ => blockKeinR body hs.retry_inv.1 σ ρ)
        (fun σ ρ => blockKeinR ueber hs.retry_inv.2 σ ρ) _ _ _
  | _, _, _, _, .forever a inv body, hs => by
      intro σ ρ
      simp only [execStmt]
      exact foreverLauf_ende_none _ _ _ (fun σ ρ => blockKeinR body hs.forever_inv σ ρ) _ _ _
  | _, _, _, _, .axiomCall .., hs => absurd hs.art (by simp [Stmt.rArt, Stmt.blattArt])
  | _, _, _, _, .ret .., hs => absurd hs.ret_inv (by decide)
  | _, _, _, _, .retWhy .., hs => absurd hs.retGrund_inv (by decide)
  | _, _, _, _, .leave .., _ => by intro σ ρ; rfl
  | _, _, _, _, .next .., _ => by intro σ ρ; rfl

theorem blockKeinR : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D V l Γ Λ Λ'), BlockR A C false b → KeinRueckBR O passes R b
  | _, _, _, _, .nil, _ => by
      intro σ ρ
      rfl
  | _, _, _, _, .cons s rest, hb => by
      intro σ ρ
      obtain ⟨hs, hr⟩ := hb.cons_inv
      simp only [execBlock]
      have h1 := stmtKeinR s hs σ ρ
      generalize execStmt O passes R s σ ρ = o at h1 ⊢
      cases o with
      | ok σ1 ρ1 => exact blockKeinR rest hr _ _
      | _ => exact h1
  | _, _, _, _, .bind e rest, hb => by
      intro σ ρ
      have hr := hb.bind_inv
      simp only [execBlock]
      rw [ende_schrumpf]
      exact blockKeinR rest hr _ _
  | _, _, _, _, .bindCall g args he hp hr rest, hb => by
      intro σ ρ
      have hr' := hb.bindCall_inv.2
      simp only [execBlock]
      split
      · rw [ende_schrumpf]; exact blockKeinR rest hr' _ _
      · exact (Fin.cast hr ‹_›).elim0
      · rfl
      · rfl
  | _, _, _, _, .bindCallInd .., hb => by cases hb
  | _, _, _, _, .bindCallElse .., hb => absurd hb.bindCallElse_inv.2.2.2.1 (by decide)
  | _, _, _, _, .bindAxiom .., hb => by cases hb
  | _, _, _, _, .bindAxiomElse .., hb => by cases hb
  | _, _, _, _, .regRead r hk rest, hb => by
      intro σ ρ
      have hr := hb.regLies_inv
      simp only [execBlock]
      split
      · split
        · rw [ende_schrumpf]; exact blockKeinR rest hr _ _
        · rfl
      · rfl
  | _, _, _, _, .regReadElse .., hb => absurd hb.regLiesElse_inv.1 (by decide)
  | _, _, _, _, .awaits g payload hp hL rest, hb => by
      intro σ ρ
      have hr := hb.awaits_inv
      simp only [execBlock]
      split
      · rw [ende_schrumpf]; exact blockKeinR rest hr _ _
      · rfl
  | _, _, _, _, .exchange g neuE hw hL rest, hb => by
      intro σ ρ
      have hr := hb.exchange_inv
      simp only [execBlock]
      rw [ende_schrumpf]
      exact blockKeinR rest hr _ _
  | _, _, _, _, .narrow .., hb => absurd hb.narrow_inv.1 (by decide)
  | _, _, _, _, .check .., hb => absurd hb.pruefung_inv.1 (by decide)
  | _, _, _, _, .float op a b lo hi rest, hb => by
      intro σ ρ
      have hr := hb.gleit_inv
      simp only [execBlock]
      split
      · rw [ende_schrumpf]; exact blockKeinR rest hr _ _
      · rfl
  | _, _, _, _, .floatLit q lo hi rest, hb => by
      intro σ ρ
      have hr := hb.gleitLit_inv
      simp only [execBlock]
      split
      · rw [ende_schrumpf]; exact blockKeinR rest hr _ _
      · rfl
  | _, _, _, _, .floatOf e lo hi rest, hb => by
      intro σ ρ
      have hr := hb.gleitVon_inv
      simp only [execBlock]
      split
      · rw [ende_schrumpf]; exact blockKeinR rest hr _ _
      · rfl
  | _, _, _, _, .floatNarrow .., hb => absurd hb.gleitNarrow_inv.1 (by decide)

theorem armsKeinR : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs),
    ArmsR A C false arms → ∀ (v : Wert D (.sum cs)),
    KeinRueckBR O passes R (armWahlG arms v).2.1
  | _, _, _, _, _, .nil, _, ⟨⟨k, hk⟩, _⟩ => (Nat.not_lt_zero k hk).elim
  | _, _, _, _, _, .cons b _, ha, ⟨⟨0, _⟩, _⟩ => blockKeinR b ha.cons_inv.1
  | _, _, _, _, _, .cons _ rest, ha, ⟨⟨_ + 1, _⟩, _⟩ => armsKeinR rest ha.cons_inv.2 _

theorem grundKeinR : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D V l Γ Λ Λ' n), GrundArmsR A C false arms →
    ∀ (r : Fin n), KeinRueckBR O passes R (grundWahlG arms r)
  | _, _, _, _, _, .nil, _, ⟨k, hk⟩ => (Nat.not_lt_zero k hk).elim
  | _, _, _, _, _, .cons b _, ha, ⟨0, _⟩ => blockKeinR b ha.cons_inv.1
  | _, _, _, _, _, .cons _ rest, ha, ⟨_ + 1, _⟩ => grundKeinR rest ha.cons_inv.2 _

end

end KeinRueck
/-! ## 8. Statements at `ende` position: `blatt`, a call by `ruf`, or `endeEntf` into `dann` -/

section Ende

variable (P : Programm D) (O : Orakel D) (passes : Nat) (f : Faden) (fn : D.Fn)
  (stapel : List (RufRahmenG D)) (rho : Env D (D.params fn)) (s0 : World D)
  (A : D.Lock → Prop) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
  (C : D.Fn → Prop)

/-- A covered statement at `ende (s; rest)` that ends normally runs to
    `ende rest`: a leaf by `blatt`, a call by the repaired `ruf` and the
    callee obligation, a compound by `endeEntf`, its `dann` simulation and
    `dannLeer`. -/
theorem endeConsOkR (hRuf : RufOk P O passes f A R C) {mr l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {log : List (RufEreignisF D)}
    {s : Stmt D (vertragVon D fn) l Γ Λ Λ'} (hs : StmtR A C mr s)
    (hok : SimOkSR P O passes f fn stapel rho s0 A R s)
    (σ σ' : World D) (ρ ρ' : Env D Γ)
    (hex : execStmt O passes R s σ ρ = .ok σ' ρ') (M : RufMaschineG D)
    (rest : Endblock D (vertragVon D fn) l Γ Λ')
    (hZ : ZustandG M f stapel fn rho s0 log ρ (.ende (.cons s rest)) σ)
    (hΛ : HeldB (vertragVon D fn).boden Λ (offen σ.spur)) (hA : FreiA A M f) :
    ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
      ZustandG M' f stapel fn rho s0 (ext ++ log) ρ' (.ende rest) σ' ∧
      offen σ'.spur = offen σ.spur := by
  have hW := hZ.welt
  have hEntf : ∀ (hent : GEntfaltbar s = true),
      ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
        ZustandG M' f stapel fn rho s0 (ext ++ log) ρ' (.ende rest) σ' ∧
        offen σ'.spur = offen σ.spur := by
    intro hent
    obtain ⟨M1, hs1, hZ1⟩ := w_endeEntf (P := P) (O := O) (passes := passes) hZ.1
      s rest ρ hent rfl
    rw [hW] at hZ1
    obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := hok log σ σ' ρ ρ' hex M1 .nil (.ende rest) hZ1 hΛ
      (hA.lauf (RufLaufG.einzeln hs1))
    have hW2 := hZ2.welt
    obtain ⟨M3, hs3, hZ3⟩ := w_dannLeer (P := P) (O := O) (passes := passes) hZ2.1
      (.ende rest) ρ' rfl
    rw [hW2] at hZ3
    exact ⟨M3, _, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3, ho2⟩
  cases hs with
  | blatt _ h =>
    have herw := h.erw O passes R σ σ' ρ ρ' hex
    obtain ⟨M1, hs1, hZ1⟩ := w_blatt (P := P) (O := O) (passes := passes) hZ.1 s rest ρ
      h.istBlatt rfl hΛ.heldIn σ' ρ' (by rw [hW, ← h.exec_R O passes R]; exact hex)
      (by rw [hW]; exact herw)
    exact ⟨M1, [], RufLaufG.einzeln hs1, hZ1, herw.offen⟩
  | call s g' hg hC =>
    cases s with
    | call g args hp hr =>
      have hgg : g = g' := Option.some.inj hg
      subst hgg
      simp only [execStmt] at hex
      split at hex
      · rename_i σ2 v hR2
        simp only [Ausgang.ok.injEq] at hex
        obtain ⟨rfl, rfl⟩ := hex
        obtain ⟨M1, hs1, hZ1⟩ := w_rufEnde (P := P) (O := O) (passes := passes) hZ.1
          g args hp hr rest ρ rfl hΛ.heldIn
        rw [hW] at hZ1
        obtain ⟨M2, e2, hl2, hG2, ho2⟩ := hRuf.1 g hC _ _ _ _ hR2 M1 _ stapel _ hZ1 _ (PopArt.wie rfl)
          (heldB_eintritt hp hΛ _ _) (hA.lauf (RufLaufG.einzeln hs1))
        exact ⟨M2, _, RufLaufG.schritt hs1 hl2, gepoppt_zustand hG2 rfl,
          by rw [ho2, (Erw.lese _ _ _).offen]⟩
      · exact (Fin.cast hr ‹_›).elim0
      · cases hex
      · cases hex
    | _ => simp [Stmt.rufZiel] at hg
  | ret _ _ => simp [execStmt] at hex
  | retWhy _ _ => simp [execStmt] at hex
  | leave _ => simp [execStmt] at hex
  | next _ => simp [execStmt] at hex
  | ite => exact hEntf rfl
  | onOption => exact hEntf rfl
  | onTag => exact hEntf rfl
  | onWhy => exact hEntf rfl
  | breaking => exact hEntf rfl
  | locks => exact hEntf rfl
  | traverse => exact hEntf rfl
  | retry => exact hEntf rfl
  | forever => exact hEntf rfl

end Ende
/-! ## 9. The frame ends: the machine pops with the value or the reason
    `execBlock` ends with

    As `RufAdaequatG.lean` §10, for any handler `R`, fragment `C`, and for
    both ends of a frame: a return (`zurueck`) pops as `PopArt` says, a
    reason (`grund`, the error channel) pops as `PopGrund` says. The end
    `e` is fixed along the recursion (a block ends the frame with exactly
    the end its statements produce); the conclusion also keeps the held
    locks (`offen`), which the callee obligation needs. -/

/-- The pop a frame end needs: `PopArt` for a return, `PopGrund` for a
    reason. -/
def PopFuer (fn : D.Fn) (caller : RufRahmenG D) (ziel : ErgVal D (D.erg fn) → RufRahmenG D)
    (zielG : Fin (D.gruende fn) → RufRahmenG D) : EndeW (vertragVon D fn) → Prop
  | .zurueck _ _ => PopArt fn caller ziel
  | .why _ _ => PopGrund fn caller zielG

/-- The popped state for a frame end. -/
def GepopptE (M' : RufMaschineG D) (f : Faden) {fn : D.Fn}
    (ziel : ErgVal D (D.erg fn) → RufRahmenG D) (zielG : Fin (D.gruende fn) → RufRahmenG D)
    (rst : List (RufRahmenG D)) (rho : Env D (D.params fn)) (s0 : World D)
    (log : List (RufEreignisF D)) : EndeW (vertragVon D fn) → Prop
  | .zurueck σ' v => GepopptG M' f (ziel v) rst fn rho s0 log v σ'
  | .why σ' r => GepopptGrundG M' f (zielG r) rst fn rho s0 log r σ'


end Gabbro.Grammatik
