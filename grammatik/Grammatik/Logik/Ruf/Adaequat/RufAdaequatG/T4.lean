/- Part 4 of 12 of `RufAdaequatG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufAdaequatG.lean` imports all parts). -/
import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.T3

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 8. Under a `locks` body nothing returns -/

section KeinRueck

variable (O : Orakel D) (passes : Nat) {V : Vertrag D} (A : D.Lock → Prop)

/-- A block never ends in `.zurueck`. -/
def KeinRueckB {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') : Prop :=
  ∀ (σ σ' : World D) (ρ : Env D Γ) (v : ErgVal D V.erg),
    execBlock O passes keinRuf b σ ρ ≠ .zurueck σ' v

mutual

theorem stmtKein : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ'), StmtG A false s →
    ∀ (σ σ' : World D) (ρ : Env D Γ) (v : ErgVal D V.erg),
      execStmt O passes keinRuf s σ ρ ≠ .zurueck σ' v
  | _, _, _, _, .assignSlot t f' i e hw hL, _ =>
      BlattG.nicht_zurueck O passes keinRuf (.assignSlot t f' i e hw hL)
  | _, _, _, _, .assignThru p t ht f' i e hw hL, _ =>
      BlattG.nicht_zurueck O passes keinRuf (.assignThru _ p t ht f' i e hw hL)
  | _, _, _, _, .assignSlotRef r t ht ho f' e hw hL, _ =>
      BlattG.nicht_zurueck O passes keinRuf (.assignSlotRef _ r t ht ho f' e hw hL)
  | _, _, _, _, .assignGlob g e hw hL, _ =>
      BlattG.nicht_zurueck O passes keinRuf (.assignGlob g e hw hL)
  | _, _, _, _, .putBytes t f' hf n i hlo hhi e hw hL, _ =>
      BlattG.nicht_zurueck O passes keinRuf (.putBytes t f' hf n i hlo hhi e hw hL)
  | _, _, _, _, .assignVar x e, _ =>
      BlattG.nicht_zurueck O passes keinRuf (.assignVar x e)
  | _, _, _, _, .shift t f' hτ i von nach hn he hw hL, _ =>
      BlattG.nicht_zurueck O passes keinRuf (.shift t f' hτ i von nach hn he hw hL)
  | _, _, _, _, .regWrite r hk e, _ =>
      BlattG.nicht_zurueck O passes keinRuf (.regWrite r hk e)
  | _, _, _, _, .transition r hk m hm hl maske bits, _ =>
      BlattG.nicht_zurueck O passes keinRuf (.transition r hk m hm hl maske bits)
  | _, _, _, _, .publish g e payload hp hw hL, _ =>
      BlattG.nicht_zurueck O passes keinRuf (.publish g e payload hp hw hL)
  | _, _, _, _, .advances m a h hs, _ =>
      BlattG.nicht_zurueck O passes keinRuf (.advances m a h hs)
  | _, _, _, _, .retires m s h a, _ =>
      BlattG.nicht_zurueck O passes keinRuf (.retires m s h a)
  | _, _, _, _, .ite c t e, hs => by
      intro σ σ' ρ v hex
      obtain ⟨ht, he⟩ := hs.ite_inv
      simp only [execStmt] at hex
      split at hex
      · exact blockKein t ht _ _ _ _ hex
      · exact blockKein e he _ _ _ _ hex
  | _, _, _, _, .onOption o p a, hs => by
      intro σ σ' ρ v hex
      obtain ⟨hp, ha⟩ := hs.onOption_inv
      simp only [execStmt] at hex
      split at hex
      · exact blockKein p hp _ _ _ _ (schrumpf_zurueck hex)
      · exact blockKein a ha _ _ _ _ hex
  | _, _, Λ₀, _, .onTag w arms, hs => by
      intro σ σ' ρ v hex
      have ha := hs.onTag_inv
      simp only [execStmt] at hex
      rw [execArms_wahl] at hex
      have hk := armsKein arms ha (eval (σ.lese Λ₀ w.orte) w (σ.lese Λ₀ w.orte) ρ)
      generalize armWahlG arms (eval (σ.lese Λ₀ w.orte) w (σ.lese Λ₀ w.orte) ρ) = x at hex hk
      obtain ⟨c, b, nutz⟩ := x
      cases c with
      | none => exact hk _ _ _ _ hex
      | some lh => exact hk _ _ _ _ (schrumpf_zurueck hex)
  | _, _, _, _, .onWhy r arms, hs => by
      intro σ σ' ρ v hex
      have ha := hs.onGrund_inv
      simp only [execStmt] at hex
      rw [execGrund_wahlW O passes keinRuf arms] at hex
      exact grundKein arms ha _ _ _ _ _ hex
  | _, _, _, _, .call .., hs => absurd hs.art (by simp only [Stmt.gArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, .callInd .., hs => absurd hs.art (by simp only [Stmt.gArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, .locks L hr body, hs => by
      intro σ σ' ρ v hex
      obtain ⟨_, hb⟩ := hs.locks_inv
      simp only [execStmt] at hex
      obtain ⟨σ1, h1, _⟩ := mapWelt_zurueck hex
      exact blockKein body hb _ _ _ _ h1
  | _, _, _, _, .breaking i body, hs => by
      intro σ σ' ρ v hex
      have hb := hs.breaking_inv
      simp only [execStmt] at hex
      exact blockKein body hb _ _ _ _ hex
  | _, _, _, _, .traverse .., hs => absurd hs.art (by simp only [Stmt.gArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, .retry .., hs => absurd hs.art (by simp only [Stmt.gArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, .forever .., hs => absurd hs.art (by simp only [Stmt.gArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, .axiomCall .., hs => absurd hs.art (by simp only [Stmt.gArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, .ret .., hs => absurd hs.ret_inv (by decide)
  | _, _, _, _, .retWhy .., hs => absurd hs.art (by simp only [Stmt.gArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, .leave .., hs => absurd hs.art (by simp only [Stmt.gArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, .next .., hs => absurd hs.art (by simp only [Stmt.gArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])

theorem blockKein : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D V l Γ Λ Λ'), BlockG A false b → KeinRueckB O passes b
  | _, _, _, _, .nil, _ => by
      intro σ σ' ρ v hex
      simp only [execBlock, reduceCtorEq] at hex
  | _, _, _, _, .cons s rest, hb => by
      intro σ σ' ρ v hex
      obtain ⟨hs, hr⟩ := hb.cons_inv
      rcases execBlock_cons_zurueck O passes keinRuf s rest hex with h | ⟨σ1, ρ1, _, h⟩
      · exact stmtKein s hs _ _ _ _ h
      · exact blockKein rest hr _ _ _ _ h
  | _, _, _, _, .bind e rest, hb => by
      intro σ σ' ρ v hex
      have hr := hb.bind_inv
      simp only [execBlock] at hex
      exact blockKein rest hr _ _ _ _ (schrumpf_zurueck hex)
  | _, _, _, _, .bindCall .., hb => by cases hb
  | _, _, _, _, .bindCallInd .., hb => by cases hb
  | _, _, _, _, .bindCallElse .., hb => by cases hb
  | _, _, _, _, .bindAxiom .., hb => by cases hb
  | _, _, _, _, .bindAxiomElse .., hb => by cases hb
  | _, _, _, _, .regRead r hk rest, hb => by
      intro σ σ' ρ v hex
      have hr := hb.regLies_inv
      simp only [execBlock] at hex
      split at hex
      · split at hex
        · exact blockKein rest hr _ _ _ _ (schrumpf_zurueck hex)
        · cases hex
      · cases hex
  | _, _, _, _, .regReadElse .., hb => absurd hb.regLiesElse_inv.1 (by decide)
  | _, _, _, _, .awaits g payload hp hL hat rest, hb => by
      intro σ σ' ρ v hex
      have hr := hb.awaits_inv
      simp only [execBlock] at hex
      split at hex
      · exact blockKein rest hr _ _ _ _ (schrumpf_zurueck hex)
      · cases hex
  | _, _, _, _, .exchange g neuE hw hL rest, hb => by
      intro σ σ' ρ v hex
      have hr := hb.exchange_inv
      simp only [execBlock] at hex
      exact blockKein rest hr _ _ _ _ (schrumpf_zurueck hex)
  | _, _, _, _, .narrow .., hb => absurd hb.narrow_inv.1 (by decide)
  | _, _, _, _, .check .., hb => absurd hb.pruefung_inv.1 (by decide)
  | _, _, _, _, .float op a b lo hi rest, hb => by
      intro σ σ' ρ v hex
      have hr := hb.gleit_inv
      simp only [execBlock] at hex
      split at hex
      · exact blockKein rest hr _ _ _ _ (schrumpf_zurueck hex)
      · cases hex
  | _, _, _, _, .floatLit q lo hi rest, hb => by
      intro σ σ' ρ v hex
      have hr := hb.gleitLit_inv
      simp only [execBlock] at hex
      split at hex
      · exact blockKein rest hr _ _ _ _ (schrumpf_zurueck hex)
      · cases hex
  | _, _, _, _, .floatOf e lo hi rest, hb => by
      intro σ σ' ρ v hex
      have hr := hb.gleitVon_inv
      simp only [execBlock] at hex
      split at hex
      · exact blockKein rest hr _ _ _ _ (schrumpf_zurueck hex)
      · cases hex
  | _, _, _, _, .floatNarrow .., hb => absurd hb.gleitNarrow_inv.1 (by decide)

theorem armsKein : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs),
    ArmsG A false arms → ∀ (v : Wert D (.sum cs)),
    KeinRueckB O passes (armWahlG arms v).2.1
  | _, _, _, _, _, .nil, _, ⟨⟨k, hk⟩, _⟩ => (Nat.not_lt_zero k hk).elim
  | _, _, _, _, _, .cons b _, ha, ⟨⟨0, _⟩, _⟩ => blockKein b ha.cons_inv.1
  | _, _, _, _, _, .cons _ rest, ha, ⟨⟨_ + 1, _⟩, _⟩ => armsKein rest ha.cons_inv.2 _

theorem grundKein : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D V l Γ Λ Λ' n), GrundArmsG A false arms →
    ∀ (r : Fin n), KeinRueckB O passes (grundWahlG arms r)
  | _, _, _, _, _, .nil, _, ⟨k, hk⟩ => (Nat.not_lt_zero k hk).elim
  | _, _, _, _, _, .cons b _, ha, ⟨0, _⟩ => blockKein b ha.cons_inv.1
  | _, _, _, _, _, .cons _ rest, ha, ⟨_ + 1, _⟩ => grundKein rest ha.cons_inv.2 _

end

end KeinRueck
/-! ## 9. Statements at `ende` position: `blatt`, or `endeEntf` into `dann` -/

section Ende

variable (P : Programm D) (O : Orakel D) (passes : Nat) (f : Faden) (fn : D.Fn)
  (stapel : List (RufRahmenG D)) (rho : Env D (D.params fn)) (s0 : World D)
  (log : List (RufEreignisF D)) (A : D.Lock → Prop)

/-- A covered statement at `ende (s; rest)` that ends normally runs to
    `ende rest`: a leaf by `blatt`, a compound by `endeEntf`, its `dann`
    simulation and `dannLeer`. -/
theorem endeConsOk {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {s : Stmt D (vertragVon D fn) l Γ Λ Λ'} (hs : StmtG A mr s)
    (hok : SimOkS P O passes f fn stapel rho s0 log A s)
    (σ σ' : World D) (ρ ρ' : Env D Γ)
    (hex : execStmt O passes keinRuf s σ ρ = .ok σ' ρ') (M : RufMaschineG D)
    (rest : Endblock D (vertragVon D fn) l Γ Λ')
    (hZ : ZustandG M f stapel fn rho s0 log ρ (.ende (.cons s rest)) σ)
    (hΛ : HeldGenau Λ (offen σ.spur)) (hA : FreiA A M f) :
    ∃ M', RufLaufG P O passes f M M' ∧
      ZustandG M' f stapel fn rho s0 log ρ' (.ende rest) σ' ∧
      offen σ'.spur = offen σ.spur := by
  have hW := hZ.welt
  have hEntf : ∀ (hent : GEntfaltbar s = true),
      ∃ M', RufLaufG P O passes f M M' ∧
        ZustandG M' f stapel fn rho s0 log ρ' (.ende rest) σ' ∧
        offen σ'.spur = offen σ.spur := by
    intro hent
    obtain ⟨M1, hs1, hZ1⟩ := w_endeEntf (P := P) (O := O) (passes := passes) hZ.1
      s rest ρ hent rfl
    rw [hW] at hZ1
    obtain ⟨M2, hr2, hZ2, ho2⟩ := hok σ σ' ρ ρ' hex M1 .nil (.ende rest) hZ1 hΛ
      (hA.lauf (RufLaufG.einzeln hs1))
    have hW2 := hZ2.welt
    obtain ⟨M3, hs3, hZ3⟩ := w_dannLeer (P := P) (O := O) (passes := passes) hZ2.1
      (.ende rest) ρ' rfl
    rw [hW2] at hZ3
    exact ⟨M3, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3, ho2⟩
  cases hs with
  | blatt _ h =>
    have herw := h.erw O passes keinRuf σ σ' ρ ρ' hex
    obtain ⟨M1, hs1, hZ1⟩ := w_blatt (P := P) (O := O) (passes := passes) hZ.1 s rest ρ
      h.istBlatt rfl hΛ.heldIn σ' ρ' (by rw [hW]; exact hex) (by rw [hW]; exact herw)
    exact ⟨M1, RufLaufG.einzeln hs1, hZ1, herw.offen⟩
  | ret _ _ => simp only [execStmt, reduceCtorEq] at hex
  | ite => exact hEntf rfl
  | onOption => exact hEntf rfl
  | onTag => exact hEntf rfl
  | onWhy => exact hEntf rfl
  | breaking => exact hEntf rfl
  | locks => exact hEntf rfl

end Ende
/-! ## 10. Return: the machine pops with the value `execBlock` returns -/


end Gabbro.Grammatik
