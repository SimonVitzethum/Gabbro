/- Part 5 of 12 of `RufAdaequatG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufAdaequatG.lean` imports all parts). -/
import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.T4

namespace Gabbro.Grammatik

variable {D : Deklaration}

section SimRet

variable (P : Programm D) (O : Orakel D) (passes : Nat) (f : Faden) (fn : D.Fn)
  (caller : RufRahmenG D) (rst : List (RufRahmenG D)) (rho : Env D (D.params fn))
  (s0 : World D) (log : List (RufEreignisF D)) (A : D.Lock → Prop)

/-- Block simulation, return: `dann b k` pops the frame with the value and
    the world `execBlock` returns. -/
def SimRetB {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D (vertragVon D fn) l Γ Λ Λ') : Prop :=
  ∀ (σ σ' : World D) (ρ : Env D Γ) (v : ErgVal D (vertragVon D fn).erg),
    execBlock O passes keinRuf b σ ρ = .zurueck σ' v →
  ∀ (M : RufMaschineG D) (k : GRest D (vertragVon D fn) l Γ Λ'),
    ZustandG M f (caller :: rst) fn rho s0 log ρ (.dann b k) σ →
    HeldGenau Λ (offen σ.spur) → FreiA A M f →
    ∃ M', RufLaufG P O passes f M M' ∧ GepopptG M' f caller rst fn rho s0 log v σ'

/-- Statement simulation, return, at `dann (s; rest) k`. -/
def SimRetS {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D (vertragVon D fn) l Γ Λ Λ') : Prop :=
  ∀ (σ σ' : World D) (ρ : Env D Γ) (v : ErgVal D (vertragVon D fn).erg),
    execStmt O passes keinRuf s σ ρ = .zurueck σ' v →
  ∀ (M : RufMaschineG D) {Λ'' : List (Res D)}
    (rest : Block D (vertragVon D fn) l Γ Λ' Λ'') (k : GRest D (vertragVon D fn) l Γ Λ''),
    ZustandG M f (caller :: rst) fn rho s0 log ρ (.dann (.cons s rest) k) σ →
    HeldGenau Λ (offen σ.spur) → FreiA A M f →
    ∃ M', RufLaufG P O passes f M M' ∧ GepopptG M' f caller rst fn rho s0 log v σ'

/-- End-block simulation, return, at `ende e`. -/
def SimRetE {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e : Endblock D (vertragVon D fn) l Γ Λ) : Prop :=
  ∀ (σ σ' : World D) (ρ : Env D Γ) (v : ErgVal D (vertragVon D fn).erg),
    execEnd O passes keinRuf e σ ρ = .zurueck σ' v →
  ∀ (M : RufMaschineG D),
    ZustandG M f (caller :: rst) fn rho s0 log ρ (.ende e) σ →
    HeldGenau Λ (offen σ.spur) → FreiA A M f →
    ∃ M', RufLaufG P O passes f M M' ∧ GepopptG M' f caller rst fn rho s0 log v σ'

theorem blattRet {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {s : Stmt D (vertragVon D fn) l Γ Λ Λ'} (h : BlattG s) :
    SimRetS P O passes f fn caller rst rho s0 log A s := by
  intro σ σ' ρ v hex
  exact absurd hex (h.nicht_zurueck O passes keinRuf σ σ' ρ v)

/-- Lift a pop after one step. -/
theorem gepoppt_vor {M M1 : RufMaschineG D} {v : ErgVal D (D.erg fn)} {σ' : World D}
    (hs : RufSchrittG P O passes M f M1)
    (h : ∃ M', RufLaufG P O passes f M1 M' ∧ GepopptG M' f caller rst fn rho s0 log v σ') :
    ∃ M', RufLaufG P O passes f M M' ∧ GepopptG M' f caller rst fn rho s0 log v σ' := by
  obtain ⟨M', hr, hG⟩ := h
  exact ⟨M', RufLaufG.schritt hs hr, hG⟩

/-- Lift a pop after a run. -/
theorem gepoppt_lauf {M M1 : RufMaschineG D} {v : ErgVal D (D.erg fn)} {σ' : World D}
    (hl : RufLaufG P O passes f M M1)
    (h : ∃ M', RufLaufG P O passes f M1 M' ∧ GepopptG M' f caller rst fn rho s0 log v σ') :
    ∃ M', RufLaufG P O passes f M M' ∧ GepopptG M' f caller rst fn rho s0 log v σ' := by
  obtain ⟨M', hr, hG⟩ := h
  exact ⟨M', hl.trans hr, hG⟩

variable (hnw : caller.wartend = false)
include hnw

/-- A statement at `ende (s; rest)` that returns: `rueckCons` for `ret`,
    `endeEntf` and the `dann` simulation for a compound. -/
theorem endeConsRet {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {s : Stmt D (vertragVon D fn) l Γ Λ Λ'} (hs : StmtG A true s) (hl : l = false)
    (hret : SimRetS P O passes f fn caller rst rho s0 log A s)
    (σ σ' : World D) (ρ : Env D Γ) (v : ErgVal D (vertragVon D fn).erg)
    (hex : execStmt O passes keinRuf s σ ρ = .zurueck σ' v) (M : RufMaschineG D)
    (rest : Endblock D (vertragVon D fn) l Γ Λ')
    (hZ : ZustandG M f (caller :: rst) fn rho s0 log ρ (.ende (.cons s rest)) σ)
    (hΛ : HeldGenau Λ (offen σ.spur)) (hA : FreiA A M f) :
    ∃ M', RufLaufG P O passes f M M' ∧ GepopptG M' f caller rst fn rho s0 log v σ' := by
  have hW := hZ.welt
  have hEntf : ∀ (hent : GEntfaltbar s = true),
      ∃ M', RufLaufG P O passes f M M' ∧ GepopptG M' f caller rst fn rho s0 log v σ' := by
    intro hent
    obtain ⟨M1, hs1, hZ1⟩ := w_endeEntf (P := P) (O := O) (passes := passes) hZ.1
      s rest ρ hent rfl
    rw [hW] at hZ1
    exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
      (hret σ σ' ρ v hex M1 .nil (.ende rest) hZ1 hΛ (hA.lauf (RufLaufG.einzeln hs1)))
  cases hs with
  | blatt _ h => exact absurd hex (h.nicht_zurueck O passes keinRuf σ σ' ρ v)
  | ret e hperm =>
    subst hl
    simp only [execStmt, Ausgang.zurueck.injEq] at hex
    obtain ⟨rfl, rfl⟩ := hex
    obtain ⟨M1, hs1, hG⟩ := w_rueckCons (P := P) (O := O) (passes := passes) hZ.1
      caller rst rfl e hperm rest ρ rfl hΛ.heldIn hnw
    rw [hW] at hG
    exact ⟨M1, RufLaufG.einzeln hs1, hG⟩
  | ite => exact hEntf rfl
  | onOption => exact hEntf rfl
  | onTag => exact hEntf rfl
  | onWhy => exact hEntf rfl
  | breaking => exact hEntf rfl
  | locks => exact hEntf rfl

-- `hnw` is used at the returns; `blockRet` and the arm recursions reach it
-- only through `stmtRet`/`endRet`, which the linter does not count as a use.
set_option maxHeartbeats 3200000 in
set_option linter.unusedSectionVars false in
mutual

theorem stmtRet : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D (vertragVon D fn) l Γ Λ Λ'), StmtG A true s →
    SimRetS P O passes f fn caller rst rho s0 log A s
  | _, _, _, _, .assignSlot t f' i e hw hL, _ =>
      blattRet P O passes f fn caller rst rho s0 log A (.assignSlot t f' i e hw hL)
  | _, _, _, _, .assignThru p t ht f' i e hw hL, _ =>
      blattRet P O passes f fn caller rst rho s0 log A (.assignThru _ p t ht f' i e hw hL)
  | _, _, _, _, .assignSlotRef r t ht ho f' e hw hL, _ =>
      blattRet P O passes f fn caller rst rho s0 log A (.assignSlotRef _ r t ht ho f' e hw hL)
  | _, _, _, _, .assignGlob g e hw hL, _ =>
      blattRet P O passes f fn caller rst rho s0 log A (.assignGlob g e hw hL)
  | _, _, _, _, .putBytes t f' hf n i hlo hhi e hw hL, _ =>
      blattRet P O passes f fn caller rst rho s0 log A
        (.putBytes t f' hf n i hlo hhi e hw hL)
  | _, _, _, _, .assignVar x e, _ =>
      blattRet P O passes f fn caller rst rho s0 log A (.assignVar x e)
  | _, _, _, _, .shift t f' hτ i von nach hn he hw hL, _ =>
      blattRet P O passes f fn caller rst rho s0 log A
        (.shift t f' hτ i von nach hn he hw hL)
  | _, _, _, _, .regWrite r hk e, _ =>
      blattRet P O passes f fn caller rst rho s0 log A (.regWrite r hk e)
  | _, _, _, _, .transition r hk m hm hl maske bits, _ =>
      blattRet P O passes f fn caller rst rho s0 log A (.transition r hk m hm hl maske bits)
  | _, _, _, _, .publish g e payload hp hw hL, _ =>
      blattRet P O passes f fn caller rst rho s0 log A (.publish g e payload hp hw hL)
  | _, _, _, _, .advances m a h hs, _ =>
      blattRet P O passes f fn caller rst rho s0 log A (.advances m a h hs)
  | _, _, _, _, .retires m s h a, _ =>
      blattRet P O passes f fn caller rst rho s0 log A (.retires m s h a)
  | _, _, _, _, .ite c t e, hs => by
      intro σ σ' ρ v hex M _ rest k hZ hΛ hA
      obtain ⟨ht, he⟩ := hs.ite_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      split at hex
      · rename_i hc
        obtain ⟨M1, hs1, hZ1⟩ := w_iteWahr (P := P) (O := O) (passes := passes) hZ.1
          c t e rest k ρ rfl (by rw [hW]; exact hc)
        rw [hW] at hZ1
        exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
          (blockRet t ht _ _ _ _ hex M1 _ hZ1 (heldGenau_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
      · rename_i hc
        obtain ⟨M1, hs1, hZ1⟩ := w_iteFalsch (P := P) (O := O) (passes := passes) hZ.1
          c t e rest k ρ rfl (by rw [hW]; simpa using hc)
        rw [hW] at hZ1
        exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
          (blockRet e he _ _ _ _ hex M1 _ hZ1 (heldGenau_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
  | _, _, _, _, .onOption o p a, hs => by
      intro σ σ' ρ v hex M _ rest k hZ hΛ hA
      obtain ⟨hp, ha⟩ := hs.onOption_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      split at hex
      · rename_i w hw
        obtain ⟨M1, hs1, hZ1⟩ := w_optSome (P := P) (O := O) (passes := passes) hZ.1
          o p a rest k ρ rfl w (by rw [hW]; exact hw)
        rw [hW] at hZ1
        exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
          (blockRet p hp _ _ _ _ (schrumpf_zurueck hex) M1 _ hZ1 (heldGenau_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
      · rename_i hw
        obtain ⟨M1, hs1, hZ1⟩ := w_optNone (P := P) (O := O) (passes := passes) hZ.1
          o p a rest k ρ rfl (by rw [hW]; exact hw)
        rw [hW] at hZ1
        exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
          (blockRet a ha _ _ _ _ hex M1 _ hZ1 (heldGenau_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
  | _, _, Λ₀, _, .onTag w arms, hs => by
      intro σ σ' ρ v hex M _ rest k hZ hΛ hA
      have ha := hs.onTag_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      rw [execArms_wahl] at hex
      have hsim := armsRet arms ha (eval (σ.lese Λ₀ w.orte) w (σ.lese Λ₀ w.orte) ρ)
      generalize hwahl : armWahlG arms (eval (σ.lese Λ₀ w.orte) w (σ.lese Λ₀ w.orte) ρ) = x
        at hex hsim
      obtain ⟨c, b, nutz⟩ := x
      cases c with
      | none =>
        obtain ⟨M1, hs1, hZ1⟩ := w_tagNone (P := P) (O := O) (passes := passes) hZ.1
          w arms rest k ρ rfl b nutz (by rw [hW]; exact hwahl)
        rw [hW] at hZ1
        exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
          (hsim _ _ _ _ hex M1 _ hZ1 (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1)))
      | some lh =>
        obtain ⟨lo, hi⟩ := lh
        obtain ⟨M1, hs1, hZ1⟩ := w_tagSome (P := P) (O := O) (passes := passes) hZ.1
          w arms rest k ρ rfl lo hi b nutz (by rw [hW]; exact hwahl)
        rw [hW] at hZ1
        exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
          (hsim _ _ _ _ (schrumpf_zurueck hex) M1 _ hZ1 (heldGenau_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
  | _, _, _, _, .onWhy r arms, hs => by
      intro σ σ' ρ v hex M _ rest k hZ hΛ hA
      have ha := hs.onGrund_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      rw [execGrund_wahlW O passes keinRuf arms] at hex
      obtain ⟨M1, hs1, hZ1⟩ := w_grund (P := P) (O := O) (passes := passes) hZ.1
        r arms rest k ρ rfl
      rw [hW] at hZ1
      exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
        (grundRet arms ha _ _ _ _ _ hex M1 _ hZ1 (heldGenau_lese _ hΛ)
          (hA.lauf (RufLaufG.einzeln hs1)))
  | _, _, _, _, .call .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, .callInd .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, .locks L hr body, hs => by
      intro σ σ' ρ v hex
      obtain ⟨_, hb⟩ := hs.locks_inv
      simp only [execStmt] at hex
      obtain ⟨σ1, h1, _⟩ := mapWelt_zurueck hex
      exact absurd h1 (blockKein O passes A body hb _ _ _ _)
  | _, _, _, _, .breaking i body, hs => by
      intro σ σ' ρ v hex M _ rest k hZ hΛ hA
      have hb := hs.breaking_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      obtain ⟨M1, hs1, hZ1⟩ := w_breaking (P := P) (O := O) (passes := passes) hZ.1
        i body rest k ρ rfl
      rw [hW] at hZ1
      exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
        (blockRet body hb _ _ _ _ hex M1 _ hZ1 hΛ (hA.lauf (RufLaufG.einzeln hs1)))
  | _, _, _, _, .traverse .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, .retry .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, .forever .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, .axiomCall .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, .ret e hperm, _ => by
      intro σ σ' ρ v hex M _ rest k hZ hΛ _
      have hW := hZ.welt
      simp only [execStmt, Ausgang.zurueck.injEq] at hex
      obtain ⟨rfl, rfl⟩ := hex
      obtain ⟨M1, hs1, hG⟩ := w_dannRet (P := P) (O := O) (passes := passes) hZ.1
        caller rst rfl e hperm rest k ρ rfl hΛ.heldIn hnw
      rw [hW] at hG
      exact ⟨M1, RufLaufG.einzeln hs1, hG⟩
  | _, _, _, _, .retWhy .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, .leave .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, .next .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])

theorem blockRet : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D (vertragVon D fn) l Γ Λ Λ'), BlockG A true b →
    SimRetB P O passes f fn caller rst rho s0 log A b
  | _, _, _, _, .nil, _ => by
      intro σ σ' ρ v hex
      simp [execBlock] at hex
  | _, _, _, _, .cons s rest, hb => by
      intro σ σ' ρ v hex M k hZ hΛ hA
      obtain ⟨hs, hr⟩ := hb.cons_inv
      rcases execBlock_cons_zurueck O passes keinRuf s rest hex with h | ⟨σ1, ρ1, h1, h2⟩
      · exact stmtRet s hs _ _ _ _ h M rest k hZ hΛ hA
      · obtain ⟨M1, hl1, hZ1, ho1⟩ := stmtOk P O passes f fn (caller :: rst) rho s0 log A
          s hs _ _ _ _ h1 M rest k hZ hΛ hA
        have hΛ1 := heldGenau_iff (s.held_iff) hΛ
        rw [← ho1] at hΛ1
        exact gepoppt_lauf P O passes f fn caller rst rho s0 log hl1
          (blockRet rest hr _ _ _ _ h2 M1 k hZ1 hΛ1 (hA.lauf hl1))
  | _, _, _, _, .bind e rest, hb => by
      intro σ σ' ρ v hex M k hZ hΛ hA
      have hr := hb.bind_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      obtain ⟨M1, hs1, hZ1⟩ := w_dannBind (P := P) (O := O) (passes := passes) hZ.1
        e rest k ρ rfl
      rw [hW] at hZ1
      exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
        (blockRet rest hr _ _ _ _ (schrumpf_zurueck hex) M1 _ hZ1 (heldGenau_lese _ hΛ)
          (hA.lauf (RufLaufG.einzeln hs1)))
  | _, _, _, _, .bindCall .., hb => by cases hb
  | _, _, _, _, .bindCallInd .., hb => by cases hb
  | _, _, _, _, .bindCallElse .., hb => by cases hb
  | _, _, _, _, .bindAxiom .., hb => by cases hb
  | _, _, _, _, .bindAxiomElse .., hb => by cases hb
  | _, _, _, _, .regRead r hk rest, hb => by
      intro σ σ' ρ v hex M k hZ hΛ hA
      have hr := hb.regLies_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i w hw
        split at hex
        · rename_i hzs
          obtain ⟨M1, hs1, hZ1⟩ := w_regLies (P := P) (O := O) (passes := passes) hZ.1
            r hk rest k ρ rfl w (by rw [hW]; exact hw) hzs
          rw [hW] at hZ1
          exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
            (blockRet rest hr _ _ _ _ (schrumpf_zurueck hex) M1 _ hZ1 hΛ
              (hA.lauf (RufLaufG.einzeln hs1)))
        · cases hex
      · cases hex
  | _, _, _, _, .regReadElse r hk zusage sonst rest, hb => by
      intro σ σ' ρ v hex M k hZ hΛ hA
      obtain ⟨_, hr, hs, _⟩ := hb.regLiesElse_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i w hw
        split at hex
        · rename_i hw0
          obtain ⟨M1, hs1, hZ1⟩ := w_regLiesElseWahr (P := P) (O := O) (passes := passes)
            hZ.1 r hk zusage sonst rest k ρ rfl w (by rw [hW]; exact hw)
            (by rw [hW]; exact hw0)
          rw [hW] at hZ1
          exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
            (blockRet rest hr _ _ _ _ (schrumpf_zurueck hex) M1 _ hZ1 (heldGenau_lese _ hΛ)
              (hA.lauf (RufLaufG.einzeln hs1)))
        · rename_i hw0
          obtain ⟨M1, hs1, hZ1⟩ := w_regLiesElseFalsch (P := P) (O := O) (passes := passes)
            hZ.1 r hk zusage sonst rest k ρ rfl w (by rw [hW]; exact hw)
            (by rw [hW]; simpa using hw0)
          rw [hW] at hZ1
          exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
            (alsRet sonst hs _ _ _ _
              (by rw [Endblock.execBlock_alsBlock, zuAusgang_zurueck hex]; rfl) M1 _ hZ1
              (heldGenau_lese _ hΛ)
              (hA.lauf (RufLaufG.einzeln hs1)))
      · cases hex
  | _, _, _, _, .awaits g payload hp hL hat rest, hb => by
      intro σ σ' ρ v hex M k hZ hΛ hA
      have hr := hb.awaits_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i hvis
        obtain ⟨M1, hs1, hZ1⟩ := w_awaits (P := P) (O := O) (passes := passes) hZ.1
          g payload hp hL hat rest k ρ rfl (by rw [hW]; exact hvis)
        rw [hW] at hZ1
        exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
          (blockRet rest hr _ _ _ _ (schrumpf_zurueck hex) M1 _ hZ1 (heldGenau_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
      · cases hex
  | _, _, Λ₀, _, .exchange g neuE hw hL rest, hb => by
      intro σ σ' ρ v hex M k hZ hΛ hA
      have hr := hb.exchange_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      obtain ⟨M1, hs1, hZ1⟩ := w_exchange (P := P) (O := O) (passes := passes) hZ.1
        g neuE hw hL rest k ρ rfl
      rw [hW] at hZ1
      have herw := (Erw.lese σ Λ₀ (.inr g :: neuE.orte)).trans
        (Erw.schreibGlob _ g Λ₀ (eval (σ.lese Λ₀ (.inr g :: neuE.orte)) neuE
          (σ.lese Λ₀ (.inr g :: neuE.orte))
          (.cons ((σ.lese Λ₀ (.inr g :: neuE.orte)).globs g) ρ)))
      exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
        (blockRet rest hr _ _ _ _ (schrumpf_zurueck hex) M1 _ hZ1
          (by rw [herw.offen]; exact hΛ) (hA.lauf (RufLaufG.einzeln hs1)))
  | _, _, _, _, .narrow e lo' hi' sonst rest, hb => by
      intro σ σ' ρ v hex M k hZ hΛ hA
      obtain ⟨_, hr, hs, _⟩ := hb.narrow_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i hin
        obtain ⟨M1, hs1, hZ1⟩ := w_narrowOk (P := P) (O := O) (passes := passes) hZ.1
          lo' hi' e sonst rest k ρ rfl hW hin
        exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
          (blockRet rest hr _ _ _ _ (schrumpf_zurueck hex) M1 _ hZ1 (heldGenau_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
      · rename_i hin
        obtain ⟨M1, hs1, hZ1⟩ := w_narrowElse (P := P) (O := O) (passes := passes) hZ.1
          lo' hi' e sonst rest k ρ rfl (by rw [hW]; exact hin)
        rw [hW] at hZ1
        exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
          (alsRet sonst hs _ _ _ _
              (by rw [Endblock.execBlock_alsBlock, zuAusgang_zurueck hex]; rfl) M1 _ hZ1
              (heldGenau_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
  | _, _, _, _, .check c sonst rest, hb => by
      intro σ σ' ρ v hex M k hZ hΛ hA
      obtain ⟨_, hr, hs, _⟩ := hb.pruefung_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i hc
        obtain ⟨M1, hs1, hZ1⟩ := w_pruefWahr (P := P) (O := O) (passes := passes) hZ.1
          c sonst rest k ρ rfl (by rw [hW]; exact hc)
        rw [hW] at hZ1
        exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
          (blockRet rest hr _ _ _ _ hex M1 _ hZ1 (heldGenau_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
      · rename_i hc
        obtain ⟨M1, hs1, hZ1⟩ := w_pruefFalsch (P := P) (O := O) (passes := passes) hZ.1
          c sonst rest k ρ rfl (by rw [hW]; simpa using hc)
        rw [hW] at hZ1
        exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
          (alsRet sonst hs _ _ _ _
              (by rw [Endblock.execBlock_alsBlock, zuAusgang_zurueck hex]; rfl) M1 _ hZ1
              (heldGenau_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
  | _, _, _, _, .float op a b lo hi rest, hb => by
      intro σ σ' ρ v hex M k hZ hΛ hA
      have hr := hb.gleit_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i w hw
        obtain ⟨M1, hs1, hZ1⟩ := w_gleit (P := P) (O := O) (passes := passes) hZ.1
          op a b lo hi rest k ρ rfl w (by rw [hW]; exact hw)
        rw [hW] at hZ1
        exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
          (blockRet rest hr _ _ _ _ (schrumpf_zurueck hex) M1 _ hZ1 (heldGenau_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
      · cases hex
  | _, _, _, _, .floatLit q lo hi rest, hb => by
      intro σ σ' ρ v hex M k hZ hΛ hA
      have hr := hb.gleitLit_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i w hw
        obtain ⟨M1, hs1, hZ1⟩ := w_gleitLit (P := P) (O := O) (passes := passes) hZ.1
          q lo hi rest k ρ rfl w hw
        rw [hW] at hZ1
        exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
          (blockRet rest hr _ _ _ _ (schrumpf_zurueck hex) M1 _ hZ1 hΛ
            (hA.lauf (RufLaufG.einzeln hs1)))
      · cases hex
  | _, _, _, _, .floatOf e lo hi rest, hb => by
      intro σ σ' ρ v hex M k hZ hΛ hA
      have hr := hb.gleitVon_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i w hw
        obtain ⟨M1, hs1, hZ1⟩ := w_gleitVon (P := P) (O := O) (passes := passes) hZ.1
          e lo hi rest k ρ rfl w (by rw [hW]; exact hw)
        rw [hW] at hZ1
        exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
          (blockRet rest hr _ _ _ _ (schrumpf_zurueck hex) M1 _ hZ1 (heldGenau_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
      · cases hex
  | _, _, _, _, .floatNarrow e lo hi sonst rest, hb => by
      intro σ σ' ρ v hex M k hZ hΛ hA
      obtain ⟨_, hr, hs, _⟩ := hb.gleitNarrow_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i w hw
        obtain ⟨M1, hs1, hZ1⟩ := w_gleitNarrowOk (P := P) (O := O) (passes := passes) hZ.1
          e lo hi sonst rest k ρ rfl w (by rw [hW]; exact hw)
        rw [hW] at hZ1
        exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
          (blockRet rest hr _ _ _ _ (schrumpf_zurueck hex) M1 _ hZ1 (heldGenau_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
      · rename_i hn
        obtain ⟨M1, hs1, hZ1⟩ := w_gleitNarrowElse (P := P) (O := O) (passes := passes) hZ.1
          e lo hi sonst rest k ρ rfl (by rw [hW]; exact hn)
        rw [hW] at hZ1
        exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
          (alsRet sonst hs _ _ _ _
              (by rw [Endblock.execBlock_alsBlock, zuAusgang_zurueck hex]; rfl) M1 _ hZ1
              (heldGenau_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))

theorem endRet : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e : Endblock D (vertragVon D fn) l Γ Λ), EndG A e →
    SimRetE P O passes f fn caller rst rho s0 log A e
  | _, _, _, .ret e hperm, he => by
      intro σ σ' ρ v hex M hZ hΛ _
      have hl := he.ret_inv
      subst hl
      have hW := hZ.welt
      simp only [execEnd, EndAusgang.zurueck.injEq] at hex
      obtain ⟨rfl, rfl⟩ := hex
      obtain ⟨M1, hs1, hG⟩ := w_rueck (P := P) (O := O) (passes := passes) hZ.1
        caller rst rfl e hperm ρ rfl hΛ.heldIn hnw
      rw [hW] at hG
      exact ⟨M1, RufLaufG.einzeln hs1, hG⟩
  | _, _, _, .retWhy .., he => by cases he
  | _, _, _, .leave .., he => by cases he
  | _, _, _, .next .., he => by cases he
  | _, _, _, .cons s rest, he => by
      intro σ σ' ρ v hex M hZ hΛ hA
      obtain ⟨hs, hr, hl⟩ := he.cons_inv
      rcases execEnd_cons_zurueck O passes keinRuf s rest hex with h | ⟨σ1, ρ1, h1, h2⟩
      · exact endeConsRet P O passes f fn caller rst rho s0 log A hnw hs hl (stmtRet s hs)
          σ σ' ρ v h M rest hZ hΛ hA
      · obtain ⟨M1, hl1, hZ1, ho1⟩ := endeConsOk P O passes f fn (caller :: rst) rho s0 log A
          hs (stmtOk P O passes f fn (caller :: rst) rho s0 log A s hs) σ σ1 ρ ρ1 h1 M rest
          hZ hΛ hA
        have hΛ1 := heldGenau_iff (s.held_iff) hΛ
        rw [← ho1] at hΛ1
        exact gepoppt_lauf P O passes f fn caller rst rho s0 log hl1
          (endRet rest hr _ _ _ _ h2 M1 hZ1 hΛ1 (hA.lauf hl1))
  | _, _, _, .bind e rest, he => by
      intro σ σ' ρ v hex M hZ hΛ hA
      have hr := he.bind_inv
      have hW := hZ.welt
      simp only [execEnd] at hex
      obtain ⟨M1, hs1, hZ1⟩ := w_endeBind (P := P) (O := O) (passes := passes) hZ.1
        e rest ρ rfl
      rw [hW] at hZ1
      exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
        (endRet rest hr _ _ _ _ (endSchrumpf_zurueck hex) M1 hZ1 (heldGenau_lese _ hΛ)
          (hA.lauf (RufLaufG.einzeln hs1)))

/-- A covered end block run as a BLOCK (the residue of an `else` branch,
    `Endblock.alsBlock`) returns on the machine as the end block does. -/
theorem alsRet : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e : Endblock D (vertragVon D fn) l Γ Λ), EndG A e →
    SimRetB P O passes f fn caller rst rho s0 log A e.alsBlock.2
  | _, _, _, .ret e hperm, he => by
      intro σ σ' ρ v hex M k hZ hΛ hA
      have hl := he.ret_inv
      subst hl
      have hW := hZ.welt
      simp only [Endblock.alsBlock, execBlock, execStmt, Ausgang.zurueck.injEq] at hex
      obtain ⟨rfl, rfl⟩ := hex
      obtain ⟨M1, hs1, hG⟩ := w_dannRet (P := P) (O := O) (passes := passes) hZ.1
        caller rst rfl e hperm .nil k ρ rfl hΛ.heldIn hnw
      rw [hW] at hG
      exact ⟨M1, RufLaufG.einzeln hs1, hG⟩
  | _, _, _, .retWhy .., he => by cases he
  | _, _, _, .leave .., he => by cases he
  | _, _, _, .next .., he => by cases he
  | _, _, _, .cons s rest, he => by
      intro σ σ' ρ v hex M k hZ hΛ hA
      obtain ⟨hs, hr, _⟩ := he.cons_inv
      rcases execBlock_cons_zurueck O passes keinRuf s _ hex with h | ⟨σ1, ρ1, h1, h2⟩
      · exact stmtRet s hs _ _ _ _ h M _ k hZ hΛ hA
      · obtain ⟨M1, hl1, hZ1, ho1⟩ := stmtOk P O passes f fn (caller :: rst) rho s0 log A
          s hs _ _ _ _ h1 M _ k hZ hΛ hA
        have hΛ1 := heldGenau_iff (s.held_iff) hΛ
        rw [← ho1] at hΛ1
        exact gepoppt_lauf P O passes f fn caller rst rho s0 log hl1
          (alsRet rest hr _ _ _ _ h2 M1 k hZ1 hΛ1 (hA.lauf hl1))
  | _, _, _, .bind e rest, he => by
      intro σ σ' ρ v hex M k hZ hΛ hA
      have hr := he.bind_inv
      have hW := hZ.welt
      simp only [Endblock.alsBlock, execBlock] at hex
      obtain ⟨M1, hs1, hZ1⟩ := w_dannBind (P := P) (O := O) (passes := passes) hZ.1
        e _ k ρ rfl
      rw [hW] at hZ1
      exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
        (alsRet rest hr _ _ _ _ (schrumpf_zurueck hex) M1 _ hZ1 (heldGenau_lese _ hΛ)
          (hA.lauf (RufLaufG.einzeln hs1)))

theorem armsRet : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} (arms : Arms D (vertragVon D fn) l Γ Λ Λ' cs),
    ArmsG A true arms → ∀ (v : Wert D (.sum cs)),
    SimRetB P O passes f fn caller rst rho s0 log A (armWahlG arms v).2.1
  | _, _, _, _, _, .nil, _, ⟨⟨k, hk⟩, _⟩ => (Nat.not_lt_zero k hk).elim
  | _, _, _, _, _, .cons b _, ha, ⟨⟨0, _⟩, _⟩ => blockRet b ha.cons_inv.1
  | _, _, _, _, _, .cons _ rest, ha, ⟨⟨_ + 1, _⟩, _⟩ => armsRet rest ha.cons_inv.2 _

theorem grundRet : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D (vertragVon D fn) l Γ Λ Λ' n), GrundArmsG A true arms →
    ∀ (r : Fin n), SimRetB P O passes f fn caller rst rho s0 log A (grundWahlG arms r)
  | _, _, _, _, _, .nil, _, ⟨k, hk⟩ => (Nat.not_lt_zero k hk).elim
  | _, _, _, _, _, .cons b _, ha, ⟨0, _⟩ => blockRet b ha.cons_inv.1
  | _, _, _, _, _, .cons _ rest, ha, ⟨_ + 1, _⟩ => grundRet rest ha.cons_inv.2 _

end

end SimRet

end Gabbro.Grammatik
