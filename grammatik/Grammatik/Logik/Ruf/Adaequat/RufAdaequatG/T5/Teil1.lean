module

public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.T4

@[expose] public section



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

end SimRet
end Gabbro.Grammatik
