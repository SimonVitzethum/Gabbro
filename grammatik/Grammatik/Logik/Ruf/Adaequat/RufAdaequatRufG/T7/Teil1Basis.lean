/- Part 7 of 10 of `RufAdaequatRufG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufAdaequatRufG.lean` imports all parts). -/
module
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T6
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

section SimRet

variable (P : Programm D) (O : Orakel D) (passes : Nat) (f : Faden) (fn : D.Fn)
  (caller : RufRahmenG D) (rst : List (RufRahmenG D)) (rho : Env D (D.params fn))
  (s0 : World D) (A : D.Lock → Prop)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (C : D.Fn → Prop)
  (ziel : ErgVal D (D.erg fn) → RufRahmenG D) (zielG : Fin (D.gruende fn) → RufRahmenG D)

/-- Block simulation, frame end: `dann b k` pops the frame with the end
    `execBlock` produces, resuming the caller as the end's pop says. -/
def SimRetBR {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D (vertragVon D fn) l Γ Λ Λ') : Prop :=
  ∀ (log : List (RufEreignisF D)) (σ : World D) (ρ : Env D Γ) (e : EndeW (vertragVon D fn)),
    PopFuer fn caller ziel zielG e → (execBlock O passes R b σ ρ).ende? = some e →
  ∀ (M : RufMaschineG D) (k : GRest D (vertragVon D fn) l Γ Λ'),
    ZustandG M f (caller :: rst) fn rho s0 log ρ (.dann b k) σ →
    HeldB (vertragVon D fn).boden Λ (offen σ.spur) → FreiA A M f →
    ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
      GepopptE M' f ziel zielG rst rho s0 (ext ++ log) e ∧ offen e.welt.spur = offen σ.spur

/-- Statement simulation, frame end, at `dann (s; rest) k`. -/
def SimRetSR {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D (vertragVon D fn) l Γ Λ Λ') : Prop :=
  ∀ (log : List (RufEreignisF D)) (σ : World D) (ρ : Env D Γ) (e : EndeW (vertragVon D fn)),
    PopFuer fn caller ziel zielG e → (execStmt O passes R s σ ρ).ende? = some e →
  ∀ (M : RufMaschineG D) {Λ'' : List (Res D)}
    (rest : Block D (vertragVon D fn) l Γ Λ' Λ'') (k : GRest D (vertragVon D fn) l Γ Λ''),
    ZustandG M f (caller :: rst) fn rho s0 log ρ (.dann (.cons s rest) k) σ →
    HeldB (vertragVon D fn).boden Λ (offen σ.spur) → FreiA A M f →
    ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
      GepopptE M' f ziel zielG rst rho s0 (ext ++ log) e ∧ offen e.welt.spur = offen σ.spur

/-- End-block simulation, frame end, at `ende e`. -/
def SimRetER {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (eb : Endblock D (vertragVon D fn) l Γ Λ) : Prop :=
  ∀ (log : List (RufEreignisF D)) (σ : World D) (ρ : Env D Γ) (e : EndeW (vertragVon D fn)),
    PopFuer fn caller ziel zielG e → (execEnd O passes R eb σ ρ).ende? = some e →
  ∀ (M : RufMaschineG D),
    ZustandG M f (caller :: rst) fn rho s0 log ρ (.ende eb) σ →
    HeldB (vertragVon D fn).boden Λ (offen σ.spur) → FreiA A M f →
    ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
      GepopptE M' f ziel zielG rst rho s0 (ext ++ log) e ∧ offen e.welt.spur = offen σ.spur

theorem blattRetR {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {s : Stmt D (vertragVon D fn) l Γ Λ Λ'} (h : BlattG s) :
    SimRetSR P O passes f fn caller rst rho s0 A R ziel zielG s := by
  intro log σ ρ e _ hex
  rw [h.ende_none O passes R σ ρ] at hex
  cases hex

/-- A call statement never ends the frame (`execStmt` of a call is `ok`,
    `logik` or `hardware`). -/
theorem call_ende_none {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {g : D.Fn} {args : Args D Γ Λ (D.params g)} {hp : RufPasst D V (D.signatur g) Λ}
    {hr : D.gruende g = 0} (σ : World D) (ρ : Env D Γ) :
    (execStmt O passes R (.call (l := l) g args hp hr) σ ρ).ende? = none := by
  simp only [execStmt]
  split
  · rfl
  · exact (Fin.cast hr ‹_›).elim0
  · rfl
  · rfl

/-- A covered call statement never ends the frame. -/
theorem stmtR_call_ende_none {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {s : Stmt D V l Γ Λ Λ'} {g : D.Fn} (hg : s.rufZiel = some g) (σ : World D)
    (ρ : Env D Γ) : (execStmt O passes R s σ ρ).ende? = none := by
  cases s with
  | call => exact call_ende_none O passes R σ ρ
  | _ => simp only [Stmt.rufZiel, reduceCtorEq] at hg

/-- Lift a pop after one step. -/
theorem gepoppt_vorR {M M1 : RufMaschineG D} {log : List (RufEreignisF D)}
    {e : EndeW (vertragVon D fn)} {σ σ1 : World D}
    (hs : RufSchrittG P O passes M f M1) (ho : offen σ1.spur = offen σ.spur)
    (h : ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M1 M' ∧
      GepopptE M' f ziel zielG rst rho s0 (ext ++ log) e ∧ offen e.welt.spur = offen σ1.spur) :
    ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
      GepopptE M' f ziel zielG rst rho s0 (ext ++ log) e ∧ offen e.welt.spur = offen σ.spur := by
  obtain ⟨M', ext, hr, hG, ho'⟩ := h
  exact ⟨M', ext, RufLaufG.schritt hs hr, hG, by rw [ho', ho]⟩

/-- Lift a pop after a run that logged `e1`. -/
theorem gepoppt_laufR {M M1 : RufMaschineG D} {log e1 : List (RufEreignisF D)}
    {e : EndeW (vertragVon D fn)} {σ σ1 : World D}
    (hl : RufLaufG P O passes f M M1) (ho : offen σ1.spur = offen σ.spur)
    (h : ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M1 M' ∧
      GepopptE M' f ziel zielG rst rho s0 (ext ++ (e1 ++ log)) e ∧
      offen e.welt.spur = offen σ1.spur) :
    ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
      GepopptE M' f ziel zielG rst rho s0 (ext ++ log) e ∧ offen e.welt.spur = offen σ.spur := by
  obtain ⟨M', ext, hr, hG, ho'⟩ := h
  exact ⟨M', ext ++ e1, hl.trans hr, by rw [List.append_assoc]; exact hG, by rw [ho', ho]⟩

/-- A statement at `ende (s; rest)` that ends the frame: `rueckCons` (or its
    bind form) for `ret`, `rueckConsGrund` for `retGrund`, `endeEntf` and
    the `dann` simulation for a compound. -/
theorem endeConsRetR {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {log : List (RufEreignisF D)}
    {s : Stmt D (vertragVon D fn) l Γ Λ Λ'} (hs : StmtR A C true s)
    (hret : SimRetSR P O passes f fn caller rst rho s0 A R ziel zielG s)
    (σ : World D) (ρ : Env D Γ) (e : EndeW (vertragVon D fn))
    (hpe : PopFuer fn caller ziel zielG e)
    (hex : (execStmt O passes R s σ ρ).ende? = some e) (M : RufMaschineG D)
    (rest : Endblock D (vertragVon D fn) l Γ Λ')
    (hZ : ZustandG M f (caller :: rst) fn rho s0 log ρ (.ende (.cons s rest)) σ)
    (hΛ : HeldB (vertragVon D fn).boden Λ (offen σ.spur)) (hA : FreiA A M f) :
    ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
      GepopptE M' f ziel zielG rst rho s0 (ext ++ log) e ∧ offen e.welt.spur = offen σ.spur := by
  have hW := hZ.welt
  have hEntf : ∀ (hent : GEntfaltbar s = true),
      ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
        GepopptE M' f ziel zielG rst rho s0 (ext ++ log) e ∧
        offen e.welt.spur = offen σ.spur := by
    intro hent
    obtain ⟨M1, hs1, hZ1⟩ := w_endeEntf (P := P) (O := O) (passes := passes) hZ.1
      s rest ρ hent rfl
    rw [hW] at hZ1
    exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 rfl
      (hret log σ ρ e hpe hex M1 .nil (.ende rest) hZ1 hΛ (hA.lauf (RufLaufG.einzeln hs1)))
  cases hs with
  | blatt _ h => rw [h.ende_none O passes R σ ρ] at hex; cases hex
  | call _ g hg _ => rw [stmtR_call_ende_none O passes R hg σ ρ] at hex; cases hex
  | ret e' hperm =>
    simp only [execStmt, Ausgang.ende?, Option.some.injEq] at hex
    subst hex
    obtain ⟨M1, hs1, hG⟩ := w_rueckConsP (P := P) (O := O) (passes := passes) hZ.1
      caller rst rfl hpe e' hperm rest ρ rfl hΛ.heldIn
    rw [hW] at hG
    exact ⟨M1, [], RufLaufG.einzeln hs1, hG, (Erw.lese _ _ _).offen⟩
  | retWhy r hperm =>
    simp only [execStmt, Ausgang.ende?, Option.some.injEq] at hex
    subst hex
    obtain ⟨M1, hs1, hG⟩ := w_rueckConsGrundP (P := P) (O := O) (passes := passes) hZ.1
      caller rst rfl hpe r hperm rest ρ rfl hΛ.heldIn
    rw [hW] at hG
    exact ⟨M1, [], RufLaufG.einzeln hs1, hG, rfl⟩
  | leave _ => simp only [Ausgang.ende?, execStmt, reduceCtorEq] at hex
  | next _ => simp only [Ausgang.ende?, execStmt, reduceCtorEq] at hex
  | ite => exact hEntf rfl
  | onOption => exact hEntf rfl
  | onTag => exact hEntf rfl
  | onWhy => exact hEntf rfl
  | breaking => exact hEntf rfl
  | locks => exact hEntf rfl
  | traverse => exact hEntf rfl
  | retry => exact hEntf rfl
  | forever => exact hEntf rfl


end SimRet
end Gabbro.Grammatik
