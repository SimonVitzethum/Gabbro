/- Part 7 of 10 of `RufAdaequatRufG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufAdaequatRufG.lean` imports all parts). -/
import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T6

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
  | _ => simp [Stmt.rufZiel] at hg

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
  | leave _ => simp [execStmt, Ausgang.ende?] at hex
  | next _ => simp [execStmt, Ausgang.ende?] at hex
  | ite => exact hEntf rfl
  | onOption => exact hEntf rfl
  | onTag => exact hEntf rfl
  | onWhy => exact hEntf rfl
  | breaking => exact hEntf rfl
  | locks => exact hEntf rfl
  | traverse => exact hEntf rfl
  | retry => exact hEntf rfl
  | forever => exact hEntf rfl

/-- **The loop of a `traverse`, frame end.** From `trav t inv body ks k` the
    machine pops the frame exactly as `traverseLauf` over `ks` ends it: the
    iterations before by the normal-completion and `next` simulations of
    the body, the ending one by its end simulation. -/
theorem travRetR {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D (vertragVon D fn) true (.index (D.count t) :: Γ) Λ Λ)
    (hbodyOk : SimOkBR P O passes f fn (caller :: rst) rho s0 A R body)
    (hbodyA : SimAbbBR P O passes f fn (caller :: rst) rho s0 A R body)
    (hbodyRet : SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG body)
    (k : GRest D (vertragVon D fn) l Γ Λ) :
    ∀ (ks : List (Wert D (.index (D.count t)))) (log : List (RufEreignisF D))
      (σ : World D) (ρ : Env D Γ) (e : EndeW (vertragVon D fn)),
      PopFuer fn caller ziel zielG e →
      (traverseLauf (l := l) (fun σ ρ => execBlock O passes R body σ ρ)
        (fun σ ρ => ((σ.lese Λ inv.orte), wahr? (eval (σ.lese Λ inv.orte) inv
          (σ.lese Λ inv.orte) ρ))) ks σ ρ).ende? = some e →
      ∀ (M : RufMaschineG D),
        ZustandG M f (caller :: rst) fn rho s0 log ρ (.trav t inv body ks k) σ →
        HeldB (vertragVon D fn).boden Λ (offen σ.spur) → FreiA A M f →
        ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
          GepopptE M' f ziel zielG rst rho s0 (ext ++ log) e ∧ offen e.welt.spur = offen σ.spur
  | [], log, σ, ρ, e, _, hex, M, hZ, _, _ => by
      simp only [traverseLauf] at hex
      split at hex <;> simp [Ausgang.ende?] at hex
  | i :: is, log, σ, ρ, e, hpe, hex, M, hZ, hΛ, hA => by
      have hW := hZ.welt
      simp only [traverseLauf] at hex
      split at hex
      · simp [Ausgang.ende?] at hex
      · rename_i hw
        have hw' : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true := by
          simpa using hw
        obtain ⟨M1, hs1, hZ1⟩ := w_travNext (P := P) (O := O) (passes := passes) hZ.1
          t inv body i is k ρ rfl (by rw [hW]; exact hw')
        rw [hW] at hZ1
        have hA1 := hA.lauf (RufLaufG.einzeln hs1)
        have hΛ1 := heldB_lese inv.orte hΛ (Λ₀ := Λ)
        have weiter : ∀ (M3 : RufMaschineG D) (e3 : List (RufEreignisF D)) (σ2 : World D)
            (ρt : Env D Γ), RufLaufG P O passes f M M3 →
            ZustandG M3 f (caller :: rst) fn rho s0 (e3 ++ log) ρt (.trav t inv body is k) σ2 →
            offen σ2.spur = offen σ.spur →
            (traverseLauf (l := l) (fun σ ρ => execBlock O passes R body σ ρ)
              (fun σ ρ => ((σ.lese Λ inv.orte), wahr? (eval (σ.lese Λ inv.orte) inv
                (σ.lese Λ inv.orte) ρ))) is σ2 ρt).ende? = some e →
            ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
              GepopptE M' f ziel zielG rst rho s0 (ext ++ log) e ∧
              offen e.welt.spur = offen σ.spur := by
          intro M3 e3 σ2 ρt hl3 hZ3 ho3 hex3
          have hΛ3 : HeldB (vertragVon D fn).boden Λ (offen σ2.spur) := by rw [ho3]; exact hΛ
          exact gepoppt_laufR P O passes f fn rst rho s0 ziel zielG hl3 ho3
            (travRetR t inv body hbodyOk hbodyA hbodyRet k is _ σ2 ρt e hpe hex3 M3 hZ3 hΛ3
              (hA.lauf hl3))
        split at hex
        · rename_i σ2 ρ2 hb2
          obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := hbodyOk log _ _ _ _ hb2 M1 _ hZ1 hΛ1 hA1
          cases ρ2 with
          | cons i2 ρt =>
            have hW2 := hZ2.welt
            obtain ⟨M3, hs3, hZ3⟩ := w_travFort (P := P) (O := O) (passes := passes) hZ2.1
              t inv body is k i2 ρt rfl
            rw [hW2] at hZ3
            exact weiter M3 e2 σ2 ρt (RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)))
              hZ3 (by rw [ho2, (Erw.lese _ _ _).offen]) hex
        · rename_i h2 σ2 ρ2 hb2
          obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := hbodyA rfl log _ _ _ _ false
            (by rw [hb2]; rfl) M1 _ hZ1 hΛ1 hA1
          cases ρ2 with
          | cons i2 ρt =>
            have hW2 := hZ2.welt
            obtain ⟨M3, hs3, hZ3⟩ := w_nextTrav (P := P) (O := O) (passes := passes) hZ2.1
              t inv body is k r i2 ρt rfl (show HeldIn _ (offen σ2.spur) from (heldB_block r (by rw [ho2]; exact hΛ1)).heldIn)
            rw [hW2] at hZ3
            exact weiter M3 e2 σ2 ρt (RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)))
              hZ3 (by rw [ho2, (Erw.lese _ _ _).offen]) hex
        · split at hex <;> simp [Ausgang.ende?] at hex
        · rename_i σ2 v2 hb2
          exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
            (hbodyRet log _ _ e hpe (by rw [hb2]; exact hex) M1 _ hZ1 hΛ1 hA1)
        · rename_i σ2 r2 hb2
          exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
            (hbodyRet log _ _ e hpe (by rw [hb2]; exact hex) M1 _ hZ1 hΛ1 hA1)
        all_goals simp [Ausgang.ende?] at hex

/-- **The loop of a `retry`, frame end.** As `travRetR`, for `retryLauf`;
    the overflow block may end the frame too. -/
theorem retryRetR {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (bis : Expr D Γ Λ .bool)
    (body : Block D (vertragVon D fn) true Γ Λ Λ) (ueber : Block D (vertragVon D fn) l Γ Λ Λ)
    (hbodyOk : SimOkBR P O passes f fn (caller :: rst) rho s0 A R body)
    (hbodyA : SimAbbBR P O passes f fn (caller :: rst) rho s0 A R body)
    (hbodyRet : SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG body)
    (hueberRet : SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG ueber)
    (k : GRest D (vertragVon D fn) l Γ Λ) :
    ∀ (n : Nat) (log : List (RufEreignisF D)) (σ : World D) (ρ : Env D Γ)
      (e : EndeW (vertragVon D fn)), PopFuer fn caller ziel zielG e →
      (retryLauf (fun σ ρ => execBlock O passes R body σ ρ)
        (fun σ ρ => ((σ.lese Λ bis.orte), wahr? (eval (σ.lese Λ bis.orte) bis
          (σ.lese Λ bis.orte) ρ)))
        (fun σ ρ => execBlock O passes R ueber σ ρ) n σ ρ).ende? = some e →
      ∀ (M : RufMaschineG D),
        ZustandG M f (caller :: rst) fn rho s0 log ρ (.wieder n bis body ueber k) σ →
        HeldB (vertragVon D fn).boden Λ (offen σ.spur) → FreiA A M f →
        ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
          GepopptE M' f ziel zielG rst rho s0 (ext ++ log) e ∧ offen e.welt.spur = offen σ.spur
  | 0, log, σ, ρ, e, hpe, hex, M, hZ, hΛ, hA => by
      have hW := hZ.welt
      simp only [retryLauf] at hex
      split at hex
      · simp [Ausgang.ende?] at hex
      · rename_i hw
        have hw' : wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ) = false := by
          simpa using hw
        obtain ⟨M1, hs1, hZ1⟩ := w_wiederUeber (P := P) (O := O) (passes := passes) hZ.1
          bis body ueber k ρ rfl
        rw [hW] at hZ1
        have hW1 := hZ1.welt
        obtain ⟨M2, hs2, hZ2⟩ := w_iteFalsch (P := P) (O := O) (passes := passes) hZ1.1
          bis .nil ueber .nil k ρ rfl (by rw [hW1]; exact hw')
        rw [hW1] at hZ2
        exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 rfl
          (gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs2 (Erw.lese _ _ _).offen
            (hueberRet log _ _ e hpe hex M2 _ hZ2 (heldB_lese bis.orte hΛ (Λ₀ := Λ))
              ((hA.lauf (RufLaufG.einzeln hs1)).lauf (RufLaufG.einzeln hs2))))
  | n + 1, log, σ, ρ, e, hpe, hex, M, hZ, hΛ, hA => by
      have hW := hZ.welt
      simp only [retryLauf] at hex
      split at hex
      · simp [Ausgang.ende?] at hex
      · rename_i hw
        have hw' : wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ) = false := by
          simpa using hw
        obtain ⟨M1, hs1, hZ1⟩ := w_wiederSchritt (P := P) (O := O) (passes := passes) hZ.1
          n bis body ueber k ρ rfl (by rw [hW]; exact hw')
        rw [hW] at hZ1
        have hA1 := hA.lauf (RufLaufG.einzeln hs1)
        have hΛ1 := heldB_lese bis.orte hΛ (Λ₀ := Λ)
        have weiter : ∀ (M3 : RufMaschineG D) (e3 : List (RufEreignisF D)) (σ2 : World D)
            (ρ2 : Env D Γ), RufLaufG P O passes f M M3 →
            ZustandG M3 f (caller :: rst) fn rho s0 (e3 ++ log) ρ2 (.wieder n bis body ueber k) σ2 →
            offen σ2.spur = offen σ.spur →
            (retryLauf (fun σ ρ => execBlock O passes R body σ ρ)
              (fun σ ρ => ((σ.lese Λ bis.orte), wahr? (eval (σ.lese Λ bis.orte) bis
                (σ.lese Λ bis.orte) ρ)))
              (fun σ ρ => execBlock O passes R ueber σ ρ) n σ2 ρ2).ende? = some e →
            ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
              GepopptE M' f ziel zielG rst rho s0 (ext ++ log) e ∧
              offen e.welt.spur = offen σ.spur := by
          intro M3 e3 σ2 ρ2 hl3 hZ3 ho3 hex3
          have hΛ3 : HeldB (vertragVon D fn).boden Λ (offen σ2.spur) := by rw [ho3]; exact hΛ
          exact gepoppt_laufR P O passes f fn rst rho s0 ziel zielG hl3 ho3
            (retryRetR bis body ueber hbodyOk hbodyA hbodyRet hueberRet k n _ σ2 ρ2 e hpe hex3 M3
              hZ3 hΛ3 (hA.lauf hl3))
        split at hex
        · rename_i σ2 ρ2 hb2
          obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := hbodyOk log _ _ _ _ hb2 M1 _ hZ1 hΛ1 hA1
          have hW2 := hZ2.welt
          obtain ⟨M3, hs3, hZ3⟩ := w_wiederFort (P := P) (O := O) (passes := passes) hZ2.1
            n bis body ueber k ρ2 rfl
          rw [hW2] at hZ3
          exact weiter M3 e2 σ2 ρ2 (RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)))
            hZ3 (by rw [ho2, (Erw.lese _ _ _).offen]) hex
        · rename_i h2 σ2 ρ2 hb2
          obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := hbodyA rfl log _ _ _ _ false
            (by rw [hb2]; rfl) M1 _ hZ1 hΛ1 hA1
          have hW2 := hZ2.welt
          obtain ⟨M3, hs3, hZ3⟩ := w_abbWieder (P := P) (O := O) (passes := passes) hZ2.1
            false n bis body ueber k r ρ2 rfl (show HeldIn _ (offen σ2.spur) from (heldB_block r (by rw [ho2]; exact hΛ1)).heldIn)
          rw [hW2] at hZ3
          exact weiter M3 e2 σ2 ρ2 (RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)))
            hZ3 (by rw [ho2, (Erw.lese _ _ _).offen]) hex
        · simp [Ausgang.ende?] at hex
        · rename_i σ2 v2 hb2
          exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
            (hbodyRet log _ _ e hpe (by rw [hb2]; exact hex) M1 _ hZ1 hΛ1 hA1)
        · rename_i σ2 r2 hb2
          exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
            (hbodyRet log _ _ e hpe (by rw [hb2]; exact hex) M1 _ hZ1 hΛ1 hA1)
        all_goals simp [Ausgang.ende?] at hex

/-- **The loop of a `forever`, frame end.** As `travRetR`, for
    `foreverLauf`: passes end normally or by `next` until one ends the
    frame. -/
theorem foreverRetR {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (a : D.Annahme)
    (inv : Expr D Γ Λ .bool) (body : Block D (vertragVon D fn) true Γ Λ Λ)
    (hbodyOk : SimOkBR P O passes f fn (caller :: rst) rho s0 A R body)
    (hbodyA : SimAbbBR P O passes f fn (caller :: rst) rho s0 A R body)
    (hbodyRet : SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG body)
    (k : GRest D (vertragVon D fn) l Γ Λ) :
    ∀ (n : Nat) (log : List (RufEreignisF D)) (σ : World D) (ρ : Env D Γ)
      (e : EndeW (vertragVon D fn)), PopFuer fn caller ziel zielG e →
      (foreverLauf (l := l) a (fun σ ρ => execBlock O passes R body σ ρ)
        (fun σ ρ => ((σ.lese Λ inv.orte), wahr? (eval (σ.lese Λ inv.orte) inv
          (σ.lese Λ inv.orte) ρ))) n σ ρ).ende? = some e →
      ∀ (M : RufMaschineG D),
        ZustandG M f (caller :: rst) fn rho s0 log ρ (.ewig a n inv body k) σ →
        HeldB (vertragVon D fn).boden Λ (offen σ.spur) → FreiA A M f →
        ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
          GepopptE M' f ziel zielG rst rho s0 (ext ++ log) e ∧ offen e.welt.spur = offen σ.spur
  | 0, log, σ, ρ, e, _, hex, M, hZ, _, _ => by
      simp [foreverLauf, Ausgang.ende?] at hex
  | n + 1, log, σ, ρ, e, hpe, hex, M, hZ, hΛ, hA => by
      have hW := hZ.welt
      simp only [foreverLauf] at hex
      split at hex
      · simp [Ausgang.ende?] at hex
      · rename_i hw
        have hw' : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true := by
          simpa using hw
        obtain ⟨M1, hs1, hZ1⟩ := w_ewigWeiter (P := P) (O := O) (passes := passes) hZ.1
          a n inv body k ρ rfl (by rw [hW]; exact hw')
        rw [hW] at hZ1
        have hA1 := hA.lauf (RufLaufG.einzeln hs1)
        have hΛ1 := heldB_lese inv.orte hΛ (Λ₀ := Λ)
        have weiter : ∀ (M3 : RufMaschineG D) (e3 : List (RufEreignisF D)) (σ2 : World D)
            (ρ2 : Env D Γ), RufLaufG P O passes f M M3 →
            ZustandG M3 f (caller :: rst) fn rho s0 (e3 ++ log) ρ2 (.ewig a n inv body k) σ2 →
            offen σ2.spur = offen σ.spur →
            (foreverLauf (l := l) a (fun σ ρ => execBlock O passes R body σ ρ)
              (fun σ ρ => ((σ.lese Λ inv.orte), wahr? (eval (σ.lese Λ inv.orte) inv
                (σ.lese Λ inv.orte) ρ))) n σ2 ρ2).ende? = some e →
            ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
              GepopptE M' f ziel zielG rst rho s0 (ext ++ log) e ∧
              offen e.welt.spur = offen σ.spur := by
          intro M3 e3 σ2 ρ2 hl3 hZ3 ho3 hex3
          have hΛ3 : HeldB (vertragVon D fn).boden Λ (offen σ2.spur) := by rw [ho3]; exact hΛ
          exact gepoppt_laufR P O passes f fn rst rho s0 ziel zielG hl3 ho3
            (foreverRetR a inv body hbodyOk hbodyA hbodyRet k n _ σ2 ρ2 e hpe hex3 M3 hZ3 hΛ3
              (hA.lauf hl3))
        split at hex
        · rename_i σ2 ρ2 hb2
          obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := hbodyOk log _ _ _ _ hb2 M1 _ hZ1 hΛ1 hA1
          have hW2 := hZ2.welt
          obtain ⟨M3, hs3, hZ3⟩ := w_ewigFort (P := P) (O := O) (passes := passes) hZ2.1
            a n inv body k ρ2 rfl
          rw [hW2] at hZ3
          exact weiter M3 e2 σ2 ρ2 (RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)))
            hZ3 (by rw [ho2, (Erw.lese _ _ _).offen]) hex
        · rename_i h2 σ2 ρ2 hb2
          obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := hbodyA rfl log _ _ _ _ false
            (by rw [hb2]; rfl) M1 _ hZ1 hΛ1 hA1
          have hW2 := hZ2.welt
          obtain ⟨M3, hs3, hZ3⟩ := w_abbEwig (P := P) (O := O) (passes := passes) hZ2.1
            false a n inv body k r ρ2 rfl (show HeldIn _ (offen σ2.spur) from (heldB_block r (by rw [ho2]; exact hΛ1)).heldIn)
          rw [hW2] at hZ3
          exact weiter M3 e2 σ2 ρ2 (RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)))
            hZ3 (by rw [ho2, (Erw.lese _ _ _).offen]) hex
        · simp [Ausgang.ende?] at hex
        · rename_i σ2 v2 hb2
          exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
            (hbodyRet log _ _ e hpe (by rw [hb2]; exact hex) M1 _ hZ1 hΛ1 hA1)
        · rename_i σ2 r2 hb2
          exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
            (hbodyRet log _ _ e hpe (by rw [hb2]; exact hex) M1 _ hZ1 hΛ1 hA1)
        all_goals simp [Ausgang.ende?] at hex

variable (hRuf : RufOk P O passes f A R C)
include hRuf

-- `hRuf` is used at calls; the arm recursions reach it only through
-- `blockRetR`, which the linter does not count as a use.
set_option maxHeartbeats 3200000 in
set_option linter.unusedSectionVars false in
mutual

theorem stmtRetR : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D (vertragVon D fn) l Γ Λ Λ'), StmtR A C true s →
    SimRetSR P O passes f fn caller rst rho s0 A R ziel zielG s
  | _, _, _, _, .assignSlot t f' i e hw hL, _ =>
      blattRetR P O passes f fn caller rst rho s0 A R ziel zielG (.assignSlot t f' i e hw hL)
  | _, _, _, _, .assignThru p t ht f' i e hw hL, _ =>
      blattRetR P O passes f fn caller rst rho s0 A R ziel zielG
        (.assignThru _ p t ht f' i e hw hL)
  | _, _, _, _, .assignSlotRef r t ht ho f' e hw hL, _ =>
      blattRetR P O passes f fn caller rst rho s0 A R ziel zielG
        (.assignSlotRef _ r t ht ho f' e hw hL)
  | _, _, _, _, .assignGlob g e hw hL, _ =>
      blattRetR P O passes f fn caller rst rho s0 A R ziel zielG (.assignGlob g e hw hL)
  | _, _, _, _, .putBytes t f' hf n i hlo hhi e hw hL, _ =>
      blattRetR P O passes f fn caller rst rho s0 A R ziel zielG
        (.putBytes t f' hf n i hlo hhi e hw hL)
  | _, _, _, _, .assignVar x e, _ =>
      blattRetR P O passes f fn caller rst rho s0 A R ziel zielG (.assignVar x e)
  | _, _, _, _, .shift t f' hτ i von nach hn he hw hL, _ =>
      blattRetR P O passes f fn caller rst rho s0 A R ziel zielG
        (.shift t f' hτ i von nach hn he hw hL)
  | _, _, _, _, .regWrite r hk e, _ =>
      blattRetR P O passes f fn caller rst rho s0 A R ziel zielG (.regWrite r hk e)
  | _, _, _, _, .transition r hk m hm hl maske bits, _ =>
      blattRetR P O passes f fn caller rst rho s0 A R ziel zielG
        (.transition r hk m hm hl maske bits)
  | _, _, _, _, .publish g e payload hp hw hL, _ =>
      blattRetR P O passes f fn caller rst rho s0 A R ziel zielG (.publish g e payload hp hw hL)
  | _, _, _, _, .advances m a h hs, _ =>
      blattRetR P O passes f fn caller rst rho s0 A R ziel zielG (.advances m a h hs)
  | _, _, _, _, .retires m s h a, _ =>
      blattRetR P O passes f fn caller rst rho s0 A R ziel zielG (.retires m s h a)
  | _, _, _, _, .ite c t e, hs => by
      intro log σ ρ E hpe hex M _ rest k hZ hΛ hA
      obtain ⟨ht, he⟩ := hs.ite_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      split at hex
      · rename_i hc
        obtain ⟨M1, hs1, hZ1⟩ := w_iteWahr (P := P) (O := O) (passes := passes) hZ.1
          c t e rest k ρ rfl (by rw [hW]; exact hc)
        rw [hW] at hZ1
        exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
          (blockRetR t ht _ _ _ _ hpe hex M1 _ hZ1 (heldB_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
      · rename_i hc
        obtain ⟨M1, hs1, hZ1⟩ := w_iteFalsch (P := P) (O := O) (passes := passes) hZ.1
          c t e rest k ρ rfl (by rw [hW]; simpa using hc)
        rw [hW] at hZ1
        exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
          (blockRetR e he _ _ _ _ hpe hex M1 _ hZ1 (heldB_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
  | _, _, _, _, .onOption o p a, hs => by
      intro log σ ρ E hpe hex M _ rest k hZ hΛ hA
      obtain ⟨hp, ha⟩ := hs.onOption_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      split at hex
      · rename_i w hw
        rw [ende_schrumpf] at hex
        obtain ⟨M1, hs1, hZ1⟩ := w_optSome (P := P) (O := O) (passes := passes) hZ.1
          o p a rest k ρ rfl w (by rw [hW]; exact hw)
        rw [hW] at hZ1
        exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
          (blockRetR p hp _ _ _ _ hpe hex M1 _ hZ1 (heldB_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
      · rename_i hw
        obtain ⟨M1, hs1, hZ1⟩ := w_optNone (P := P) (O := O) (passes := passes) hZ.1
          o p a rest k ρ rfl (by rw [hW]; exact hw)
        rw [hW] at hZ1
        exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
          (blockRetR a ha _ _ _ _ hpe hex M1 _ hZ1 (heldB_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
  | _, _, Λ₀, _, .onTag w arms, hs => by
      intro log σ ρ E hpe hex M _ rest k hZ hΛ hA
      have ha := hs.onTag_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      rw [execArms_wahl, ende_schrumpfArm] at hex
      have hsim := armsRetR arms ha (eval (σ.lese Λ₀ w.orte) w (σ.lese Λ₀ w.orte) ρ)
      generalize hwahl : armWahlG arms (eval (σ.lese Λ₀ w.orte) w (σ.lese Λ₀ w.orte) ρ) = x
        at hex hsim
      obtain ⟨c, b, nutz⟩ := x
      cases c with
      | none =>
        obtain ⟨M1, hs1, hZ1⟩ := w_tagNone (P := P) (O := O) (passes := passes) hZ.1
          w arms rest k ρ rfl b nutz (by rw [hW]; exact hwahl)
        rw [hW] at hZ1
        exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
          (hsim _ _ _ _ hpe hex M1 _ hZ1 (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1)))
      | some lh =>
        obtain ⟨lo, hi⟩ := lh
        obtain ⟨M1, hs1, hZ1⟩ := w_tagSome (P := P) (O := O) (passes := passes) hZ.1
          w arms rest k ρ rfl lo hi b nutz (by rw [hW]; exact hwahl)
        rw [hW] at hZ1
        exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
          (hsim _ _ _ _ hpe hex M1 _ hZ1 (heldB_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
  | _, _, _, _, .onWhy r arms, hs => by
      intro log σ ρ E hpe hex M _ rest k hZ hΛ hA
      have ha := hs.onGrund_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      rw [execGrund_wahlW O passes R arms] at hex
      obtain ⟨M1, hs1, hZ1⟩ := w_grund (P := P) (O := O) (passes := passes) hZ.1
        r arms rest k ρ rfl
      rw [hW] at hZ1
      exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
        (grundRetR arms ha _ _ _ _ _ hpe hex M1 _ hZ1 (heldB_lese _ hΛ)
          (hA.lauf (RufLaufG.einzeln hs1)))
  | _, _, _, _, .call g args hp hr, _ => by
      intro log σ ρ E _ hex
      rw [call_ende_none O passes R σ ρ] at hex
      cases hex
  | _, _, _, _, .callInd .., hs => absurd hs.art (by simp [Stmt.rArt, Stmt.blattArt])
  | _, _, _, _, .locks L hr body, hs => by
      intro log σ ρ E _ hex
      obtain ⟨_, hb, _⟩ := hs.locks_inv
      simp only [execStmt] at hex
      rw [ende_mapWelt_none _ (blockKeinR O passes R A C body hb _ _)] at hex
      cases hex
  | _, _, _, _, .breaking i body, hs => by
      intro log σ ρ E hpe hex M _ rest k hZ hΛ hA
      have hb := hs.breaking_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      obtain ⟨M1, hs1, hZ1⟩ := w_breaking (P := P) (O := O) (passes := passes) hZ.1
        i body rest k ρ rfl
      rw [hW] at hZ1
      exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 rfl
        (blockRetR body hb _ _ _ _ hpe hex M1 _ hZ1 hΛ (hA.lauf (RufLaufG.einzeln hs1)))
  | _, _, _, _, .traverse t inv body, hs => by
      intro log σ ρ E hpe hex M _ rest k hZ hΛ hA
      have hb := hs.traverse_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      obtain ⟨M1, hs1, hZ1⟩ := w_dannTrav (P := P) (O := O) (passes := passes) hZ.1
        t inv body rest k ρ rfl
      rw [hW] at hZ1
      exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 rfl
        (travRetR P O passes f fn caller rst rho s0 A R ziel zielG t inv body
          (blockOkR P O passes f fn (caller :: rst) rho s0 A R C hRuf body hb)
          (blockAbbR P O passes f fn (caller :: rst) rho s0 A R C hRuf body hb)
          (blockRetR body hb) (.dann rest k) _ log σ ρ E hpe hex M1 hZ1 hΛ
          (hA.lauf (RufLaufG.einzeln hs1)))
  | _, _, _, _, .retry n bis body ueber, hs => by
      intro log σ ρ E hpe hex M _ rest k hZ hΛ hA
      obtain ⟨hb, hu⟩ := hs.retry_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      obtain ⟨M1, hs1, hZ1⟩ := w_dannRetry (P := P) (O := O) (passes := passes) hZ.1
        n bis body ueber rest k ρ rfl
      rw [hW] at hZ1
      exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 rfl
        (retryRetR P O passes f fn caller rst rho s0 A R ziel zielG bis body ueber
          (blockOkR P O passes f fn (caller :: rst) rho s0 A R C hRuf body hb)
          (blockAbbR P O passes f fn (caller :: rst) rho s0 A R C hRuf body hb)
          (blockRetR body hb) (blockRetR ueber hu)
          (.dann rest k) n log σ ρ E hpe hex M1 hZ1 hΛ (hA.lauf (RufLaufG.einzeln hs1)))
  | _, _, _, _, .forever a inv body, hs => by
      intro log σ ρ E hpe hex M _ rest k hZ hΛ hA
      have hb := hs.forever_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      obtain ⟨M1, hs1, hZ1⟩ := w_dannForever (P := P) (O := O) (passes := passes) hZ.1
        a inv body rest k ρ rfl
      rw [hW] at hZ1
      exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 rfl
        (foreverRetR P O passes f fn caller rst rho s0 A R ziel zielG a inv body
          (blockOkR P O passes f fn (caller :: rst) rho s0 A R C hRuf body hb)
          (blockAbbR P O passes f fn (caller :: rst) rho s0 A R C hRuf body hb)
          (blockRetR body hb) (.dann rest k) passes log σ ρ E hpe hex M1 hZ1 hΛ
          (hA.lauf (RufLaufG.einzeln hs1)))
  | _, _, _, _, .axiomCall .., hs => absurd hs.art (by simp [Stmt.rArt, Stmt.blattArt])
  | _, _, _, _, .ret e hperm, _ => by
      intro log σ ρ E hpe hex M _ rest k hZ hΛ _
      have hW := hZ.welt
      simp only [execStmt, Ausgang.ende?, Option.some.injEq] at hex
      subst hex
      obtain ⟨M1, hs1, hG⟩ := w_dannRetP (P := P) (O := O) (passes := passes) hZ.1
        caller rst rfl hpe e hperm rest k ρ rfl hΛ.heldIn
      rw [hW] at hG
      exact ⟨M1, [], RufLaufG.einzeln hs1, hG, (Erw.lese _ _ _).offen⟩
  | _, _, _, _, .retWhy r hperm, _ => by
      intro log σ ρ E hpe hex M _ rest k hZ hΛ _
      have hW := hZ.welt
      simp only [execStmt, Ausgang.ende?, Option.some.injEq] at hex
      subst hex
      obtain ⟨M1, hs1, hG⟩ := w_dannRetGrundP (P := P) (O := O) (passes := passes) hZ.1
        caller rst rfl hpe r hperm rest k ρ rfl hΛ.heldIn
      rw [hW] at hG
      exact ⟨M1, [], RufLaufG.einzeln hs1, hG, rfl⟩
  | _, _, _, _, .leave .., _ => by
      intro log σ ρ E _ hex
      simp [execStmt, Ausgang.ende?] at hex
  | _, _, _, _, .next .., _ => by
      intro log σ ρ E _ hex
      simp [execStmt, Ausgang.ende?] at hex

theorem blockRetR : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D (vertragVon D fn) l Γ Λ Λ'), BlockR A C true b →
    SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG b
  | _, _, _, _, .nil, _ => by
      intro log σ ρ E _ hex
      simp [execBlock, Ausgang.ende?] at hex
  | _, _, _, _, .cons s rest, hb => by
      intro log σ ρ E hpe hex M k hZ hΛ hA
      obtain ⟨hs, hr⟩ := hb.cons_inv
      rcases execBlock_cons_ende O passes R s rest hex with h | ⟨σ1, ρ1, h1, h2⟩
      · exact stmtRetR s hs _ _ _ _ hpe h M rest k hZ hΛ hA
      · obtain ⟨M1, e1, hl1, hZ1, ho1⟩ := stmtOkR P O passes f fn (caller :: rst) rho s0 A R C hRuf
          s hs _ _ _ _ _ h1 M rest k hZ hΛ hA
        have hΛ1 := heldB_iff (s.held_iff) hΛ
        rw [← ho1] at hΛ1
        exact gepoppt_laufR P O passes f fn rst rho s0 ziel zielG hl1 ho1
          (blockRetR rest hr _ _ _ _ hpe h2 M1 k hZ1 hΛ1 (hA.lauf hl1))
  | _, _, _, _, .bind e rest, hb => by
      intro log σ ρ E hpe hex M k hZ hΛ hA
      have hr := hb.bind_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      rw [ende_schrumpf] at hex
      obtain ⟨M1, hs1, hZ1⟩ := w_dannBind (P := P) (O := O) (passes := passes) hZ.1
        e rest k ρ rfl
      rw [hW] at hZ1
      exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
        (blockRetR rest hr _ _ _ _ hpe hex M1 _ hZ1 (heldB_lese _ hΛ)
          (hA.lauf (RufLaufG.einzeln hs1)))
  | _, _, _, _, .bindCall g args he hp hr rest, hb => by
      intro log σ ρ E hpe hex M k hZ hΛ hA
      obtain ⟨hC, hrest⟩ := hb.bindCall_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i σ2 w hR2
        rw [ende_schrumpf] at hex
        obtain ⟨M1, hs1, hZ1⟩ := w_bindCall (P := P) (O := O) (passes := passes) hZ.1
          g args he hp hr rest k ρ rfl hΛ.heldIn
        rw [hW] at hZ1
        obtain ⟨M2, e2, hl2, hG2, ho2⟩ := hRuf.1 g hC _ _ _ _ hR2 M1 _ (caller :: rst) _ hZ1 _
          (PopArt.bind rest k ρ rfl he) (heldB_eintritt hp hΛ _ _)
          (hA.lauf (RufLaufG.einzeln hs1))
        have hZ2 := gepoppt_zustand hG2 rfl
        have hΛ2 : HeldB (vertragVon D fn).boden (nach D g _) (offen σ2.spur) :=
          heldB_iff (fun L => held_nachSig_iff _ _ L)
            (by rw [ho2, (Erw.lese _ _ _).offen]; exact hΛ)
        have hl12 := RufLaufG.schritt hs1 hl2
        have ho12 : offen σ2.spur = offen σ.spur := by rw [ho2, (Erw.lese _ _ _).offen]
        exact gepoppt_laufR P O passes f fn rst rho s0 ziel zielG hl12 ho12
          (blockRetR rest hrest _ _ _ _ hpe hex M2 _ hZ2 hΛ2 (hA.lauf hl12))
      · exact (Fin.cast hr ‹_›).elim0
      · simp [Ausgang.ende?] at hex
      · simp [Ausgang.ende?] at hex
  | _, _, _, _, .bindCallInd .., hb => by cases hb
  | _, _, _, _, .bindCallElse g args he hp hr err rest, hb => by
      intro log σ ρ E hpe hex M k hZ hΛ hA
      obtain ⟨hC, herr, hrest, _, _⟩ := hb.bindCallElse_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      obtain ⟨M1, hs1, hZ1⟩ := w_bindCallElse (P := P) (O := O) (passes := passes) hZ.1
        g args he hp hr err rest k ρ rfl hΛ.heldIn
      rw [hW] at hZ1
      split at hex
      · rename_i σ2 w hR2
        rw [ende_schrumpf] at hex
        obtain ⟨M2, e2, hl2, hG2, ho2⟩ := hRuf.1 g hC _ _ _ _ hR2 M1 _ (caller :: rst) _ hZ1 _
          (PopArt.bindSonst _ err rest k ρ rfl he) (heldB_eintritt hp hΛ _ _)
          (hA.lauf (RufLaufG.einzeln hs1))
        have hZ2 := gepoppt_zustand hG2 rfl
        have hΛ2 : HeldB (vertragVon D fn).boden (nach D g _) (offen σ2.spur) :=
          heldB_iff (fun L => held_nachSig_iff _ _ L)
            (by rw [ho2, (Erw.lese _ _ _).offen]; exact hΛ)
        have hl12 := RufLaufG.schritt hs1 hl2
        have ho12 : offen σ2.spur = offen σ.spur := by rw [ho2, (Erw.lese _ _ _).offen]
        exact gepoppt_laufR P O passes f fn rst rho s0 ziel zielG hl12 ho12
          (blockRetR rest hrest _ _ _ _ hpe hex M2 _ hZ2 hΛ2 (hA.lauf hl12))
      · rename_i σ2 r hR2
        rw [ende_zuAusgang, endEnde_schrumpf] at hex
        obtain ⟨M2, e2, hl2, hG2, ho2⟩ := hRuf.2 g hC _ _ _ _ hR2 M1 _ (caller :: rst) _ hZ1 _
          (PopGrund.sonst err rest k ρ rfl) (heldB_eintritt hp hΛ _ _)
          (hA.lauf (RufLaufG.einzeln hs1))
        have hZ2 := gepopptGrund_zustand hG2 rfl
        have hΛ2 : HeldB (vertragVon D fn).boden (nach D g _) (offen σ2.spur) :=
          heldB_iff (fun L => held_nachSig_iff _ _ L)
            (by rw [ho2, (Erw.lese _ _ _).offen]; exact hΛ)
        have hl12 := RufLaufG.schritt hs1 hl2
        have ho12 : offen σ2.spur = offen σ.spur := by rw [ho2, (Erw.lese _ _ _).offen]
        exact gepoppt_laufR P O passes f fn rst rho s0 ziel zielG hl12 ho12
          (alsRetR err herr _ _ _ _ hpe
            (by rw [Endblock.execBlock_alsBlock, ende_zuAusgang]; exact hex) M2 _ hZ2 hΛ2 (hA.lauf hl12))
      · simp [Ausgang.ende?] at hex
      · simp [Ausgang.ende?] at hex
  | _, _, _, _, .bindAxiom .., hb => by cases hb
  | _, _, _, _, .bindAxiomElse .., hb => by cases hb
  | _, _, _, _, .regRead r hk rest, hb => by
      intro log σ ρ E hpe hex M k hZ hΛ hA
      have hr := hb.regLies_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i w hw
        split at hex
        · rename_i hzs
          rw [ende_schrumpf] at hex
          obtain ⟨M1, hs1, hZ1⟩ := w_regLies (P := P) (O := O) (passes := passes) hZ.1
            r hk rest k ρ rfl w (by rw [hW]; exact hw) hzs
          rw [hW] at hZ1
          exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 rfl
            (blockRetR rest hr _ _ _ _ hpe hex M1 _ hZ1 hΛ (hA.lauf (RufLaufG.einzeln hs1)))
        · simp [Ausgang.ende?] at hex
      · simp [Ausgang.ende?] at hex
  | _, _, _, _, .regReadElse r hk zusage sonst rest, hb => by
      intro log σ ρ E hpe hex M k hZ hΛ hA
      obtain ⟨_, hr, hs, _⟩ := hb.regLiesElse_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i w hw
        split at hex
        · rename_i hw0
          rw [ende_schrumpf] at hex
          obtain ⟨M1, hs1, hZ1⟩ := w_regLiesElseWahr (P := P) (O := O) (passes := passes)
            hZ.1 r hk zusage sonst rest k ρ rfl w (by rw [hW]; exact hw)
            (by rw [hW]; exact hw0)
          rw [hW] at hZ1
          exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 ((Erw.fragt _ _).trans (Erw.lese _ _ _)).offen
            (blockRetR rest hr _ _ _ _ hpe hex M1 _ hZ1 (heldB_lese (σ := σ.fragt _) _ hΛ)
              (hA.lauf (RufLaufG.einzeln hs1)))
        · rename_i hw0
          rw [ende_zuAusgang] at hex
          obtain ⟨M1, hs1, hZ1⟩ := w_regLiesElseFalsch (P := P) (O := O) (passes := passes)
            hZ.1 r hk zusage sonst rest k ρ rfl w (by rw [hW]; exact hw)
            (by rw [hW]; simpa using hw0)
          rw [hW] at hZ1
          exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 ((Erw.fragt _ _).trans (Erw.lese _ _ _)).offen
            (alsRetR sonst hs _ _ _ _ hpe
              (by rw [Endblock.execBlock_alsBlock, ende_zuAusgang]; exact hex) M1 _ hZ1 (heldB_lese (σ := σ.fragt _) _ hΛ)
              (hA.lauf (RufLaufG.einzeln hs1)))
      · simp [Ausgang.ende?] at hex
  | _, _, _, _, .awaits g payload hp hL hat rest, hb => by
      intro log σ ρ E hpe hex M k hZ hΛ hA
      have hr := hb.awaits_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i hvis
        rw [ende_schrumpf] at hex
        obtain ⟨M1, hs1, hZ1⟩ := w_awaits (P := P) (O := O) (passes := passes) hZ.1
          g payload hp hL hat rest k ρ rfl (by rw [hW]; exact hvis)
        rw [hW] at hZ1
        exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 ((Erw.fragt _ _).trans (Erw.lese _ _ _)).offen
          (blockRetR rest hr _ _ _ _ hpe hex M1 _ hZ1 (heldB_lese (σ := σ.fragt _) _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
      · simp [Ausgang.ende?] at hex
  | _, _, Λ₀, _, .exchange g neuE hw hL rest, hb => by
      intro log σ ρ E hpe hex M k hZ hΛ hA
      have hr := hb.exchange_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      rw [ende_schrumpf] at hex
      obtain ⟨M1, hs1, hZ1⟩ := w_exchange (P := P) (O := O) (passes := passes) hZ.1
        g neuE hw hL rest k ρ rfl
      rw [hW] at hZ1
      have herw := (Erw.lese σ Λ₀ (.inr g :: neuE.orte)).trans
        (Erw.schreibGlob _ g Λ₀ (eval (σ.lese Λ₀ (.inr g :: neuE.orte)) neuE
          (σ.lese Λ₀ (.inr g :: neuE.orte))
          (.cons ((σ.lese Λ₀ (.inr g :: neuE.orte)).globs g) ρ)))
      exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 herw.offen
        (blockRetR rest hr _ _ _ _ hpe hex M1 _ hZ1
          (by rw [herw.offen]; exact hΛ) (hA.lauf (RufLaufG.einzeln hs1)))
  | _, _, _, _, .narrow e lo' hi' sonst rest, hb => by
      intro log σ ρ E hpe hex M k hZ hΛ hA
      obtain ⟨_, hr, hs, _⟩ := hb.narrow_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i hin
        rw [ende_schrumpf] at hex
        obtain ⟨M1, hs1, hZ1⟩ := w_narrowOk (P := P) (O := O) (passes := passes) hZ.1
          lo' hi' e sonst rest k ρ rfl hW hin
        exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
          (blockRetR rest hr _ _ _ _ hpe hex M1 _ hZ1 (heldB_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
      · rename_i hin
        rw [ende_zuAusgang] at hex
        obtain ⟨M1, hs1, hZ1⟩ := w_narrowElse (P := P) (O := O) (passes := passes) hZ.1
          lo' hi' e sonst rest k ρ rfl (by rw [hW]; exact hin)
        rw [hW] at hZ1
        exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
          (alsRetR sonst hs _ _ _ _ hpe
              (by rw [Endblock.execBlock_alsBlock, ende_zuAusgang]; exact hex) M1 _ hZ1 (heldB_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
  | _, _, _, _, .check c sonst rest, hb => by
      intro log σ ρ E hpe hex M k hZ hΛ hA
      obtain ⟨_, hr, hs, _⟩ := hb.pruefung_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i hc
        obtain ⟨M1, hs1, hZ1⟩ := w_pruefWahr (P := P) (O := O) (passes := passes) hZ.1
          c sonst rest k ρ rfl (by rw [hW]; exact hc)
        rw [hW] at hZ1
        exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
          (blockRetR rest hr _ _ _ _ hpe hex M1 _ hZ1 (heldB_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
      · rename_i hc
        rw [ende_zuAusgang] at hex
        obtain ⟨M1, hs1, hZ1⟩ := w_pruefFalsch (P := P) (O := O) (passes := passes) hZ.1
          c sonst rest k ρ rfl (by rw [hW]; simpa using hc)
        rw [hW] at hZ1
        exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
          (alsRetR sonst hs _ _ _ _ hpe
              (by rw [Endblock.execBlock_alsBlock, ende_zuAusgang]; exact hex) M1 _ hZ1 (heldB_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
  | _, _, _, _, .float op a b lo hi rest, hb => by
      intro log σ ρ E hpe hex M k hZ hΛ hA
      have hr := hb.gleit_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i w hw
        rw [ende_schrumpf] at hex
        obtain ⟨M1, hs1, hZ1⟩ := w_gleit (P := P) (O := O) (passes := passes) hZ.1
          op a b lo hi rest k ρ rfl w (by rw [hW]; exact hw)
        rw [hW] at hZ1
        exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
          (blockRetR rest hr _ _ _ _ hpe hex M1 _ hZ1 (heldB_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
      · simp [Ausgang.ende?] at hex
  | _, _, _, _, .floatLit q lo hi rest, hb => by
      intro log σ ρ E hpe hex M k hZ hΛ hA
      have hr := hb.gleitLit_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i w hw
        rw [ende_schrumpf] at hex
        obtain ⟨M1, hs1, hZ1⟩ := w_gleitLit (P := P) (O := O) (passes := passes) hZ.1
          q lo hi rest k ρ rfl w hw
        rw [hW] at hZ1
        exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 rfl
          (blockRetR rest hr _ _ _ _ hpe hex M1 _ hZ1 hΛ (hA.lauf (RufLaufG.einzeln hs1)))
      · simp [Ausgang.ende?] at hex
  | _, _, _, _, .floatOf e lo hi rest, hb => by
      intro log σ ρ E hpe hex M k hZ hΛ hA
      have hr := hb.gleitVon_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i w hw
        rw [ende_schrumpf] at hex
        obtain ⟨M1, hs1, hZ1⟩ := w_gleitVon (P := P) (O := O) (passes := passes) hZ.1
          e lo hi rest k ρ rfl w (by rw [hW]; exact hw)
        rw [hW] at hZ1
        exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
          (blockRetR rest hr _ _ _ _ hpe hex M1 _ hZ1 (heldB_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
      · simp [Ausgang.ende?] at hex
  | _, _, _, _, .floatNarrow e lo hi sonst rest, hb => by
      intro log σ ρ E hpe hex M k hZ hΛ hA
      obtain ⟨_, hr, hs, _⟩ := hb.gleitNarrow_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i w hw
        rw [ende_schrumpf] at hex
        obtain ⟨M1, hs1, hZ1⟩ := w_gleitNarrowOk (P := P) (O := O) (passes := passes) hZ.1
          e lo hi sonst rest k ρ rfl w (by rw [hW]; exact hw)
        rw [hW] at hZ1
        exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
          (blockRetR rest hr _ _ _ _ hpe hex M1 _ hZ1 (heldB_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
      · rename_i hn
        rw [ende_zuAusgang] at hex
        obtain ⟨M1, hs1, hZ1⟩ := w_gleitNarrowElse (P := P) (O := O) (passes := passes) hZ.1
          e lo hi sonst rest k ρ rfl (by rw [hW]; exact hn)
        rw [hW] at hZ1
        exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
          (alsRetR sonst hs _ _ _ _ hpe
              (by rw [Endblock.execBlock_alsBlock, ende_zuAusgang]; exact hex) M1 _ hZ1 (heldB_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))

theorem endRetR : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (eb : Endblock D (vertragVon D fn) l Γ Λ), EndR A C eb →
    SimRetER P O passes f fn caller rst rho s0 A R ziel zielG eb
  | _, _, _, .ret e hperm, _ => by
      intro log σ ρ E hpe hex M hZ hΛ _
      have hW := hZ.welt
      simp only [execEnd, EndAusgang.ende?, Option.some.injEq] at hex
      subst hex
      obtain ⟨M1, hs1, hG⟩ := w_rueckP (P := P) (O := O) (passes := passes) hZ.1
        caller rst rfl hpe e hperm ρ rfl hΛ.heldIn
      rw [hW] at hG
      exact ⟨M1, [], RufLaufG.einzeln hs1, hG, (Erw.lese _ _ _).offen⟩
  | _, _, _, .retWhy r hperm, _ => by
      intro log σ ρ E hpe hex M hZ hΛ _
      have hW := hZ.welt
      simp only [execEnd, EndAusgang.ende?, Option.some.injEq] at hex
      subst hex
      obtain ⟨M1, hs1, hG⟩ := w_rueckGrundP (P := P) (O := O) (passes := passes) hZ.1
        caller rst rfl hpe r hperm ρ rfl hΛ.heldIn
      rw [hW] at hG
      exact ⟨M1, [], RufLaufG.einzeln hs1, hG, rfl⟩
  | _, _, _, .leave .., he => by cases he
  | _, _, _, .next .., he => by cases he
  | _, _, _, .cons s rest, he => by
      intro log σ ρ E hpe hex M hZ hΛ hA
      obtain ⟨hs, hr, _⟩ := he.cons_inv
      rcases execEnd_cons_ende O passes R s rest hex with h | ⟨σ1, ρ1, h1, h2⟩
      · exact endeConsRetR P O passes f fn caller rst rho s0 A R C ziel zielG hs (stmtRetR s hs)
          σ ρ E hpe h M rest hZ hΛ hA
      · obtain ⟨M1, e1, hl1, hZ1, ho1⟩ := endeConsOkR P O passes f fn (caller :: rst) rho s0 A R C
          hRuf hs (stmtOkR P O passes f fn (caller :: rst) rho s0 A R C hRuf s hs) σ σ1 ρ ρ1 h1 M
          rest hZ hΛ hA
        have hΛ1 := heldB_iff (s.held_iff) hΛ
        rw [← ho1] at hΛ1
        exact gepoppt_laufR P O passes f fn rst rho s0 ziel zielG hl1 ho1
          (endRetR rest hr _ _ _ _ hpe h2 M1 hZ1 hΛ1 (hA.lauf hl1))
  | _, _, _, .bind e rest, he => by
      intro log σ ρ E hpe hex M hZ hΛ hA
      have hr := he.bind_inv
      have hW := hZ.welt
      simp only [execEnd] at hex
      rw [endEnde_schrumpf] at hex
      obtain ⟨M1, hs1, hZ1⟩ := w_endeBind (P := P) (O := O) (passes := passes) hZ.1
        e rest ρ rfl
      rw [hW] at hZ1
      exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
        (endRetR rest hr _ _ _ _ hpe hex M1 hZ1 (heldB_lese _ hΛ)
          (hA.lauf (RufLaufG.einzeln hs1)))

/-- A covered end block run as a BLOCK (the residue of an `else` branch
    or of the reason block of `let … else`, `Endblock.alsBlock`) ends the
    frame on the machine as the end block does. -/
theorem alsRetR : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (eb : Endblock D (vertragVon D fn) l Γ Λ), EndR A C eb →
    SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG eb.alsBlock.2
  | _, _, _, .ret e hperm, _ => by
      intro log σ ρ E hpe hex M k hZ hΛ _
      have hW := hZ.welt
      simp only [Endblock.alsBlock, execBlock, execStmt, Ausgang.ende?,
        Option.some.injEq] at hex
      subst hex
      obtain ⟨M1, hs1, hG⟩ := w_dannRetP (P := P) (O := O) (passes := passes) hZ.1
        caller rst rfl hpe e hperm .nil k ρ rfl hΛ.heldIn
      rw [hW] at hG
      exact ⟨M1, [], RufLaufG.einzeln hs1, hG, (Erw.lese _ _ _).offen⟩
  | _, _, _, .retWhy r hperm, _ => by
      intro log σ ρ E hpe hex M k hZ hΛ _
      have hW := hZ.welt
      simp only [Endblock.alsBlock, execBlock, execStmt, Ausgang.ende?,
        Option.some.injEq] at hex
      subst hex
      obtain ⟨M1, hs1, hG⟩ := w_dannRetGrundP (P := P) (O := O) (passes := passes) hZ.1
        caller rst rfl hpe r hperm .nil k ρ rfl hΛ.heldIn
      rw [hW] at hG
      exact ⟨M1, [], RufLaufG.einzeln hs1, hG, rfl⟩
  | _, _, _, .leave .., he => by cases he
  | _, _, _, .next .., he => by cases he
  | _, _, _, .cons s rest, he => by
      intro log σ ρ E hpe hex M k hZ hΛ hA
      obtain ⟨hs, hr, _⟩ := he.cons_inv
      rcases execBlock_cons_ende O passes R s _ hex with h | ⟨σ1, ρ1, h1, h2⟩
      · exact stmtRetR s hs _ _ _ _ hpe h M _ k hZ hΛ hA
      · obtain ⟨M1, e1, hl1, hZ1, ho1⟩ := stmtOkR P O passes f fn (caller :: rst) rho s0 A R C hRuf
          s hs _ _ _ _ _ h1 M _ k hZ hΛ hA
        have hΛ1 := heldB_iff (s.held_iff) hΛ
        rw [← ho1] at hΛ1
        exact gepoppt_laufR P O passes f fn rst rho s0 ziel zielG hl1 ho1
          (alsRetR rest hr _ _ _ _ hpe h2 M1 k hZ1 hΛ1 (hA.lauf hl1))
  | _, _, _, .bind e rest, he => by
      intro log σ ρ E hpe hex M k hZ hΛ hA
      have hr := he.bind_inv
      have hW := hZ.welt
      simp only [Endblock.alsBlock, execBlock] at hex
      rw [ende_schrumpf] at hex
      obtain ⟨M1, hs1, hZ1⟩ := w_dannBind (P := P) (O := O) (passes := passes) hZ.1
        e _ k ρ rfl
      rw [hW] at hZ1
      exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
        (alsRetR rest hr _ _ _ _ hpe hex M1 _ hZ1 (heldB_lese _ hΛ)
          (hA.lauf (RufLaufG.einzeln hs1)))

theorem armsRetR : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} (arms : Arms D (vertragVon D fn) l Γ Λ Λ' cs),
    ArmsR A C true arms → ∀ (v : Wert D (.sum cs)),
    SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG (armWahlG arms v).2.1
  | _, _, _, _, _, .nil, _, ⟨⟨k, hk⟩, _⟩ => (Nat.not_lt_zero k hk).elim
  | _, _, _, _, _, .cons b _, ha, ⟨⟨0, _⟩, _⟩ => blockRetR b ha.cons_inv.1
  | _, _, _, _, _, .cons _ rest, ha, ⟨⟨_ + 1, _⟩, _⟩ => armsRetR rest ha.cons_inv.2 _

theorem grundRetR : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D (vertragVon D fn) l Γ Λ Λ' n), GrundArmsR A C true arms →
    ∀ (r : Fin n), SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG (grundWahlG arms r)
  | _, _, _, _, _, .nil, _, ⟨k, hk⟩ => (Nat.not_lt_zero k hk).elim
  | _, _, _, _, _, .cons b _, ha, ⟨0, _⟩ => blockRetR b ha.cons_inv.1
  | _, _, _, _, _, .cons _ rest, ha, ⟨_ + 1, _⟩ => grundRetR rest ha.cons_inv.2 _

end

end SimRet

end Gabbro.Grammatik
