/- Part 7 of 10 of `RufAdaequatRufG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufAdaequatRufG.lean` imports all parts). -/
module
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T7.Teil1Basis
import all Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T7.Teil1Basis
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
      split at hex <;> simp only [Ausgang.ende?, reduceCtorEq] at hex
  | i :: is, log, σ, ρ, e, hpe, hex, M, hZ, hΛ, hA => by
      have hW := hZ.welt
      simp only [traverseLauf] at hex
      split at hex
      · simp only [Ausgang.ende?, reduceCtorEq] at hex
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
        · split at hex <;> simp only [Ausgang.ende?, reduceCtorEq] at hex
        · rename_i σ2 v2 hb2
          exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
            (hbodyRet log _ _ e hpe (by rw [hb2]; exact hex) M1 _ hZ1 hΛ1 hA1)
        · rename_i σ2 r2 hb2
          exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
            (hbodyRet log _ _ e hpe (by rw [hb2]; exact hex) M1 _ hZ1 hΛ1 hA1)
        all_goals simp only [Ausgang.ende?, reduceCtorEq] at hex

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
      · simp only [Ausgang.ende?, reduceCtorEq] at hex
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
      · simp only [Ausgang.ende?, reduceCtorEq] at hex
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
        · simp only [Ausgang.ende?, reduceCtorEq] at hex
        · rename_i σ2 v2 hb2
          exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
            (hbodyRet log _ _ e hpe (by rw [hb2]; exact hex) M1 _ hZ1 hΛ1 hA1)
        · rename_i σ2 r2 hb2
          exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
            (hbodyRet log _ _ e hpe (by rw [hb2]; exact hex) M1 _ hZ1 hΛ1 hA1)
        all_goals simp only [Ausgang.ende?, reduceCtorEq] at hex

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
      simp only [Ausgang.ende?, foreverLauf, reduceCtorEq] at hex
  | n + 1, log, σ, ρ, e, hpe, hex, M, hZ, hΛ, hA => by
      have hW := hZ.welt
      simp only [foreverLauf] at hex
      split at hex
      · simp only [Ausgang.ende?, reduceCtorEq] at hex
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
        · simp only [Ausgang.ende?, reduceCtorEq] at hex
        · rename_i σ2 v2 hb2
          exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
            (hbodyRet log _ _ e hpe (by rw [hb2]; exact hex) M1 _ hZ1 hΛ1 hA1)
        · rename_i σ2 r2 hb2
          exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
            (hbodyRet log _ _ e hpe (by rw [hb2]; exact hex) M1 _ hZ1 hΛ1 hA1)
        all_goals simp only [Ausgang.ende?, reduceCtorEq] at hex

variable (hRuf : RufOk P O passes f A R C)
include hRuf

end SimRet
end Gabbro.Grammatik
