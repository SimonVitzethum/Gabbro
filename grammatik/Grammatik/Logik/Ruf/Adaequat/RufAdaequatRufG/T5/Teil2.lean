module

public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T4
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T5.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section SimOk
variable (P : Programm D) (O : Orakel D) (passes : Nat) (f : Faden) (fn : D.Fn)
  (stapel : List (RufRahmenG D)) (rho : Env D (D.params fn)) (s0 : World D)
  (A : D.Lock → Prop) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
  (C : D.Fn → Prop)

/-- **The loop of a `forever`, normal completion.** From `ewig a n inv body
    k` the machine runs to `k` exactly as `foreverLauf` with `n` passes left
    ends normally -- which it does only by `leave`: a read of the invariant
    before each pass (`ewigWeiter`, only on `true`), the body to its normal
    end (`ewigFort`) or to `next` (`dannNextEwig`), each spending one pass,
    and finally `leave` (`dannLeaveEwig`). -/
theorem foreverOkR {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (a : D.Annahme)
    (inv : Expr D Γ Λ .bool) (body : Block D (vertragVon D fn) true Γ Λ Λ)
    (hbody : SimOkBR P O passes f fn stapel rho s0 A R body)
    (hbodyA : SimAbbBR P O passes f fn stapel rho s0 A R body)
    (k : GRest D (vertragVon D fn) l Γ Λ) :
    ∀ (n : Nat) (log : List (RufEreignisF D)) (σ σ' : World D) (ρ ρ' : Env D Γ),
      foreverLauf (l := l) a (fun σ ρ => execBlock O passes R body σ ρ)
        (fun σ ρ => ((σ.lese Λ inv.orte), wahr? (eval (σ.lese Λ inv.orte) inv
          (σ.lese Λ inv.orte) ρ))) n σ ρ = .ok σ' ρ' →
      ∀ (M : RufMaschineG D), ZustandG M f stapel fn rho s0 log ρ (.ewig a n inv body k) σ →
        HeldB (vertragVon D fn).boden Λ (offen σ.spur) → FreiA A M f →
        ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
          ZustandG M' f stapel fn rho s0 (ext ++ log) ρ' k σ' ∧ offen σ'.spur = offen σ.spur
  | 0, log, σ, σ', ρ, ρ', hex, M, hZ, hΛ, hA => by
      simp only [foreverLauf] at hex
      cases hex
  | n + 1, log, σ, σ', ρ, ρ', hex, M, hZ, hΛ, hA => by
      have hW := hZ.welt
      simp only [foreverLauf] at hex
      split at hex
      · cases hex
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
            ZustandG M3 f stapel fn rho s0 (e3 ++ log) ρ2 (.ewig a n inv body k) σ2 →
            offen σ2.spur = offen σ.spur →
            foreverLauf (l := l) a (fun σ ρ => execBlock O passes R body σ ρ)
              (fun σ ρ => ((σ.lese Λ inv.orte), wahr? (eval (σ.lese Λ inv.orte) inv
                (σ.lese Λ inv.orte) ρ))) n σ2 ρ2 = .ok σ' ρ' →
            ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
              ZustandG M' f stapel fn rho s0 (ext ++ log) ρ' k σ' ∧
              offen σ'.spur = offen σ.spur := by
          intro M3 e3 σ2 ρ2 hl3 hZ3 ho3 hex3
          have hΛ3 : HeldB (vertragVon D fn).boden Λ (offen σ2.spur) := by rw [ho3]; exact hΛ
          obtain ⟨M4, e4, hr4, hZ4, ho4⟩ := foreverOkR a inv body hbody hbodyA k n _ σ2 σ' ρ2 ρ'
            hex3 M3 hZ3 hΛ3 (hA.lauf hl3)
          exact ⟨M4, e4 ++ e3, hl3.trans hr4, by rw [List.append_assoc]; exact hZ4,
            by rw [ho4, ho3]⟩
        split at hex
        · rename_i σ2 ρ2 hb2
          obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := hbody log _ _ _ _ hb2 M1 _ hZ1 hΛ1 hA1
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
        · rename_i h2 σ2 ρ2 hb2
          simp only [Ausgang.ok.injEq] at hex
          obtain ⟨hσ, hρ⟩ := hex
          subst hσ hρ
          obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := hbodyA rfl log _ _ _ _ true
            (by rw [hb2]; rfl) M1 _ hZ1 hΛ1 hA1
          have hW2 := hZ2.welt
          obtain ⟨M3, hs3, hZ3⟩ := w_abbEwig (P := P) (O := O) (passes := passes) hZ2.1
            true a n inv body k r ρ2 rfl (show HeldIn _ (offen σ2.spur) from (heldB_block r (by rw [ho2]; exact hΛ1)).heldIn)
          rw [hW2] at hZ3
          exact ⟨M3, e2, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
            by rw [ho2, (Erw.lese _ _ _).offen]⟩
        all_goals cases hex

/-- **A `retry` exits abruptly only through its overflow block.** Inside an
    outer loop, `retryLauf` ends in `leave`/`next` only where the overflow
    block does (the body's own exits are consumed); the machine runs the
    tries as `retryOkR` does and then the overflow block to its exit. -/
theorem retryAbbR {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (hl : l = true)
    (bis : Expr D Γ Λ .bool)
    (body : Block D (vertragVon D fn) true Γ Λ Λ) (ueber : Block D (vertragVon D fn) l Γ Λ Λ)
    (hbody : SimOkBR P O passes f fn stapel rho s0 A R body)
    (hbodyA : SimAbbBR P O passes f fn stapel rho s0 A R body)
    (hueberA : SimAbbBR P O passes f fn stapel rho s0 A R ueber)
    (k : GRest D (vertragVon D fn) l Γ Λ) :
    ∀ (n : Nat) (log : List (RufEreignisF D)) (σ σ' : World D) (ρ ρ' : Env D Γ) (w : Bool),
      (retryLauf (fun σ ρ => execBlock O passes R body σ ρ)
        (fun σ ρ => ((σ.lese Λ bis.orte), wahr? (eval (σ.lese Λ bis.orte) bis
          (σ.lese Λ bis.orte) ρ)))
        (fun σ ρ => execBlock O passes R ueber σ ρ) n σ ρ).abb? = some (w, σ', ρ') →
      ∀ (M : RufMaschineG D), ZustandG M f stapel fn rho s0 log ρ (.wieder n bis body ueber k) σ →
        HeldB (vertragVon D fn).boden Λ (offen σ.spur) → FreiA A M f →
        ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)) (Λx : List (Res D))
          (r : Block D (vertragVon D fn) l Γ Λx Λ), RufLaufG P O passes f M M' ∧
          ZustandG M' f stapel fn rho s0 (ext ++ log) ρ' (.dann (.cons (abbS hl w) r) k) σ' ∧
          offen σ'.spur = offen σ.spur
  | 0, log, σ, σ', ρ, ρ', w, hex, M, hZ, hΛ, hA => by
      have hW := hZ.welt
      simp only [retryLauf] at hex
      split at hex
      · simp only [Ausgang.abb?, reduceCtorEq] at hex
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
        obtain ⟨M3, e3, Λx, r, hr3, hZ3, ho3⟩ := hueberA hl log _ _ _ _ w hex M2 _ hZ2
          (heldB_lese bis.orte hΛ (Λ₀ := Λ))
          ((hA.lauf (RufLaufG.einzeln hs1)).lauf (RufLaufG.einzeln hs2))
        obtain ⟨M4, hs4, hZ4⟩ := peelDannR P O passes f fn stapel rho s0 hl hZ3
        exact ⟨M4, e3, Λ, .nil, RufLaufG.schritt hs1 (RufLaufG.schritt hs2
          (hr3.trans (RufLaufG.einzeln hs4))), hZ4, by rw [ho3, (Erw.lese _ _ _).offen]⟩
  | n + 1, log, σ, σ', ρ, ρ', w, hex, M, hZ, hΛ, hA => by
      subst hl
      have hW := hZ.welt
      simp only [retryLauf] at hex
      split at hex
      · simp only [Ausgang.abb?, reduceCtorEq] at hex
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
            ZustandG M3 f stapel fn rho s0 (e3 ++ log) ρ2 (.wieder n bis body ueber k) σ2 →
            offen σ2.spur = offen σ.spur →
            (retryLauf (fun σ ρ => execBlock O passes R body σ ρ)
              (fun σ ρ => ((σ.lese Λ bis.orte), wahr? (eval (σ.lese Λ bis.orte) bis
                (σ.lese Λ bis.orte) ρ)))
              (fun σ ρ => execBlock O passes R ueber σ ρ) n σ2 ρ2).abb? = some (w, σ', ρ') →
            ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)) (Λx : List (Res D))
              (r : Block D (vertragVon D fn) true Γ Λx Λ), RufLaufG P O passes f M M' ∧
              ZustandG M' f stapel fn rho s0 (ext ++ log) ρ' (.dann (.cons (abbS rfl w) r) k) σ' ∧
              offen σ'.spur = offen σ.spur := by
          intro M3 e3 σ2 ρ2 hl3 hZ3 ho3 hex3
          have hΛ3 : HeldB (vertragVon D fn).boden Λ (offen σ2.spur) := by rw [ho3]; exact hΛ
          obtain ⟨M4, e4, Λx, r, hr4, hZ4, ho4⟩ := retryAbbR rfl bis body ueber hbody hbodyA hueberA
            k n _ σ2 σ' ρ2 ρ' w hex3 M3 hZ3 hΛ3 (hA.lauf hl3)
          exact ⟨M4, e4 ++ e3, Λx, r, hl3.trans hr4, by rw [List.append_assoc]; exact hZ4,
            by rw [ho4, ho3]⟩
        split at hex
        · rename_i σ2 ρ2 hb2
          obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := hbody log _ _ _ _ hb2 M1 _ hZ1 hΛ1 hA1
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
        · simp only [Ausgang.abb?, reduceCtorEq] at hex
        all_goals simp only [Ausgang.abb?, reduceCtorEq] at hex


variable (hRuf : RufOk P O passes f A R C)
include hRuf

-- `hRuf` discharges the calls in `stmtOkR`/`blockOkR`; `armsOkR`/`grundOkR`
-- need it only through their recursive `blockOkR` calls, which the linter
-- does not count as a use.
set_option linter.unusedSectionVars false in
theorem stmtOkR_ite 
    {mr : Bool}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (c)
    (t)
    (e)
    (hs : StmtR A C mr (.ite c t e : Stmt D (vertragVon D fn) l Γ Λ Λ'))
    (ih_blockOkR_t : ∀ {mr : Bool}, BlockR A C mr t → SimOkBR P O passes f fn stapel rho s0 A R t)
    (ih_blockOkR_e : ∀ {mr : Bool}, BlockR A C mr e → SimOkBR P O passes f fn stapel rho s0 A R e)
    : SimOkSR P O passes f fn stapel rho s0 A R (.ite c t e : Stmt D (vertragVon D fn) l Γ Λ Λ') :=
  by
  intro log σ σ' ρ ρ' hex M _ rest k hZ hΛ hA
  obtain ⟨ht, he⟩ := hs.ite_inv
  have hW := hZ.welt
  simp only [execStmt] at hex
  split at hex
  · rename_i hc
    obtain ⟨M1, hs1, hZ1⟩ := w_iteWahr (P := P) (O := O) (passes := passes) hZ.1
      c t e rest k ρ rfl (by rw [hW]; exact hc)
    rw [hW] at hZ1
    obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := ih_blockOkR_t ht _ _ _ _ _ hex M1 _ hZ1
      (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
    exact ⟨M2, _, RufLaufG.schritt hs1 hr2, hZ2, by rw [ho2, (Erw.lese _ _ _).offen]⟩
  · rename_i hc
    obtain ⟨M1, hs1, hZ1⟩ := w_iteFalsch (P := P) (O := O) (passes := passes) hZ.1
      c t e rest k ρ rfl (by rw [hW]; simpa using hc)
    rw [hW] at hZ1
    obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := ih_blockOkR_e he _ _ _ _ _ hex M1 _ hZ1
      (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
    exact ⟨M2, _, RufLaufG.schritt hs1 hr2, hZ2, by rw [ho2, (Erw.lese _ _ _).offen]⟩

set_option linter.unusedSectionVars false in
theorem stmtOkR_onOption 
    {mr : Bool}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_n}
    (o)
    (p)
    (a)
    (hs : StmtR A C mr (.onOption (n := zi_n) o p a : Stmt D (vertragVon D fn) l Γ Λ Λ'))
    (ih_blockOkR_p : ∀ {mr : Bool}, BlockR A C mr p → SimOkBR P O passes f fn stapel rho s0 A R p)
    (ih_blockOkR_a : ∀ {mr : Bool}, BlockR A C mr a → SimOkBR P O passes f fn stapel rho s0 A R a)
    : SimOkSR P O passes f fn stapel rho s0 A R (.onOption (n := zi_n) o p a : Stmt D (vertragVon D fn) l Γ Λ Λ') :=
  by
  intro log σ σ' ρ ρ' hex M _ rest k hZ hΛ hA
  obtain ⟨hp, ha⟩ := hs.onOption_inv
  have hW := hZ.welt
  simp only [execStmt] at hex
  split at hex
  · rename_i v hv
    obtain ⟨w, hw⟩ := schrumpf_ok hex
    obtain ⟨M1, hs1, hZ1⟩ := w_optSome (P := P) (O := O) (passes := passes) hZ.1
      o p a rest k ρ rfl v (by rw [hW]; exact hv)
    rw [hW] at hZ1
    obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := ih_blockOkR_p hp _ _ _ _ _ hw M1 _ hZ1
      (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
    obtain ⟨M3, hs3, hZ3⟩ := schrumpfOkR P O passes f fn stapel rho s0 hZ2
    exact ⟨M3, _, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
      by rw [ho2, (Erw.lese _ _ _).offen]⟩
  · rename_i hv
    obtain ⟨M1, hs1, hZ1⟩ := w_optNone (P := P) (O := O) (passes := passes) hZ.1
      o p a rest k ρ rfl (by rw [hW]; exact hv)
    rw [hW] at hZ1
    obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := ih_blockOkR_a ha _ _ _ _ _ hex M1 _ hZ1
      (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
    exact ⟨M2, _, RufLaufG.schritt hs1 hr2, hZ2, by rw [ho2, (Erw.lese _ _ _).offen]⟩

set_option linter.unusedSectionVars false in
theorem stmtOkR_onTag 
    {mr : Bool}
    {l : Bool}
    {Γ : Ctx}
    {Λ₀ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_cs}
    (v)
    (arms)
    (hs : StmtR A C mr (.onTag (cs := zi_cs) v arms : Stmt D (vertragVon D fn) l Γ Λ₀ Λ'))
    (ih_armsOkR_arms : ∀ {mr : Bool}, ArmsR A C mr arms → ∀ (v : Wert D (.sum _)), SimOkBR P O passes f fn stapel rho s0 A R (armWahlG arms v).2.1)
    : SimOkSR P O passes f fn stapel rho s0 A R (.onTag (cs := zi_cs) v arms : Stmt D (vertragVon D fn) l Γ Λ₀ Λ') :=
  by
  intro log σ σ' ρ ρ' hex M _ rest k hZ hΛ hA
  have ha := hs.onTag_inv
  have hW := hZ.welt
  simp only [execStmt] at hex
  rw [execArms_wahl] at hex
  have hsim := ih_armsOkR_arms ha (eval (σ.lese Λ₀ v.orte) v (σ.lese Λ₀ v.orte) ρ)
  generalize hwahl : armWahlG arms (eval (σ.lese Λ₀ v.orte) v (σ.lese Λ₀ v.orte) ρ) = w
    at hex hsim
  obtain ⟨c, b, nutz⟩ := w
  cases c with
  | none =>
    obtain ⟨M1, hs1, hZ1⟩ := w_tagNone (P := P) (O := O) (passes := passes) hZ.1
      v arms rest k ρ rfl b nutz (by rw [hW]; exact hwahl)
    rw [hW] at hZ1
    obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := hsim _ _ _ _ _ hex M1 _ hZ1
      (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
    exact ⟨M2, _, RufLaufG.schritt hs1 hr2, hZ2, by rw [ho2, (Erw.lese _ _ _).offen]⟩
  | some lh =>
    obtain ⟨lo, hi⟩ := lh
    obtain ⟨w', hw'⟩ := schrumpf_ok hex
    obtain ⟨M1, hs1, hZ1⟩ := w_tagSome (P := P) (O := O) (passes := passes) hZ.1
      v arms rest k ρ rfl lo hi b nutz (by rw [hW]; exact hwahl)
    rw [hW] at hZ1
    obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := hsim _ _ _ _ _ hw' M1 _ hZ1
      (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
    obtain ⟨M3, hs3, hZ3⟩ := schrumpfOkR P O passes f fn stapel rho s0 hZ2
    exact ⟨M3, _, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
      by rw [ho2, (Erw.lese _ _ _).offen]⟩

set_option linter.unusedSectionVars false in
theorem stmtOkR_onWhy 
    {mr : Bool}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_n}
    (r)
    (arms)
    (hs : StmtR A C mr (.onWhy (n := zi_n) r arms : Stmt D (vertragVon D fn) l Γ Λ Λ'))
    (ih_grundOkR_arms : ∀ {mr : Bool}, GrundArmsR A C mr arms → ∀ (r : Fin _), SimOkBR P O passes f fn stapel rho s0 A R (grundWahlG arms r))
    : SimOkSR P O passes f fn stapel rho s0 A R (.onWhy (n := zi_n) r arms : Stmt D (vertragVon D fn) l Γ Λ Λ') :=
  by
  intro log σ σ' ρ ρ' hex M _ rest k hZ hΛ hA
  have ha := hs.onGrund_inv
  have hW := hZ.welt
  simp only [execStmt] at hex
  rw [execGrund_wahlW O passes R arms] at hex
  obtain ⟨M1, hs1, hZ1⟩ := w_grund (P := P) (O := O) (passes := passes) hZ.1
    r arms rest k ρ rfl
  rw [hW] at hZ1
  obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := ih_grundOkR_arms ha _ _ _ _ _ _ hex M1 _ hZ1
    (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
  exact ⟨M2, _, RufLaufG.schritt hs1 hr2, hZ2, by rw [ho2, (Erw.lese _ _ _).offen]⟩

set_option linter.unusedSectionVars false in
theorem stmtOkR_call 
    {mr : Bool}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (g)
    (args)
    (hp)
    (hr)
    (hs : StmtR A C mr (.call g args hp hr : Stmt D (vertragVon D fn) l Γ Λ _))
    : SimOkSR P O passes f fn stapel rho s0 A R (.call g args hp hr : Stmt D (vertragVon D fn) l Γ Λ _) :=
  by
  intro log σ σ' ρ ρ' hex M _ rest k hZ hΛ hA
  have hC := hs.call_inv
  have hW := hZ.welt
  simp only [execStmt] at hex
  split at hex
  · rename_i σ2 v hR2
    simp only [Ausgang.ok.injEq] at hex
    obtain ⟨rfl, rfl⟩ := hex
    obtain ⟨M1, hs1, hZ1⟩ := w_rufDann (P := P) (O := O) (passes := passes) hZ.1
      g args hp hr rest k ρ rfl hΛ.heldIn
    rw [hW] at hZ1
    obtain ⟨M2, e2, hl2, hG2, ho2⟩ := hRuf.1 g hC _ _ _ _ hR2 M1 _ stapel _ hZ1 _ (PopArt.wie rfl)
      (heldB_eintritt hp hΛ _ _) (hA.lauf (RufLaufG.einzeln hs1))
    exact ⟨M2, _, RufLaufG.schritt hs1 hl2, gepoppt_zustand hG2 rfl,
      by rw [ho2, (Erw.lese _ _ _).offen]⟩
  · exact (Fin.cast hr ‹_›).elim0
  · cases hex
  · cases hex

set_option linter.unusedSectionVars false in
theorem stmtOkR_locks 
    {mr : Bool}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (hr)
    (body)
    (hs : StmtR A C mr (.locks L hr body : Stmt D (vertragVon D fn) l Γ Λ _))
    (ih_blockOkR_body : ∀ {mr : Bool}, BlockR A C mr body → SimOkBR P O passes f fn stapel rho s0 A R body)
    : SimOkSR P O passes f fn stapel rho s0 A R (.locks L hr body : Stmt D (vertragVon D fn) l Γ Λ _) :=
  by
  intro log σ σ' ρ ρ' hex M _ rest k hZ hΛ hA
  obtain ⟨hAL, hb, hbo⟩ := hs.locks_inv
  have hW := hZ.welt
  simp only [execStmt] at hex
  obtain ⟨σ1, hb1, rfl⟩ := mapWelt_ok hex
  obtain ⟨M1, hs1, hZ1⟩ := w_locksB (P := P) (O := O) (passes := passes) hZ.1
    L hr body rest k ρ rfl hΛ hbo (hA L hAL)
  rw [hW] at hZ1
  obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := ih_blockOkR_body hb _ _ _ _ _ hb1 M1 _ hZ1
    (heldB_locks L hΛ) (hA.lauf (RufLaufG.einzeln hs1))
  have hW2 := hZ2.welt
  obtain ⟨M3, hs3, hZ3⟩ := w_freiGib (P := P) (O := O) (passes := passes) hZ2.1
    L (.dann rest k) ρ' rfl
  rw [hW2] at hZ3
  exact ⟨M3, _, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
    offen_gibt_nimmt σ σ1 L ho2⟩

set_option linter.unusedSectionVars false in
theorem stmtOkR_breaking 
    {mr : Bool}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (i)
    (body)
    (hs : StmtR A C mr (.breaking i body : Stmt D (vertragVon D fn) l Γ Λ Λ'))
    (ih_blockOkR_body : ∀ {mr : Bool}, BlockR A C mr body → SimOkBR P O passes f fn stapel rho s0 A R body)
    : SimOkSR P O passes f fn stapel rho s0 A R (.breaking i body : Stmt D (vertragVon D fn) l Γ Λ Λ') :=
  by
  intro log σ σ' ρ ρ' hex M _ rest k hZ hΛ hA
  have hb := hs.breaking_inv
  have hW := hZ.welt
  simp only [execStmt] at hex
  obtain ⟨M1, hs1, hZ1⟩ := w_breaking (P := P) (O := O) (passes := passes) hZ.1
    i body rest k ρ rfl
  rw [hW] at hZ1
  obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := ih_blockOkR_body hb _ _ _ _ _ hex M1 _ hZ1
    hΛ (hA.lauf (RufLaufG.einzeln hs1))
  exact ⟨M2, _, RufLaufG.schritt hs1 hr2, hZ2, ho2⟩

end SimOk
end Gabbro.Grammatik
