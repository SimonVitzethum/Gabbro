/-
  File:      Grammatik/Gen/Erzeuger/AnweisungVollst.lean
  Subject:   COMPLETENESS of the statement clauses, one step: if the expressions, the blocks and the end blocks of
             the sizes below `k` are all in their streams, then so is every statement of size `k`
             (`stmtS_vollst`). The proof cases on the statement; a constructor without a clause stops the build.
-/
import Grammatik.Gen.Erzeuger.Block

namespace Gabbro.Grammatik.Gen

set_option linter.unusedSectionVars false

open Gabbro.Grammatik

variable {D : Deklaration} [Aufz D] [Zahlen] {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

/-- The statements of the context at hand of size below `k` are in the stream. -/
def SUnter (Ss : Sz (SS D V l Γ Λ)) (k : Nat) : Prop :=
  ∀ (Λ' : List (Res D)) (s : Stmt D V l Γ Λ Λ'), groesseStmt s < k → (⟨Λ', s⟩ : SS D V l Γ Λ) ∈ Ss (groesseStmt s)

/-- The blocks of the context at hand of size below `k` are in the stream. -/
def BUnter (Bs : Sz (SB D V l Γ Λ)) (k : Nat) : Prop :=
  ∀ (Λ' : List (Res D)) (b : Block D V l Γ Λ Λ'), groesseBlock b < k → (⟨Λ', b⟩ : SB D V l Γ Λ) ∈ Bs (groesseBlock b)

/-- The end blocks of the context at hand of size below `k` are in the stream. -/
def NUnter (Ns : Sz (Endblock D V l Γ Λ)) (k : Nat) : Prop :=
  ∀ (e : Endblock D V l Γ Λ), groesseEnd e < k → e ∈ Ns (groesseEnd e)

/-- Close `x ∈ stmtS ...` from `hc : x ∈ clause k`. -/
macro "stm " c:term ", " h:term : tactic =>
  `(tactic| exact Sz.mem_alle (c := $c) (by simp) $h)

set_option maxHeartbeats 8000000 in
/-- **Completeness of the statement clauses.** -/
theorem stmtS_vollst (O : Orakel V) (E : Sz (SE D Γ Λ)) (Bs : Sz (SB D V l Γ Λ)) {Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') (hu : groesseStmt s < unendlich) (hE : Unter E (groesseStmt s))
    (hB : BUnter Bs (groesseStmt s)) (hO : OUnter O (groesseStmt s)) :
    (⟨Λ', s⟩ : SS D V l Γ Λ) ∈ stmtS O E Bs (groesseStmt s) := by
  cases s with
  | assignSlot t f i e hw hL =>
    simp only [groesseStmt] at hu hE hB hO ⊢
    have hi := hE _ i (by omega)
    have he := hE _ e (by omega)
    stm (sAssignSlot E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.tab_mem t)) <|
      Sz.mem_bind (Sz.mem_wahl (Aufz.feld_mem t f)) <| Sz.mem_bind (mem_tyS hi) <| Sz.mem_bind (mem_tyS he) <|
      Sz.mem_wenn hw <| Sz.mem_wenn hL <| Sz.mem_pure _) (by omega)
  | assignThru p t ht f i e hw hL =>
    simp only [groesseStmt] at hu hE hB hO ⊢
    have hp := hE _ p (by omega)
    have hi := hE _ i (by omega)
    have he := hE _ e (by omega)
    stm (sAssignThru E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (mem_ptrTS hp) <|
      Sz.mem_bind (Sz.mem_wahl (Aufz.tab_mem t)) <| Sz.mem_wenn ht <|
      Sz.mem_bind (Sz.mem_wahl (Aufz.feld_mem t f)) <| Sz.mem_bind (mem_tyS hi) <| Sz.mem_bind (mem_tyS he) <|
      Sz.mem_wenn hw <| Sz.mem_wenn hL <| Sz.mem_pure _) (by omega)
  | assignSlotRef r t ht ho f e hw hL =>
    simp only [groesseStmt] at hu hE hB hO ⊢
    have hr := hE _ r (by omega)
    have he := hE _ e (by omega)
    stm (sAssignSlotRef E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (mem_refS hr) <|
      Sz.mem_bind (Sz.mem_wahl (Aufz.tab_mem t)) <| Sz.mem_wenn ht <| Sz.mem_wenn ho <|
      Sz.mem_bind (Sz.mem_wahl (Aufz.feld_mem t f)) <| Sz.mem_bind (mem_tyS he) <|
      Sz.mem_wenn hw <| Sz.mem_wenn hL <| Sz.mem_pure _) (by omega)
  | assignGlob g e hw hL =>
    simp only [groesseStmt] at hu hE hB hO ⊢
    have he := hE _ e (by omega)
    stm (sAssignGlob E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.glob_mem g)) <|
      Sz.mem_bind (mem_tyS he) <| Sz.mem_wenn hw <| Sz.mem_wenn hL <| Sz.mem_pure _) (by omega)
  | putBytes t f hf n i hlo hhi e hw hL =>
    simp only [groesseStmt] at hu hE hB hO ⊢
    have hi := hE _ i (by omega)
    have he := hE _ e (by omega)
    stm (sPutBytes E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.tab_mem t)) <|
      Sz.mem_bind (Sz.mem_wahl (Aufz.feld_mem t f)) <| Sz.mem_wenn hf <|
      Sz.mem_bind (mem_nS (n := n) rfl (by omega)) <| Sz.mem_bind (mem_intS hi) <| Sz.mem_wenn hlo <|
      Sz.mem_wenn hhi <| Sz.mem_bind (mem_tyS he) <| Sz.mem_wenn hw <| Sz.mem_wenn hL <| Sz.mem_pure _)
      (by omega)
  | assignVar x e =>
    simp only [groesseStmt] at hu hE hB hO ⊢
    have he := hE _ e (by omega)
    stm (sAssignVar E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (mem_varS x) <|
      Sz.mem_bind (mem_tyS he) <| Sz.mem_pure _) (by omega)
  | shift t f hτ i von nach hn he hw hL =>
    simp only [groesseStmt] at hu hE hB hO ⊢
    have hi := hE _ i (by omega)
    stm (sShift E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.tab_mem t)) <|
      Sz.mem_bind (Sz.mem_wahl (Aufz.feld_mem t f)) <| mem_mitTypInt hτ <| Sz.mem_bind (mem_tyS hi) <|
      Sz.mem_bind (mem_zS (n := von) rfl (by omega)) <| Sz.mem_bind (mem_zS (n := nach) rfl (by omega)) <|
      Sz.mem_wenn hn <| Sz.mem_wenn he <| Sz.mem_wenn hw <| Sz.mem_wenn hL <| Sz.mem_pure _) (by omega)
  | ite c t e =>
    simp only [groesseStmt] at hu hE hB hO ⊢
    have hc := hE _ c (by omega)
    have ht := hB _ t (by omega)
    have he := hB _ e (by omega)
    stm (sIte E Bs), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (mem_tyS hc) <| Sz.mem_bind ht <|
      Sz.mem_bind (mem_ofTy he) <| Sz.mem_pure _) (by omega)
  | @onOption _ _ n _ _ o p a =>
    simp only [groesseStmt] at hu hE hB hO ⊢
    have hok := bindOk_of (τ := Ty.index n) (by omega)
    have h0 := kostT_null hok
    have ho : (⟨n, o⟩ : Σ n : Int, Expr D Γ Λ (.opt n)) ∈ (optS E (groesseExpr o)).filter
        (fun p => Zahlen.bindOk (Ty.index p.1)) := List.mem_filter.2 ⟨mem_optS (hE _ o (by omega)), hok⟩
    have hp := hO.bl (groesseBlock p + (groesseBlock a + 0)) _ _ _ _ p (by omega) (by omega)
    have ha := hB _ a (by omega)
    stm (sOnOption O E Bs), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bindS ho hp <|
      Sz.mem_bind (mem_ofTy ha) <| Sz.mem_pure _) (by omega)
  | onTag v arms =>
    simp only [groesseStmt] at hu hE hB hO ⊢
    have hv := hE _ v (by omega)
    have harms := mem_armsS hO arms (by omega)
    stm (sOnTag O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bindS (mem_sumS hv) harms <|
      Sz.mem_pure _) (by omega)
  | onWhy r arms =>
    simp only [groesseStmt] at hu hE hB hO ⊢
    have hr := hE _ r (by omega)
    have harms := mem_grundArmsS hO arms (by omega)
    stm (sOnWhy O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bindS (mem_whyS hr) harms <|
      Sz.mem_pure _) (by omega)
  | call f args hp hr =>
    simp only [groesseStmt] at hu hE hB hO ⊢
    stm (sCall E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.fn_mem f)) <|
      Sz.mem_wenn hp <| Sz.mem_wenn hr <| Sz.mem_bind (mem_argsS hE _ args (by omega)) <| Sz.mem_pure _)
      (by omega)
  | callInd p args hp hr =>
    simp only [groesseStmt] at hu hE hB hO ⊢
    have hpp := hE _ p (by omega)
    stm (sCallInd E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (mem_fnptrS hpp) <|
      Sz.mem_wenn hp <| Sz.mem_wenn hr <| Sz.mem_bind (mem_argsS hE _ args (by omega)) <| Sz.mem_pure _)
      (by omega)
  | locks L hr body =>
    simp only [groesseStmt] at hu hE hB hO ⊢
    have hb := hO.bl (groesseBlock body + 0) _ _ _ _ body (by omega) (by omega)
    stm (sLocks O), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.lock_mem L)) <|
      Sz.mem_wenn hr <| Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) (mem_ofTy hb) <| Sz.mem_pure _)
      (by omega)
  | breaking i body =>
    simp only [groesseStmt] at hu hE hB hO ⊢
    have hb := hB _ body (by omega)
    stm (sBreaking Bs), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.inv_mem i)) <|
      Sz.mem_bind hb <| Sz.mem_pure _) (by omega)
  | traverse t inv body =>
    simp only [groesseStmt] at hu hE hB hO ⊢
    have hi := hE _ inv (by omega)
    have hb := hO.bl (groesseBlock body + 0) _ _ _ _ body (by omega) (by omega)
    stm (sTraverse O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.tab_mem t)) <|
      Sz.mem_bindR (mem_tyS hi) (mem_ofTy hb) <| Sz.mem_pure _) (by omega)
  | retry n bis body ueb =>
    simp only [groesseStmt] at hu hE hB hO ⊢
    have hbis := hE _ bis (by omega)
    have hb := hO.bl (groesseBlock body + (groesseBlock ueb + 0)) _ _ _ _ body (by omega) (by omega)
    have hueb := hB _ ueb (by omega)
    stm (sRetry O E Bs), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (mem_nS (n := n) rfl (by omega)) <|
      Sz.mem_bindR (mem_tyS hbis) (mem_ofTy hb) <| Sz.mem_bind (mem_ofTy hueb) <| Sz.mem_pure _) (by omega)
  | forever a inv body =>
    simp only [groesseStmt] at hu hE hB hO ⊢
    have hi := hE _ inv (by omega)
    have hb := hO.bl (groesseBlock body + 0) _ _ _ _ body (by omega) (by omega)
    stm (sForever O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.annahme_mem a)) <|
      Sz.mem_bindR (mem_tyS hi) (mem_ofTy hb) <| Sz.mem_pure _) (by omega)
  | axiomCall a args hae hw hg hd hgd =>
    simp only [groesseStmt] at hu hE hB hO ⊢
    stm (sAxiomCall E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.ax_mem a)) <|
      Sz.mem_wenn hae <| Sz.mem_wenn hw <| Sz.mem_wenn hg <| Sz.mem_wenn hd <| Sz.mem_wenn hgd <|
      Sz.mem_bind (mem_argsS hE _ args (by omega)) <| Sz.mem_pure _) (by omega)
  | regWrite r hk e =>
    simp only [groesseStmt] at hu hE hB hO ⊢
    have he := hE _ e (by omega)
    stm (sRegWrite E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.reg_mem r)) <|
      Sz.mem_wenn hk <| Sz.mem_bind (mem_tyS he) <| Sz.mem_pure _) (by omega)
  | transition r hk m' hm hl maske bits =>
    simp only [groesseStmt] at hu hE hB hO ⊢
    stm sTransition, Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.reg_mem r)) <|
      Sz.mem_bind (Sz.mem_wahl (Aufz.reg_mem m')) <| Sz.mem_wenn hk <| Sz.mem_wenn hm <| Sz.mem_wenn hl <|
      Sz.mem_bind (mem_zW (n := maske) rfl (by omega)) <| Sz.mem_bind (mem_zW (n := bits) rfl (by omega)) <|
      Sz.mem_pure _) (by omega)
  | publish g e payload hp hw hL =>
    simp only [groesseStmt] at hu hE hB hO ⊢
    subst hp
    have he := hE _ e (by omega)
    stm (sPublish E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.glob_mem g)) <|
      Sz.mem_wenn hw <| Sz.mem_wenn hL <| Sz.mem_bind (mem_tyS he) <| Sz.mem_pure _) (by omega)
  | advances mk a hmem hs =>
    simp only [groesseStmt]
    stm sAdvances, Sz.mem_blatt (List.mem_flatMap.2 ⟨.marke mk a, hmem, by
      dsimp only
      rw [dif_pos hmem, dif_pos hs]; simp⟩)
  | retires mk s hmem a =>
    simp only [groesseStmt]
    stm sRetires, Sz.mem_blatt (List.mem_flatMap.2 ⟨.marke mk s, hmem, by
      dsimp only
      rw [dif_pos hmem]
      exact List.mem_map.2 ⟨a, Aufz.annahme_mem a, rfl⟩⟩)
  | ret e hΛ =>
    simp only [groesseStmt] at hu hE hB hO ⊢
    stm (sRet E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (mem_ergS hE e (by omega)) <|
      Sz.mem_wenn hΛ <| Sz.mem_pure _) (by omega)
  | retWhy r hΛ =>
    simp only [groesseStmt]
    stm sRetWhy, Sz.mem_blatt (List.mem_flatMap.2 ⟨r, List.mem_finRange r, by rw [dif_pos hΛ]; simp⟩)
  | leave hl =>
    simp only [groesseStmt]
    stm sLeave, Sz.mem_blatt (by rw [dif_pos hl]; simp)
  | next hl =>
    simp only [groesseStmt]
    stm sNext, Sz.mem_blatt (by rw [dif_pos hl]; simp)

end Gabbro.Grammatik.Gen
