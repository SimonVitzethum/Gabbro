/-
  File:      Grammatik/Gen/Erzeuger/Kompakt/Anweisung.lean
  Subject:   REPRESENTATIVES of the statements: if the parts of a statement (its expressions, the blocks of the context
             at hand, the blocks of other contexts) have representatives in the streams, the statement has one in the
             clause stream (`stmtS_rep`): the same constructor over the parts' representatives, standing for it
             (`GlS`). One case per constructor; a constructor without a case stops the build.
-/
import Grammatik.Gen.Erzeuger.Kompakt.Teile
import Grammatik.Gen.Erzeuger.AnweisungVollst

namespace Gabbro.Grammatik.Gen

set_option linter.unusedSectionVars false

open Gabbro.Grammatik

variable {D : Deklaration} [Aufz D] [Zahlen] {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

set_option maxHeartbeats 16000000 in
/-- **Representatives of the statements.** -/
theorem stmtS_rep (O : Orakel V) (E : Sz (SE D Γ Λ)) (Bs : Sz (SB D V l Γ Λ)) {Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') (hu : groesseStmt s < unendlich) (hE : ERU E (groesseStmt s))
    (hB : BRU Bs (groesseStmt s)) (hO : ORU O (groesseStmt s)) :
    ∃ s' : Stmt D V l Γ Λ Λ', (⟨Λ', s'⟩ : SS D V l Γ Λ) ∈ stmtS O E Bs (groesseStmt s') ∧ GlS s' s := by
  cases s with
  | assignSlot t f i e hw hL =>
    simp only [groesseStmt] at hu hE hB hO
    obtain ⟨i', hi, ⟨_, _⟩⟩ := hE _ i (by omega)
    obtain ⟨e', he, ⟨_, _⟩⟩ := hE _ e (by omega)
    refine ⟨.assignSlot t f i' e' hw hL, ?_, ?_⟩
    · simp only [groesseStmt]
      stm (sAssignSlot E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.tab_mem t)) <|
        Sz.mem_bind (Sz.mem_wahl (Aufz.feld_mem t f)) <| Sz.mem_bind (mem_tyS hi) <| Sz.mem_bind (mem_tyS he) <|
        Sz.mem_wenn hw <| Sz.mem_wenn hL <| Sz.mem_pure _) (by omega)
    · glfertig
  | assignThru p t ht f i e hw hL =>
    simp only [groesseStmt] at hu hE hB hO
    obtain ⟨p', hp, ⟨_, _⟩⟩ := hE _ p (by omega)
    obtain ⟨i', hi, ⟨_, _⟩⟩ := hE _ i (by omega)
    obtain ⟨e', he, ⟨_, _⟩⟩ := hE _ e (by omega)
    refine ⟨.assignThru p' t ht f i' e' hw hL, ?_, ?_⟩
    · simp only [groesseStmt]
      stm (sAssignThru E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (mem_ptrTS hp) <|
        Sz.mem_bind (Sz.mem_wahl (Aufz.tab_mem t)) <| Sz.mem_wenn ht <|
        Sz.mem_bind (Sz.mem_wahl (Aufz.feld_mem t f)) <| Sz.mem_bind (mem_tyS hi) <| Sz.mem_bind (mem_tyS he) <|
        Sz.mem_wenn hw <| Sz.mem_wenn hL <| Sz.mem_pure _) (by omega)
    · glfertig
  | assignSlotRef r t ht ho f e hw hL =>
    simp only [groesseStmt] at hu hE hB hO
    obtain ⟨r', hr, ⟨_, _⟩⟩ := hE _ r (by omega)
    obtain ⟨e', he, ⟨_, _⟩⟩ := hE _ e (by omega)
    refine ⟨.assignSlotRef r' t ht ho f e' hw hL, ?_, ?_⟩
    · simp only [groesseStmt]
      stm (sAssignSlotRef E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (mem_refS hr) <|
        Sz.mem_bind (Sz.mem_wahl (Aufz.tab_mem t)) <| Sz.mem_wenn ht <| Sz.mem_wenn ho <|
        Sz.mem_bind (Sz.mem_wahl (Aufz.feld_mem t f)) <| Sz.mem_bind (mem_tyS he) <|
        Sz.mem_wenn hw <| Sz.mem_wenn hL <| Sz.mem_pure _) (by omega)
    · glfertig
  | assignGlob g e hw hL =>
    simp only [groesseStmt] at hu hE hB hO
    obtain ⟨e', he, ⟨_, _⟩⟩ := hE _ e (by omega)
    refine ⟨.assignGlob g e' hw hL, ?_, ?_⟩
    · simp only [groesseStmt]
      stm (sAssignGlob E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.glob_mem g)) <|
        Sz.mem_bind (mem_tyS he) <| Sz.mem_wenn hw <| Sz.mem_wenn hL <| Sz.mem_pure _) (by omega)
    · glfertig
  | putBytes t f hf n i hlo hhi e hw hL =>
    simp only [groesseStmt] at hu hE hB hO
    obtain ⟨i', hi, ⟨_, _⟩⟩ := hE _ i (by omega)
    obtain ⟨e', he, ⟨_, _⟩⟩ := hE _ e (by omega)
    refine ⟨.putBytes t f hf n i' hlo hhi e' hw hL, ?_, ?_⟩
    · simp only [groesseStmt]
      stm (sPutBytes E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.tab_mem t)) <|
        Sz.mem_bind (Sz.mem_wahl (Aufz.feld_mem t f)) <| Sz.mem_wenn hf <|
        Sz.mem_bind (mem_nS (n := n) rfl (by omega)) <| Sz.mem_bind (mem_intS hi) <| Sz.mem_wenn hlo <|
        Sz.mem_wenn hhi <| Sz.mem_bind (mem_tyS he) <| Sz.mem_wenn hw <| Sz.mem_wenn hL <| Sz.mem_pure _)
        (by omega)
    · glfertig
  | assignVar x e =>
    simp only [groesseStmt] at hu hE hB hO
    obtain ⟨e', he, ⟨_, _⟩⟩ := hE _ e (by omega)
    refine ⟨.assignVar x e', ?_, ?_⟩
    · simp only [groesseStmt]
      stm (sAssignVar E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (mem_varS x) <|
        Sz.mem_bind (mem_tyS he) <| Sz.mem_pure _) (by omega)
    · glfertig
  | shift t f hτ i von nach hn he hw hL =>
    simp only [groesseStmt] at hu hE hB hO
    obtain ⟨i', hi, ⟨_, _⟩⟩ := hE _ i (by omega)
    refine ⟨.shift t f hτ i' von nach hn he hw hL, ?_, ?_⟩
    · simp only [groesseStmt]
      stm (sShift E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.tab_mem t)) <|
        Sz.mem_bind (Sz.mem_wahl (Aufz.feld_mem t f)) <| mem_mitTypInt hτ <| Sz.mem_bind (mem_tyS hi) <|
        Sz.mem_bind (mem_zS (n := von) rfl (by omega)) <| Sz.mem_bind (mem_zS (n := nach) rfl (by omega)) <|
        Sz.mem_wenn hn <| Sz.mem_wenn he <| Sz.mem_wenn hw <| Sz.mem_wenn hL <| Sz.mem_pure _) (by omega)
    · glfertig
  | ite c t e =>
    simp only [groesseStmt] at hu hE hB hO
    obtain ⟨c', hc, ⟨_, _⟩⟩ := hE _ c (by omega)
    obtain ⟨t', ht, ⟨_, _, _, _, _, _⟩⟩ := hB _ t (by omega)
    obtain ⟨e', he, ⟨_, _, _, _, _, _⟩⟩ := hB _ e (by omega)
    refine ⟨.ite c' t' e', ?_, ?_⟩
    · simp only [groesseStmt]
      stm (sIte E Bs), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (mem_tyS hc) <| Sz.mem_bind ht <|
        Sz.mem_bind (mem_ofTy he) <| Sz.mem_pure _) (by omega)
    · glfertig
  | @onOption _ _ n _ _ o p a =>
    simp only [groesseStmt] at hu hE hB hO
    obtain ⟨o', hoo, ⟨_, _⟩⟩ := hE _ o (by omega)
    obtain ⟨p', hpm, ⟨_, _, _, _, _, _⟩⟩ := hO.bl _ _ _ _ p (by omega)
    obtain ⟨a', ha, ⟨_, _, _, _, _, _⟩⟩ := hB _ a (by omega)
    refine ⟨.onOption o' p' a', ?_, ?_⟩
    · simp only [groesseStmt]
      have hp := hpm (groesseBlock p' + (groesseBlock a' + 0)) (by omega)
      have hok := bindOk_of (τ := Ty.index n) (by omega)
      have h0 := kostT_null hok
      have ho : (⟨n, o'⟩ : Σ n : Int, Expr D Γ Λ (.opt n)) ∈ (optS E (groesseExpr o')).filter
          (fun p => Zahlen.bindOk (Ty.index p.1)) := List.mem_filter.2 ⟨mem_optS hoo, hok⟩
      stm (sOnOption O E Bs), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bindS ho hp <|
        Sz.mem_bind (mem_ofTy ha) <| Sz.mem_pure _) (by omega)
    · glfertig
  | onTag v arms =>
    simp only [groesseStmt] at hu hE hB hO
    obtain ⟨v', hv, ⟨_, _⟩⟩ := hE _ v (by omega)
    obtain ⟨arms', harms, ⟨_, _, _, _, _, _⟩⟩ := armsS_rep hO arms (by omega)
    refine ⟨.onTag v' arms', ?_, ?_⟩
    · simp only [groesseStmt]
      stm (sOnTag O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bindS (mem_sumS hv) harms <|
        Sz.mem_pure _) (by omega)
    · glfertig
  | onWhy r arms =>
    simp only [groesseStmt] at hu hE hB hO
    obtain ⟨r', hr, ⟨_, _⟩⟩ := hE _ r (by omega)
    obtain ⟨arms', harms, ⟨_, _, _, _, _, _⟩⟩ := grundArmsS_rep hO arms (by omega)
    refine ⟨.onWhy r' arms', ?_, ?_⟩
    · simp only [groesseStmt]
      stm (sOnWhy O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bindS (mem_whyS hr) harms <|
        Sz.mem_pure _) (by omega)
    · glfertig
  | call f args hp hr =>
    simp only [groesseStmt] at hu hE hB hO
    obtain ⟨args', hargs, ⟨_, _⟩⟩ := argsS_rep hE _ args (by omega)
    refine ⟨.call f args' hp hr, ?_, ?_⟩
    · simp only [groesseStmt]
      stm (sCall E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.fn_mem f)) <|
        Sz.mem_wenn hp <| Sz.mem_wenn hr <| Sz.mem_bind hargs <| Sz.mem_pure _)
        (by omega)
    · glfertig
  | callInd p args hp hr =>
    simp only [groesseStmt] at hu hE hB hO
    obtain ⟨p', hpp, ⟨_, _⟩⟩ := hE _ p (by omega)
    obtain ⟨args', hargs, ⟨_, _⟩⟩ := argsS_rep hE _ args (by omega)
    refine ⟨.callInd p' args' hp hr, ?_, ?_⟩
    · simp only [groesseStmt]
      stm (sCallInd E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (mem_fnptrS hpp) <|
        Sz.mem_wenn hp <| Sz.mem_wenn hr <| Sz.mem_bind hargs <| Sz.mem_pure _)
        (by omega)
    · glfertig
  | locks L hr body =>
    simp only [groesseStmt] at hu hE hB hO
    obtain ⟨body', hbm, ⟨_, _, _, _, _, _⟩⟩ := hO.bl _ _ _ _ body (by omega)
    refine ⟨.locks L hr body', ?_, ?_⟩
    · simp only [groesseStmt]
      have hb := hbm (groesseBlock body' + 0) (by omega)
      stm (sLocks O), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.lock_mem L)) <|
        Sz.mem_wenn hr <| Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) (mem_ofTy hb) <| Sz.mem_pure _)
        (by omega)
    · glfertig
  | breaking i body =>
    simp only [groesseStmt] at hu hE hB hO
    obtain ⟨body', hb, ⟨_, _, _, _, _, _⟩⟩ := hB _ body (by omega)
    refine ⟨.breaking i body', ?_, ?_⟩
    · simp only [groesseStmt]
      stm (sBreaking Bs), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.inv_mem i)) <|
        Sz.mem_bind hb <| Sz.mem_pure _) (by omega)
    · glfertig
  | traverse t inv body =>
    simp only [groesseStmt] at hu hE hB hO
    obtain ⟨inv', hi, ⟨_, _⟩⟩ := hE _ inv (by omega)
    obtain ⟨body', hbm, ⟨_, _, _, _, _, _⟩⟩ := hO.bl _ _ _ _ body (by omega)
    refine ⟨.traverse t inv' body', ?_, ?_⟩
    · simp only [groesseStmt]
      have hb := hbm (groesseBlock body' + 0) (by omega)
      stm (sTraverse O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.tab_mem t)) <|
        Sz.mem_bindR (mem_tyS hi) (mem_ofTy hb) <| Sz.mem_pure _) (by omega)
    · glfertig
  | retry n bis body ueb =>
    simp only [groesseStmt] at hu hE hB hO
    obtain ⟨bis', hbis, ⟨_, _⟩⟩ := hE _ bis (by omega)
    obtain ⟨body', hbm, ⟨_, _, _, _, _, _⟩⟩ := hO.bl _ _ _ _ body (by omega)
    obtain ⟨ueb', hueb, ⟨_, _, _, _, _, _⟩⟩ := hB _ ueb (by omega)
    refine ⟨.retry n bis' body' ueb', ?_, ?_⟩
    · simp only [groesseStmt]
      have hb := hbm (groesseBlock body' + (groesseBlock ueb' + 0)) (by omega)
      stm (sRetry O E Bs), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (mem_nS (n := n) rfl (by omega)) <|
        Sz.mem_bindR (mem_tyS hbis) (mem_ofTy hb) <| Sz.mem_bind (mem_ofTy hueb) <| Sz.mem_pure _) (by omega)
    · glfertig
  | forever a inv body =>
    simp only [groesseStmt] at hu hE hB hO
    obtain ⟨inv', hi, ⟨_, _⟩⟩ := hE _ inv (by omega)
    obtain ⟨body', hbm, ⟨_, _, _, _, _, _⟩⟩ := hO.bl _ _ _ _ body (by omega)
    refine ⟨.forever a inv' body', ?_, ?_⟩
    · simp only [groesseStmt]
      have hb := hbm (groesseBlock body' + 0) (by omega)
      stm (sForever O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.annahme_mem a)) <|
        Sz.mem_bindR (mem_tyS hi) (mem_ofTy hb) <| Sz.mem_pure _) (by omega)
    · glfertig
  | axiomCall a args hae hw hg hd hgd =>
    simp only [groesseStmt] at hu hE hB hO
    obtain ⟨args', hargs, ⟨_, _⟩⟩ := argsS_rep hE _ args (by omega)
    refine ⟨.axiomCall a args' hae hw hg hd hgd, ?_, ?_⟩
    · simp only [groesseStmt]
      stm (sAxiomCall E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.ax_mem a)) <|
        Sz.mem_wenn hae <| Sz.mem_wenn hw <| Sz.mem_wenn hg <| Sz.mem_wenn hd <| Sz.mem_wenn hgd <|
        Sz.mem_bind hargs <| Sz.mem_pure _) (by omega)
    · glfertig
  | regWrite r hk e =>
    simp only [groesseStmt] at hu hE hB hO
    obtain ⟨e', he, ⟨_, _⟩⟩ := hE _ e (by omega)
    refine ⟨.regWrite r hk e', ?_, ?_⟩
    · simp only [groesseStmt]
      stm (sRegWrite E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.reg_mem r)) <|
        Sz.mem_wenn hk <| Sz.mem_bind (mem_tyS he) <| Sz.mem_pure _) (by omega)
    · glfertig
  | transition r hk m' hm hl maske bits =>
    simp only [groesseStmt] at hu hE hB hO
    refine ⟨.transition r hk m' hm hl maske bits, ?_, GlS.refl _⟩
    simp only [groesseStmt]
    stm sTransition, Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.reg_mem r)) <|
      Sz.mem_bind (Sz.mem_wahl (Aufz.reg_mem m')) <| Sz.mem_wenn hk <| Sz.mem_wenn hm <| Sz.mem_wenn hl <|
      Sz.mem_bind (mem_zW (n := maske) rfl (by omega)) <| Sz.mem_bind (mem_zW (n := bits) rfl (by omega)) <|
      Sz.mem_pure _) (by omega)
  | publish g e payload hp hw hL =>
    simp only [groesseStmt] at hu hE hB hO
    obtain ⟨e', he, ⟨_, _⟩⟩ := hE _ e (by omega)
    refine ⟨.publish g e' payload hp hw hL, ?_, ?_⟩
    · simp only [groesseStmt]
      subst hp
      stm (sPublish E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.glob_mem g)) <|
        Sz.mem_wenn hw <| Sz.mem_wenn hL <| Sz.mem_bind (mem_tyS he) <| Sz.mem_pure _) (by omega)
    · glfertig
  | advances mk a hmem hs =>
    refine ⟨.advances mk a hmem hs, ?_, GlS.refl _⟩
    simp only [groesseStmt]
    stm sAdvances, Sz.mem_blatt (List.mem_flatMap.2 ⟨.marke mk a, hmem, by
      dsimp only
      rw [dif_pos hmem, dif_pos hs]; simp only [List.mem_cons, List.not_mem_nil, or_false]⟩)
  | retires mk s hmem a =>
    refine ⟨.retires mk s hmem a, ?_, GlS.refl _⟩
    simp only [groesseStmt]
    stm sRetires, Sz.mem_blatt (List.mem_flatMap.2 ⟨.marke mk s, hmem, by
      dsimp only
      rw [dif_pos hmem]
      exact List.mem_map.2 ⟨a, Aufz.annahme_mem a, rfl⟩⟩)
  | ret e hΛ =>
    simp only [groesseStmt] at hu hE hB hO
    obtain ⟨e', herg, ⟨_, _⟩⟩ := ergS_rep hE e (by omega)
    refine ⟨.ret e' hΛ, ?_, ?_⟩
    · simp only [groesseStmt]
      stm (sRet E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (herg) <|
        Sz.mem_wenn hΛ <| Sz.mem_pure _) (by omega)
    · glfertig
  | retWhy r hΛ =>
    refine ⟨.retWhy r hΛ, ?_, GlS.refl _⟩
    simp only [groesseStmt]
    stm sRetWhy, Sz.mem_blatt (List.mem_flatMap.2 ⟨r, List.mem_finRange r, by rw [dif_pos hΛ]; simp only [List.mem_cons, List.not_mem_nil, or_false]⟩)
  | leave hl =>
    refine ⟨.leave hl, ?_, GlS.refl _⟩
    simp only [groesseStmt]
    stm sLeave, Sz.mem_blatt (by rw [dif_pos hl]; simp only [List.mem_cons, List.not_mem_nil, or_false])
  | next hl =>
    refine ⟨.next hl, ?_, GlS.refl _⟩
    simp only [groesseStmt]
    stm sNext, Sz.mem_blatt (by rw [dif_pos hl]; simp only [List.mem_cons, List.not_mem_nil, or_false])

end Gabbro.Grammatik.Gen
