/-
  File:      Grammatik/Gen/Erzeuger/BlockVollst.lean
  Subject:   COMPLETENESS of the block and end-block clauses, one step each (see `AnweisungVollst.lean`).
-/
import Grammatik.Gen.Erzeuger.AnweisungVollst

namespace Gabbro.Grammatik.Gen

set_option linter.unusedSectionVars false

open Gabbro.Grammatik

variable {D : Deklaration} [Aufz D] [Zahlen] {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

/-- Close `x ∈ blockS ...` / `x ∈ endS ...` from `hc : x ∈ clause k`. -/
macro "blk " c:term ", " h:term : tactic =>
  `(tactic| exact Sz.mem_alle (c := $c) (by simp) $h)

set_option maxHeartbeats 8000000 in
/-- **Completeness of the block clauses.** -/
theorem blockS_vollst (O : Orakel V) (E : Sz (SE D Γ Λ)) (Ss : Sz (SS D V l Γ Λ)) (Bs : Sz (SB D V l Γ Λ))
    (Ns : Sz (Endblock D V l Γ Λ)) {Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') (hu : groesseBlock b < unendlich)
    (hE : Unter E (groesseBlock b)) (hS : SUnter Ss (groesseBlock b)) (hB : BUnter Bs (groesseBlock b))
    (hN : NUnter Ns (groesseBlock b)) (hO : OUnter O (groesseBlock b)) :
    (⟨Λ', b⟩ : SB D V l Γ Λ) ∈ blockS O E Ss Bs Ns (groesseBlock b) := by
  cases b with
  | nil =>
    simp only [groesseBlock]
    blk bNil, Sz.mem_blatt (by simp)
  | cons s rest =>
    simp only [groesseBlock] at hu hE hS hB hN hO ⊢
    have hs := hS _ s (by omega)
    have hr := hO.bl (groesseBlock rest + 0) _ _ _ _ rest (by omega) (by omega)
    blk (bCons O Ss), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bindS hs hr <| Sz.mem_pure _) (by omega)
  | bind e rest =>
    simp only [groesseBlock] at hu hE hS hB hN hO ⊢
    have he := hE _ e (by omega)
    have hr := hO.bl (groesseBlock rest + 0) _ _ _ _ rest (by omega) (by omega)
    blk (bBind O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bindS he hr <| Sz.mem_pure _) (by omega)
  | bindCall f args he hp hr rest =>
    simp only [groesseBlock] at hu hE hS hB hN hO ⊢
    have hr' := hO.bl (groesseBlock rest + 0) _ _ _ _ rest (by omega) (by omega)
    blk (bBindCall O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.fn_mem f)) <|
      mem_mitSome he <| Sz.mem_wenn hp <| Sz.mem_wenn hr <|
      Sz.mem_bindR (mem_argsS hE _ args (by omega)) hr' <| Sz.mem_pure _) (by omega)
  | bindCallInd p args he hp hr rest =>
    simp only [groesseBlock] at hu hE hS hB hN hO ⊢
    have hpp := hE _ p (by omega)
    have hr' := hO.bl (groesseBlock rest + 0) _ _ _ _ rest (by omega) (by omega)
    blk (bBindCallInd O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (mem_fnptrS hpp) <|
      mem_mitSome he <| Sz.mem_wenn hp <| Sz.mem_wenn hr <|
      Sz.mem_bindR (mem_argsS hE _ args (by omega)) hr' <| Sz.mem_pure _) (by omega)
  | bindCallElse f args he hp hr err rest =>
    simp only [groesseBlock] at hu hE hS hB hN hO ⊢
    have herr := hO.en (groesseEnd err + (0 + (groesseBlock rest + 0))) _ _ _ err (by omega) (by omega)
    have hr' := hO.bl (groesseBlock rest + 0) _ _ _ _ rest (by omega) (by omega)
    blk (bBindCallElse O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.fn_mem f)) <|
      mem_mitSome he <| Sz.mem_wenn hp <| Sz.mem_wenn hr <|
      Sz.mem_bindR (mem_argsS hE _ args (by omega)) herr <|
      Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <| Sz.mem_pure _) (by omega)
  | bindAxiom a args he hw hg hd hgd rest =>
    simp only [groesseBlock] at hu hE hS hB hN hO ⊢
    have hr' := hO.bl (groesseBlock rest + 0) _ _ _ _ rest (by omega) (by omega)
    blk (bBindAxiom O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.ax_mem a)) <|
      mem_mitSome he <| Sz.mem_wenn hw <| Sz.mem_wenn hg <| Sz.mem_wenn hd <| Sz.mem_wenn hgd <|
      Sz.mem_bindR (mem_argsS hE _ args (by omega)) hr' <| Sz.mem_pure _) (by omega)
  | bindAxiomElse a args he hr hw hg hd hgd err rest =>
    simp only [groesseBlock] at hu hE hS hB hN hO ⊢
    have herr := hO.en (groesseEnd err + (0 + (groesseBlock rest + 0))) _ _ _ err (by omega) (by omega)
    have hr' := hO.bl (groesseBlock rest + 0) _ _ _ _ rest (by omega) (by omega)
    blk (bBindAxiomElse O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.ax_mem a)) <|
      mem_mitSome he <| Sz.mem_wenn hr <| Sz.mem_wenn hw <| Sz.mem_wenn hg <| Sz.mem_wenn hd <|
      Sz.mem_wenn hgd <| Sz.mem_bindR (mem_argsS hE _ args (by omega)) herr <|
      Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <| Sz.mem_pure _) (by omega)
  | regRead r hk rest =>
    simp only [groesseBlock] at hu hE hS hB hN hO ⊢
    have hr' := hO.bl (groesseBlock rest + 0) _ _ _ _ rest (by omega) (by omega)
    blk (bRegRead O), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.reg_mem r)) <|
      Sz.mem_wenn hk <| Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <| Sz.mem_pure _) (by omega)
  | regReadElse r hk z sonst rest =>
    simp only [groesseBlock] at hu hE hS hB hN hO ⊢
    have hz := hO.ex (groesseExpr z + (groesseEnd sonst + (0 + (groesseBlock rest + 0)))) _ _ _ z
      (by omega) (by omega)
    have hso := hN sonst (by omega)
    have hr' := hO.bl (groesseBlock rest + 0) _ _ _ _ rest (by omega) (by omega)
    blk (bRegReadElse O Ns), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.reg_mem r)) <|
      Sz.mem_wenn hk <| Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) (mem_tyS hz) <|
      Sz.mem_bind hso <| Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <| Sz.mem_pure _) (by omega)
  | awaits g payload hp hL rest =>
    simp only [groesseBlock] at hu hE hS hB hN hO ⊢
    subst hp
    have hr' := hO.bl (groesseBlock rest + 0) _ _ _ _ rest (by omega) (by omega)
    blk (bAwaits O), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.glob_mem g)) <|
      Sz.mem_wenn hL <| Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <| Sz.mem_pure _) (by omega)
  | exchange g neu hw hL rest =>
    simp only [groesseBlock] at hu hE hS hB hN hO ⊢
    have hne := hO.ex (groesseExpr neu + (0 + (groesseBlock rest + 0))) _ _ _ neu (by omega) (by omega)
    have hr' := hO.bl (groesseBlock rest + 0) _ _ _ _ rest (by omega) (by omega)
    blk (bExchange O), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.glob_mem g)) <|
      Sz.mem_wenn hw <| Sz.mem_wenn hL <| Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) (mem_tyS hne) <|
      Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <| Sz.mem_pure _) (by omega)
  | narrow e lo' hi' sonst rest =>
    simp only [groesseBlock] at hu hE hS hB hN hO ⊢
    have he := hE _ e (by omega)
    have hso := hN sonst (by omega)
    have hr' := hO.bl (groesseBlock rest + 0) _ _ _ _ rest (by omega) (by omega)
    blk (bNarrow O E Ns), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (mem_intS he) <|
      Sz.mem_bind (mem_zS (n := lo') rfl (by omega)) <| Sz.mem_bind (mem_zS (n := hi') rfl (by omega)) <|
      Sz.mem_bind hso <| Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <| Sz.mem_pure _) (by omega)
  | check c sonst rest =>
    simp only [groesseBlock] at hu hE hS hB hN hO ⊢
    have hc := hE _ c (by omega)
    have hso := hN sonst (by omega)
    have hre := hB _ rest (by omega)
    blk (bCheck E Bs Ns), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (mem_tyS hc) <| Sz.mem_bind hso <|
      Sz.mem_bind hre <| Sz.mem_pure _) (by omega)
  | float op a b' lo hi rest =>
    simp only [groesseBlock, groessePaar] at hu hE hS hB hN hO ⊢
    have ha := hE _ a (by omega)
    have hb := hE _ b' (by omega)
    have hlo : lo ∈ paarS (Zahlen.kostP lo) := mem_paarS rfl (by omega)
    have hhi : hi ∈ paarS (Zahlen.kostP hi) := mem_paarS rfl (by omega)
    have hr' := hO.bl (groesseBlock rest + 0) _ _ _ _ rest (by omega) (by omega)
    blk (bFloat O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (mem_gleitOps op)) <|
      Sz.mem_bind (mem_flS ha) <| Sz.mem_bind (mem_flS hb) <| Sz.mem_bind hlo <| Sz.mem_bind hhi <|
      Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <| Sz.mem_pure _) (by omega)
  | floatLit q lo hi rest =>
    simp only [groesseBlock, groessePaar] at hu hE hS hB hN hO ⊢
    have hq : q ∈ paarS (Zahlen.kostP q) := mem_paarS rfl (by omega)
    have hlo : lo ∈ paarS (Zahlen.kostP lo) := mem_paarS rfl (by omega)
    have hhi : hi ∈ paarS (Zahlen.kostP hi) := mem_paarS rfl (by omega)
    have hr' := hO.bl (groesseBlock rest + 0) _ _ _ _ rest (by omega) (by omega)
    blk (bFloatLit O), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind hq <| Sz.mem_bind hlo <|
      Sz.mem_bind hhi <| Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <| Sz.mem_pure _) (by omega)
  | floatOf e lo hi rest =>
    simp only [groesseBlock, groessePaar] at hu hE hS hB hN hO ⊢
    have he := hE _ e (by omega)
    have hlo : lo ∈ paarS (Zahlen.kostP lo) := mem_paarS rfl (by omega)
    have hhi : hi ∈ paarS (Zahlen.kostP hi) := mem_paarS rfl (by omega)
    have hr' := hO.bl (groesseBlock rest + 0) _ _ _ _ rest (by omega) (by omega)
    blk (bFloatOf O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (mem_intS he) <| Sz.mem_bind hlo <|
      Sz.mem_bind hhi <| Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <| Sz.mem_pure _) (by omega)
  | floatNarrow e lo hi sonst rest =>
    simp only [groesseBlock, groessePaar] at hu hE hS hB hN hO ⊢
    have he := hE _ e (by omega)
    have hso := hN sonst (by omega)
    have hlo : lo ∈ paarS (Zahlen.kostP lo) := mem_paarS rfl (by omega)
    have hhi : hi ∈ paarS (Zahlen.kostP hi) := mem_paarS rfl (by omega)
    have hr' := hO.bl (groesseBlock rest + 0) _ _ _ _ rest (by omega) (by omega)
    blk (bFloatNarrow O E Ns), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (mem_flS he) <| Sz.mem_bind hlo <|
      Sz.mem_bind hhi <| Sz.mem_bind hso <| Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <|
      Sz.mem_pure _) (by omega)

set_option maxHeartbeats 8000000 in
/-- **Completeness of the end-block clauses.** -/
theorem endS_vollst (O : Orakel V) (E : Sz (SE D Γ Λ)) (Ss : Sz (SS D V l Γ Λ)) (e : Endblock D V l Γ Λ)
    (hu : groesseEnd e < unendlich) (hE : Unter E (groesseEnd e)) (hS : SUnter Ss (groesseEnd e))
    (hO : OUnter O (groesseEnd e)) : e ∈ endS O E Ss (groesseEnd e) := by
  cases e with
  | ret x hΛ =>
    simp only [groesseEnd] at hu hE hS hO ⊢
    blk (eRet E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (mem_ergS hE x (by omega)) <|
      Sz.mem_wenn hΛ <| Sz.mem_pure _) (by omega)
  | retWhy r hΛ =>
    simp only [groesseEnd]
    blk eRetWhy, Sz.mem_blatt (List.mem_flatMap.2 ⟨r, List.mem_finRange r, by rw [dif_pos hΛ]; simp⟩)
  | leave hl =>
    simp only [groesseEnd]
    blk eLeave, Sz.mem_blatt (by rw [dif_pos hl]; simp)
  | next hl =>
    simp only [groesseEnd]
    blk eNext, Sz.mem_blatt (by rw [dif_pos hl]; simp)
  | cons s rest =>
    simp only [groesseEnd] at hu hE hS hO ⊢
    have hs := hS _ s (by omega)
    have hr := hO.en (groesseEnd rest + 0) _ _ _ rest (by omega) (by omega)
    blk (eCons O Ss), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bindS hs hr <| Sz.mem_pure _) (by omega)
  | bind x rest =>
    simp only [groesseEnd] at hu hE hS hO ⊢
    have hx := hE _ x (by omega)
    have hr := hO.en (groesseEnd rest + 0) _ _ _ rest (by omega) (by omega)
    blk (eBind O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bindS hx hr <| Sz.mem_pure _) (by omega)
  | bindAxiom a args he hw hg hd hgd rest =>
    simp only [groesseEnd] at hu hE hS hO ⊢
    have hr := hO.en (groesseEnd rest + 0) _ _ _ rest (by omega) (by omega)
    blk (eBindAxiom O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.ax_mem a)) <|
      mem_mitSome he <| Sz.mem_wenn hw <| Sz.mem_wenn hg <| Sz.mem_wenn hd <| Sz.mem_wenn hgd <|
      Sz.mem_bindR (mem_argsS hE _ args (by omega)) hr <| Sz.mem_pure _) (by omega)
  | bindAxiomElse a args he hr hw hg hd hgd err rest =>
    simp only [groesseEnd] at hu hE hS hO ⊢
    have herr := hO.en (groesseEnd err + (0 + (groesseEnd rest + 0))) _ _ _ err (by omega) (by omega)
    have hr' := hO.en (groesseEnd rest + 0) _ _ _ rest (by omega) (by omega)
    blk (eBindAxiomElse O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.ax_mem a)) <|
      mem_mitSome he <| Sz.mem_wenn hr <| Sz.mem_wenn hw <| Sz.mem_wenn hg <| Sz.mem_wenn hd <|
      Sz.mem_wenn hgd <| Sz.mem_bindR (mem_argsS hE _ args (by omega)) herr <|
      Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <| Sz.mem_pure _) (by omega)

end Gabbro.Grammatik.Gen
