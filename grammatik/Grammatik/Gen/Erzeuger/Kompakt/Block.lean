/-
  File:      Grammatik/Gen/Erzeuger/Kompakt/Block.lean
  Subject:   REPRESENTATIVES of the blocks and end blocks (`blockS_rep`, `endS_rep`), as `Kompakt/Anweisung.lean` for the
             statements: the same constructor over the parts' representatives, standing for it.
-/
import Grammatik.Gen.Erzeuger.Kompakt.Anweisung
import Grammatik.Gen.Erzeuger.BlockVollst

namespace Gabbro.Grammatik.Gen

set_option linter.unusedSectionVars false

open Gabbro.Grammatik

variable {D : Deklaration} [Aufz D] [Zahlen] {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

set_option maxHeartbeats 16000000 in
/-- **Representatives of the blocks.** -/
theorem blockS_rep (O : Orakel V) (E : Sz (SE D Γ Λ)) (Ss : Sz (SS D V l Γ Λ)) (Bs : Sz (SB D V l Γ Λ))
    (Ns : Sz (Endblock D V l Γ Λ)) {Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') (hu : groesseBlock b < unendlich)
    (hE : ERU E (groesseBlock b)) (hS : SRU Ss (groesseBlock b)) (hB : BRU Bs (groesseBlock b))
    (hN : NRU Ns (groesseBlock b)) (hO : ORU O (groesseBlock b)) :
    ∃ b' : Block D V l Γ Λ Λ', (⟨Λ', b'⟩ : SB D V l Γ Λ) ∈ blockS O E Ss Bs Ns (groesseBlock b') ∧ GlB b' b := by
  cases b with
  | nil =>
    refine ⟨.nil, ?_, GlB.refl _⟩
    simp only [groesseBlock]
    blk bNil, Sz.mem_blatt (by simp)
  | cons s rest =>
    simp only [groesseBlock] at hu hE hS hB hN hO
    obtain ⟨s', hs, ⟨_, _, _, _, _, _⟩⟩ := hS _ s (by omega)
    obtain ⟨rest', hrm, ⟨_, _, _, _, _, _⟩⟩ := hO.bl _ _ _ _ rest (by omega)
    refine ⟨.cons s' rest', ?_, ?_⟩
    · simp only [groesseBlock]
      have hr := hrm (groesseBlock rest' + 0) (by omega)
      blk (bCons O Ss), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bindS hs hr <| Sz.mem_pure _) (by omega)
    · glfertig
  | @bind _ _ τ _ _ e rest =>
    simp only [groesseBlock] at hu hE hS hB hN hO
    obtain ⟨e', hem, ⟨_, _⟩⟩ := hE _ e (by omega)
    obtain ⟨rest', hrm, ⟨_, _, _, _, _, _⟩⟩ := hO.bl _ _ _ _ rest (by omega)
    refine ⟨.bind e' rest', ?_, ?_⟩
    · simp only [groesseBlock]
      have hr := hrm (groesseBlock rest' + 0) (by omega)
      have hok := bindOk_of (τ := τ) (by omega)
      have h0 := kostT_null hok
      have he : (⟨τ, e'⟩ : SE D Γ Λ) ∈ (E (groesseExpr e')).filter (fun p => Zahlen.bindOk p.1) :=
        List.mem_filter.2 ⟨hem, hok⟩
      blk (bBind O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bindS he hr <| Sz.mem_pure _) (by omega)
    · glfertig
  | bindCall f args he hp hr rest =>
    simp only [groesseBlock] at hu hE hS hB hN hO
    obtain ⟨rest', hr'm, ⟨_, _, _, _, _, _⟩⟩ := hO.bl _ _ _ _ rest (by omega)
    obtain ⟨args', hargs, ⟨_, _⟩⟩ := argsS_rep hE _ args (by omega)
    refine ⟨.bindCall f args' he hp hr rest', ?_, ?_⟩
    · simp only [groesseBlock]
      have hr' := hr'm (groesseBlock rest' + 0) (by omega)
      blk (bBindCall O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.fn_mem f)) <|
        mem_mitSome he <| Sz.mem_wenn hp <| Sz.mem_wenn hr <|
        Sz.mem_bindR hargs hr' <| Sz.mem_pure _) (by omega)
    · glfertig
  | bindCallInd p args he hp hr rest =>
    simp only [groesseBlock] at hu hE hS hB hN hO
    obtain ⟨p', hpp, ⟨_, _⟩⟩ := hE _ p (by omega)
    obtain ⟨rest', hr'm, ⟨_, _, _, _, _, _⟩⟩ := hO.bl _ _ _ _ rest (by omega)
    obtain ⟨args', hargs, ⟨_, _⟩⟩ := argsS_rep hE _ args (by omega)
    refine ⟨.bindCallInd p' args' he hp hr rest', ?_, ?_⟩
    · simp only [groesseBlock]
      have hr' := hr'm (groesseBlock rest' + 0) (by omega)
      blk (bBindCallInd O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (mem_fnptrS hpp) <|
        mem_mitSome he <| Sz.mem_wenn hp <| Sz.mem_wenn hr <|
        Sz.mem_bindR hargs hr' <| Sz.mem_pure _) (by omega)
    · glfertig
  | bindCallElse f args he hp hr err rest =>
    simp only [groesseBlock] at hu hE hS hB hN hO
    obtain ⟨err', herrm, ⟨_, _, _, _, _, _⟩⟩ := hO.en _ _ _ err (by omega)
    obtain ⟨rest', hr'm, ⟨_, _, _, _, _, _⟩⟩ := hO.bl _ _ _ _ rest (by omega)
    obtain ⟨args', hargs, ⟨_, _⟩⟩ := argsS_rep hE _ args (by omega)
    refine ⟨.bindCallElse f args' he hp hr err' rest', ?_, ?_⟩
    · simp only [groesseBlock]
      have hr' := hr'm (groesseBlock rest' + 0) (by omega)
      have herr := herrm (groesseEnd err' + (0 + (groesseBlock rest' + 0))) (by omega)
      blk (bBindCallElse O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.fn_mem f)) <|
        mem_mitSome he <| Sz.mem_wenn hp <| Sz.mem_wenn hr <|
        Sz.mem_bindR hargs herr <|
        Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <| Sz.mem_pure _) (by omega)
    · glfertig
  | bindAxiom a args he hw hg hd hgd rest =>
    simp only [groesseBlock] at hu hE hS hB hN hO
    obtain ⟨rest', hr'm, ⟨_, _, _, _, _, _⟩⟩ := hO.bl _ _ _ _ rest (by omega)
    obtain ⟨args', hargs, ⟨_, _⟩⟩ := argsS_rep hE _ args (by omega)
    refine ⟨.bindAxiom a args' he hw hg hd hgd rest', ?_, ?_⟩
    · simp only [groesseBlock]
      have hr' := hr'm (groesseBlock rest' + 0) (by omega)
      blk (bBindAxiom O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.ax_mem a)) <|
        mem_mitSome he <| Sz.mem_wenn hw <| Sz.mem_wenn hg <| Sz.mem_wenn hd <| Sz.mem_wenn hgd <|
        Sz.mem_bindR hargs hr' <| Sz.mem_pure _) (by omega)
    · glfertig
  | bindAxiomElse a args he hr hw hg hd hgd err rest =>
    simp only [groesseBlock] at hu hE hS hB hN hO
    obtain ⟨err', herrm, ⟨_, _, _, _, _, _⟩⟩ := hO.en _ _ _ err (by omega)
    obtain ⟨rest', hr'm, ⟨_, _, _, _, _, _⟩⟩ := hO.bl _ _ _ _ rest (by omega)
    obtain ⟨args', hargs, ⟨_, _⟩⟩ := argsS_rep hE _ args (by omega)
    refine ⟨.bindAxiomElse a args' he hr hw hg hd hgd err' rest', ?_, ?_⟩
    · simp only [groesseBlock]
      have hr' := hr'm (groesseBlock rest' + 0) (by omega)
      have herr := herrm (groesseEnd err' + (0 + (groesseBlock rest' + 0))) (by omega)
      blk (bBindAxiomElse O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.ax_mem a)) <|
        mem_mitSome he <| Sz.mem_wenn hr <| Sz.mem_wenn hw <| Sz.mem_wenn hg <| Sz.mem_wenn hd <|
        Sz.mem_wenn hgd <| Sz.mem_bindR hargs herr <|
        Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <| Sz.mem_pure _) (by omega)
    · glfertig
  | regRead r hk rest =>
    simp only [groesseBlock] at hu hE hS hB hN hO
    obtain ⟨rest', hr'm, ⟨_, _, _, _, _, _⟩⟩ := hO.bl _ _ _ _ rest (by omega)
    refine ⟨.regRead r hk rest', ?_, ?_⟩
    · simp only [groesseBlock]
      have hr' := hr'm (groesseBlock rest' + 0) (by omega)
      blk (bRegRead O), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.reg_mem r)) <|
        Sz.mem_wenn hk <| Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <| Sz.mem_pure _) (by omega)
    · glfertig
  | regReadElse r hk z sonst rest =>
    simp only [groesseBlock] at hu hE hS hB hN hO
    obtain ⟨z', hzm, ⟨_, _⟩⟩ := hO.ex _ _ _ z (by omega)
    obtain ⟨sonst', hso, ⟨_, _, _, _, _, _⟩⟩ := hN sonst (by omega)
    obtain ⟨rest', hr'm, ⟨_, _, _, _, _, _⟩⟩ := hO.bl _ _ _ _ rest (by omega)
    refine ⟨.regReadElse r hk z' sonst' rest', ?_, ?_⟩
    · simp only [groesseBlock]
      have hr' := hr'm (groesseBlock rest' + 0) (by omega)
      have hz := hzm (groesseExpr z' + (groesseEnd sonst' + (0 + (groesseBlock rest' + 0)))) (by omega)
      blk (bRegReadElse O Ns), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.reg_mem r)) <|
        Sz.mem_wenn hk <| Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) (mem_tyS hz) <|
        Sz.mem_bind hso <| Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <| Sz.mem_pure _) (by omega)
    · glfertig
  | awaits g payload hp hL hat rest =>
    simp only [groesseBlock] at hu hE hS hB hN hO
    obtain ⟨rest', hr'm, ⟨_, _, _, _, _, _⟩⟩ := hO.bl _ _ _ _ rest (by omega)
    refine ⟨.awaits g payload hp hL hat rest', ?_, ?_⟩
    · simp only [groesseBlock]
      have hr' := hr'm (groesseBlock rest' + 0) (by omega)
      subst hp
      blk (bAwaits O), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.glob_mem g)) <|
        Sz.mem_wenn hL <| Sz.mem_wenn hat <| Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <| Sz.mem_pure _) (by omega)
    · glfertig
  | exchange g neu hw hL rest =>
    simp only [groesseBlock] at hu hE hS hB hN hO
    obtain ⟨neu', hnem, ⟨_, _⟩⟩ := hO.ex _ _ _ neu (by omega)
    obtain ⟨rest', hr'm, ⟨_, _, _, _, _, _⟩⟩ := hO.bl _ _ _ _ rest (by omega)
    refine ⟨.exchange g neu' hw hL rest', ?_, ?_⟩
    · simp only [groesseBlock]
      have hr' := hr'm (groesseBlock rest' + 0) (by omega)
      have hne := hnem (groesseExpr neu' + (0 + (groesseBlock rest' + 0))) (by omega)
      blk (bExchange O), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.glob_mem g)) <|
        Sz.mem_wenn hw <| Sz.mem_wenn hL <| Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) (mem_tyS hne) <|
        Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <| Sz.mem_pure _) (by omega)
    · glfertig
  | narrow e lo' hi' sonst rest =>
    simp only [groesseBlock] at hu hE hS hB hN hO
    obtain ⟨e', he, ⟨_, _⟩⟩ := hE _ e (by omega)
    obtain ⟨sonst', hso, ⟨_, _, _, _, _, _⟩⟩ := hN sonst (by omega)
    obtain ⟨rest', hr'm, ⟨_, _, _, _, _, _⟩⟩ := hO.bl _ _ _ _ rest (by omega)
    refine ⟨.narrow e' lo' hi' sonst' rest', ?_, ?_⟩
    · simp only [groesseBlock]
      have hr' := hr'm (groesseBlock rest' + 0) (by omega)
      have hok := bindOk_of (τ := Ty.int lo' hi') (by omega)
      have h0 := kostT_null hok
      blk (bNarrow O E Ns), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (mem_intS he) <|
        Sz.mem_bind (mem_zS (n := lo') rfl (by omega)) <| Sz.mem_bind (mem_zS (n := hi') rfl (by omega)) <|
        Sz.mem_wenn hok <| Sz.mem_bind hso <| Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <| Sz.mem_pure _) (by omega)
    · glfertig
  | check c sonst rest =>
    simp only [groesseBlock] at hu hE hS hB hN hO
    obtain ⟨c', hc, ⟨_, _⟩⟩ := hE _ c (by omega)
    obtain ⟨sonst', hso, ⟨_, _, _, _, _, _⟩⟩ := hN sonst (by omega)
    obtain ⟨rest', hre, ⟨_, _, _, _, _, _⟩⟩ := hB _ rest (by omega)
    refine ⟨.check c' sonst' rest', ?_, ?_⟩
    · simp only [groesseBlock]
      blk (bCheck E Bs Ns), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (mem_tyS hc) <| Sz.mem_bind hso <|
        Sz.mem_bind hre <| Sz.mem_pure _) (by omega)
    · glfertig
  | float op a b lo hi rest =>
    simp only [groesseBlock, groessePaar] at hu hE hS hB hN hO
    obtain ⟨a', ha, ⟨_, _⟩⟩ := hE _ a (by omega)
    obtain ⟨b', hb, ⟨_, _⟩⟩ := hE _ b (by omega)
    obtain ⟨rest', hr'm, ⟨_, _, _, _, _, _⟩⟩ := hO.bl _ _ _ _ rest (by omega)
    refine ⟨.float op a' b' lo hi rest', ?_, ?_⟩
    · simp only [groesseBlock, groessePaar]
      have hr' := hr'm (groesseBlock rest' + 0) (by omega)
      have hlo : lo ∈ paarS (Zahlen.kostP lo) := mem_paarS rfl (by omega)
      have hhi : hi ∈ paarS (Zahlen.kostP hi) := mem_paarS rfl (by omega)
      have hok := bindOk_of (τ := Ty.fl lo hi) (by omega)
      have h0 := kostT_null hok
      blk (bFloat O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (mem_gleitOps op)) <|
        Sz.mem_bind (mem_flS ha) <| Sz.mem_bind (mem_flS hb) <| Sz.mem_bind hlo <| Sz.mem_bind hhi <|
        Sz.mem_wenn hok <| Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <| Sz.mem_pure _) (by omega)
    · glfertig
  | floatLit q lo hi rest =>
    simp only [groesseBlock, groessePaar] at hu hE hS hB hN hO
    obtain ⟨rest', hr'm, ⟨_, _, _, _, _, _⟩⟩ := hO.bl _ _ _ _ rest (by omega)
    refine ⟨.floatLit q lo hi rest', ?_, ?_⟩
    · simp only [groesseBlock, groessePaar]
      have hr' := hr'm (groesseBlock rest' + 0) (by omega)
      have hq : q ∈ paarS (Zahlen.kostP q) := mem_paarS rfl (by omega)
      have hlo : lo ∈ paarS (Zahlen.kostP lo) := mem_paarS rfl (by omega)
      have hhi : hi ∈ paarS (Zahlen.kostP hi) := mem_paarS rfl (by omega)
      have hok := bindOk_of (τ := Ty.fl lo hi) (by omega)
      have h0 := kostT_null hok
      blk (bFloatLit O), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind hq <| Sz.mem_bind hlo <|
        Sz.mem_bind hhi <| Sz.mem_wenn hok <| Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <| Sz.mem_pure _) (by omega)
    · glfertig
  | floatOf e lo hi rest =>
    simp only [groesseBlock, groessePaar] at hu hE hS hB hN hO
    obtain ⟨e', he, ⟨_, _⟩⟩ := hE _ e (by omega)
    obtain ⟨rest', hr'm, ⟨_, _, _, _, _, _⟩⟩ := hO.bl _ _ _ _ rest (by omega)
    refine ⟨.floatOf e' lo hi rest', ?_, ?_⟩
    · simp only [groesseBlock, groessePaar]
      have hr' := hr'm (groesseBlock rest' + 0) (by omega)
      have hlo : lo ∈ paarS (Zahlen.kostP lo) := mem_paarS rfl (by omega)
      have hhi : hi ∈ paarS (Zahlen.kostP hi) := mem_paarS rfl (by omega)
      have hok := bindOk_of (τ := Ty.fl lo hi) (by omega)
      have h0 := kostT_null hok
      blk (bFloatOf O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (mem_intS he) <| Sz.mem_bind hlo <|
        Sz.mem_bind hhi <| Sz.mem_wenn hok <| Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <| Sz.mem_pure _) (by omega)
    · glfertig
  | floatNarrow e lo hi sonst rest =>
    simp only [groesseBlock, groessePaar] at hu hE hS hB hN hO
    obtain ⟨e', he, ⟨_, _⟩⟩ := hE _ e (by omega)
    obtain ⟨sonst', hso, ⟨_, _, _, _, _, _⟩⟩ := hN sonst (by omega)
    obtain ⟨rest', hr'm, ⟨_, _, _, _, _, _⟩⟩ := hO.bl _ _ _ _ rest (by omega)
    refine ⟨.floatNarrow e' lo hi sonst' rest', ?_, ?_⟩
    · simp only [groesseBlock, groessePaar]
      have hr' := hr'm (groesseBlock rest' + 0) (by omega)
      have hlo : lo ∈ paarS (Zahlen.kostP lo) := mem_paarS rfl (by omega)
      have hhi : hi ∈ paarS (Zahlen.kostP hi) := mem_paarS rfl (by omega)
      have hok := bindOk_of (τ := Ty.fl lo hi) (by omega)
      have h0 := kostT_null hok
      blk (bFloatNarrow O E Ns), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (mem_flS he) <| Sz.mem_bind hlo <|
        Sz.mem_bind hhi <| Sz.mem_wenn hok <| Sz.mem_bind hso <| Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <|
        Sz.mem_pure _) (by omega)
    · glfertig

set_option maxHeartbeats 16000000 in
/-- **Representatives of the end blocks.** -/
theorem endS_rep (O : Orakel V) (E : Sz (SE D Γ Λ)) (Ss : Sz (SS D V l Γ Λ)) (e : Endblock D V l Γ Λ)
    (hu : groesseEnd e < unendlich) (hE : ERU E (groesseEnd e)) (hS : SRU Ss (groesseEnd e))
    (hO : ORU O (groesseEnd e)) : ∃ e' : Endblock D V l Γ Λ, e' ∈ endS O E Ss (groesseEnd e') ∧ GlN e' e := by
  cases e with
  | ret x hΛ =>
    simp only [groesseEnd] at hu hE hS hO
    obtain ⟨x', herg, ⟨_, _⟩⟩ := ergS_rep hE x (by omega)
    refine ⟨.ret x' hΛ, ?_, ?_⟩
    · simp only [groesseEnd]
      blk (eRet E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (herg) <|
        Sz.mem_wenn hΛ <| Sz.mem_pure _) (by omega)
    · glfertig
  | retWhy r hΛ =>
    refine ⟨.retWhy r hΛ, ?_, GlN.refl _⟩
    simp only [groesseEnd]
    blk eRetWhy, Sz.mem_blatt (List.mem_flatMap.2 ⟨r, List.mem_finRange r, by rw [dif_pos hΛ]; simp⟩)
  | leave hl =>
    refine ⟨.leave hl, ?_, GlN.refl _⟩
    simp only [groesseEnd]
    blk eLeave, Sz.mem_blatt (by rw [dif_pos hl]; simp)
  | next hl =>
    refine ⟨.next hl, ?_, GlN.refl _⟩
    simp only [groesseEnd]
    blk eNext, Sz.mem_blatt (by rw [dif_pos hl]; simp)
  | cons s rest =>
    simp only [groesseEnd] at hu hE hS hO
    obtain ⟨s', hs, ⟨_, _, _, _, _, _⟩⟩ := hS _ s (by omega)
    obtain ⟨rest', hrm, ⟨_, _, _, _, _, _⟩⟩ := hO.en _ _ _ rest (by omega)
    refine ⟨.cons s' rest', ?_, ?_⟩
    · simp only [groesseEnd]
      have hr := hrm (groesseEnd rest' + 0) (by omega)
      blk (eCons O Ss), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bindS hs hr <| Sz.mem_pure _) (by omega)
    · glfertig
  | @bind _ _ τ _ x rest =>
    simp only [groesseEnd] at hu hE hS hO
    obtain ⟨x', hem, ⟨_, _⟩⟩ := hE _ x (by omega)
    obtain ⟨rest', hrm, ⟨_, _, _, _, _, _⟩⟩ := hO.en _ _ _ rest (by omega)
    refine ⟨.bind x' rest', ?_, ?_⟩
    · simp only [groesseEnd]
      have hr := hrm (groesseEnd rest' + 0) (by omega)
      have hok := bindOk_of (τ := τ) (by omega)
      have h0 := kostT_null hok
      have he : (⟨τ, x'⟩ : SE D Γ Λ) ∈ (E (groesseExpr x')).filter (fun p => Zahlen.bindOk p.1) :=
        List.mem_filter.2 ⟨hem, hok⟩
      blk (eBind O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bindS he hr <| Sz.mem_pure _) (by omega)
    · glfertig
  | bindCall f args he hp hr rest =>
    simp only [groesseEnd] at hu hE hS hO
    obtain ⟨rest', hr'm, ⟨_, _, _, _, _, _⟩⟩ := hO.en _ _ _ rest (by omega)
    obtain ⟨args', hargs, ⟨_, _⟩⟩ := argsS_rep hE _ args (by omega)
    refine ⟨.bindCall f args' he hp hr rest', ?_, ?_⟩
    · simp only [groesseEnd]
      have hr' := hr'm (groesseEnd rest' + 0) (by omega)
      blk (eBindCall O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.fn_mem f)) <|
        mem_mitSome he <| Sz.mem_wenn hp <| Sz.mem_wenn hr <|
        Sz.mem_bindR hargs hr' <| Sz.mem_pure _) (by omega)
    · glfertig
  | bindCallElse f args he hp hr err rest =>
    simp only [groesseEnd] at hu hE hS hO
    obtain ⟨err', herrm, ⟨_, _, _, _, _, _⟩⟩ := hO.en _ _ _ err (by omega)
    obtain ⟨rest', hr'm, ⟨_, _, _, _, _, _⟩⟩ := hO.en _ _ _ rest (by omega)
    obtain ⟨args', hargs, ⟨_, _⟩⟩ := argsS_rep hE _ args (by omega)
    refine ⟨.bindCallElse f args' he hp hr err' rest', ?_, ?_⟩
    · simp only [groesseEnd]
      have hr' := hr'm (groesseEnd rest' + 0) (by omega)
      have herr := herrm (groesseEnd err' + (0 + (groesseEnd rest' + 0))) (by omega)
      blk (eBindCallElse O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.fn_mem f)) <|
        mem_mitSome he <| Sz.mem_wenn hp <| Sz.mem_wenn hr <|
        Sz.mem_bindR hargs herr <|
        Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <| Sz.mem_pure _) (by omega)
    · glfertig
  | bindAxiom a args he hw hg hd hgd rest =>
    simp only [groesseEnd] at hu hE hS hO
    obtain ⟨rest', hrm, ⟨_, _, _, _, _, _⟩⟩ := hO.en _ _ _ rest (by omega)
    obtain ⟨args', hargs, ⟨_, _⟩⟩ := argsS_rep hE _ args (by omega)
    refine ⟨.bindAxiom a args' he hw hg hd hgd rest', ?_, ?_⟩
    · simp only [groesseEnd]
      have hr := hrm (groesseEnd rest' + 0) (by omega)
      blk (eBindAxiom O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.ax_mem a)) <|
        mem_mitSome he <| Sz.mem_wenn hw <| Sz.mem_wenn hg <| Sz.mem_wenn hd <| Sz.mem_wenn hgd <|
        Sz.mem_bindR hargs hr <| Sz.mem_pure _) (by omega)
    · glfertig
  | bindAxiomElse a args he hr hw hg hd hgd err rest =>
    simp only [groesseEnd] at hu hE hS hO
    obtain ⟨err', herrm, ⟨_, _, _, _, _, _⟩⟩ := hO.en _ _ _ err (by omega)
    obtain ⟨rest', hr'm, ⟨_, _, _, _, _, _⟩⟩ := hO.en _ _ _ rest (by omega)
    obtain ⟨args', hargs, ⟨_, _⟩⟩ := argsS_rep hE _ args (by omega)
    refine ⟨.bindAxiomElse a args' he hr hw hg hd hgd err' rest', ?_, ?_⟩
    · simp only [groesseEnd]
      have hr' := hr'm (groesseEnd rest' + 0) (by omega)
      have herr := herrm (groesseEnd err' + (0 + (groesseEnd rest' + 0))) (by omega)
      blk (eBindAxiomElse O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.ax_mem a)) <|
        mem_mitSome he <| Sz.mem_wenn hr <| Sz.mem_wenn hw <| Sz.mem_wenn hg <| Sz.mem_wenn hd <|
        Sz.mem_wenn hgd <| Sz.mem_bindR hargs herr <|
        Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <| Sz.mem_pure _) (by omega)
    · glfertig

  | regRead r hk rest =>
    simp only [groesseEnd] at hu hE hS hO
    obtain ⟨rest', hr'm, ⟨_, _, _, _, _, _⟩⟩ := hO.en _ _ _ rest (by omega)
    refine ⟨.regRead r hk rest', ?_, ?_⟩
    · simp only [groesseEnd]
      have hr' := hr'm (groesseEnd rest' + 0) (by omega)
      blk (eRegRead O), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.reg_mem r)) <|
        Sz.mem_wenn hk <| Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <| Sz.mem_pure _) (by omega)
    · glfertig
  | regReadElse r hk z sonst rest =>
    simp only [groesseEnd] at hu hE hS hO
    obtain ⟨z', hzm, ⟨_, _⟩⟩ := hO.ex _ _ _ z (by omega)
    obtain ⟨sonst', hsom, ⟨_, _, _, _, _, _⟩⟩ := hO.en _ _ _ sonst (by omega)
    obtain ⟨rest', hr'm, ⟨_, _, _, _, _, _⟩⟩ := hO.en _ _ _ rest (by omega)
    refine ⟨.regReadElse r hk z' sonst' rest', ?_, ?_⟩
    · simp only [groesseEnd]
      have hr' := hr'm (groesseEnd rest' + 0) (by omega)
      have hso := hsom (groesseEnd sonst' + (0 + (groesseEnd rest' + 0))) (by omega)
      have hz := hzm (groesseExpr z' + (0 + (groesseEnd sonst' + (0 + (groesseEnd rest' + 0))))) (by omega)
      blk (eRegReadElse O), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.reg_mem r)) <|
        Sz.mem_wenn hk <| Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) (mem_tyS hz) <|
        Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hso <|
        Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <| Sz.mem_pure _) (by omega)
    · glfertig
  | awaits g payload hp hL hat rest =>
    simp only [groesseEnd] at hu hE hS hO
    obtain ⟨rest', hr'm, ⟨_, _, _, _, _, _⟩⟩ := hO.en _ _ _ rest (by omega)
    refine ⟨.awaits g payload hp hL hat rest', ?_, ?_⟩
    · simp only [groesseEnd]
      have hr' := hr'm (groesseEnd rest' + 0) (by omega)
      subst hp
      blk (eAwaits O), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.glob_mem g)) <|
        Sz.mem_wenn hL <| Sz.mem_wenn hat <| Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <| Sz.mem_pure _) (by omega)
    · glfertig
  | bindCallInd p args he hp hr rest =>
    simp only [groesseEnd] at hu hE hS hO
    obtain ⟨p', hpp, ⟨_, _⟩⟩ := hE _ p (by omega)
    obtain ⟨rest', hr'm, ⟨_, _, _, _, _, _⟩⟩ := hO.en _ _ _ rest (by omega)
    obtain ⟨args', hargs, ⟨_, _⟩⟩ := argsS_rep hE _ args (by omega)
    refine ⟨.bindCallInd p' args' he hp hr rest', ?_, ?_⟩
    · simp only [groesseEnd]
      have hr' := hr'm (groesseEnd rest' + 0) (by omega)
      blk (eBindCallInd O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (mem_fnptrS hpp) <|
        mem_mitSome he <| Sz.mem_wenn hp <| Sz.mem_wenn hr <|
        Sz.mem_bindR hargs hr' <| Sz.mem_pure _) (by omega)
    · glfertig

end Gabbro.Grammatik.Gen
