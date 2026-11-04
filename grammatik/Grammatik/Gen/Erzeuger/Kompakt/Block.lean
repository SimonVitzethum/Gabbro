/-
  File:      Grammatik/Gen/Erzeuger/Kompakt/Block.lean
  Subject:   REPRESENTATIVES of the blocks: the same constructor over the parts' representatives,
             preserving the full summary and the size bound. End-block representatives are publicly imported.
-/
module
public import Grammatik.Gen.Erzeuger.Kompakt.End
@[expose] public section


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
    blk bNil, Sz.mem_blatt (by simp only [List.mem_cons, List.not_mem_nil, or_false])
  | cons s rest =>
    simp only [groesseBlock] at hu hE hS hB hN hO
    obtain ⟨s', hs, gs⟩ := hS _ s (by omega)
    obtain ⟨rest', hrm, gr⟩ := hO.bl _ _ _ _ rest (by omega)
    refine ⟨.cons s' rest', ?_, ?_⟩
    · simp only [groesseBlock]
      have hr := hrm (groesseBlock rest' + 0) (by omega)
      blk (bCons O Ss), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bindS hs hr <| Sz.mem_pure _) (by omega)
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro A; simp only [mB, gs.m A, gr.m A]
      · intro K Rg; simp only [Block.gOk, gs.g K Rg, gr.g K Rg]
      · intro x; simp only [Block.ants, List.mem_append, gs.ant x, gr.ant x]
      · intro x; simp only [Block.regs, List.mem_append, gs.r x, gr.r x]
      · intro x; simp only [koerperB, List.mem_append, gs.o x, gr.o x]
      · simpa only [groesseBlock] using
          Nat.add_le_add (Nat.add_le_add_left gs.groesse 1) gr.groesse
  | @bind _ _ τ _ _ e rest =>
    simp only [groesseBlock] at hu hE hS hB hN hO
    obtain ⟨e', hem, ge⟩ := hE _ e (by omega)
    obtain ⟨rest', hrm, gr⟩ := hO.bl _ _ _ _ rest (by omega)
    refine ⟨.bind e' rest', ?_, ?_⟩
    · simp only [groesseBlock]
      have hr := hrm (groesseBlock rest' + 0) (by omega)
      have hok := bindOk_of (τ := τ) (by omega)
      have h0 := kostT_null hok
      have he : (⟨τ, e'⟩ : SE D Γ Λ) ∈ (E (groesseExpr e')).filter (fun p => Zahlen.bindOk p.1) :=
        List.mem_filter.2 ⟨hem, hok⟩
      blk (bBind O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bindS he hr <| Sz.mem_pure _) (by omega)
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro A; simp only [mB, gr.m A]
      · intro K Rg; simp only [Block.gOk, gr.g K Rg]
      · intro x; simp only [Block.ants, gr.ant x]
      · intro x; simp only [Block.regs, gr.r x]
      · intro x; simp only [koerperB, List.mem_append, ge.orte x, gr.o x]
      · simpa only [groesseBlock] using
          Nat.add_le_add (Nat.add_le_add_left ge.groesse (1 + Zahlen.kostT τ)) gr.groesse
  | bindCall f args he hp hr rest =>
    simp only [groesseBlock] at hu hE hS hB hN hO
    obtain ⟨rest', hr'm, gr⟩ := hO.bl _ _ _ _ rest (by omega)
    obtain ⟨args', hargs, gargs⟩ := argsS_rep hE _ args (by omega)
    refine ⟨.bindCall f args' he hp hr rest', ?_, ?_⟩
    · simp only [groesseBlock]
      have hr' := hr'm (groesseBlock rest' + 0) (by omega)
      blk (bBindCall O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.fn_mem f)) <|
        mem_mitSome he <| Sz.mem_wenn hp <| Sz.mem_wenn hr <|
        Sz.mem_bindR hargs hr' <| Sz.mem_pure _) (by omega)
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro A; simp only [mB, gr.m A]
      · intro K Rg; simp only [Block.gOk, gr.g K Rg]
      · intro x; simp only [Block.ants, gr.ant x]
      · intro x; simp only [Block.regs, gr.r x]
      · intro x; simp only [koerperB, List.mem_append, gargs.orte x, gr.o x]
      · simpa only [groesseBlock] using
          Nat.add_le_add (Nat.add_le_add_left gargs.groesse 1) gr.groesse
  | bindCallInd p args he hp hr rest =>
    simp only [groesseBlock] at hu hE hS hB hN hO
    obtain ⟨p', hpp, gp⟩ := hE _ p (by omega)
    obtain ⟨rest', hr'm, gr⟩ := hO.bl _ _ _ _ rest (by omega)
    obtain ⟨args', hargs, gargs⟩ := argsS_rep hE _ args (by omega)
    refine ⟨.bindCallInd p' args' he hp hr rest', ?_, ?_⟩
    · simp only [groesseBlock]
      have hr' := hr'm (groesseBlock rest' + 0) (by omega)
      blk (bBindCallInd O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (mem_fnptrS hpp) <|
        mem_mitSome he <| Sz.mem_wenn hp <| Sz.mem_wenn hr <|
        Sz.mem_bindR hargs hr' <| Sz.mem_pure _) (by omega)
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro A; simp only [mB, gr.m A]
      · intro K Rg; simp only [Block.gOk, gr.g K Rg]
      · intro x; simp only [Block.ants, gr.ant x]
      · intro x; simp only [Block.regs, gr.r x]
      · intro x; simp only [koerperB, List.mem_append, gp.orte x, gargs.orte x, gr.o x]
      · simpa only [groesseBlock] using
          Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left gp.groesse 1) gargs.groesse) gr.groesse
  | bindCallIndElse p args he hp hr err rest =>
    simp only [groesseBlock] at hu hE hS hB hN hO
    obtain ⟨p', hpp, gp⟩ := hE _ p (by omega)
    obtain ⟨err', herrm, gerr⟩ := hO.en _ _ _ err (by omega)
    obtain ⟨rest', hr'm, gr⟩ := hO.bl _ _ _ _ rest (by omega)
    obtain ⟨args', hargs, gargs⟩ := argsS_rep hE _ args (by omega)
    refine ⟨.bindCallIndElse p' args' he hp hr err' rest', ?_, ?_⟩
    · simp only [groesseBlock]
      have hr' := hr'm (groesseBlock rest' + 0) (by omega)
      have herr := herrm (groesseEnd err' + (0 + (groesseBlock rest' + 0))) (by omega)
      blk (bBindCallIndElse O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (mem_fnptrS hpp) <|
        mem_mitSome he <| Sz.mem_wenn hp <| Sz.mem_wenn hr <|
        Sz.mem_bindR hargs herr <|
        Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <| Sz.mem_pure _) (by omega)
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro A; simp only [mB, gerr.m A, gr.m A]
      · intro K Rg; simp only [Block.gOk, gerr.g K Rg, gr.g K Rg]
      · intro x; simp only [Block.ants, List.mem_append, gerr.ant x, gr.ant x]
      · intro x; simp only [Block.regs, List.mem_append, gerr.r x, gr.r x]
      · intro x; simp only [koerperB, List.mem_append, gp.orte x, gargs.orte x, gerr.o x, gr.o x]
      · simpa only [groesseBlock] using
          Nat.add_le_add
            (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left gp.groesse 1) gargs.groesse) gerr.groesse)
            gr.groesse
  | bindCallElse f args he hp hr err rest =>
    simp only [groesseBlock] at hu hE hS hB hN hO
    obtain ⟨err', herrm, gerr⟩ := hO.en _ _ _ err (by omega)
    obtain ⟨rest', hr'm, gr⟩ := hO.bl _ _ _ _ rest (by omega)
    obtain ⟨args', hargs, gargs⟩ := argsS_rep hE _ args (by omega)
    refine ⟨.bindCallElse f args' he hp hr err' rest', ?_, ?_⟩
    · simp only [groesseBlock]
      have hr' := hr'm (groesseBlock rest' + 0) (by omega)
      have herr := herrm (groesseEnd err' + (0 + (groesseBlock rest' + 0))) (by omega)
      blk (bBindCallElse O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.fn_mem f)) <|
        mem_mitSome he <| Sz.mem_wenn hp <| Sz.mem_wenn hr <|
        Sz.mem_bindR hargs herr <|
        Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <| Sz.mem_pure _) (by omega)
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro A; simp only [mB, gerr.m A, gr.m A]
      · intro K Rg; simp only [Block.gOk, gerr.g K Rg, gr.g K Rg]
      · intro x; simp only [Block.ants, List.mem_append, gerr.ant x, gr.ant x]
      · intro x; simp only [Block.regs, List.mem_append, gerr.r x, gr.r x]
      · intro x; simp only [koerperB, List.mem_append, gargs.orte x, gerr.o x, gr.o x]
      · simpa only [groesseBlock] using
          Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left gargs.groesse 1) gerr.groesse) gr.groesse
  | bindAxiom a args he hw hg hd hgd rest =>
    simp only [groesseBlock] at hu hE hS hB hN hO
    obtain ⟨rest', hr'm, gr⟩ := hO.bl _ _ _ _ rest (by omega)
    obtain ⟨args', hargs, gargs⟩ := argsS_rep hE _ args (by omega)
    refine ⟨.bindAxiom a args' he hw hg hd hgd rest', ?_, ?_⟩
    · simp only [groesseBlock]
      have hr' := hr'm (groesseBlock rest' + 0) (by omega)
      blk (bBindAxiom O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.ax_mem a)) <|
        mem_mitSome he <| Sz.mem_wenn hw <| Sz.mem_wenn hg <| Sz.mem_wenn hd <| Sz.mem_wenn hgd <|
        Sz.mem_bindR hargs hr' <| Sz.mem_pure _) (by omega)
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro A; simp only [mB, gr.m A]
      · intro K Rg; simp only [Block.gOk, gr.g K Rg]
      · intro x; simp only [Block.ants, List.mem_cons, gr.ant x]
      · intro x; simp only [Block.regs, gr.r x]
      · intro x; simp only [koerperB, List.mem_append, gargs.orte x, gr.o x]
      · simpa only [groesseBlock] using
          Nat.add_le_add (Nat.add_le_add_left gargs.groesse 1) gr.groesse
  | bindAxiomOpt => simp only [groesseBlock] at hu; omega
  | bindAxiomOptElse => simp only [groesseBlock] at hu; omega
  | bindAxiomElse a args he hr hw hg hd hgd err rest =>
    simp only [groesseBlock] at hu hE hS hB hN hO
    obtain ⟨err', herrm, gerr⟩ := hO.en _ _ _ err (by omega)
    obtain ⟨rest', hr'm, gr⟩ := hO.bl _ _ _ _ rest (by omega)
    obtain ⟨args', hargs, gargs⟩ := argsS_rep hE _ args (by omega)
    refine ⟨.bindAxiomElse a args' he hr hw hg hd hgd err' rest', ?_, ?_⟩
    · simp only [groesseBlock]
      have hr' := hr'm (groesseBlock rest' + 0) (by omega)
      have herr := herrm (groesseEnd err' + (0 + (groesseBlock rest' + 0))) (by omega)
      blk (bBindAxiomElse O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.ax_mem a)) <|
        mem_mitSome he <| Sz.mem_wenn hr <| Sz.mem_wenn hw <| Sz.mem_wenn hg <| Sz.mem_wenn hd <|
        Sz.mem_wenn hgd <| Sz.mem_bindR hargs herr <|
        Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <| Sz.mem_pure _) (by omega)
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro A; simp only [mB, gerr.m A, gr.m A]
      · intro K Rg; simp only [Block.gOk, gerr.g K Rg, gr.g K Rg]
      · intro x; simp only [Block.ants, List.mem_cons, List.mem_append, gerr.ant x, gr.ant x]
      · intro x; simp only [Block.regs, List.mem_append, gerr.r x, gr.r x]
      · intro x; simp only [koerperB, List.mem_append, gargs.orte x, gerr.o x, gr.o x]
      · simpa only [groesseBlock] using
          Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left gargs.groesse 1) gerr.groesse) gr.groesse
  | regRead r hk rest =>
    simp only [groesseBlock] at hu hE hS hB hN hO
    obtain ⟨rest', hr'm, gr⟩ := hO.bl _ _ _ _ rest (by omega)
    refine ⟨.regRead r hk rest', ?_, ?_⟩
    · simp only [groesseBlock]
      have hr' := hr'm (groesseBlock rest' + 0) (by omega)
      blk (bRegRead O), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.reg_mem r)) <|
        Sz.mem_wenn hk <| Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <| Sz.mem_pure _) (by omega)
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro A; simp only [mB, gr.m A]
      · intro K Rg; simp only [Block.gOk, gr.g K Rg]
      · intro x; simp only [Block.ants, List.mem_cons, gr.ant x]
      · intro x; simp only [Block.regs, List.mem_cons, gr.r x]
      · intro x; simp only [koerperB, gr.o x]
      · simpa only [groesseBlock] using
          Nat.add_le_add_left gr.groesse 1
  | regReadElse r hk z sonst rest =>
    simp only [groesseBlock] at hu hE hS hB hN hO
    obtain ⟨z', hzm, gz⟩ := hO.ex _ _ _ z (by omega)
    obtain ⟨sonst', hso, gso⟩ := hN sonst (by omega)
    obtain ⟨rest', hr'm, gr⟩ := hO.bl _ _ _ _ rest (by omega)
    refine ⟨.regReadElse r hk z' sonst' rest', ?_, ?_⟩
    · simp only [groesseBlock]
      have hr' := hr'm (groesseBlock rest' + 0) (by omega)
      have hz := hzm (groesseExpr z' + (groesseEnd sonst' + (0 + (groesseBlock rest' + 0)))) (by omega)
      blk (bRegReadElse O Ns), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.reg_mem r)) <|
        Sz.mem_wenn hk <| Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) (mem_tyS hz) <|
        Sz.mem_bind hso <| Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <| Sz.mem_pure _) (by omega)
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro A; simp only [mB, gso.m A, gr.m A]
      · intro K Rg; simp only [Block.gOk, gso.g K Rg, gr.g K Rg]
      · intro x; simp only [Block.ants, List.mem_cons, List.mem_append, gso.ant x, gr.ant x]
      · intro x; simp only [Block.regs, List.mem_cons, List.mem_append, gso.r x, gr.r x]
      · intro x; simp only [koerperB, List.mem_append, gz.orte x, gso.o x, gr.o x]
      · simpa only [groesseBlock] using
          Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left gz.groesse 1) gso.groesse) gr.groesse
  | awaits g payload hp hL hat rest =>
    simp only [groesseBlock] at hu hE hS hB hN hO
    obtain ⟨rest', hr'm, gr⟩ := hO.bl _ _ _ _ rest (by omega)
    refine ⟨.awaits g payload hp hL hat rest', ?_, ?_⟩
    · simp only [groesseBlock]
      have hr' := hr'm (groesseBlock rest' + 0) (by omega)
      subst hp
      blk (bAwaits O), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.glob_mem g)) <|
        Sz.mem_wenn hL <| Sz.mem_wenn hat <| Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <| Sz.mem_pure _) (by omega)
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro A; simp only [mB, gr.m A]
      · intro K Rg; simp only [Block.gOk, gr.g K Rg]
      · intro x; simp only [Block.ants, gr.ant x]
      · intro x; simp only [Block.regs, gr.r x]
      · intro x; simp only [koerperB, List.mem_cons, gr.o x]
      · simpa only [groesseBlock] using
          Nat.add_le_add_left gr.groesse 1
  | exchange g neu hw hL rest =>
    simp only [groesseBlock] at hu hE hS hB hN hO
    obtain ⟨neu', hnem, gne⟩ := hO.ex _ _ _ neu (by omega)
    obtain ⟨rest', hr'm, gr⟩ := hO.bl _ _ _ _ rest (by omega)
    refine ⟨.exchange g neu' hw hL rest', ?_, ?_⟩
    · simp only [groesseBlock]
      have hr' := hr'm (groesseBlock rest' + 0) (by omega)
      have hne := hnem (groesseExpr neu' + (0 + (groesseBlock rest' + 0))) (by omega)
      blk (bExchange O), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.glob_mem g)) <|
        Sz.mem_wenn hw <| Sz.mem_wenn hL <| Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) (mem_tyS hne) <|
        Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <| Sz.mem_pure _) (by omega)
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro A; simp only [mB, gr.m A]
      · intro K Rg; simp only [Block.gOk, gr.g K Rg]
      · intro x; simp only [Block.ants, gr.ant x]
      · intro x; simp only [Block.regs, gr.r x]
      · intro x; simp only [koerperB, List.mem_cons, List.mem_append, gne.orte x, gr.o x]
      · simpa only [groesseBlock] using
          Nat.add_le_add (Nat.add_le_add_left gne.groesse 1) gr.groesse
  | narrow e lo' hi' sonst rest =>
    simp only [groesseBlock] at hu hE hS hB hN hO
    obtain ⟨e', he, ge⟩ := hE _ e (by omega)
    obtain ⟨sonst', hso, gso⟩ := hN sonst (by omega)
    obtain ⟨rest', hr'm, gr⟩ := hO.bl _ _ _ _ rest (by omega)
    refine ⟨.narrow e' lo' hi' sonst' rest', ?_, ?_⟩
    · simp only [groesseBlock]
      have hr' := hr'm (groesseBlock rest' + 0) (by omega)
      have hok := bindOk_of (τ := Ty.int lo' hi') (by omega)
      have h0 := kostT_null hok
      blk (bNarrow O E Ns), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (mem_intS he) <|
        Sz.mem_bind (mem_zS (n := lo') rfl (by omega)) <| Sz.mem_bind (mem_zS (n := hi') rfl (by omega)) <|
        Sz.mem_wenn hok <| Sz.mem_bind hso <| Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <| Sz.mem_pure _) (by omega)
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro A; simp only [mB, gso.m A, gr.m A]
      · intro K Rg; simp only [Block.gOk, gso.g K Rg, gr.g K Rg]
      · intro x; simp only [Block.ants, List.mem_append, gso.ant x, gr.ant x]
      · intro x; simp only [Block.regs, List.mem_append, gso.r x, gr.r x]
      · intro x; simp only [koerperB, List.mem_append, ge.orte x, gso.o x, gr.o x]
      · simpa only [groesseBlock] using
          Nat.add_le_add
            (Nat.add_le_add
              (Nat.add_le_add_right
                (Nat.add_le_add_right
                  (Nat.add_le_add_right (Nat.add_le_add_left ge.groesse 1) (Zahlen.kost lo'))
                  (Zahlen.kost hi')) (Zahlen.kostT (.int lo' hi'))) gso.groesse) gr.groesse
  | narrowRequired _ _ _ _ => simp only [groesseBlock] at hu; omega
  | check c sonst rest =>
    simp only [groesseBlock] at hu hE hS hB hN hO
    obtain ⟨c', hc, gc⟩ := hE _ c (by omega)
    obtain ⟨sonst', hso, gso⟩ := hN sonst (by omega)
    obtain ⟨rest', hre, gr⟩ := hB _ rest (by omega)
    refine ⟨.check c' sonst' rest', ?_, ?_⟩
    · simp only [groesseBlock]
      blk (bCheck E Bs Ns), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (mem_tyS hc) <| Sz.mem_bind hso <|
        Sz.mem_bind hre <| Sz.mem_pure _) (by omega)
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro A; simp only [mB, gso.m A, gr.m A]
      · intro K Rg; simp only [Block.gOk, gso.g K Rg, gr.g K Rg]
      · intro x; simp only [Block.ants, List.mem_append, gso.ant x, gr.ant x]
      · intro x; simp only [Block.regs, List.mem_append, gso.r x, gr.r x]
      · intro x; simp only [koerperB, List.mem_append, gc.orte x, gso.o x, gr.o x]
      · simpa only [groesseBlock] using
          Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left gc.groesse 1) gso.groesse) gr.groesse
  | float op a b lo hi rest =>
    simp only [groesseBlock, groessePaar] at hu hE hS hB hN hO
    obtain ⟨a', ha, ga⟩ := hE _ a (by omega)
    obtain ⟨b', hb, gb⟩ := hE _ b (by omega)
    obtain ⟨rest', hr'm, gr⟩ := hO.bl _ _ _ _ rest (by omega)
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
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro A; simp only [mB, gr.m A]
      · intro K Rg; simp only [Block.gOk, gr.g K Rg]
      · intro x; simp only [Block.ants, gr.ant x]
      · intro x; simp only [Block.regs, gr.r x]
      · intro x; simp only [koerperB, List.mem_append, ga.orte x, gb.orte x, gr.o x]
      · simpa only [groesseBlock] using
          Nat.add_le_add
            (Nat.add_le_add_right
              (Nat.add_le_add_right
                (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_left ga.groesse 1) gb.groesse)
                  (groessePaar lo)) (groessePaar hi)) (Zahlen.kostT (.fl lo hi))) gr.groesse
  | floatLit q lo hi rest =>
    simp only [groesseBlock, groessePaar] at hu hE hS hB hN hO
    obtain ⟨rest', hr'm, gr⟩ := hO.bl _ _ _ _ rest (by omega)
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
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro A; simp only [mB, gr.m A]
      · intro K Rg; simp only [Block.gOk, gr.g K Rg]
      · intro x; simp only [Block.ants, gr.ant x]
      · intro x; simp only [Block.regs, gr.r x]
      · intro x; simp only [koerperB, gr.o x]
      · simpa only [groesseBlock] using
          Nat.add_le_add_left gr.groesse
            (1 + groessePaar q + groessePaar lo + groessePaar hi + Zahlen.kostT (.fl lo hi))
  | floatOf e lo hi rest =>
    simp only [groesseBlock, groessePaar] at hu hE hS hB hN hO
    obtain ⟨e', he, ge⟩ := hE _ e (by omega)
    obtain ⟨rest', hr'm, gr⟩ := hO.bl _ _ _ _ rest (by omega)
    refine ⟨.floatOf e' lo hi rest', ?_, ?_⟩
    · simp only [groesseBlock, groessePaar]
      have hr' := hr'm (groesseBlock rest' + 0) (by omega)
      have hlo : lo ∈ paarS (Zahlen.kostP lo) := mem_paarS rfl (by omega)
      have hhi : hi ∈ paarS (Zahlen.kostP hi) := mem_paarS rfl (by omega)
      have hok := bindOk_of (τ := Ty.fl lo hi) (by omega)
      have h0 := kostT_null hok
      blk (bFloatOf O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (mem_intS he) <| Sz.mem_bind hlo <|
        Sz.mem_bind hhi <| Sz.mem_wenn hok <| Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <| Sz.mem_pure _) (by omega)
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro A; simp only [mB, gr.m A]
      · intro K Rg; simp only [Block.gOk, gr.g K Rg]
      · intro x; simp only [Block.ants, gr.ant x]
      · intro x; simp only [Block.regs, gr.r x]
      · intro x; simp only [koerperB, List.mem_append, ge.orte x, gr.o x]
      · simpa only [groesseBlock] using
          Nat.add_le_add
            (Nat.add_le_add_right
              (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_left ge.groesse 1)
                (groessePaar lo)) (groessePaar hi)) (Zahlen.kostT (.fl lo hi))) gr.groesse
  | floatNarrow e lo hi sonst rest =>
    simp only [groesseBlock, groessePaar] at hu hE hS hB hN hO
    obtain ⟨e', he, ge⟩ := hE _ e (by omega)
    obtain ⟨sonst', hso, gso⟩ := hN sonst (by omega)
    obtain ⟨rest', hr'm, gr⟩ := hO.bl _ _ _ _ rest (by omega)
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
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro A; simp only [mB, gso.m A, gr.m A]
      · intro K Rg; simp only [Block.gOk, gso.g K Rg, gr.g K Rg]
      · intro x; simp only [Block.ants, List.mem_append, gso.ant x, gr.ant x]
      · intro x; simp only [Block.regs, List.mem_append, gso.r x, gr.r x]
      · intro x; simp only [koerperB, List.mem_append, ge.orte x, gso.o x, gr.o x]
      · simpa only [groesseBlock] using
          Nat.add_le_add
            (Nat.add_le_add
              (Nat.add_le_add_right
                (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_left ge.groesse 1)
                  (groessePaar lo)) (groessePaar hi)) (Zahlen.kostT (.fl lo hi))) gso.groesse) gr.groesse

end Gabbro.Grammatik.Gen
