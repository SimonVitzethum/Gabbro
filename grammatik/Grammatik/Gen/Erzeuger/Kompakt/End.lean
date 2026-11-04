/-
  File:      Grammatik/Gen/Erzeuger/Kompakt/End.lean
  Subject:   REPRESENTATIVES of the end blocks: the same constructor over the parts' representatives,
             preserving the full summary and the size bound.
-/
module
public import Grammatik.Gen.Erzeuger.Kompakt.Anweisung
public import Grammatik.Gen.Erzeuger.BlockVollst
@[expose] public section


namespace Gabbro.Grammatik.Gen

set_option linter.unusedSectionVars false

open Gabbro.Grammatik

variable {D : Deklaration} [Aufz D] [Zahlen] {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

set_option maxHeartbeats 16000000 in
/-- **Representatives of the end blocks.** -/
theorem endS_rep (O : Orakel V) (E : Sz (SE D Γ Λ)) (Ss : Sz (SS D V l Γ Λ)) (e : Endblock D V l Γ Λ)
    (hu : groesseEnd e < unendlich) (hE : ERU E (groesseEnd e)) (hS : SRU Ss (groesseEnd e))
    (hO : ORU O (groesseEnd e)) : ∃ e' : Endblock D V l Γ Λ, e' ∈ endS O E Ss (groesseEnd e') ∧ GlN e' e := by
  cases e with
  | ret x hΛ =>
    simp only [groesseEnd] at hu hE hS hO
    obtain ⟨x', herg, gx⟩ := ergS_rep hE x (by omega)
    refine ⟨.ret x' hΛ, ?_, ?_⟩
    · simp only [groesseEnd]
      blk (eRet E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (herg) <|
        Sz.mem_wenn hΛ <| Sz.mem_pure _) (by omega)
    · refine ⟨(fun _ => rfl), (fun _ _ => rfl), (fun _ => Iff.rfl), (fun _ => Iff.rfl), ?_, ?_⟩
      · intro c; exact gx.orte c
      · simpa only [groesseEnd] using Nat.add_le_add_left gx.groesse 1
  | retScoped _ _ => simp only [groesseEnd] at hu; omega
  | retWhyScoped _ _ => simp only [groesseEnd] at hu; omega
  | retWhy r hΛ =>
    refine ⟨.retWhy r hΛ, ?_, GlN.refl _⟩
    simp only [groesseEnd]
    blk eRetWhy, Sz.mem_blatt (List.mem_flatMap.2 ⟨r, List.mem_finRange r, by rw [dif_pos hΛ]; simp only [List.mem_cons, List.not_mem_nil, or_false]⟩)
  | leave hl =>
    refine ⟨.leave hl, ?_, GlN.refl _⟩
    simp only [groesseEnd]
    blk eLeave, Sz.mem_blatt (by rw [dif_pos hl]; simp only [List.mem_cons, List.not_mem_nil, or_false])
  | next hl =>
    refine ⟨.next hl, ?_, GlN.refl _⟩
    simp only [groesseEnd]
    blk eNext, Sz.mem_blatt (by rw [dif_pos hl]; simp only [List.mem_cons, List.not_mem_nil, or_false])
  | cons s rest =>
    simp only [groesseEnd] at hu hE hS hO
    obtain ⟨s', hs, gs⟩ := hS _ s (by omega)
    obtain ⟨rest', hrm, gr⟩ := hO.en _ _ _ rest (by omega)
    refine ⟨.cons s' rest', ?_, ?_⟩
    · simp only [groesseEnd]
      have hr := hrm (groesseEnd rest' + 0) (by omega)
      blk (eCons O Ss), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bindS hs hr <| Sz.mem_pure _) (by omega)
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro A; simp only [mE, gs.m A, gr.m A]
      · intro K Rg; simp only [Endblock.gOk, gs.g K Rg, gr.g K Rg]
      · intro x; simp only [Endblock.ants, List.mem_append, gs.ant x, gr.ant x]
      · intro x; simp only [Endblock.regs, List.mem_append, gs.r x, gr.r x]
      · intro x; simp only [koerperE, List.mem_append, gs.o x, gr.o x]
      · simpa only [groesseEnd] using
          Nat.add_le_add (Nat.add_le_add_left gs.groesse 1) gr.groesse
  | @bind _ _ τ _ x rest =>
    simp only [groesseEnd] at hu hE hS hO
    obtain ⟨x', hem, gx⟩ := hE _ x (by omega)
    obtain ⟨rest', hrm, gr⟩ := hO.en _ _ _ rest (by omega)
    refine ⟨.bind x' rest', ?_, ?_⟩
    · simp only [groesseEnd]
      have hr := hrm (groesseEnd rest' + 0) (by omega)
      have hok := bindOk_of (τ := τ) (by omega)
      have h0 := kostT_null hok
      have he : (⟨τ, x'⟩ : SE D Γ Λ) ∈ (E (groesseExpr x')).filter (fun p => Zahlen.bindOk p.1) :=
        List.mem_filter.2 ⟨hem, hok⟩
      blk (eBind O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bindS he hr <| Sz.mem_pure _) (by omega)
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro A; simp only [mE, gr.m A]
      · intro K Rg; simp only [Endblock.gOk, gr.g K Rg]
      · intro x; simp only [Endblock.ants, gr.ant x]
      · intro x; simp only [Endblock.regs, gr.r x]
      · intro x; simp only [koerperE, List.mem_append, gx.orte x, gr.o x]
      · simpa only [groesseEnd] using
          Nat.add_le_add (Nat.add_le_add_left gx.groesse (1 + Zahlen.kostT τ)) gr.groesse
  | bindCall f args he hp hr rest =>
    simp only [groesseEnd] at hu hE hS hO
    obtain ⟨rest', hr'm, gr⟩ := hO.en _ _ _ rest (by omega)
    obtain ⟨args', hargs, gargs⟩ := argsS_rep hE _ args (by omega)
    refine ⟨.bindCall f args' he hp hr rest', ?_, ?_⟩
    · simp only [groesseEnd]
      have hr' := hr'm (groesseEnd rest' + 0) (by omega)
      blk (eBindCall O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.fn_mem f)) <|
        mem_mitSome he <| Sz.mem_wenn hp <| Sz.mem_wenn hr <|
        Sz.mem_bindR hargs hr' <| Sz.mem_pure _) (by omega)
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro A; simp only [mE, gr.m A]
      · intro K Rg; simp only [Endblock.gOk, gr.g K Rg]
      · intro x; simp only [Endblock.ants, gr.ant x]
      · intro x; simp only [Endblock.regs, gr.r x]
      · intro x; simp only [koerperE, List.mem_append, gargs.orte x, gr.o x]
      · simpa only [groesseEnd] using
          Nat.add_le_add (Nat.add_le_add_left gargs.groesse 1) gr.groesse
  | bindCallElse f args he hp hr err rest =>
    simp only [groesseEnd] at hu hE hS hO
    obtain ⟨err', herrm, gerr⟩ := hO.en _ _ _ err (by omega)
    obtain ⟨rest', hr'm, gr⟩ := hO.en _ _ _ rest (by omega)
    obtain ⟨args', hargs, gargs⟩ := argsS_rep hE _ args (by omega)
    refine ⟨.bindCallElse f args' he hp hr err' rest', ?_, ?_⟩
    · simp only [groesseEnd]
      have hr' := hr'm (groesseEnd rest' + 0) (by omega)
      have herr := herrm (groesseEnd err' + (0 + (groesseEnd rest' + 0))) (by omega)
      blk (eBindCallElse O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.fn_mem f)) <|
        mem_mitSome he <| Sz.mem_wenn hp <| Sz.mem_wenn hr <|
        Sz.mem_bindR hargs herr <|
        Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <| Sz.mem_pure _) (by omega)
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro A; simp only [mE, gerr.m A, gr.m A]
      · intro K Rg; simp only [Endblock.gOk, gerr.g K Rg, gr.g K Rg]
      · intro x; simp only [Endblock.ants, List.mem_append, gerr.ant x, gr.ant x]
      · intro x; simp only [Endblock.regs, List.mem_append, gerr.r x, gr.r x]
      · intro x; simp only [koerperE, List.mem_append, gargs.orte x, gerr.o x, gr.o x]
      · simpa only [groesseEnd] using
          Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left gargs.groesse 1) gerr.groesse) gr.groesse
  | bindAxiom a args he hw hg hd hgd rest =>
    simp only [groesseEnd] at hu hE hS hO
    obtain ⟨rest', hrm, gr⟩ := hO.en _ _ _ rest (by omega)
    obtain ⟨args', hargs, gargs⟩ := argsS_rep hE _ args (by omega)
    refine ⟨.bindAxiom a args' he hw hg hd hgd rest', ?_, ?_⟩
    · simp only [groesseEnd]
      have hr := hrm (groesseEnd rest' + 0) (by omega)
      blk (eBindAxiom O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.ax_mem a)) <|
        mem_mitSome he <| Sz.mem_wenn hw <| Sz.mem_wenn hg <| Sz.mem_wenn hd <| Sz.mem_wenn hgd <|
        Sz.mem_bindR hargs hr <| Sz.mem_pure _) (by omega)
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro A; simp only [mE, gr.m A]
      · intro K Rg; simp only [Endblock.gOk, gr.g K Rg]
      · intro x; simp only [Endblock.ants, List.mem_cons, gr.ant x]
      · intro x; simp only [Endblock.regs, gr.r x]
      · intro x; simp only [koerperE, List.mem_append, gargs.orte x, gr.o x]
      · simpa only [groesseEnd] using
          Nat.add_le_add (Nat.add_le_add_left gargs.groesse 1) gr.groesse
  | bindAxiomOpt => simp only [groesseEnd] at hu; omega
  | bindAxiomOptElse => simp only [groesseEnd] at hu; omega
  | bindAxiomElse a args he hr hw hg hd hgd err rest =>
    simp only [groesseEnd] at hu hE hS hO
    obtain ⟨err', herrm, gerr⟩ := hO.en _ _ _ err (by omega)
    obtain ⟨rest', hr'm, gr⟩ := hO.en _ _ _ rest (by omega)
    obtain ⟨args', hargs, gargs⟩ := argsS_rep hE _ args (by omega)
    refine ⟨.bindAxiomElse a args' he hr hw hg hd hgd err' rest', ?_, ?_⟩
    · simp only [groesseEnd]
      have hr' := hr'm (groesseEnd rest' + 0) (by omega)
      have herr := herrm (groesseEnd err' + (0 + (groesseEnd rest' + 0))) (by omega)
      blk (eBindAxiomElse O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.ax_mem a)) <|
        mem_mitSome he <| Sz.mem_wenn hr <| Sz.mem_wenn hw <| Sz.mem_wenn hg <| Sz.mem_wenn hd <|
        Sz.mem_wenn hgd <| Sz.mem_bindR hargs herr <|
        Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <| Sz.mem_pure _) (by omega)
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro A; simp only [mE, gerr.m A, gr.m A]
      · intro K Rg; simp only [Endblock.gOk, gerr.g K Rg, gr.g K Rg]
      · intro x; simp only [Endblock.ants, List.mem_cons, List.mem_append, gerr.ant x, gr.ant x]
      · intro x; simp only [Endblock.regs, List.mem_append, gerr.r x, gr.r x]
      · intro x; simp only [koerperE, List.mem_append, gargs.orte x, gerr.o x, gr.o x]
      · simpa only [groesseEnd] using
          Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left gargs.groesse 1) gerr.groesse) gr.groesse

  | regRead r hk rest =>
    simp only [groesseEnd] at hu hE hS hO
    obtain ⟨rest', hr'm, gr⟩ := hO.en _ _ _ rest (by omega)
    refine ⟨.regRead r hk rest', ?_, ?_⟩
    · simp only [groesseEnd]
      have hr' := hr'm (groesseEnd rest' + 0) (by omega)
      blk (eRegRead O), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.reg_mem r)) <|
        Sz.mem_wenn hk <| Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <| Sz.mem_pure _) (by omega)
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro A; simp only [mE, gr.m A]
      · intro K Rg; simp only [Endblock.gOk, gr.g K Rg]
      · intro x; simp only [Endblock.ants, List.mem_cons, gr.ant x]
      · intro x; simp only [Endblock.regs, List.mem_cons, gr.r x]
      · intro x; simp only [koerperE, gr.o x]
      · simpa only [groesseEnd] using
          Nat.add_le_add_left gr.groesse 1
  | regReadElse r hk z sonst rest =>
    simp only [groesseEnd] at hu hE hS hO
    obtain ⟨z', hzm, gz⟩ := hO.ex _ _ _ z (by omega)
    obtain ⟨sonst', hsom, gso⟩ := hO.en _ _ _ sonst (by omega)
    obtain ⟨rest', hr'm, gr⟩ := hO.en _ _ _ rest (by omega)
    refine ⟨.regReadElse r hk z' sonst' rest', ?_, ?_⟩
    · simp only [groesseEnd]
      have hr' := hr'm (groesseEnd rest' + 0) (by omega)
      have hso := hsom (groesseEnd sonst' + (0 + (groesseEnd rest' + 0))) (by omega)
      have hz := hzm (groesseExpr z' + (0 + (groesseEnd sonst' + (0 + (groesseEnd rest' + 0))))) (by omega)
      blk (eRegReadElse O), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.reg_mem r)) <|
        Sz.mem_wenn hk <| Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) (mem_tyS hz) <|
        Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hso <|
        Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <| Sz.mem_pure _) (by omega)
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro A; simp only [mE, gso.m A, gr.m A]
      · intro K Rg; simp only [Endblock.gOk, gso.g K Rg, gr.g K Rg]
      · intro x; simp only [Endblock.ants, List.mem_cons, List.mem_append, gso.ant x, gr.ant x]
      · intro x; simp only [Endblock.regs, List.mem_cons, List.mem_append, gso.r x, gr.r x]
      · intro x; simp only [koerperE, List.mem_append, gz.orte x, gso.o x, gr.o x]
      · simpa only [groesseEnd] using
          Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left gz.groesse 1) gso.groesse) gr.groesse
  | awaits g payload hp hL hat rest =>
    simp only [groesseEnd] at hu hE hS hO
    obtain ⟨rest', hr'm, gr⟩ := hO.en _ _ _ rest (by omega)
    refine ⟨.awaits g payload hp hL hat rest', ?_, ?_⟩
    · simp only [groesseEnd]
      have hr' := hr'm (groesseEnd rest' + 0) (by omega)
      subst hp
      blk (eAwaits O), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (Aufz.glob_mem g)) <|
        Sz.mem_wenn hL <| Sz.mem_wenn hat <| Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <| Sz.mem_pure _) (by omega)
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro A; simp only [mE, gr.m A]
      · intro K Rg; simp only [Endblock.gOk, gr.g K Rg]
      · intro x; simp only [Endblock.ants, gr.ant x]
      · intro x; simp only [Endblock.regs, gr.r x]
      · intro x; simp only [koerperE, List.mem_cons, gr.o x]
      · simpa only [groesseEnd] using
          Nat.add_le_add_left gr.groesse 1
  | bindCallInd p args he hp hr rest =>
    simp only [groesseEnd] at hu hE hS hO
    obtain ⟨p', hpp, gp⟩ := hE _ p (by omega)
    obtain ⟨rest', hr'm, gr⟩ := hO.en _ _ _ rest (by omega)
    obtain ⟨args', hargs, gargs⟩ := argsS_rep hE _ args (by omega)
    refine ⟨.bindCallInd p' args' he hp hr rest', ?_, ?_⟩
    · simp only [groesseEnd]
      have hr' := hr'm (groesseEnd rest' + 0) (by omega)
      blk (eBindCallInd O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (mem_fnptrS hpp) <|
        mem_mitSome he <| Sz.mem_wenn hp <| Sz.mem_wenn hr <|
        Sz.mem_bindR hargs hr' <| Sz.mem_pure _) (by omega)
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro A; simp only [mE, gr.m A]
      · intro K Rg; simp only [Endblock.gOk, gr.g K Rg]
      · intro x; simp only [Endblock.ants, gr.ant x]
      · intro x; simp only [Endblock.regs, gr.r x]
      · intro x; simp only [koerperE, List.mem_append, gp.orte x, gargs.orte x, gr.o x]
      · simpa only [groesseEnd] using
          Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left gp.groesse 1) gargs.groesse) gr.groesse
  | bindCallIndElse p args he hp hr err rest =>
    simp only [groesseEnd] at hu hE hS hO
    obtain ⟨p', hpp, gp⟩ := hE _ p (by omega)
    obtain ⟨err', herrm, gerr⟩ := hO.en _ _ _ err (by omega)
    obtain ⟨rest', hr'm, gr⟩ := hO.en _ _ _ rest (by omega)
    obtain ⟨args', hargs, gargs⟩ := argsS_rep hE _ args (by omega)
    refine ⟨.bindCallIndElse p' args' he hp hr err' rest', ?_, ?_⟩
    · simp only [groesseEnd]
      have hr' := hr'm (groesseEnd rest' + 0) (by omega)
      have herr := herrm (groesseEnd err' + (0 + (groesseEnd rest' + 0))) (by omega)
      blk (eBindCallIndElse O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (mem_fnptrS hpp) <|
        mem_mitSome he <| Sz.mem_wenn hp <| Sz.mem_wenn hr <|
        Sz.mem_bindR hargs herr <|
        Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <| Sz.mem_pure _) (by omega)
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro A; simp only [mE, gerr.m A, gr.m A]
      · intro K Rg; simp only [Endblock.gOk, gerr.g K Rg, gr.g K Rg]
      · intro x; simp only [Endblock.ants, List.mem_append, gerr.ant x, gr.ant x]
      · intro x; simp only [Endblock.regs, List.mem_append, gerr.r x, gr.r x]
      · intro x; simp only [koerperE, List.mem_append, gp.orte x, gargs.orte x, gerr.o x, gr.o x]
      · simpa only [groesseEnd] using
          Nat.add_le_add
            (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left gp.groesse 1) gargs.groesse) gerr.groesse)
            gr.groesse
  | narrow _ _ _ _ _ => simp only [groesseEnd] at hu; omega
  | narrowRequired _ _ _ _ => simp only [groesseEnd] at hu; omega
  | exchange _ _ _ _ _ => simp only [groesseEnd] at hu; omega
  | ite _ _ _ => simp only [groesseEnd] at hu; omega

  | float op a b lo hi rest =>
    simp only [groesseEnd, groessePaar] at hu hE hS hO
    obtain ⟨a', ha, ga⟩ := hE _ a (by omega)
    obtain ⟨b', hb, gb⟩ := hE _ b (by omega)
    obtain ⟨rest', hr'm, gr⟩ := hO.en _ _ _ rest (by omega)
    refine ⟨.float op a' b' lo hi rest', ?_, ?_⟩
    · simp only [groesseEnd, groessePaar]
      have hr' := hr'm (groesseEnd rest' + 0) (by omega)
      have hlo : lo ∈ paarS (Zahlen.kostP lo) := mem_paarS rfl (by omega)
      have hhi : hi ∈ paarS (Zahlen.kostP hi) := mem_paarS rfl (by omega)
      have hok := bindOk_of (τ := Ty.fl lo hi) (by omega)
      have h0 := kostT_null hok
      blk (eFloat O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (Sz.mem_wahl (mem_gleitOps op)) <|
        Sz.mem_bind (mem_flS ha) <| Sz.mem_bind (mem_flS hb) <| Sz.mem_bind hlo <| Sz.mem_bind hhi <|
        Sz.mem_wenn hok <| Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <| Sz.mem_pure _) (by omega)
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro A; simp only [mE, gr.m A]
      · intro K Rg; simp only [Endblock.gOk, gr.g K Rg]
      · intro x; simp only [Endblock.ants, gr.ant x]
      · intro x; simp only [Endblock.regs, gr.r x]
      · intro x; simp only [koerperE, List.mem_append, ga.orte x, gb.orte x, gr.o x]
      · simpa only [groesseEnd] using
          Nat.add_le_add
            (Nat.add_le_add_right
              (Nat.add_le_add_right
                (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_left ga.groesse 1) gb.groesse)
                  (groessePaar lo)) (groessePaar hi)) (Zahlen.kostT (.fl lo hi))) gr.groesse
  | floatLit q lo hi rest =>
    simp only [groesseEnd, groessePaar] at hu hE hS hO
    obtain ⟨rest', hr'm, gr⟩ := hO.en _ _ _ rest (by omega)
    refine ⟨.floatLit q lo hi rest', ?_, ?_⟩
    · simp only [groesseEnd, groessePaar]
      have hr' := hr'm (groesseEnd rest' + 0) (by omega)
      have hq : q ∈ paarS (Zahlen.kostP q) := mem_paarS rfl (by omega)
      have hlo : lo ∈ paarS (Zahlen.kostP lo) := mem_paarS rfl (by omega)
      have hhi : hi ∈ paarS (Zahlen.kostP hi) := mem_paarS rfl (by omega)
      have hok := bindOk_of (τ := Ty.fl lo hi) (by omega)
      have h0 := kostT_null hok
      blk (eFloatLit O), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind hq <| Sz.mem_bind hlo <|
        Sz.mem_bind hhi <| Sz.mem_wenn hok <| Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <| Sz.mem_pure _) (by omega)
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro A; simp only [mE, gr.m A]
      · intro K Rg; simp only [Endblock.gOk, gr.g K Rg]
      · intro x; simp only [Endblock.ants, gr.ant x]
      · intro x; simp only [Endblock.regs, gr.r x]
      · intro x; simp only [koerperE, gr.o x]
      · simpa only [groesseEnd] using
          Nat.add_le_add_left gr.groesse
            (1 + groessePaar q + groessePaar lo + groessePaar hi + Zahlen.kostT (.fl lo hi))
  | floatOf e lo hi rest =>
    simp only [groesseEnd, groessePaar] at hu hE hS hO
    obtain ⟨e', he, ge⟩ := hE _ e (by omega)
    obtain ⟨rest', hr'm, gr⟩ := hO.en _ _ _ rest (by omega)
    refine ⟨.floatOf e' lo hi rest', ?_, ?_⟩
    · simp only [groesseEnd, groessePaar]
      have hr' := hr'm (groesseEnd rest' + 0) (by omega)
      have hlo : lo ∈ paarS (Zahlen.kostP lo) := mem_paarS rfl (by omega)
      have hhi : hi ∈ paarS (Zahlen.kostP hi) := mem_paarS rfl (by omega)
      have hok := bindOk_of (τ := Ty.fl lo hi) (by omega)
      have h0 := kostT_null hok
      blk (eFloatOf O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (mem_intS he) <| Sz.mem_bind hlo <|
        Sz.mem_bind hhi <| Sz.mem_wenn hok <| Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <| Sz.mem_pure _) (by omega)
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro A; simp only [mE, gr.m A]
      · intro K Rg; simp only [Endblock.gOk, gr.g K Rg]
      · intro x; simp only [Endblock.ants, gr.ant x]
      · intro x; simp only [Endblock.regs, gr.r x]
      · intro x; simp only [koerperE, List.mem_append, ge.orte x, gr.o x]
      · simpa only [groesseEnd] using
          Nat.add_le_add
            (Nat.add_le_add_right
              (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_left ge.groesse 1)
                (groessePaar lo)) (groessePaar hi)) (Zahlen.kostT (.fl lo hi))) gr.groesse
  | floatNarrow e lo hi sonst rest =>
    simp only [groesseEnd, groessePaar] at hu hE hS hO
    obtain ⟨e', he, ge⟩ := hE _ e (by omega)
    obtain ⟨sonst', hsom, gso⟩ := hO.en _ _ _ sonst (by omega)
    obtain ⟨rest', hr'm, gr⟩ := hO.en _ _ _ rest (by omega)
    refine ⟨.floatNarrow e' lo hi sonst' rest', ?_, ?_⟩
    · simp only [groesseEnd, groessePaar]
      have hso := hsom (groesseEnd sonst' + (0 + (groesseEnd rest' + 0))) (by omega)
      have hr' := hr'm (groesseEnd rest' + 0) (by omega)
      have hlo : lo ∈ paarS (Zahlen.kostP lo) := mem_paarS rfl (by omega)
      have hhi : hi ∈ paarS (Zahlen.kostP hi) := mem_paarS rfl (by omega)
      have hok := bindOk_of (τ := Ty.fl lo hi) (by omega)
      have h0 := kostT_null hok
      blk (eFloatNarrow O E), Sz.mem_cast (Sz.mem_knoten <| Sz.mem_bind (mem_flS he) <| Sz.mem_bind hlo <|
        Sz.mem_bind hhi <| Sz.mem_wenn hok <| Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hso <| Sz.mem_bindR (A := Sz.pure ()) (Sz.mem_pure ()) hr' <|
        Sz.mem_pure _) (by omega)
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro A; simp only [mE, gso.m A, gr.m A]
      · intro K Rg; simp only [Endblock.gOk, gso.g K Rg, gr.g K Rg]
      · intro x; simp only [Endblock.ants, List.mem_append, gso.ant x, gr.ant x]
      · intro x; simp only [Endblock.regs, List.mem_append, gso.r x, gr.r x]
      · intro x; simp only [koerperE, List.mem_append, ge.orte x, gso.o x, gr.o x]
      · simpa only [groesseEnd] using
          Nat.add_le_add
            (Nat.add_le_add
              (Nat.add_le_add_right
                (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_left ge.groesse 1)
                  (groessePaar lo)) (groessePaar hi)) (Zahlen.kostT (.fl lo hi))) gso.groesse) gr.groesse

end Gabbro.Grammatik.Gen
