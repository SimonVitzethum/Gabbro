module
public import Core.Ast.LowLevel.Exec.Proofs.ExecKern
public import Core.Ast.LowLevel.Exec.Registry
@[expose] public section
namespace Gabbro.Core.Ast.LowLevel
open Gabbro.Core.Text Katalog Maschine Waechter Aussen Annahme
open Gabbro.Core.Sicherheit (Absturz NeueWirkungen)
private theorem jlNoneSomeFalse {α : Type} (x : α) : ¬ ((none : Option α) = some x) := by
  intro h
  cases h
private theorem jlExists2 {α β : Type} {a : α} {b : β} {P : α → β → Prop} :
    (∃ x y, a = x ∧ b = y ∧ P x y) ↔ P a b := by
  constructor
  · rintro ⟨x, y, rfl, rfl, h⟩
    exact h
  · intro h
    exact ⟨a, b, rfl, rfl, h⟩
private theorem jumpLongNotHalted {b : Bool} (h : !b = true) : ¬ b := by
  cases b with
  | false =>
      intro hb
      cases hb
  | true =>
      cases h
private theorem jumpLongPrints (tree : ExecTree .jumpLong) :
    tree.production (tree.printPieces.map PrintedToken.value) := by
  cases tree with
  | jumpLong target dest space stack =>
      cases space <;> cases stack <;>
        simpa [ExecTree.production, ExecTree.printPieces, keyword, word,
          Identifier.print, PrintedToken.unquoted, printPunctuation, printOpen,
          printClose, printSemicolon, openParen, closeParen, semicolon,
          String.reduceToList]
private theorem jumpLongProductionUnique {tokens : List Token} {a b : ExecTree .jumpLong}
    (ha : a.production tokens) (hb : b.production tokens) : a = b := by
  cases a with
  | jumpLong t d sp st =>
      cases b with
      | jumpLong t' d' sp' st' =>
          cases hsp : sp <;> cases hst : st <;> cases hsp' : sp' <;> cases hst' : st'
          all_goals
            simp only [ExecTree.production, hsp, hst, hsp', hst', Option.isNone,
              Option.isNone_none, Option.isNone_some, jlNoneSomeFalse, Option.some.injEq,
              Bool.false_eq_true, false_and, and_false, or_false, false_or, true_and,
              and_true, exists_false, exists_prop, exists_eq_left, exists_eq_right,
              exists_eq_left', exists_eq_right', jlExists2] at ha hb
            rw [ha] at hb
            have hlen := congrArg List.length hb
            simp only [List.length_cons, List.length_nil] at hlen
            first
            | (exfalso; omega)
            | (
              have ht : t = t' := by
                apply Subtype.ext
                have h := congrArg (fun l : List Token => l[2]?) hb
                simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
                  Option.some.injEq, Token.word.injEq] at h
                exact h
              have hd : d = d' := by
                apply Subtype.ext
                have h := congrArg (fun l : List Token => l[6]?) hb
                simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
                  Option.some.injEq, Token.word.injEq] at h
                exact h
              subst t'
              subst d'
              have hspEq : sp = sp' := by
                first
                | simpa only [hsp, hsp']
                | (
                  simpa only [hsp, hsp', Identifier] using congrArg some (Subtype.ext (by
                    have h := congrArg (fun l : List Token => l[9]?) hb
                    simpa only [List.getElem?_cons_zero, List.getElem?_cons_succ,
                      Option.some.injEq, Token.word.injEq] using h))
                  )
              have hstEq : st = st' := by
                first
                | simpa only [hst, hst']
                | (
                  simpa only [hst, hst', Identifier] using congrArg some (Subtype.ext (by
                    have h := congrArg (fun l : List Token => l[8]?) hb
                    simpa only [List.getElem?_cons_zero, List.getElem?_cons_succ,
                      Option.some.injEq, Token.word.injEq] using h))
                  )
                | (
                  simpa only [hst, hst', Identifier] using congrArg some (Subtype.ext (by
                    have h := congrArg (fun l : List Token => l[11]?) hb
                    simpa only [List.getElem?_cons_zero, List.getElem?_cons_succ,
                      Option.some.injEq, Token.word.injEq] using h))
                  )
              have hfirst : ExecTree.jumpLong t d sp st = ExecTree.jumpLong t d sp' st :=
                congrArg (fun x => ExecTree.jumpLong t d x st) hspEq
              have hsecond : ExecTree.jumpLong t d sp' st = ExecTree.jumpLong t d sp' st' :=
                congrArg (fun x => ExecTree.jumpLong t d sp' x) hstEq
              simpa only [hsp, hst, hsp', hst'] using hfirst.trans hsecond
            )
private def jumpLongSyntax : Gabbro.Core.Text.Syntax (ExecTree .jumpLong) where
  reads := fun tokens tree => tree.production tokens
  unique := by
    intro tokens a b ha hb
    exact jumpLongProductionUnique ha hb
  printPieces := ExecTree.printPieces
  reads_print := jumpLongPrints
private theorem jumpLongParse : ExecParseAussage .jumpLong := by
  intro text tree
  change Gabbro.Core.Text.Parse jumpLongSyntax.grammar text tree ↔
    ∃ pieces, Lexed text pieces ∧ tree.production (canonicalTokens pieces)
  exact jumpLongSyntax.parse_iff
private theorem jumpLongInversion : ExecInversionAussage .jumpLong := by
  intro tree tokens prod
  cases tree with
  | jumpLong target dest space stack =>
      obtain ⟨pieces, lexed, aligned⟩ :=
        PrintedToken.renderLexed 0 (ExecTree.printPieces (.jumpLong target dest space stack))
      refine ⟨pieces, ?_, ?_⟩
      · exact lexed
      · have hp := jumpLongPrints (.jumpLong target dest space stack)
        cases space <;> cases stack <;>
          simp only [ExecTree.production, Option.isNone, Option.isNone_none,
            Option.isNone_some, jlNoneSomeFalse, Option.some.injEq, Bool.false_eq_true,
            false_and, and_false, or_false, false_or, true_and, and_true, exists_false,
            exists_prop, exists_eq_left, exists_eq_right, exists_eq_left',
            exists_eq_right', jlExists2] at hp prod
        all_goals exact aligned.trans (hp.trans prod.symm)
private theorem jumpLongEindeutig : ExecEindeutigAussage .jumpLong := by
  intro a b tokens ha hb
  exact jumpLongProductionUnique ha hb
private theorem jumpLongDruck : ExecDruckAussage .jumpLong := by
  intro tree
  refine ⟨jumpLongSyntax.reads_print tree, ?_⟩
  change Gabbro.Core.Text.Parse jumpLongSyntax.grammar (ExecTree.print tree) tree
  simpa only [jumpLongSyntax, Syntax.grammar, Syntax.print, ExecTree.print] using
    jumpLongSyntax.parse_print tree
private theorem jumpLongMeaning : JumpLongMeaningAussage := by
  intro code dest sp st s c frame heval
  simp only [ExecInstruction.evaluate] at heval
  cases hcur : (s.lokal c).current with
  | none =>
      rw [hcur] at heval
      dsimp at heval
      cases heval
  | some cur =>
      rw [hcur] at heval
      dsimp at heval
      cases hdst : (s.lokal c).states[dest]? with
      | none =>
          rw [hdst] at heval
          dsimp at heval
          cases heval
      | some decl =>
          rw [hdst] at heval
          dsimp at heval
          cases htr : decl.translation with
          | off =>
              cases hsp : sp with
              | none =>
                  simp only [spaceOk, htr, hsp, Bool.and_true] at heval
                  split at heval
                  · rename_i hcond
                    cases heval
                    have hcond' := hcond
                    simp only [Bool.and_eq_true] at hcond'
                    refine ⟨cur, decl, rfl, bne_iff_ne.mp hcond'.1.1, rfl,
                      jumpLongNotHalted hcond'.1.2, rfl, rfl, rfl, ?_, ?_⟩
                    · intro hon
                      rw [htr] at hon
                      cases hon
                    · intro _hoff
                      rfl
                  · cases heval
              | some id =>
                  simp only [spaceOk, htr, hsp, Bool.and_false, if_false] at heval
                  cases heval
          | on =>
              cases hsp : sp with
              | none =>
                  simp only [spaceOk, htr, hsp, Bool.and_false, if_false] at heval
                  cases heval
              | some id =>
                  simp only [spaceOk, htr, hsp, Bool.and_true] at heval
                  split at heval
                  · rename_i hcond
                    cases heval
                    have hcond' := hcond
                    simp only [Bool.and_eq_true] at hcond'
                    refine ⟨cur, decl, rfl, bne_iff_ne.mp hcond'.1.1.1, rfl,
                      jumpLongNotHalted hcond'.1.1.2, rfl, rfl, rfl, ?_, ?_⟩
                    · intro _hon
                      exact ⟨id, rfl⟩
                    · intro hoff
                      rw [htr] at hoff
                      cases hoff
                  · cases heval
private theorem jlLowerStart (c : Char) (lo : 'a' ≤ c) (hi : c ≤ 'z') : isNameStart c := by
  unfold isNameStart isLetter
  left
  left
  exact ⟨lo, hi⟩
private def jlIdent (c : Char) (h : isNameStart c) : Identifier :=
  ⟨[c], ⟨c, [], rfl, h, by intro a ha; cases ha⟩⟩
private def jlFirst : Identifier := jlIdent 'a' (jlLowerStart 'a' (by decide) (by decide))
private def jlSecond : Identifier := jlIdent 'b' (jlLowerStart 'b' (by decide) (by decide))
private def jlStack : Identifier := jlIdent 't' (jlLowerStart 't' (by decide) (by decide))
private theorem jlFirst_ne_second_val : jlFirst.val ≠ jlSecond.val := by
  change [('a' : Char)] ≠ [('b' : Char)]
  intro h
  have hc : ('a' : Char) = 'b' := (List.cons.inj h).1
  simpa only [Char.reduceEq] using hc
private theorem jlFirst_beq_second_false : (jlFirst.val == jlSecond.val) = false :=
  beq_eq_false_iff_ne.mpr jlFirst_ne_second_val
private def jlFirstDecl : ExecStateDecl :=
  { widthBits := 64, privilege := .kernel, translation := .on, guards := [] }
private def jlSecondDecl : ExecStateDecl :=
  { widthBits := 64, privilege := .kernel, translation := .off, guards := [] }
private theorem jlFirstWF : jlFirstDecl.wellformed := by
  unfold ExecStateDecl.wellformed jlFirstDecl
  right
  right
  rfl
private theorem jlSecondWF : jlSecondDecl.wellformed := by
  unfold ExecStateDecl.wellformed jlSecondDecl
  right
  right
  rfl
private theorem jlImageGueltig : image.gueltig (Plattform.x86_64).ziel := by
  refine ⟨List.Mem.head _, ?_, ?_⟩
  · intro a byte present
    change (if a = 0 then some 0 else none) = some byte at present
    split at present
    · rename_i atZero
      subst a
      exact Nat.pow_pos (Nat.zero_lt_succ _)
    · cases present
  · intro a mem
    have h : a = 0 := List.mem_singleton.mp mem
    subst a
    exact ⟨0, rfl⟩
private theorem jlZulStart {k : Katalog} {env : Katalog.Umgebung} {regions : List Strecke}
    (hw : Hardware k env) (img : image.gueltig k.plattform.ziel)
    (pairwise : regions.Pairwise Strecke.getrennt)
    (ok : ∀ r ∈ regions, r.von < r.bis ∧ r.bis ≤ 2 ^ k.plattform.ziel.physicalBits ∧
      ∀ e d, k.plattform.geraet e = some d → d.bus = .mmio → r.getrennt d.window) :
    Katalog.ZulStart k env image
      ⟨0, (fun i => if i = 0 then some 0 else none), regions, (fun _ => none),
        env.politik.sicht 0 []⟩ := by
  refine ⟨img, hw.kerne, ?_, ?_, pairwise, ok, ?_, rfl⟩
  · intro i hi
    refine ⟨0, ?_⟩
    change (if i = 0 then some 0 else none) = some 0
    change i < 1 at hi
    have : i = 0 := by omega
    subst i
    rfl
  · intro i c hc
    change (if i = 0 then some 0 else none) = some c at hc
    split at hc
    · rename_i hi
      subst i
      cases hc
      constructor
      · change 0 < 1
        omega
      · simpa using hw.kerne
    · cases hc
  · intro a byte hb
    change (none : Option UInt8) = some byte at hb
    cases hb
private theorem jlKlauseln (code : List ExecInstruction) :
    KlauselnWahr (execProgram Plattform.x86_64.katalog code) := by
  intro ρ runs
  dsimp [kanonischeKlauseln, execProgram, Quelltabellen.leer, Quellklauseln.leer]
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    cases hp
  · intro t p hp
    cases hp
  · intro t done p hp
    cases hp
private theorem jlWaechter (code : List ExecInstruction) :
    WaechterHalten (execProgram Plattform.x86_64.katalog code) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ρ runs t o args bedarf
    dsimp [kanonischeVerwendung, execProgram, Quelltabellen.leer] at bedarf
    cases bedarf
  · intro ρ runs t
    rintro ⟨C, nonempty, blocked⟩
    obtain ⟨c, hc⟩ := nonempty
    obtain ⟨b, hblock, _, _, _⟩ := blocked c hc
    exact hblock
  · intro ρ runs t l h _ hne
    exact (hne rfl).elim
private theorem jlAkzeptiert (code : List ExecInstruction) :
    Annahme.Akzeptiert (execProgram Plattform.x86_64.katalog code) := by
  refine ⟨⟨Plattform.katalog_wohlgeformt .x86_64, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    jlKlauseln code, jlWaechter code⟩
  · intro i
    exact execRegelLokal Plattform.x86_64.katalog i
  · refine ⟨zulassung_m2 _, ?_⟩
    apply aussen_gueltig_aus_kontext
    intro run t s c w spur s' step
    cases step with
    | kontext _ _ regel execute =>
        obtain ⟨_, _, frame, _, planEq, rfl⟩ := regel
        cases (List.cons.inj planEq).1
        obtain ⟨rfl, rfl⟩ := execGenauInternal execute
        exact ⟨⟨fun _ mem => (List.not_mem_nil mem).elim, [],
          (List.append_nil _).symm, fun _ mem => (List.not_mem_nil mem).elim⟩, fun h => h⟩
  · exact execProgramFlussLokal Plattform.x86_64.katalog code
  · exact schrankenLokal_leer rfl rfl rfl
  · exact Gabbro.Core.Annahme.abschnittWartefrei_ohne_blockade _ fun _ _ _ hb => hb
  · exact execDomaenenLokal _ _
private theorem jumpLongJoint : JumpLongJointAussage := by
  let k : Katalog := Plattform.x86_64.katalog
  let extent : Strecke := ⟨0, 4096⟩
  let scope : ExecScope :=
    { states := [jlFirst, jlSecond], spaces := [], stapel := [jlStack],
      code := [(jlFirst, jlFirst)], entries := [] }
  let code : Nat := 0
  let dest : Nat := 1
  let sp : Option Nat := none
  let st : Option Nat := some 0
  let op : ExecInstruction := .jumpLong code dest sp st
  let tree : ExecTree .jumpLong := .jumpLong jlFirst jlSecond none (some jlStack)
  let pre : List ExecInstruction := [.declareState jlFirstDecl, .declareState jlSecondDecl]
  let sicht : Nat → AussenVerlauf → AussenSicht := fun _ _ => AussenSicht.leer
  let env : Katalog.Umgebung := Katalog.Umgebung.referenz k 1 sicht
  let start : AussenStart :=
    ⟨0, (fun i => if i = 0 then some 0 else none), [extent], (fun _ => none),
      env.politik.sicht 0 []⟩
  let text : RawText := tree.print
  let E : ExecUnit := execProgram k (pre ++ [op])
  let s0 := (I.start E start).2
  let frame1 : ExecFrame := (s0.lokal entryContext).declare jlFirstDecl
  let s1 := frame1.advance entryContext s0
  let frame2 : ExecFrame := (s1.lokal entryContext).declare jlSecondDecl
  let s2 := frame2.advance entryContext s1
  let next : ExecFrame := { (s2.lokal entryContext) with
    result := some (.jumpedLong code dest), current := some dest, activeSpace := sp }
  have hardware : Hardware k env := by
    apply Katalog.Umgebung.referenz_hardware k 1 sicht
    · simpa [k] using Plattform.katalog_wohlgeformt .x86_64
    · omega
  have hzul : E.ZulStart env start := by
    change Katalog.ZulStart k env image
      ⟨0, (fun i => if i = 0 then some 0 else none), [extent], (fun _ => none),
        env.politik.sicht 0 []⟩
    apply jlZulStart (k := k) (env := env) (regions := [extent]) hardware
    · simpa [k, Plattform.katalog] using jlImageGueltig
    · exact List.Pairwise.cons (by intro a ha; cases ha) List.Pairwise.nil
    · intro r hr
      have rext : r = extent := List.mem_singleton.mp hr
      subst r
      refine ⟨by change 0 < 4096; omega, by change 4096 ≤ 2 ^ (52 : Nat); omega, ?_⟩
      intro endpoint device selected mmio
      cases endpoint <;> cases selected
      · cases mmio
      · exact Or.inl (by change 4096 ≤ 0x10000000; omega)
  have accepted : Annahme.Akzeptiert E := by
    change Annahme.Akzeptiert (execProgram k (pre ++ [op]))
    simpa [k] using jlAkzeptiert (pre ++ [op])
  have hnode : (scope.states.map Subtype.val).Nodup := by
    change [jlFirst.val, jlSecond.val].Nodup
    exact List.nodup_cons.mpr ⟨by
      intro hmem
      exact jlFirst_ne_second_val (List.mem_singleton.mp hmem), List.nodup_singleton _⟩
  have hnosp : (scope.spaces.map Subtype.val).Nodup := by
    change ([] : List (List Char)).Nodup
    exact List.nodup_nil
  have hnost : (scope.stapel.map Subtype.val).Nodup := by
    change [jlStack.val].Nodup
    exact List.nodup_singleton _
  have hnoen : (scope.entries.map Subtype.val).Nodup := by
    change ([] : List (List Char)).Nodup
    exact List.nodup_nil
  have hslotCode : scope.slotCode jlFirst = some 0 := by
    change [jlFirst.val].idxOf? jlFirst.val = some 0
    simp only [List.idxOf?_cons, beq_self_eq_true, if_true]
  have hslotState : scope.slotState jlSecond = some 1 := by
    change [jlFirst.val, jlSecond.val].idxOf? jlSecond.val = some 1
    simp only [List.idxOf?_cons, jlFirst_beq_second_false, if_false, beq_self_eq_true,
      Bool.false_eq_true, if_true, Option.map_some, Nat.zero_add]
  have hslotStack : scope.slotStack jlStack = some 0 := by
    change [jlStack.val].idxOf? jlStack.val = some 0
    simp only [List.idxOf?_cons, beq_self_eq_true, if_true]
  have hElab : elaborateExec scope tree = some op := by
    dsimp [tree, elaborateExec, scope, op, code, dest, sp, st]
    rw [hslotCode, hslotState, hslotStack]
    dsimp
  have hparse : ExecParse text tree := by
    change Gabbro.Core.Text.Parse jumpLongSyntax.grammar (jumpLongSyntax.print tree) tree
    exact jumpLongSyntax.parse_print tree
  have hbezeichnet : BezeichnetExec k scope text (execUnit k op) .jumpLong := by
    refine ⟨tree, hparse, ?_⟩
    exact ⟨op, hElab, rfl⟩
  have hs0lokal : s0.lokal entryContext = { pc := 0, stapel := [0] } := by
    simp only [s0, I.start, E, execProgram, start, execBoot, Zustand.start, entryContext,
      ↓reduceIte, List.length_cons, List.length_nil, Nat.zero_add, List.range_one]
  have hs0status : s0.status entryContext = .laeuft := by
    simp only [s0, I.start, E, execProgram, start, execBoot, Zustand.start, entryContext,
      ↓reduceIte]
  have heval0 : (ExecInstruction.declareState jlFirstDecl).evaluate s0 entryContext =
      some frame1 := by
    change (if jlFirstDecl.wellformed then pure ((s0.lokal entryContext).declare jlFirstDecl)
      else none) = some frame1
    rw [if_pos jlFirstWF]
    rfl
  have heval1 : (ExecInstruction.declareState jlSecondDecl).evaluate s1 entryContext =
      some frame2 := by
    change (if jlSecondDecl.wellformed then pure ((s1.lokal entryContext).declare jlSecondDecl)
      else none) = some frame2
    rw [if_pos jlSecondWF]
    rfl
  have hs1pc : (s1.lokal entryContext).pc = 1 := by
    simp only [s1, ExecFrame.advance, Function.update_self, frame1, ExecFrame.declare,
      hs0lokal]
  have hs1status : s1.status entryContext = .laeuft := by
    simpa only [s1, ExecFrame.advance] using hs0status
  have hs2pc : (s2.lokal entryContext).pc = 2 := by
    simp only [s2, ExecFrame.advance, Function.update_self, frame2, ExecFrame.declare,
      s1, frame1, hs0lokal]
  have hs2status : s2.status entryContext = .laeuft := by
    simpa only [s2, ExecFrame.advance] using hs1status
  have hs2current : (s2.lokal entryContext).current = some 0 := by
    simp only [s2, ExecFrame.advance, Function.update_self, frame2, ExecFrame.declare,
      s1, frame1, hs0lokal, List.nil_append, List.cons_append]
  have hs2states : (s2.lokal entryContext).states = [jlFirstDecl, jlSecondDecl] := by
    simp only [s2, ExecFrame.advance, Function.update_self, frame2, ExecFrame.declare,
      s1, frame1, hs0lokal, List.nil_append, List.cons_append]
  have hs2stapel : (s2.lokal entryContext).stapel = [0] := by
    simp only [s2, ExecFrame.advance, Function.update_self, frame2, ExecFrame.declare,
      s1, frame1, hs0lokal]
  have hs2spaces : (s2.lokal entryContext).spaces = [] := by
    simp only [s2, ExecFrame.advance, Function.update_self, frame2, ExecFrame.declare,
      s1, frame1, hs0lokal]
  have hs2halted : (s2.lokal entryContext).halted = false := by
    simp only [s2, ExecFrame.advance, Function.update_self, frame2, ExecFrame.declare,
      s1, frame1, hs0lokal]
  have heval : op.evaluate s2 entryContext = some next := by
    change (do let cur ← (s2.lokal entryContext).current
               let dst ← (s2.lokal entryContext).states[dest]?
               if cur != dest && !(s2.lokal entryContext).halted &&
                   stackOk (s2.lokal entryContext).stapel st &&
                   spaceOk dst.translation (s2.lokal entryContext).spaces sp then
                 pure { (s2.lokal entryContext) with
                   result := some (.jumpedLong code dest),
                   current := some dest, activeSpace := sp }
               else none) = some next
    dsimp [dest, code, sp, st]
    rw [hs2current]
    simp only [Option.bind_some]
    rw [hs2states]
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.bind_some]
    rw [hs2halted, hs2stapel, hs2spaces]
    try dsimp [jlSecondDecl]
    simp only [Bool.true_and, Bool.not_false, stackOk, spaceOk, List.length_cons,
      List.length_nil, Nat.zero_add, Nat.reduceLT, decide_true, if_true]
    simpa only [next, code, dest, sp, st, jlFirstDecl, jlSecondDecl, hs2states,
      hs2stapel, hs2halted, hs2spaces]
  have hhead0 : E.system.kopf s0 entryContext = some (.declareState jlFirstDecl) := by
    change execHead (pre ++ [op]) s0 entryContext = some (.declareState jlFirstDecl)
    simpa [execHead, hs0status, hs0lokal, pre, List.getElem?_cons_zero, heval0]
  have hhead1 : E.system.kopf s1 entryContext = some (.declareState jlSecondDecl) := by
    change execHead (pre ++ [op]) s1 entryContext = some (.declareState jlSecondDecl)
    simpa [execHead, hs1status, hs1pc, pre, List.getElem?_cons_succ, List.getElem?_cons_zero, heval1]
  have hhead2 : E.system.kopf s2 entryContext = some op := by
    change execHead (pre ++ [op]) s2 entryContext = some op
    simpa [execHead, hs2status, hs2pc, pre, List.getElem?_cons_succ, List.getElem?_cons_zero, heval]
  have hstep0 : (ExecInstruction.rule (.declareState jlFirstDecl)).ideal entryContext s0 ()
      [plan] (frame1.advance entryContext s0) := by
    exact ⟨frame1, heval0, rfl, rfl⟩
  have hstep1 : (ExecInstruction.rule (.declareState jlSecondDecl)).ideal entryContext s1 ()
      [plan] (frame2.advance entryContext s1) := by
    exact ⟨frame2, heval1, rfl, rfl⟩
  have hreach1 : E.system.IErreichbar s0 s1 := by
    exact System.IErreichbar.schritt entryContext () [plan] System.IErreichbar.start
      ⟨.declareState jlFirstDecl, hhead0, hstep0⟩
  have hreach2 : E.system.IErreichbar s0 s2 := by
    exact System.IErreichbar.schritt entryContext () [plan] hreach1
      ⟨.declareState jlSecondDecl, hhead1, hstep1⟩
  have hstepIdeal : E.system.ISchritt entryContext s2 () [plan] (next.advance entryContext s2) := by
    exact ⟨op, hhead2, ⟨next, heval, rfl, rfl⟩⟩
  have hstepImpl : E.system.ImplSchritt entryContext s2 () [plan] (next.advance entryContext s2) := by
    exact ⟨op, hhead2, ⟨next, heval, rfl, rfl⟩⟩
  refine ⟨k, scope, tree, op, env, start, text, pre, s2, next, ?_⟩
  exact ⟨⟨jlFirstDecl, jlSecondDecl, code, dest, sp, st, rfl, rfl⟩,
    hardware, hzul, accepted, hnode, hnosp, hnost, hnoen, hbezeichnet, hparse, hElab,
    hreach2, hhead2, heval, hstepIdeal, hstepImpl⟩
theorem jumpLong_aussage : JumpLongAussage := by
  refine ⟨?kern, jumpLongMeaning, jumpLongJoint⟩
  unfold execObligationsKern
  exact ⟨jumpLongParse, jumpLongInversion, jumpLongEindeutig, jumpLongDruck,
    execElaboriert .jumpLong, execRealisiert .jumpLong, execAnnahme .jumpLong,
    execIdeal .jumpLong, execEinheit .jumpLong, execImpl .jumpLong,
    execFortschritt .jumpLong, execErhaltung .jumpLong, execSicher .jumpLong,
    execRegelAntwortSicher .jumpLong, (fun k _ _ op _ => execAussenLokalUnit k op),
    execKosten .jumpLong, execSchranken, execEtiketten, execFluss⟩
end Gabbro.Core.Ast.LowLevel
