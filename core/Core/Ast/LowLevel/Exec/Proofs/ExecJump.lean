module

public import Core.Ast.LowLevel.Exec.Proofs.ExecKern
public import Core.Ast.LowLevel.Exec.Registry

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Gabbro.Core.Text Katalog Maschine Waechter
open Gabbro.Core.Annahme
open Gabbro.Core.Aussen

private theorem jumpPrints (tree : ExecTree .jump) :
    tree.production (tree.printPieces.map PrintedToken.value) := by
  cases tree with
  | jump target =>
      simpa [ExecTree.production, ExecTree.printPieces, keyword, word, Identifier.print,
        PrintedToken.unquoted, printPunctuation, printOpen, printClose, printSemicolon,
        openParen, closeParen, semicolon, String.reduceToList]

private theorem jumpEindeutig : ExecEindeutigAussage .jump := by
  intro first second tokens h1 h2
  cases first with
  | jump t1 =>
      cases second with
      | jump t2 =>
          simp only [ExecTree.production] at h1 h2
          have heq : t1.val = t2.val := by
            have h := congrArg (fun l : List Token => l[1]?) (h1.symm.trans h2)
            simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h
            simpa only [Token.word.injEq] using h
          exact congrArg ExecTree.jump (Subtype.ext heq)

private def jumpSyntax : Gabbro.Core.Text.Syntax (ExecTree .jump) where
  reads := fun tokens tree => tree.production tokens
  unique := by
    intro tokens a b ha hb
    exact jumpEindeutig a b tokens ha hb
  printPieces := ExecTree.printPieces
  reads_print := jumpPrints

private theorem jumpParse : ExecParseAussage .jump := by
  intro text tree
  change Gabbro.Core.Text.Parse jumpSyntax.grammar text tree ↔
    ∃ pieces, Lexed text pieces ∧ tree.production (canonicalTokens pieces)
  exact jumpSyntax.parse_iff

private theorem jumpInversion : ExecInversionAussage .jump := by
  intro tree tokens prod
  cases tree with
  | jump target =>
      obtain ⟨pieces, lex, aligned⟩ :=
        PrintedToken.renderLexed 0 (ExecTree.printPieces (.jump target))
      refine ⟨pieces, ?_, ?_⟩
      · exact lex
      · have prints := jumpPrints (.jump target)
        simp only [ExecTree.production] at prod prints
        rw [← prints] at prod
        exact aligned.trans prod.symm

private theorem jumpDruck : ExecDruckAussage .jump := by
  intro tree
  constructor
  · exact jumpPrints tree
  · change Gabbro.Core.Text.Parse jumpSyntax.grammar (jumpSyntax.print tree) tree
    exact jumpSyntax.parse_print tree

private theorem jumpMeaning : JumpMeaningAussage := by
  intro code state s c frame h
  change (do
    let cur ← (s.lokal c).current
    if cur == state ∧ ¬ (s.lokal c).halted ∧ state < (s.lokal c).states.length then
      some { (s.lokal c) with result := some (ExecResult.jumped code state) }
    else none) = some frame at h
  cases hcur : (s.lokal c).current with
  | none =>
      simp only [hcur, Option.bind_none] at h
      cases h
  | some cur =>
      simp only [hcur, Option.bind_some] at h
      dsimp at h
      by_cases hcond : cur == state ∧ ¬ (s.lokal c).halted ∧ state < (s.lokal c).states.length
      · rw [if_pos hcond] at h
        simp only [Option.some.injEq] at h
        subst frame
        have hcurEq : cur = state := beq_iff_eq.mp hcond.1
        subst cur
        exact ⟨rfl, hcond.2.2, hcond.2.1, rfl, rfl⟩
      · rw [if_neg hcond] at h
        cases h

private def jumpStateName : Identifier :=
  ⟨['s'], ⟨'s', [], rfl, by
    unfold isNameStart isLetter
    left
    left
    constructor <;> decide, by
      intro a h
      cases h⟩⟩

private def jumpCodeName : Identifier :=
  ⟨['f'], ⟨'f', [], rfl, by
    unfold isNameStart isLetter
    left
    left
    constructor <;> decide, by
      intro a h
      cases h⟩⟩

private theorem jumpState_slot : [jumpStateName.val].idxOf? jumpStateName.val = some 0 := by
  simp only [List.idxOf?_cons, beq_self_eq_true, if_true]

private theorem jumpCode_slot : [jumpCodeName.val].idxOf? jumpCodeName.val = some 0 := by
  simp only [List.idxOf?_cons, beq_self_eq_true, if_true]

private def jumpScope : ExecScope :=
  ⟨[jumpStateName], [], [], [(jumpCodeName, jumpStateName)], []⟩

private theorem jumpSlotCode_slot : jumpScope.slotCode jumpCodeName = some 0 := by
  change [jumpCodeName.val].idxOf? jumpCodeName.val = some 0
  exact jumpCode_slot

private theorem jumpCodeState_slot : jumpScope.codeState jumpCodeName = some 0 := by
  simp only [jumpScope, ExecScope.codeState, ExecScope.slotState, List.find?_cons,
    beq_self_eq_true, if_true, List.map_cons, List.map_nil, jumpState_slot]

private theorem jumpElab : elaborateExec jumpScope (ExecTree.jump jumpCodeName) =
    some (ExecInstruction.jump 0 0) := by
  simp only [elaborateExec, jumpSlotCode_slot, jumpCodeState_slot, Option.bind_some]

private theorem imageGueltigX86Jump : image.gueltig (Plattform.x86_64).ziel := by
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

private def jumpStart (h : Katalog.Umgebung) : AussenStart :=
  ⟨0, (fun i => if i = 0 then some 0 else none), [], (fun _ => none), h.politik.sicht 0 []⟩

private theorem jumpZulStart {k : Katalog} {h : Katalog.Umgebung}
    (hw : Hardware k h) (img : image.gueltig k.plattform.ziel) :
    Katalog.ZulStart k h image (jumpStart h) := by
  refine ⟨img, hw.kerne, ?_, ?_, List.Pairwise.nil, ?_, ?_, rfl⟩
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
  · intro r hr
    cases hr
  · intro a byte hb
    change (none : Option UInt8) = some byte at hb
    cases hb

private theorem jumpKlauseln (k : Katalog) (code : List ExecInstruction) :
    KlauselnWahr (execProgram k code) := by
  intro ρ runs
  dsimp [kanonischeKlauseln, execProgram, Quelltabellen.leer, Quellklauseln.leer]
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    cases hp
  · intro t p hp
    cases hp
  · intro t done p hp
    cases hp

private theorem jumpWaechter (k : Katalog) (code : List ExecInstruction) :
    WaechterHalten (execProgram k code) := by
  constructor
  · intro ρ runs t o args bedarf
    change False at bedarf
    exact False.elim bedarf
  · intro ρ runs t
    rintro ⟨C, nonempty, blocked⟩
    obtain ⟨c, hc⟩ := nonempty
    obtain ⟨b, hb, _, _⟩ := blocked c hc
    exact hb

private theorem jumpAkzeptiert (code : List ExecInstruction) :
    Akzeptiert (execProgram Plattform.x86_64.katalog code) := by
  refine ⟨?_, jumpKlauseln _ code, jumpWaechter _ code⟩
  refine ⟨by simpa [execProgram, Plattform.katalog] using Plattform.katalog_wohlgeformt .x86_64, ?_, ?_, ?_⟩
  · intro i c s u w p hideal
    change ∃ frame, i.evaluate s c = some frame ∧ [p] = [plan] ∧
      u = frame.advance c s at hideal
    rcases hideal with ⟨frame, heval, hp, hu⟩
    have hp' : p = plan := by simpa using hp
    subst p
    unfold Annahme.Befugt
    constructor
    · intro x hx
      cases hx
    · intro l hl
      cases hl
  · exact ⟨zulassung_m2 _, by
      apply aussen_gueltig_aus_kontext
      intro run t s c w spur s' step
      cases step with
      | kontext _ _ regel execute =>
          obtain ⟨_, _, frame, _, planEq, rfl⟩ := regel
          cases (List.cons.inj planEq).1
          obtain ⟨rfl, rfl⟩ := execGenauInternal execute
          exact ⟨⟨fun _ mem => (List.not_mem_nil mem).elim, [],
            (List.append_nil _).symm, fun _ mem => (List.not_mem_nil mem).elim⟩, fun h => h⟩⟩
  · exact execProgramFlussLokal _ code

private theorem jumpJoint : JumpJointAussage := by
  let k : Katalog := Plattform.x86_64.katalog
  let decl : ExecStateDecl := ⟨64, .kernel, .off, []⟩
  let tree : ExecTree .jump := .jump jumpCodeName
  let op : ExecInstruction := .jump 0 0
  let pre : List ExecInstruction := [.declareState decl]
  let sicht : Nat → AussenVerlauf → AussenSicht := fun _ _ => AussenSicht.leer
  let env : Katalog.Umgebung := Katalog.Umgebung.referenz k 1 sicht
  let start := jumpStart env
  let text : RawText := tree.print
  let E : ExecUnit := execProgram k (pre ++ [op])
  let s0 : ExecState := (I.start E start).2
  have hw : Hardware k env := by
    apply Katalog.Umgebung.referenz_hardware k 1 sicht
    · simpa [k] using Plattform.katalog_wohlgeformt .x86_64
    · omega
  have hzul : E.ZulStart env start := by
    change Katalog.ZulStart k env image (jumpStart env)
    exact jumpZulStart hw imageGueltigX86Jump
  have accepted : Akzeptiert E := by
    change Akzeptiert (execProgram k (pre ++ [op]))
    exact jumpAkzeptiert (pre ++ [op])
  have hElab : elaborateExec jumpScope tree = some op := by
    simpa [tree, op] using jumpElab
  have hparse : ExecParse text tree := by
    change Gabbro.Core.Text.Parse jumpSyntax.grammar (jumpSyntax.print tree) tree
    exact jumpSyntax.parse_print tree
  have hbezeichnet : BezeichnetExec k jumpScope text (execUnit k op) .jump := by
    refine ⟨tree, hparse, ?_⟩
    exact ⟨op, hElab, rfl⟩
  have hnodupStates : (jumpScope.states.map Subtype.val).Nodup := by
    change [jumpStateName.val].Nodup
    exact List.nodup_singleton _
  have hnodupSpaces : (jumpScope.spaces.map Subtype.val).Nodup := by
    change ([] : List (List Char)).Nodup
    exact List.nodup_nil
  have hnodupStapel : (jumpScope.stapel.map Subtype.val).Nodup := by
    change ([] : List (List Char)).Nodup
    exact List.nodup_nil
  have hnodupEntries : (jumpScope.entries.map Subtype.val).Nodup := by
    change ([] : List (List Char)).Nodup
    exact List.nodup_nil
  have decl_wf : decl.wellformed := by
    change 64 = 16 ∨ 64 = 32 ∨ 64 = 64
    omega
  have hs0status : s0.status entryContext = .laeuft := by
    simp only [s0, I.start, E, execProgram, execBoot, jumpStart, Zustand.start,
      entryContext, ↓reduceIte]
  have hs0pc : (s0.lokal entryContext).pc = 0 := by
    rfl
  let frame0 : ExecFrame := ExecFrame.declare (s0.lokal entryContext) decl
  have heval0 : (ExecInstruction.declareState decl).evaluate s0 entryContext = some frame0 := by
    change (if decl.wellformed then some (ExecFrame.declare (s0.lokal entryContext) decl) else none) =
      some frame0
    rw [if_pos decl_wf]
    rfl
  let s : ExecState := frame0.advance entryContext s0
  have hhead0 : E.system.kopf s0 entryContext = some (ExecInstruction.declareState decl) := by
    change execHead (pre ++ [op]) s0 entryContext = some (ExecInstruction.declareState decl)
    exact (execHead_some_iff (ExecInstruction.declareState decl) s0 entryContext).2
      ⟨hs0status, rfl, hs0pc, by rw [heval0]; rfl⟩
  have hstep0 : (ExecInstruction.rule (ExecInstruction.declareState decl)).ideal
      entryContext s0 () [plan] s := by
    change ∃ frame, (ExecInstruction.declareState decl).evaluate s0 entryContext = some frame ∧
      [plan] = [plan] ∧ s = frame.advance entryContext s0
    exact ⟨frame0, heval0, rfl, rfl⟩
  have hreach : E.system.IErreichbar s0 s := by
    exact System.IErreichbar.schritt entryContext () [plan] System.IErreichbar.start
      ⟨ExecInstruction.declareState decl, hhead0, hstep0⟩
  have hsstatus : s.status entryContext = .laeuft := by
    simpa [s, ExecFrame.advance] using hs0status
  have hspc : (s.lokal entryContext).pc = 1 := by
    simp only [s, ExecFrame.advance, Function.update_self, hs0pc]
  have hscurrent : (s.lokal entryContext).current = some 0 := by
    simp only [s, ExecFrame.advance, frame0, ExecFrame.declare, Function.update_self,
      s0, I.start, E, execProgram, execBoot, jumpStart, Zustand.start, entryContext, ↓reduceIte]
  have hshalted : (s.lokal entryContext).halted = false := by
    simp only [s, ExecFrame.advance, frame0, ExecFrame.declare, Function.update_self,
      s0, I.start, E, execProgram, execBoot, jumpStart, Zustand.start, entryContext, ↓reduceIte]
  have hsstates : (s.lokal entryContext).states = [decl] := by
    simp only [s, ExecFrame.advance, frame0, ExecFrame.declare, Function.update_self,
      List.nil_append, s0, I.start, E, execProgram, execBoot, jumpStart, Zustand.start,
      entryContext, ↓reduceIte]
  let next : ExecFrame := { (s.lokal entryContext) with result := some (ExecResult.jumped 0 0) }
  have hcond : 0 == 0 ∧ ¬ (s.lokal entryContext).halted ∧
      0 < (s.lokal entryContext).states.length := by
    rw [hshalted, hsstates]
    decide
  have heval : op.evaluate s entryContext = some next := by
    change (do
      let cur ← (s.lokal entryContext).current
      if cur == 0 ∧ ¬ (s.lokal entryContext).halted ∧
          0 < (s.lokal entryContext).states.length then
        some { (s.lokal entryContext) with result := some (ExecResult.jumped 0 0) }
      else none) = some next
    rw [hscurrent]
    dsimp
    rw [if_pos hcond]
    rfl
  have hevalSome : (op.evaluate s entryContext).isSome = true := by
    rw [heval]
    rfl
  have hhead : E.system.kopf s entryContext = some op := by
    change execHead (pre ++ [op]) s entryContext = some op
    unfold execHead
    simp only [entryContext, ↓reduceIte, hsstatus, hspc, List.getElem?_cons_succ,
      List.getElem?_cons_zero]
    exact if_pos hevalSome
  have hstep : E.system.ISchritt entryContext s () [plan] (next.advance entryContext s) := by
    refine ⟨op, hhead, ?_⟩
    change ∃ frame, op.evaluate s entryContext = some frame ∧ [plan] = [plan] ∧
      (next.advance entryContext s) = frame.advance entryContext s
    exact ⟨next, heval, rfl, rfl⟩
  have himpl : E.system.ImplSchritt entryContext s () [plan] (next.advance entryContext s) := by
    refine ⟨op, hhead, ?_⟩
    change ∃ frame, op.evaluate s entryContext = some frame ∧ [plan] = [plan] ∧
      (next.advance entryContext s) = frame.advance entryContext s
    exact ⟨next, heval, rfl, rfl⟩
  refine ⟨k, jumpScope, tree, op, env, start, text, pre, s, next, ?_⟩
  exact ⟨⟨decl, 0, 0, rfl, rfl⟩, hw, hzul, accepted, hnodupStates,
    hnodupSpaces, hnodupStapel, hnodupEntries, hbezeichnet, hparse, hElab,
    hreach, hhead, heval, hstep, himpl⟩

theorem jump_aussage : JumpAussage := by
  refine ⟨?kern, jumpMeaning, jumpJoint⟩
  unfold execObligationsKern
  exact ⟨jumpParse, jumpInversion, jumpEindeutig, jumpDruck,
    execElaboriert .jump, execRealisiert .jump, execAnnahme .jump, execIdeal .jump,
    execEinheit .jump, execImpl .jump, execFortschritt .jump, execErhaltung .jump,
    execSicher .jump, execRegelAntwortSicher .jump,
    execAussen .jump, execKosten .jump,
    execSchranken, execEtiketten, execFluss⟩

end Gabbro.Core.Ast.LowLevel
