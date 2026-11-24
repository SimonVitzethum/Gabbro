module

public import Core.Ast.LowLevel.Exec.Registry
public import Core.Ast.LowLevel.Exec.Proofs.ExecKern

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Gabbro.Core.Text Katalog Maschine Waechter
open Gabbro.Core.Annahme
open Gabbro.Core.Aussen

private theorem waitPrints (tree : ExecTree .waitInterrupt) :
    tree.production (tree.printPieces.map PrintedToken.value) := by
  cases tree
  simp only [ExecTree.production, ExecTree.printPieces, List.map_cons, List.map_nil,
    keyword, semicolon, printSemicolon, printPunctuation, word, Identifier.print,
    PrintedToken.unquoted, String.reduceToList]

private theorem waitEindeutig : ExecEindeutigAussage .waitInterrupt := by
  intro first second tokens h1 h2
  cases first
  cases second
  rfl

private def waitSyntax : Gabbro.Core.Text.Syntax (ExecTree .waitInterrupt) where
  reads := fun tokens tree => tree.production tokens
  unique := by
    intro tokens a b ha hb
    exact waitEindeutig a b tokens ha hb
  printPieces := ExecTree.printPieces
  reads_print := waitPrints

private theorem waitParse : ExecParseAussage .waitInterrupt := by
  intro text tree
  change Gabbro.Core.Text.Parse waitSyntax.grammar text tree ↔
    ∃ pieces, Lexed text pieces ∧ tree.production (canonicalTokens pieces)
  exact waitSyntax.parse_iff

private theorem waitInversion : ExecInversionAussage .waitInterrupt := by
  intro tree tokens prod
  cases tree
  obtain ⟨pieces, lex, aligned⟩ :=
    PrintedToken.renderLexed 0 (ExecTree.printPieces (.waitInterrupt : ExecTree .waitInterrupt))
  refine ⟨pieces, ?_, ?_⟩
  · exact lex
  · have prints := waitPrints (.waitInterrupt : ExecTree .waitInterrupt)
    simp only [ExecTree.production] at prod prints
    rw [← prints] at prod
    exact aligned.trans prod.symm

private theorem waitDruck : ExecDruckAussage .waitInterrupt := by
  intro tree
  constructor
  · exact waitPrints tree
  · change Gabbro.Core.Text.Parse waitSyntax.grammar (waitSyntax.print tree) tree
    exact waitSyntax.parse_print tree

private theorem waitMeaning : WaitMeaningAussage := by
  intro s c frame heval
  change (if (s.lokal c).current.isSome ∧ ¬ (s.lokal c).halted then
    some { (s.lokal c) with result := some .waited } else none) = some frame at heval
  split at heval
  · rename_i hcond
    cases heval
    have hhalt : (s.lokal c).halted = false := by
      cases h : (s.lokal c).halted
      · rfl
      · exact (hcond.2 h).elim
    exact ⟨hcond.1, hcond.2, rfl, hhalt⟩
  · cases heval

private theorem waitImageGueltig : image.gueltig (Plattform.x86_64).ziel := by
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

private theorem waitProgramAkzeptiert (code : List ExecInstruction) :
    Annahme.Akzeptiert (execProgram Plattform.x86_64.katalog code) := by
  let E := execProgram Plattform.x86_64.katalog code
  refine ⟨⟨Plattform.katalog_wohlgeformt .x86_64, ?_, ⟨zulassung_m2 _, ?_⟩,
    execProgramFlussLokal _ code, ?_⟩, ?_, ?_⟩
  · intro i
    exact execRegelLokal Plattform.x86_64.katalog i
  · apply aussen_gueltig_aus_kontext
    intro run t s c w spur s' step
    cases step with
    | kontext _ _ regel execute =>
      obtain ⟨i, hi, frame, heval, planEq, hu⟩ := regel
      cases (List.cons.inj planEq).1
      obtain ⟨traceEq, nextEq⟩ := execGenauInternal execute
      subst spur
      rw [nextEq, hu]
      simp only [ExecFrame.advance]
      refine ⟨?_, ?_⟩
      · refine ⟨fun _ mem => (List.not_mem_nil mem).elim, [], ?_,
          fun _ mem => (List.not_mem_nil mem).elim⟩
        rw [List.append_nil]
      · intro h q hq hcut hans
        exact h q hq hcut hans
  · exact schrankenLokal_leer rfl rfl rfl
  · intro ρ lauf
    change (∀ p ∈ ([] : List (ExecState → Prop)), p (I.start E ρ.start).2) ∧
      (∀ t : I.Schnitt E ρ, ∀ p ∈ ([] : List (ExecState → Prop)), p (ρ.zeit.zustand t.val)) ∧
      (∀ t : I.Schnitt E ρ, (∀ c, E.system.fertig (ρ.zeit.zustand t.val) c) →
        ∀ p ∈ ([] : List (ExecState → Prop)), p (ρ.zeit.zustand t.val))
    exact ⟨fun _ h => (List.not_mem_nil h).elim,
      fun _ _ h => (List.not_mem_nil h).elim,
      fun _ _ _ h => (List.not_mem_nil h).elim⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro ρ lauf t op args need
      exact False.elim need
    · intro ρ lauf t waiting
      obtain ⟨C, nonEmpty, blocked⟩ := waiting
      obtain ⟨c, hc⟩ := nonEmpty
      obtain ⟨b, hb, _⟩ := blocked c hc
      simpa only [execProgram] using hb
    · intro ρ lauf t l h holder bound
      have hnone : E.schranken.halten l = none := by
        rfl
      rw [hnone] at bound
      exact (bound rfl).elim

private theorem waitErfuellbar : WaitJointAussage := by
  let k : Katalog := Plattform.x86_64.katalog
  let decl : ExecStateDecl := ⟨64, .kernel, .off, []⟩
  let scope : ExecScope := ⟨[], [], [], [], []⟩
  let tree : ExecTree .waitInterrupt := .waitInterrupt
  let op : ExecInstruction := .waitInterrupt
  let sicht : Nat → AussenVerlauf → AussenSicht := fun _ _ => AussenSicht.leer
  let env : Katalog.Umgebung := Katalog.Umgebung.referenz k 1 sicht
  let pre : List ExecInstruction := [.declareState decl]
  let E : ExecUnit := execProgram k (pre ++ [op])
  let text : RawText := tree.print
  have hardware : Hardware k env := by
    apply Katalog.Umgebung.referenz_hardware k 1 sicht
    · simpa only [k] using Plattform.katalog_wohlgeformt .x86_64
    · omega
  obtain ⟨start, hstart⟩ :=
    Katalog.zulStart_erfuellbar (k := k) (h := env) (bild := image) hardware waitImageGueltig
  let s0 : ExecState := (I.start E start).2
  have hs0status : s0.status entryContext = .laeuft := by
    simp only [s0, I.start, E, execProgram, execBoot, Zustand.start, entryContext, ↓reduceIte]
  have hs0pc : (s0.lokal entryContext).pc = 0 := by
    rfl
  have hs0states : (s0.lokal entryContext).states = [] := by
    rfl
  have hdecl : decl.wellformed := by
    decide
  let frame0 : ExecFrame := (s0.lokal entryContext).declare decl
  have heval0 : (.declareState decl : ExecInstruction).evaluate s0 entryContext = some frame0 := by
    change (if decl.wellformed then some ((s0.lokal entryContext).declare decl) else none) = some frame0
    rw [if_pos hdecl]
  let s : ExecState := frame0.advance entryContext s0
  have hsstatus : s.status entryContext = .laeuft := by
    simpa only [s, ExecFrame.advance] using hs0status
  have hspc : (s.lokal entryContext).pc = 1 := by
    simp only [s, ExecFrame.advance, Function.update_self, hs0pc]
  have hscurrent : (s.lokal entryContext).current = some 0 := by
    simp only [s, ExecFrame.advance, Function.update_self, frame0, ExecFrame.declare, hs0states]
  have shalted : (s.lokal entryContext).halted = false := by
    simp only [s, ExecFrame.advance, Function.update_self, frame0, ExecFrame.declare]
    rfl
  let next : ExecFrame := { (s.lokal entryContext) with result := some .waited }
  have hcond : (s.lokal entryContext).current.isSome ∧ ¬ (s.lokal entryContext).halted := by
    constructor
    · rw [hscurrent]
      rfl
    · intro hh
      rw [shalted] at hh
      cases hh
  have heval : op.evaluate s entryContext = some next := by
    change (if (s.lokal entryContext).current.isSome ∧ ¬ (s.lokal entryContext).halted then
      some { (s.lokal entryContext) with result := some .waited } else none) = some next
    rw [if_pos hcond]
  have hhead0 : E.system.kopf s0 entryContext = some (.declareState decl : ExecInstruction) := by
    change execHead [(.declareState decl : ExecInstruction), .waitInterrupt] s0 entryContext =
      some (.declareState decl : ExecInstruction)
    unfold execHead
    rw [if_pos rfl, hs0status, hs0pc]
    dsimp
    simp only [List.getElem?_cons_zero, Option.bind_some]
    rw [if_pos (by rw [heval0]; rfl)]
  have hhead : E.system.kopf s entryContext = some op := by
    change execHead [(.declareState decl : ExecInstruction), .waitInterrupt] s entryContext =
      some (.waitInterrupt : ExecInstruction)
    unfold execHead
    rw [if_pos rfl, hsstatus, hspc]
    dsimp
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, List.getElem?_nil,
      Option.bind_some]
    rw [if_pos (by rw [heval]; rfl)]
  have hstep0 : ((ExecInstruction.rule (.declareState decl : ExecInstruction)).ideal
      entryContext s0 () [plan] s) := by
    change ∃ frame : ExecFrame,
      (.declareState decl : ExecInstruction).evaluate s0 entryContext = some frame ∧
      [plan] = [plan] ∧ s = frame.advance entryContext s0
    exact ⟨frame0, heval0, rfl, rfl⟩
  have hreach : E.system.IErreichbar (I.start E start).2 s := by
    change E.system.IErreichbar s0 s
    exact System.IErreichbar.schritt entryContext () [plan] System.IErreichbar.start
      ⟨.declareState decl, hhead0, hstep0⟩
  have hstep : E.system.ISchritt entryContext s () [plan] (next.advance entryContext s) := by
    refine ⟨op, hhead, ?_⟩
    exact ⟨next, heval, rfl, rfl⟩
  have himpl : E.system.ImplSchritt entryContext s () [plan] (next.advance entryContext s) := by
    refine ⟨op, hhead, ?_⟩
    exact ⟨next, heval, rfl, rfl⟩
  have hparse : ExecParse text tree := (waitDruck tree).2
  have hElab : elaborateExec scope tree = some op := by
    rfl
  have hbezeichnet : BezeichnetExec k scope text (execUnit k op) .waitInterrupt := by
    refine ⟨tree, hparse, ?_⟩
    exact ⟨op, hElab, rfl⟩
  have haccepted : Annahme.Akzeptiert E := by
    change Annahme.Akzeptiert (execProgram k (pre ++ [op]))
    exact waitProgramAkzeptiert (pre ++ [op])
  refine ⟨k, scope, tree, op, env, start, text, pre, s, next, ?_⟩
  refine ⟨⟨decl, rfl, rfl⟩, hardware, ?_, haccepted, ?_, ?_, ?_, ?_,
    hbezeichnet, hparse, hElab, hreach, hhead, heval, hstep, himpl⟩
  · change Katalog.ZulStart k env image start
    exact hstart
  · change ([] : List RawText).Nodup
    exact List.nodup_nil
  · change ([] : List RawText).Nodup
    exact List.nodup_nil
  · change ([] : List RawText).Nodup
    exact List.nodup_nil
  · change ([] : List RawText).Nodup
    exact List.nodup_nil

theorem wait_aussage : WaitAussage := by
  refine ⟨?kern, waitMeaning, waitErfuellbar⟩
  unfold execObligationsKern
  exact ⟨waitParse, waitInversion, waitEindeutig, waitDruck,
    execElaboriert .waitInterrupt, execRealisiert .waitInterrupt, execAnnahme .waitInterrupt,
    execIdeal .waitInterrupt, execEinheit .waitInterrupt, execImpl .waitInterrupt,
    execFortschritt .waitInterrupt, execErhaltung .waitInterrupt, execSicher .waitInterrupt,
    execRegelAntwortSicher .waitInterrupt, execAussen .waitInterrupt, execKosten .waitInterrupt,
    execSchranken, execEtiketten, execFluss⟩

end Gabbro.Core.Ast.LowLevel
