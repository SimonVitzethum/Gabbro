module

public import Core.Ast.LowLevel.Exec.Registry
public import Core.Ast.LowLevel.Exec.Proofs.ExecKern

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Gabbro.Core.Text Katalog Maschine Waechter
open Gabbro.Core.Annahme
open Gabbro.Core.Aussen

private theorem stopWordStopVal : (lowWord 's' "top").value = keyword "stop" := by rfl
private theorem stopWordCoreVal : (lowWord 'c' "ore").value = keyword "core" := by rfl
private theorem stopSemicolonVal : printSemicolon.value = semicolon := by rfl

private theorem stopPrints : (ExecTree.stopCore).production
    ((ExecTree.stopCore).printPieces.map PrintedToken.value) := by
  simp only [ExecTree.production, ExecTree.printPieces, List.map_cons, List.map_nil,
    stopWordStopVal, stopWordCoreVal, stopSemicolonVal]

private theorem stopDerivesSymbols {form : ExecForm} (ts : List LocatedToken) :
    DerivesSymbols (tokenGrammar (fun tokens (t : ExecTree form) => t.production tokens))
      (ts.map Symbol.terminal) ts := by
  induction ts with
  | nil => exact DerivesSymbols.nil
  | cons t ts ih => exact DerivesSymbols.terminal ih

private theorem stopParseOfPrint (tree : ExecTree form)
    (prints : tree.production (tree.printPieces.map PrintedToken.value)) :
    ExecParse tree.print tree := by
  obtain ⟨pieces, lexical, align⟩ := PrintedToken.renderLexed 0 tree.printPieces
  refine ⟨True.intro, pieces, lexical, ?_⟩
  refine Derives.production ⟨semanticTokens pieces, rfl, ?_⟩
    (stopDerivesSymbols (semanticTokens pieces))
  change tree.production (canonicalTokens pieces)
  rw [align]
  exact prints

private theorem stopParse : ExecParseAussage .stopCore := by
  intro text tree
  constructor
  · intro parsed
    rcases parsed with ⟨root, pieces, lex, derives⟩
    refine ⟨pieces, lex, ?_⟩
    cases derives with
    | production production children =>
        obtain ⟨expected, rfl, reads⟩ := production
        simpa only [canonicalTokens, children.terminalTokens] using reads
  · rintro ⟨pieces, lex, prod⟩
    refine ⟨True.intro, pieces, lex, ?_⟩
    refine Derives.production ⟨semanticTokens pieces, rfl, ?_⟩
      (stopDerivesSymbols (semanticTokens pieces))
    simpa only [canonicalTokens] using prod

private theorem stopInversion : ExecInversionAussage .stopCore := by
  intro tree tokens prod
  obtain ⟨pieces, lex, align⟩ := PrintedToken.renderLexed 0 tree.printPieces
  refine ⟨pieces, lex, ?_⟩
  cases tree
  simp only [ExecTree.production] at prod
  rw [align]
  exact stopPrints.trans prod.symm

private theorem stopEindeutig : ExecEindeutigAussage .stopCore := by
  intro first second tokens hfirst hsecond
  cases first
  cases second
  rfl

private theorem stopDruck : ExecDruckAussage .stopCore := by
  intro tree
  cases tree
  exact ⟨stopPrints, stopParseOfPrint _ stopPrints⟩

private theorem stopMeaning : StopMeaningAussage := by
  intro s c frame h
  simp only [ExecInstruction.evaluate] at h
  dsimp at h
  by_cases hcond : (s.lokal c).current.isSome ∧ ¬ (s.lokal c).halted
  · rw [if_pos hcond] at h
    cases h
    exact ⟨hcond.1, hcond.2, rfl, rfl⟩
  · rw [if_neg hcond] at h
    cases h

private theorem stopImageGueltigX86 : image.gueltig (Plattform.x86_64).ziel := by
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

private theorem stopZulStart {k : Katalog} {h : Katalog.Umgebung}
    (hw : Hardware k h) (img : image.gueltig k.plattform.ziel) :
    Katalog.ZulStart k h image
      ⟨0, (fun i => if i = 0 then some 0 else none), [], (fun _ => none), h.politik.sicht 0 []⟩ := by
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
    cases hb

private theorem stopKlauselnWahr (k : Katalog) (code : List ExecInstruction) :
    KlauselnWahr (execProgram k code) := by
  intro ρ lauf
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    cases hp
  · intro t p hp
    cases hp
  · intro t done p hp
    cases hp

private theorem stopWaechterHalten (k : Katalog) (code : List ExecInstruction) :
    WaechterHalten (execProgram k code) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ρ lauf t op args bedarf
    dsimp [kanonischeVerwendung, execProgram, Quelltabellen.leer] at bedarf
    cases bedarf
  · intro ρ lauf t
    rintro ⟨C, nonempty, blocked⟩
    obtain ⟨c, hc⟩ := nonempty
    obtain ⟨b, hblock, _, _, _⟩ := blocked c hc
    exact hblock
  · intro ρ lauf t l h _ hne
    exact (hne rfl).elim

private theorem stopAkzeptiertX86 (code : List ExecInstruction) :
    Akzeptiert (execProgram Plattform.x86_64.katalog code) := by
  refine ⟨?_, stopKlauselnWahr _ code, stopWaechterHalten _ code⟩
  refine ⟨by simpa only [execProgram] using Plattform.katalog_wohlgeformt .x86_64, ?_, ?_, ?_, ?_⟩
  · intro i
    exact execRegelLokal Plattform.x86_64.katalog i
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
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro η lauf
      exact ⟨stapelZustand_leer rfl _, speicherZustand_leer rfl _⟩
    · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      exact ⟨stapelZustand_leer rfl _, speicherZustand_leer rfl _⟩
    · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _
      exact ⟨stapelZustand_leer rfl _, speicherZustand_leer rfl _⟩
    · exact tiefenBezug_eq rfl

private theorem stopJoint : StopJointAussage := by
  let decl : ExecStateDecl := ⟨64, .kernel, .off, []⟩
  let pre : List ExecInstruction := [.declareState decl]
  let op : ExecInstruction := .stopCore
  let k : Katalog := Plattform.x86_64.katalog
  let sicht : Nat → AussenVerlauf → AussenSicht := fun _ _ => AussenSicht.leer
  let env : Katalog.Umgebung := Katalog.Umgebung.referenz k 1 sicht
  let start : AussenStart :=
    ⟨0, (fun i => if i = 0 then some 0 else none), [], (fun _ => none), env.politik.sicht 0 []⟩
  let scope : ExecScope := ⟨[], [], [], [], []⟩
  let tree : ExecTree .stopCore := .stopCore
  let text : RawText := tree.print
  let E : ExecUnit := execProgram k (pre ++ [op])
  let s0 : ExecState := (I.start E start).2
  have hardware : Hardware k env := Katalog.Umgebung.referenz_hardware k 1 sicht
    (by simpa only [k] using Plattform.katalog_wohlgeformt .x86_64) (by omega)
  have hdeclWell : decl.wellformed := by
    change (64 = 16 ∨ 64 = 32 ∨ 64 = 64)
    exact Or.inr (Or.inr rfl)
  have hs0status : s0.status entryContext = .laeuft := by
    simp only [s0, I.start, E, execProgram, Zustand.start, execBoot, start, entryContext, ↓reduceIte]
  have hs0pc : (s0.lokal entryContext).pc = 0 := by
    simp only [s0, I.start, E, execProgram, Zustand.start, execBoot, start, entryContext, ↓reduceIte]
  let frame0 : ExecFrame := (s0.lokal entryContext).declare decl
  have heval0 : (ExecInstruction.declareState decl).evaluate s0 entryContext = some frame0 := by
    simp only [ExecInstruction.evaluate]
    dsimp
    rw [if_pos hdeclWell]
  have heval0some : ((ExecInstruction.declareState decl).evaluate s0 entryContext).isSome = true := by
    rw [heval0]
    rfl
  have hhead0 : E.system.kopf s0 entryContext = some (.declareState decl) := by
    change execHead (pre ++ [op]) s0 entryContext = some (.declareState decl)
    unfold execHead
    rw [if_pos rfl]
    rw [hs0status]
    simp only [pre, op, hs0pc, List.cons_append, List.nil_append,
      List.getElem?_cons_zero]
    change (if ((ExecInstruction.declareState decl).evaluate s0 entryContext).isSome = true then
      some (ExecInstruction.declareState decl) else none) = some (ExecInstruction.declareState decl)
    rw [if_pos heval0some]
  let s : ExecState := frame0.advance entryContext s0
  have hstep0 : E.system.ISchritt entryContext s0 () [plan] s := by
    refine ⟨.declareState decl, hhead0, ?_⟩
    exact ⟨frame0, heval0, rfl, rfl⟩
  have hreach : E.system.IErreichbar (I.start E start).2 s := by
    exact System.IErreichbar.schritt entryContext () [plan] System.IErreichbar.start hstep0
  have hsstatus : s.status entryContext = .laeuft := by
    simpa only [s, ExecFrame.advance] using hs0status
  have hspc : (s.lokal entryContext).pc = 1 := by
    simp only [s, ExecFrame.advance, Function.update_self, hs0pc]
  have hcurrent0 : (s.lokal entryContext).current = some 0 := by
    simp only [s, ExecFrame.advance, Function.update_self, frame0, ExecFrame.declare,
      s0, I.start, E, execProgram, Zustand.start, execBoot, start, entryContext, ↓reduceIte]
  have hhalted0 : (s.lokal entryContext).halted = false := by
    simp only [s, ExecFrame.advance, Function.update_self, frame0, ExecFrame.declare,
      s0, I.start, E, execProgram, Zustand.start, execBoot, start, entryContext, ↓reduceIte]
  have hcond : (s.lokal entryContext).current.isSome ∧ ¬ (s.lokal entryContext).halted := by
    constructor
    · rw [hcurrent0]
      rfl
    · rw [hhalted0]
      intro h
      cases h
  let next : ExecFrame := { (s.lokal entryContext) with
    result := some .stopped
    halted := true }
  have heval : ExecInstruction.stopCore.evaluate s entryContext = some next := by
    simp only [ExecInstruction.evaluate]
    dsimp
    rw [if_pos hcond]
  have hevalSome : (ExecInstruction.stopCore.evaluate s entryContext).isSome = true := by
    rw [heval]
    rfl
  have hhead : E.system.kopf s entryContext = some op := by
    change execHead (pre ++ [op]) s entryContext = some op
    unfold execHead
    rw [if_pos rfl]
    rw [hsstatus]
    simp only [pre, op, hspc, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
    change (if (ExecInstruction.stopCore.evaluate s entryContext).isSome = true then
      some ExecInstruction.stopCore else none) = some ExecInstruction.stopCore
    rw [if_pos hevalSome]
  have hstep : E.system.ISchritt entryContext s () [plan] (next.advance entryContext s) := by
    refine ⟨.stopCore, hhead, ?_⟩
    exact ⟨next, heval, rfl, rfl⟩
  have himpl : E.system.ImplSchritt entryContext s () [plan] (next.advance entryContext s) := by
    refine ⟨.stopCore, hhead, ?_⟩
    exact ⟨next, heval, rfl, rfl⟩
  have hzul : E.ZulStart env start := by
    change Katalog.ZulStart k env image start
    exact stopZulStart (k := k) (h := env) hardware stopImageGueltigX86
  have hacc : Annahme.Akzeptiert E := by
    exact stopAkzeptiertX86 (pre ++ [op])
  have hopElab : elaborateExec scope tree = some op := by
    rfl
  have hparse : ExecParse text tree := by
    exact stopParseOfPrint tree stopPrints
  have hbezeichnet : BezeichnetExec k scope text (execUnit k op) .stopCore := by
    refine ⟨tree, hparse, ?_⟩
    exact ⟨op, hopElab, rfl⟩
  refine ⟨k, scope, tree, op, env, start, text, pre, s, next, ?_⟩
  refine ⟨?_, hardware, hzul, hacc, ?_, ?_, ?_, ?_, hbezeichnet, hparse, hopElab,
    hreach, hhead, heval, hstep, himpl⟩
  · exact ⟨decl, rfl, rfl⟩
  · exact List.nodup_nil
  · exact List.nodup_nil
  · exact List.nodup_nil
  · exact List.nodup_nil

theorem stop_aussage : StopAussage := by
  refine ⟨?kern, stopMeaning, stopJoint⟩
  unfold execObligationsKern
  exact ⟨stopParse, stopInversion, stopEindeutig, stopDruck,
    execElaboriert .stopCore, execRealisiert .stopCore, execAnnahme .stopCore,
    execIdeal .stopCore, execEinheit .stopCore, execImpl .stopCore,
    execFortschritt .stopCore, execErhaltung .stopCore, execSicher .stopCore,
    execRegelAntwortSicher .stopCore, execAussen .stopCore, execKosten .stopCore,
    execSchranken, execEtiketten, execFluss⟩

end Gabbro.Core.Ast.LowLevel
