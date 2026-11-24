module

public import Core.Ast.LowLevel.Exec.Registry
public import Core.Ast.LowLevel.Exec.Proofs.ExecKern

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Gabbro.Core.Text Katalog Maschine Waechter
open Gabbro.Core.Annahme
open Gabbro.Core.Aussen
open Gabbro.Core.Sicherheit (Absturz NeueWirkungen)

private theorem execPrintIntegerVal (n : Nat) : (printInteger n).value = .natural n := by rfl
private theorem execIdentifierPrintVal (i : Identifier) : (Identifier.print i).value = .word i.val := by rfl
private theorem execPrintOpenBraceVal : printOpenBrace.value = openBrace := by rfl
private theorem execPrintCloseBraceVal : printCloseBrace.value = closeBrace := by rfl
private theorem execPrintCommaVal : printComma.value = comma := by rfl
private theorem execPrintSemicolonVal : printSemicolon.value = semicolon := by rfl

private theorem execPrivilegeVal (p : ExecPrivilege) :
    (privilegePrint p).value = privilegeKeyword p := by
  cases p <;> simp only [privilegePrint, privilegeKeyword, word, Identifier.print,
    PrintedToken.unquoted, keyword, String.reduceToList]

private theorem execTranslationVal (t : ExecTranslation) :
    (translationPrint t).value = translationKeyword t := by
  cases t <;> simp only [translationPrint, translationKeyword, word, Identifier.print,
    PrintedToken.unquoted, keyword, String.reduceToList]

private theorem execGuardVal (g : ExecGuard) : (guardPrint g).value = guardKeyword g := by
  cases g <;> simp only [guardPrint, guardKeyword, word, Identifier.print,
    PrintedToken.unquoted, keyword, String.reduceToList]

private theorem execMapIntersperse {α β : Type} (f : α → β) (sep : α) : ∀ xs : List α,
    (xs.intersperse sep).map f = (xs.map f).intersperse (f sep)
  | [] => rfl
  | [_] => rfl
  | x :: y :: ys => by
      simp only [List.intersperse_cons_cons, List.map_cons, execMapIntersperse f sep (y :: ys)]

private theorem execGuardsTokensPrint (guards : List ExecGuard) :
    ((guards.map guardPrint).intersperse printComma).map PrintedToken.value =
      guardsTokens guards := by
  induction guards with
  | nil => rfl
  | cons g gs ih =>
      cases gs with
      | nil =>
          simp only [List.map_cons, List.map_nil, List.intersperse_singleton, List.intersperse_nil,
            execGuardVal, guardsTokens]
      | cons h hs =>
          have ih' :
              List.map PrintedToken.value
                  (List.intersperse printComma (guardPrint h :: List.map guardPrint hs)) =
                List.intersperse comma (guardKeyword h :: List.map guardKeyword hs) := by
            simpa only [List.map_cons, guardsTokens] using ih
          simp only [List.map_cons, List.intersperse_cons_cons, execPrintCommaVal, execGuardVal,
            ih', guardsTokens]

private theorem execStateDeclPrints (name : Identifier) (decl : ExecStateDecl) :
    (ExecTree.stateDecl name decl).production
      ((ExecTree.stateDecl name decl).printPieces.map PrintedToken.value) := by
  simp only [ExecTree.production, ExecTree.printPieces, List.map_cons, List.map_nil,
    List.map_append, List.append_assoc, execIdentifierPrintVal, execPrintIntegerVal,
    execPrintOpenBraceVal, execPrintCloseBraceVal, execPrintCommaVal, execPrintSemicolonVal,
    execPrivilegeVal, execTranslationVal, execGuardsTokensPrint, word, Identifier.print,
    PrintedToken.unquoted, keyword, String.reduceToList]

private theorem execPrivilegeKeyword_inj : Function.Injective privilegeKeyword := by
  intro a b h
  cases a <;> cases b <;>
    simp only [privilegeKeyword, keyword, String.reduceToList, Token.word.injEq, List.cons.injEq,
      Char.reduceEq, reduceCtorEq] at h ⊢
  all_goals simp_all

private theorem execTranslationKeyword_inj : Function.Injective translationKeyword := by
  intro a b h
  cases a <;> cases b <;>
    simp only [translationKeyword, keyword, String.reduceToList, Token.word.injEq, List.cons.injEq,
      Char.reduceEq, reduceCtorEq] at h ⊢
  all_goals simp_all

private theorem execGuardKeyword_inj : Function.Injective guardKeyword := by
  intro a b h
  cases a <;> cases b <;>
    simp only [guardKeyword, keyword, String.reduceToList, Token.word.injEq, List.cons.injEq,
      Char.reduceEq, reduceCtorEq] at h ⊢
  all_goals simp_all

private def execGuardKey : List ExecGuard → List Token
  | [] => []
  | [g] => [guardKeyword g]
  | g :: h :: rest => guardKeyword g :: comma :: execGuardKey (h :: rest)

private theorem execGuardsTokensKey : ∀ gs, guardsTokens gs = execGuardKey gs
  | [] => rfl
  | [g] => by
      simp only [guardsTokens, execGuardKey, List.map_cons, List.map_nil,
        List.intersperse_singleton, List.intersperse_nil]
  | g :: h :: rest => by
      rw [show guardsTokens (g :: h :: rest) =
        guardKeyword g :: comma :: guardsTokens (h :: rest) by
          simp only [guardsTokens, List.map_cons, List.intersperse_cons_cons]]
      rw [show execGuardKey (g :: h :: rest) =
        guardKeyword g :: comma :: execGuardKey (h :: rest) by rfl]
      rw [execGuardsTokensKey (h :: rest)]

private theorem execGuardKey_inj : Function.Injective execGuardKey := by
  intro as bs h
  induction as generalizing bs with
  | nil =>
      cases bs with
      | nil => rfl
      | cons b bs => cases bs <;> cases h
  | cons a as ih =>
      cases as with
      | nil =>
          cases bs with
          | nil => cases h
          | cons b bs =>
              cases bs with
              | nil =>
                  change [guardKeyword a] = [guardKeyword b] at h
                  simp only [List.cons.injEq] at h
                  have : a = b := execGuardKeyword_inj h.1
                  subst b
                  rfl
              | cons c cs =>
                  change [guardKeyword a] = guardKeyword b :: comma :: execGuardKey (c :: cs) at h
                  simp only [List.cons.injEq] at h
                  cases h.2
      | cons a2 as2 =>
          cases bs with
          | nil => cases h
          | cons b bs =>
              cases bs with
              | nil =>
                  change guardKeyword a :: comma :: execGuardKey (a2 :: as2) = [guardKeyword b] at h
                  simp only [List.cons.injEq] at h
                  cases h.2
              | cons b2 bs2 =>
                  change guardKeyword a :: comma :: execGuardKey (a2 :: as2) =
                    guardKeyword b :: comma :: execGuardKey (b2 :: bs2) at h
                  simp only [List.cons.injEq] at h
                  rcases h with ⟨hhead, htail⟩
                  rcases htail with ⟨_, htail⟩
                  have : a = b := execGuardKeyword_inj hhead
                  subst b
                  cases ih htail
                  rfl

private theorem execGuardsTokens_inj : Function.Injective guardsTokens := by
  intro a b h
  apply execGuardKey_inj
  rwa [execGuardsTokensKey a, execGuardsTokensKey b] at h

private theorem execEindeutig_stateDecl : ExecEindeutigAussage .stateDecl := by
  intro first second tokens hfirst hsecond
  cases first with
  | stateDecl name1 decl1 =>
      cases second with
      | stateDecl name2 decl2 =>
          simp only [ExecTree.production] at hfirst hsecond
          have h := hfirst.symm.trans hsecond
          have h' := h
          simp only [List.cons_append, List.nil_append, List.cons.injEq] at h'
          rcases h' with ⟨_, hn, _, _, hw, _, _, hp, _, _, ht, _, _, _, htail⟩
          have hnv : name1.val = name2.val := by simpa only [Token.word.injEq] using hn
          have hwv : decl1.widthBits = decl2.widthBits := by
            simpa only [Token.natural.injEq] using hw
          have hpv : decl1.privilege = decl2.privilege := execPrivilegeKeyword_inj hp
          have htv : decl1.translation = decl2.translation := execTranslationKeyword_inj ht
          have hgv : decl1.guards = decl2.guards :=
            execGuardsTokens_inj (List.append_cancel_right htail)
          have hname : name1 = name2 := Subtype.ext hnv
          subst name2
          cases decl1 with
          | mk w1 p1 t1 g1 =>
              cases decl2 with
              | mk w2 p2 t2 g2 =>
                  change w1 = w2 at hwv
                  change p1 = p2 at hpv
                  change t1 = t2 at htv
                  change g1 = g2 at hgv
                  subst w2
                  subst p2
                  subst t2
                  subst g2
                  rfl

private def execStateDeclSyntax : Gabbro.Core.Text.Syntax (ExecTree .stateDecl) where
  reads := fun tokens tree => tree.production tokens
  unique := by
    intro tokens a b ha hb
    exact execEindeutig_stateDecl a b tokens ha hb
  printPieces := ExecTree.printPieces
  reads_print := by
    intro tree
    cases tree with
    | stateDecl name decl => exact execStateDeclPrints name decl

private theorem execParse_stateDecl : ExecParseAussage .stateDecl := by
  intro text tree
  change Gabbro.Core.Text.Parse execStateDeclSyntax.grammar text tree ↔
    ∃ pieces, Lexed text pieces ∧ tree.production (canonicalTokens pieces)
  exact execStateDeclSyntax.parse_iff

private theorem execInversion_stateDecl : ExecInversionAussage .stateDecl := by
  intro tree tokens prod
  obtain ⟨pieces, lex, aligned⟩ := PrintedToken.renderLexed 0 (ExecTree.printPieces tree)
  refine ⟨pieces, lex, ?_⟩
  cases tree with
  | stateDecl name decl =>
      have prints := execStateDeclPrints name decl
      simp only [ExecTree.production] at prod prints
      rw [← prints] at prod
      exact aligned.trans prod.symm

private theorem execDruck_stateDecl : ExecDruckAussage .stateDecl := by
  intro tree
  constructor
  · cases tree with
    | stateDecl name decl => exact execStateDeclPrints name decl
  · change Gabbro.Core.Text.Parse execStateDeclSyntax.grammar (execStateDeclSyntax.print tree) tree
    exact execStateDeclSyntax.parse_print tree

private theorem execStateDeclMeaning : StateDeclMeaningAussage := by
  intro decl s c frame heval
  by_cases hwf : decl.wellformed
  · simp only [ExecInstruction.evaluate] at heval
    dsimp at heval
    rw [if_pos hwf] at heval
    cases heval
    simp only [ExecFrame.declare, true_and]
    rfl
  · simp only [ExecInstruction.evaluate] at heval
    dsimp at heval
    rw [if_neg hwf] at heval
    cases heval

private theorem imageGueltigX86 : image.gueltig (Plattform.x86_64).ziel := by
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

private theorem execZulStart {k : Katalog} {h : Katalog.Umgebung} {regions : List Strecke}
    (hw : Hardware k h) (img : image.gueltig k.plattform.ziel)
    (pairwise : regions.Pairwise Strecke.getrennt)
    (ok : ∀ r ∈ regions, r.von < r.bis ∧ r.bis ≤ 2 ^ k.plattform.ziel.physicalBits ∧
      ∀ e d, k.plattform.geraet e = some d → d.bus = .mmio → r.getrennt d.window) :
    Katalog.ZulStart k h image
      ⟨0, (fun i => if i = 0 then some 0 else none), regions, (fun _ => none),
        h.politik.sicht 0 []⟩ := by
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

private theorem execKlauseln (k : Katalog) (code : List ExecInstruction) :
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

private theorem execWaechter (k : Katalog) (code : List ExecInstruction) :
    WaechterHalten (execProgram k code) := by
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

private theorem execAussenLokalProgram (k : Katalog) (code : List ExecInstruction) :
    Gabbro.Core.Annahme.AussenLokal (execProgram k code) := by
  refine ⟨zulassung_m2 _, ?_⟩
  apply aussen_gueltig_aus_kontext
  intro run t s c w spur s' step
  cases step with
  | kontext _ _ regel execute =>
    obtain ⟨_, _, frame, _, planEq, rfl⟩ := regel
    cases (List.cons.inj planEq).1
    obtain ⟨rfl, rfl⟩ := execGenauInternal execute
    exact ⟨⟨fun _ mem => (List.not_mem_nil mem).elim, [],
      (List.append_nil _).symm, fun _ mem => (List.not_mem_nil mem).elim⟩, fun h => h⟩

private theorem execAkzeptiert (k : Katalog) (code : List ExecInstruction)
    (wf : KatalogWohlgeformt k) : Annahme.Akzeptiert (execProgram k code) := by
  refine ⟨⟨wf, ?_, ?_, execProgramFlussLokal k code, ?_⟩, execKlauseln k code, execWaechter k code⟩
  · intro i
    exact execRegelLokal k i
  · exact execAussenLokalProgram k code
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro η lauf
      exact ⟨stapelZustand_leer rfl _, speicherZustand_leer rfl _⟩
    · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      exact ⟨stapelZustand_leer rfl _, speicherZustand_leer rfl _⟩
    · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _
      exact ⟨stapelZustand_leer rfl _, speicherZustand_leer rfl _⟩
    · exact tiefenBezug_eq rfl

private def execStateName : Identifier :=
  ⟨['s'], ⟨'s', [], rfl, by
    unfold isNameStart isLetter
    left
    left
    constructor <;> decide, by
      intro a h
      cases h⟩⟩

private theorem execStateDeclErfuellbar : ExecErfuellbarAussage .stateDecl := by
  let k : Katalog := Plattform.x86_64.katalog
  let decl : ExecStateDecl := ⟨64, .kernel, .on, []⟩
  let scope : ExecScope := ⟨[execStateName], [], [], [], []⟩
  let tree : ExecTree .stateDecl := .stateDecl execStateName decl
  let op : ExecInstruction := .declareState decl
  let sicht : Nat → AussenVerlauf → AussenSicht := fun _ _ => AussenSicht.leer
  let env : Katalog.Umgebung := Katalog.Umgebung.referenz k 1 sicht
  let start : AussenStart :=
    ⟨0, (fun i => if i = 0 then some 0 else none), [], (fun _ => none), env.politik.sicht 0 []⟩
  let E : ExecUnit := execProgram k [op]
  let text : RawText := tree.print
  let s : ExecState := (I.start E start).2
  let next : ExecFrame := (s.lokal entryContext).declare decl
  have wf : KatalogWohlgeformt k := by simpa [k] using Plattform.katalog_wohlgeformt .x86_64
  have hardware : Hardware k env := by
    apply Katalog.Umgebung.referenz_hardware k 1 sicht
    · exact wf
    · omega
  have admitted : E.ZulStart env start := by
    apply execZulStart (k := k) (h := env) (regions := [])
    · exact hardware
    · simpa [k, Plattform.katalog] using imageGueltigX86
    · exact List.Pairwise.nil
    · intro r hr
      cases hr
  have accepted : Annahme.Akzeptiert E := execAkzeptiert k [op] wf
  have hdeclWF : decl.wellformed := by decide
  have hElab : elaborateExec scope tree = some op := by
    simp only [tree, op, elaborateExec, hdeclWF, ↓reduceIte]
  have hParse : ExecParse text tree := by
    change Gabbro.Core.Text.Parse execStateDeclSyntax.grammar (execStateDeclSyntax.print tree) tree
    exact execStateDeclSyntax.parse_print tree
  have heval : op.evaluate s entryContext = some next := by
    simp only [op, ExecInstruction.evaluate]
    dsimp
    rw [if_pos hdeclWF]
  have hstatus : s.status entryContext = .laeuft := by rfl
  have hpc : (s.lokal entryContext).pc = 0 := by rfl
  have hhead : E.system.kopf s entryContext = some op := by
    change execHead [op] s entryContext = some op
    exact (execHead_some_iff op s entryContext).2 ⟨hstatus, rfl, hpc, by rw [heval]; rfl⟩
  have hreach : E.system.IErreichbar (I.start E start).2 s := by
    change E.system.IErreichbar s s
    exact System.IErreichbar.start
  have hstep : E.system.ISchritt entryContext s () [plan] (next.advance entryContext s) := by
    refine ⟨op, hhead, ?_⟩
    exact ⟨next, heval, rfl, rfl⟩
  have himpl : E.system.ImplSchritt entryContext s () [plan] (next.advance entryContext s) := by
    refine ⟨op, hhead, ?_⟩
    exact ⟨next, heval, rfl, rfl⟩
  have hnodupStates : (scope.states.map Subtype.val).Nodup := by
    dsimp [scope]
    exact List.nodup_singleton _
  have hnodupSpaces : (scope.spaces.map Subtype.val).Nodup := by
    dsimp [scope]
    exact List.nodup_nil
  have hnodupStapel : (scope.stapel.map Subtype.val).Nodup := by
    dsimp [scope]
    exact List.nodup_nil
  have hnodupEntries : (scope.entries.map Subtype.val).Nodup := by
    dsimp [scope]
    exact List.nodup_nil
  refine ⟨k, scope, tree, op, env, start, text, [], s, next, ?_⟩
  exact ⟨True.intro, hardware, admitted, accepted, hnodupStates, hnodupSpaces, hnodupStapel,
    hnodupEntries, ⟨tree, hParse, ⟨op, hElab, rfl⟩⟩, hParse, hElab, hreach, hhead, heval,
    hstep, himpl⟩

theorem stateDecl_aussage : StateDeclAussage := by
  refine ⟨?kern, execStateDeclMeaning, execStateDeclErfuellbar⟩
  unfold execObligationsKern
  exact ⟨execParse_stateDecl, execInversion_stateDecl, execEindeutig_stateDecl,
    execDruck_stateDecl, execElaboriert .stateDecl, execRealisiert .stateDecl,
    execAnnahme .stateDecl, execIdeal .stateDecl, execEinheit .stateDecl,
    execImpl .stateDecl, execFortschritt .stateDecl, execErhaltung .stateDecl,
    execSicher .stateDecl, execRegelAntwortSicher .stateDecl, execAussen .stateDecl,
    execKosten .stateDecl, execSchranken, execEtiketten, execFluss⟩

end Gabbro.Core.Ast.LowLevel
