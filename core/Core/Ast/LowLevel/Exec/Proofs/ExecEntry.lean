module

public import Core.Ast.LowLevel.Exec.Registry
public import Core.Ast.LowLevel.Exec.Proofs.ExecKern

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Gabbro.Core.Text Katalog Maschine Waechter
open Gabbro.Core.Annahme
open Gabbro.Core.Aussen
open Gabbro.Core.Sicherheit (Absturz NeueWirkungen)

private def entryKeywordFirst (t : Token) : Nat :=
  match t with
  | .word (c :: _) => c.toNat
  | _ => 0

private def entryKindFirst : EntryKind → Nat
  | .interrupt => 'i'.toNat
  | .exception => 'e'.toNat
  | .nonmaskable => 'n'.toNat
  | .machineCheck => 'm'.toNat
  | .fatal => 'f'.toNat

private theorem entryKeywordFirst_kind (k : EntryKind) :
    entryKeywordFirst (entryKindKeyword k) = entryKindFirst k := by
  cases k <;> rfl

private theorem entryKindKeyword_inj {k₁ k₂ : EntryKind}
    (h : entryKindKeyword k₁ = entryKindKeyword k₂) : k₁ = k₂ := by
  have hf : entryKindFirst k₁ = entryKindFirst k₂ := by
    rw [← entryKeywordFirst_kind k₁, ← entryKeywordFirst_kind k₂]
    exact congrArg entryKeywordFirst h
  cases k₁ <;> cases k₂ <;> simp only [entryKindFirst, Char.reduceToNat] at hf ⊢ <;> omega

private theorem entryPrints_none (name : Identifier) (kind : EntryKind) (stack : EntryStack) :
    (ExecTree.entryDecl name kind stack none).production
      ((ExecTree.entryDecl name kind stack none).printPieces.map PrintedToken.value) := by
  left
  constructor
  · rfl
  · cases kind <;> cases stack <;> rfl

private theorem entryPrints_some (name : Identifier) (kind : EntryKind) (stack : EntryStack) (n : Nat) :
    (ExecTree.entryDecl name kind stack (some n)).production
      ((ExecTree.entryDecl name kind stack (some n)).printPieces.map PrintedToken.value) := by
  right
  refine ⟨n, rfl, ?_⟩
  cases kind <;> cases stack <;> rfl

private theorem entryPrints (tree : ExecTree .entryDecl) :
    tree.production (tree.printPieces.map PrintedToken.value) := by
  cases tree with
  | entryDecl name kind stack priority =>
      cases priority
      · exact entryPrints_none name kind stack
      · exact entryPrints_some name kind stack _

private theorem entryEindeutig : ExecEindeutigAussage .entryDecl := by
  intro a b tokens ha hb
  cases a with
  | entryDecl na ka sa pa =>
      cases b with
      | entryDecl nb kb sb pb =>
          cases pa with
          | none =>
              cases pb with
              | none =>
                  simp only [ExecTree.production] at ha hb
                  rcases ha with ⟨_, ha'⟩ | ⟨_, hn, _⟩
                  · rcases hb with ⟨_, hb'⟩ | ⟨_, hn', _⟩
                    · have htokEq := ha'.symm.trans hb'
                      have hval : na.val = nb.val := by
                        have h := congrArg (fun l : List Token => l[1]?) htokEq
                        change some (Token.word na.val) = some (Token.word nb.val) at h
                        have hword : Token.word na.val = Token.word nb.val := by
                          injection h with hword
                        simpa only [Token.word.injEq] using hword
                      have hkTok : entryKindKeyword ka = entryKindKeyword kb := by
                        have h := congrArg (fun l : List Token => l[2]?) htokEq
                        change some (entryKindKeyword ka) = some (entryKindKeyword kb) at h
                        injection h with hkw
                      have hk : ka = kb := entryKindKeyword_inj hkTok
                      have hna : na = nb := Subtype.ext hval
                      cases sa <;> cases sb
                      · subst nb
                        subst kb
                        rfl
                      · have hs := congrArg (fun l : List Token => l[4]?) htokEq
                        simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
                          Option.some.injEq, keyword, String.reduceToList, Token.word.injEq,
                          List.cons.injEq, Char.reduceEq, Bool.false_eq_true] at hs
                        cases hs
                      · have hs := congrArg (fun l : List Token => l[4]?) htokEq
                        simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
                          Option.some.injEq, keyword, String.reduceToList, Token.word.injEq,
                          List.cons.injEq, Char.reduceEq, Bool.false_eq_true] at hs
                        cases hs
                      · subst nb
                        subst kb
                        rfl
                    · cases hn'
                  · cases hn
              | some nB =>
                  simp only [ExecTree.production] at ha hb
                  rcases ha with ⟨_, ha'⟩ | ⟨_, hn, _⟩
                  · rcases hb with ⟨hnone', _⟩ | ⟨m, hm, hb'⟩
                    · cases hnone'
                    · cases hm
                      have hlen := congrArg List.length (ha'.symm.trans hb')
                      cases sa <;> cases sb <;>
                        simp only [List.length_append, List.length_cons, List.length_nil] at hlen <;>
                        omega
                  · cases hn
          | some nA =>
              cases pb with
              | none =>
                  simp only [ExecTree.production] at ha hb
                  rcases ha with ⟨hnone, _⟩ | ⟨m, hm, ha'⟩
                  · cases hnone
                  · rcases hb with ⟨_, hb'⟩ | ⟨_, hn', _⟩
                    · cases hm
                      have hlen := congrArg List.length (ha'.symm.trans hb')
                      cases sa <;> cases sb <;>
                        simp only [List.length_append, List.length_cons, List.length_nil] at hlen <;>
                        omega
                    · cases hn'
              | some nB =>
                  simp only [ExecTree.production] at ha hb
                  rcases ha with ⟨hnone, _⟩ | ⟨m₁, hm₁, ha'⟩
                  · cases hnone
                  · rcases hb with ⟨hnone', _⟩ | ⟨m₂, hm₂, hb'⟩
                    · cases hnone'
                    · cases hm₁
                      cases hm₂
                      have htokEq := ha'.symm.trans hb'
                      have hval : na.val = nb.val := by
                        have h := congrArg (fun l : List Token => l[1]?) htokEq
                        change some (Token.word na.val) = some (Token.word nb.val) at h
                        have hword : Token.word na.val = Token.word nb.val := by
                          injection h with hword
                        simpa only [Token.word.injEq] using hword
                      have hkTok : entryKindKeyword ka = entryKindKeyword kb := by
                        have h := congrArg (fun l : List Token => l[2]?) htokEq
                        change some (entryKindKeyword ka) = some (entryKindKeyword kb) at h
                        injection h with hkw
                      have hk : ka = kb := entryKindKeyword_inj hkTok
                      have hna : na = nb := Subtype.ext hval
                      cases sa <;> cases sb
                      · have hn : nA = nB := by
                          have h := congrArg (fun l : List Token => l[7]?) htokEq
                          change some (Token.natural nA) = some (Token.natural nB) at h
                          injection h with hn'
                          simpa using hn'
                        subst nB
                        subst nb
                        subst kb
                        rfl
                      · have hs := congrArg (fun l : List Token => l[4]?) htokEq
                        simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
                          Option.some.injEq, keyword, String.reduceToList, Token.word.injEq,
                          List.cons.injEq, Char.reduceEq, Bool.false_eq_true] at hs
                        cases hs
                      · have hs := congrArg (fun l : List Token => l[4]?) htokEq
                        simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
                          Option.some.injEq, keyword, String.reduceToList, Token.word.injEq,
                          List.cons.injEq, Char.reduceEq, Bool.false_eq_true] at hs
                        cases hs
                      · have hn : nA = nB := by
                          have h := congrArg (fun l : List Token => l[6]?) htokEq
                          change some (Token.natural nA) = some (Token.natural nB) at h
                          injection h with hn'
                          simpa using hn'
                        subst nB
                        subst nb
                        subst kb
                        rfl

private def entrySyntax : Gabbro.Core.Text.Syntax (ExecTree .entryDecl) where
  reads := fun tokens tree => tree.production tokens
  unique := by
    intro tokens a b ha hb
    exact entryEindeutig a b tokens ha hb
  printPieces := ExecTree.printPieces
  reads_print := entryPrints

private theorem entryParse : ExecParseAussage .entryDecl := by
  intro text tree
  change Gabbro.Core.Text.Parse entrySyntax.grammar text tree ↔
    ∃ pieces, Lexed text pieces ∧ tree.production (canonicalTokens pieces)
  exact entrySyntax.parse_iff

private theorem entryProduction_unique (tree : ExecTree .entryDecl) {t₁ t₂ : List Token}
    (h₁ : tree.production t₁) (h₂ : tree.production t₂) : t₁ = t₂ := by
  cases tree with
  | entryDecl name kind stack priority =>
      cases priority with
      | none =>
          simp only [ExecTree.production] at h₁ h₂
          rcases h₁ with ⟨_, ht₁⟩ | ⟨_, hn, _⟩
          · rcases h₂ with ⟨_, ht₂⟩ | ⟨_, hn', _⟩
            · rw [ht₁, ht₂]
            · cases hn'
          · cases hn
      | some n =>
          simp only [ExecTree.production] at h₁ h₂
          rcases h₁ with ⟨hnone, _⟩ | ⟨m₁, hm₁, ht₁⟩
          · cases hnone
          · rcases h₂ with ⟨hnone', _⟩ | ⟨m₂, hm₂, ht₂⟩
            · cases hnone'
            · cases hm₁
              cases hm₂
              rw [ht₁, ht₂]

private theorem entryInversion : ExecInversionAussage .entryDecl := by
  intro tree tokens prod
  obtain ⟨pieces, lex, aligned⟩ :=
    PrintedToken.renderLexed 0 (ExecTree.printPieces tree)
  refine ⟨pieces, lex, ?_⟩
  exact aligned.trans (entryProduction_unique tree (entryPrints tree) prod)

private theorem entryDruck : ExecDruckAussage .entryDecl := by
  intro tree
  constructor
  · exact entryPrints tree
  · change Gabbro.Core.Text.Parse entrySyntax.grammar (entrySyntax.print tree) tree
    exact entrySyntax.parse_print tree

private theorem entryMeaning : EntryMeaningAussage := by
  intro name kind stack priority s c resultFrame h
  simp only [ExecInstruction.evaluate] at h
  dsimp at h
  split at h
  · rename_i hcond
    cases h
    exact ⟨hcond.1, hcond.2.1, hcond.2.2, rfl, rfl⟩
  · cases h

private theorem entryImageGueltigX86 : image.gueltig (Plattform.x86_64).ziel := by
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

private theorem entryZulStart {k : Katalog} {h : Katalog.Umgebung}
    (hw : Hardware k h) (img : image.gueltig k.plattform.ziel) :
    Katalog.ZulStart k h image
      ⟨0, (fun i => if i = 0 then some 0 else none), [], (fun _ => none),
        h.politik.sicht 0 []⟩ := by
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

private theorem entryUnitAkzeptiert (k : Katalog) (op : ExecInstruction)
    (hwf : KatalogWohlgeformt k) : Annahme.Akzeptiert (execUnit k op) := by
  refine ⟨⟨hwf, ?_, execAussenLokalUnit k op, execFlussLokal k op, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i
    exact execRegelLokal k i
  · exact schrankenLokal_leer rfl rfl rfl
  · exact Gabbro.Core.Annahme.abschnittWartefrei_ohne_blockade _ fun _ _ _ hb => hb
  · exact execDomaenenLokal _ _
  · intro ρ runs
    dsimp [kanonischeKlauseln, execUnit, execProgram, Quelltabellen.leer, Quellklauseln.leer]
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      cases hp
    · intro t p hp
      cases hp
    · intro t done p hp
      cases hp
  · refine ⟨?_, ?_, ?_⟩
    · intro ρ runs t o args bedarf
      dsimp [kanonischeVerwendung, execUnit, execProgram, Quelltabellen.leer] at bedarf
      cases bedarf
    · intro ρ runs t
      rintro ⟨C, nonempty, blocked⟩
      obtain ⟨c, hc⟩ := nonempty
      obtain ⟨b, hblock, _, _, _⟩ := blocked c hc
      exact hblock
    · intro ρ runs t l h _ hne
      exact (hne rfl).elim

private def entryName : Identifier :=
  ⟨['e'], ⟨'e', [], rfl, by
    unfold isNameStart isLetter
    left
    left
    constructor <;> decide, by
      intro a h
      cases h⟩⟩

private theorem entryName_slot :
    List.idxOf? entryName.val [entryName.val] = some 0 := by
  simp only [List.idxOf?_cons, beq_self_eq_true, if_true]

private theorem entry_erfuellbar : ExecErfuellbarAussage .entryDecl := by
  let k : Katalog := Plattform.x86_64.katalog
  let sicht : Nat → AussenVerlauf → AussenSicht := fun _ _ => AussenSicht.leer
  let env : Katalog.Umgebung := Katalog.Umgebung.referenz k 1 sicht
  let scope : ExecScope := ⟨[entryName], [], [], [], [entryName]⟩
  let tree : ExecTree .entryDecl := .entryDecl entryName .exception .perCore none
  let op : ExecInstruction := .declareEntry entryName .exception .perCore none
  let start : AussenStart :=
    ⟨0, (fun i => if i = 0 then some 0 else none), [], (fun _ => none), env.politik.sicht 0 []⟩
  let «prefix» : List ExecInstruction := []
  let E : ExecUnit := execProgram k («prefix» ++ [op])
  let text : RawText := tree.print
  let s : ExecState := (I.start E start).2
  let next : ExecFrame := { s.lokal entryContext with
    result := some (.entryDeclared entryName)
    entries := (s.lokal entryContext).entries ++ [(entryName, .exception)] }
  have hardware : Hardware k env := by
    apply Katalog.Umgebung.referenz_hardware k 1 sicht
    · simpa [k] using Plattform.katalog_wohlgeformt .x86_64
    · omega
  have admitted : E.ZulStart env start := by
    change Katalog.ZulStart k env image start
    exact entryZulStart (k := k) (h := env) hardware entryImageGueltigX86
  have accepted : Annahme.Akzeptiert E := by
    change Annahme.Akzeptiert (execUnit k op)
    exact entryUnitAkzeptiert k op (by simpa [k] using Plattform.katalog_wohlgeformt .x86_64)
  have hElab : elaborateExec scope tree = some op := by
    change (List.idxOf? entryName.val [entryName.val]).map
        (fun _ => ExecInstruction.declareEntry entryName .exception .perCore none) =
      some (ExecInstruction.declareEntry entryName .exception .perCore none)
    rw [entryName_slot]
    rfl
  have hParse : ExecParse text tree := by
    change Gabbro.Core.Text.Parse entrySyntax.grammar (entrySyntax.print tree) tree
    exact entrySyntax.parse_print tree
  have hBez : BezeichnetExec k scope text (execUnit k op) .entryDecl := by
    refine ⟨tree, hParse, ?_⟩
    exact ⟨op, hElab, rfl⟩
  have hentries : (s.lokal entryContext).entries = [] := by
    rfl
  have hcond :
      (s.lokal entryContext).entries.all (fun p => p.1.val != entryName.val) = true ∧
      (EntryKind.needsOwnStack .exception = true → EntryStack.perCore = EntryStack.own) ∧
      (EntryKind.needsPriority .exception = true ↔ false = true) := by
    rw [hentries]
    constructor
    · rfl
    · constructor
      · intro hb
        cases hb
      · rfl
  have heval : op.evaluate s entryContext = some next := by
    simp only [op, ExecInstruction.evaluate]
    dsimp
    rw [if_pos hcond]
  have hhead : E.system.kopf s entryContext = some op := by
    change execHead [op] s entryContext = some op
    exact (execHead_some_iff op s entryContext).2 ⟨rfl, rfl, rfl, by rw [heval]; rfl⟩
  have hreach : E.system.IErreichbar (I.start E start).2 s := by
    change E.system.IErreichbar s s
    exact System.IErreichbar.start
  have hstep : E.system.ISchritt entryContext s () [plan] (next.advance entryContext s) := by
    refine ⟨op, hhead, ?_⟩
    exact ⟨next, heval, rfl, rfl⟩
  have himpl : E.system.ImplSchritt entryContext s () [plan] (next.advance entryContext s) := by
    refine ⟨op, hhead, ?_⟩
    exact ⟨next, heval, rfl, rfl⟩
  refine ⟨k, scope, tree, op, env, start, text, «prefix», s, next, ?_⟩
  exact ⟨True.intro, hardware, admitted, accepted,
    List.nodup_singleton _, List.nodup_nil, List.nodup_nil, List.nodup_singleton _,
    hBez, hParse, hElab, hreach, hhead, heval, hstep, himpl⟩

theorem entry_aussage : EntryAussage := by
  refine ⟨?kern, entryMeaning, entry_erfuellbar⟩
  unfold execObligationsKern
  exact ⟨entryParse, entryInversion, entryEindeutig, entryDruck,
    execElaboriert .entryDecl, execRealisiert .entryDecl, execAnnahme .entryDecl,
    execIdeal .entryDecl, execEinheit .entryDecl, execImpl .entryDecl,
    execFortschritt .entryDecl, execErhaltung .entryDecl, execSicher .entryDecl,
    execRegelAntwortSicher .entryDecl, execAussen .entryDecl, execKosten .entryDecl,
    execSchranken, execEtiketten, execFluss⟩

end Gabbro.Core.Ast.LowLevel
