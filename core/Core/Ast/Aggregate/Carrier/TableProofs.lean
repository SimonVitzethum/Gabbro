module

public import Core.Ast.Aggregate.Carrier.Table
public import Core.Ast.Semantik.Formbeweise

/-!
# Table

Prove the pinned statements in this file.
-/

@[expose] public section

open Gabbro.Core.Text

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Gabbro.Core.Text

private theorem printPubVal : printPub.value = keyword "pub" := by decide
private theorem printTableVal : printTable.value = keyword "table" := by decide
private theorem printCountVal : printCount.value = keyword "count" := by decide
private theorem printSlotVal : printSlot.value = keyword "slot" := by decide
private theorem printEffectsVal : printEffects.value = keyword "effects" := by decide
private theorem printOpenBraceVal : printOpenBrace.value = openBrace := by decide
private theorem printCloseBraceVal : printCloseBrace.value = closeBrace := by decide
private theorem printColonVal : printColon.value = colon := by decide
private theorem printCommaVal : printComma.value = comma := by decide
private theorem printIntegerVal (n : Nat) : (printInteger n).value = .natural n := by rfl
private theorem identifierPrintVal (i : Identifier) : (Identifier.print i).value = .word i.val := by rfl

private theorem tableHeaderValue {scope : Scope} (item : TableDeclaration scope) :
    item.header.map PrintedToken.value =
      (if item.exported then [keyword "pub"] else []) ++
        [keyword "table", .word item.name.val, keyword "count", .natural item.count,
          openBrace, keyword "slot", openBrace] := by
  cases h : item.exported <;>
    simp only [TableDeclaration.header, h, List.map_append, List.map_cons, List.map_nil,
      printPubVal, printTableVal, identifierPrintVal, printCountVal, printIntegerVal,
      printOpenBraceVal, printSlotVal]

private theorem effectGroupHeaderValue {scope : Scope} (item : EffectGroupDeclaration scope) :
    item.header.map PrintedToken.value =
      (if item.exported then [keyword "pub"] else []) ++
        [keyword "effects", .word item.name.val, openBrace] := by
  cases h : item.exported <;>
    simp only [EffectGroupDeclaration.header, h, List.map_append, List.map_cons, List.map_nil,
      printPubVal, printEffectsVal, identifierPrintVal, printOpenBraceVal]

private theorem tableTok_ne_const : keyword "table" ≠ keyword "const" := by decide
private theorem pubTok_ne_const : keyword "pub" ≠ keyword "const" := by decide
private theorem tableTok_ne_fn : keyword "table" ≠ keyword "fn" := by decide
private theorem pubTok_ne_fn : keyword "pub" ≠ keyword "fn" := by decide
private theorem tableTok_ne_type : keyword "table" ≠ keyword "type" := by decide
private theorem pubTok_ne_type : keyword "pub" ≠ keyword "type" := by decide
private theorem tableTok_ne_tagged : keyword "table" ≠ keyword "tagged" := by decide
private theorem pubTok_ne_tagged : keyword "pub" ≠ keyword "tagged" := by decide
private theorem tableTok_ne_effects : keyword "table" ≠ keyword "effects" := by decide
private theorem pubTok_ne_effects : keyword "pub" ≠ keyword "effects" := by decide
private theorem tableTok_ne_pub : keyword "table" ≠ keyword "pub" := by decide

private theorem tableHeaderPrefix_eq {scope : Scope} (head item : TableDeclaration scope)
    (input input' : List Token)
    (h : head.header.map PrintedToken.value ++ input = item.header.map PrintedToken.value ++ input') :
    head.exported = item.exported ∧ head.name.val = item.name.val ∧
      head.count = item.count ∧ input = input' := by
  rw [tableHeaderValue head, tableHeaderValue item] at h
  cases he : head.exported <;> cases ie : item.exported <;>
    simp only [he, ie, List.nil_append, List.cons_append] at h
  · have h1 := (List.cons.inj h).2
    have hnameTok : Token.word head.name.val = Token.word item.name.val := (List.cons.inj h1).1
    have h2 := (List.cons.inj h1).2
    have h3 := (List.cons.inj h2).2
    have hcountTok : Token.natural head.count = Token.natural item.count := (List.cons.inj h3).1
    have h4 := (List.cons.inj h3).2
    have h5 := (List.cons.inj h4).2
    have h6 := (List.cons.inj h5).2
    have hin : input = input' := (List.cons.inj h6).2
    injection hnameTok with hname
    injection hcountTok with hcount
    exact ⟨rfl, hname, hcount, hin⟩
  · exact (tableTok_ne_pub (List.cons.inj h).1).elim
  · exact (tableTok_ne_pub (List.cons.inj h).1.symm).elim
  · have h1 := (List.cons.inj h).2
    have hnameTok : Token.word head.name.val = Token.word item.name.val := (List.cons.inj h1).1
    have h2 := (List.cons.inj h1).2
    have h3 := (List.cons.inj h2).2
    have hcountTok : Token.natural head.count = Token.natural item.count := (List.cons.inj h3).1
    have h4 := (List.cons.inj h3).2
    have h5 := (List.cons.inj h4).2
    have h6 := (List.cons.inj h5).2
    have hin : input = input' := (List.cons.inj h6).2
    injection hnameTok with hname
    injection hcountTok with hcount
    exact ⟨rfl, hname, hcount, hin⟩

theorem tableInversion : TableInversionAussage := by
  intro scope input tree rest head read
  generalize htok : head.header.map PrintedToken.value ++ input = toks at read
  cases read with
  | constant name ordinary written valid value static fits typeRead exprRead =>
      cases ex : head.exported <;>
        simp only [tableHeaderValue, ex, List.nil_append, List.cons_append] at htok
      · exact (tableTok_ne_const (List.cons.inj htok).1).elim
      · exact (pubTok_ne_const (List.cons.inj htok).1).elim
  | function name ordinary result valid parameters measure body distinct returns effects
      paramsRead resultRead effectRead measureRead blockRead =>
      cases ex : head.exported <;>
        simp only [tableHeaderValue, ex, List.nil_append, List.cons_append] at htok
      · exact (tableTok_ne_fn (List.cons.inj htok).1).elim
      · exact (pubTok_ne_fn (List.cons.inj htok).1).elim
  | record exported name valid distinct memberRead =>
      cases exported <;> cases ex : head.exported <;>
        simp only [tableHeaderValue, ex, recordDeclarationPrefix, List.nil_append, List.cons_append] at htok
      · exact (tableTok_ne_type (List.cons.inj htok).1).elim
      · exact (pubTok_ne_type (List.cons.inj htok).1).elim
      · exact (tableTok_ne_pub (List.cons.inj htok).1).elim
      · exact (tableTok_ne_type (List.cons.inj ((List.cons.inj htok).2)).1).elim
  | tagged exported name valid distinct firstRead tailRead =>
      cases exported <;> cases ex : head.exported <;>
        simp only [tableHeaderValue, ex, taggedDeclarationPrefix, List.nil_append, List.cons_append] at htok
      · exact (tableTok_ne_tagged (List.cons.inj htok).1).elim
      · exact (pubTok_ne_tagged (List.cons.inj htok).1).elim
      · exact (tableTok_ne_pub (List.cons.inj htok).1).elim
      · exact (tableTok_ne_tagged (List.cons.inj ((List.cons.inj htok).2)).1).elim
  | table item fieldRead =>
      rcases tableHeaderPrefix_eq head item input _ htok with ⟨hexp, hnameVal, hcount, hin⟩
      rw [← hin] at fieldRead
      exact ⟨item, (Subtype.ext hnameVal).symm, hcount.symm, hexp.symm, fieldRead, rfl⟩
  | effectGroup item effectRead =>
      cases hie : item.exported <;> cases ex : head.exported <;>
        simp only [tableHeaderValue, effectGroupHeaderValue, hie, ex, List.nil_append,
          List.cons_append] at htok
      · exact (tableTok_ne_effects (List.cons.inj htok).1).elim
      · exact (pubTok_ne_effects (List.cons.inj htok).1).elim
      · exact (tableTok_ne_pub (List.cons.inj htok).1).elim
      · exact (tableTok_ne_effects (List.cons.inj ((List.cons.inj htok).2)).1).elim

private def tableFieldTokenList : List RecordMember → List Token
  | [] => []
  | m :: ms => m.name.print.value :: colon :: m.written.printPieces.map PrintedToken.value ++
      comma :: tableFieldTokenList ms

private theorem tableFields_print_reads (scope : Scope) (name : Identifier) (count : Nat)
    (fields : List RecordMember)
    (valid : ∀ m ∈ fields, m.written.valid (carrierFieldScope scope name count)) :
    TableFieldsRead (carrierFieldScope scope name count)
      (tableFieldTokenList fields ++ [closeBrace, closeBrace]) fields [closeBrace] := by
  induction fields with
  | nil => exact TableFieldsRead.close
  | cons m ms ih =>
      simpa only [tableFieldTokenList, List.append_assoc] using
        (TableFieldsRead.next m.name
          (WrittenType.printReads m.written (valid m (by simp)) (by intro more same; cases same))
          (ih (fun x hx => valid x (by simp [hx]))))

private theorem tablePrints (scope : Scope) (item : TableDeclaration scope) :
    (tableForm scope).produktion item
      (((Category.declaration scope).printPieces ((tableForm scope).produktion.tree item)).map
        PrintedToken.value) := by
  refine ⟨(item.fields.flatMap RecordMember.printPieces ++ [printCloseBrace, printCloseBrace]).map
    PrintedToken.value, ?_, ?_⟩
  · simp only [Category.printPieces, Decl.printPieces, List.map_append]
  · have hmap : (item.fields.flatMap RecordMember.printPieces).map PrintedToken.value =
        tableFieldTokenList item.fields := by
      induction item.fields with
      | nil => rfl
      | cons m ms ih =>
          simp only [List.flatMap_cons, List.map_append, List.map_cons, List.map_nil,
            RecordMember.printPieces, tableFieldTokenList, printColonVal, printCommaVal, ih]
    rw [hmap]
    simpa only [List.map_append, List.map_cons, List.map_nil, printCloseBraceVal] using
      (tableFields_print_reads scope item.name item.count item.fields item.valid)

theorem tableDerivation : TableDerivationAussage := by
  intro scope
  exact {
    reads := by
      intro item tokens prod
      rcases prod with ⟨input, rfl, fieldRead⟩
      exact DeclReads.table item fieldRead
    prints := tablePrints scope
    erfuellbar := by
      intro item
      exact Surface.Rule.satisfiableOfPrint item (tablePrints scope item)
  }

theorem tableScope : TableScopeAussage := by
  intro scope item
  constructor
  · simp [Scope.carrierCount, TableDeclaration.binding, carrierBinding]
  constructor
  · intro other hne
    have hne' : item.name.val ≠ other.val := fun h => hne h.symm
    simp [Scope.carrierCount, TableDeclaration.binding, carrierBinding, hne']
  · intro h
    cases h

theorem tableBinding : TableBindingAussage := by
  intro scope item frame
  simp [tableInstruction, Befehl.auswerten, Rahmen.installSchema, TableDeclaration.binding,
    carrierBinding]

theorem tableParse : TableParseAussage := by
  intro scope item text pieces lexed prod
  exact (tableDerivation scope).parse lexed prod

theorem tableElaboriert : TableElaboriertAussage := by
  intro scope item
  rfl

private theorem table_amOrt (scope : Scope) : (tableForm scope).RegelAmOrt := by
  intro item
  rfl

theorem tableRealisiert : TableRealisiertAussage := by
  intro scope item platform s running active live atPc
  exact (tableForm scope).realisiert (table_amOrt scope) platform item s running active live atPc

theorem tableAnnahme : TableAnnahmeAussage := by
  intro scope
  exact Quellform.annahme (tableForm scope)

theorem tableIdeal : TableIdealAussage := by
  intro scope
  refine ⟨table_amOrt scope, ?_⟩
  intro item
  refine ⟨((tableForm scope).befehl item).bestimmt, ?_⟩
  intro c s w plans u
  rfl

theorem tableEinheit : TableEinheitAussage := by
  intro scope platform item
  exact ⟨rfl, ((tableForm scope).befehl item).kommutation⟩

theorem tableImpl : TableImplAussage := by
  intro scope item c s w plans u
  rfl

theorem tableErhaltung : TableErhaltungAussage := by
  intro scope
  exact Quellform.erhaltung (tableForm scope) (fun _ => rfl)

theorem tableRegelSicher : TableRegelSicherAussage := by
  intro scope platform item
  exact (tableErhaltung scope platform item).2.2.2

theorem tableErfuellbarAm : TableErfuellbarAmAussage := by
  intro platform start
  let carrier : Identifier := keywordName 'c' [] (by decide) (fun _ m => (List.not_mem_nil m).elim)
  let pname : Identifier := keywordName 'p' [] (by decide) (fun _ m => (List.not_mem_nil m).elim)
  let qname : Identifier := keywordName 'q' [] (by decide) (fun _ m => (List.not_mem_nil m).elim)
  let fname : Identifier := keywordName 'f' [] (by decide) (fun _ m => (List.not_mem_nil m).elim)
  let item : TableDeclaration [] := {
    exported := false
    name := carrier
    count := 1
    fields := []
    valid := fun f h => (List.not_mem_nil h).elim
    distinct := by decide
  }
  let scope : Scope := [item.binding]
  have resolved : scope.carrierCount carrier = some 1 := by
    decide
  have pOrdinary : ordinaryLocal pname := by
    dsimp [ordinaryLocal, ordinaryAtomWord, pname]
    decide
  have qOrdinary : ordinaryLocal qname := by
    dsimp [ordinaryLocal, ordinaryAtomWord, qname]
    decide
  let paramIndex : Parameter scope := ⟨pname, .index carrier 1, resolved, pOrdinary⟩
  let paramOption : Parameter scope := ⟨qname, .indexOption carrier 1, resolved, qOrdinary⟩
  have fnOrdinary : directName fname := by
    constructor
    · dsimp [ordinaryLocal, ordinaryAtomWord, fname]
      decide
    · dsimp [fname]
      simp
  have validNone : ∀ t ∈ (none : Option WrittenType).toList, WrittenType.valid scope t := by
    intro t h
    cases h
  let argsVal : Surface.FunctionArgs scope := {
    name := fname
    ordinary := fnOrdinary
    parameters := [paramIndex, paramOption]
    result := none
    valid := validNone
    measure := none
    body := .braces .done
    distinct := by decide
    returns := by
      intro h
      cases h
  }
  let rest : UnitBody [item.binding] scope := .step argsVal.declaration .done
  let tree : Ast.Unit := ⟨scope, .step (.table item) rest⟩
  let E := elaborieren (category := .unit) platform tree
  let s := (I.start E start).2
  refine ⟨item, scope, rest, Ast.print (category := .unit) tree, s, ?_⟩
  dsimp only
  refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨argsVal, .done, rfl, ?_, ?_⟩
    · exact ⟨paramIndex, by simp, rfl⟩
    · exact ⟨paramOption, by simp, rfl⟩
  · exact Ast.parse_print (category := .unit) tree
  · rfl
  · exact .start
  · rfl
  · exact ⟨tableInstruction item, rfl, rfl, rfl⟩
  · exact ⟨tableInstruction item, rfl, rfl, rfl⟩

end Gabbro.Core.Ast.Semantik
