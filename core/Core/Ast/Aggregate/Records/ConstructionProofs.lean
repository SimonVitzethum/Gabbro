module

public import Core.Ast.Aggregate.Records.Construction
public import Core.Ast.Semantik.Formbeweise
import Core.Ast.Semantik.Runtime.ExpressionAggregates

/-!
# RecordValue

- `Surface.RecordValueInversionAussage`
- `Surface.RecordValueSuffixAussage`
- `Surface.RecordValueDerivationAussage`
- `RecordValueParseAussage`
- `RecordValueElaboriertAussage`
- `RecordValueRealisiertAussage`
- `RecordValueAnnahmeAussage`
- `RecordValueIdealAussage`
- `RecordValueEinheitAussage`
- `RecordValueImplAussage`
- `RecordValueErhaltungAussage`
- `RecordValueRegelSicherAussage`
- `RecordValueErfuellbarAmAussage`
- `RecordValueSlotsAussage`
-/

namespace Gabbro.Core.Ast.Surface

open Gabbro.Core.Text

private theorem recordValue_reads (scope : Scope) (args : RecordValueArgs scope) {tokens : List Token}
    (prod : (recordValue scope).production args tokens) :
    (Category.expression scope).reads tokens ((recordValue scope).tree args) := by
  rcases prod with ⟨input, rfl, labelRead⟩
  change ExprReads scope 0 (.word args.ref.name.val :: openParen :: input)
    ((Surface.recordValue scope).tree args).2 []
  exact .atom (AtomReads.recordValue args.ref args.fields args.fits labelRead)
    (.stop noOperatorAtEnd)

public theorem RecordValueInversion : RecordValueInversionAussage := by
  intro scope labels types input type ref tree rest read
  generalize hword : Token.word ref.name.val = word at read
  generalize hinput : openParen :: input = tokens at read
  cases read with
  | trueLit => exact (ref.ordinary.1 (Token.word.inj hword)).elim
  | falseLit => exact (ref.ordinary.2.1 (Token.word.inj hword)).elim
  | textLength _ => exact (ref.ordinary.2.2.1 (Token.word.inj hword)).elim
  | «variable» localRef visible ordinary =>
    have same := Local.nameVisible_unique localRef ref.schema visible.2 ref.visible
      ((Token.word.inj hword).symm.trans ref.spelled.symm)
    exact (Eq.mp (congrArg Ty.valueBinding (congrArg Sigma.fst same)) visible.1 : False).elim
  | variantValue _ label _ _ _ available _ _ =>
    exact (available.2 _ ref.schema.binding_mem (ref.spelled.trans (Token.word.inj hword))).elim
  | recordValue actual fields fits labelRead =>
    cases hinput
    exact ⟨⟨_, _, actual, _, _, _, fields, fits⟩, Subtype.ext (Token.word.inj hword).symm, labelRead, rfl⟩
  | _ => cases hword

public theorem RecordValueSuffix : RecordValueSuffixAussage := by
  intro scope input labels types items rest read
  exact read.consumes

private theorem labeledPrintReads (items : LabeledItems scope labels types) (rest : List Token) :
    LabeledItemsRead scope (items.printPieces.map PrintedToken.value ++ closeParen :: rest) items rest ∧
    LabeledItemsTail scope (items.printTail.map PrintedToken.value ++ closeParen :: rest) items rest := by
  induction types generalizing labels with
  | nil =>
    cases items
    exact ⟨.close, .close⟩
  | cons type types ih =>
    cases items with
    | next label value tail =>
      let more := tail.printTail.map PrintedToken.value ++ closeParen :: rest
      have blocked : ¬ Continues 0 more := by
        cases tail with
        | empty => exact noOperatorAtClose
        | next _ _ _ => exact noOperatorAtComma
      have read := LabeledItemsRead.next label (value.printReads blocked) (ih tail).2
      refine ⟨?_, ?_⟩
      · simpa only [LabeledItems.printPieces, List.map_append, List.map_cons, List.map_nil,
          List.cons_append, List.nil_append, List.append_assoc, Expr.printTokens, more,
          show printColon.value = colon from rfl,
          show label.print.value = .word label.val from rfl] using read
      · simpa only [LabeledItems.printTail, LabeledItems.printPieces, List.map_append, List.map_cons,
          List.map_nil, List.cons_append, List.nil_append, List.append_assoc, Expr.printTokens, more,
          show printComma.value = comma from rfl, show printColon.value = colon from rfl,
          show label.print.value = .word label.val from rfl] using
          (LabeledItemsTail.comma label value tail read)

private theorem recordValuePrints (scope : Scope) (args : RecordValueArgs scope) :
    (recordValue scope).production args
      (((Category.expression scope).printPieces ((recordValue scope).tree args)).map PrintedToken.value) := by
  refine ⟨args.args.printPieces.map PrintedToken.value ++ [closeParen], ?_, (labeledPrintReads args.args []).1⟩
  simp only [Category.printPieces, recordValue, RecordValueArgs.expression, Expr.typed, Expr.printPieces,
    List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  rfl

public theorem RecordValueDerivation : RecordValueDerivationAussage := by
  rintro scope ⟨witness⟩
  exact ⟨fun args _ => recordValue_reads scope args, recordValuePrints scope,
    Rule.satisfiableOfPrint witness (recordValuePrints scope witness)⟩

end Gabbro.Core.Ast.Surface

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Katalog Waechter

theorem recordValue_parse : RecordValueParseAussage := by
  intro scope args text pieces lexed prod
  exact (Category.syntax (category := .expression scope)).parse_iff.mpr
    ⟨pieces, lexed, Surface.recordValue_reads scope args prod⟩

theorem recordValue_elaboriert : RecordValueElaboriertAussage := by
  intro scope platform args
  rfl

theorem recordValue_annahme : RecordValueAnnahmeAussage := by
  intro scope
  exact Quellform.annahme (recordValueForm scope)

theorem recordValue_einheit : RecordValueEinheitAussage := by
  intro scope platform args
  exact ⟨rfl, ((recordValueForm scope).befehl args).kommutation⟩

theorem recordValue_impl : RecordValueImplAussage := by
  intro scope args c s w plans u
  rfl

theorem recordValue_erhaltung : RecordValueErhaltungAussage := by
  intro scope
  exact Quellform.erhaltung (recordValueForm scope) (fun args =>
    expr_keine_invarianten 0 ((Surface.recordValue scope).tree args).2)

theorem recordValue_regelSicher : RecordValueRegelSicherAussage := by
  intro scope platform args
  exact (Quellform.erhaltung (recordValueForm scope) (fun a =>
    expr_keine_invarianten 0 ((Surface.recordValue scope).tree a).2) platform args).2.2.2

private theorem recordValue_amOrt (scope : Scope) : (recordValueForm scope).RegelAmOrt := by
  intro args
  change (((labeledCode 0 args.args).code ++ [_])[(labeledCode 0 args.args).code.length]?) = _
  simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero, recordValueForm, Nat.zero_add]

public theorem recordValue_realisiert : RecordValueRealisiertAussage := by
  intro scope platform args s running active live atPc
  exact (recordValueForm scope).realisiert (recordValue_amOrt scope) platform args s running active live atPc

public theorem recordValue_ideal : RecordValueIdealAussage := by
  intro scope
  exact ⟨recordValue_amOrt scope,
    fun args => ⟨((recordValueForm scope).befehl args).bestimmt, fun _ _ _ _ _ => Iff.rfl⟩⟩

public theorem recordValue_slots : RecordValueSlotsAussage := by
  intro scope args frame actual temps
  let widened (i : Fin args.types.length) :=
    Wert.widen (args.actualTypes.get (args.fields.slot i)) (args.types.get i)
      (args.fits i) (tupleGet args.actualTypes (args.fields.slot i) actual)
  have placed (i : Fin args.types.length) :
      (frame.temp (args.fields.slot i).val).bind (wertAls (args.types.get i)) = some (widened i) := by
    rw [temps (args.fields.slot i), Option.bind_some]
    exact wertAls_widen _ _ (args.fits i) _
  have read := ExpressionAggregates.readRecord frame args.types
    (fun i => (args.fields.slot i).val) widened placed
  change (Rahmen.schreibe frame 0 ((liesRecord frame.temp args.types
    (List.ofFn fun i => (args.fields.slot i).val)).map fun record =>
      ⟨recordValueType args.ref.name.val args.labels args.types, record⟩)).temp 0 = _
  rw [read]
  simp only [Rahmen.schreibe, Function.update_self]
  rfl

open Gabbro.Core.Text

@[expose] public def RecordExample.name : Identifier :=
  keywordName 'r' [] (by decide) (fun _ member => (List.not_mem_nil member).elim)

@[expose] public def RecordExample.field : Identifier :=
  keywordName 'x' [] (by decide) (fun _ member => (List.not_mem_nil member).elim)

@[expose] public def RecordExample.scope : Scope :=
  [⟨RecordExample.name, recordSchemaType RecordExample.name.val [RecordExample.field] [.bool], false, true⟩]

@[expose] public def RecordExample.value : Surface.RecordValueArgs RecordExample.scope := by
  let localRef : Local RecordExample.scope
      (recordSchemaType RecordExample.name.val [RecordExample.field] [.bool]) := .here
  let ref : RecordRef RecordExample.scope [RecordExample.field] [.bool] :=
    ⟨RecordExample.name, (directName_of_singleton (name := RecordExample.name) rfl).1,
      localRef, trivial, rfl, rfl, List.nodup_singleton _⟩
  exact ⟨_, _, ref, _, _, .next RecordExample.field .trueLit .empty,
    ⟨rfl, List.nodup_singleton _, id, fun _ => rfl⟩, fun i => by
      have eq : i = 0 := Fin.eq_zero i
      subst i
      trivial⟩

public theorem recordValue_erfuellbarAm : RecordValueErfuellbarAmAussage := by
  intro platform start
  let args := RecordExample.value
  let form := recordValueForm RecordExample.scope
  let E := form.einheit platform args
  let s₀ := (I.start E start).2
  let s₁ := (Befehl.wahrheitswert 0 true).nach eintritt s₀
  have step : E.system.ISchritt eintritt s₀ () [plan] s₁ := ⟨.wahrheitswert 0 true, rfl, rfl, rfl⟩
  refine ⟨RecordExample.scope, args, form.erfuellbar_aus_erreichbar platform start args s₁
    (.schritt eintritt () [plan] .start step) ?_ ?_⟩
  · exact form.realisiert (recordValue_amOrt _) platform args s₁ rfl rfl rfl rfl
  · intro guard found
    cases found

end Gabbro.Core.Ast.Semantik
