module

public import Core.Ast.Variant.Obligations

/-!
# VariantValue

- `Surface.VariantValueInversionAussage`
- `Surface.VariantValueSuffixAussage`
- `Surface.VariantValueDerivationAussage`
- `VariantValueParseAussage`
- `VariantValueElaboriertAussage`
- `VariantValueRealisiertAussage`
- `VariantValueAnnahmeAussage`
- `VariantValueIdealAussage`
- `VariantValueEinheitAussage`
- `VariantValueImplAussage`
- `VariantValueErhaltungAussage`
- `VariantValueRegelSicherAussage`
- `VariantValueErfuellbarAmAussage`
- `VariantValuePayloadAussage`
-/

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Katalog Waechter

private theorem vv_amOrt (scope : Scope) : (variantValueForm scope).RegelAmOrt := by
  intro a
  change (((caseCode 0 a.payload).code ++
    [(Befehl.baueVariante 0 a.ref.name.val a.labels a.payloads a.index)]))[
      (caseCode 0 a.payload).code.length]? =
    some (Befehl.baueVariante 0 a.ref.name.val a.labels a.payloads a.index)
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp only [Nat.sub_self, List.getElem?_cons_zero]

theorem variantValue_annahme : VariantValueAnnahmeAussage := by
  intro scope platform args
  let form := variantValueForm scope
  refine ⟨(form.befehl args).lokal _ rfl, ?_, ?_⟩
  · rintro s c ⟨op, operands⟩ head guard
    exact ⟨c, form.befehl args, head, guard⟩
  · intro t c s w stepPlan u spur next step execute ev
    obtain ⟨rfl, _⟩ := (form.befehl args).vollzug_genau (w := w) step execute
    exact List.not_mem_nil

private theorem vv_caseCode_inv (slot : Nat) {ty : Option (Ty .value)}
    (payload : CasePayload scope ty) : (caseCode slot payload).klauseln.invariant = [] := by
  cases payload with
  | nullary paren => rfl
  | value e => simpa [caseCode] using expr_keine_invarianten slot e

theorem variantValue_erhaltung : VariantValueErhaltungAussage := by
  intro scope platform args
  let p := (variantValueForm scope).fragment args
  let b := (variantValueForm scope).befehl args
  have inv : p.klauseln.invariant = [] := by
    change ((caseCode 0 args.payload).klauseln.invariant ++
      (Fragment.einzel b).klauseln.invariant) = []
    rw [vv_caseCode_inv]
    rfl
  exact ⟨b.abgleich p platform, b.fortschritt p, b.komponierbar p platform,
    b.sicherheitsPflichten p platform [] (tabLeer _ inv) (fun b _ => rfl)⟩

theorem variantValue_regelSicher : VariantValueRegelSicherAussage := by
  intro scope platform args
  exact (variantValue_erhaltung scope platform args).2.2.2.1

theorem variantValue_elaboriert : VariantValueElaboriertAussage := by
  intro scope platform args
  rfl

theorem variantValue_realisiert : VariantValueRealisiertAussage := by
  intro scope platform args s running active live atPc
  exact (variantValueForm scope).realisiert (vv_amOrt scope) platform args s running active live atPc

theorem variantValue_ideal : VariantValueIdealAussage := by
  intro scope
  constructor
  · exact vv_amOrt scope
  · intro args
    constructor
    · exact ((variantValueForm scope).befehl args).bestimmt
    · intro c s w plans u
      rfl

theorem variantValue_einheit : VariantValueEinheitAussage := by
  intro scope platform args
  exact ⟨rfl, ((variantValueForm scope).befehl args).kommutation⟩

theorem variantValue_impl : VariantValueImplAussage := by
  intro scope args c s w plans u
  rfl

private theorem vv_case_inject (cases : List (Option (Ty .value))) (index : Fin cases.length)
    (payload : Wert ((cases.get index).getD .productEnd)) :
    (variantCase cases (variantInject cases index payload)).1 = index.val := by
  induction cases with
  | nil => exact Fin.elim0 index
  | cons head tail ih =>
      cases index with
      | mk n bound =>
        cases n with
        | zero => rfl
        | succ n =>
            have h := ih ⟨n, Nat.lt_of_succ_lt_succ bound⟩ payload
            simpa [variantCase, variantInject, h]

theorem variantValue_payload : VariantValuePayloadAussage := by
  intro scope a frame payload h
  constructor
  · change ((variantActual (a.payloads.get a.index) (frame.temp 0)).bind
      (fun value => (some ⟨variantValueType a.ref.name.val a.labels a.payloads,
        variantInject a.payloads a.index value⟩ : Option Dynamisch))) =
      (some ⟨variantValueType a.ref.name.val a.labels a.payloads,
        variantInject a.payloads a.index payload⟩ : Option Dynamisch)
    rw [h]
    rfl
  · exact vv_case_inject a.payloads a.index payload

open Gabbro.Core.Text
open Surface

theorem variantValue_inversion : VariantValueInversionAussage := by
  intro scope input type tree rest caseName ordinary available read
  generalize spelling : caseName.val = word at read
  cases read with
  | trueLit => exact (ordinary.1 spelling).elim
  | falseLit => exact (ordinary.2.1 spelling).elim
  | textLength _ => exact (ordinary.2.2.1 spelling).elim
  | «variable» ref _ _ => exact (available.2 _ ref.binding_mem spelling.symm).elim
  | recordValue ref _ _ _ =>
    exact (available.2 _ ref.schema.binding_mem (ref.spelled.trans spelling.symm)).elim
  | variantValue ref label index written ordinary available payload payloadRead =>
    exact ⟨⟨_, _, ref, label, index, written, ordinary, available, payload⟩,
      Subtype.ext spelling.symm, payloadRead, rfl⟩

private theorem casePayloadPrints (payload : CasePayload scope type) :
    CasePayloadRead scope (payload.printPieces.map PrintedToken.value ++ [closeParen]) payload [closeParen] := by
  cases payload with
  | nullary parens =>
    cases parens
    · exact .bare (fun _ impossible => by cases impossible)
    · exact .empty
  | value expr =>
    simpa only [CasePayload.printPieces, Expr.printTokens, List.map_append, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.append_assoc, show printOpen.value = openParen from rfl,
      show printClose.value = closeParen from rfl] using
        (CasePayloadRead.value (expr.printReads (rest := [closeParen, closeParen]) noOperatorAtClose))

private theorem variantValuePrints (scope : Scope) (args : VariantValueArgs scope) :
    (variantValue scope).production args
      (((Category.expression scope).printPieces ((variantValue scope).tree args)).map PrintedToken.value) := by
  refine Or.inr ⟨args.payload.printPieces.map PrintedToken.value ++ [closeParen], ?_, casePayloadPrints args.payload⟩
  simp only [Category.printPieces, variantValue, VariantValueArgs.expression, Expr.typed, Expr.printPieces,
    List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_assoc]
  rfl

theorem variantValue_derivation : VariantValueDerivationAussage := by
  rintro scope ⟨witness⟩
  refine ⟨?_, variantValuePrints scope, Rule.satisfiableOfPrint witness (variantValuePrints scope witness)⟩
  intro args tokens production
  rcases production with ⟨input, rfl, payload⟩ | ⟨input, rfl, payload⟩
  · exact .atom (.variantValue args.ref args.label args.index args.written
      args.ordinary args.available args.payload payload) (.stop noOperatorAtEnd)
  · exact .atom (.grouped (.atom (.variantValue args.ref args.label args.index args.written
      args.ordinary args.available args.payload payload) (.stop noOperatorAtClose))) (.stop noOperatorAtEnd)

theorem variantValue_suffix : Gabbro.Core.Ast.Surface.VariantValueSuffixAussage := by
  intro scope input type payload rest read
  cases read with
  | bare closed => exact List.suffix_refl _
  | empty => exact (List.suffix_cons _ _).trans (List.suffix_cons _ _)
  | value exprRead =>
      exact (List.suffix_cons _ _).trans
        ((ExprReads.consumes exprRead).trans (List.suffix_cons _ _))

theorem variantValue_parse : Gabbro.Core.Ast.Semantik.VariantValueParseAussage := by
  intro scope args text pieces lexed production
  apply (Gabbro.Core.Ast.Category.expression scope).syntax.parse_iff.mpr
  refine ⟨pieces, lexed, ?_⟩
  rcases production with ⟨input, same, payloadRead⟩ | ⟨input, same, payloadRead⟩
  · rw [same]
    exact .atom (.variantValue args.ref args.label args.index args.written
      args.ordinary args.available args.payload payloadRead) (.stop Gabbro.Core.Ast.noOperatorAtEnd)
  · rw [same]
    exact .atom (.grouped (.atom (.variantValue args.ref args.label args.index args.written
      args.ordinary args.available args.payload payloadRead) (.stop Gabbro.Core.Ast.noOperatorAtClose)))
      (.stop Gabbro.Core.Ast.noOperatorAtEnd)

theorem variantValue_erfuellbarAm : VariantValueErfuellbarAmAussage := by
  intro platform start
  let name : Gabbro.Core.Ast.Identifier :=
    Gabbro.Core.Ast.keywordName 'v' [] (by decide) (fun _ member => (List.not_mem_nil member).elim)
  let lbl : Gabbro.Core.Ast.Identifier :=
    Gabbro.Core.Ast.keywordName 'a' [] (by decide) (fun _ member => (List.not_mem_nil member).elim)
  let member : Gabbro.Core.Ast.VariantMember := ⟨lbl, none⟩
  let labels : List Gabbro.Core.Ast.Identifier := Gabbro.Core.Ast.variantLabels [member]
  let payloads : List (Option (Ty .value)) := Gabbro.Core.Ast.variantPayloads [member]
  let schemaType : Ty .value := variantSchemaType name.val labels payloads
  let binding : Gabbro.Core.Ast.Binding := ⟨name, schemaType, false, true⟩
  let scope : Scope := [binding]
  let refSchema : Local scope schemaType := .here
  let ref : Gabbro.Core.Ast.VariantRef scope labels payloads :=
    ⟨name, refSchema, trivial, rfl, rfl,
      by change [lbl.val].Nodup; exact List.nodup_singleton _⟩
  let index : Fin payloads.length := ⟨0, Nat.zero_lt_succ _⟩
  have written : labels[index.val]? = some lbl := rfl
  have ordinary : Gabbro.Core.Ast.ordinaryLocal lbl := by
    exact (directName_of_singleton (name := lbl) rfl).1
  have available : availableCase scope lbl := by
    constructor
    · exact List.count_singleton_self
    · intro b hb
      have same : b = binding := List.mem_singleton.mp hb
      subst b
      intro same
      cases same
  let a : Gabbro.Core.Ast.Surface.VariantValueArgs scope :=
    ⟨labels, payloads, ref, lbl, index, written, ordinary, available, .nullary false⟩
  refine ⟨scope, a, ?_⟩
  let form := variantValueForm scope
  let s := (I.start (form.einheit platform a) start).2
  dsimp [Quellform.ErfuellbarAm]
  refine ⟨Ast.print (category := .expression scope) (form.produktion.tree a), s,
    Ast.parse_print _, rfl, .start, ?_, ?_⟩
  · exact form.realisiert (vv_amOrt scope) platform a s rfl rfl rfl rfl
  · intro g guard; cases guard

end Gabbro.Core.Ast.Semantik
