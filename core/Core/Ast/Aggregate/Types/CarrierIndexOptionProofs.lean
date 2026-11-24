module

public import Core.Ast.Aggregate.Types.CarrierIndexOption
public import Core.Ast.Semantik.Formbeweise

/-!
# CarrierIndexOption

Prove the pinned statements in this file.
- `CarrierIndexOptionInversionAussage`
- `CarrierIndexOptionDerivationAussage`
- `CarrierIndexOptionCasesAussage`
- `CarrierIndexOptionZeroAussage`
- `CarrierIndexOptionParseAussage`
- `CarrierIndexOptionElaboriertAussage`
- `CarrierIndexOptionRealisiertAussage`
- `CarrierIndexOptionAnnahmeAussage`
- `CarrierIndexOptionIdealAussage`
- `CarrierIndexOptionEinheitAussage`
- `CarrierIndexOptionImplAussage`
- `CarrierIndexOptionErhaltungAussage`
- `CarrierIndexOptionSignatureAussage`
- `CarrierIndexOptionRegelSicherAussage`
- `CarrierIndexOptionErfuellbarAmAussage`
-/

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Katalog Waechter
open Gabbro.Core.Text

private theorem optionToken_ne_bool : keyword "option" ≠ keyword "bool" := by decide

private theorem optionToken_ne_string : keyword "option" ≠ keyword "string" := by decide

private theorem optionToken_ne_index : keyword "option" ≠ keyword "index" := by decide

private theorem optionToken_ne_intWord (signed : Bool) (width : Nat) :
    keyword "option" ≠ .word (intSpelling signed width) := by
  intro h
  change Token.word "option".toList = Token.word (intSpelling signed width) at h
  injection h with hl
  cases signed
  · exact (by decide : ('o' : Char) ≠ 'u') (List.cons.inj hl).1
  · exact (by decide : ('o' : Char) ≠ 'i') (List.cons.inj hl).1

private theorem carrier_am_ort (scope : Scope) (belongs : WrittenType → Prop) :
    (carrierTypeForm scope belongs).RegelAmOrt := by
  intro args
  let a := args.val
  change ((Fragment.einzel (functionInstruction scope a.name a.parameters a.result a.measure.isSome
      (functionCode a.result a.measure a.body))).anhaengen
      (functionCode a.result a.measure a.body)).code[0]? =
    some (functionInstruction scope a.name a.parameters a.result a.measure.isSome
      (functionCode a.result a.measure a.body))
  simp only [Fragment.anhaengen, Fragment.einzel, List.cons_append, List.nil_append,
    List.getElem?_cons_zero]

private theorem carrier_keine_invarianten (scope : Scope) (belongs : WrittenType → Prop)
    (args : {args : Surface.FunctionArgs scope // ∃ p ∈ args.parameters, belongs p.written}) :
    ((carrierTypeForm scope belongs).fragment args).klauseln.invariant = [] := by
  let rec blockInv {res : Option (Ty .value)} {before after : Scope} (t : Block res before after) :
      (block t).klauseln.invariant = [] :=
    match t with
    | .done => rfl
    | .step first rest => by
        change (stmt first).klauseln.invariant ++ (block rest).klauseln.invariant = []
        rw [stmt_keine_invarianten, blockInv rest]
        rfl
  have bracedInv : ∀ {res : Option (Ty .value)} {before : Scope} (t : BracedBlock res before),
      (bracedBlock t).klauseln.invariant = [] := by
    intro res before t
    rcases t with ⟨body⟩
    change (block body).klauseln.invariant ++ [] = []
    rw [blockInv body]
    rfl
  have codeInv : ∀ {s : Scope} (res : Option WrittenType) (measure : Option (Measure s))
      (body : BracedBlock (writtenResult res) s),
      (functionCode res measure body).klauseln.invariant = [] := by
    intro s res measure body
    cases measure with
    | none =>
        simp only [functionCode, Fragment.anhaengen, Fragment.einzel, Quellklauseln.anhaengen,
          Quellklauseln.leer, List.append_nil, List.nil_append]
        exact bracedInv body
    | some m =>
        simp only [functionCode, Fragment.anhaengen, Fragment.einzel, Quellklauseln.anhaengen,
          Quellklauseln.leer, List.append_nil, List.nil_append]
        rw [expr_keine_invarianten]
        exact bracedInv body
  let a := args.val
  change (decl ((functionForm scope).produktion.tree a).2).klauseln.invariant = []
  change ((Fragment.einzel (functionInstruction scope a.name a.parameters a.result a.measure.isSome
    (functionCode a.result a.measure a.body))).anhaengen
    (functionCode a.result a.measure a.body)).klauseln.invariant = []
  simp only [Fragment.anhaengen, Fragment.einzel, Quellklauseln.anhaengen, Quellklauseln.leer,
    List.append_nil, List.nil_append]
  exact codeInv a.result a.measure a.body

private theorem carrier_signature (scope : Scope) (args : Surface.FunctionArgs scope) (frame : Rahmen) :
    CarrierParameterEffect scope args frame := by
  unfold CarrierParameterEffect
  dsimp [functionForm, functionInstruction, Befehl.auswerten]
  refine ⟨⟨args.name, frame.pc + 1, args.parameters.map (fun p => p.written.type),
    writtenResult args.result, scope.length, args.measure.isSome,
    (functionCode args.result args.measure args.body).code.filterMap fun
      | .rufe target callArgs bind => some ⟨target, callArgs, bind⟩
      | _ => none⟩, ?_, rfl, rfl⟩
  rfl

theorem carrierIndexOptionInversion : CarrierIndexOptionInversionAussage := by
  intro scope input written rest read
  generalize htok : keyword "option" :: input = toks at read
  cases read with
  | bool => exact (optionToken_ne_bool (List.cons.inj htok).1).elim
  | integer valid closed =>
      rename_i signed width
      exact (optionToken_ne_intWord signed width (List.cons.inj htok).1).elim
  | interval valid ls rs =>
      rename_i signed width input' lo hi more
      exact (optionToken_ne_intWord signed width (List.cons.inj htok).1).elim
  | array count bound elemRead boundRead =>
      cases (List.cons.inj htok).1
  | tuple firstRead secondRead tailRead =>
      cases (List.cons.inj htok).1
  | text => exact (optionToken_ne_string (List.cons.inj htok).1).elim
  | index carrier resolved => exact (optionToken_ne_index (List.cons.inj htok).1).elim
  | indexOption carrier resolved =>
      exact ⟨carrier, _, (List.cons.inj htok).2, resolved, rfl⟩

theorem carrierIndexOptionDerivation : CarrierIndexOptionDerivationAussage := by
  intro scope carrier count rest resolved
  change TypeReads scope (keyword "option" :: keyword "index" :: keyword "into" ::
    .word carrier.val :: rest) (.indexOption carrier count) rest
  exact TypeReads.indexOption carrier resolved

theorem carrierIndexOptionCases : CarrierIndexOptionCasesAussage := by
  intro count value
  change Sum (Wert (indexType count)) (Sum PUnit Empty) at value
  cases value with
  | inl present => exact Or.inl ⟨present, rfl⟩
  | inr rest =>
      cases rest with
      | inl unit => exact Or.inr rfl
      | inr empty => cases empty

theorem carrierIndexOptionZero : CarrierIndexOptionZeroAussage := by
  constructor
  · exact ⟨Sum.inr (Sum.inl PUnit.unit)⟩
  · intro value
    change Sum (Wert (indexType 0)) (Sum PUnit Empty) at value
    cases value with
    | inl present =>
        change Zahl 0 ((0 : Int) - 1) at present
        have impossible : (0 : Int) ≤ (0 : Int) - 1 := le_trans present.unten present.oben
        omega
    | inr rest =>
        cases rest with
        | inl unit => rfl
        | inr empty => cases empty

theorem carrierIndexOptionParse : CarrierIndexOptionParseAussage := by
  intro scope args text pieces lexed production
  apply (Category.declaration scope).syntax.parse_iff.mpr
  exact ⟨pieces, lexed, (Surface.function_entry scope).reads args.val (canonicalTokens pieces) production⟩

theorem carrierIndexOptionElaboriert : CarrierIndexOptionElaboriertAussage := by
  intro scope platform args
  rfl

theorem carrierIndexOptionRealisiert : CarrierIndexOptionRealisiertAussage := by
  intro scope platform args s running active live atPc
  exact (carrierTypeForm scope indexOptionTypeUse).realisiert (carrier_am_ort scope _) platform
    args s running active live atPc

theorem carrierIndexOptionAnnahme : CarrierIndexOptionAnnahmeAussage := by
  intro scope
  exact Quellform.annahme (carrierTypeForm scope indexOptionTypeUse)

theorem carrierIndexOptionIdeal : CarrierIndexOptionIdealAussage := by
  intro scope
  refine ⟨carrier_am_ort scope _, ?_⟩
  intro args
  refine ⟨Befehl.bestimmt _, ?_⟩
  intro c s w plans u
  rfl

theorem carrierIndexOptionEinheit : CarrierIndexOptionEinheitAussage := by
  intro scope platform args
  exact ⟨rfl, ((carrierTypeForm scope indexOptionTypeUse).befehl args).kommutation⟩

theorem carrierIndexOptionImpl : CarrierIndexOptionImplAussage := by
  intro scope args c s w plans u
  rfl

theorem carrierIndexOptionErhaltung : CarrierIndexOptionErhaltungAussage := by
  intro scope
  apply Quellform.erhaltung
  intro args
  exact carrier_keine_invarianten scope indexOptionTypeUse args

theorem carrierIndexOptionSignature : CarrierIndexOptionSignatureAussage := by
  intro scope args frame h
  exact carrier_signature scope args frame

theorem carrierIndexOptionRegelSicher : CarrierIndexOptionRegelSicherAussage := by
  intro scope platform args
  exact Befehl.sicher ((carrierTypeForm scope indexOptionTypeUse).fragment args) platform
    (carrier_keine_invarianten scope indexOptionTypeUse args)
    ((carrierTypeForm scope indexOptionTypeUse).befehl args)

theorem carrierIndexOptionErfuellbarAm : CarrierIndexOptionErfuellbarAmAussage := by
  intro platform start
  let carrier : Identifier := keywordName 'c' [] (by decide) (fun _ member => (List.not_mem_nil member).elim)
  let scope : Scope := [⟨carrier, .carrierSchema 1, false, false⟩]
  have resolved : scope.carrierCount carrier = some 1 := by decide
  let pname : Identifier := keywordName 'p' [] (by decide) (fun _ member => (List.not_mem_nil member).elim)
  have pOrdinary : ordinaryLocal pname := by
    dsimp [ordinaryLocal, ordinaryAtomWord, pname]
    decide
  let param : Parameter scope := ⟨pname, .indexOption carrier 1, resolved, pOrdinary⟩
  let fname : Identifier := keywordName 'f' [] (by decide) (fun _ member => (List.not_mem_nil member).elim)
  have fOrdinary : directName fname := by
    dsimp [directName, ordinaryLocal, ordinaryAtomWord, fname]
    decide
  have validNone : ∀ t ∈ (none : Option WrittenType).toList, WrittenType.valid scope t := by
    intro t mem
    cases mem
  let args : Surface.FunctionArgs scope :=
    ⟨fname, fOrdinary, [param], none, validNone, none, .braces .done,
      by simp only [List.map_cons, List.map_nil, List.nodup_cons, List.nodup_nil, List.not_mem_nil], by
      intro h
      cases h⟩
  have belongs : ∃ p ∈ args.parameters, indexOptionTypeUse p.written := by
    refine ⟨param, ?_, ?_⟩
    · change param ∈ ([param] : List (Parameter scope))
      simp only [List.mem_singleton]
    · trivial
  let witness : {args : Surface.FunctionArgs scope // ∃ p ∈ args.parameters, indexOptionTypeUse p.written} :=
    ⟨args, belongs⟩
  refine ⟨scope, witness, ?_⟩
  let form := carrierTypeForm scope indexOptionTypeUse
  let E := form.einheit platform witness
  let s := (I.start E start).2
  refine ⟨Ast.print (category := .declaration scope) (form.produktion.tree witness), s,
    Ast.parse_print _, rfl, .start, ?_, ?_, ?_⟩
  · exact form.realisiert (carrier_am_ort scope _) platform witness s rfl rfl rfl rfl
  · intro g guard
    cases guard
  · exact carrier_signature scope args (s.lokal eintritt)

end Gabbro.Core.Ast.Semantik
