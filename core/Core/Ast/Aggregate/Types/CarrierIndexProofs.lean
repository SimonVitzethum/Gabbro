module

public import Core.Ast.Aggregate.Types.CarrierIndex
public import Core.Ast.Semantik.Formbeweise
public import Core.Ast.ProgramSurface
import Init.Omega

/-!
# CarrierIndex

Prove the pinned statements in this file.
- `CarrierIndexInversionAussage`
- `CarrierIndexDerivationAussage`
- `CarrierIndexRangeAussage`
- `CarrierIndexParseAussage`
- `CarrierIndexElaboriertAussage`
- `CarrierIndexRealisiertAussage`
- `CarrierIndexAnnahmeAussage`
- `CarrierIndexIdealAussage`
- `CarrierIndexEinheitAussage`
- `CarrierIndexImplAussage`
- `CarrierIndexErhaltungAussage`
- `CarrierIndexSignatureAussage`
- `CarrierIndexRegelSicherAussage`
- `CarrierIndexErfuellbarAmAussage`
-/

@[expose] public section

open Gabbro.Core.Text

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Gabbro.Core.Text

theorem carrierIndexInversion : CarrierIndexInversionAussage := by
  intro scope input written rest read
  cases read with
  | index carrier resolved =>
      exact ⟨carrier, _, rfl, resolved, rfl⟩

theorem carrierIndexDerivation : CarrierIndexDerivationAussage := by
  intro scope carrier count rest resolved
  have hIndex : printIndex.value = keyword "index" := by
    decide
  have hInto : printInto.value = keyword "into" := by
    decide
  have hCarrier : (Identifier.print carrier).value = .word carrier.val := rfl
  simpa only [WrittenType.printPieces, List.map_cons, List.map_nil, List.nil_append,
    hIndex, hInto, hCarrier] using
    (TypeReads.index (scope := scope) (rest := rest) carrier resolved)

theorem carrierIndexRange : CarrierIndexRangeAussage := by
  intro count offset
  constructor
  · rintro ⟨value, rfl⟩
    have oben := value.oben
    exact ⟨value.unten, by omega⟩
  · rintro ⟨nonneg, below⟩
    exact ⟨⟨offset, nonneg, by omega⟩, rfl⟩

theorem carrierIndexParse : CarrierIndexParseAussage := by
  intro scope args text pieces lexed production
  exact (Surface.function_entry scope).parse lexed production

theorem carrierIndexElaboriert : CarrierIndexElaboriertAussage := by
  intro scope platform args
  rfl

private theorem carrierIndex_am_ort (scope : Scope) :
    (carrierTypeForm scope indexTypeUse).RegelAmOrt := by
  intro args
  change ((Fragment.einzel (functionInstruction scope args.val.name args.val.parameters
    args.val.result args.val.measure.isSome
    (functionCode args.val.result args.val.measure args.val.body))).anhaengen
    (functionCode args.val.result args.val.measure args.val.body)).code[0]? =
      some (functionInstruction scope args.val.name args.val.parameters args.val.result
        args.val.measure.isSome (functionCode args.val.result args.val.measure args.val.body))
  simp only [Fragment.anhaengen, Fragment.einzel, List.cons_append, List.nil_append,
    List.getElem?_cons_zero]

theorem carrierIndexRealisiert : CarrierIndexRealisiertAussage := by
  intro scope platform args s running active live atPc
  exact (carrierTypeForm scope indexTypeUse).realisiert (carrierIndex_am_ort scope)
    platform args s running active live atPc

theorem carrierIndexAnnahme : CarrierIndexAnnahmeAussage := by
  intro scope
  exact Quellform.annahme (carrierTypeForm scope indexTypeUse)

theorem carrierIndexIdeal : CarrierIndexIdealAussage := by
  intro scope
  refine ⟨carrierIndex_am_ort scope, ?_⟩
  intro args
  refine ⟨Befehl.bestimmt _, ?_⟩
  intro c s w plans u
  rfl

theorem carrierIndexEinheit : CarrierIndexEinheitAussage := by
  intro scope platform args
  exact ⟨rfl, ((carrierTypeForm scope indexTypeUse).befehl args).kommutation⟩

theorem carrierIndexImpl : CarrierIndexImplAussage := by
  intro scope args c s w plans u
  rfl

private theorem carrierIndex_keine_invarianten (scope : Scope)
    (args : {a : Surface.FunctionArgs scope // ∃ p ∈ a.parameters, indexTypeUse p.written}) :
    ((carrierTypeForm scope indexTypeUse).fragment args).klauseln.invariant = [] := by
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
        simp only [functionCode, Fragment.anhaengen, Fragment.einzel,
          Quellklauseln.anhaengen, Quellklauseln.leer, List.append_nil, List.nil_append]
        exact bracedInv body
    | some m =>
        simp only [functionCode, Fragment.anhaengen, Fragment.einzel,
          Quellklauseln.anhaengen, Quellklauseln.leer, List.append_nil, List.nil_append]
        rw [expr_keine_invarianten]
        exact bracedInv body
  change (decl ((carrierTypeForm scope indexTypeUse).produktion.tree args).2).klauseln.invariant = []
  change ((Fragment.einzel (functionInstruction scope args.val.name args.val.parameters
    args.val.result args.val.measure.isSome
    (functionCode args.val.result args.val.measure args.val.body))).anhaengen
    (functionCode args.val.result args.val.measure args.val.body)).klauseln.invariant = []
  simp only [Fragment.anhaengen, Fragment.einzel, Quellklauseln.anhaengen,
    Quellklauseln.leer, List.append_nil, List.nil_append]
  exact codeInv args.val.result args.val.measure args.val.body

theorem carrierIndexErhaltung : CarrierIndexErhaltungAussage := by
  intro scope
  apply Quellform.erhaltung
  intro args
  exact carrierIndex_keine_invarianten scope args

theorem carrierIndexRegelSicher : CarrierIndexRegelSicherAussage := by
  intro scope platform args
  exact Befehl.sicher ((carrierTypeForm scope indexTypeUse).fragment args) platform
    (carrierIndex_keine_invarianten scope args) ((carrierTypeForm scope indexTypeUse).befehl args)

theorem carrierIndexSignature : CarrierIndexSignatureAussage := by
  intro scope args frame premise
  dsimp [CarrierParameterEffect, functionForm, functionInstruction, Befehl.auswerten]
  refine ⟨_, rfl, rfl, rfl⟩

private def carrierIndex_singleIdent (c : Char) (low : 'a' ≤ c) (high : c ≤ 'z') : Identifier :=
  ⟨[c], c, [], rfl, Or.inl (Or.inl ⟨low, high⟩), fun _ member => (List.not_mem_nil member).elim⟩

theorem carrierIndexErfuellbarAm : CarrierIndexErfuellbarAmAussage := by
  intro platform start
  let carrier : Identifier :=
    carrierIndex_singleIdent 'c' (by change 97 ≤ 99; omega) (by change 99 ≤ 122; omega)
  let paramName : Identifier :=
    carrierIndex_singleIdent 'p' (by change 97 ≤ 112; omega) (by change 112 ≤ 122; omega)
  let fnName : Identifier :=
    carrierIndex_singleIdent 'f' (by change 97 ≤ 102; omega) (by change 102 ≤ 122; omega)
  let count : Nat := 1
  let scope : Scope := [⟨carrier, .carrierSchema count, false, false⟩]
  have resolved : scope.carrierCount carrier = some count := by
    simp [Scope.carrierCount, scope, carrierIndex_singleIdent]
  have paramOrdinary : ordinaryLocal paramName := by
    simp [ordinaryLocal, ordinaryAtomWord, paramName, carrierIndex_singleIdent]
  let param : Parameter scope := ⟨paramName, .index carrier count, resolved, paramOrdinary⟩
  have fnOrdinary : directName fnName := by
    constructor
    · change ordinaryAtomWord fnName.val
      simp [ordinaryAtomWord, fnName, carrierIndex_singleIdent]
    · simp [fnName, carrierIndex_singleIdent]
  let argsVal : Surface.FunctionArgs scope :=
    ⟨fnName, fnOrdinary, [param], none, by intro t mem; cases mem, none, .braces .done,
      by simp [param], by intro h; cases h⟩
  let args : {a : Surface.FunctionArgs scope // ∃ p ∈ a.parameters, indexTypeUse p.written} :=
    ⟨argsVal, by
      refine ⟨param, ?_, ?_⟩
      · simp [argsVal]
      · change True
        trivial⟩
  let form := carrierTypeForm scope indexTypeUse
  let E := form.einheit platform args
  let s₀ := (I.start E start).2
  refine ⟨args, ?_⟩
  refine ⟨Ast.print (form.produktion.tree args), s₀, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Ast.parse_print (form.produktion.tree args)
  · rfl
  · exact .start
  · exact form.realisiert (carrierIndex_am_ort scope) platform args s₀ rfl rfl rfl rfl
  · intro g guard
    cases guard
  · dsimp [CarrierParameterEffect, functionForm, functionInstruction, Befehl.auswerten]
    refine ⟨_, rfl, rfl, rfl⟩

end Gabbro.Core.Ast.Semantik
