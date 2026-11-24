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

private theorem indexToken_ne_bool : keyword "index" ≠ keyword "bool" := by
  decide

private theorem indexToken_ne_string : keyword "index" ≠ keyword "string" := by
  decide

private theorem indexToken_ne_option : keyword "index" ≠ keyword "option" := by
  decide

private theorem indexToken_ne_intWord (signed : Bool) (width : Nat) :
    keyword "index" ≠ .word (intSpelling signed width) := by
  intro h
  change Token.word "index".toList = Token.word (intSpelling signed width) at h
  injection h with hl
  cases signed
  · exact (by decide : ('i' : Char) ≠ 'u') (List.cons.inj hl).1
  · have tailEq : (toString width).toList = "ndex".toList := (List.cons.inj hl).2.symm
    have mem : ('n' : Char) ∈ Nat.toDigits 10 width := by
      have inTail : ('n' : Char) ∈ (toString width).toList := by
        rw [tailEq]
        decide
      simpa using inTail
    have digit := Nat.isDigit_of_mem_toDigits (n := width) (b := 10) (by decide) (by decide) mem
    have notDigit : ('n' : Char).isDigit = false := by decide
    rw [notDigit] at digit
    cases digit

theorem carrierIndexInversion : CarrierIndexInversionAussage := by
  intro scope input written rest read
  generalize htok : keyword "index" :: input = toks at read
  cases read with
  | bool => exact (indexToken_ne_bool (List.cons.inj htok).1).elim
  | integer valid closed =>
      rename_i signed width
      exact (indexToken_ne_intWord signed width (List.cons.inj htok).1).elim
  | interval valid ls rs =>
      rename_i signed width input' lo hi more
      exact (indexToken_ne_intWord signed width (List.cons.inj htok).1).elim
  | array count bound elemRead boundRead =>
      cases (List.cons.inj htok).1
  | tuple firstRead secondRead tailRead =>
      cases (List.cons.inj htok).1
  | text => exact (indexToken_ne_string (List.cons.inj htok).1).elim
  | indexOption carrier resolved => exact (indexToken_ne_option (List.cons.inj htok).1).elim
  | index carrier resolved =>
      exact ⟨carrier, _, (List.cons.inj htok).2, resolved, rfl⟩

theorem carrierIndexDerivation : CarrierIndexDerivationAussage := by
  intro scope carrier count rest resolved
  have hIndex : printIndex.value = keyword "index" := by
    decide
  have hInto : printInto.value = keyword "into" := by
    decide
  have hCarrier : (Identifier.print carrier).value = .word carrier.val := rfl
  change TypeReads scope (printIndex.value :: printInto.value :: (Identifier.print carrier).value :: rest)
    (.index carrier count) rest
  simpa only [hIndex, hInto, hCarrier] using
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
    decide
  have paramOrdinary : ordinaryLocal paramName := by
    dsimp [ordinaryLocal, ordinaryAtomWord, paramName, carrierIndex_singleIdent]
    decide
  let param : Parameter scope := ⟨paramName, .index carrier count, resolved, paramOrdinary⟩
  have fnOrdinary : directName fnName := by
    constructor
    · dsimp [ordinaryLocal, ordinaryAtomWord, fnName, carrierIndex_singleIdent]
      decide
    · dsimp [fnName, carrierIndex_singleIdent]
      decide
  have validNone : ∀ t ∈ (none : Option WrittenType).toList, WrittenType.valid scope t := by
    intro t mem
    cases mem
  let argsVal : Surface.FunctionArgs scope := {
    name := fnName
    ordinary := fnOrdinary
    parameters := [param]
    result := none
    valid := validNone
    measure := none
    body := .braces .done
    distinct := by
      change (paramName.val :: []).Nodup
      simp only [List.nodup_cons, List.not_mem_nil, List.nodup_nil, and_true, not_false_eq_true]
    returns := by
      intro h
      cases h
  }
  let args : {a : Surface.FunctionArgs scope // ∃ p ∈ a.parameters, indexTypeUse p.written} :=
    ⟨argsVal, by
      refine ⟨param, ?_, ?_⟩
      · change param ∈ [param]
        exact List.mem_cons_self
      · change True
        trivial⟩
  let form := carrierTypeForm scope indexTypeUse
  let E := form.einheit platform args
  let s₀ := (I.start E start).2
  refine ⟨scope, args, ?_⟩
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
