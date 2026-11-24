module

public import Core.Ast.Inventory.Entries.WrittenTypeStatements
public import Core.Ast.Semantik.Formbeweise
public import Core.Ast.ProgramSurface

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Katalog Waechter
open Gabbro.Core.Text

private theorem boolTypeDerivation :
    ∀ scope rest, TypeReads scope (WrittenType.bool.printPieces.map PrintedToken.value ++ rest) .bool rest := by
  intro scope rest
  simpa only [WrittenType.printPieces, List.map_cons, List.map_nil, List.singleton_append,
    (show printBoolType.value = keyword "bool" from rfl)] using
    (TypeReads.bool (scope := scope) (rest := rest))

private theorem integerTypeDerivation :
    ∀ scope signed width interval rest, (WrittenType.integer signed width interval).valid scope →
      (∀ more, rest ≠ keyword "in" :: more) →
      TypeReads scope ((WrittenType.integer signed width interval).printPieces.map PrintedToken.value ++ rest)
        (.integer signed width interval) rest := by
  intro scope signed width interval rest valid closed
  exact WrittenType.printReads (.integer signed width interval) valid closed

private theorem scalarType_am_ort (belongs : WrittenType → Prop)
    (ctx : Scope × Option (Ty .value)) : (typeUseForm ctx belongs).RegelAmOrt := by
  intro args
  change (((expr 0 args.val.value).code ++
      [Befehl.bindeWert 0 args.val.written.type false])[(expr 0 args.val.value).code.length]? =
    some (.bindeWert 0 args.val.written.type false))
  simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]

private theorem scalarType_keine_invarianten (belongs : WrittenType → Prop)
    (ctx : Scope × Option (Ty .value))
    (args : {a : Surface.MutableLocalArgs ctx.1 ctx.2 // belongs a.written}) :
    ((typeUseForm ctx belongs).fragment args).klauseln.invariant = [] := by
  exact stmt_keine_invarianten (((Surface.mutableLocal ctx.1 ctx.2).tree args.val).2)

private theorem scalarTypeParse (belongs : WrittenType → Prop) :
    ∀ ctx, (typeUseForm ctx belongs).ParseAussage := by
  intro ctx args text pieces lexed production
  exact (Surface.mutableLocal_entry ctx.1 ctx.2).parse lexed production

private theorem scalarTypeElaboriert (belongs : WrittenType → Prop) :
    ∀ ctx, (typeUseForm ctx belongs).ElaboriertAussage := by
  intro ctx platform args
  rfl

private theorem scalarTypeRealisiert (belongs : WrittenType → Prop) :
    ∀ ctx, (typeUseForm ctx belongs).RealisiertAussage := by
  intro ctx platform args s running active live atPc
  exact (typeUseForm ctx belongs).realisiert (scalarType_am_ort belongs ctx) platform args
    s running active live atPc

private theorem scalarTypeAnnahme (belongs : WrittenType → Prop) :
    ∀ ctx, (typeUseForm ctx belongs).AnnahmeAussage := by
  intro ctx
  exact Quellform.annahme (typeUseForm ctx belongs)

private theorem scalarTypeIdeal (belongs : WrittenType → Prop) :
    ∀ ctx, (typeUseForm ctx belongs).IdealAussage := by
  intro ctx
  refine ⟨scalarType_am_ort belongs ctx, ?_⟩
  intro args
  refine ⟨Befehl.bestimmt _, ?_⟩
  intro c s w plans u
  rfl

private theorem scalarTypeEinheit (belongs : WrittenType → Prop) :
    ∀ ctx, (typeUseForm ctx belongs).EinheitAussage := by
  intro ctx platform args
  exact ⟨rfl, ((typeUseForm ctx belongs).befehl args).kommutation⟩

private theorem scalarTypeImpl (belongs : WrittenType → Prop) :
    ∀ ctx, (typeUseForm ctx belongs).ImplAussage := by
  intro ctx args c s w plans u
  rfl

private theorem scalarTypeErhaltung (belongs : WrittenType → Prop) :
    ∀ ctx, (typeUseForm ctx belongs).ErhaltungsAussage := by
  intro ctx
  exact Quellform.erhaltung (typeUseForm ctx belongs)
    (fun args => scalarType_keine_invarianten belongs ctx args)

private theorem scalarTypeUseAussage (belongs : WrittenType → Prop) : LocalTypeUseAussage belongs :=
  ⟨scalarTypeParse belongs, scalarTypeElaboriert belongs, scalarTypeRealisiert belongs,
    scalarTypeAnnahme belongs, scalarTypeIdeal belongs, scalarTypeEinheit belongs,
    scalarTypeImpl belongs, scalarTypeErhaltung belongs⟩

private theorem scalarName : Identifier :=
  ⟨['x'], ⟨'x', [], rfl,
    Or.inl (Or.inl ⟨by change 97 ≤ 120; omega, by change 120 ≤ 122; omega⟩),
    by intro a m; cases m⟩⟩

private theorem reachableArgs (belongs : WrittenType → Prop)
    (atRoot : ∀ ctx, (typeUseForm ctx belongs).RegelAmOrt)
    (platform : Plattform) (start : AussenStart)
    (name : Identifier) (ordinary : ordinaryLocal name)
    (written : WrittenType) (valid : written.valid [])
    (type : Ty .value) (value : Expr [] type) (fits : Fits type written.type)
    (member : belongs written) (instruction : Befehl) :
    ∃ args : {a : Surface.MutableLocalArgs [] none // belongs a.written},
      args.val.written = written ∧ (typeUseForm ([], none) belongs).ErfuellbarAm platform start args := by
  let argsVal : Surface.MutableLocalArgs [] none := ⟨name, ordinary, written, valid, type, value, fits⟩
  let args : {a : Surface.MutableLocalArgs [] none // belongs a.written} := ⟨argsVal, member⟩
  let form := typeUseForm ([], none) belongs
  let E := form.einheit platform args
  let s₀ := (I.start E start).2
  let s₁ := instruction.nach eintritt s₀
  have step : E.system.ISchritt eintritt s₀ () [plan] s₁ := ⟨instruction, rfl, rfl, rfl⟩
  have reached : E.system.IErreichbar s₀ s₁ := .schritt eintritt () [plan] .start step
  refine ⟨args, rfl, form.erfuellbar_aus_erreichbar platform start args s₁ reached
    (form.realisiert (atRoot ([], none)) platform args s₁ rfl rfl rfl rfl) ?_⟩
  intro g guard
  cases guard

private theorem boolTypeErfuellbarAm : BoolTypeErfuellbarAussage := by
  intro platform start
  have ordinary : ordinaryLocal scalarName := (directName_of_singleton (name := scalarName) rfl).1
  exact reachableArgs boolTypeUse (scalarType_am_ort boolTypeUse) platform start
    scalarName ordinary .bool trivial .bool .trueLit trivial trivial
    (.wahrheitswert 0 true)

private theorem integerTypeErfuellbarAm : IntegerTypeErfuellbarAussage := by
  intro platform start signed bounded
  have ordinary : ordinaryLocal scalarName := (directName_of_singleton (name := scalarName) rfl).1
  cases bounded with
  | false =>
      obtain ⟨args, written, erf⟩ := reachableArgs integerTypeUse (scalarType_am_ort integerTypeUse)
        platform start scalarName ordinary (.integer signed 1 none)
        (by cases signed <;> decide) (.int 0 0) (.lit 0)
        (by cases signed <;> decide) trivial (.literal 0 0)
      exact ⟨1, none, args, rfl, written, erf⟩
  | true =>
      obtain ⟨args, written, erf⟩ := reachableArgs integerTypeUse (scalarType_am_ort integerTypeUse)
        platform start scalarName ordinary (.integer signed 1 (some (0, 0)))
        (by cases signed <;> decide) (.int 0 0) (.lit 0)
        (by cases signed <;> decide) trivial (.literal 0 0)
      exact ⟨1, some (0, 0), args, rfl, written, erf⟩

private theorem boolTypeRegistry : BoolTypeRegistryAussage :=
  ⟨boolTypeDerivation, scalarTypeUseAussage boolTypeUse, boolTypeErfuellbarAm⟩

private theorem integerTypeRegistry : IntegerTypeRegistryAussage :=
  ⟨integerTypeDerivation, scalarTypeUseAussage integerTypeUse, integerTypeErfuellbarAm⟩

public theorem boolTypeEntry : RegistryPacketProof ``WrittenType.bool BoolTypeRegistryAussage :=
  ⟨boolTypeRegistry⟩

public theorem integerTypeEntry : RegistryPacketProof ``WrittenType.integer IntegerTypeRegistryAussage :=
  ⟨integerTypeRegistry⟩

end Gabbro.Core.Ast.Semantik
