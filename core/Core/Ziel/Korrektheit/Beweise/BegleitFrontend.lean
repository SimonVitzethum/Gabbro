/-
  File:      core/Core/Ziel/Korrektheit/Beweise/BegleitFrontend.lean
  Subject:   COMPANION LEMMAS for the pinned statements of `Core/Ziel/Korrektheit/Frontend.lean`
             (front-end correctness): for every `…Aussage` an `X.erfuellbar` (the premises hold
             jointly, or the proved statement itself) and an `X.nichtTrivial` (the statement is
             non-empty: a parse, denotation or admitted form exists, or a degenerate
             printer/parser violates it). No statement is changed.
-/
module

public import Core.Ziel.Korrektheit.Frontend
public import Core.Ast.Semantik.Formbeweise

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core
open Classical

/-- The empty source unit: no declarations. Its printed text and its elaboration are the canonical
    witnesses below. -/
def leereUnit : Ast.Unit := ⟨[], Ast.UnitBody.done⟩

/-- The empty unit is admitted by every platform: it selects no environment and its two boot
    instructions are platform-allowed. Feeds: `Befehl.platformAllowed`, `Fragment.anhaengen`. -/
theorem leereUnit_zugelassen (P : Katalog.Plattform) :
    Ast.Semantik.zugelassen P Ast.Category.unit leereUnit := by
  constructor
  · exact ⟨List.nodup_nil, fun e mem => (List.not_mem_nil mem).elim⟩
  · change (Ast.Semantik.programm leereUnit).code.all (Ast.Semantik.Befehl.platformAllowed P) = true
    simp only [Ast.Semantik.programm, leereUnit, Ast.Semantik.unitBody, Ast.Semantik.Fragment.leer,
      Ast.Semantik.Fragment.anhaengen, Ast.Semantik.Fragment.einzel, List.append_nil,
      List.nil_append, List.singleton_append, List.all_cons, List.all_nil,
      Ast.Semantik.Befehl.platformAllowed, Bool.true_and]

/-- The printed text of the empty unit denotes its elaboration on every platform. Feeds:
    `Ast.parse_print`, `leereUnit_zugelassen`. -/
theorem leereUnit_bezeichnet (P : Katalog.Plattform) :
    Ast.Semantik.Bezeichnet P Ast.Category.unit (Ast.print (category := Ast.Category.unit) leereUnit)
      (Ast.Semantik.elaborieren (category := Ast.Category.unit) P leereUnit) := by
  refine ⟨leereUnit, Ast.parse_print (category := Ast.Category.unit) leereUnit, ?_⟩
  exact ⟨rfl, leereUnit_zugelassen P⟩

/-- The premises of round-trip hold jointly: the proved statement itself. -/
theorem ParseDruckAussage.erfuellbar : ParseDruckAussage :=
  parse_druck

/-- Round-trip is non-empty: the empty unit parses from what is printed. Feeds: `Ast.parse_print`. -/
theorem ParseDruckAussage.nichtTrivial :
    ∃ t : Ast.Unit, Ast.Parse (category := Ast.Category.unit)
      (Ast.print (category := Ast.Category.unit) t) t :=
  ⟨leereUnit, Ast.parse_print (category := Ast.Category.unit) leereUnit⟩

/-- The premises of unambiguity hold jointly: the proved statement itself. -/
theorem ParseEindeutigAussage.erfuellbar : ParseEindeutigAussage :=
  parse_eindeutig

/-- Unambiguity is non-empty: some text has a tree, so uniqueness is not vacuous. Feeds:
    `Ast.parse_print`. -/
theorem ParseEindeutigAussage.nichtTrivial :
    ∃ (c : Ast.Category) (text : Text.RawText) (t : c.Tree), Ast.Parse text t :=
  ⟨Ast.Category.unit, Ast.print (category := Ast.Category.unit) leereUnit, leereUnit,
    Ast.parse_print (category := Ast.Category.unit) leereUnit⟩

/-- The premises of elaboration correctness hold jointly: the proved statement itself. -/
theorem ElabKorrektAussage.erfuellbar (P : Katalog.Plattform) : ElabKorrektAussage P :=
  elab_korrekt_vollstaendig P

/-- Elaboration correctness is non-empty: the empty unit elaborates to a unit. -/
theorem ElabKorrektAussage.nichtTrivial (P : Katalog.Plattform) :
    ∃ (c : Ast.Category) (t : c.Tree) (E : Ast.Semantik.Einheit),
      Ast.Semantik.Elaboriert P t E :=
  ⟨Ast.Category.unit, leereUnit, Ast.Semantik.elaborieren (category := Ast.Category.unit) P leereUnit, rfl⟩

/-- The premises of denotational functionality hold jointly: the proved statement itself. -/
theorem BezeichnetFunktionalAussage.erfuellbar (P : Katalog.Plattform) :
    BezeichnetFunktionalAussage P :=
  bezeichnet_funktional P

/-- Functionality is non-empty: some text denotes a unit. Feeds: `leereUnit_bezeichnet`. -/
theorem BezeichnetFunktionalAussage.nichtTrivial (P : Katalog.Plattform) :
    ∃ (a : Text.RawText) (E : Ast.Semantik.Einheit),
      Ast.Semantik.Bezeichnet P Ast.Category.unit a E :=
  ⟨Ast.print (category := Ast.Category.unit) leereUnit, Ast.Semantik.elaborieren (category := Ast.Category.unit) P leereUnit, leereUnit_bezeichnet P⟩

/-- The premises of text well-formedness hold jointly: the proved statement itself. -/
theorem TextWohlgeformtAussage.erfuellbar (P : Katalog.Plattform) : TextWohlgeformtAussage P :=
  text_wohlgeformt P

/-- Well-formedness is non-empty: the printed empty unit is well formed. Feeds:
    `leereUnit_bezeichnet`, `text_wohlgeformt`. -/
theorem TextWohlgeformtAussage.nichtTrivial (P : Katalog.Plattform) :
    ∃ a : Text.RawText,
      Text.WohlgeformterText (Text.tokenGrammar (Ast.Category.reads Ast.Category.unit))
        (fun t => Ast.Semantik.zugelassen P Ast.Category.unit t) a := by
  refine ⟨Ast.print (category := Ast.Category.unit) leereUnit, ?_⟩
  exact (text_wohlgeformt P (Ast.print (category := Ast.Category.unit) leereUnit)).2
    ⟨Ast.Semantik.elaborieren (category := Ast.Category.unit) P leereUnit, leereUnit_bezeichnet P⟩

/-- The premises of the form-realisation statement hold jointly: the literal form places its
    instruction at its declared position. Feeds: `literalForm`, `literal_am_ort`. -/
theorem RealisiertAlleFormenAussage.erfuellbar :
    ∃ (category : Ast.Category) (Arguments : Type) (form : Ast.Semantik.Quellform category Arguments),
      form.RegelAmOrt :=
  ⟨Ast.Category.expression [], Nat, Ast.Semantik.literalForm [], Ast.Semantik.literal_am_ort []⟩

/-- The position premise is load-bearing: the same literal form with a different instruction at
    the declared position is not realised there. Feeds: `literal_am_ort`. -/
theorem RealisiertAlleFormenAussage.nichtTrivial :
    ∃ (category : Ast.Category) (Arguments : Type) (form : Ast.Semantik.Quellform category Arguments),
      ¬ form.RegelAmOrt := by
  let form : Ast.Semantik.Quellform (Ast.Category.expression []) Nat :=
    { Ast.Semantik.literalForm [] with befehl := fun value => Ast.Semantik.Befehl.literal 1 value }
  refine ⟨Ast.Category.expression [], Nat, form, ?_⟩
  intro position
  have h0 := position 0
  have horig := Ast.Semantik.literal_am_ort [] 0
  change ((Ast.Semantik.literalForm []).fragment 0).code[0]? = some (Ast.Semantik.Befehl.literal 0 0) at horig
  change ((Ast.Semantik.literalForm []).fragment 0).code[0]? = some (Ast.Semantik.Befehl.literal 1 0) at h0
  rw [horig] at h0
  cases h0

/-- A reference parser derived from `Ast.Parse` by a classical choice of witness. It agrees with
    the parse relation in both directions (`Ast.parse_deterministic` makes the choice unique). -/
noncomputable def parserAusParse : Parser :=
  ⟨fun a => if h : ∃ t : Ast.Unit, Ast.Parse (category := Ast.Category.unit) a t
    then some (Classical.choose h) else none⟩

theorem parserAusParse_korrekt : ParserKorrektAussage parserAusParse := by
  intro a t
  constructor
  · intro h
    dsimp [parserAusParse] at h
    split at h
    · rename_i existsTree
      cases h
      exact Classical.choose_spec existsTree
    · cases h
  · intro parsed
    dsimp [parserAusParse]
    split
    · rename_i existsTree
      congr
      exact Ast.parse_deterministic (Classical.choose_spec existsTree) parsed
    · rename_i noTree
      exact (noTree ⟨t, parsed⟩).elim

/-- The premises of parser correctness hold jointly: a parser agreeing with the reference
    relation is realisable, and it accepts the empty unit. -/
theorem ParserKorrektAussage.erfuellbar :
    ∃ π : Parser, ParserKorrektAussage π ∧ ∃ a t, π.parse a = some t := by
  refine ⟨parserAusParse, parserAusParse_korrekt, ?_⟩
  exact ⟨Ast.print (category := Ast.Category.unit) leereUnit, leereUnit,
    (parserAusParse_korrekt (Ast.print (category := Ast.Category.unit) leereUnit) leereUnit).2
      (Ast.parse_print (category := Ast.Category.unit) leereUnit)⟩

/-- Agreement is not a tautology: a parser that returns nothing violates it on the empty unit. -/
theorem ParserKorrektAussage.nichtTrivial : ∃ π : Parser, ¬ ParserKorrektAussage π := by
  let π : Parser := ⟨fun _ => none⟩
  refine ⟨π, ?_⟩
  intro agrees
  have parsed : Ast.Parse (category := Ast.Category.unit) (Ast.print (category := Ast.Category.unit) leereUnit) leereUnit :=
    Ast.parse_print (category := Ast.Category.unit) leereUnit
  have noneSome := (agrees (Ast.print (category := Ast.Category.unit) leereUnit) leereUnit).2 parsed
  change none = some leereUnit at noneSome
  cases noneSome

end Gabbro.Core.Ziel.Korrektheit
