/-
  File:      core/Core/Ziel/Korrektheit/Beweise2/FormBelegBasis.lean
  Subject:   A TYPED form certificate for the complete registered base family of `Expr` constructors
             (the eleven rows of `Waechter/Check.lean`: lit, binary, trueLit, falseLit, variable,
             negativeLit, neg, not, div, compare, logic). The aggregate and text constructors of
             `Expr` are deliberately NOT in this base family; that gap is proved explicitly below.

  The global registry evidence in `BegleitZusammensetzung.lean` (`beleg`, `beleg_gedeckt`) is the
  Unit placeholder: it does not distinguish forms. This module does NOT replace that placeholder
  and does not touch `R₀`, any Zielsatz or a pin. It adds a separate certificate whose `Form` is a
  real inductive indexed by the eleven registered base constructors, proves `FormenGedecktAussage`
  for it with accepted source units, and proves that each form is backed by an existing typed
  `RegistryEntry` of the root-imported `exprSchema` family together with its joint satisfiability
  statement. All evidence is reused: source parse via `Ast.parse_print`, elaboration and admission
  via `elab_korrekt`/`zugelassen`, acceptance via the guard analysis (`waechterAbstrakt`) or the
  guard-free-fragment rule, and the occurrence via the elaborated code of the unit. Acceptance is
  additionally transported to the concrete source notion `Annahme.Quelle.Akzeptiert` along
  `akzeptiert_elaboriert_iff`, the equivalence the frame `R₀` actually uses.
-/
module

public import Core.Ziel.Korrektheit.Zusammensetzung
public import Core.Ziel.Korrektheit.Waechter.WaechterAbstrakt
public import Core.Ast.Semantik.Beispiele

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core
open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Katalog
open Gabbro.Core.Waechter
open Gabbro.Core.Ziel.Korrektheit.WaechterAnalyse

/-- The registered base family: exactly the eleven `Expr` constructors that `Waechter/Check.lean`
    lists under `exprSchema`. Each has complete Parse/Elaboriert/Realisiert/locality/satisfiability
    evidence in the root build. -/
inductive BasisForm where
  | lit
  | binary
  | trueLit
  | falseLit
  | variable
  | negativeLit
  | neg
  | not
  | div
  | compare
  | logic

/-- A reserved ordinary name for the single constant of a witness unit. -/
def basisName : Identifier :=
  keywordName 'x' [] (by decide) (fun _ member => (List.not_mem_nil member).elim)

theorem basisName_ordinary : ordinaryLocal basisName :=
  (directName_of_singleton (name := basisName) rfl).1

/-- A source unit whose only declaration computes one base-family expression. The `variable` form needs
    a preceding constant so that its local reference has a binding to resolve to. -/
def basisUnit : BasisForm → Ast.Unit
  | .lit =>
      let written : WrittenType := .integer false 8 none
      let value : Expr [] (.int 1 1) := .lit 1
      ⟨[⟨basisName, .int 0 255, false, true⟩],
        .step (.constant basisName basisName_ordinary written
          (by
            change 1 ≤ 8 ∧ 8 ≤ 64 ∧ (0 : Int) ≤ 0 ∧ (0 : Int) ≤ 255 ∧ (255 : Int) ≤ 255
            omega) value
          (by trivial)
          (by
            change (0 : Int) ≤ 1 ∧ (1 : Int) ≤ 255
            omega)) .done⟩
  | .binary =>
      let written : WrittenType := .integer false 8 none
      let value : Expr [] (.int 3 3) := .binary .add (.lit 1) (.lit 2)
      ⟨[⟨basisName, .int 0 255, false, true⟩],
        .step (.constant basisName basisName_ordinary written
          (by
            change 1 ≤ 8 ∧ 8 ≤ 64 ∧ (0 : Int) ≤ 0 ∧ (0 : Int) ≤ 255 ∧ (255 : Int) ≤ 255
            omega) value
          (by trivial)
          (by
            change (0 : Int) ≤ 3 ∧ (3 : Int) ≤ 255
            omega)) .done⟩
  | .trueLit =>
      let value : Expr [] .bool := .trueLit
      ⟨[⟨basisName, .bool, false, true⟩],
        .step (.constant basisName basisName_ordinary .bool trivial value
          (by trivial) (by trivial)) .done⟩
  | .falseLit =>
      let value : Expr [] .bool := .falseLit
      ⟨[⟨basisName, .bool, false, true⟩],
        .step (.constant basisName basisName_ordinary .bool trivial value
          (by trivial) (by trivial)) .done⟩
  | .variable =>
      let b0 : Binding := ⟨basisName, .int 0 255, false, true⟩
      let ref : Local [b0] (.int 0 255) := .here
      let value : Expr [b0] (.int 0 255) := .variable ref ⟨trivial, trivial⟩ basisName_ordinary
      ⟨[⟨basisName, .int 0 255, false, true⟩, ⟨basisName, .int 0 255, false, true⟩],
        .step (.constant basisName basisName_ordinary (.integer false 8 none)
          (by change 1 ≤ 8 ∧ 8 ≤ 64 ∧ (0 : Int) ≤ 0 ∧ (0 : Int) ≤ 255 ∧ (255 : Int) ≤ 255; omega)
          (.lit 1) (by trivial) (by change (0 : Int) ≤ 1 ∧ (1 : Int) ≤ 255; omega))
        (.step (.constant basisName basisName_ordinary (.integer false 8 none)
          (by change 1 ≤ 8 ∧ 8 ≤ 64 ∧ (0 : Int) ≤ 0 ∧ (0 : Int) ≤ 255 ∧ (255 : Int) ≤ 255; omega) value
          (by trivial) (by change (0 : Int) ≤ 0 ∧ (255 : Int) ≤ 255; omega)) .done)⟩
  | .negativeLit =>
      let value : Expr [] (.int (-1) (-1)) := .negativeLit 1
      ⟨[⟨basisName, .int (-128) 127, false, true⟩],
        .step (.constant basisName basisName_ordinary (.integer true 8 none)
          (by change 1 ≤ 8 ∧ 8 ≤ 64 ∧ (-128 : Int) ≤ -128 ∧ (-128 : Int) ≤ 127 ∧ (127 : Int) ≤ 127; omega)
          value (by trivial) (by change (-128 : Int) ≤ -1 ∧ (-1 : Int) ≤ 127; omega)) .done⟩
  | .neg =>
      let value : Expr [] (.int (-1) (-1)) := .neg (.lit 1)
      ⟨[⟨basisName, .int (-128) 127, false, true⟩],
        .step (.constant basisName basisName_ordinary (.integer true 8 none)
          (by change 1 ≤ 8 ∧ 8 ≤ 64 ∧ (-128 : Int) ≤ -128 ∧ (-128 : Int) ≤ 127 ∧ (127 : Int) ≤ 127; omega)
          value (by trivial) (by change (-128 : Int) ≤ -1 ∧ (-1 : Int) ≤ 127; omega)) .done⟩
  | .not =>
      let value : Expr [] .bool := .not .trueLit
      ⟨[⟨basisName, .bool, false, true⟩],
        .step (.constant basisName basisName_ordinary .bool trivial value
          (by trivial) (by trivial)) .done⟩
  | .div =>
      let value : Expr [] (.int 0 4) := .div (.lit 4) (.lit 2) (Or.inl (by omega))
      ⟨[⟨basisName, .int 0 255, false, true⟩],
        .step (.constant basisName basisName_ordinary (.integer false 8 none)
          (by change 1 ≤ 8 ∧ 8 ≤ 64 ∧ (0 : Int) ≤ 0 ∧ (0 : Int) ≤ 255 ∧ (255 : Int) ≤ 255; omega)
          value (by trivial) (by change (0 : Int) ≤ 0 ∧ (4 : Int) ≤ 255; omega)) .done⟩
  | .compare =>
      let value : Expr [] .bool := .compare .lt (.lit 1) (.lit 2)
      ⟨[⟨basisName, .bool, false, true⟩],
        .step (.constant basisName basisName_ordinary .bool trivial value
          (by trivial) (by trivial)) .done⟩
  | .logic =>
      let value : Expr [] .bool := .logic .and .trueLit .falseLit
      ⟨[⟨basisName, .bool, false, true⟩],
        .step (.constant basisName basisName_ordinary .bool trivial value
          (by trivial) (by trivial)) .done⟩

/-- The elaborated code of each witness unit, used for admission, acceptance and occurrence. -/
theorem basisUnit_code_lit :
    (fragment Ast.Category.unit (basisUnit .lit)).code =
      [.literal 0 1, .bindeWert 0 (.int 0 255) true, .starte Ast.Semantik.mainName, .ende] := rfl

theorem basisUnit_code_binary :
    (fragment Ast.Category.unit (basisUnit .binary)).code =
      [.literal 0 1, .literal 1 2, .binaer .add 0,
        .bindeWert 0 (.int 0 255) true, .starte Ast.Semantik.mainName, .ende] := rfl

theorem basisUnit_code_trueLit :
    (fragment Ast.Category.unit (basisUnit .trueLit)).code =
      [.wahrheitswert 0 true, .bindeWert 0 .bool true, .starte Ast.Semantik.mainName, .ende] := rfl

theorem basisUnit_code_falseLit :
    (fragment Ast.Category.unit (basisUnit .falseLit)).code =
      [.wahrheitswert 0 false, .bindeWert 0 .bool true, .starte Ast.Semantik.mainName, .ende] := rfl

theorem basisUnit_code_variable :
    (fragment Ast.Category.unit (basisUnit .variable)).code =
      [.literal 0 1, .bindeWert 0 (.int 0 255) true, .lesen 0 0,
        .bindeWert 0 (.int 0 255) true, .starte Ast.Semantik.mainName, .ende] := rfl

theorem basisUnit_code_negativeLit :
    (fragment Ast.Category.unit (basisUnit .negativeLit)).code =
      [.negativ 0 1, .bindeWert 0 (.int (-128) 127) true,
        .starte Ast.Semantik.mainName, .ende] := rfl

theorem basisUnit_code_neg :
    (fragment Ast.Category.unit (basisUnit .neg)).code =
      [.literal 0 1, .negieren 0, .bindeWert 0 (.int (-128) 127) true,
        .starte Ast.Semantik.mainName, .ende] := rfl

theorem basisUnit_code_not :
    (fragment Ast.Category.unit (basisUnit .not)).code =
      [.wahrheitswert 0 true, .verneinen 0, .bindeWert 0 .bool true,
        .starte Ast.Semantik.mainName, .ende] := rfl

theorem basisUnit_code_div :
    (fragment Ast.Category.unit (basisUnit .div)).code =
      [.literal 0 4, .literal 1 2, .teilen 0, .bindeWert 0 (.int 0 255) true,
        .starte Ast.Semantik.mainName, .ende] := rfl

theorem basisUnit_code_compare :
    (fragment Ast.Category.unit (basisUnit .compare)).code =
      [.literal 0 1, .literal 1 2, .vergleichen .lt 0, .bindeWert 0 .bool true,
        .starte Ast.Semantik.mainName, .ende] := rfl

theorem basisUnit_code_logic :
    (fragment Ast.Category.unit (basisUnit .logic)).code =
      [.wahrheitswert 0 true, .springeWenn 0 false 2, .wahrheitswert 0 false,
        .bindeWert 0 .bool true, .starte Ast.Semantik.mainName, .ende] := rfl

/-- The witness units declare no environment interface, hence no catalogue row is needed for admission. -/
private theorem basisUnit_environmentAllowed (f : BasisForm) (P : Plattform) :
    (fragment Ast.Category.unit (basisUnit f)).environmentAllowed P.katalog := by
  cases f <;>
    simp only [Fragment.environmentAllowed, Fragment.environment] <;>
    first
    | rw [basisUnit_code_lit]
    | rw [basisUnit_code_binary]
    | rw [basisUnit_code_trueLit]
    | rw [basisUnit_code_falseLit]
    | rw [basisUnit_code_variable]
    | rw [basisUnit_code_negativeLit]
    | rw [basisUnit_code_neg]
    | rw [basisUnit_code_not]
    | rw [basisUnit_code_div]
    | rw [basisUnit_code_compare]
    | rw [basisUnit_code_logic]
  all_goals
    simp only [List.filterMap_cons, List.filterMap_nil]
    exact ⟨List.nodup_nil, fun e present => (List.not_mem_nil present).elim⟩

/-- Each witness unit is admitted on every platform: its code is frame-only and its types are
    platform-independent. -/
theorem basisUnit_zugelassen (f : BasisForm) (P : Plattform) :
    Ast.Semantik.zugelassen P Ast.Category.unit (basisUnit f) := by
  change (fragment Ast.Category.unit (basisUnit f)).environmentAllowed P.katalog ∧
    (fragment Ast.Category.unit (basisUnit f)).code.all (Befehl.platformAllowed P) = true
  refine ⟨basisUnit_environmentAllowed f P, ?_⟩
  cases f <;>
    first
    | rw [basisUnit_code_lit]
    | rw [basisUnit_code_binary]
    | rw [basisUnit_code_trueLit]
    | rw [basisUnit_code_falseLit]
    | rw [basisUnit_code_variable]
    | rw [basisUnit_code_negativeLit]
    | rw [basisUnit_code_neg]
    | rw [basisUnit_code_not]
    | rw [basisUnit_code_div]
    | rw [basisUnit_code_compare]
    | rw [basisUnit_code_logic]
  all_goals
    simp only [Befehl.platformAllowed, platformType, List.all_cons, List.all_nil, Bool.true_and]

/-- Every instruction of a witness code is frame-only. -/
private theorem basisUnit_rein (f : BasisForm) :
    ∀ b ∈ (fragment Ast.Category.unit (basisUnit f)).code, b.Privat := by
  cases f <;>
    first
    | rw [basisUnit_code_lit]
    | rw [basisUnit_code_binary]
    | rw [basisUnit_code_trueLit]
    | rw [basisUnit_code_falseLit]
    | rw [basisUnit_code_variable]
    | rw [basisUnit_code_negativeLit]
    | rw [basisUnit_code_neg]
    | rw [basisUnit_code_not]
    | rw [basisUnit_code_div]
    | rw [basisUnit_code_compare]
    | rw [basisUnit_code_logic]
  all_goals
    intro b present
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Befehl.Privat, Befehl.klasse]

/-- The static guard verdict accepts every witness code (the division witness has a nonzero literal
    divisor, so the checker discharges its generated guard). -/
private theorem basisUnit_guarded (f : BasisForm) :
    waechterPruefeCode (fragment Ast.Category.unit (basisUnit f)).code = true := by
  cases f <;>
    first
    | rw [basisUnit_code_lit]
    | rw [basisUnit_code_binary]
    | rw [basisUnit_code_trueLit]
    | rw [basisUnit_code_falseLit]
    | rw [basisUnit_code_variable]
    | rw [basisUnit_code_negativeLit]
    | rw [basisUnit_code_neg]
    | rw [basisUnit_code_not]
    | rw [basisUnit_code_div]
    | rw [basisUnit_code_compare]
    | rw [basisUnit_code_logic]
  all_goals rfl

/-- A fragment with empty clauses, frame-only code and a passing guard analysis yields a fully accepted
    unit. The clause component is discharged because every witness unit carries no written clauses. -/
private theorem basisAkzeptiert (p : Fragment) (P : Plattform)
    (clauses : p.klauseln = .leer) (rein : ∀ b ∈ p.code, b.Privat)
    (guarded : waechterPruefeCode p.code = true) :
    Annahme.Akzeptiert (p.einheit P) := by
  refine ⟨p.lokal_rahmen P rein, ?_, waechterAbstrakt p P guarded⟩
  intro run conforms
  change (∀ pred ∈ p.klauseln.voraus, _) ∧
    (∀ _ : Maschine.I.Schnitt (p.einheit P) run, ∀ pred ∈ p.klauseln.invariant, _) ∧
    ∀ _ : Maschine.I.Schnitt (p.einheit P) run, _ → ∀ pred ∈ p.klauseln.sicher, _
  rw [clauses]
  exact ⟨fun _ h => (List.not_mem_nil h).elim,
    fun _ _ h => (List.not_mem_nil h).elim,
    fun _ _ _ h => (List.not_mem_nil h).elim⟩

/-- Each witness unit is accepted on every platform. -/
theorem basisUnit_akzeptiert (f : BasisForm) (P : Plattform) :
    Annahme.Akzeptiert (einheitVon P (basisUnit f)) := by
  let p := fragment Ast.Category.unit (basisUnit f)
  change Annahme.Akzeptiert (p.einheit P)
  exact basisAkzeptiert p P rfl (basisUnit_rein f) (basisUnit_guarded f)

/-- The concrete source acceptance the frame `R₀` actually uses agrees with the acceptance statement of
    `FormenGedecktAussage` on every witness unit, by `akzeptiert_elaboriert_iff`. -/
theorem basisUnit_quellAkzeptiert (f : BasisForm) (P : Plattform) :
    Annahme.Quelle.Akzeptiert (einheitVon P (basisUnit f)) := by
  exact (Annahme.Quelle.akzeptiert_elaboriert_iff P (basisUnit f)).2 (basisUnit_akzeptiert f P)

/-- The typed form certificate: a form occurs through the printed source unit of its family, and
    its realisation is that exact unit's elaboration. -/
def basisBeleg : FormBeleg where
  Form := BasisForm
  enthaelt a f := a = Ast.print (category := Ast.Category.unit) (basisUnit f)
  realisiert f a E := a = Ast.print (category := Ast.Category.unit) (basisUnit f) ∧
    E = einheitVon Plattform.x86_64 (basisUnit f)

/-- Every form of the family occurs in an accepted source unit and is realised there: the form
    coverage leg (`FormenGedecktAussage`) holds for the typed certificate. -/
theorem basisBeleg_gedeckt : FormenGedecktAussage Plattform.x86_64 basisBeleg := by
  intro f
  refine ⟨Ast.print (category := Ast.Category.unit) (basisUnit f),
    einheitVon Plattform.x86_64 (basisUnit f), ?_, ?_, ?_, ?_⟩
  · rfl
  · exact ⟨basisUnit f, Ast.parse_print (category := Ast.Category.unit) (basisUnit f),
      ⟨rfl, basisUnit_zugelassen f Plattform.x86_64⟩⟩
  · exact basisUnit_akzeptiert f Plattform.x86_64
  · exact ⟨rfl, rfl⟩

/-- The same coverage under the concrete source acceptance that `R₀` binds as its `Akzeptiert` field:
    the equivalence `akzeptiert_elaboriert_iff` turns each witness's guard acceptance into the
    source-provenance acceptance of the goal frame. -/
theorem basisBeleg_gedeckt_quell :
    ∀ f : BasisForm, ∃ (a : Text.RawText) (E : Ast.Semantik.Einheit),
      basisBeleg.enthaelt a f ∧ Ast.Semantik.Bezeichnet Plattform.x86_64 Ast.Category.unit a E ∧
        Annahme.Quelle.Akzeptiert E ∧ basisBeleg.realisiert f a E := by
  intro f
  refine ⟨Ast.print (category := Ast.Category.unit) (basisUnit f),
    einheitVon Plattform.x86_64 (basisUnit f), ?_, ?_, ?_, ?_⟩
  · rfl
  · exact ⟨basisUnit f, Ast.parse_print (category := Ast.Category.unit) (basisUnit f),
      ⟨rfl, basisUnit_zugelassen f Plattform.x86_64⟩⟩
  · exact basisUnit_quellAkzeptiert f Plattform.x86_64
  · exact ⟨rfl, rfl⟩

/-- The family is genuinely backed by the existing registry: each form maps to a constructor of the
    root-imported `Expr` family whose complete typed `RegistryEntry` is already registered. -/
def basisFormConstructor : BasisForm → Lean.Name
  | .lit => ``Expr.lit
  | .binary => ``Expr.binary
  | .trueLit => ``Expr.trueLit
  | .falseLit => ``Expr.falseLit
  | .variable => ``Expr.variable
  | .negativeLit => ``Expr.negativeLit
  | .neg => ``Expr.neg
  | .not => ``Expr.not
  | .div => ``Expr.div
  | .compare => ``Expr.compare
  | .logic => ``Expr.logic

theorem basisForm_registry_covered (f : BasisForm) :
    Nonempty (RegistryEntry (basisFormConstructor f) (exprSchema (basisFormConstructor f))) := by
  cases f
  · exact ⟨literalEntry⟩
  · exact ⟨binaryEntry⟩
  · exact ⟨trueLitEntry⟩
  · exact ⟨falseLitEntry⟩
  · exact ⟨variableEntry⟩
  · exact ⟨negativeLitEntry⟩
  · exact ⟨negEntry⟩
  · exact ⟨notValueEntry⟩
  · exact ⟨divisionEntry⟩
  · exact ⟨comparisonEntry⟩
  · exact ⟨logicEntry⟩

/-- The registry's joint satisfiability statements are inhabited by the existing form proofs, so
    the premises of every rule in each entry hold together. -/
theorem basisForm_jointlySatisfiable (f : BasisForm) :
    Nonempty (match f with
      | .lit => LiteralErfuellbar
      | .binary => BinaryErfuellbar
      | .trueLit => trueLitJoint
      | .falseLit => falseLitJoint
      | .variable => variableJoint
      | .negativeLit => negativeLitJoint
      | .neg => negJoint
      | .not => notValueJoint
      | .div => divisionJoint
      | .compare => comparisonJoint
      | .logic => logicJoint) := by
  cases f
  · exact ⟨literal_erfuellbar⟩
  · exact ⟨binary_erfuellbar⟩
  · exact ⟨trueLit_erfuellbar⟩
  · exact ⟨falseLit_erfuellbar⟩
  · exact ⟨variable_erfuellbar⟩
  · exact ⟨negativeLit_erfuellbar⟩
  · exact ⟨neg_erfuellbar⟩
  · exact ⟨notValue_erfuellbar⟩
  · exact ⟨division_erfuellbar⟩
  · exact ⟨comparison_erfuellbar⟩
  · exact ⟨logic_erfuellbar⟩

/-- The form's instruction occurs in the witness unit's code at the exact linearisation position
    that the registry entry assigns to it. This is the unit-level counterpart of `Quellform.Realisiert`. -/
theorem basisUnit_occurrence (f : BasisForm) :
    match f with
    | .lit => (fragment Ast.Category.unit (basisUnit f)).code[0]? = some (.literal 0 1)
    | .binary => (fragment Ast.Category.unit (basisUnit f)).code[2]? = some (.binaer .add 0)
    | .trueLit => (fragment Ast.Category.unit (basisUnit f)).code[0]? = some (.wahrheitswert 0 true)
    | .falseLit => (fragment Ast.Category.unit (basisUnit f)).code[0]? = some (.wahrheitswert 0 false)
    | .variable => (fragment Ast.Category.unit (basisUnit f)).code[2]? = some (.lesen 0 0)
    | .negativeLit => (fragment Ast.Category.unit (basisUnit f)).code[0]? = some (.negativ 0 1)
    | .neg => (fragment Ast.Category.unit (basisUnit f)).code[1]? = some (.negieren 0)
    | .not => (fragment Ast.Category.unit (basisUnit f)).code[1]? = some (.verneinen 0)
    | .div => (fragment Ast.Category.unit (basisUnit f)).code[2]? = some (.teilen 0)
    | .compare => (fragment Ast.Category.unit (basisUnit f)).code[2]? = some (.vergleichen .lt 0)
    | .logic => (fragment Ast.Category.unit (basisUnit f)).code[1]? = some (.springeWenn 0 false 2) := by
  cases f <;>
    first
    | rw [basisUnit_code_lit]
    | rw [basisUnit_code_binary]
    | rw [basisUnit_code_trueLit]
    | rw [basisUnit_code_falseLit]
    | rw [basisUnit_code_variable]
    | rw [basisUnit_code_negativeLit]
    | rw [basisUnit_code_neg]
    | rw [basisUnit_code_not]
    | rw [basisUnit_code_div]
    | rw [basisUnit_code_compare]
    | rw [basisUnit_code_logic]
  all_goals rfl

/-- The missing constructor ranges, proved explicitly: the thirteen `Expr` constructors outside the
    registered base family are aggregate, record, variant, text and option forms. None of them is a
    member of `BasisForm`, so this certificate does not claim to cover them. -/
theorem basisForm_nicht_arrayValue (f : BasisForm) : basisFormConstructor f ≠ ``Expr.arrayValue := by
  cases f <;> simp [basisFormConstructor, Lean.Name.str.injEq, String.reduceEq]
theorem basisForm_nicht_arrayIndex (f : BasisForm) : basisFormConstructor f ≠ ``Expr.arrayIndex := by
  cases f <;> simp [basisFormConstructor, Lean.Name.str.injEq, String.reduceEq]
theorem basisForm_nicht_tupleValue (f : BasisForm) : basisFormConstructor f ≠ ``Expr.tupleValue := by
  cases f <;> simp [basisFormConstructor, Lean.Name.str.injEq, String.reduceEq]
theorem basisForm_nicht_tupleField (f : BasisForm) : basisFormConstructor f ≠ ``Expr.tupleField := by
  cases f <;> simp [basisFormConstructor, Lean.Name.str.injEq, String.reduceEq]
theorem basisForm_nicht_recordValue (f : BasisForm) : basisFormConstructor f ≠ ``Expr.recordValue := by
  cases f <;> simp [basisFormConstructor, Lean.Name.str.injEq, String.reduceEq]
theorem basisForm_nicht_recordField (f : BasisForm) : basisFormConstructor f ≠ ``Expr.recordField := by
  cases f <;> simp [basisFormConstructor, Lean.Name.str.injEq, String.reduceEq]
theorem basisForm_nicht_variantValue (f : BasisForm) : basisFormConstructor f ≠ ``Expr.variantValue := by
  cases f <;> simp [basisFormConstructor, Lean.Name.str.injEq, String.reduceEq]
theorem basisForm_nicht_textLiteral (f : BasisForm) : basisFormConstructor f ≠ ``Expr.textLiteral := by
  cases f <;> simp [basisFormConstructor, Lean.Name.str.injEq, String.reduceEq]
theorem basisForm_nicht_textConcat (f : BasisForm) : basisFormConstructor f ≠ ``Expr.textConcat := by
  cases f <;> simp [basisFormConstructor, Lean.Name.str.injEq, String.reduceEq]
theorem basisForm_nicht_textIndex (f : BasisForm) : basisFormConstructor f ≠ ``Expr.textIndex := by
  cases f <;> simp [basisFormConstructor, Lean.Name.str.injEq, String.reduceEq]
theorem basisForm_nicht_substring (f : BasisForm) : basisFormConstructor f ≠ ``Expr.substring := by
  cases f <;> simp [basisFormConstructor, Lean.Name.str.injEq, String.reduceEq]
theorem basisForm_nicht_textLength (f : BasisForm) : basisFormConstructor f ≠ ``Expr.textLength := by
  cases f <;> simp [basisFormConstructor, Lean.Name.str.injEq, String.reduceEq]
theorem basisForm_nicht_optionIsSome (f : BasisForm) : basisFormConstructor f ≠ ``Expr.optionIsSome := by
  cases f <;> simp [basisFormConstructor, Lean.Name.str.injEq, String.reduceEq]

end Gabbro.Core.Ziel.Korrektheit
