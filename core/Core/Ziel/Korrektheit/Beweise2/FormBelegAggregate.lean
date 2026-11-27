/-
  File:      core/Core/Ziel/Korrektheit/Beweise2/FormBelegAggregate.lean
  Subject:   A TYPED, COMPOSABLE form certificate for the four aggregate `Expr` constructors
             (`Expr.arrayValue`, `Expr.arrayIndex`, `Expr.tupleValue`, `Expr.tupleField`). This is the
             next isolated M12 form-register part after the eleven scalar base forms of
             `FormBelegBasis.lean`. Each form gets its own source witness, admission and acceptance
             proof, a per-form registry and joint-satisfiability proof, a real occurrence at the
             registry's linearisation position, and the registry's stronger `ErfuellbarAm` evidence.
             Acceptance is transported to the concrete `Annahme.Quelle.Akzeptiert` the frame `R₀`
             binds. The static source checker's refusal of the value-dependent index guard is proved
             precisely, and the fully coverable literal-index case is carried by the certificate.

  This module does NOT replace the Unit placeholder `beleg` of `BegleitZusammensetzung.lean`, and it
  does not touch `R₀`, any Zielsatz, a pin or the root. It adds a separate composable certificate and
  proves that the union with `basisBeleg` stays covered.
-/
module

public import Core.Ziel.Korrektheit.Zusammensetzung
public import Core.Ziel.Korrektheit.Waechter.WaechterAbstrakt
public import Core.Ziel.Korrektheit.Beweise2.FormBelegBasisRegistry
public import Core.Ast.Inventory.Entries.Arrays
public import Core.Ast.Inventory.Entries.ArrayIndex
public import Core.Ast.Inventory.Entries.Tuples
public import Init.Omega

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core
open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Annahme
open Gabbro.Core.Katalog
open Gabbro.Core.Waechter
open Gabbro.Core.Ziel.Korrektheit.WaechterAnalyse

/-- The four aggregate expression forms, one constructor per registered inventory row. -/
inductive AggregatForm where
  | arrayValue
  | arrayIndex
  | tupleValue
  | tupleField

/-- A source unit whose only declaration computes one aggregate expression. The `arrayIndex` witness
    uses a literal index so the static guard check discharges at the registry's linearisation point. -/
def aggregatUnit : AggregatForm → Ast.Unit
  | .arrayValue =>
      let written : WrittenType := .array (.integer false 8 (some (1, 1))) 1
      let items : ExprItems [] [(.int 1 1)] := .next (.lit 1) .empty
      let value : Expr [] (.array (.int 1 1) 1) :=
        .arrayValue items rfl (fun i => by
          have bound : i.val < 1 := by simpa only [List.length_cons, List.length_nil, Nat.zero_add] using i.isLt
          have hi : i.val = 0 := by omega
          cases i with
          | mk val isLt =>
              simp only at hi
              subst val
              exact ⟨le_rfl, le_rfl⟩)
      ⟨[⟨basisName, written.type, false, true⟩],
        .step (.constant basisName basisName_ordinary written
          (by change 1 ≤ 8 ∧ 8 ≤ 64 ∧ (0 : Int) ≤ 1 ∧ (1 : Int) ≤ 1 ∧ (1 : Int) ≤ 255; omega)
          value (by trivial) rfl) .done⟩
  | .arrayIndex =>
      let written : WrittenType := .integer false 8 (some (5, 5))
      let base : Expr [] (.array (.int 5 5) 1) :=
        .arrayValue (.next (.lit 5) .empty) rfl (fun i => by
          have bound : i.val < 1 := by simpa only [List.length_cons, List.length_nil, Nat.zero_add] using i.isLt
          have hi : i.val = 0 := by omega
          cases i with
          | mk val isLt =>
              simp only at hi
              subst val
              exact ⟨le_rfl, le_rfl⟩)
      let value : Expr [] (.int 5 5) := .arrayIndex base (.lit 0) (by omega) (by omega)
      ⟨[⟨basisName, written.type, false, true⟩],
        .step (.constant basisName basisName_ordinary written
          (by change 1 ≤ 8 ∧ 8 ≤ 64 ∧ (0 : Int) ≤ 5 ∧ (5 : Int) ≤ 5 ∧ (5 : Int) ≤ 255; omega)
          value (by trivial) ⟨le_rfl, le_rfl⟩) .done⟩
  | .tupleValue =>
      let written : WrittenType :=
        .tuple (.integer false 8 (some (1, 1))) (.integer false 8 (some (2, 2))) .empty
      let value : Expr [] (tupleType [.int 1 1, .int 2 2]) := .tupleValue (.lit 1) (.lit 2) .empty
      ⟨[⟨basisName, written.type, false, true⟩],
        .step (.constant basisName basisName_ordinary written
          (by
            constructor
            · change 1 ≤ 8 ∧ 8 ≤ 64 ∧ (0 : Int) ≤ 1 ∧ (1 : Int) ≤ 1 ∧ (1 : Int) ≤ 255
              omega
            · constructor
              · change 1 ≤ 8 ∧ 8 ≤ 64 ∧ (0 : Int) ≤ 2 ∧ (2 : Int) ≤ 2 ∧ (2 : Int) ≤ 255
                omega
              · trivial) value (by trivial) rfl) .done⟩
  | .tupleField =>
      let written : WrittenType := .integer false 8 (some (1, 1))
      let base : Expr [] (tupleType [.int 1 1, .int 2 2]) := .tupleValue (.lit 1) (.lit 2) .empty
      let value : Expr [] (.int 1 1) := .tupleField base 0
      ⟨[⟨basisName, written.type, false, true⟩],
        .step (.constant basisName basisName_ordinary written
          (by change 1 ≤ 8 ∧ 8 ≤ 64 ∧ (0 : Int) ≤ 1 ∧ (1 : Int) ≤ 1 ∧ (1 : Int) ≤ 255; omega)
          value (by trivial) ⟨le_rfl, le_rfl⟩) .done⟩

/-- The elaborated code of each witness unit. -/
theorem aggregatUnit_code_arrayValue :
    (fragment Ast.Category.unit (aggregatUnit .arrayValue)).code =
      [.literal 0 1, .baueArray 0 (.int 1 1) 1,
        .bindeWert 0 (.array (.int 1 1) 1) true, .starte Ast.Semantik.mainName, .ende] := rfl

theorem aggregatUnit_code_arrayIndex :
    (fragment Ast.Category.unit (aggregatUnit .arrayIndex)).code =
      [.literal 0 5, .baueArray 0 (.int 5 5) 1, .literal 1 0, .liesArray 0 (.int 5 5) 1,
        .bindeWert 0 (.int 5 5) true, .starte Ast.Semantik.mainName, .ende] := rfl

theorem aggregatUnit_code_tupleValue :
    (fragment Ast.Category.unit (aggregatUnit .tupleValue)).code =
      [.literal 0 1, .literal 1 2, .baueTupel 0 [.int 1 1, .int 2 2],
        .bindeWert 0 (tupleType [.int 1 1, .int 2 2]) true,
        .starte Ast.Semantik.mainName, .ende] := rfl

theorem aggregatUnit_code_tupleField :
    (fragment Ast.Category.unit (aggregatUnit .tupleField)).code =
      [.literal 0 1, .literal 1 2, .baueTupel 0 [.int 1 1, .int 2 2],
        .liesTupelfeld 0 [.int 1 1, .int 2 2] 0, .bindeWert 0 (.int 1 1) true,
        .starte Ast.Semantik.mainName, .ende] := rfl

/-- The witness units declare no environment interface, hence no catalogue row is needed for admission. -/
private theorem aggregatUnit_environmentAllowed (f : AggregatForm) (P : Plattform) :
    (fragment Ast.Category.unit (aggregatUnit f)).environmentAllowed P.katalog := by
  cases f <;>
    simp only [Fragment.environmentAllowed, Fragment.environment] <;>
    first
    | rw [aggregatUnit_code_arrayValue]
    | rw [aggregatUnit_code_arrayIndex]
    | rw [aggregatUnit_code_tupleValue]
    | rw [aggregatUnit_code_tupleField]
  all_goals
    simp only [List.filterMap_cons, List.filterMap_nil]
    exact ⟨List.nodup_nil, fun e present => (List.not_mem_nil present).elim⟩

/-- Each witness unit is admitted on every platform: its code is frame-only and its types are
    platform-independent. -/
theorem aggregatUnit_zugelassen (f : AggregatForm) (P : Plattform) :
    Ast.Semantik.zugelassen P Ast.Category.unit (aggregatUnit f) := by
  change (fragment Ast.Category.unit (aggregatUnit f)).environmentAllowed P.katalog ∧
    (fragment Ast.Category.unit (aggregatUnit f)).code.all (Befehl.platformAllowed P) = true
  refine ⟨aggregatUnit_environmentAllowed f P, ?_⟩
  cases f <;>
    first
    | rw [aggregatUnit_code_arrayValue]
    | rw [aggregatUnit_code_arrayIndex]
    | rw [aggregatUnit_code_tupleValue]
    | rw [aggregatUnit_code_tupleField]
  all_goals
    simp only [Befehl.platformAllowed, platformType, tupleType, List.all_cons, List.all_nil, Bool.true_and]

/-- Every instruction of a witness code is frame-only. Each membership is reduced to an exact
    instruction equality, then discharged by the class of that instruction; no blanket simplification. -/
private theorem aggregatUnit_rein (f : AggregatForm) :
    ∀ b ∈ (fragment Ast.Category.unit (aggregatUnit f)).code, b.Privat := by
  cases f <;>
    first
    | rw [aggregatUnit_code_arrayValue]
    | rw [aggregatUnit_code_arrayIndex]
    | rw [aggregatUnit_code_tupleValue]
    | rw [aggregatUnit_code_tupleField]
  all_goals
    intro b present
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact Or.inl rfl | exact Or.inr (Or.inl rfl)

/-- The static guard verdict accepts every literal-index witness code: the array-read witness uses a
    literal zero offset, so the checker's endpoint analysis discharges the pinned index guard. -/
private theorem aggregatUnit_guarded (f : AggregatForm) :
    waechterPruefeCode (fragment Ast.Category.unit (aggregatUnit f)).code = true := by
  cases f <;>
    first
    | rw [aggregatUnit_code_arrayValue]
    | rw [aggregatUnit_code_arrayIndex]
    | rw [aggregatUnit_code_tupleValue]
    | rw [aggregatUnit_code_tupleField]
  all_goals rfl

/-- A fragment with empty clauses, frame-only code and a passing guard analysis yields a fully accepted
    unit; the clause component is discharged because every witness unit carries no written clauses. -/
private theorem aggregatAkzeptiert (p : Fragment) (P : Plattform)
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
theorem aggregatUnit_akzeptiert (f : AggregatForm) (P : Plattform) :
    Annahme.Akzeptiert (einheitVon P (aggregatUnit f)) := by
  let p := fragment Ast.Category.unit (aggregatUnit f)
  change Annahme.Akzeptiert (p.einheit P)
  exact aggregatAkzeptiert p P rfl (aggregatUnit_rein f) (aggregatUnit_guarded f)

/-- The concrete source acceptance the frame `R₀` binds agrees with the elaborated acceptance on every
    witness unit, by `akzeptiert_elaboriert_iff`. -/
theorem aggregatUnit_quellAkzeptiert (f : AggregatForm) (P : Plattform) :
    Annahme.Quelle.Akzeptiert (einheitVon P (aggregatUnit f)) := by
  exact (Annahme.Quelle.akzeptiert_elaboriert_iff P (aggregatUnit f)).2 (aggregatUnit_akzeptiert f P)

/-- The instruction that realises each form and the exact linearisation position the registry assigns
    to it. The occurrence below is at this position, not mere membership of the instruction in the code. -/
def aggregatBefehl : AggregatForm → Befehl
  | .arrayValue => .baueArray 0 (.int 1 1) 1
  | .arrayIndex => .liesArray 0 (.int 5 5) 1
  | .tupleValue => .baueTupel 0 [.int 1 1, .int 2 2]
  | .tupleField => .liesTupelfeld 0 [.int 1 1, .int 2 2] 0

def aggregatPosition : AggregatForm → Nat
  | .arrayValue => 1
  | .arrayIndex => 3
  | .tupleValue => 2
  | .tupleField => 3

theorem aggregatUnit_occurrence (f : AggregatForm) :
    (fragment Ast.Category.unit (aggregatUnit f)).code[aggregatPosition f]? = some (aggregatBefehl f) := by
  cases f <;>
    first
    | rw [aggregatUnit_code_arrayValue]
    | rw [aggregatUnit_code_arrayIndex]
    | rw [aggregatUnit_code_tupleValue]
    | rw [aggregatUnit_code_tupleField]
  all_goals rfl

/-- The typed, composable form certificate. Its realisation leg carries three things: the printed
    witness text, the denoted elaborated unit, the real occurrence at the registry position, and the
    registry's stronger joint-satisfiability evidence (`ErfuellbarAm`) for every external start. -/
def aggregatBeleg : FormBeleg where
  Form := AggregatForm
  enthaelt a f := a = Ast.print (category := Ast.Category.unit) (aggregatUnit f)
  realisiert f a E :=
    a = Ast.print (category := Ast.Category.unit) (aggregatUnit f) ∧
    E = einheitVon Plattform.x86_64 (aggregatUnit f) ∧
    (fragment Ast.Category.unit (aggregatUnit f)).code[aggregatPosition f]? = some (aggregatBefehl f) ∧
    ∀ start : AussenStart,
      match f with
      | .arrayValue => ∃ args, (arrayValueForm []).ErfuellbarAm Plattform.x86_64 start args
      | .arrayIndex => ∃ args, (arrayIndexForm []).ErfuellbarAm Plattform.x86_64 start args
      | .tupleValue => ∃ args, (tupleValueForm []).ErfuellbarAm Plattform.x86_64 start args
      | .tupleField => ∃ args, (tupleFieldForm []).ErfuellbarAm Plattform.x86_64 start args

/-- The registry's stronger realisation proofs are reused directly: at a state whose program counter
    sits at the form's linearisation point the form's instruction is at the head of the elaborated
    unit. This is the executed occurrence behind the exact-position code witness above, not mere
    membership of an instruction in a list. -/
theorem aggregatForm_realisiertAussage (f : AggregatForm) :
    match f with
    | .arrayValue => ArrayValueRealisiertAussage
    | .arrayIndex => ArrayIndexRealisiertAussage
    | .tupleValue => TupleValueRealisiertAussage
    | .tupleField => TupleFieldRealisiertAussage := by
  cases f
  · exact arrayValueRealisiert
  · exact arrayIndexRealisiert
  · exact tupleValue_realisiert
  · exact TupleFieldRealisiert

/-- The registry's joint-satisfiability statements are inhabited by the existing form proofs, so the
    premises of every rule in each entry hold together for every external start. -/
private theorem aggregatForm_erfuellbar (f : AggregatForm) (start : AussenStart) :
    match f with
    | .arrayValue => ∃ args, (arrayValueForm []).ErfuellbarAm Plattform.x86_64 start args
    | .arrayIndex => ∃ args, (arrayIndexForm []).ErfuellbarAm Plattform.x86_64 start args
    | .tupleValue => ∃ args, (tupleValueForm []).ErfuellbarAm Plattform.x86_64 start args
    | .tupleField => ∃ args, (tupleFieldForm []).ErfuellbarAm Plattform.x86_64 start args := by
  cases f
  · exact arrayValueErfuellbarAm Plattform.x86_64 start
  · exact arrayIndexErfuellbarAm Plattform.x86_64 start
  · exact tupleValue_erfuellbar Plattform.x86_64 start
  · exact TupleFieldErfuellbarAm Plattform.x86_64 start

/-- Every form occurs in an accepted source unit, is denoted there, is realised at its registry
    position and is backed by the registry's reachable-and-guarded evidence. -/
theorem aggregatBeleg_gedeckt : FormenGedecktAussage Plattform.x86_64 aggregatBeleg := by
  intro f
  refine ⟨Ast.print (category := Ast.Category.unit) (aggregatUnit f),
    einheitVon Plattform.x86_64 (aggregatUnit f), ?_, ?_, ?_, ?_⟩
  · rfl
  · exact ⟨aggregatUnit f, Ast.parse_print (category := Ast.Category.unit) (aggregatUnit f),
      ⟨rfl, aggregatUnit_zugelassen f Plattform.x86_64⟩⟩
  · exact aggregatUnit_akzeptiert f Plattform.x86_64
  · exact ⟨rfl, rfl, aggregatUnit_occurrence f, aggregatForm_erfuellbar f⟩

/-- The same coverage under the concrete source acceptance `R₀` binds as its `Akzeptiert` field. -/
theorem aggregatBeleg_gedeckt_quell :
    ∀ f : AggregatForm, ∃ (a : Text.RawText) (E : Ast.Semantik.Einheit),
      aggregatBeleg.enthaelt a f ∧ Ast.Semantik.Bezeichnet Plattform.x86_64 Ast.Category.unit a E ∧
        Annahme.Quelle.Akzeptiert E ∧ aggregatBeleg.realisiert f a E := by
  intro f
  refine ⟨Ast.print (category := Ast.Category.unit) (aggregatUnit f),
    einheitVon Plattform.x86_64 (aggregatUnit f), ?_, ?_, ?_, ?_⟩
  · rfl
  · exact ⟨aggregatUnit f, Ast.parse_print (category := Ast.Category.unit) (aggregatUnit f),
      ⟨rfl, aggregatUnit_zugelassen f Plattform.x86_64⟩⟩
  · exact aggregatUnit_quellAkzeptiert f Plattform.x86_64
  · exact ⟨rfl, rfl, aggregatUnit_occurrence f, aggregatForm_erfuellbar f⟩

/-- The family is genuinely backed by the existing registry: each form maps to a constructor whose
    complete typed `RegistryEntry` is already registered. -/
def aggregatFormConstructor : AggregatForm → Lean.Name
  | .arrayValue => ``Expr.arrayValue
  | .arrayIndex => ``Expr.arrayIndex
  | .tupleValue => ``Expr.tupleValue
  | .tupleField => ``Expr.tupleField

theorem aggregatForm_registry_covered (f : AggregatForm) :
    Nonempty (RegistryEntry (aggregatFormConstructor f) (exprSchema (aggregatFormConstructor f))) := by
  cases f
  · exact ⟨arrayValueEntry.entry⟩
  · exact ⟨arrayIndexEntry.entry⟩
  · exact ⟨tupleValueEntry.entry⟩
  · exact ⟨tupleFieldEntry.entry⟩

/-- The four forms are exactly the aggregate rows that lie outside the registered base family. None
    of them is a member of `BasisForm`, so the two certificates cover disjoint constructor ranges. -/
theorem basisForm_nicht_aggregat (f : BasisForm) :
    basisFormConstructor f ≠ ``Expr.arrayValue ∧ basisFormConstructor f ≠ ``Expr.arrayIndex ∧
      basisFormConstructor f ≠ ``Expr.tupleValue ∧ basisFormConstructor f ≠ ``Expr.tupleField := by
  exact ⟨basisForm_nicht_arrayValue f, basisForm_nicht_arrayIndex f,
    basisForm_nicht_tupleValue f, basisForm_nicht_tupleField f⟩

theorem aggregatForm_nicht_basis (f : AggregatForm) :
    aggregatFormConstructor f ≠ ``Expr.lit ∧ aggregatFormConstructor f ≠ ``Expr.binary ∧
      aggregatFormConstructor f ≠ ``Expr.trueLit ∧ aggregatFormConstructor f ≠ ``Expr.falseLit ∧
        aggregatFormConstructor f ≠ ``Expr.variable ∧ aggregatFormConstructor f ≠ ``Expr.negativeLit ∧
          aggregatFormConstructor f ≠ ``Expr.neg ∧ aggregatFormConstructor f ≠ ``Expr.not ∧
            aggregatFormConstructor f ≠ ``Expr.div ∧ aggregatFormConstructor f ≠ ``Expr.compare ∧
              aggregatFormConstructor f ≠ ``Expr.logic := by
  cases f <;> simp only [aggregatFormConstructor, ne_eq, Lean.Name.str.injEq, String.reduceEq,
    and_false, not_false_eq_true, and_self]

/-- Composability: two form certificates union to one whose coverage is the union of the two coverage
    legs. This joins the aggregate package to `basisBeleg` without touching the frame or the root. -/
def FormBeleg.summe (B₁ B₂ : FormBeleg) : FormBeleg where
  Form := Sum B₁.Form B₂.Form
  enthaelt a f := match f with | .inl f => B₁.enthaelt a f | .inr f => B₂.enthaelt a f
  realisiert f a E := match f with | .inl f => B₁.realisiert f a E | .inr f => B₂.realisiert f a E

theorem FormenGedecktAussage.summe (P : Katalog.Plattform) (B₁ B₂ : FormBeleg)
    (h₁ : FormenGedecktAussage P B₁) (h₂ : FormenGedecktAussage P B₂) :
    FormenGedecktAussage P (FormBeleg.summe B₁ B₂) := by
  intro f
  cases f with
  | inl f => exact h₁ f
  | inr f => exact h₂ f

theorem basisUndAggregatBeleg_gedeckt :
    FormenGedecktAussage Plattform.x86_64 (FormBeleg.summe basisBeleg aggregatBeleg) :=
  FormenGedecktAussage.summe Plattform.x86_64 basisBeleg aggregatBeleg
    basisBeleg_gedeckt aggregatBeleg_gedeckt

/-- THE STATIC-CHECKER GAP (index). A source unit whose array read uses a value-dependent index cannot
    be accepted by the static guard analysis, even though the guard is actually satisfiable. The unit
    declares the offset as a constant binding, so the elaborated `.lesen` writes an unknown value into
    the operand slot; the flow-insensitive interval join therefore loses the constant and refuses the
    `.liesArray` guard. -/
def aggregatUnitArrayIndexVariabel : Ast.Unit :=
  let base : Expr [⟨basisName, .int 0 0, false, true⟩] (.array (.int 5 5) 1) :=
    .arrayValue (.next (.lit 5) .empty) rfl (fun i => by
      have bound : i.val < 1 := by simpa only [List.length_cons, List.length_nil, Nat.zero_add] using i.isLt
      have hi : i.val = 0 := by omega
      cases i with
      | mk val isLt =>
          simp only at hi
          subst val
          exact ⟨le_rfl, le_rfl⟩)
  let ref : Local [⟨basisName, .int 0 0, false, true⟩] (.int 0 0) := .here
  let index : Expr [⟨basisName, .int 0 0, false, true⟩] (.int 0 0) :=
    .variable ref ⟨trivial, trivial⟩ basisName_ordinary
  let value : Expr [⟨basisName, .int 0 0, false, true⟩] (.int 5 5) :=
    .arrayIndex base index (by omega) (by omega)
  ⟨[⟨basisName, .int 5 5, false, true⟩, ⟨basisName, .int 0 0, false, true⟩],
    .step (.constant basisName basisName_ordinary (.integer false 8 (some (0, 0)))
      (by change 1 ≤ 8 ∧ 8 ≤ 64 ∧ (0 : Int) ≤ 0 ∧ (0 : Int) ≤ 0 ∧ (0 : Int) ≤ 255; omega)
      (.lit 0) (by trivial) ⟨le_rfl, le_rfl⟩)
    (.step (.constant basisName basisName_ordinary (.integer false 8 (some (5, 5)))
      (by change 1 ≤ 8 ∧ 8 ≤ 64 ∧ (0 : Int) ≤ 5 ∧ (5 : Int) ≤ 5 ∧ (5 : Int) ≤ 255; omega)
      value (by trivial) ⟨le_rfl, le_rfl⟩) .done)⟩

theorem aggregatUnitArrayIndexVariabel_code :
    (fragment Ast.Category.unit aggregatUnitArrayIndexVariabel).code =
      [.literal 0 0, .bindeWert 0 (.int 0 0) true, .literal 0 5, .baueArray 0 (.int 5 5) 1,
        .lesen 1 0, .liesArray 0 (.int 5 5) 1, .bindeWert 0 (.int 5 5) true,
        .starte Ast.Semantik.mainName, .ende] := rfl

/-- Precise reason for the refusal: the operand slot of the `liesArray` is poisoned by the local read,
    so the joined integer environment is top and the checker has no bound with which to discharge the
    guard. -/
theorem aggregatUnitArrayIndexVariabel_umgebungInt :
    slotUnbekanntInt (fragment Ast.Category.unit aggregatUnitArrayIndexVariabel).code 1 = true ∧
      umgebungInt (fragment Ast.Category.unit aggregatUnitArrayIndexVariabel).code 1 = none := by
  rw [aggregatUnitArrayIndexVariabel_code]
  constructor <;> rfl

theorem aggregatUnitArrayIndexVariabel_nichtStatisch :
    waechterPruefeCode (fragment Ast.Category.unit aggregatUnitArrayIndexVariabel).code = false := by
  rw [aggregatUnitArrayIndexVariabel_code]
  rfl

/-- The gap is an incompleteness, not an unsafety: at the value-dependent occurrence the actual offset
    is the declared constant zero and the array holds one element, so the registry's pinned index guard
    is satisfied. The stronger registry evidence proves exactly this guard at a reachable state. -/
theorem aggregatUnitArrayIndexVariabel_guardErfuellbar : waechterBedarf .index (0, 1) := by
  change (0 : Nat) < 1
  omega

theorem aggregatUnitArrayIndexVariabel_registryBeleg :
    ∀ start : AussenStart, ∃ args, (arrayIndexForm []).ErfuellbarAm Plattform.x86_64 start args :=
  arrayIndexErfuellbarAm Plattform.x86_64

end Gabbro.Core.Ziel.Korrektheit
