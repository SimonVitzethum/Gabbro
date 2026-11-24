module

public import Core.Ast.Semantik.Beispiele

/-!
# Adding the meaning of a source constructor

Read the production and its exact AST indices in `Core.Ast`. This recipe covers the semantic
half of the registry. The syntax proof supplies the corresponding `Surface.Rule.Entry`.

## Statements owned by the language designer

1. Extend `expr`, `stmt`, `block` or `unitBody` at the actual constructor. Specify the
   child order, the local state each child receives and leaves, and the source occurrence's
   instruction index. Compose child fragments with `Fragment.anhaengen`. Written
   predicates go in `Quellklauseln` in source order. A new partial operation adds an
   operand type and a `waechterBedarf` case. Its use is collected from the pre-state
   at the source head, including when there is no hardware opportunity or successor.
2. Specify the concrete and ideal transitions separately. For an existing kind of local
   instruction, supply its `Befehl.auswerten` and `Befehl.guard` arms. The plan and successor
   are then given by `Befehl.ideal` and `Befehl.impl`. For a form with a different effect,
   specify its plan, precondition and successor in each relation. Use the shared machine
   protocol to commit memory, synchronization and outside events.
3. Name the linearisation point, before and after relations, local state relation and bound
   on private steps. For one atomic local step the before and after relations are empty,
   the state relation is equality and the bound is zero. Supply the occurrence's
   `Quellform` descriptor and register its schema against its actual constructor name.

The exact statement interface for the existing atomic local forms is
`Quellform.statements`. After substituting the new descriptor, its fields are

```lean
realization := .surface (∀ scope, (forms scope).ParseAussage)
  (∀ scope, (forms scope).ElaboriertAussage) (∀ scope, (forms scope).RealisiertAussage)
acceptanceRule := ∀ scope, (forms scope).AnnahmeAussage
idealRule := ∀ scope, (forms scope).IdealAussage
unitsAndCommutation := ∀ scope, (forms scope).EinheitAussage
implementationRule := ∀ scope, (forms scope).ImplAussage
preservation := ∀ scope, (forms scope).ErhaltungsAussage
jointlySatisfiable := joint
```

The definitions in `Quellform.lean` are the statement templates. A form with distinct
concrete and ideal transfers still supplies one typed `RegistryStatements` record.
Use the following statements with its concrete `E` and instruction `b`.

```lean
RegelLokal E b
Ideal.RegelBestimmt (E.system.regel b)
Kommutation vor nach andere
I.RegelAbgleich E b
Ideal.RegelFortschritt E.system b
I.RegelKomponierbar E.einrichtung E.system b
Sicherheit.RegelSicher safetyUnit b
```

Use the actual rule equations for the ideal and implementation fields, including
the plan and successor. The designer fixes these equations, the exact guard operands,
the bound, and the joint premise before handing off proofs. For core-only syntax,
replace the surface triple by checked origin from elaboration or from a runtime rule.
Use `ErfuellbarAm` for the current forms. Its source parses and elaborates, the occurrence
is reachable from canonical initialization, both form rules execute there, and its
guard operands meet `waechterBedarf`. Use one theorem for all operators of a constructor
when the constructor has a finite operator table.

The four local safety obligations are fields of `Sicherheit.SchrittSicherheit`.
The pre-state, plan and intermediate state come from the concrete rule.
`FuehrtSchrittAus` supplies the executed trace and final state. Memory safety checks the
trace addresses and the release ledger. Invariant preservation carries the cut predicate
and establishes the lock-handoff conditions. Race freedom carries graph order and checks
device authority in the trace and journal. TOCTOU freedom checks commit validity and
authority under the policies allowed by the chosen rows. For stateful forms, state the
source-level condition that makes each of these fields provable and prove it is preserved.
M7S connects these conditions to the run induction and handles startup, pauses and
environment steps.

## Proofs filled after the statements are fixed

1. Apply the syntax entry to the lexing and production premises for `Parse`. For
   `Elaboriert`, unfold the typed fragment translation. Show the instruction occupies
   the declared index with `List.getElem?_append_right` and the child lengths. Apply
   `Quellform.realisiert` to the live context and instruction pointer at that occurrence.
2. Invert an ideal rule to obtain the exact plan. For zero memory footprint and
   zero reads, discharge `Befugt` by eliminating membership in each empty list.
   For an access, exhibit its matching live handle, extent and rights at the pre-state.
   Introduce the head context and recorded operands to prove the table includes its
   guard use. Compare the plan and successor equalities to prove determinism.
3. Supply the one-step unit and its mover proofs. For multiple steps, show the
   before and after steps move in their required direction past other contexts, and
   bound the concrete private steps consumed before the next ideal step.
4. For local simulation, decompose the shared protocol relation and the local-state
   relation. For the atomic forms substitute the equal pre-states and replay the same
   `FuehrtSchrittAus` in `I.Schritt.kontext`. For an implementation-only step use the
   private alternative of `RegelAbgleich` with empty trace and preserved relation.
5. Given an ideal head, exhibit the choice, plans and successor or the exact
   blocking reason. Prove `RegelKomponierbar` with the shared action and memory
   extension. For an internal local step use `FuehrtAus.intern` and `Speicherfolge.nil`.
6. Invert the executed concrete step before reasoning about safety. For an internal
   local step, `vollzug_genau` gives the empty trace and frame-only update. Prove
   the four fields from unchanged graph, locks, rights and journal. A step with effects
   must prove the actual address, handoff, access order and commit obligations it triggers.
7. Build the actual source occurrence using the syntax proof. Show that executing
   its children reaches the declared head from `I.start`. Prove the guard for the
   resulting operands and the joint premise for the registry. Assemble the typed
   entry, activate its constructor in `Core/Waechter/Check.lean`, measure changed pins,
   and run the full Core guards.

## Worked literal

The designer writes the following statements and equations. The literal puts its value
in the requested temporary. At the fragment root that temporary and the instruction
index are both zero.

```lean
def literalForm (scope : Scope) : Quellform (.expression scope .integer) Nat where
  produktion := Surface.literal scope
  befehl := .literal 0
  position := fun _ => 0

def LiteralErfuellbar : Prop :=
  ∀ start, ∃ value, (literalForm []).ErfuellbarAm .x86_64 start value
```

The corresponding equation in `expr` is
`| .lit value => .einzel (.literal slot value)`. The transfer increments the program
counter and writes `Int.ofNat value` at `slot` with `Function.update`; the guard
is `some ⟨.ganzzahlBereich, (Int.ofNat value, width)⟩`. The ideal and implementation
relations both require `plans = [plan]` and `u = b.nach c s`. The literal arm of
`exprSchema` fixes all obligations to
`⟨.surface, Quellform.statements literalForm LiteralErfuellbar constructor⟩`.

The prover fills the location proof by reflexivity. The shared
`Quellform.eintrag` applies the seven steps above, using `Surface.literal_entry`,
the literal location proof and the empty invariant table. The last premise uses the
literal `1` at the canonical start, which already points to instruction zero.

```lean
theorem literal_am_ort (scope : Scope) : (literalForm scope).RegelAmOrt :=
  fun _ => rfl

theorem literal_erfuellbar : LiteralErfuellbar := by
  intro start
  let form := literalForm []
  let s := (I.start (form.einheit .x86_64 1) start).2
  refine ⟨1, form.erfuellbar_aus_erreichbar .x86_64 start 1 s .start
    (form.realisiert (literal_am_ort []) .x86_64 1 s rfl rfl) ?_⟩
  intro g guard
  have same : (⟨.ganzzahlBereich, (1, Plattform.x86_64.ziel.wbits)⟩ : Bedarf) = g :=
    Option.some.inj guard
  subst g
  exact kleinerWert 1 (by omega) (by omega)

def literalEntry : RegistryEntry ``Expr.lit (exprSchema ``Expr.lit) := by
  rw [exprSchema, ite_eq_left rfl]
  exact Quellform.eintrag literalForm LiteralErfuellbar ``Expr.lit Surface.literal_entry literal_am_ort
    (fun _ _ => rfl) literal_erfuellbar
```

`kleinerWert` is the arithmetic bound on the exact integer at the chosen signed width.
`Beispiele.lean` checks this proof and the add, multiply and binding cases.
-/
