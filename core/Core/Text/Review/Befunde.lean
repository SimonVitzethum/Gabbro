/-
  File:      Core/Text/Review/Befunde.lean
  Subject:   Review findings on the `...Aussage : Prop` definitions in Core/Ast (without LowLevel)
             and Core/Text, and on the registry schemas they feed.

  Review of statements, not of proofs. No statement is false: every concrete Inversion, Derivation,
  Bytes, Suffix, Widen, Binding, Payload, Scope, Dispatch and ErfuellbarAm statement matches its name
  and has a jointly satisfiable premise bundle with a real occurrence. The defects are vacuous
  obligations of the generic `Quellform.statements` template, repeated per form:

  * `ImplAussage` only restates the implementation step of the class: for every instruction of the frame-only
    classes `lokal` and `ruf` (every instruction a source form elaborates to, `Befehl.Privat`) `Befehl.impl` is the ideal step
    of its class (`Befehl.impl_privat`). It holds for EVERY form and cannot tell a correct command from a
    wrong one. `falschesLiteralForm` below is a form whose command is provably not the literal command,
    yet it satisfies the obligation. This is the "only talks about ideal = impl" case.
  * `IdealAussage` has three conjuncts; the rule-determinacy one holds for every `Befehl` and the
    equation one is `Iff.rfl`. Only `RegelAmOrt` is substantive, and that is pinned separately as
    `KernOrtAussage`.
  * `EinheitAussage` demands `stotterLaenge = 0` and moves past `vor`/`danach`; both are
    definitions (`fun _ => 0` and `fun _ _ => False`), so it holds for every form with empty
    mover relations - the "empty traces" case.
  * `ElaboriertAussage` is the definitional identity `E = elaborieren platform tree`.
  * `AnnahmeAussage`, `ErhaltungsAussage`, `RegelSicherAussage`, `KostenUndSpurAussage` and
    `RegelAntwortSicherAussage` are generic theorems over an arbitrary `Befehl`: their traces are
    forced to `⟨[], []⟩` by `Befehl.vollzug_genau`, or discharged by `Befehl.sicher`/`.antwortSicher`.
    Again the "empty traces" case.
  * `LocalTypeUseAussage` quantifies over `{a // anyTypeUse a.written}`, the universal
    selector fixed by the model, and additionally exhibits a selected written type
    (`∃ w, anyTypeUse w`). No caller-supplied selector remains, so the eight obligations
    cannot hold vacuously over an empty subtype - the former "premise that never holds"
    case is closed by construction.
-/
module

public import Core.Ast.Semantik.Formbeweise
public import Core.Ast.Inventory.Entries.WrittenTypeStatements

@[expose] public section

namespace Gabbro.Core.Text.Review

open Gabbro.Core.Ast.Semantik
open Maschine Annahme Katalog Waechter Sicherheit
open Gabbro.Core.Text (PrintedToken)

/-- `impl` is defined as the very proposition the obligation asks it to be equivalent to. Hence
    the obligation is `Iff.rfl` for every form, independent of its command. -/
theorem implAussage_allQuellformen {category : Gabbro.Core.Ast.Category} {Arguments : Type}
    (form : Quellform category Arguments) : form.ImplAussage := by
  intro args c s w plans u
  exact (form.befehl args).impl_privat (form.privat args) c s w plans u

/-- Two of the three `IdealAussage` conjuncts are generic (`Befehl.bestimmt`, `Iff.rfl`); given
    `RegelAmOrt` the statement therefore holds for every form. -/
theorem idealAussage_allQuellformenAmOrt {category : Gabbro.Core.Ast.Category} {Arguments : Type}
    (form : Quellform category Arguments) (amOrt : form.RegelAmOrt) : form.IdealAussage := by
  refine ⟨amOrt, ?_⟩
  intro args
  exact ⟨form.bestimmt args, fun c s w plans u => Befehl.ideal_privat _ (form.privat args) c s w plans u⟩

/-- `stotterLaenge` is constantly zero and both mover relations are constantly false, so the unit
    and commutation duty is discharged for every form with empty before/after relations. -/
theorem einheitAussage_allQuellformen {category : Gabbro.Core.Ast.Category} {Arguments : Type}
    (form : Quellform category Arguments) : form.EinheitAussage := by
  intro platform args
  refine ⟨?_, ?_⟩
  · rfl
  · exact Befehl.kommutation _

/-- Elaboration is just the form's own unit construction; the equality is definitional. -/
theorem elaboriertAussage_allQuellformen {category : Gabbro.Core.Ast.Category} {Arguments : Type}
    (form : Quellform category Arguments) : form.ElaboriertAussage := by
  intro platform args
  rfl

/-- The generic `Quellform.annahme` needs no premise about the form; its event clause uses the
    empty trace of the single local step. -/
theorem annahmeAussage_allQuellformen {category : Gabbro.Core.Ast.Category} {Arguments : Type}
    (form : Quellform category Arguments) : form.AnnahmeAussage :=
  Quellform.annahme form

/-- Given the generic invariant-freeness premise (always supplied for these forms), preservation
    is a tuple of theorems true of every `Befehl`. -/
theorem erhaltungsAussage_allQuellformen {category : Gabbro.Core.Ast.Category} {Arguments : Type}
    (form : Quellform category Arguments)
    (ohneInvarianten : ∀ args, (form.fragment args).klauseln.invariant = []) :
    form.ErhaltungsAussage :=
  Quellform.erhaltung form ohneInvarianten

/-- The local step of any `Befehl` emits no memory and no outside trace and contributes one unit
    of work, so the cost-and-trace duty holds for every form. -/
theorem textKostenUndSpur_allQuellformen {category : Gabbro.Core.Ast.Category} {Arguments : Type}
    (form : Quellform category Arguments) (platform : Plattform) (args : Arguments) :
    TextInstructionCost (form.fragment args) platform (form.befehl args) := by
  intro t c s choice stepPlan u spur next head step execute
  have transfer := ((form.befehl args).impl_privat (form.privat args) c s choice [stepPlan] u).1 step
  have planEq : stepPlan = (form.befehl args).plan (s.lokal c) 0 := by
    have h : [stepPlan] = [(form.befehl args).plan (s.lokal c) 0] := transfer.1
    exact (List.cons.inj h).1
  subst stepPlan
  have uEq : u = (form.befehl args).nach c s := transfer.2
  subst u
  obtain ⟨spurEq, _⟩ := (form.befehl args).vollzug_genau_privat (form.privat args) (w := choice) step execute
  subst spur
  refine ⟨rfl, rfl, ?_⟩
  rfl

/-- Likewise the answer-authority duty: the forced empty trace has no answer event. -/
theorem antwortSicher_allQuellformen {category : Gabbro.Core.Ast.Category} {Arguments : Type}
    (form : Quellform category Arguments) (platform : Plattform) (args : Arguments) :
    Gabbro.Core.Ast.Semantik.RegelAntwortSicher
      (form.fragment args) platform (form.befehl args) := by
  intro t c s choice stepPlan u spur next head step execute
  have transfer := ((form.befehl args).impl_privat (form.privat args) c s choice [stepPlan] u).1 step
  have planEq : stepPlan = (form.befehl args).plan (s.lokal c) 0 := by
    have h : [stepPlan] = [(form.befehl args).plan (s.lokal c) 0] := transfer.1
    exact (List.cons.inj h).1
  subst stepPlan
  have uEq : u = (form.befehl args).nach c s := transfer.2
  subst u
  obtain ⟨spurEq, _⟩ := (form.befehl args).vollzug_genau_privat (form.privat args) (w := choice) step execute
  subst spur
  constructor
  · intro answer h
    rcases (form.befehl args).plan_privat_aktion (form.privat args) (s.lokal c) with h1|⟨v1,a1,h1⟩|⟨g1,h1⟩|⟨v2,k2,h1⟩|⟨l3,k3,p3,h1⟩
    · rw [h1] at h; cases h
    · rw [h1] at h; cases h
    · rw [h1] at h; cases h
    · rw [h1] at h; cases h
    · rw [h1] at h; cases h
  · intro answer h
    exact List.not_mem_nil h

/-- The local safety duty is `Befehl.sicher`, a theorem for every command once the form's invariant
    table is a checker-accepted predicate table. -/
theorem regelSicher_allQuellformen {category : Gabbro.Core.Ast.Category} {Arguments : Type}
    (form : Quellform category Arguments) (platform : Plattform) (args : Arguments)
    (ps : List Praedikat)
    (tab : (form.fragment args).klauseln.invariant = ps.map Praedikat.gilt)
    (ok : ∀ b ∈ (form.fragment args).code, pruefeBefehlErhalt ps b = true) :
    Sicherheit.RegelSicher ((form.fragment args).sicherheitsEinheit platform) (form.befehl args) :=
  (form.befehl args).sicher (form.fragment args) platform ps tab ok

/-- A form with the literal's production and position but a deliberately wrong command. -/
def falschesLiteralForm : Quellform (.expression []) Nat where
  produktion := (literalForm []).produktion
  befehl := fun _ => .ende
  position := (literalForm []).position

theorem falschesLiteralForm_anderesBefehl (n : Nat) :
    falschesLiteralForm.befehl n ≠ (literalForm []).befehl n := by
  intro h
  cases h

theorem falschesLiteralForm_impl_vakuös : falschesLiteralForm.ImplAussage :=
  implAussage_allQuellformen falschesLiteralForm

theorem falschesLiteralForm_einheit_vakuös : falschesLiteralForm.EinheitAussage :=
  einheitAussage_allQuellformen falschesLiteralForm

theorem falschesLiteralForm_elaboriert_vakuös : falschesLiteralForm.ElaboriertAussage :=
  elaboriertAussage_allQuellformen falschesLiteralForm

theorem falschesLiteralForm_annahme_vakuös : falschesLiteralForm.AnnahmeAussage :=
  annahmeAussage_allQuellformen falschesLiteralForm

theorem falschesLiteralForm_kosten_vakuös (platform : Plattform) (n : Nat) :
    TextInstructionCost (falschesLiteralForm.fragment n) platform (falschesLiteralForm.befehl n) :=
  textKostenUndSpur_allQuellformen falschesLiteralForm platform n

theorem falschesLiteralForm_antwort_vakuös (platform : Plattform) (n : Nat) :
    Gabbro.Core.Ast.Semantik.RegelAntwortSicher
      (falschesLiteralForm.fragment n) platform (falschesLiteralForm.befehl n) :=
  antwortSicher_allQuellformen falschesLiteralForm platform n

end Gabbro.Core.Text.Review
