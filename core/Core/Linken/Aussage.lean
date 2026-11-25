module

public import Core.Linken.Modul
public import Core.Ast.Semantik.Elaborierung
public import Core.Ast.Aggregate.Types.Model
public import Core.Annahme.Annahme
public import Core.Ast.LowLevel.Proofs.EnvironmentSatisfiability

@[expose] public section

namespace Gabbro.Core.Linken

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Annahme

/-- A build plan is accepted exactly when linking yields a fragment whose unit is accepted.
    All theorems over accepted units (safety, noninterference) then hold for the linked program. -/
def BauplanAkzeptiert (plan : Bauplan) : Prop :=
  ∃ frag, linke plan = some frag ∧ Akzeptiert (frag.einheit plan.plattform)

/-- Acceptance of a plan is linking followed by unit acceptance. -/
def LinkAkzeptanzAussage : Prop :=
  ∀ plan : Bauplan, BauplanAkzeptiert plan ↔
    ∃ frag, linke plan = some frag ∧ Akzeptiert (frag.einheit plan.plattform)

/-- Linking is acceptance by definition. -/
theorem linkAkzeptanz : LinkAkzeptanzAussage :=
  fun _ => Iff.rfl

/-- The defining module: defines the function `main` with an empty body. -/
def modulDef : Modul :=
  { name := "a"
    fragment := (Fragment.einzel
      (Befehl.definiere mainName [] none 0 2 false [] none)).anhaengen
      (Fragment.einzel Befehl.rueckVoid)
    exporte := ["main"]
    importe := [] }

/-- The calling module: calls the function `main` defined in the other module. -/
def modulCall : Modul :=
  { name := "b"
    fragment := Fragment.einzel (Befehl.rufe mainName [] none)
    exporte := []
    importe := ["main"] }

/-- The two-module build plan: `b` calls the function `main` exported by `a`. -/
def beispielPlan : Bauplan :=
  { module := [modulDef, modulCall]
    abhaengigkeiten := [("b", "a")]
    plattform := .x86_64
    einstieg := "a" }

/-- The linked code defines `main` and then calls it. -/
def beispielFragment : Fragment :=
  verknuepfteFragmente beispielPlan

/-- There is an accepted linked plan with two modules where one calls the other's function. -/
def LinkErfuellbarAussage : Prop :=
  ∃ (plan : Bauplan) (frag : Fragment) (fn : Identifier),
    linke plan = some frag ∧
    plan.module.length = 2 ∧
    (∃ params result globale skip mass calls effects,
      Befehl.definiere fn params result globale skip mass calls effects ∈ frag.code) ∧
    (∃ args bind, Befehl.rufe fn args bind ∈ frag.code) ∧
    Akzeptiert (frag.einheit plan.plattform)

/-- The link check holds for the example plan. -/
theorem beispielOk : bauplanOk beispielPlan = true :=
  rfl

/-- Linking the example plan yields the concatenated fragments. -/
theorem beispielLinke : linke beispielPlan = some beispielFragment :=
  rfl

/-- The example plan has two modules. -/
theorem beispielZwei : beispielPlan.module.length = 2 :=
  rfl

/-- The example code is the three instructions. -/
theorem beispielCode : beispielFragment.code =
    [Befehl.definiere mainName [] none 0 2 false [] none, Befehl.rueckVoid,
      Befehl.rufe mainName [] none] := by
  rfl

/-- The example clauses are empty. -/
theorem beispielKlauseln : beispielFragment.klauseln = .leer := by
  rfl

/-- Every instruction of the example is guard-free. -/
theorem beispielGuard (b : Befehl) (present : b ∈ beispielFragment.code) (frame : Rahmen) :
    b.guard frame = none := by
  simp only [beispielCode, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl <;> rfl

/-- Every instruction of the example is frame-only. -/
theorem beispielRein (b : Befehl) (present : b ∈ beispielFragment.code) : b.Privat := by
  simp only [beispielCode, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl <;> first | exact Or.inl rfl | exact Or.inr rfl

/-- The example's linked unit is accepted. -/
theorem beispielAkzeptiert : Akzeptiert (beispielFragment.einheit beispielPlan.plattform) := by
  exact Fragment.akzeptiert_ohne_bedarf beispielFragment _ beispielKlauseln beispielRein
    (fun b present frame => beispielGuard b present frame)

/-- Two modules, one call: the satisfiability witness. -/
theorem link_erfuellbar : LinkErfuellbarAussage := by
  refine ⟨beispielPlan, beispielFragment, mainName, beispielLinke, beispielZwei, ?_, ?_,
    beispielAkzeptiert⟩
  · refine ⟨[], none, 0, 2, false, [], none, ?_⟩
    rw [beispielCode]
    exact List.mem_cons_self
  · refine ⟨[], none, ?_⟩
    rw [beispielCode]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

end Gabbro.Core.Linken
