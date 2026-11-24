module

public import Core.Ast.Semantik.ProgramForms
public import Core.Ast.Semantik.ProgramObligations
public import Core.Ast.Semantik.Formen

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Waechter

/-- The characteristic instruction of the unbounded loop is its closing back-jump: it sits right
    after the body of one pass and returns to the first instruction of that body. -/
theorem forever_amOrt (scope : Scope) (result : Option (Ty .value)) :
    (foreverForm scope result).RegelAmOrt := by
  intro args
  change ((bracedBlock args.body).anhaengen
    (Fragment.einzel (Befehl.zurueckSprung (bracedBlock args.body).code.length))).code[(bracedBlock args.body).code.length]? =
      some (Befehl.zurueckSprung (bracedBlock args.body).code.length)
  simp only [Fragment.anhaengen, Fragment.einzel]
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

-- Mirror boundedWhile_parse using the source production and lexical premises.
theorem forever_parse (scope : Scope) (result : Option (Ty .value)) :
    (foreverForm scope result).ParseAussage := by
  intro args text pieces lexed production
  exact (Surface.forever_entry scope result).parse lexed production

-- Mirror boundedWhile_elaboriert using the compositional fragment.
theorem forever_elaboriert (scope : Scope) (result : Option (Ty .value)) :
    (foreverForm scope result).ElaboriertAussage := by
  intro platform args
  rfl

-- Mirror boundedWhile_realisiert using the concrete instruction position.
theorem forever_realisiert (scope : Scope) (result : Option (Ty .value)) :
    (foreverForm scope result).RealisiertAussage := by
  intro platform args s running active live atPc
  exact (foreverForm scope result).realisiert (forever_amOrt scope result) platform args s
    running active live atPc

-- Mirror boundedWhile_annahme at the source head with the exact operands.
theorem forever_annahme (scope : Scope) (result : Option (Ty .value)) :
    (foreverForm scope result).AnnahmeAussage := by
  intro platform args
  refine ⟨((foreverForm scope result).befehl args).lokal _ rfl, ?_, ?_⟩
  · rintro s c ⟨op, operands⟩ head guard
    exact ⟨c, (foreverForm scope result).befehl args, head, guard⟩
  · intro t c s w stepPlan u spur next step execute ev
    obtain ⟨rfl, _⟩ := ((foreverForm scope result).befehl args).vollzug_genau (w := w) step execute
    exact List.not_mem_nil

-- Mirror boundedWhile_ideal for the back-jump instruction.
theorem forever_ideal (scope : Scope) (result : Option (Ty .value)) :
    (foreverForm scope result).IdealAussage := by
  constructor
  · exact forever_amOrt scope result
  · intro args
    constructor
    · exact ((foreverForm scope result).befehl args).bestimmt
    · intro c s w plans u
      exact Iff.rfl

-- Mirror boundedWhile_einheit: one linearisation point and zero private steps.
theorem forever_einheit (scope : Scope) (result : Option (Ty .value)) :
    (foreverForm scope result).EinheitAussage := by
  intro platform args
  exact ⟨rfl, ((foreverForm scope result).befehl args).kommutation⟩

-- Mirror boundedWhile_impl with the explicit transfer and its plan.
theorem forever_impl (scope : Scope) (result : Option (Ty .value)) :
    (foreverForm scope result).ImplAussage := by
  intro args c s w plans u
  exact Iff.rfl

-- Mirror boundedWhile_erhaltung with the instruction-local transfer and safety.
theorem forever_erhaltung (scope : Scope) (result : Option (Ty .value)) :
    (foreverForm scope result).ErhaltungsAussage := by
  intro platform args
  have inv : ((foreverForm scope result).fragment args).klauseln.invariant = [] := by
    change (stmt ((foreverForm scope result).produktion.tree args).2).klauseln.invariant = []
    exact stmt_keine_invarianten _
  exact ⟨((foreverForm scope result).befehl args).abgleich ((foreverForm scope result).fragment args) platform,
    ((foreverForm scope result).befehl args).fortschritt ((foreverForm scope result).fragment args),
    ((foreverForm scope result).befehl args).komponierbar ((foreverForm scope result).fragment args) platform,
    ((foreverForm scope result).befehl args).sicherheitsPflichten ((foreverForm scope result).fragment args)
      platform inv⟩

-- Mirror boundedWhile_erfuellbar at the actual instruction and its reachable pre-state: an empty
-- body runs its closing block instruction once and then stands at the back-jump.
theorem forever_erfuellbar : foreverJoint := by
  intro platform start
  let ctx : StatementContext := ([], none)
  let form := foreverForm ctx.1 ctx.2
  let a : Surface.ForeverArgs [] none := ⟨none, .braces .done⟩
  let E := form.einheit platform a
  let s₀ := (I.start E start).2
  let s₁ := (Befehl.blockEnde 0).nach eintritt s₀
  have step1 : E.system.ISchritt eintritt s₀ () [plan] s₁ := ⟨.blockEnde 0, rfl, rfl, rfl⟩
  have reached : E.system.IErreichbar s₀ s₁ := .schritt eintritt () [plan] .start step1
  refine ⟨ctx, a, Ast.print (form.produktion.tree a), s₁,
    Ast.parse_print (form.produktion.tree a), rfl, reached,
    form.realisiert (forever_amOrt ctx.1 ctx.2) platform a s₁ rfl rfl rfl rfl, ?_⟩
  intro g guard
  cases guard

def foreverProofs : RegistryEntry ``Stmt.forever
    ⟨.surface, Quellform.statements (Context := StatementContext) (fun ctx => foreverForm ctx.1 ctx.2)
      foreverJoint ``Stmt.forever⟩ where
  realization := .surface (fun ctx => forever_parse ctx.1 ctx.2) (fun ctx => forever_elaboriert ctx.1 ctx.2)
    (fun ctx => forever_realisiert ctx.1 ctx.2)
  acceptanceRule := fun ctx => forever_annahme ctx.1 ctx.2
  idealRule := fun ctx => forever_ideal ctx.1 ctx.2
  unitsAndCommutation := fun ctx => forever_einheit ctx.1 ctx.2
  implementationRule := fun ctx => forever_impl ctx.1 ctx.2
  preservation := fun ctx => forever_erhaltung ctx.1 ctx.2
  jointlySatisfiable := forever_erfuellbar

def foreverEntry : RegistryEntry ``Stmt.forever (stmtSchema ``Stmt.forever) := by
  simp only [stmtSchema, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
  exact foreverProofs

end Gabbro.Core.Ast.Semantik
