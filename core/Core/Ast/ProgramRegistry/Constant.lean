module

public import Core.Ast.Semantik.ProgramForms
public import Core.Ast.Semantik.ProgramObligations
public import Core.Ast.Semantik.Formen

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Waechter

-- Mirror Rule.Entry.parse using the source production and lexical premises.
theorem constant_parse (scope : Scope) : (constantForm scope).ParseAussage := by
  intro args text pieces lexed production
  exact (Surface.constant_entry scope).parse lexed production

-- Mirror elab_korrekt using the compositional fragment.
theorem constant_elaboriert (scope : Scope) : (constantForm scope).ElaboriertAussage := by
  intro platform args
  rfl

-- Mirror Quellform.realisiert using the concrete instruction position.
theorem constant_realisiert (scope : Scope) : (constantForm scope).RealisiertAussage := by
  intro platform args s running active live atPc
  exact (constantForm scope).realisiert (fun args => by
    change ((expr 0 args.value).anhaengen (.einzel (.bindeWert 0 args.written.type true))).code[(expr 0 args.value).code.length]? = some (.bindeWert 0 args.written.type true)
    simp only [Fragment.anhaengen, Fragment.einzel, List.getElem?_append_right (Nat.le_refl _),
      Nat.sub_self, List.getElem?_cons_zero]) platform args s running active live atPc

-- Mirror Quellform.annahme at the source head with the exact operands.
theorem constant_annahme (scope : Scope) : (constantForm scope).AnnahmeAussage := by
  intro platform args
  refine ⟨((constantForm scope).befehl args).lokal _ rfl, ?_, ?_⟩
  · rintro s c ⟨op, operands⟩ head guard
    exact ⟨c, (constantForm scope).befehl args, head, guard⟩
  · intro t c s w stepPlan u spur next step execute ev
    obtain ⟨rfl, _⟩ := ((constantForm scope).befehl args).vollzug_genau (w := w) step execute
    exact List.not_mem_nil

-- Mirror binary_am_ort and Befehl.bestimmt for the new instruction.
theorem constant_ideal (scope : Scope) : (constantForm scope).IdealAussage := by
  constructor
  · intro args
    change ((expr 0 args.value).anhaengen (.einzel (.bindeWert 0 args.written.type true))).code[(expr 0 args.value).code.length]? = some (.bindeWert 0 args.written.type true)
    simp only [Fragment.anhaengen, Fragment.einzel, List.getElem?_append_right (Nat.le_refl _),
      Nat.sub_self, List.getElem?_cons_zero]
  · intro args
    constructor
    · exact ((constantForm scope).befehl args).bestimmt
    · intro c s w plans u
      exact Iff.rfl

-- Mirror Befehl.kommutation with one linearisation point and zero private steps.
theorem constant_einheit (scope : Scope) : (constantForm scope).EinheitAussage := by
  intro platform args
  exact ⟨rfl, ((constantForm scope).befehl args).kommutation⟩

-- Mirror Quellform.ImplAussage with the explicit transfer and its plan.
theorem constant_impl (scope : Scope) : (constantForm scope).ImplAussage := by
  intro args c s w plans u
  exact Iff.rfl

-- Mirror Quellform.erhaltung with the instruction-local transfer and safety.
theorem constant_erhaltung (scope : Scope) : (constantForm scope).ErhaltungsAussage := by
  intro platform args
  have inv : ((constantForm scope).fragment args).klauseln.invariant = [] := by
    change (expr 0 args.value).klauseln.invariant ++ [] = []
    rw [expr_keine_invarianten]
    rfl
  exact ⟨((constantForm scope).befehl args).abgleich ((constantForm scope).fragment args) platform,
    ((constantForm scope).befehl args).fortschritt ((constantForm scope).fragment args),
    ((constantForm scope).befehl args).komponierbar ((constantForm scope).fragment args) platform,
    ((constantForm scope).befehl args).sicherheitsPflichten ((constantForm scope).fragment args) platform inv⟩

-- Mirror Befehl.sicher to discharge the six SchrittSicherheit fields at every concrete cut.
theorem constant_sicher (scope : Scope) platform a :
    Sicherheit.RegelSicher (((constantForm scope).fragment a).sicherheitsEinheit platform)
      ((constantForm scope).befehl a) := by
  have inv : ((constantForm scope).fragment a).klauseln.invariant = [] := by
    change (expr 0 a.value).klauseln.invariant ++ [] = []
    rw [expr_keine_invarianten]
    rfl
  exact ((constantForm scope).befehl a).sicher ((constantForm scope).fragment a) platform inv

-- Mirror binary_erfuellbar at the actual instruction and reachable pre-state.
theorem constant_erfuellbar : constantJoint := by
  intro platform start
  let ctx : Scope := []
  let form := constantForm ctx
  let name : Identifier := keywordName 'x' [] (by decide) (fun _ member => (List.not_mem_nil member).elim)
  have ordinaryName : ordinaryLocal name := (directName_of_singleton (name := name) rfl).1
  let a : Surface.ConstantArgs [] := ⟨name, ordinaryName, .bool, trivial, .bool, Expr.trueLit, trivial, trivial⟩
  let E := form.einheit platform a
  let s₀ := (I.start E start).2
  let s₁ := (Befehl.wahrheitswert 0 true).nach eintritt s₀
  have initStep : E.system.ISchritt eintritt s₀ () [plan] s₁ :=
    ⟨.wahrheitswert 0 true, rfl, rfl, rfl⟩
  have reached : E.system.IErreichbar s₀ s₁ := .schritt eintritt () [plan] .start initStep
  refine ⟨ctx, a, Ast.print (form.produktion.tree a), s₁,
    Ast.parse_print (form.produktion.tree a), rfl, reached,
    form.realisiert (fun args => by
      change ((expr 0 args.value).anhaengen (.einzel (.bindeWert 0 args.written.type true))).code[(expr 0 args.value).code.length]? = some (.bindeWert 0 args.written.type true)
      simp only [Fragment.anhaengen, Fragment.einzel, List.getElem?_append_right (Nat.le_refl _),
        Nat.sub_self, List.getElem?_cons_zero])
      platform a s₁ rfl rfl rfl rfl, ?_⟩
  intro g guard
  cases guard

def constantProofs : RegistryEntry ``Decl.constant
    ⟨.surface, Quellform.statements (Context := Scope) (constantForm) constantJoint ``Decl.constant⟩ where
  realization := .surface (constant_parse) (constant_elaboriert) (constant_realisiert)
  acceptanceRule := constant_annahme
  idealRule := constant_ideal
  unitsAndCommutation := constant_einheit
  implementationRule := constant_impl
  preservation := constant_erhaltung
  jointlySatisfiable := constant_erfuellbar

def constantEntry : RegistryEntry ``Decl.constant (declSchema ``Decl.constant) := by
  rw [declSchema,
    if_pos rfl]
  exact constantProofs

end Gabbro.Core.Ast.Semantik
