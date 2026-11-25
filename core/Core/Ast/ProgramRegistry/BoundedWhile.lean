module

public import Core.Ast.Semantik.ProgramForms
public import Core.Ast.Semantik.ProgramObligations
public import Core.Ast.Semantik.Formen

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Waechter

-- Mirror Rule.Entry.parse using the source production and lexical premises.
theorem boundedWhile_parse (scope : Scope) (result : Option (Ty .value)) : (boundedWhileForm scope result).ParseAussage := by
  intro args text pieces lexed production
  exact (Surface.boundedWhile_entry scope result).parse lexed production

-- Mirror elab_korrekt using the compositional fragment.
theorem boundedWhile_elaboriert (scope : Scope) (result : Option (Ty .value)) : (boundedWhileForm scope result).ElaboriertAussage := by
  intro platform args
  rfl

-- Mirror Quellform.realisiert using the concrete instruction position.
theorem boundedWhile_realisiert (scope : Scope) (result : Option (Ty .value)) : (boundedWhileForm scope result).RealisiertAussage := by
  intro platform args s running active live atPc
  exact (boundedWhileForm scope result).realisiert (fun args => by
    change ((((((expr 0 args.bound).anhaengen (.einzel (.setzePasszahl 0 ((expr 0 args.condition).code.length + 1)))).anhaengen (expr 0 args.condition)).anhaengen (.einzel (whileInstruction args.condition (bracedBlock args.body) args.overflow))).anhaengen (bracedBlock args.body)).anhaengen (.einzel (.zurueckSprung ((expr 0 args.condition).code.length + (bracedBlock args.body).code.length + 1)))).code[(expr 0 args.bound).code.length + 1 + (expr 0 args.condition).code.length]? = some (whileInstruction args.condition (bracedBlock args.body) args.overflow)

    simp only [Fragment.anhaengen, Fragment.einzel]
    have hlt1 : (expr 0 args.bound).code.length + 1 + (expr 0 args.condition).code.length < (((((expr 0 args.bound).code ++ [Befehl.setzePasszahl 0 ((expr 0 args.condition).code.length + 1)]) ++ (expr 0 args.condition).code) ++ [whileInstruction args.condition (bracedBlock args.body) args.overflow]) ++ (bracedBlock args.body).code).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have hlt2 : (expr 0 args.bound).code.length + 1 + (expr 0 args.condition).code.length < ((((expr 0 args.bound).code ++ [Befehl.setzePasszahl 0 ((expr 0 args.condition).code.length + 1)]) ++ (expr 0 args.condition).code) ++ [whileInstruction args.condition (bracedBlock args.body) args.overflow]).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [List.getElem?_append_left hlt1, List.getElem?_append_left hlt2]
    rw [List.getElem?_append_right]
    · simp only [List.length_append, List.length_cons, List.length_nil, Nat.sub_self, List.getElem?_cons_zero]
    · simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    ) platform args s running active live atPc

-- Mirror Quellform.annahme at the source head with the exact operands.
theorem boundedWhile_annahme (scope : Scope) (result : Option (Ty .value)) : (boundedWhileForm scope result).AnnahmeAussage := by
  intro platform args
  refine ⟨((boundedWhileForm scope result).befehl args).lokal _ rfl, ?_, ?_⟩
  · rintro s c ⟨op, operands⟩ head guard
    exact ⟨c, (boundedWhileForm scope result).befehl args, head, guard⟩
  · intro t c s w stepPlan u spur next step execute ev
    obtain ⟨rfl, _⟩ := ((boundedWhileForm scope result).befehl args).vollzug_genau (w := w) step execute
    exact List.not_mem_nil

-- Mirror binary_am_ort and Befehl.bestimmt for the new instruction.
theorem boundedWhile_ideal (scope : Scope) (result : Option (Ty .value)) : (boundedWhileForm scope result).IdealAussage := by
  constructor
  · intro args
    change ((((((expr 0 args.bound).anhaengen (.einzel (.setzePasszahl 0 ((expr 0 args.condition).code.length + 1)))).anhaengen (expr 0 args.condition)).anhaengen (.einzel (whileInstruction args.condition (bracedBlock args.body) args.overflow))).anhaengen (bracedBlock args.body)).anhaengen (.einzel (.zurueckSprung ((expr 0 args.condition).code.length + (bracedBlock args.body).code.length + 1)))).code[(expr 0 args.bound).code.length + 1 + (expr 0 args.condition).code.length]? = some (whileInstruction args.condition (bracedBlock args.body) args.overflow)
    simp only [Fragment.anhaengen, Fragment.einzel]
    have hlt1 : (expr 0 args.bound).code.length + 1 + (expr 0 args.condition).code.length < (((((expr 0 args.bound).code ++ [Befehl.setzePasszahl 0 ((expr 0 args.condition).code.length + 1)]) ++ (expr 0 args.condition).code) ++ [whileInstruction args.condition (bracedBlock args.body) args.overflow]) ++ (bracedBlock args.body).code).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have hlt2 : (expr 0 args.bound).code.length + 1 + (expr 0 args.condition).code.length < ((((expr 0 args.bound).code ++ [Befehl.setzePasszahl 0 ((expr 0 args.condition).code.length + 1)]) ++ (expr 0 args.condition).code) ++ [whileInstruction args.condition (bracedBlock args.body) args.overflow]).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [List.getElem?_append_left hlt1, List.getElem?_append_left hlt2]
    rw [List.getElem?_append_right]
    · simp only [List.length_append, List.length_cons, List.length_nil, Nat.sub_self, List.getElem?_cons_zero]
    · simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  · intro args
    constructor
    · exact (boundedWhileForm scope result).bestimmt args
    · intro c s w plans u
      exact Iff.rfl

-- Mirror Befehl.kommutation with one linearisation point and zero private steps.
theorem boundedWhile_einheit (scope : Scope) (result : Option (Ty .value)) : (boundedWhileForm scope result).EinheitAussage := by
  intro platform args
  exact ⟨rfl, ((boundedWhileForm scope result).befehl args).kommutation⟩

-- Mirror Quellform.ImplAussage with the explicit transfer and its plan.
theorem boundedWhile_impl (scope : Scope) (result : Option (Ty .value)) : (boundedWhileForm scope result).ImplAussage := by
  intro args c s w plans u
  exact Iff.rfl

-- Mirror Quellform.erhaltung with the instruction-local transfer and safety.
theorem boundedWhile_erhaltung (scope : Scope) (result : Option (Ty .value)) : (boundedWhileForm scope result).ErhaltungsAussage := by
  intro platform args
  have inv : ((boundedWhileForm scope result).fragment args).klauseln.invariant = [] := by
    change (stmt ((boundedWhileForm scope result).produktion.tree args).2).klauseln.invariant = []
    exact stmt_keine_invarianten _
  exact ⟨((boundedWhileForm scope result).befehl args).abgleich ((boundedWhileForm scope result).fragment args) platform,
    ((boundedWhileForm scope result).befehl args).fortschritt ((boundedWhileForm scope result).fragment args),
    ((boundedWhileForm scope result).befehl args).komponierbar ((boundedWhileForm scope result).fragment args) platform,
    ((boundedWhileForm scope result).befehl args).sicherheitsPflichten ((boundedWhileForm scope result).fragment args) platform inv⟩

-- Mirror Befehl.sicher to discharge the six SchrittSicherheit fields at every concrete cut.
theorem boundedWhile_sicher (scope : Scope) (result : Option (Ty .value)) platform a :
    Sicherheit.RegelSicher (((boundedWhileForm scope result).fragment a).sicherheitsEinheit platform)
      ((boundedWhileForm scope result).befehl a) := by
  have inv : ((boundedWhileForm scope result).fragment a).klauseln.invariant = [] := by
    change (stmt ((boundedWhileForm scope result).produktion.tree a).2).klauseln.invariant = []
    exact stmt_keine_invarianten _
  exact ((boundedWhileForm scope result).befehl a).sicher ((boundedWhileForm scope result).fragment a) platform inv

-- Mirror binary_erfuellbar at the actual instruction and reachable pre-state.
theorem boundedWhile_erfuellbar : boundedWhileJoint := by
  intro platform start
  let ctx : StatementContext := ([], none)
  let form := boundedWhileForm ctx.1 ctx.2
  let name : Identifier := keywordName 'x' [] (by decide) (fun _ member => (List.not_mem_nil member).elim)
  have ordinaryName : ordinaryLocal name := (directName_of_singleton (name := name) rfl).1
  let a : Surface.BoundedWhileArgs [] none := ⟨Expr.trueLit, 1, 1, Expr.lit 1, trivial, by omega, name, .braces .done⟩
  let E := form.einheit platform a
  let s₀ := (I.start E start).2
  let s₁ := (Befehl.literal 0 1).nach eintritt s₀
  let s₂ := (Befehl.setzePasszahl 0 2).nach eintritt s₁
  let s₃ := (Befehl.wahrheitswert 0 true).nach eintritt s₂
  have step1 : E.system.ISchritt eintritt s₀ () [plan] s₁ := ⟨.literal 0 1, rfl, rfl, rfl⟩
  have step2 : E.system.ISchritt eintritt s₁ () [plan] s₂ := ⟨.setzePasszahl 0 2, rfl, rfl, rfl⟩
  have step3 : E.system.ISchritt eintritt s₂ () [plan] s₃ := ⟨.wahrheitswert 0 true, rfl, rfl, rfl⟩
  have reached : E.system.IErreichbar s₀ s₃ :=
    .schritt eintritt () [plan] (.schritt eintritt () [plan] (.schritt eintritt () [plan] .start step1) step2) step3
  refine ⟨ctx, a, Ast.print (form.produktion.tree a), s₃,
    Ast.parse_print (form.produktion.tree a), rfl, reached,
    form.realisiert (fun args => by
    change ((((((expr 0 args.bound).anhaengen (.einzel (.setzePasszahl 0 ((expr 0 args.condition).code.length + 1)))).anhaengen (expr 0 args.condition)).anhaengen (.einzel (whileInstruction args.condition (bracedBlock args.body) args.overflow))).anhaengen (bracedBlock args.body)).anhaengen (.einzel (.zurueckSprung ((expr 0 args.condition).code.length + (bracedBlock args.body).code.length + 1)))).code[(expr 0 args.bound).code.length + 1 + (expr 0 args.condition).code.length]? = some (whileInstruction args.condition (bracedBlock args.body) args.overflow)
    simp only [Fragment.anhaengen, Fragment.einzel]
    have hlt1 : (expr 0 args.bound).code.length + 1 + (expr 0 args.condition).code.length < (((((expr 0 args.bound).code ++ [Befehl.setzePasszahl 0 ((expr 0 args.condition).code.length + 1)]) ++ (expr 0 args.condition).code) ++ [whileInstruction args.condition (bracedBlock args.body) args.overflow]) ++ (bracedBlock args.body).code).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have hlt2 : (expr 0 args.bound).code.length + 1 + (expr 0 args.condition).code.length < ((((expr 0 args.bound).code ++ [Befehl.setzePasszahl 0 ((expr 0 args.condition).code.length + 1)]) ++ (expr 0 args.condition).code) ++ [whileInstruction args.condition (bracedBlock args.body) args.overflow]).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [List.getElem?_append_left hlt1, List.getElem?_append_left hlt2]
    rw [List.getElem?_append_right]
    · simp only [List.length_append, List.length_cons, List.length_nil, Nat.sub_self, List.getElem?_cons_zero]
    · simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    ) platform a s₃ rfl rfl rfl rfl, ?_⟩
  intro g guard
  cases guard

def boundedWhileProofs : RegistryEntry ``Stmt.whileBounded
    ⟨.surface, Quellform.statements (Context := StatementContext) (fun ctx => boundedWhileForm ctx.1 ctx.2) boundedWhileJoint ``Stmt.whileBounded⟩ where
  realization := .surface (fun ctx => boundedWhile_parse ctx.1 ctx.2) (fun ctx => boundedWhile_elaboriert ctx.1 ctx.2) (fun ctx => boundedWhile_realisiert ctx.1 ctx.2)
  acceptanceRule := fun ctx => boundedWhile_annahme ctx.1 ctx.2
  idealRule := fun ctx => boundedWhile_ideal ctx.1 ctx.2
  unitsAndCommutation := fun ctx => boundedWhile_einheit ctx.1 ctx.2
  implementationRule := fun ctx => boundedWhile_impl ctx.1 ctx.2
  preservation := fun ctx => boundedWhile_erhaltung ctx.1 ctx.2
  jointlySatisfiable := boundedWhile_erfuellbar

def boundedWhileEntry : RegistryEntry ``Stmt.whileBounded (stmtSchema ``Stmt.whileBounded) := by
  rw [stmtSchema,
    if_neg (differentLabels (a := "whileBounded") (b := "letValue") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "whileBounded") (b := "assignVar") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "whileBounded") (b := "ret") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "whileBounded") (b := "ite") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "whileBounded") (b := "retVoid") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "whileBounded") (b := "letMutable") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "whileBounded") (b := "directCall") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "whileBounded") (b := "bindDirect") (by intro same; simp only [String.reduceEq] at same)),
    if_pos rfl]
  exact boundedWhileProofs

end Gabbro.Core.Ast.Semantik
