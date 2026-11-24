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
    · exact ((boundedWhileForm scope result).befehl args).bestimmt
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
    ((boundedWhileForm scope result).befehl args).sicher ((boundedWhileForm scope result).fragment args) platform inv⟩

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
  have ordinaryName : ordinaryLocal name := by
    change ['x'] ≠ ['t', 'r', 'u', 'e'] ∧ ['x'] ≠ ['f', 'a', 'l', 's', 'e']
    constructor
    · intro h
      cases h
    · intro h
      cases h
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

-- Mirror Rule.Entry.parse using the source production and lexical premises.
theorem forRange_parse (scope : Scope) (result : Option (Ty .value)) : (forRangeForm scope result).ParseAussage := by
  intro args text pieces lexed production
  exact (Surface.forRange_entry scope result).parse lexed production

-- Mirror elab_korrekt using the compositional fragment.
theorem forRange_elaboriert (scope : Scope) (result : Option (Ty .value)) : (forRangeForm scope result).ElaboriertAussage := by
  intro platform args
  rfl

-- Mirror Quellform.realisiert using the concrete instruction position.
theorem forRange_realisiert (scope : Scope) (result : Option (Ty .value)) : (forRangeForm scope result).RealisiertAussage := by
  intro platform args s running active live atPc
  exact (forRangeForm scope result).realisiert (fun args => by
    change (((((((expr 0 args.lower).anhaengen (expr 1 args.upper)).anhaengen (.einzel (Befehl.forAnfang 0 1 (rangeBinding args.name args.lo args.hi).type ((bracedBlock args.body).code.length + 4) (BracedBlock.rangeUses args.name args.body).1 ((BracedBlock.rangeUses args.name args.body).2 && args.overflow.isNone)))).anhaengen (.einzel (forInstruction (bracedBlock args.body) args.overflow))).anhaengen (bracedBlock args.body)).anhaengen (.einzel (Befehl.forNaechster ((bracedBlock args.body).code.length + 1) (rangeBinding args.name args.lo args.hi).type))).anhaengen (.einzel (Befehl.blockEnde 1))).code[(expr 0 args.lower).code.length + (expr 1 args.upper).code.length + 1]? = some (forInstruction (bracedBlock args.body) args.overflow)
    simp only [Fragment.anhaengen, Fragment.einzel]
    have hlt1 : (expr 0 args.lower).code.length + (expr 1 args.upper).code.length + 1 < ((((((expr 0 args.lower).code ++ (expr 1 args.upper).code) ++ [Befehl.forAnfang 0 1 (rangeBinding args.name args.lo args.hi).type ((bracedBlock args.body).code.length + 4) (BracedBlock.rangeUses args.name args.body).1 ((BracedBlock.rangeUses args.name args.body).2 && args.overflow.isNone)]) ++ [forInstruction (bracedBlock args.body) args.overflow]) ++ (bracedBlock args.body).code) ++ [Befehl.forNaechster ((bracedBlock args.body).code.length + 1) (rangeBinding args.name args.lo args.hi).type]).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have hlt2 : (expr 0 args.lower).code.length + (expr 1 args.upper).code.length + 1 < (((((expr 0 args.lower).code ++ (expr 1 args.upper).code) ++ [Befehl.forAnfang 0 1 (rangeBinding args.name args.lo args.hi).type ((bracedBlock args.body).code.length + 4) (BracedBlock.rangeUses args.name args.body).1 ((BracedBlock.rangeUses args.name args.body).2 && args.overflow.isNone)]) ++ [forInstruction (bracedBlock args.body) args.overflow]) ++ (bracedBlock args.body).code).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have hlt3 : (expr 0 args.lower).code.length + (expr 1 args.upper).code.length + 1 < ((((expr 0 args.lower).code ++ (expr 1 args.upper).code) ++ [Befehl.forAnfang 0 1 (rangeBinding args.name args.lo args.hi).type ((bracedBlock args.body).code.length + 4) (BracedBlock.rangeUses args.name args.body).1 ((BracedBlock.rangeUses args.name args.body).2 && args.overflow.isNone)]) ++ [forInstruction (bracedBlock args.body) args.overflow]).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [List.getElem?_append_left hlt1, List.getElem?_append_left hlt2, List.getElem?_append_left hlt3]
    rw [List.getElem?_append_right]
    · simp only [List.length_append, List.length_cons, List.length_nil, Nat.sub_self, List.getElem?_cons_zero]
    · simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    ) platform args s running active live atPc

-- Mirror Quellform.annahme at the source head with the exact operands.
theorem forRange_annahme (scope : Scope) (result : Option (Ty .value)) : (forRangeForm scope result).AnnahmeAussage := by
  intro platform args
  refine ⟨((forRangeForm scope result).befehl args).lokal _ rfl, ?_, ?_⟩
  · rintro s c ⟨op, operands⟩ head guard
    exact ⟨c, (forRangeForm scope result).befehl args, head, guard⟩
  · intro t c s w stepPlan u spur next step execute ev
    obtain ⟨rfl, _⟩ := ((forRangeForm scope result).befehl args).vollzug_genau (w := w) step execute
    exact List.not_mem_nil

-- Mirror binary_am_ort and Befehl.bestimmt for the new instruction.
theorem forRange_ideal (scope : Scope) (result : Option (Ty .value)) : (forRangeForm scope result).IdealAussage := by
  constructor
  · intro args
    change (((((((expr 0 args.lower).anhaengen (expr 1 args.upper)).anhaengen (.einzel (Befehl.forAnfang 0 1 (rangeBinding args.name args.lo args.hi).type ((bracedBlock args.body).code.length + 4) (BracedBlock.rangeUses args.name args.body).1 ((BracedBlock.rangeUses args.name args.body).2 && args.overflow.isNone)))).anhaengen (.einzel (forInstruction (bracedBlock args.body) args.overflow))).anhaengen (bracedBlock args.body)).anhaengen (.einzel (Befehl.forNaechster ((bracedBlock args.body).code.length + 1) (rangeBinding args.name args.lo args.hi).type))).anhaengen (.einzel (Befehl.blockEnde 1))).code[(expr 0 args.lower).code.length + (expr 1 args.upper).code.length + 1]? = some (forInstruction (bracedBlock args.body) args.overflow)
    simp only [Fragment.anhaengen, Fragment.einzel]
    have hlt1 : (expr 0 args.lower).code.length + (expr 1 args.upper).code.length + 1 < ((((((expr 0 args.lower).code ++ (expr 1 args.upper).code) ++ [Befehl.forAnfang 0 1 (rangeBinding args.name args.lo args.hi).type ((bracedBlock args.body).code.length + 4) (BracedBlock.rangeUses args.name args.body).1 ((BracedBlock.rangeUses args.name args.body).2 && args.overflow.isNone)]) ++ [forInstruction (bracedBlock args.body) args.overflow]) ++ (bracedBlock args.body).code) ++ [Befehl.forNaechster ((bracedBlock args.body).code.length + 1) (rangeBinding args.name args.lo args.hi).type]).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have hlt2 : (expr 0 args.lower).code.length + (expr 1 args.upper).code.length + 1 < (((((expr 0 args.lower).code ++ (expr 1 args.upper).code) ++ [Befehl.forAnfang 0 1 (rangeBinding args.name args.lo args.hi).type ((bracedBlock args.body).code.length + 4) (BracedBlock.rangeUses args.name args.body).1 ((BracedBlock.rangeUses args.name args.body).2 && args.overflow.isNone)]) ++ [forInstruction (bracedBlock args.body) args.overflow]) ++ (bracedBlock args.body).code).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have hlt3 : (expr 0 args.lower).code.length + (expr 1 args.upper).code.length + 1 < ((((expr 0 args.lower).code ++ (expr 1 args.upper).code) ++ [Befehl.forAnfang 0 1 (rangeBinding args.name args.lo args.hi).type ((bracedBlock args.body).code.length + 4) (BracedBlock.rangeUses args.name args.body).1 ((BracedBlock.rangeUses args.name args.body).2 && args.overflow.isNone)]) ++ [forInstruction (bracedBlock args.body) args.overflow]).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [List.getElem?_append_left hlt1, List.getElem?_append_left hlt2, List.getElem?_append_left hlt3]
    rw [List.getElem?_append_right]
    · simp only [List.length_append, List.length_cons, List.length_nil, Nat.sub_self, List.getElem?_cons_zero]
    · simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  · intro args
    constructor
    · exact ((forRangeForm scope result).befehl args).bestimmt
    · intro c s w plans u
      exact Iff.rfl

-- Mirror Befehl.kommutation with one linearisation point and zero private steps.
theorem forRange_einheit (scope : Scope) (result : Option (Ty .value)) : (forRangeForm scope result).EinheitAussage := by
  intro platform args
  exact ⟨rfl, ((forRangeForm scope result).befehl args).kommutation⟩

-- Mirror Quellform.ImplAussage with the explicit transfer and its plan.
theorem forRange_impl (scope : Scope) (result : Option (Ty .value)) : (forRangeForm scope result).ImplAussage := by
  intro args c s w plans u
  exact Iff.rfl

-- Mirror Quellform.erhaltung with the instruction-local transfer and safety.
theorem forRange_erhaltung (scope : Scope) (result : Option (Ty .value)) : (forRangeForm scope result).ErhaltungsAussage := by
  intro platform args
  have inv : ((forRangeForm scope result).fragment args).klauseln.invariant = [] := by
    change (stmt ((forRangeForm scope result).produktion.tree args).2).klauseln.invariant = []
    exact stmt_keine_invarianten _
  exact ⟨((forRangeForm scope result).befehl args).abgleich ((forRangeForm scope result).fragment args) platform,
    ((forRangeForm scope result).befehl args).fortschritt ((forRangeForm scope result).fragment args),
    ((forRangeForm scope result).befehl args).komponierbar ((forRangeForm scope result).fragment args) platform,
    ((forRangeForm scope result).befehl args).sicher ((forRangeForm scope result).fragment args) platform inv⟩

-- Mirror Befehl.sicher to discharge the six SchrittSicherheit fields at every concrete cut.
theorem forRange_sicher (scope : Scope) (result : Option (Ty .value)) platform a :
    Sicherheit.RegelSicher (((forRangeForm scope result).fragment a).sicherheitsEinheit platform)
      ((forRangeForm scope result).befehl a) := by
  have inv : ((forRangeForm scope result).fragment a).klauseln.invariant = [] := by
    change (stmt ((forRangeForm scope result).produktion.tree a).2).klauseln.invariant = []
    exact stmt_keine_invarianten _
  exact ((forRangeForm scope result).befehl a).sicher ((forRangeForm scope result).fragment a) platform inv

-- Mirror binary_erfuellbar at the actual instruction and reachable pre-state.
theorem forRange_erfuellbar : forRangeJoint := by
  intro platform start
  let ctx : StatementContext := ([], none)
  let form := forRangeForm ctx.1 ctx.2
  let name : Identifier := keywordName 'x' [] (by decide) (fun _ member => (List.not_mem_nil member).elim)
  have ordinaryName : ordinaryLocal name := by
    change ['x'] ≠ ['t', 'r', 'u', 'e'] ∧ ['x'] ≠ ['f', 'a', 'l', 's', 'e']
    constructor <;> intro h <;> cases h
  let a : Surface.ForRangeArgs [] none := ⟨name, ordinaryName, 1, 1, 3, 3, Expr.lit 1, Expr.lit 3, ⟨trivial, trivial⟩, none, .braces .done⟩
  let setup : Befehl := .forAnfang 0 1 (rangeBinding name 1 3).type ((bracedBlock a.body).code.length + 4) (BracedBlock.rangeUses name a.body).1 ((BracedBlock.rangeUses name a.body).2 && a.overflow.isNone)
  let E := form.einheit platform a
  let s₀ := (I.start E start).2
  let s₁ := (Befehl.literal 0 1).nach eintritt s₀
  let s₂ := (Befehl.literal 1 3).nach eintritt s₁
  let s₃ := setup.nach eintritt s₂
  have reached : E.system.IErreichbar s₀ s₃ :=
    .schritt eintritt () [plan] (.schritt eintritt () [plan] (.schritt eintritt () [plan] .start
      ⟨.literal 0 1, rfl, rfl, rfl⟩) ⟨.literal 1 3, rfl, rfl, rfl⟩) ⟨setup, rfl, rfl, rfl⟩
  refine ⟨ctx, a, Ast.print (form.produktion.tree a), s₃,
    Ast.parse_print (form.produktion.tree a), rfl, reached,
    form.realisiert (fun args => by
    change (((((((expr 0 args.lower).anhaengen (expr 1 args.upper)).anhaengen (.einzel (Befehl.forAnfang 0 1 (rangeBinding args.name args.lo args.hi).type ((bracedBlock args.body).code.length + 4) (BracedBlock.rangeUses args.name args.body).1 ((BracedBlock.rangeUses args.name args.body).2 && args.overflow.isNone)))).anhaengen (.einzel (forInstruction (bracedBlock args.body) args.overflow))).anhaengen (bracedBlock args.body)).anhaengen (.einzel (Befehl.forNaechster ((bracedBlock args.body).code.length + 1) (rangeBinding args.name args.lo args.hi).type))).anhaengen (.einzel (Befehl.blockEnde 1))).code[(expr 0 args.lower).code.length + (expr 1 args.upper).code.length + 1]? = some (forInstruction (bracedBlock args.body) args.overflow)
    simp only [Fragment.anhaengen, Fragment.einzel]
    have hlt1 : (expr 0 args.lower).code.length + (expr 1 args.upper).code.length + 1 < ((((((expr 0 args.lower).code ++ (expr 1 args.upper).code) ++ [Befehl.forAnfang 0 1 (rangeBinding args.name args.lo args.hi).type ((bracedBlock args.body).code.length + 4) (BracedBlock.rangeUses args.name args.body).1 ((BracedBlock.rangeUses args.name args.body).2 && args.overflow.isNone)]) ++ [forInstruction (bracedBlock args.body) args.overflow]) ++ (bracedBlock args.body).code) ++ [Befehl.forNaechster ((bracedBlock args.body).code.length + 1) (rangeBinding args.name args.lo args.hi).type]).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have hlt2 : (expr 0 args.lower).code.length + (expr 1 args.upper).code.length + 1 < (((((expr 0 args.lower).code ++ (expr 1 args.upper).code) ++ [Befehl.forAnfang 0 1 (rangeBinding args.name args.lo args.hi).type ((bracedBlock args.body).code.length + 4) (BracedBlock.rangeUses args.name args.body).1 ((BracedBlock.rangeUses args.name args.body).2 && args.overflow.isNone)]) ++ [forInstruction (bracedBlock args.body) args.overflow]) ++ (bracedBlock args.body).code).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have hlt3 : (expr 0 args.lower).code.length + (expr 1 args.upper).code.length + 1 < ((((expr 0 args.lower).code ++ (expr 1 args.upper).code) ++ [Befehl.forAnfang 0 1 (rangeBinding args.name args.lo args.hi).type ((bracedBlock args.body).code.length + 4) (BracedBlock.rangeUses args.name args.body).1 ((BracedBlock.rangeUses args.name args.body).2 && args.overflow.isNone)]) ++ [forInstruction (bracedBlock args.body) args.overflow]).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [List.getElem?_append_left hlt1, List.getElem?_append_left hlt2, List.getElem?_append_left hlt3]
    rw [List.getElem?_append_right]
    · simp only [List.length_append, List.length_cons, List.length_nil, Nat.sub_self, List.getElem?_cons_zero]
    · simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    ) platform a s₃ rfl rfl rfl rfl, ?_⟩
  intro g guard
  cases guard

def forRangeProofs : RegistryEntry ``Stmt.forRange
    ⟨.surface, Quellform.statements (Context := StatementContext) (fun ctx => forRangeForm ctx.1 ctx.2) forRangeJoint ``Stmt.forRange⟩ where
  realization := .surface (fun ctx => forRange_parse ctx.1 ctx.2) (fun ctx => forRange_elaboriert ctx.1 ctx.2) (fun ctx => forRange_realisiert ctx.1 ctx.2)
  acceptanceRule := fun ctx => forRange_annahme ctx.1 ctx.2
  idealRule := fun ctx => forRange_ideal ctx.1 ctx.2
  unitsAndCommutation := fun ctx => forRange_einheit ctx.1 ctx.2
  implementationRule := fun ctx => forRange_impl ctx.1 ctx.2
  preservation := fun ctx => forRange_erhaltung ctx.1 ctx.2
  jointlySatisfiable := forRange_erfuellbar

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
    ((constantForm scope).befehl args).sicher ((constantForm scope).fragment args) platform inv⟩

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
  have ordinaryName : ordinaryLocal name := by
    change ['x'] ≠ ['t', 'r', 'u', 'e'] ∧ ['x'] ≠ ['f', 'a', 'l', 's', 'e']
    constructor
    · intro h
      cases h
    · intro h
      cases h
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

-- Mirror Rule.Entry.parse using the source production and lexical premises.
theorem function_parse (scope : Scope) : (functionForm scope).ParseAussage := by
  intro args text pieces lexed production
  exact (Surface.function_entry scope).parse lexed production

-- Mirror elab_korrekt using the compositional fragment.
theorem function_elaboriert (scope : Scope) : (functionForm scope).ElaboriertAussage := by
  intro platform args
  rfl

-- Mirror Quellform.realisiert using the concrete instruction position.
theorem function_realisiert (scope : Scope) : (functionForm scope).RealisiertAussage := by
  intro platform args s running active live atPc
  exact (functionForm scope).realisiert (fun args => by
    change ((Fragment.einzel (functionInstruction scope args.name args.parameters args.result args.measure.isSome (functionCode args.result args.measure args.body))).anhaengen (functionCode args.result args.measure args.body)).code[0]? = some (functionInstruction scope args.name args.parameters args.result args.measure.isSome (functionCode args.result args.measure args.body))
    simp only [Fragment.anhaengen, Fragment.einzel, List.cons_append, List.nil_append, List.getElem?_cons_zero]
    ) platform args s running active live atPc

-- Mirror Quellform.annahme at the source head with the exact operands.
theorem function_annahme (scope : Scope) : (functionForm scope).AnnahmeAussage := by
  intro platform args
  refine ⟨((functionForm scope).befehl args).lokal _ rfl, ?_, ?_⟩
  · rintro s c ⟨op, operands⟩ head guard
    exact ⟨c, (functionForm scope).befehl args, head, guard⟩
  · intro t c s w stepPlan u spur next step execute ev
    obtain ⟨rfl, _⟩ := ((functionForm scope).befehl args).vollzug_genau (w := w) step execute
    exact List.not_mem_nil

-- Mirror binary_am_ort and Befehl.bestimmt for the new instruction.
theorem function_ideal (scope : Scope) : (functionForm scope).IdealAussage := by
  constructor
  · intro args
    change ((Fragment.einzel (functionInstruction scope args.name args.parameters args.result args.measure.isSome (functionCode args.result args.measure args.body))).anhaengen (functionCode args.result args.measure args.body)).code[0]? = some (functionInstruction scope args.name args.parameters args.result args.measure.isSome (functionCode args.result args.measure args.body))
    simp only [Fragment.anhaengen, Fragment.einzel, List.cons_append, List.nil_append, List.getElem?_cons_zero]
  · intro args
    constructor
    · exact ((functionForm scope).befehl args).bestimmt
    · intro c s w plans u
      exact Iff.rfl

-- Mirror Befehl.kommutation with one linearisation point and zero private steps.
theorem function_einheit (scope : Scope) : (functionForm scope).EinheitAussage := by
  intro platform args
  exact ⟨rfl, ((functionForm scope).befehl args).kommutation⟩

-- Mirror Quellform.ImplAussage with the explicit transfer and its plan.
theorem function_impl (scope : Scope) : (functionForm scope).ImplAussage := by
  intro args c s w plans u
  exact Iff.rfl

-- Mirror Quellform.erhaltung with the instruction-local transfer and safety.
theorem function_erhaltung (scope : Scope) : (functionForm scope).ErhaltungsAussage := by
  intro platform args
  let rec blockInv {res : Option (Ty .value)} {before after : Scope} (t : Block res before after) :
      (block t).klauseln.invariant = [] :=
    match t with
    | .done => rfl
    | .step first rest => by
        change (stmt first).klauseln.invariant ++ (block rest).klauseln.invariant = []
        rw [stmt_keine_invarianten, blockInv rest]
        rfl
  have bracedInv : ∀ {res : Option (Ty .value)} {before : Scope} (t : BracedBlock res before), (bracedBlock t).klauseln.invariant = [] := by
    intro res before t
    rcases t with ⟨body⟩
    change (block body).klauseln.invariant ++ [] = []
    rw [blockInv body]
    rfl
  have codeInv : ∀ {s : Scope} (res : Option WrittenType) (measure : Option (Measure s)) (body : BracedBlock (writtenResult res) s),
      (functionCode res measure body).klauseln.invariant = [] := by
    intro s res measure body
    cases measure with
    | none =>
        simp only [functionCode, Fragment.anhaengen, Fragment.einzel, Quellklauseln.anhaengen, Quellklauseln.leer, List.append_nil, List.nil_append]
        exact bracedInv body
    | some m =>
        simp only [functionCode, Fragment.anhaengen, Fragment.einzel, Quellklauseln.anhaengen, Quellklauseln.leer, List.append_nil, List.nil_append]
        rw [expr_keine_invarianten]
        exact bracedInv body
  have inv : ((functionForm scope).fragment args).klauseln.invariant = [] := by
    change (decl ((functionForm scope).produktion.tree args).2).klauseln.invariant = []
    change ((Fragment.einzel (functionInstruction scope args.name args.parameters args.result args.measure.isSome (functionCode args.result args.measure args.body))).anhaengen (functionCode args.result args.measure args.body)).klauseln.invariant = []
    simp only [Fragment.anhaengen, Fragment.einzel, Quellklauseln.anhaengen, Quellklauseln.leer, List.append_nil, List.nil_append]
    exact codeInv args.result args.measure args.body
  exact ⟨((functionForm scope).befehl args).abgleich ((functionForm scope).fragment args) platform,
    ((functionForm scope).befehl args).fortschritt ((functionForm scope).fragment args),
    ((functionForm scope).befehl args).komponierbar ((functionForm scope).fragment args) platform,
    ((functionForm scope).befehl args).sicher ((functionForm scope).fragment args) platform inv⟩

-- Mirror Befehl.sicher to discharge the six SchrittSicherheit fields at every concrete cut.
theorem function_sicher (scope : Scope) platform a :
    Sicherheit.RegelSicher (((functionForm scope).fragment a).sicherheitsEinheit platform)
      ((functionForm scope).befehl a) := by
  let rec blockInv {res : Option (Ty .value)} {before after : Scope} (t : Block res before after) :
      (block t).klauseln.invariant = [] :=
    match t with
    | .done => rfl
    | .step first rest => by
        change (stmt first).klauseln.invariant ++ (block rest).klauseln.invariant = []
        rw [stmt_keine_invarianten, blockInv rest]
        rfl
  have bracedInv : ∀ {res : Option (Ty .value)} {before : Scope} (t : BracedBlock res before), (bracedBlock t).klauseln.invariant = [] := by
    intro res before t
    rcases t with ⟨body⟩
    change (block body).klauseln.invariant ++ [] = []
    rw [blockInv body]
    rfl
  have codeInv : ∀ {s : Scope} (res : Option WrittenType) (measure : Option (Measure s)) (body : BracedBlock (writtenResult res) s),
      (functionCode res measure body).klauseln.invariant = [] := by
    intro s res measure body
    cases measure with
    | none =>
        simp only [functionCode, Fragment.anhaengen, Fragment.einzel, Quellklauseln.anhaengen, Quellklauseln.leer, List.append_nil, List.nil_append]
        exact bracedInv body
    | some m =>
        simp only [functionCode, Fragment.anhaengen, Fragment.einzel, Quellklauseln.anhaengen, Quellklauseln.leer, List.append_nil, List.nil_append]
        rw [expr_keine_invarianten]
        exact bracedInv body
  have inv : ((functionForm scope).fragment a).klauseln.invariant = [] := by
    change (decl ((functionForm scope).produktion.tree a).2).klauseln.invariant = []
    change ((Fragment.einzel (functionInstruction scope a.name a.parameters a.result a.measure.isSome (functionCode a.result a.measure a.body))).anhaengen (functionCode a.result a.measure a.body)).klauseln.invariant = []
    simp only [Fragment.anhaengen, Fragment.einzel, Quellklauseln.anhaengen, Quellklauseln.leer, List.append_nil, List.nil_append]
    exact codeInv a.result a.measure a.body
  exact ((functionForm scope).befehl a).sicher ((functionForm scope).fragment a) platform inv

-- Mirror binary_erfuellbar at the actual instruction and reachable pre-state.
theorem function_erfuellbar : functionJoint := by
  intro platform start
  let ctx : Scope := []
  let form := functionForm ctx
  let name : Identifier := keywordName 'f' [] (by decide) (fun _ member => (List.not_mem_nil member).elim)
  have ordinaryName : directName name := by
    change (['f'] ≠ ['t', 'r', 'u', 'e'] ∧ ['f'] ≠ ['f', 'a', 'l', 's', 'e']) ∧
      ['f'] ∉ ["let", "if", "return", "while", "for", "leave", "next"].map String.toList
    constructor
    · constructor <;> intro h <;> cases h
    · decide
  have validNone : ∀ t ∈ (none : Option WrittenType).toList, WrittenType.valid t := by
    intro t mem
    cases mem
  let a : Surface.FunctionArgs [] := ⟨name, ordinaryName, [], none, validNone, none, .braces .done, List.nodup_nil, by intro h; cases h⟩
  let E := form.einheit platform a
  let s₀ := (I.start E start).2
  refine ⟨ctx, a, Ast.print (form.produktion.tree a), s₀,
    Ast.parse_print (form.produktion.tree a), rfl, .start,
    form.realisiert (fun args => by
    change ((Fragment.einzel (functionInstruction ctx args.name args.parameters args.result args.measure.isSome (functionCode args.result args.measure args.body))).anhaengen (functionCode args.result args.measure args.body)).code[0]? = some (functionInstruction ctx args.name args.parameters args.result args.measure.isSome (functionCode args.result args.measure args.body))
    simp only [Fragment.anhaengen, Fragment.einzel, List.cons_append, List.nil_append, List.getElem?_cons_zero]
    ) platform a s₀ rfl rfl rfl rfl, ?_⟩
  intro g guard
  cases guard

def functionProofs : RegistryEntry ``Decl.function
    ⟨.surface, Quellform.statements (Context := Scope) (functionForm) functionJoint ``Decl.function⟩ where
  realization := .surface (function_parse) (function_elaboriert) (function_realisiert)
  acceptanceRule := function_annahme
  idealRule := function_ideal
  unitsAndCommutation := function_einheit
  implementationRule := function_impl
  preservation := function_erhaltung
  jointlySatisfiable := function_erfuellbar

-- Mirror Rule.Entry.parse using the source production and lexical premises.
theorem program_parse  : (programForm).ParseAussage := by
  intro args text pieces lexed production
  exact (Surface.program_entry).parse lexed production

-- Mirror elab_korrekt using the compositional fragment.
theorem program_elaboriert  : (programForm).ElaboriertAussage := by
  intro platform args
  rfl

-- Mirror Quellform.realisiert using the concrete instruction position.
theorem program_realisiert  : (programForm).RealisiertAussage := by
  intro platform args s running active live atPc
  exact (programForm).realisiert (fun args => by
    change (((unitBody args.unit.2).anhaengen (.einzel (.starte mainName))).anhaengen (.einzel .ende)).code[(unitBody args.unit.2).code.length]? = some (.starte mainName)
    simp only [Fragment.anhaengen, Fragment.einzel]
    have hlt : (unitBody args.unit.2).code.length < ((unitBody args.unit.2).code ++ [Befehl.starte mainName]).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [List.getElem?_append_left hlt]
    rw [List.getElem?_append_right]
    · simp only [List.length_append, List.length_cons, List.length_nil, Nat.sub_self, List.getElem?_cons_zero]
    · omega
    ) platform args s running active live atPc

-- Mirror Quellform.annahme at the source head with the exact operands.
theorem program_annahme  : (programForm).AnnahmeAussage := by
  intro platform args
  refine ⟨((programForm).befehl args).lokal _ rfl, ?_, ?_⟩
  · rintro s c ⟨op, operands⟩ head guard
    exact ⟨c, (programForm).befehl args, head, guard⟩
  · intro t c s w stepPlan u spur next step execute ev
    obtain ⟨rfl, _⟩ := ((programForm).befehl args).vollzug_genau (w := w) step execute
    exact List.not_mem_nil

-- Mirror binary_am_ort and Befehl.bestimmt for the new instruction.
theorem program_ideal  : (programForm).IdealAussage := by
  constructor
  · intro args
    change (((unitBody args.unit.2).anhaengen (.einzel (.starte mainName))).anhaengen (.einzel .ende)).code[(unitBody args.unit.2).code.length]? = some (.starte mainName)
    simp only [Fragment.anhaengen, Fragment.einzel]
    have hlt : (unitBody args.unit.2).code.length < ((unitBody args.unit.2).code ++ [Befehl.starte mainName]).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [List.getElem?_append_left hlt]
    rw [List.getElem?_append_right]
    · simp only [List.length_append, List.length_cons, List.length_nil, Nat.sub_self, List.getElem?_cons_zero]
    · omega
  · intro args
    constructor
    · exact ((programForm).befehl args).bestimmt
    · intro c s w plans u
      exact Iff.rfl

-- Mirror Befehl.kommutation with one linearisation point and zero private steps.
theorem program_einheit  : (programForm).EinheitAussage := by
  intro platform args
  exact ⟨rfl, ((programForm).befehl args).kommutation⟩

-- Mirror Quellform.ImplAussage with the explicit transfer and its plan.
theorem program_impl  : (programForm).ImplAussage := by
  intro args c s w plans u
  exact Iff.rfl

-- Mirror Quellform.erhaltung with the instruction-local transfer and safety.
theorem program_erhaltung  : (programForm).ErhaltungsAussage := by
  intro platform args
  let rec blockInv {res : Option (Ty .value)} {before after : Scope} (t : Block res before after) :
      (block t).klauseln.invariant = [] :=
    match t with
    | .done => rfl
    | .step first rest => by
        change (stmt first).klauseln.invariant ++ (block rest).klauseln.invariant = []
        rw [stmt_keine_invarianten, blockInv rest]
        rfl
  have bracedInv : ∀ {res : Option (Ty .value)} {before : Scope} (t : BracedBlock res before), (bracedBlock t).klauseln.invariant = [] := by
    intro res before t
    rcases t with ⟨body⟩
    change (block body).klauseln.invariant ++ [] = []
    rw [blockInv body]
    rfl
  have codeInv : ∀ {s : Scope} (res : Option WrittenType) (measure : Option (Measure s)) (body : BracedBlock (writtenResult res) s),
      (functionCode res measure body).klauseln.invariant = [] := by
    intro s res measure body
    cases measure with
    | none =>
        simp only [functionCode, Fragment.anhaengen, Fragment.einzel, Quellklauseln.anhaengen, Quellklauseln.leer, List.append_nil, List.nil_append]
        exact bracedInv body
    | some m =>
        simp only [functionCode, Fragment.anhaengen, Fragment.einzel, Quellklauseln.anhaengen, Quellklauseln.leer, List.append_nil, List.nil_append]
        rw [expr_keine_invarianten]
        exact bracedInv body
  have declInv : ∀ {before after : Scope} (d : Decl before after), (decl d).klauseln.invariant = [] := by
    intro before after d
    cases d with
    | constant name ord written valid value static fits =>
        simp only [decl, Fragment.anhaengen, Fragment.einzel, Quellklauseln.anhaengen, Quellklauseln.leer, List.append_nil, List.nil_append]
        exact expr_keine_invarianten 0 value
    | function name ord parameters res valid measure body distinct returns =>
        simp only [decl, Fragment.anhaengen, Fragment.einzel, Quellklauseln.anhaengen, Quellklauseln.leer, List.append_nil, List.nil_append]
        exact codeInv res measure body
  have unitInv : ∀ {before after : Scope} (u : UnitBody before after), (unitBody u).klauseln.invariant = [] := by
    intro before after u
    induction u with
    | done => rfl
    | step first rest ih =>
        simp only [unitBody, Fragment.anhaengen, Quellklauseln.anhaengen]
        rw [declInv, ih]
        rfl
  have inv : (programForm.fragment args).klauseln.invariant = [] := by
    change (programm args.unit).klauseln.invariant = []
    simp only [programm, Fragment.anhaengen, Fragment.einzel, Quellklauseln.anhaengen, Quellklauseln.leer, List.append_nil, List.nil_append]
    exact unitInv args.unit.2
  exact ⟨((programForm).befehl args).abgleich (programForm.fragment args) platform,
    ((programForm).befehl args).fortschritt (programForm.fragment args),
    ((programForm).befehl args).komponierbar (programForm.fragment args) platform,
    ((programForm).befehl args).sicher (programForm.fragment args) platform inv⟩

-- Mirror Befehl.sicher to discharge the six SchrittSicherheit fields at every concrete cut.
theorem program_sicher  platform a :
    Sicherheit.RegelSicher (((programForm).fragment a).sicherheitsEinheit platform)
      ((programForm).befehl a) := by
  let rec blockInv {res : Option (Ty .value)} {before after : Scope} (t : Block res before after) :
      (block t).klauseln.invariant = [] :=
    match t with
    | .done => rfl
    | .step first rest => by
        change (stmt first).klauseln.invariant ++ (block rest).klauseln.invariant = []
        rw [stmt_keine_invarianten, blockInv rest]
        rfl
  have bracedInv : ∀ {res : Option (Ty .value)} {before : Scope} (t : BracedBlock res before), (bracedBlock t).klauseln.invariant = [] := by
    intro res before t
    rcases t with ⟨body⟩
    change (block body).klauseln.invariant ++ [] = []
    rw [blockInv body]
    rfl
  have codeInv : ∀ {s : Scope} (res : Option WrittenType) (measure : Option (Measure s)) (body : BracedBlock (writtenResult res) s),
      (functionCode res measure body).klauseln.invariant = [] := by
    intro s res measure body
    cases measure with
    | none =>
        simp only [functionCode, Fragment.anhaengen, Fragment.einzel, Quellklauseln.anhaengen, Quellklauseln.leer, List.append_nil, List.nil_append]
        exact bracedInv body
    | some m =>
        simp only [functionCode, Fragment.anhaengen, Fragment.einzel, Quellklauseln.anhaengen, Quellklauseln.leer, List.append_nil, List.nil_append]
        rw [expr_keine_invarianten]
        exact bracedInv body
  have declInv : ∀ {before after : Scope} (d : Decl before after), (decl d).klauseln.invariant = [] := by
    intro before after d
    cases d with
    | constant name ord written valid value static fits =>
        simp only [decl, Fragment.anhaengen, Fragment.einzel, Quellklauseln.anhaengen, Quellklauseln.leer, List.append_nil, List.nil_append]
        exact expr_keine_invarianten 0 value
    | function name ord parameters res valid measure body distinct returns =>
        simp only [decl, Fragment.anhaengen, Fragment.einzel, Quellklauseln.anhaengen, Quellklauseln.leer, List.append_nil, List.nil_append]
        exact codeInv res measure body
  have unitInv : ∀ {before after : Scope} (u : UnitBody before after), (unitBody u).klauseln.invariant = [] := by
    intro before after u
    induction u with
    | done => rfl
    | step first rest ih =>
        simp only [unitBody, Fragment.anhaengen, Quellklauseln.anhaengen]
        rw [declInv, ih]
        rfl
  have inv : (programForm.fragment a).klauseln.invariant = [] := by
    change (programm a.unit).klauseln.invariant = []
    simp only [programm, Fragment.anhaengen, Fragment.einzel, Quellklauseln.anhaengen, Quellklauseln.leer, List.append_nil, List.nil_append]
    exact unitInv a.unit.2
  exact ((programForm).befehl a).sicher (programForm.fragment a) platform inv

-- Mirror binary_erfuellbar at the actual instruction and reachable pre-state.
theorem program_erfuellbar : programJoint := by
  intro platform start
  let form := programForm
  let name : Identifier := mainName
  have ord : directName name := by
    change (['m', 'a', 'i', 'n'] ≠ ['t', 'r', 'u', 'e'] ∧ ['m', 'a', 'i', 'n'] ≠ ['f', 'a', 'l', 's', 'e']) ∧
      ['m', 'a', 'i', 'n'] ∉ ["let", "if", "return", "while", "for", "leave", "next"].map String.toList
    constructor
    · constructor <;> intro h <;> cases h
    · decide
  have validNone : ∀ t ∈ (none : Option WrittenType).toList, WrittenType.valid t := by
    intro t mem
    cases mem
  let first : Decl [] [] := .function name ord [] none validNone none (.braces .done) List.nodup_nil (by intro h; cases h)
  let a : Surface.ProgramArgs := ⟨[], [], first, .done⟩
  let defIns : Befehl := .definiere name [] none 0 3 false []
  let E := form.einheit platform a
  let s₀ := (I.start E start).2
  let s₁ := defIns.nach eintritt s₀
  have reached : E.system.IErreichbar s₀ s₁ := .schritt eintritt () [plan] .start ⟨defIns, rfl, rfl, rfl⟩
  refine ⟨a, ?_, ?_⟩
  · refine ⟨Ast.print (form.produktion.tree a), s₁,
      Ast.parse_print (form.produktion.tree a), rfl, reached,
      form.realisiert (fun args => by
      change (((unitBody args.unit.2).anhaengen (.einzel (.starte mainName))).anhaengen (.einzel .ende)).code[(unitBody args.unit.2).code.length]? = some (.starte mainName)
      simp only [Fragment.anhaengen, Fragment.einzel]
      have hlt : (unitBody args.unit.2).code.length < ((unitBody args.unit.2).code ++ [Befehl.starte mainName]).length := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      rw [List.getElem?_append_left hlt]
      rw [List.getElem?_append_right]
      · simp only [List.length_append, List.length_cons, List.length_nil, Nat.sub_self, List.getElem?_cons_zero]
      · omega
    ) platform a s₁ rfl rfl rfl rfl, ?_⟩
    intro g guard
    cases guard
  · refine ⟨a.unit, Ast.print (category := .unit) a.unit, s₁, Ast.parse_print _, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact reached
    · rfl
    · exact ⟨.starte mainName, rfl, rfl, rfl⟩
    · exact ⟨.starte mainName, rfl, rfl, rfl⟩
    · rfl
    · rfl
def programProofs : RegistryEntry ``UnitBody.step
    ⟨.surface, Quellform.statements (Context := PUnit) (fun _ => programForm) programJoint ``UnitBody.step⟩ where
  realization := .surface (fun _ => program_parse) (fun _ => program_elaboriert) (fun _ => program_realisiert)
  acceptanceRule := fun _ => program_annahme
  idealRule := fun _ => program_ideal
  unitsAndCommutation := fun _ => program_einheit
  implementationRule := fun _ => program_impl
  preservation := fun _ => program_erhaltung
  jointlySatisfiable := program_erfuellbar

def returnVoidEntry : RegistryEntry ``Stmt.retVoid (stmtSchema ``Stmt.retVoid) := by
  rw [stmtSchema,
    if_neg (differentLabels (a := "retVoid") (b := "letValue") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "retVoid") (b := "assignVar") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "retVoid") (b := "ret") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "retVoid") (b := "ite") (by intro same; simp only [String.reduceEq] at same)),
    if_pos rfl]
  exact returnVoidProofs

def mutableLocalEntry : RegistryEntry ``Stmt.letMutable (stmtSchema ``Stmt.letMutable) := by
  rw [stmtSchema,
    if_neg (differentLabels (a := "letMutable") (b := "letValue") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "letMutable") (b := "assignVar") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "letMutable") (b := "ret") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "letMutable") (b := "ite") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "letMutable") (b := "retVoid") (by intro same; simp only [String.reduceEq] at same)),
    if_pos rfl]
  exact mutableLocalProofs

def directCallEntry : RegistryEntry ``Stmt.directCall (stmtSchema ``Stmt.directCall) := by
  rw [stmtSchema,
    if_neg (differentLabels (a := "directCall") (b := "letValue") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "directCall") (b := "assignVar") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "directCall") (b := "ret") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "directCall") (b := "ite") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "directCall") (b := "retVoid") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "directCall") (b := "letMutable") (by intro same; simp only [String.reduceEq] at same)),
    if_pos rfl]
  exact directCallProofs

def bindDirectEntry : RegistryEntry ``Stmt.bindDirect (stmtSchema ``Stmt.bindDirect) := by
  rw [stmtSchema,
    if_neg (differentLabels (a := "bindDirect") (b := "letValue") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "bindDirect") (b := "assignVar") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "bindDirect") (b := "ret") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "bindDirect") (b := "ite") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "bindDirect") (b := "retVoid") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "bindDirect") (b := "letMutable") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "bindDirect") (b := "directCall") (by intro same; simp only [String.reduceEq] at same)),
    if_pos rfl]
  exact bindDirectProofs

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

def forRangeEntry : RegistryEntry ``Stmt.forRange (stmtSchema ``Stmt.forRange) := by
  rw [stmtSchema,
    if_neg (differentLabels (a := "forRange") (b := "letValue") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "forRange") (b := "assignVar") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "forRange") (b := "ret") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "forRange") (b := "ite") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "forRange") (b := "retVoid") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "forRange") (b := "letMutable") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "forRange") (b := "directCall") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "forRange") (b := "bindDirect") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "forRange") (b := "whileBounded") (by intro same; simp only [String.reduceEq] at same)),
    if_pos rfl]
  exact forRangeProofs

def constantEntry : RegistryEntry ``Decl.constant (declSchema ``Decl.constant) := by
  rw [declSchema,
    if_pos rfl]
  exact constantProofs

def functionEntry : RegistryEntry ``Decl.function (declSchema ``Decl.function) := by
  rw [declSchema,
    if_neg (differentLabels (a := "function") (b := "constant") (by intro same; simp only [String.reduceEq] at same)),
    if_pos rfl]
  exact functionProofs

end Gabbro.Core.Ast.Semantik
