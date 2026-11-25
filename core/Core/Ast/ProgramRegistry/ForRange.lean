module

public import Core.Ast.Semantik.ProgramForms
public import Core.Ast.Semantik.ProgramObligations
public import Core.Ast.Semantik.Formen

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Waechter

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
    ((forRangeForm scope result).befehl args).sicherheitsPflichten ((forRangeForm scope result).fragment args) platform [] (tabLeer _ inv) (fun b _ => rfl)⟩

-- Mirror Befehl.sicher to discharge the six SchrittSicherheit fields at every concrete cut.
theorem forRange_sicher (scope : Scope) (result : Option (Ty .value)) platform a :
    Sicherheit.RegelSicher (((forRangeForm scope result).fragment a).sicherheitsEinheit platform)
      ((forRangeForm scope result).befehl a) := by
  have inv : ((forRangeForm scope result).fragment a).klauseln.invariant = [] := by
    change (stmt ((forRangeForm scope result).produktion.tree a).2).klauseln.invariant = []
    exact stmt_keine_invarianten _
  exact ((forRangeForm scope result).befehl a).sicher ((forRangeForm scope result).fragment a) platform [] (tabLeer _ inv) (fun b _ => rfl)

-- Mirror binary_erfuellbar at the actual instruction and reachable pre-state.
theorem forRange_erfuellbar : forRangeJoint := by
  intro platform start
  let ctx : StatementContext := ([], none)
  let form := forRangeForm ctx.1 ctx.2
  let name : Identifier := keywordName 'x' [] (by decide) (fun _ member => (List.not_mem_nil member).elim)
  have ordinaryName : ordinaryLocal name := (directName_of_singleton (name := name) rfl).1
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

end Gabbro.Core.Ast.Semantik
