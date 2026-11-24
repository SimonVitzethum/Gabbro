module

public import Core.Ast.Semantik.ProgramForms
public import Core.Ast.Semantik.ProgramObligations
public import Core.Ast.Semantik.Formen

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Waechter

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
  have ordinaryName : directName name := directName_of_singleton rfl
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

def functionEntry : RegistryEntry ``Decl.function (declSchema ``Decl.function) := by
  rw [declSchema,
    if_neg (differentLabels (a := "function") (b := "constant") (by intro same; simp only [String.reduceEq] at same)),
    if_pos rfl]
  exact functionProofs

end Gabbro.Core.Ast.Semantik
