module

public import Core.Ast.Semantik.ProgramForms
public import Core.Ast.Semantik.ProgramObligations
public import Core.Ast.Semantik.Formen

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Waechter

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
    | record _ => rfl
    | tagged _ => rfl
    | table _ => rfl
    | effectGroup _ => rfl
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
    | record _ => rfl
    | tagged _ => rfl
    | table _ => rfl
    | effectGroup _ => rfl
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
  have ord : directName name := mainName_direct
  have validNone : ∀ t ∈ (none : Option WrittenType).toList, WrittenType.valid [] t := by
    intro t mem
    cases mem
  let first : Decl [] [] := .function name ord [] none validNone none (.braces .done) List.nodup_nil (by intro h; cases h) none
  let a : Surface.ProgramArgs := ⟨[], [], first, .done⟩
  let defIns : Befehl := .definiere name [] none 0 3 false [] none
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

end Gabbro.Core.Ast.Semantik
