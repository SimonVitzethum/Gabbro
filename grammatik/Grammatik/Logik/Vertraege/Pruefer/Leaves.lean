module

public import Grammatik.Logik.Vertraege.Pruefer.Control.Narrowing
public import Grammatik.Logik.Vertraege.Pruefer.Control.Memory

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.VC
open Invarianten.Frag.Symbolic Symbolic

variable {D : Deklaration} {V : Vertrag D} {S : SperrInv D} {program : Programm D}

theorem symbolic_values_equal (valuation : Assignment Nat) (before after : World D)
    (same : assignment before = assignment after) : values valuation before = values valuation after := by
  funext key
  cases key with
  | inl memory => exact congrFun same memory
  | inr _ => rfl

def storeStatement {context : Context A next} (policy : A → CallObligation program)
    {l : Bool} (symbols : SymEnv D Nat Γ) (bounded : symbols.Bounded next)
    (code : Stmt D V l Γ Λ Λ) (expression : Expr D Γ Λ τ) (reads : List (D.Tab ⊕ D.Glob))
    (key : Observation D) (store : World D → Wert D τ → World D)
    (corresponds : ∀ world value, assignment (store world value) = (assignment world).bind key (scalarValue τ value))
    (execute : ∀ valuation (runtime : Runtime program (fun _ => []) S) world actual,
      symbols.Realizes valuation world actual →
      execStmtH S runtime.oracle runtime.environment runtime.passes runtime.calls code world actual =
        let read := world.lese Λ reads
        .ok (store read (eval read expression read actual)) actual)
    (goals : Symbolic.Goals (program := program) (S := S) context V Γ) :
    Except Frag.Refusal (Symbolic.StatementCondition policy code symbols goals) := do
  let pre ← Symbolic.selectValue symbols bounded expression
    (fun actual value item runtime world => goals.normal.holds item runtime (store world value) actual)
    (fun more larger symbol valueBounded => do
      let post ← goals.normal.encode more larger symbols (symbols.bounded_mono bounded larger)
      return storeCondition symbols (symbols.bounded_mono bounded larger) symbol valueBounded key store corresponds
        goals.normal.holds post)
  return (pre.read Λ reads).map (fun valuation item runtime world ready actual realized _ _ => by
    unfold Runtime.wpS
    rw [execute valuation runtime world actual realized]
    exact ready actual ((symbols.realizes_world actual valuation world (world.lese Λ reads)).mp realized))

def slotStoreStatement {context : Context A next} (policy : A → CallObligation program)
    {l : Bool} (symbols : SymEnv D Nat Γ) (bounded : symbols.Bounded next)
    (code : Stmt D V l Γ Λ Λ) (table : D.Tab) (field : D.Feld table)
    (index : Expr D Γ Λ (.index (D.count table))) (expression : Expr D Γ Λ (D.typ table field))
    (reads : List (D.Tab ⊕ D.Glob))
    (execute : ∀ (runtime : Runtime program (fun _ => []) S) world actual,
      execStmtH S runtime.oracle runtime.environment runtime.passes runtime.calls code world actual =
        let read := world.lese Λ reads
        .ok (read.schreibSlot table Λ (eval read index read actual).n field (eval read expression read actual)) actual)
    (goals : Symbolic.Goals (program := program) (S := S) context V Γ) :
    Except Frag.Refusal (Symbolic.StatementCondition policy code symbols goals) := do
  let encoded ← Invarianten.Frag.Symbolic.translate index symbols
  let offset ← encoded.constantIndex
  storeStatement policy symbols bounded code expression reads (.slot table field offset.val)
    (fun world value => world.schreibSlot table Λ offset.val field value)
    (fun world value => assignment_schreibSlot world table field offset.val Λ value)
    (fun valuation runtime world actual realized => by
      rw [execute runtime world actual]
      exact congrArg (fun position => Ausgang.ok
        ((world.lese Λ reads).schreibSlot table Λ position field
          (eval (world.lese Λ reads) expression (world.lese Λ reads) actual)) actual)
        (offset.property valuation (world.lese Λ reads) actual
          ((symbols.realizes_world actual valuation world (world.lese Λ reads)).mp realized))) goals

theorem scalarValue_int_cast {kind : Ty} (numeric : kind = .int lo hi) (value : Wert D kind) :
    scalarValue kind value = (numeric ▸ value : Wert D (.int lo hi)).n := by
  cases numeric
  rfl

/-- A transition proves the previous stage and substitutes the new stage in
    the continuation. The slot identity is the same one used for a store. -/
def shiftCondition {context : Context A next} (policy : A → CallObligation program)
    {l : Bool} (symbols : SymEnv D Nat Γ) (bounded : symbols.Bounded next)
    (table : D.Tab) (field : D.Feld table) (numeric : D.typ table field = .int lo hi)
    (index : Expr D Γ Λ (.index (D.count table))) (source target : Int) (fits : lo ≤ target ∧ target ≤ hi)
    (edge : D.erlaubt table field source target = true) (writes : V.schreibt table = true) (access : darf D table Λ)
    (goals : Symbolic.Goals (program := program) (S := S) context V Γ) :
    Except Frag.Refusal (Symbolic.StatementCondition policy
      (.shift table field numeric index source target fits edge writes access : Stmt D V l Γ Λ Λ) symbols goals) := do
  let encoded ← Invarianten.Frag.Symbolic.translate index symbols
  let offset ← encoded.constantIndex
  let key := Observation.slot table field offset.val
  let payload : Wert D (D.typ table field) := numeric ▸ (⟨target, fits.1, fits.2⟩ : Zahl lo hi)
  let post ← goals.normal.encode next (Nat.le_refl next) symbols bounded
  let store := storeCondition symbols bounded (.known payload) trivial key
    (fun world value => world.schreibSlot table Λ offset.val field value)
    (fun world value => assignment_schreibSlot world table field offset.val Λ value)
    goals.normal.holds post
  let reads := (.inl table :: index.orte)
  return {
    formula := .and (.eq (.var (.inl key)) (.konst source)) store.formula
    sound := fun valuation item present runtime world valid actual realized _ _ => by
      let read := world.lese Λ reads
      have locals := (symbols.realizes_world actual valuation world read).mp realized
      have atSlot := offset.property valuation read actual locals
      have before : scalarValue (D.typ table field) (read.slots table offset.val field) = source := valid.1
      have sourceMatches := (scalarValue_int_cast numeric (read.slots table offset.val field)).symm.trans before
      have stored := (store.read Λ reads).sound valuation item present runtime world valid.2
        actual locals payload rfl
      unfold Runtime.wpS
      simp only [execStmtH, ← show read = world.lese Λ (.inl table :: index.orte) from rfl]
      rw [atSlot, if_pos sourceMatches]
      exact stored }

def memoryIdentityStatement {context : Context A next} (policy : A → CallObligation program)
    {l : Bool} (symbols : SymEnv D Nat Γ) (bounded : symbols.Bounded next)
    (code : Stmt D V l Γ Λ Λ')
    (execute : ∀ (runtime : Runtime program (fun _ => []) S) world actual,
      ∃ after, assignment after = assignment world ∧
        execStmtH S runtime.oracle runtime.environment runtime.passes runtime.calls code world actual = .ok after actual)
    (goals : Symbolic.Goals (program := program) (S := S) context V Γ) :
    Except Frag.Refusal (Symbolic.StatementCondition policy code symbols goals) := do
  let post ← goals.normal.encode next (Nat.le_refl next) symbols bounded
  return {
    formula := post.formula
    sound := fun valuation item present runtime world valid actual realized _ _ => by
      obtain ⟨after, same, result⟩ := execute runtime world actual
      unfold Runtime.wpS
      rw [result]
      exact post.sound valuation item present runtime after (by
        rw [symbolic_values_equal valuation after world same]
        exact valid) actual ((symbols.realizes_world actual valuation world after).mp realized) }

def leafCondition {context : Context A next} (policy : A → CallObligation program)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (code : Stmt D V l Γ Λ Λ')
    (symbols : SymEnv D Nat Γ) (bounded : symbols.Bounded next)
    (goals : Symbolic.Goals (program := program) (S := S) context V Γ) :
    Except Frag.Refusal (Symbolic.StatementCondition policy code symbols goals) :=
  match code with
  | .assignGlob name expression hw hl =>
      storeStatement policy symbols bounded (.assignGlob name expression hw hl) expression expression.orte (.glob name)
        (fun world value => world.schreibGlob name Λ value)
        (fun world value => assignment_schreibGlob world name Λ value)
        (fun _ _ _ _ _ => rfl) goals
  | .publish name expression payload hp hw hl =>
      storeStatement policy symbols bounded (.publish name expression payload hp hw hl) expression expression.orte (.glob name)
        (fun world value => world.schreibGlob name Λ value)
        (fun world value => assignment_schreibGlob world name Λ value)
        (fun _ _ _ _ _ => rfl) goals
  | .assignSlot table field index expression hw hl =>
      slotStoreStatement policy symbols bounded (.assignSlot table field index expression hw hl)
        table field index expression (index.orte ++ expression.orte) (fun _ _ _ => rfl) goals
  | .assignThru pointer table ht field index expression hw hl =>
      slotStoreStatement policy symbols bounded (.assignThru pointer table ht field index expression hw hl)
        table field index expression (pointer.orte ++ index.orte ++ expression.orte) (fun _ _ _ => rfl) goals
  | .assignThruOwn pointer table ht field index expression m st ho he hg hw hl =>
      slotStoreStatement policy symbols bounded (.assignThruOwn pointer table ht field index expression m st ho he hg hw hl)
        table field index expression (pointer.orte ++ index.orte ++ expression.orte) (fun _ _ _ => rfl) goals
  | .assignVar name expression => do
      let pre ← Symbolic.selectValue symbols bounded expression
        (fun actual value item runtime world => goals.normal.holds item runtime world (actual.set name value))
        (fun more larger symbol valueBounded => do
          let post ← goals.normal.encode more larger (symbols.set name symbol)
            (symbols.bounded_set more (symbols.bounded_mono bounded larger) name symbol valueBounded)
          return post.map (fun valuation _ _ world ready actual realized value selected =>
            ready (actual.set name value) (symbols.realizes_set actual valuation world name symbol value realized selected)))
      return (pre.read Λ expression.orte).map (fun valuation _ _ world ready actual realized _ _ =>
        ready actual ((symbols.realizes_world actual valuation world (world.lese Λ expression.orte)).mp realized))
  | .advances m stage h hs =>
      memoryIdentityStatement policy symbols bounded (.advances m stage h hs) (fun _ world _ => ⟨world, rfl, rfl⟩) goals
  | .retires m stage h hs =>
      memoryIdentityStatement policy symbols bounded (.retires m stage h hs) (fun _ world _ => ⟨world, rfl, rfl⟩) goals
  | .transition r hk register hm hl mask bits =>
      memoryIdentityStatement policy symbols bounded (.transition r hk register hm hl mask bits) (fun _ world _ =>
        ⟨world.fragt (.inr (.inl register)), by funext key; cases key <;> rfl, rfl⟩) goals
  | .regWrite r hk expression =>
      memoryIdentityStatement policy symbols bounded (.regWrite r hk expression) (fun _ world _ =>
        ⟨world.lese Λ expression.orte, assignment_lese _ _ _, rfl⟩) goals
  | .ret expression _ => do
      let pre ← Symbolic.returnCondition symbols bounded V.erg expression goals.returned
      return (pre.read Λ expression.orte).map (fun valuation _ _ world ready actual realized _ _ =>
        ready actual ((symbols.realizes_world actual valuation world (world.lese Λ expression.orte)).mp realized))
  | .retWhy _ _ => do
      let pre ← goals.reason.encode next (Nat.le_refl next) .nil trivial
      return pre.map (fun _ _ _ _ ready _ _ _ _ => ready .nil trivial)
  | .leave _ => do
      let pre ← goals.escape.encode next (Nat.le_refl next) symbols bounded
      return pre.map (fun _ _ _ _ ready actual realized _ _ => ready actual realized)
  | .next _ => do
      let pre ← goals.again.encode next (Nat.le_refl next) symbols bounded
      return pre.map (fun _ _ _ _ ready actual realized _ _ => ready actual realized)
  | .shift table field numeric index source target fits edge writes access =>
      shiftCondition policy symbols bounded table field numeric index source target fits edge writes access goals
  | .assignSlotRef .. => .error (.unsupported "contract reference store needs a tracked cell identity")
  | .putBytes .. => .error (.unsupported "contract byte store needs bytewise observation substitution")
  | .onOption .. => .error (.unsupported "contract option dispatch needs a typed payload observation")
  | .onTag .. => .error (.unsupported "contract tagged dispatch needs a typed payload observation")
  | .axiomCall .. | .axiomCallElse .. => .error (.unsupported "contract oracle call needs quantified answer and poststate observations")
  | .forever .. => .error (.unsupported "contract forever loop needs a checked inductive invariant")
  | .consumeTraverse table member edge .tru bound mass body =>
      if empty : (D.count table).toNat = 0 then
        memoryIdentityStatement policy symbols bounded (.consumeTraverse table member edge .tru bound mass body)
          (fun _ world _ => by
            let checked := world.lese Λ (Expr.tru (D := D) (Γ := Γ) (Λ := Λ)).orte
            let after := checked.lese Λ (member.orte ++ edge.orte)
            have indices : alleIndizes (D.count table) = [] := by
              simp only [alleIndizes, empty, List.range_zero, List.filterMap_nil]
            refine ⟨after, (assignment_lese checked Λ _).trans (assignment_lese world Λ _), ?_⟩
            simp only [execStmtH, verbrauchLauf, eval, wahr?, Bool.true_eq_false, ↓reduceIte,
              verbrauchSel, indices, verbrauchWahl, verbrauchWahlAux, List.all_nil, Bool.not_true]) goals
      else .error (.unsupported "contract consuming traversal needs a checked membership and measure invariant")
  | .consumeTraverse .. => .error (.unsupported "contract consuming traversal needs a checked membership and measure invariant")
  | _ => .error (.unsupported "contract structured statement needs the recursive control compiler")

end Gabbro.Grammatik.Vertraege.Pruefer
