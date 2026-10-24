/-
  File:      Grammatik/Berechenbarkeit/Brainfuck/ToTM2.lean
  Subject:   Every byte-Brainfuck instruction compiled to Mathlib's existing TM2.

  Four stacks hold the two tape sides, unread input and reversed output. The finite
  local state is one byte; labels have the program's finite size. This is an intermediate
  compilation theorem, not yet the missing implementation of these stacks in Gabbro.
-/
import Grammatik.Berechenbarkeit.Brainfuck.Machine

namespace Gabbro.Grammatik.Berechenbarkeit.Brainfuck

inductive Stack where
  | left | right | input | output
  deriving DecidableEq

abbrev TMStatement (n : Nat) := Turing.TM2.Stmt (fun _ : Stack => Byte) (Fin (n + 1)) Byte
abbrev TMState (n : Nat) := Turing.TM2.Cfg (fun _ : Stack => Byte) (Fin (n + 1)) Byte

def storageOf {n : Nat} (s : State n) : Stack → List Byte
  | .left => s.left
  | .right => s.right
  | .input => s.remainingInput
  | .output => s.reversedOutput

def label {n : Nat} (pc : Fin (n + 1)) : Option (Fin (n + 1)) :=
  if pc.val < n then some pc else none

def encode {n : Nat} (s : State n) : TMState n := ⟨label s.pc, s.head, storageOf s⟩

/-- Reaching the end is a halt in this very step, not an extra observable instruction. -/
def jump {n : Nat} (pc : Fin (n + 1)) : TMStatement n :=
  if pc.val < n then .goto (fun _ => pc) else .halt

theorem jump_exec {n : Nat} (pc : Fin (n + 1)) (b : Byte) (storage : Stack → List Byte) :
    Turing.TM2.stepAux (jump pc) b storage = ⟨label pc, b, storage⟩ := by
  unfold jump label
  split <;> rfl

def compileInstruction {n : Nat} (op : Instruction n) (next : Fin (n + 1)) : TMStatement n :=
  match op with
  | .right => .push .left id (.pop .right (fun _ b => b.getD 0) (jump next))
  | .left => .push .right id (.pop .left (fun _ b => b.getD 0) (jump next))
  | .increment => .load increment (jump next)
  | .decrement => .load decrement (jump next)
  | .input => .pop .input (fun _ b => b.getD 0) (jump next)
  | .output => .push .output id (jump next)
  | .open exit => .branch (fun b => decide (b = 0)) (jump exit) (jump next)
  | .close body => .branch (fun b => decide (b = 0)) (jump next) (jump body)

/-- A finite, syntax-directed program. Runtime dispatch uses no unbounded host evaluator. -/
def compile {n : Nat} (p : Program n) (pc : Fin (n + 1)) : TMStatement n :=
  if running : pc.val < n then
    compileInstruction (p.code.get ⟨pc.val, running⟩) (successor pc running)
  else .halt

/-- Each source command becomes genuine operations of Mathlib's TM2, with the same head,
    tape sides, remaining input and output history. There is no assumed instruction oracle. -/
theorem instruction_correct {n : Nat} (op : Instruction n) (next : Fin (n + 1)) (s : State n) :
    Turing.TM2.stepAux (compileInstruction op next) s.head (storageOf s) =
      encode (execute op next s) := by
  cases op with
  | right =>
      simp only [compileInstruction, Turing.TM2.stepAux, id_eq, jump_exec]
      simp only [Function.update_of_ne (by decide : Stack.right ≠ Stack.left), storageOf]
      simp only [encode, execute, List.headD_eq_head?_getD]
      congr 1
      funext k; cases k <;> simp [storageOf, Function.update]
  | left =>
      simp only [compileInstruction, Turing.TM2.stepAux, id_eq, jump_exec]
      simp only [Function.update_of_ne (by decide : Stack.left ≠ Stack.right), storageOf]
      simp only [encode, execute, List.headD_eq_head?_getD]
      congr 1
      funext k; cases k <;> simp [storageOf, Function.update]
  | increment =>
      simp only [compileInstruction, Turing.TM2.stepAux, jump_exec, encode, execute]
      congr 1
  | decrement =>
      simp only [compileInstruction, Turing.TM2.stepAux, jump_exec, encode, execute]
      congr 1
  | input =>
      simp only [compileInstruction, Turing.TM2.stepAux, jump_exec, storageOf, encode, execute,
        List.headD_eq_head?_getD]
      congr 1
      funext k; cases k <;> simp [storageOf, Function.update]
  | output =>
      simp only [compileInstruction, Turing.TM2.stepAux, id_eq, jump_exec, encode, execute]
      congr 1
      funext k; cases k <;> simp [storageOf, Function.update]
  | «open» exit =>
      by_cases h : s.head = 0 <;>
        simp only [compileInstruction, Turing.TM2.stepAux, h, decide_true, decide_false,
          Bool.cond_true, Bool.cond_false, jump_exec, encode, execute, ↓reduceIte] <;> congr 1
  | close body =>
      by_cases h : s.head = 0 <;>
        simp only [compileInstruction, Turing.TM2.stepAux, h, decide_true, decide_false,
          Bool.cond_true, Bool.cond_false, jump_exec, encode, execute, ↓reduceIte] <;> congr 1

/-- Exact one-step preservation, including normal halt. -/
theorem step_correct {n : Nat} (p : Program n) (s : State n) :
    Turing.TM2.step (compile p) (encode s) = (step p s).map encode := by
  by_cases running : s.pc.val < n
  · simp only [encode, label, running, ↓reduceIte, Turing.TM2.step, compile, step]
    exact congrArg some (instruction_correct _ _ s)
  · simp [encode, label, running, Turing.TM2.step, step]

/-- A refinement in Mathlib's existing transition framework. -/
theorem respects {n : Nat} (p : Program n) :
    StateTransition.Respects (step p) (Turing.TM2.step (compile p)) (fun s t => encode s = t) := by
  intro s t h
  subst t
  cases hs : step p s with
  | none => simpa [hs] using step_correct p s
  | some u =>
      refine ⟨encode u, rfl, .single ?_⟩
      simpa only [Option.mem_def, hs, Option.map_some] using step_correct p s

/-- Full partial evaluation commutes with compilation: both halting and divergence. -/
theorem evaluation_correct {n : Nat} (p : Program n) (s : State n) :
    StateTransition.eval (Turing.TM2.step (compile p)) (encode s) =
      encode <$> StateTransition.eval (step p) s :=
  StateTransition.tr_eval' _ _ _ (respects p) s

/-- Termination in either machine is equivalent, without a claim to decide it. -/
theorem termination_iff {n : Nat} (p : Program n) (s : State n) :
    (StateTransition.eval (Turing.TM2.step (compile p)) (encode s)).Dom ↔
      (StateTransition.eval (step p) s).Dom :=
  StateTransition.tr_eval_dom (respects p) rfl

theorem reachable_preservation {n : Nat} (p : Program n) {s t : State n}
    (h : StateTransition.Reaches (step p) s t) :
    Turing.TM2.Reaches (compile p) (encode s) (encode t) := by
  obtain ⟨u, hu, hrun⟩ := StateTransition.tr_reaches (respects p) rfl h
  rwa [← hu] at hrun

/-- Every intermediate target state is the encoding of a reachable source state. This
    preserves output prefixes even when the source never reaches a final state. -/
theorem reachable_reflection {n : Nat} (p : Program n) (s : State n) {u : TMState n}
    (h : Turing.TM2.Reaches (compile p) (encode s) u) :
    ∃ t, StateTransition.Reaches (step p) s t ∧ u = encode t := by
  induction h with
  | refl => exact ⟨s, .refl, rfl⟩
  | @tail u v _ huv ih =>
      obtain ⟨t, ht, rfl⟩ := ih
      have he : Turing.TM2.step (compile p) (encode t) = some v := huv
      rw [step_correct] at he
      cases hs : step p t with
      | none => simp [hs] at he
      | some w =>
          simp only [hs, Option.map_some, Option.some.injEq] at he
          exact ⟨w, ht.tail hs, he.symm⟩

theorem steps_iff_reaches {n : Nat} (p : Program n) (s t : State n) :
    (∃ k, Steps p k s t) ↔ StateTransition.Reaches (step p) s t := by
  constructor
  · rintro ⟨k, h⟩
    induction h with
    | zero => exact .refl
    | more hs _ ih => exact .head hs ih
  · intro h
    refine Relation.ReflTransGen.head_induction_on h ⟨0, .zero t⟩ ?_
    intro a b hab _ ih
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, .more hab hk⟩

theorem haltsWith_iff_eval {n : Nat} (p : Program n) (input output : List Byte) :
    HaltsWith p input output ↔
      ∃ s, s ∈ StateTransition.eval (step p) (initial input) ∧ s.output = output := by
  constructor
  · rintro ⟨k, s, hrun, hhalt, hout⟩
    exact ⟨s, StateTransition.mem_eval.mpr ⟨(steps_iff_reaches _ _ _).mp ⟨k, hrun⟩, hhalt⟩, hout⟩
  · rintro ⟨s, hs, hout⟩
    obtain ⟨hrun, hhalt⟩ := StateTransition.mem_eval.mp hs
    obtain ⟨k, hk⟩ := (steps_iff_reaches _ _ _).mpr hrun
    exact ⟨k, s, hk, hhalt, hout⟩

def TMHaltsWith {n : Nat} (p : Program n) (input output : List Byte) : Prop :=
  ∃ t, t ∈ StateTransition.eval (Turing.TM2.step (compile p)) (encode (initial input)) ∧
    (t.stk .output).reverse = output

/-- **All well-formed byte-Brainfuck programs compile to the existing TM2 with exactly
    the same halting/output behavior.** The Gabbro backend is a separate remaining obligation. -/
theorem compiler_correct {n : Nat} (p : Program n) (input output : List Byte) :
    HaltsWith p input output ↔ TMHaltsWith p input output := by
  rw [haltsWith_iff_eval]
  unfold TMHaltsWith
  rw [evaluation_correct]
  constructor
  · rintro ⟨s, hs, hout⟩
    exact ⟨encode s, (Part.mem_map_iff _).mpr ⟨s, hs, rfl⟩, hout⟩
  · rintro ⟨t, ht, hout⟩
    obtain ⟨s, hs, rfl⟩ := (Part.mem_map_iff _).mp ht
    exact ⟨s, hs, hout⟩

end Gabbro.Grammatik.Berechenbarkeit.Brainfuck
