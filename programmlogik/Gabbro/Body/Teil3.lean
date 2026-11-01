module

public import Lean
public import Gabbro.Body.Teil2

@[expose] public section

namespace Gabbro.Body

inductive Stmt where
  /-- `carrier.slots[index].field = value;` -/
  | assign (carrier : String) (index : Expr) (field : String) (value : Expr)
  /-- `carrier.field = value;` at a record or a `format`. -/
  | assignField (carrier : String) (field : String) (value : Expr)
  /-- `name = value;` at a `static`. -/
  | assignGlobal (name : String) (value : Expr)
  /-- `let name = value;` -/
  | bindName (name : String) (value : Expr)
  | ite (cond : Expr) (thenB elseB : List Stmt)
  /-- `match e { Some(b) => …, None => … }` -- the only `match` form of the core. -/
  | onOption (subject : Expr) (binder : String) (onPresent onAbsent : List Stmt)
  /-- `f(a, b);` -- **a call, and it is taken over the callee's CONTRACT.**

      The callee is named, not inlined. What it does is looked up in an ENVIRONMENT that
      the theorem quantifies over, and the caller's theorem then carries the callee's
      contract as a HYPOTHESIS. *Nothing about the callee is assumed here* -- and that is
      the difference between compositional reasoning and an axiom about foreign code, which
      `refinement.rs` refuses for the reason that an axiom proves everything after it. -/
  | call (callee : String) (params : List String) (args : List Expr) (pre : Expr)
  /-- `let n = f(a, b);` -- **a call whose RESULT is bound.** The commonest call shape in the
      corpus, and it stays a STATEMENT: a callee may write, so an expression that contained
      it would no longer be pure and `eval` would have to carry the environment. -/
  | bindCall (name : String) (callee : String) (params : List String) (args : List Expr)
      (pre : Expr)
  /-- `let name = f(a, b) else (err) { … };` -- **the error propagation**: a callee that
      answers with a `reason` does not fill the binding; the `else` block runs with the
      reason bound to `err`, and ends (`M1` demands it). -/
  | bindCallElse (name : String) (callee : String) (params : List String) (args : List Expr)
      (pre : Expr) (err : String) (onErr : List Stmt)
  /-- `match e { Case => …, … }` over a `reason` -- the arm is picked by the case's name;
      no arm for the reason met is stuck (`M123` demands the enumeration be closed). -/
  | onReason (subject : Expr) (arms : List (String × List Stmt))
  /-- `match e { Case(b) => …, Case2 => …, … }` over a `tagged` value -- the arm by the
      case's name, the payload bound to the binder where the arm names one. `D005` demands
      the match be exhaustive, so a case no arm names is stuck, never silent. -/
  | onTag (subject : Expr) (arms : List (String × Option String × List Stmt))
  /-- `return f(a, b);` -- a call whose result is returned straight on. -/
  | retCall (callee : String) (params : List String) (args : List Expr) (pre : Expr)
  /-- `traverse … invariant P { … }` -- **a loop is an anonymous routine.**

      Its meaning is looked up in the same `Env` a call uses, under an id of its own. *That
      is not a shortcut: it is what a loop IS to a prover* -- something that runs an unknown
      number of times and leaves a state, and the only thing anyone knows about it is what
      the invariant says.

      **The invariant is DATA and not decoration.** The theorem over a body that loops carries
      the loop rule as a hypothesis --

          \forall t, eval t inv = some (.bool true)
                 \to eval (\rho id t).1 inv = some (.bool true)

      -- and that hypothesis is discharged by a separate theorem over `body`. The body is
      carried too, so that theorem has something to talk about. -/
  | loop (id : String) (inv : Expr) (body : List Stmt)
  /-- `locks S { … }` -- **a critical section, and it costs no memory model.**

      Its meaning is the body's. That looks naive read alone and is not: the whole model is
      SEQUENTIAL, and what makes a sequential reading sound is exactly that the lock is held
      -- `H005`/`H006`/`H012`/`H016` carry it, and the header books it as `races`. *A lock
      that added state here would be the second register over a statement a pass already
      discharges.*

      **The lock's NAME stays in the datum** all the same. Inlining the body would erase the
      critical section from the record, and a reader could no longer see where one was. -/
  | locked (lock : String) (body : List Stmt)
  /-- `breaking I { … }` -- **the SUSPENSION of a table invariant, and it is not an exit.**

      Its meaning is the body's, and the ground is the same as at a lock: what `breaking`
      changes is not which statements run but which DUTY holds in between. The transition is
      the body's; the duty stands beside it as an obligation of its own -- `maintains I`
      appears in the register as its own line and is refused there (`table-invariant`,
      quantified over every slot).

      **The names travel in the datum, and that is the load-bearing half.** This reading is
      sound exactly as far as this channel cannot state a table invariant, and it cannot.
      *Should it ever get a quantifier, this name is where an invariant channel has to read
      off where the suspension lay* -- a record that inlined the body would have erased it.

      It stood refused as `non-local-exit` until 2026-08-28, in one arm with `leave` and
      `next`, under the sentence *"a non-local exit out of a named loop"*. It is neither
      non-local nor an exit: four obligations of the register paid for one word covering
      three things (`messung/AUSSETZUNG.md`). -/
  | breaking (invariants : List String) (body : List Stmt)
  /-- `A = v publishes { p, q };` -- **a release store, and it costs no memory model either.**

      The store itself is a store. What makes the PAYLOAD visible to the reader is
      `release_stellt_sichtbarkeit_her` -- an assumption of the axiom layer since
      `beispiele/06-annahmen.gab`, `unfalsifiable` with its reason written out, and rebooked
      there by `K100.2`. *In a single world the visibility is automatic; the assumption is
      what licenses reading it that way.*

      **The payload travels in the datum all the same.** It is the surface that rests on the
      assumption rather than on the transition -- and a record that dropped it would hide
      exactly which places those are. -/
  | publish (atomic : String) (value : Expr) (payload : List String)
  /-- `let n = A awaits { p, q };` -- the other half of the pairing. -/
  | awaitLoad (name : String) (atomic : String) (payload : List String)
  /-- `let n = A exchange …;` -- an atomic swap: the old value is bound, the new one stored. -/
  | exchangeWith (name : String) (atomic : String) (value : Expr)
  | ret (value : Option Expr)
  /-- `next m;` -- **the end of one pass of the innermost loop** (2026-09-07): the
      iteration ends here, in this state, the invariant has to hold in it, and the loop goes
      on. *A `next` of an OUTER loop is refused by the emitter* -- it would have to carry
      the mark through a `.loop` step that does not run the body. -/
  | exit
  /-- `leave m;` -- **the end of the innermost loop**: the pass ends here, the invariant has
      to hold, and no pass follows (`iterate` stops). A `return` inside a loop is desugared
      to this by the emitter, with the value in a local. -/
  | leave
  deriving Repr

/-- **What every routine of the program does, as a map from name to state transformer.**

    **The pair is the state AND the result.** A callee can both write and return, and an
    environment that gave only the state would make `let x = f(a);` unstatable -- which is
    22 of the corpus's call sites.

    A theorem about a body that calls does not fix `Env`: it QUANTIFIES over it and assumes
    only what the callee's contract says. *An environment fixed by the emitter would be the
    emitter deciding what a callee does, and that is exactly the decision a proof is for.* -/
abbrev Env := String → State → State × Option Value

/-- The carrier a place belongs to -- what an `effects { writes X }` clause names. -/
def Place.carrier : Place → String
  | .slot c _ _ => c
  | .field c _ => c
  | .global n => n

/-! ### 4.1 What a theorem may ASSUME about a callee -- and nothing else

    Three hypotheses, each read off a DECLARATION by the emitter (2026-09-07), and together
    they are the whole of what "compositional over the contract" means here:

      `Contract ρ f pre post`   the callee's `ensures`, under its `requires`;
      `Frame ρ f writes`        the callee's `effects` list -- every place outside it survives
                                (`Passlogik.Wirkung.huelle_deckt` is what licenses reading
                                the DECLARED list as the transitive one);
      `LoopRule ρ id inv`       a loop preserves its `invariant` -- and the theorem that
                                discharges it is emitted beside the routine's.

    *None of them is an axiom.* Each is a hypothesis of the theorem that uses it, and each is
    discharged by another theorem of the same register -- the callee's `ensures` by the
    callee's duty, the loop rule by the loop's. **What remains assumed is what the plumbing
    carries** (the `effects` list is complete, `E008`/`E010`), exactly as before.
-/

/-! ### 4.0 The well-typed WORLD

    `Place → Value` is an unconstrained map; that a slot declared `u32` carries a number is
    hypothesis `U2`. Since 2026-09-07 the hypothesis has ONE form for the whole unit: a
    `Typing` -- the shape every declared place carries, written by the emitter out of the
    declarations -- and `WF Γ σ`, that the world respects it. **The two theorems below are
    what make it cost a person nothing**: a store of a value of the right shape keeps the
    world well-formed, and a read from a well-formed world yields a value of the declared
    shape. `gabbro_simp` carries both.
-/

abbrev Typing := Place → Option Shape

def WF (Γ : Typing) (σ : World) : Prop :=
  ∀ p sh, Γ p = some sh → (σ p).hasShape sh = true

theorem WF_store (Γ : Typing) (σ : World) (p : Place) (v : Value) (h : WF Γ σ)
    (hv : ∀ sh, Γ p = some sh → v.hasShape sh = true) : WF Γ (store σ p v) := by
  intro q sh hq
  simp only [store]
  split
  · rename_i hqp; subst hqp; exact hv sh hq
  · exact h q sh hq

theorem WF_int (Γ : Typing) (σ : World) (p : Place) (h : WF Γ σ) (hp : Γ p = some .int) :
    ∃ n, σ p = .int n := by
  have := h p .int hp
  cases hv : σ p <;> simp only [Value.hasShape, hv, Value.int.injEq, exists_eq', Bool.false_eq_true] at this ⊢

theorem WF_intIn (Γ : Typing) (σ : World) (p : Place) (lo hi : Int) (h : WF Γ σ)
    (hp : Γ p = some (.intIn lo hi)) : ∃ n, σ p = .int n ∧ lo ≤ n ∧ n ≤ hi := by
  have := h p (.intIn lo hi) hp
  cases hv : σ p <;> simp only [Value.hasShape, hv, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq, Value.int.injEq, exists_eq_left', Bool.false_eq_true] at this ⊢
  exact this

theorem WF_bool (Γ : Typing) (σ : World) (p : Place) (h : WF Γ σ) (hp : Γ p = some .bool) :
    ∃ b, σ p = .bool b := by
  have := h p .bool hp
  cases hv : σ p <;> simp only [Value.hasShape, hv, Bool.false_eq_true, Value.bool.injEq, exists_eq'] at this ⊢

theorem WF_opt (Γ : Typing) (σ : World) (p : Place) (h : WF Γ σ) (hp : Γ p = some .opt) :
    σ p = .absent ∨ ∃ n, σ p = .present n := by
  have := h p .opt hp
  cases hv : σ p <;> simp only [Value.hasShape, hv, Bool.false_eq_true, reduceCtorEq, exists_const, or_false, Value.present.injEq, exists_eq', or_true] at this ⊢

theorem WF_sum (Γ : Typing) (σ : World) (p : Place) (cs : List (String × Option (Option (Int × Int)))) (h : WF Γ σ)
    (hp : Γ p = some (.sum cs)) :
    ∃ t q, σ p = .tagged t q ∧ Shape.caseOk cs t q = true := by
  have := h p (.sum cs) hp
  cases hv : σ p <;> simp only [Value.hasShape, hv, Bool.false_eq_true, Value.tagged.injEq] at this ⊢
  exact ⟨_, _, ⟨rfl, rfl⟩, this⟩

/-- **The callee's contract.** `pre` is a `Prop` over the entry state: the world is
    well-formed, and the callee's precondition expression -- the SAME expression the call
    gets stuck on in `step` (the declared shapes of the parameters, the `requires`, and
    every invariant the callee maintains) -- holds. So a caller that gets past the call
    has, by that very fact, the second half of what the contract asks for; the first it
    carries along, because every post promises it back. `post` sees the entry state (for
    `old(...)`), the exit state and the result. -/
def Contract (ρ : Env) (f : String) (pre : State → Prop)
    (post : State → State → Option Value → Prop) : Prop :=
  ∀ t, pre t → post t (ρ f t).1 (ρ f t).2

/-- **The callee's frame.** A place whose carrier is not in the `writes` list is untouched. -/
def Frame (ρ : Env) (f : String) (writes : List String) : Prop :=
  ∀ t p, p.carrier ∉ writes → (ρ f t).1.world p = t.world p

/-- **The loop rule.** From a well-formed state that satisfies the invariant, the loop
    leaves a well-formed one that does. `wf` is the unit's well-formedness of the WORLD
    (`U2`); the shapes of the LOCALS in scope travel inside `inv`, as `hasShape` conjuncts
    the emitter adds -- a local whose shape the invariant did not carry would come out of
    the loop unconstrained. -/
def LoopRule (ρ : Env) (id : String) (wf : State → Prop) (inv : Expr) : Prop :=
  ∀ t, wf t → eval t inv = some (.bool true) →
    wf (ρ id t).1 ∧ eval (ρ id t).1 inv = some (.bool true)

/-- Bind a list of names to a list of values, left to right. -/
def bindAll : List String → List Value → Binding → Binding
  | [], _, β => β
  | _, [], β => β
  | n :: ns, v :: vs, β => bindAll ns vs (bindLocal β n v)

/-- Evaluate a list of expressions, or get stuck on the first that does. -/
def evalAll (s : State) : List Expr → Option (List Value)
  | [] => some []
  | e :: es =>
      match eval s e, evalAll s es with
      | some v, some vs => some (v :: vs)
      | _, _ => none

/-- How a descent ends. **`stuck` is an outcome of its own and not a `running`** -- a model
    that conflated getting stuck with carrying on would prove things about a body that never
    runs. -/
inductive Outcome where
  | running (s : State)
  | returned (s : State) (v : Option Value)
  /-- The body of a loop ended through `next` -- a THIRD way to end, beside falling off
      the end and returning. `finalState` has it; `finalValue` has not. -/
  | exited (s : State)
  /-- The body of a loop ended through `leave`, and so did the loop. -/
  | left (s : State)
  | stuck

mutual

def step (ρ : Env) : Stmt → State → Outcome
  | .assign c i f e, s =>
      match eval s i, eval s e with
      | some (.int k), some v => .running { s with world := store s.world (.slot c k f) v }
      | _, _ => .stuck
  | .assignField c f e, s =>
      match eval s e with
      | some v => .running { s with world := store s.world (.field c f) v }
      | none => .stuck
  | .assignGlobal n e, s =>
      match eval s e with
      | some v => .running { s with world := store s.world (.global n) v }
      | none => .stuck
  | .bindName n e, s =>
      match eval s e with
      | some v => .running { s with local' := bindLocal s.local' n v }
      | none => .stuck
  | .ite c t e, s =>
      match eval s c with
      | some (.bool true) => exec ρ t s
      | some (.bool false) => exec ρ e s
      | _ => .stuck
  | .onOption g bn onP onA, s =>
      match eval s g with
      | some (.present k) => exec ρ onP { s with local' := bindLocal s.local' bn (.int k) }
      | some .absent => exec ρ onA s
      | _ => .stuck
  -- **A call changes the WORLD and nothing else.** Gabbro is call by value, so a callee
  -- cannot touch the caller's local names -- the caller's `local'` survives by construction
  -- rather than by a frame argument.
  -- **And a call whose PRECONDITION does not hold gets STUCK** (2026-09-07). `pre` is the
  -- callee's `requires`, evaluated in the callee's entry state -- so the strong goal
  -- (*the body runs to an end*) demands at every call site that the caller established
  -- it. That is the `V` duty of the register, carried by the theorem of the caller instead
  -- of by a goal of its own; `refinement.rs` could only write it for a literal or an
  -- untouched parameter, and this reads the state at the call.
  | .call f ps as pre, s =>
      match evalAll s as with
      | some vs =>
          let t := { world := s.world, local' := bindAll ps vs (fun _ => .absent) }
          match eval t pre with
          | some (.bool true) => .running { s with world := (ρ f t).1.world }
          | _ => .stuck
      | none => .stuck
  | .bindCall n f ps as pre, s =>
      match evalAll s as with
      | some vs =>
          let t := { world := s.world, local' := bindAll ps vs (fun _ => .absent) }
          match eval t pre with
          | some (.bool true) =>
            -- **The call's answer is read through the PROJECTIONS, never by matching the
            -- pair** (2026-09-07): `(ρ f t).1` and `(ρ f t).2` are what a contract talks
            -- about, and a `match ρ f t with | (t', v)` would stand in a proof until someone
            -- wrote the pair's eta by hand.
            match (ρ f t).2 with
            -- **A callee that returns nothing cannot fill a binding.** Getting stuck is
            -- the right answer: `M1` refuses the program, and a model that invented a
            -- value here would prove things about a program the checker rejects.
            | some v => .running { world := (ρ f t).1.world, local' := bindLocal s.local' n v }
            | none => .stuck
          | _ => .stuck
      | none => .stuck
  | .bindCallElse n f ps as pre err onErr, s =>
      match evalAll s as with
      | some vs =>
          let t := { world := s.world, local' := bindAll ps vs (fun _ => .absent) }
          match eval t pre with
          | some (.bool true) =>
            match (ρ f t).2 with
            | some (.reason x) =>
                exec ρ onErr { world := (ρ f t).1.world, local' := bindLocal s.local' err (.reason x) }
            | some v => .running { world := (ρ f t).1.world, local' := bindLocal s.local' n v }
            -- **A callee with an error channel and NO value** (`fn f() or R`) answers
            -- nothing on success: the binding gets no value (`absent`), and the body goes
            -- on -- what `let ok = f() else (e) { … }` means for such a callee.
            | none => .running { world := (ρ f t).1.world, local' := bindLocal s.local' n .absent }
          | _ => .stuck
      | none => .stuck
  | .onReason g arms, s =>
      match eval s g with
      | some (.reason x) => pickArm ρ arms x s
      | _ => .stuck
  | .onTag g arms, s =>
      match eval s g with
      | some (.tagged x p) => pickTag ρ arms x p s
      | _ => .stuck
  | .retCall f ps as pre, s =>
      match evalAll s as with
      | some vs =>
          let t := { world := s.world, local' := bindAll ps vs (fun _ => .absent) }
          match eval t pre with
          | some (.bool true) => .returned { s with world := (ρ f t).1.world } (ρ f t).2
          | _ => .stuck
      | none => .stuck
  -- **A loop leaves a state the environment gives**, exactly as a call does. What is known
  -- about that state is what the loop rule -- carried as a hypothesis, never as an axiom --
  -- says about the invariant.
  -- **And a loop entered with its invariant FALSE gets stuck** (2026-09-07). The loop
  -- rule -- carried as `LoopRule` -- says only that the invariant is PRESERVED; that it
  -- holds on entry is the caller's half, and a model that let a body walk into a loop
  -- without it would let the rule conclude from nothing.
  --
  -- **And the loop leaves the WHOLE state, locals included** (2026-09-07). Until today the
  -- arm kept the caller's locals and took only the world -- wrong for every body that
  -- counts in a local inside the loop (`n = n + 1;`), which Gabbro allows and the corpus
  -- does. A `let` of the body leaks into the binding as a name nothing after the loop may
  -- read (`namen.rs`), so leaking it is harmless.
  -- **A `match` and not an `if`**: an `if` on an equation over `Option Value` asks for a
  -- `Decidable` instance, and a proof that unfolds the step then lets the kernel EVALUATE
  -- the decision -- over a `forallSlots` of four thousand slots. Measured: *deep recursion
  -- detected*, on the first loop of `beispiele/01`.
  | .loop id inv _, s =>
      match eval s inv with
      | some (.bool true) => .running (ρ id s).1
      | _ => .stuck
  | .locked _ b, s => exec ρ b s
  -- **A suspension changes no state.** See the constructor: the transition is the body's,
  -- the duty stands beside it.
  | .breaking _ b, s => exec ρ b s
  | .publish a e _, s =>
      match eval s e with
      | some v => .running { s with world := store s.world (.global a) v }
      | none => .stuck
  | .awaitLoad n a _, s =>
      .running { s with local' := bindLocal s.local' n (s.world (.global a)) }
  | .exchangeWith n a e, s =>
      match eval s e with
      | some v =>
          .running { world := store s.world (.global a) v,
                     local' := bindLocal s.local' n (s.world (.global a)) }
      | none => .stuck
  | .ret none, s => .returned s none
  | .ret (some e), s =>
      match eval s e with
      | some v => .returned s (some v)
      | none => .stuck
  | .exit, s => .exited s
  | .leave, s => .left s

def exec (ρ : Env) : List Stmt → State → Outcome
  | [], s => .running s
  | a :: rest, s =>
      match step ρ a s with
      | .running s' => exec ρ rest s'
      | o => o

/-- The arm of a `match` over a `reason`, by the case's name. -/
def pickArm (ρ : Env) : List (String × List Stmt) → String → State → Outcome
  | [], _, _ => .stuck
  | (n, b) :: rest, x, s => if n = x then exec ρ b s else pickArm ρ rest x s

/-- The arm of a `match` over a `tagged` value: by the case's name, the payload bound. -/
def pickTag (ρ : Env) : List (String × Option String × List Stmt) → String → Option Int → State → Outcome
  | [], _, _, _ => .stuck
  | (n, bd, b) :: rest, x, p, s =>
      if n = x then
        match bd, p with
        | some v, some k => exec ρ b { s with local' := bindLocal s.local' v (.int k) }
        | none, _ => exec ρ b s
        | some _, none => .stuck
      else pickTag ρ rest x p s

end

/-- The state at the end -- **`return` and running off the end both end in a state**, and for
    a postcondition the two are the same thing: the state afterwards. Only `stuck` has none. -/
def finalState : Outcome → Option State
  | .running s => some s
  | .returned s _ => some s
  | .exited s => some s
  | .left s => some s
  | .stuck => none

/-- The result, where the body produced one. For an `ensures` that names `result`. -/
def finalValue : Outcome → Option Value
  | .returned _ (some v) => some v
  | _ => none

/-! ### 5.1 What ties the environment to the BODIES -- and who discharges what

    Everything above quantifies over `Env`. The two definitions below say what it means for
    an `Env` to BE the program, and the two theorems after them are the whole of the wiring:
    a duty proved over a body yields the callee's `Contract`; a loop's body preserving the
    invariant yields its `LoopRule`. **The emitter instantiates them per unit** -- no person
    writes an induction over the call graph or over the iterations.
-/

end Gabbro.Body
