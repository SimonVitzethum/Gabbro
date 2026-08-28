/-
  File:    Gabbro/Body.lean
  Subject: What a Gabbro BODY means -- the statement descent as a state transition.

  WHY THIS FILE IS NOT IN `passlogik/`
    `passlogik/` formalises the CHECKER -- range lattices, effect hulls, rank order. Those
    are statements about PASSES. This one is a statement about PROGRAMS, and the two must not
    live in one namespace: a theorem about a pass read as a theorem about a program is a
    different claim with different consequences.

  WHAT IT CLOSES
    `passlogik/README.md` books the same missing item four times (`B1`, `L1`, `P2`, `R1`):

        "The STATEMENT DESCENT -- what a body does statement by statement -- stands in NONE
         of the seven files."

    And `messung/P6.md` measures what hangs on it: of 62 obligations, `refinement.rs` refuses
    seventeen with `body-effect`, because there is no meaning of a Gabbro body -- ten `N`,
    six `E`, and the one `R`.

  WHAT IS MODELLED
    A WORLD as an assignment of places (a table's slot field, a `static`) to values, a local
    binding for `let` names, and the descent over the SEQUENTIAL CORE: `let`, assignment,
    `if`, `match` over `option`, `return`.

  WHAT THE PLUMBING ALREADY CARRIES -- and what this model therefore need not build
    This is the whole reason the file is short. Every line names the theorem that allows it:

      overflow      Integers are `Int`, unbounded.
                    -> `Passlogik.Bereich.passt_dann_kein_ueberlauf` (`M104`)
      frame         The frame IS the declared `effects` list; a place outside it survives.
                    -> `Passlogik.Wirkung.huelle_deckt` (`E005`/`E008`)
      alias         Two distinct `Place`s are distinct places, full stop.
                    -> the alias passes; `A1` closed 2026-08-24 with `R007`
      termination   The core has no loop -- and the loop forms carry their measure.
                    -> `K008`/`K009`, `Bereich.keine_unendliche_verengung`
      races         Sequential reading is sound; `Held(L)` holds at the body's entry.
                    -> `H005`/`H006`/`H012`/`H016`

    **Hence there is NO heap model here, NO separation logic, NO pointers and NO
    concurrency.** A state is a map from places to values. Whoever reads this file without
    reading the plumbing alongside will take the model for naive -- it is the cashed-out form
    of this folder's thesis.

  ASSUMED RATHER THAN PROVED
    (U1) That the EMITTER (`crates/gabbro-check/src/lean.rs`) translates a Gabbro body into a
         `Stmt` datum correctly does not stand here. That is the same seam the other seven
         files have -- only this one is drawn mechanically and is therefore mutable.
         `instrumente/pruefe-lean-beweis.sh` drives it in both directions.
    (U2) The WELL-FORMED state -- that a slot field carries a value of its declared shape --
         is a hypothesis and not a consequence. The emitter writes it per unit out of the
         `table` declaration; it stands visibly in the theory.
    (U3) Two distinct carrier names denote two distinct objects. That is the alias statement,
         and the alias passes carry it -- no line here does.

  DOES NOT PROVE
    That a body terminates (the core has no loop -- there is nothing to show), that it is
    overflow-free (`M104`), or that it respects its frame (`E005`).
-/

namespace Gabbro.Body

/-! ## 1. Values

    Four forms, and the list is closed. `option index into T` is `absent`/`present` -- **not
    `Option Int`**, because a value has to be comparable with every other value, and a sum
    type over `Int` would be two levels.
-/

inductive Value where
  | int (n : Int)
  | bool (t : Bool)
  | absent
  | present (n : Int)
  deriving DecidableEq, Repr

/-! ## 2. Places

    A place is a location in the WORLD. Two forms: a table's slot field with an evaluated
    index, and a `static`.

    **`DecidableEq` here IS the alias freedom.** Two places are equal or distinct and nothing
    in between -- the statement that costs an alias analysis in the general case and that
    Gabbro carries.
-/

inductive Place where
  | slot (carrier : String) (index : Int) (field : String)
  /-- A field of a RECORD or a `format` -- `s.len`, `header.e_entry`. **No index**: a record
      is one object, not a table of them, and giving it a dummy index would make two
      different things one `Place` and let a slot alias a record field. -/
  | field (carrier : String) (name : String)
  | global (name : String)
  deriving DecidableEq

abbrev World := Place → Value
abbrev Binding := String → Value

/-- The state: the world and the local names. -/
structure State where
  world : World
  local' : Binding

/-- A pointwise write. **The frame falls out here** -- every other place survives. -/
def store (σ : World) (p : Place) (v : Value) : World :=
  fun q => if q = p then v else σ q

/-- **`bindLocal`, not `bind`.** A definition called `bind` is shadowed by `Bind.bind` from
    core, and `simp [bind]` then resolves to the class method instead of this function --
    measured: the speech test's TRUE theorem stopped going through, with the message
    *"Expected a proposition, but found `Binding → String → Value → Binding`"*. -/
def bindLocal (β : Binding) (n : String) (v : Value) : Binding :=
  fun m => if m = n then v else β m

@[simp] theorem store_here (σ : World) (p : Place) (v : Value) : store σ p v p = v := by
  simp [store]

@[simp] theorem store_elsewhere (σ : World) (p q : Place) (v : Value) (h : q ≠ p) :
    store σ p v q = σ q := by
  simp [store, h]

@[simp] theorem bindLocal_here (β : Binding) (n : String) (v : Value) : bindLocal β n v n = v := by
  simp [bindLocal]

@[simp] theorem bindLocal_elsewhere (β : Binding) (n m : String) (v : Value) (h : m ≠ n) :
    bindLocal β n v m = β m := by
  simp [bindLocal, h]

/-! ## 3. Expressions

    The list covers exactly what `refinement.rs` already has a term for, plus the PLACE WITH
    A SUFFIX -- and that is the whole gain. `messung/P6.md` §4.3 names it as the thing the
    Isabelle emitter has no model of: *"a place with suffixes is a location in the WORLD"*.
    Here is the world.
-/

inductive UnOp where
  | not
  | neg
  deriving DecidableEq, Repr

inductive BinOp where
  | add | sub | mul
  | eq | ne | lt | le | gt | ge
  | and | or
  deriving DecidableEq, Repr

inductive Expr where
  | lit (v : Value)
  | name (n : String)
  | place (carrier : String) (index : Expr) (field : String)
  | global (name : String)
  | un (op : UnOp) (a : Expr)
  | bin (op : BinOp) (a b : Expr)
  /-- `Some(e)` -- the one value CONSTRUCTOR the corpus writes. `None` needs none: it is a
      literal. **A body that writes an option and could not say `Some` would have to be
      refused whole**, and `27-freiliste` is exactly that shape. -/
  | someOf (a : Expr)
  /-- `s.len` -- a field of a record or a `format`. -/
  | fieldOf (carrier : String) (name : String)
  deriving Repr

/-- **An evaluation may GET STUCK.** `none` means the value did not have the shape the
    operator needs. That is not an error case one may define away -- the world is an
    unconstrained map, and that a slot field carries the shape its declaration names is
    hypothesis `U2` and stands per unit as a premise.

    *A model that substituted a default value here would prove statements for a reason the
    machine does not have* -- the same trap `messung/P6.md` §2.1 names for `nat`. -/
def unop : UnOp → Value → Option Value
  | .not, .bool t => some (.bool (!t))
  | .neg, .int n => some (.int (-n))
  | _, _ => none

def binop : BinOp → Value → Value → Option Value
  | .add, .int a, .int b => some (.int (a + b))
  | .sub, .int a, .int b => some (.int (a - b))
  | .mul, .int a, .int b => some (.int (a * b))
  | .lt, .int a, .int b => some (.bool (decide (a < b)))
  | .le, .int a, .int b => some (.bool (decide (a ≤ b)))
  | .gt, .int a, .int b => some (.bool (decide (a > b)))
  | .ge, .int a, .int b => some (.bool (decide (a ≥ b)))
  | .and, .bool x, .bool y => some (.bool (x && y))
  | .or, .bool x, .bool y => some (.bool (x || y))
  -- **Equality stands over ALL values**, not only over numbers: `c.slots[s].elter == None`
  -- is exactly this form, and it is the commonest postcondition in the corpus.
  | .eq, x, y => some (.bool (decide (x = y)))
  | .ne, x, y => some (.bool (decide (x ≠ y)))
  | _, _, _ => none

def eval (s : State) : Expr → Option Value
  | .lit v => some v
  | .name n => some (s.local' n)
  | .global g => some (s.world (.global g))
  | .place c i f =>
      match eval s i with
      | some (.int k) => some (s.world (.slot c k f))
      | _ => none
  | .un op a =>
      match eval s a with
      | some v => unop op v
      | none => none
  | .bin op a b =>
      match eval s a, eval s b with
      | some x, some y => binop op x y
      | _, _ => none
  | .someOf a =>
      match eval s a with
      | some (.int n) => some (.present n)
      | _ => none
  | .fieldOf c f => some (s.world (.field c f))

/-! ### 3.1 The WELL-FORMEDNESS of a place

    The world is an unconstrained map: nothing about `Place → Value` says that a `bool` slot
    field carries a truth value. **That is deliberate** -- a model that builds the shape into
    the type can no longer NAME the premise, and an unnamed premise is the most expensive
    kind.

    The emitter writes per unit which shape a field has, **and it reads that from the
    DECLARATION** -- not from how the body uses the field. *A premise guessed from the use
    makes the goal easier, not harder; it is exactly the quiet weakening this channel is
    built against.*
-/

def isInt (v : Value) : Prop := ∃ n, v = .int n
def isBool (v : Value) : Prop := ∃ t, v = .bool t
def isOption (v : Value) : Prop := v = .absent ∨ ∃ n, v = .present n

/-! ## 4. Statements -- the SEQUENTIAL CORE

    Seven kinds of `StmtArt`, and `messung/` measures that they carry **12 of the 17** open
    body obligations: `Let`, `LetSonst`, assignment, `Wenn`, `Match`, `Return`, `Ruf`. What
    does not stand here the emitter refuses by name.

    `Ruf` is absent on purpose and is not an omission: a call is to be taken COMPOSITIONALLY
    over the callee's contract, never over its body. As long as the emitter has no gate for
    that, it refuses -- **a refused obligation costs a number; an inlined body costs the
    number's meaning.**
-/

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
  | call (callee : String) (params : List String) (args : List Expr)
  /-- `let n = f(a, b);` -- **a call whose RESULT is bound.** The commonest call shape in the
      corpus, and it stays a STATEMENT: a callee may write, so an expression that contained
      it would no longer be pure and `eval` would have to carry the environment. -/
  | bindCall (name : String) (callee : String) (params : List String) (args : List Expr)
  /-- `return f(a, b);` -- a call whose result is returned straight on. -/
  | retCall (callee : String) (params : List String) (args : List Expr)
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
  | ret (value : Option Expr)
  deriving Repr

/-- **What every routine of the program does, as a map from name to state transformer.**

    **The pair is the state AND the result.** A callee can both write and return, and an
    environment that gave only the state would make `let x = f(a);` unstatable -- which is
    22 of the corpus's call sites.

    A theorem about a body that calls does not fix `Env`: it QUANTIFIES over it and assumes
    only what the callee's contract says. *An environment fixed by the emitter would be the
    emitter deciding what a callee does, and that is exactly the decision a proof is for.* -/
abbrev Env := String → State → State × Option Value

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
  | .call f ps as, s =>
      match evalAll s as with
      | some vs =>
          .running { s with
            world := (ρ f { world := s.world, local' := bindAll ps vs (fun _ => .absent) }).1.world }
      | none => .stuck
  | .bindCall n f ps as, s =>
      match evalAll s as with
      | some vs =>
          match ρ f { world := s.world, local' := bindAll ps vs (fun _ => .absent) } with
          -- **A callee that returns nothing cannot fill a binding.** Getting stuck is the
          -- right answer: `M1` refuses the program, and a model that invented a value here
          -- would prove things about a program the checker rejects.
          | (t, some v) => .running { world := t.world, local' := bindLocal s.local' n v }
          | (_, none) => .stuck
      | none => .stuck
  | .retCall f ps as, s =>
      match evalAll s as with
      | some vs =>
          match ρ f { world := s.world, local' := bindAll ps vs (fun _ => .absent) } with
          | (t, v) => .returned { s with world := t.world } v
      | none => .stuck
  -- **A loop leaves a state the environment gives**, exactly as a call does. What is known
  -- about that state is what the loop rule -- carried as a hypothesis, never as an axiom --
  -- says about the invariant.
  | .loop id _ _, s => .running { s with world := (ρ id s).1.world }
  | .ret none, s => .returned s none
  | .ret (some e), s =>
      match eval s e with
      | some v => .returned s (some v)
      | none => .stuck

def exec (ρ : Env) : List Stmt → State → Outcome
  | [], s => .running s
  | a :: rest, s =>
      match step ρ a s with
      | .running s' => exec ρ rest s'
      | o => o

end

/-- The state at the end -- **`return` and running off the end both end in a state**, and for
    a postcondition the two are the same thing: the state afterwards. Only `stuck` has none. -/
def finalState : Outcome → Option State
  | .running s => some s
  | .returned s _ => some s
  | .stuck => none

/-- The result, where the body produced one. For an `ensures` that names `result`. -/
def finalValue : Outcome → Option Value
  | .returned _ (some v) => some v
  | _ => none

/-! ## 5. What holds over EVERY body

    These theorems belong to the model, not to a unit -- the emitter may use them without
    rewriting them per file.
-/

/-- **An empty sequence changes nothing.** -/
@[simp] theorem exec_nil (ρ : Env) (s : State) : exec ρ [] s = .running s := by
  simp [exec]

/-- **The descent is deterministic** -- it is a function, so this holds by construction. The
    theorem stands here anyway, because it is the statement a RELATIONAL model would have to
    prove at this point. -/
theorem exec_deterministic (ρ : Env) (as : List Stmt) (s : State) (o₁ o₂ : Outcome)
    (h₁ : exec ρ as s = o₁) (h₂ : exec ρ as s = o₂) : o₁ = o₂ := by
  subst h₁; exact h₂

/-- **A place no assignment names survives a single step.**

    This is the frame statement in its smallest form. It stands here for assignment, because
    that is where the frame arises; over a whole sequence it is carried by
    `Passlogik.Wirkung.huelle_deckt` out of the `effects` list, and the two meet at the pass. -/
theorem assign_leaves_others (ρ : Env) (c : String) (i e : Expr) (f : String) (s s' : State)
    (p : Place) (h : step ρ (.assign c i f e) s = .running s')
    (hne : ∀ k, p ≠ .slot c k f) : s'.world p = s.world p := by
  simp only [step] at h
  split at h
  · rename_i k v hi he
    injection h with h
    subst h
    simp only [store]
    rw [if_neg (hne k)]
  · exact absurd h (by simp)

end Gabbro.Body

/-! ## 6. The proof bundle

    **`gabbro_simp` unfolds the model, and it stands OUTSIDE the namespace on purpose.**
    A tactic declared inside `Gabbro.Body` is not in scope for a specification that merely
    `open`s it -- measured: every use reported *"unknown tactic"*, and the goal then stood
    open beside an error that looked like a typo. The names inside are fully qualified for
    the same reason.

    It lives here and not in the generated file so that a specification need not know the
    model's internals, and so a change to the model reaches every proof through one place.
    *A tactic copied into every generated module is one statement in as many places as there
    are files.*
-/

open Lean.Parser.Tactic in
macro "gabbro_simp" : tactic =>
  `(tactic| simp [Gabbro.Body.exec, Gabbro.Body.step, Gabbro.Body.eval, Gabbro.Body.unop,
                  Gabbro.Body.binop, Gabbro.Body.finalState, Gabbro.Body.finalValue,
                  Gabbro.Body.store, Gabbro.Body.bindLocal, Gabbro.Body.bindAll,
                  Gabbro.Body.evalAll])

-- The same, with the caller's own facts: `gabbro_simp [hf, mySpec]`.
open Lean.Parser.Tactic in
macro "gabbro_simp" "[" ts:simpLemma,* "]" : tactic =>
  `(tactic| simp [Gabbro.Body.exec, Gabbro.Body.step, Gabbro.Body.eval, Gabbro.Body.unop,
                  Gabbro.Body.binop, Gabbro.Body.finalState, Gabbro.Body.finalValue,
                  Gabbro.Body.store, Gabbro.Body.bindLocal, Gabbro.Body.bindAll,
                  Gabbro.Body.evalAll, $ts,*])
