module

public import Lean
public import Gabbro.Body.Teil3
public import Gabbro.Body.Teil10RecRegeln

@[expose] public section

namespace Gabbro.Body

/-- **`ρ f` runs `body`.** Wherever the body ends, the environment's answer is that state and
    that value. Nothing is said where the body gets stuck -- a stuck body is what the duties
    exclude. -/
def Runs (ρ : Env) (f : String) (body : List Stmt) : Prop :=
  ∀ t s', finalState (exec ρ body t) = some s' →
    (ρ f t).1 = s' ∧ (ρ f t).2 = finalValue (exec ρ body t)

/-- One pass of a loop body per index in `ks`, the loop variable `v` bound to it -- and each
    pass ends by falling off, by `next` or by `leave`. A `retry`/`forever` has no variable;
    the emitter passes a name no body reads. -/
def iterate (ρ : Env) (body : List Stmt) (v : String) : List Int → State → Option State
  | [], t => some t
  | k :: ks, t =>
      match exec ρ body { t with local' := bindLocal t.local' v (.int k) } with
      | .running t' => iterate ρ body v ks t'
      | .exited t' => iterate ρ body v ks t'
      -- **`leave` ends the loop**: the remaining indices are not visited.
      | .left t' => some t'
      | _ => none

/-- **`ρ id` runs the loop `id`**: some sequence of passes of the body, and the state
    afterwards is the one the environment answers with. WHICH indices, and how many, is the
    domain's and the measure's business (`K008`/`K009`, `S005`), not this file's -- the rule
    below holds for every sequence. -/
def RunsLoop (ρ : Env) (id : String) (body : List Stmt) (v : String) : Prop :=
  ∀ t, ∃ ks t', iterate ρ body v ks t = some t' ∧ (ρ id t).1 = t'

/-- **A duty over the body IS the contract** -- for any environment that runs the body. -/
theorem contract_of_duty (ρ : Env) (f : String) (body : List Stmt) (pre : State → Prop)
    (post : State → State → Option Value → Prop) (hr : Runs ρ f body)
    (hd : ∀ t, pre t →
      ∃ s', finalState (exec ρ body t) = some s' ∧ post t s' (finalValue (exec ρ body t))) :
    Contract ρ f pre post := by
  intro t ht
  obtain ⟨s', hs', hp⟩ := hd t ht
  obtain ⟨h1, h2⟩ := hr t s' hs'
  rw [h1, h2]
  exact hp

/-- `t'` lies **below** `t` in the measure `e`: the measure is a non-negative integer in both
states and strictly smaller in `t'`. This is what `decreases e` on a recursive routine means. -/
def Below (e : Expr) (t' t : State) : Prop :=
  ∃ a b, eval t' e = some (.int a) ∧ eval t e = some (.int b) ∧ 0 ≤ a ∧ a < b

/-- **The bounded self-contract**: `ρ f` meets `post` under `pre` on every state strictly
below `s` in the measure `e`. What a self-recursive routine's duty may assume about its own
recursive call -- and only that. -/
def ContractBelow (ρ : Env) (f : String) (e : Expr) (s : State) (pre : State → Prop)
    (post : State → State → Option Value → Prop) : Prop :=
  ∀ t', pre t' → Below e t' s → post t' (ρ f t').1 (ρ f t').2

/-- **A self-recursive routine meeting its duty under the bounded self-contract IS its
contract** -- the duty may assume the contract for every call on a state strictly below the
current one in the measure `e`; induction over the measure lifts that to every state. The
person proves `hd` (their own logic); the induction lives here once. -/
theorem contract_of_duty_rec (ρ : Env) (f : String) (body : List Stmt) (pre : State → Prop)
    (post : State → State → Option Value → Prop) (e : Expr) (hr : Runs ρ f body)
    (hd : ∀ t, pre t → ContractBelow ρ f e t pre post →
      ∃ s', finalState (exec ρ body t) = some s' ∧ post t s' (finalValue (exec ρ body t))) :
    Contract ρ f pre post := by
  unfold ContractBelow at hd
  have key : ∀ (n : Nat) (t : State), pre t → (∀ b, eval t e = some (.int b) → b < n) →
      post t (ρ f t).1 (ρ f t).2 := by
    intro n
    induction n with
    | zero =>
      intro t ht hb
      obtain ⟨s', hs', hp⟩ := hd t ht (by
        intro t' _ ⟨a, b, _, hbt, ha, hab⟩
        have := hb b hbt
        omega)
      obtain ⟨h1, h2⟩ := hr t s' hs'
      rw [h1, h2]
      exact hp
    | succ n ih =>
      intro t ht hb
      obtain ⟨s', hs', hp⟩ := hd t ht (by
        intro t' ht' ⟨a, b, hat, hbt, ha, hab⟩
        apply ih t' ht'
        intro b' hb'
        rw [hat] at hb'
        have := hb b hbt
        cases hb'
        omega)
      obtain ⟨h1, h2⟩ := hr t s' hs'
      rw [h1, h2]
      exact hp
  intro t ht
  by_cases hm : ∃ b, eval t e = some (.int b)
  · obtain ⟨b, hb⟩ := hm
    apply key (b.toNat + 1) t ht
    intro b' hb'
    rw [hb] at hb'
    cases hb'
    omega
  · apply key 0 t ht
    intro b hb
    exact absurd ⟨b, hb⟩ hm

/-! ### Mutual recursion -- a CYCLE of routines, one induction

    `gerade` calls `ungerade` calls `gerade`: no routine's duty can assume the other's
    contract outright. What each may assume is the other's contract on states whose measure
    lies strictly below its own -- `BelowM`, the callee's `decreases` at the callee's state
    against the caller's at the caller's -- and one induction over that common bound gives
    every contract of the cycle. The members are data (`Member`), so that the theorem is
    stated once for cycles of every size. -/

structure Member where
  name : String
  body : List Stmt
  pre : State → Prop
  post : State → State → Option Value → Prop
  measure : Expr

/-- `t'` lies below `t` -- the measure `e'` at `t'` against the measure `e` at `t`. -/
def BelowM (e' e : Expr) (t' t : State) : Prop :=
  ∃ a b, eval t' e' = some (.int a) ∧ eval t e = some (.int b) ∧ 0 ≤ a ∧ a < b

/-- The contract of a cycle member `r'`, bounded by the measure `e` of the caller at `s`. -/
def ContractBelowM (ρ : Env) (r' : Member) (e : Expr) (s : State) : Prop :=
  ∀ t', r'.pre t' → BelowM r'.measure e t' s → r'.post t' (ρ r'.name t').1 (ρ r'.name t').2

/-- **Every member of a cycle meeting its duty under the bounded contracts of the cycle
    IS every contract of the cycle.** -/
theorem contracts_of_duties_rec (ρ : Env) (rs : List Member)
    (hr : ∀ r ∈ rs, Runs ρ r.name r.body)
    (hd : ∀ r ∈ rs, ∀ t, r.pre t → (∀ r' ∈ rs, ContractBelowM ρ r' r.measure t) →
      ∃ s', finalState (exec ρ r.body t) = some s' ∧ r.post t s' (finalValue (exec ρ r.body t))) :
    ∀ r ∈ rs, Contract ρ r.name r.pre r.post := by
  unfold ContractBelowM at hd
  have key : ∀ (n : Nat), ∀ r ∈ rs, ∀ t, r.pre t →
      (∀ b, eval t r.measure = some (.int b) → b < n) →
      r.post t (ρ r.name t).1 (ρ r.name t).2 := by
    intro n
    induction n with
    | zero =>
      intro r hr' t ht hb
      obtain ⟨s', hs', hp⟩ := hd r hr' t ht (by
        intro r' _ t' _ ⟨a, b, _, hbt, ha, hab⟩
        have := hb b hbt
        omega)
      obtain ⟨h1, h2⟩ := hr r hr' t s' hs'
      rw [h1, h2]
      exact hp
    | succ n ih =>
      intro r hr' t ht hb
      obtain ⟨s', hs', hp⟩ := hd r hr' t ht (by
        intro r' hr'' t' ht' ⟨a, b, hat, hbt, ha, hab⟩
        apply ih r' hr'' t' ht'
        intro b' hb'
        rw [hat] at hb'
        have := hb b hbt
        cases hb'
        omega)
      obtain ⟨h1, h2⟩ := hr r hr' t s' hs'
      rw [h1, h2]
      exact hp
  intro r hr' t ht
  by_cases hm : ∃ b, eval t r.measure = some (.int b)
  · obtain ⟨b, hb⟩ := hm
    apply key (b.toNat + 1) r hr' t ht
    intro b' hb'
    rw [hb] at hb'
    cases hb'
    omega
  · apply key 0 r hr' t ht
    intro b hb
    exact absurd ⟨b, hb⟩ hm

/-- **The loop's body preserving the invariant IS the loop rule** -- for any environment that
    runs the loop. The induction over the passes stands here once. -/
theorem looprule_of_body (ρ : Env) (id : String) (wf : State → Prop) (inv : Expr)
    (body : List Stmt) (v : String) (hr : RunsLoop ρ id body v)
    (hb : ∀ t (k : Int), wf t → eval t inv = some (.bool true) →
      ∃ t', finalState (exec ρ body { t with local' := bindLocal t.local' v (.int k) })
        = some t' ∧ wf t' ∧ eval t' inv = some (.bool true)) :
    LoopRule ρ id wf inv := by
  intro t hw ht
  obtain ⟨ks, t', hit, heq⟩ := hr t
  rw [heq]
  clear heq
  induction ks generalizing t with
  | nil => simp only [iterate, Option.some.injEq] at hit; subst hit; exact ⟨hw, ht⟩
  | cons k ks ih =>
    simp only [iterate] at hit
    split at hit
    · rename_i u hu
      obtain ⟨u', hu', hwf, hinv⟩ := hb t k hw ht
      rw [hu] at hu'; simp only [finalState, Option.some.injEq] at hu'; subst hu'
      exact ih u hwf hinv hit
    · rename_i u hu
      obtain ⟨u', hu', hwf, hinv⟩ := hb t k hw ht
      rw [hu] at hu'; simp only [finalState, Option.some.injEq] at hu'; subst hu'
      exact ih u hwf hinv hit
    · rename_i u hu
      obtain ⟨u', hu', hwf, hinv⟩ := hb t k hw ht
      rw [hu] at hu'; simp only [finalState, Option.some.injEq] at hu'; subst hu'
      simp only [Option.some.injEq] at hit; subst hit; exact ⟨hwf, hinv⟩
    · exact absurd hit (by simp only [reduceCtorEq, not_false_eq_true])

/-- **`ρ id` runs the loop `id` over indices of a RANGE** -- what a `traverse … over slots
    of T` (or any domain inside one table) visits: indices of that table, `lo ≤ k < hi`.
    Which of them, in which order, how often: the domain's business; that none lies
    outside: the checker's (`K008`/`K009`), and here the premise a pass may use. -/
def RunsLoopIn (ρ : Env) (id : String) (body : List Stmt) (v : String) (lo hi : Int) : Prop :=
  ∀ t, ∃ ks t', (∀ k ∈ ks, lo ≤ k ∧ k < hi) ∧ iterate ρ body v ks t = some t' ∧ (ρ id t).1 = t'

/-- **The loop rule from a pass that may assume its index is in range.** -/
theorem looprule_of_body_in (ρ : Env) (id : String) (wf : State → Prop) (inv : Expr)
    (body : List Stmt) (v : String) (lo hi : Int) (hr : RunsLoopIn ρ id body v lo hi)
    (hb : ∀ t (k : Int), lo ≤ k → k < hi → wf t → eval t inv = some (.bool true) →
      ∃ t', finalState (exec ρ body { t with local' := bindLocal t.local' v (.int k) })
        = some t' ∧ wf t' ∧ eval t' inv = some (.bool true)) :
    LoopRule ρ id wf inv := by
  intro t hw ht
  obtain ⟨ks, t', hks, hit, heq⟩ := hr t
  rw [heq]
  clear heq
  induction ks generalizing t with
  | nil => simp only [iterate, Option.some.injEq] at hit; subst hit; exact ⟨hw, ht⟩
  | cons k ks ih =>
    have hk : lo ≤ k ∧ k < hi := hks k (by simp only [List.mem_cons, true_or])
    have hks' : ∀ k ∈ ks, lo ≤ k ∧ k < hi := fun k' hk' => hks k' (by simp only [List.mem_cons, hk', or_true])
    simp only [iterate] at hit
    split at hit
    · rename_i u hu
      obtain ⟨u', hu', hwf, hinv⟩ := hb t k hk.1 hk.2 hw ht
      rw [hu] at hu'; simp only [finalState, Option.some.injEq] at hu'; subst hu'
      exact ih u hwf hinv hks' hit
    · rename_i u hu
      obtain ⟨u', hu', hwf, hinv⟩ := hb t k hk.1 hk.2 hw ht
      rw [hu] at hu'; simp only [finalState, Option.some.injEq] at hu'; subst hu'
      exact ih u hwf hinv hks' hit
    · rename_i u hu
      obtain ⟨u', hu', hwf, hinv⟩ := hb t k hk.1 hk.2 hw ht
      rw [hu] at hu'; simp only [finalState, Option.some.injEq] at hu'; subst hu'
      simp only [Option.some.injEq] at hit; subst hit; exact ⟨hwf, hinv⟩
    · exact absurd hit (by simp only [reduceCtorEq, not_false_eq_true])

/-! ### 5.1a Counting the passes -- `#pass` (agent b, 2026-09-08)

    **A counter incremented in a loop cannot be bounded by an invariant that does not know
    how often the loop runs.** `n ≤ 16` does not survive `n += 1`, and it never will: the
    rule above quantifies over EVERY state that satisfies the invariant, so a pass starting
    at `n = 16` has to be handled and cannot be. What the person means is `n ≤ <passes so
    far>`, and for that sentence to be sayable two things must be true of the model:

    * the number of passes already done is a value the invariant can name -- the ghost local
      `#pass`, bound to `0` right before the loop and increased by one by every pass (the
      emitter writes both; the increment is the pass's own first statement, so a `next` or a
      `leave` in the middle does not skip it);
    * the number of passes is BOUNDED. `RunsLoopIn` says every index lies in the domain's
      range and says nothing about how many passes there are, and no invariant can bound a
      counter without that. `RunsLoopN` adds the bound: at most `np` passes, where `np` is
      the domain's `count`. **This is a stronger assumption about the environment than
      `RunsLoopIn`, and it is exactly the sentence `by unvisited` makes** -- each slot of the
      domain is visited at most once, so a traversal of a table of `count N` runs at most `N`
      passes. It is assumed here, as the running of the body is assumed (`Runs`,
      `RunsLoop`, `RunsLoopIn`), and not proved: which indices a domain yields is the
      checker's business (`K008`/`K009`), not this file's.

    The pass may then assume `#pass = i` with `0 ≤ i < np`, and owes `#pass = i + 1` at its
    end -- one `simp` over the increment the emitter wrote, never a person's line. -/

/-- **`ρ id` runs the loop `id` over indices of a range, in at most `np` passes.** -/
def RunsLoopN (ρ : Env) (id : String) (body : List Stmt) (v : String) (lo hi np : Int) : Prop :=
  ∀ t, ∃ ks t', (∀ k ∈ ks, lo ≤ k ∧ k < hi) ∧ (ks.length : Int) ≤ np ∧
    iterate ρ body v ks t = some t' ∧ (ρ id t).1 = t'

/-- **The loop rule of a loop that counts its passes in the ghost local `pv`.** The same
    sentence as `LoopRule`, from a state in which the counter stands at zero -- which is
    where the emitter puts the loop, one `bindName` before it. -/
def LoopRuleP (ρ : Env) (id : String) (wf : State → Prop) (inv : Expr) (pv : String) : Prop :=
  ∀ t, wf t → eval t inv = some (.bool true) → t.local' pv = .int 0 →
    wf (ρ id t).1 ∧ eval (ρ id t).1 inv = some (.bool true)

/-- The induction over the passes, with the counter carried along. -/
theorem looprule_passes_aux (ρ : Env) (wf : State → Prop) (inv : Expr) (body : List Stmt)
    (v pv : String) (lo hi np : Int)
    (hb : ∀ t (k i : Int), lo ≤ k → k < hi → 0 ≤ i → i < np →
      t.local' pv = .int i → wf t → eval t inv = some (.bool true) →
      ∃ t', finalState (exec ρ body { t with local' := bindLocal t.local' v (.int k) }) = some t'
        ∧ wf t' ∧ eval t' inv = some (.bool true) ∧ t'.local' pv = .int (i + 1)) :
    ∀ (ks : List Int) (i : Int) (t u : State), (∀ k ∈ ks, lo ≤ k ∧ k < hi) →
      0 ≤ i → i + (ks.length : Int) ≤ np → t.local' pv = .int i →
      wf t → eval t inv = some (.bool true) → iterate ρ body v ks t = some u →
      wf u ∧ eval u inv = some (.bool true) := by
  intro ks
  induction ks with
  | nil =>
    intro i t u _ _ _ _ hw ht hit
    simp only [iterate, Option.some.injEq] at hit; subst hit; exact ⟨hw, ht⟩
  | cons k ks ih =>
    intro i t u hks h0 hlen hpv hw ht hit
    have hk : lo ≤ k ∧ k < hi := hks k (by simp only [List.mem_cons, true_or])
    have hks' : ∀ k' ∈ ks, lo ≤ k' ∧ k' < hi := fun k' hk' => hks k' (by simp only [List.mem_cons, hk', or_true])
    simp only [List.length_cons] at hlen
    have hlt : i < np := by omega
    have hlen' : i + 1 + (ks.length : Int) ≤ np := by omega
    obtain ⟨u', hu', hwf, hinv, hpv'⟩ := hb t k i hk.1 hk.2 h0 hlt hpv hw ht
    simp only [iterate] at hit
    split at hit
    · rename_i w hw'
      rw [hw'] at hu'; simp only [finalState, Option.some.injEq] at hu'; subst hu'
      exact ih (i + 1) w u hks' (by omega) hlen' hpv' hwf hinv hit
    · rename_i w hw'
      rw [hw'] at hu'; simp only [finalState, Option.some.injEq] at hu'; subst hu'
      exact ih (i + 1) w u hks' (by omega) hlen' hpv' hwf hinv hit
    · rename_i w hw'
      rw [hw'] at hu'; simp only [finalState, Option.some.injEq] at hu'; subst hu'
      simp only [Option.some.injEq] at hit; subst hit; exact ⟨hwf, hinv⟩
    · exact absurd hit (by simp only [reduceCtorEq, not_false_eq_true])

/-- **The loop rule from a pass that may assume its index is in range AND that it is the
    `i`-th of at most `np` passes.** -/
theorem looprule_of_body_p (ρ : Env) (id : String) (wf : State → Prop) (inv : Expr)
    (body : List Stmt) (v pv : String) (lo hi np : Int) (hr : RunsLoopN ρ id body v lo hi np)
    (hb : ∀ t (k i : Int), lo ≤ k → k < hi → 0 ≤ i → i < np →
      t.local' pv = .int i → wf t → eval t inv = some (.bool true) →
      ∃ t', finalState (exec ρ body { t with local' := bindLocal t.local' v (.int k) }) = some t'
        ∧ wf t' ∧ eval t' inv = some (.bool true) ∧ t'.local' pv = .int (i + 1)) :
    LoopRuleP ρ id wf inv pv := by
  intro t hw ht h0
  obtain ⟨ks, t', hks, hlen, hit, heq⟩ := hr t
  rw [heq]
  exact looprule_passes_aux ρ wf inv body v pv lo hi np hb ks 0 t t' hks (by omega)
    (by omega) h0 hw ht hit

/-! ## 5. What holds over EVERY body

    These theorems belong to the model, not to a unit -- the emitter may use them without
    rewriting them per file.
-/

/-- **An empty sequence changes nothing.** -/
@[simp] theorem exec_nil (ρ : Env) (s : State) : exec ρ [] s = .running s := by
  simp only [exec]

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
  · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])

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
                  Gabbro.Body.binop, Gabbro.Body.bits,
                  Gabbro.Body.finalState, Gabbro.Body.finalValue,
                  Gabbro.Body.bindLocal, Gabbro.Body.bindAll,
                  Gabbro.Body.evalAll, Gabbro.Body.allBelow_true_iff,
                  Gabbro.Body.eval_recOf, Gabbro.Body.eval_recGet, Gabbro.Body.eval_recSet,
                  ↓Gabbro.Body.recGet_after_recSet, ↓Gabbro.Body.recGet_frame,
                  ↓Gabbro.Body.recSet_idempotent, ↓Gabbro.Body.recSet_recGet,
                  ↓Gabbro.Body.eval_and_true_iff, ↓Gabbro.Body.eval_hasShape_true_iff, Gabbro.Body.orBool_true_iff,
                  Gabbro.Body.Contract, Gabbro.Body.Frame, Gabbro.Body.ContractBelow,
                  Gabbro.Body.Below, Gabbro.Body.ContractBelowM, Gabbro.Body.BelowM,
                  Gabbro.Body.LoopRule, Gabbro.Body.Place.carrier, Gabbro.Body.wrap, Gabbro.Body.pickArm, Gabbro.Body.pickTag])

-- The same, with the caller's own facts: `gabbro_simp [hf, mySpec]`.
open Lean.Parser.Tactic in
macro "gabbro_simp" "[" ts:simpLemma,* "]" : tactic =>
  -- the caller's definitions first (`_pre`, `_inv`, `_post`), so that the pre-lemmas
  -- (`↓eval_and_true_iff`) see the conjunction BEFORE `eval` is unfolded under it
  `(tactic| ((try simp only [$ts,*]); simp [Gabbro.Body.exec, Gabbro.Body.step, Gabbro.Body.eval, Gabbro.Body.unop,
                  Gabbro.Body.binop, Gabbro.Body.bits,
                  Gabbro.Body.finalState, Gabbro.Body.finalValue,
                  Gabbro.Body.bindLocal, Gabbro.Body.bindAll,
                  Gabbro.Body.evalAll, Gabbro.Body.allBelow_true_iff,
                  Gabbro.Body.eval_recOf, Gabbro.Body.eval_recGet, Gabbro.Body.eval_recSet,
                  ↓Gabbro.Body.recGet_after_recSet, ↓Gabbro.Body.recGet_frame,
                  ↓Gabbro.Body.recSet_idempotent, ↓Gabbro.Body.recSet_recGet,
                  ↓Gabbro.Body.eval_and_true_iff, ↓Gabbro.Body.eval_hasShape_true_iff, Gabbro.Body.orBool_true_iff,
                  Gabbro.Body.Contract, Gabbro.Body.Frame, Gabbro.Body.ContractBelow,
                  Gabbro.Body.Below, Gabbro.Body.ContractBelowM, Gabbro.Body.BelowM,
                  Gabbro.Body.LoopRule, Gabbro.Body.Place.carrier, Gabbro.Body.wrap, Gabbro.Body.pickArm, Gabbro.Body.pickTag, $ts,*]))

-- The same, and every hypothesis of the context as a rewrite: `simp [model, lemmas, *]`.
open Lean.Parser.Tactic in
macro "gabbro_simp_hyps" "[" ts:simpLemma,* "]" : tactic =>
  `(tactic| ((try simp only [$ts,*]); simp [Gabbro.Body.exec, Gabbro.Body.step, Gabbro.Body.eval, Gabbro.Body.unop,
                  Gabbro.Body.binop, Gabbro.Body.bits,
                  Gabbro.Body.finalState, Gabbro.Body.finalValue,
                  Gabbro.Body.bindLocal, Gabbro.Body.bindAll,
                  Gabbro.Body.evalAll, Gabbro.Body.allBelow_true_iff,
                  Gabbro.Body.eval_recOf, Gabbro.Body.eval_recGet, Gabbro.Body.eval_recSet,
                  ↓Gabbro.Body.recGet_after_recSet, ↓Gabbro.Body.recGet_frame,
                  ↓Gabbro.Body.recSet_idempotent, ↓Gabbro.Body.recSet_recGet,
                  ↓Gabbro.Body.eval_and_true_iff, ↓Gabbro.Body.eval_hasShape_true_iff, Gabbro.Body.orBool_true_iff,
                  Gabbro.Body.Contract, Gabbro.Body.Frame, Gabbro.Body.ContractBelow,
                  Gabbro.Body.Below, Gabbro.Body.ContractBelowM, Gabbro.Body.BelowM,
                  Gabbro.Body.LoopRule, Gabbro.Body.Place.carrier, Gabbro.Body.wrap, Gabbro.Body.pickArm, Gabbro.Body.pickTag, $ts,*, *]))

/-! ## 7. What the generated theorem ends with

    **`gabbro_auto` closes what the model closes by computation and leaves a `sorry` on
    what it does not** -- and that `sorry` is, by construction, the human's own logic: every
    hypothesis the goal could need is already in front of the turnstile (§4.1). The
    generated file counts its `sorry` warnings in `instrumente/pruefe-lean-beweis.sh`; a
    person proves the corresponding `_statement` in a file of their own and instantiates
    the unit's wiring theorem with it.

    What the automation does, in order, and each step is plumbing a person used to write:
      1. `gabbro_simp` runs the body;
      2. `gabbro_calls` instantiates every `Contract` and `LoopRule` hypothesis at every
         `ρ f t` the goal mentions, tries the precondition (well-typed world by
         `gabbro_wf`, the rest by computation), and rewrites with the frame;
      3. the conjunction of the promise is split, `gabbro_wf` closes the well-typedness
         of every stored world;
      4. what is left is the person's: a `requires` at a call the model could not
         compute, an invariant after a store, an equation between two indices.
-/
