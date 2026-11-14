module

public import Grammatik.Kern.Semantik.Evaluation.Aggregates.Values
public import Grammatik.Kern.Semantik.Semantik

@[expose] public section

namespace Gabbro.Grammatik

/-!
G has no aggregate identity or sharing store: `World.slots`, `World.globs`, and
`Env` contain `Wert`s. Argument evaluation constructs a fresh `Env` of values;
calls return a world and a result, never a callee environment.

There is also NO parameter-immutability invariant in this G syntax: `assignVar`
accepts any `Var Γ τ`, including a parameter in `Γ = D.params f`. The isolation
below comes from value semantics, not a prohibition on parameter assignment.
Sharing backing storage therefore needs a compiler simulation with a no-write,
copy-on-write, or ownership/liveness argument, including retained string views.
No such storage representation, move form, or new language rule is added here.
-/

variable {D : Deklaration}

/-- A context position, independent of the type of its value. -/
def Var.position : {Γ : Ctx} → {τ : Ty} → Var Γ τ → Nat
  | _, _, .here => 0
  | _, _, .there x => x.position + 1

/-- Replacing one binding leaves every distinct binding unchanged, even when
both bindings previously contained equal aggregate values. -/
theorem Env.get_set_other :
    ∀ {Γ : Ctx} {τ ν : Ty} (ρ : Env D Γ) (x : Var Γ τ) (y : Var Γ ν)
      (v : Wert D τ), x.position ≠ y.position → (ρ.set x v).get y = ρ.get y
  | _, _, _, .cons _ _, .here, .here, _, h => (h rfl).elim
  | _, _, _, .cons _ _, .here, .there _, _, _ => rfl
  | _, _, _, .cons _ _, .there _, .here, _, _ => rfl
  | _, _, _, .cons _ ρ, .there x, .there y, v, h =>
      Env.get_set_other ρ x y v (by intro heq; apply h; exact congrArg (· + 1) heq)

/-- G environments are determined by their typed binding values. -/
theorem Env.value_ext : ∀ {Γ : Ctx} (ρ η : Env D Γ),
    (∀ {τ : Ty} (x : Var Γ τ), ρ.get x = η.get x) → ρ = η
  | [], .nil, .nil, _ => rfl
  | _ :: _, .cons v ρ, .cons w η, h => by
      have hv : v = w := h .here
      have ht : ρ = η := Env.value_ext ρ η (fun x => h (.there x))
      cases hv
      cases ht
      rfl

/-- Every expression observes only the values of its environment. This is an
equality inside G, not a relation to a compiler's heap. -/
theorem eval_env_values {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (entry state : World D) (e : Expr D Γ Λ τ) (ρ η : Env D Γ)
    (h : ∀ {ν : Ty} (x : Var Γ ν), ρ.get x = η.get x) :
    eval entry e state ρ = eval entry e state η := by
  rw [Env.value_ext ρ η h]

/-- The same value equality preserves the complete statement outcome, including
the world and its access trace, rather than only its returned scalar. -/
theorem execStmt_env_values {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (s : Stmt D V l Γ Λ Λ') (state : World D) (ρ η : Env D Γ)
    (h : ∀ {τ : Ty} (x : Var Γ τ), ρ.get x = η.get x) :
    execStmt O passes R s state ρ = execStmt O passes R s state η := by
  rw [Env.value_ext ρ η h]

/-- Assignment copies the source binding's value; no aggregate storage identity
or source invalidation is part of the G step. -/
theorem execStmt_copy {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} {τ : Ty} (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (x y : Var Γ τ) (state : World D) (ρ : Env D Γ) :
    execStmt O passes R (Stmt.assignVar (V := V) (l := l) (Λ := Λ) x (.var y)) state ρ =
      .ok (state.lese Λ []) (ρ.set x (ρ.get y)) := rfl

/-- Array replacement is evaluated from the old environment before its target
binding is replaced, just like the existing `execStmt_assignField` for records. -/
theorem execStmt_assignArray {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} {τ : Ty} {n : Nat} (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (x : Var Γ (.arr τ n)) (i : Expr D Γ Λ (.index n)) (e : Expr D Γ Λ τ)
    (state : World D) (ρ : Env D Γ) :
    execStmt O passes R (Stmt.assignVar (V := V) (l := l) x (.arrSet (.var x) i e)) state ρ =
      let readState := state.lese Λ (i.orte ++ e.orte)
      .ok readState (ρ.set x (arrSetW (ρ.get x)
        (eval readState i readState ρ).fin (eval readState e readState ρ))) := by
  simp only [execStmt, Expr.orte, List.nil_append, eval]

/-- Array get-after-set is a law of the actual G expression evaluator. -/
theorem eval_arrGet_arrSet {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} {n : Nat}
    (entry state : World D) (ρ : Env D Γ) (a : Expr D Γ Λ (.arr τ n))
    (i : Expr D Γ Λ (.index n)) (e : Expr D Γ Λ τ) :
    eval entry (.arrGet (.arrSet a i e) i) state ρ = eval entry e state ρ := by
  simp only [eval]
  exact arrSetW_same _ _ _

/-- Array frame at expression evaluation; indices are compared as positions. -/
theorem eval_arrGet_arrSet_other {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} {n : Nat}
    (entry state : World D) (ρ : Env D Γ) (a : Expr D Γ Λ (.arr τ n))
    (i j : Expr D Γ Λ (.index n)) (e : Expr D Γ Λ τ)
    (h : (eval entry j state ρ).fin ≠ (eval entry i state ρ).fin) :
    eval entry (.arrGet (.arrSet a i e) j) state ρ = eval entry (.arrGet a j) state ρ := by
  simp only [eval]
  exact arrSetW_other _ _ _ _ h

/-- The existing prefix operation can be read from its retained source value.
This states byte equality only; allocation, lifetime, trace and cost correctness
of a physical zero-copy representation remain compiler obligations. -/
theorem eval_strGet_strWeit {Γ : Ctx} {Λ : List (Res D)} {n m : Nat} {lo hi : Int}
    (entry state : World D) (ρ : Env D Γ) (s : Expr D Γ Λ (.str n))
    (i : Expr D Γ Λ (.int lo hi)) (h : (eval entry i state ρ).n.toNat < m) :
    eval entry (.strGet (.strWeit m s) i) state ρ = eval entry (.strGet s i) state ρ := by
  simp only [eval]
  exact strGetW_strWeitW m _ _ h

/-- A successful ordinary call keeps the caller's value bindings, irrespective
of assignments made in the callee. Only its returned world is installed. -/
theorem execStmt_call_preserves_caller {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (f : D.Fn) (args : Args D Γ Λ (D.params f))
    (hp : RufPasst D V (D.signatur f) Λ) (hr : D.gruende f = 0)
    (state resultState : World D) (ρ : Env D Γ) (result : ErgVal D (D.erg f))
    (h : R f (state.lese Λ args.orte)
      (evalArgs (state.lese Λ args.orte) args (state.lese Λ args.orte) ρ) =
      .ok resultState result) :
    execStmt O passes R (Stmt.call (V := V) (l := l) f args hp hr) state ρ =
      .ok resultState ρ := by
  simp only [execStmt, h]

end Gabbro.Grammatik
