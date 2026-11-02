module

public import Grammatik.Bausteine.Walk.Binding

@[expose] public section

namespace Gabbro.Grammatik

/-- The original lexical scope embedded beneath generated index, entry and child binders. -/
abbrev WalkRen (outer inner : Ctx) := ∀ {ty : Ty}, Var outer ty → Var inner ty

/-- Source predicates and a visit body in their actual lexical/resource context. The generated walker
    supplies entry values and the complete root-to-entry path; it never synthesizes an address or owner.
    A source adapter must prove its mapping construction, loop control and invariant obligations before
    enabling a `mappings of` form. This interface alone does not enable source walkers. -/
structure WalkCode {D : Deklaration} {shape : WalkShape} (binding : WalkBinding D shape)
    (V : Vertrag D) (outer : Ctx) (resources : List (Res D)) where
  invariant : ∀ {Γ : Ctx}, WalkRen outer Γ → Nat →
    List (Expr D Γ resources (.index shape.arity)) → Expr D Γ resources .bool
  leaf : ∀ {Γ : Ctx}, WalkRen outer Γ → Expr D Γ resources binding.entryTy → Expr D Γ resources .bool
  descend : ∀ {Γ : Ctx}, WalkRen outer Γ → Expr D Γ resources binding.entryTy → Expr D Γ resources .bool
  visit : ∀ {Γ : Ctx}, WalkRen outer Γ → Nat →
    List (Expr D Γ resources (.index shape.arity)) → Expr D Γ resources binding.entryTy → Block D V true Γ resources resources

/-- The bounded index of one generated level, cast to the walker's index type. -/
def WalkBinding.levelIndex {D : Deklaration} {shape : WalkShape} {V : Vertrag D}
    {outer Γ : Ctx} {resources : List (Res D)} (binding : WalkBinding D shape) :
    Expr D (.index (D.count binding.iterator) :: Γ) resources (.index shape.arity) :=
  cast (congrArg (Expr D (.index (D.count binding.iterator) :: Γ) resources)
    (congrArg Ty.index binding.count)) (Expr.var .here)

/-- The outer scope embedded beneath generated index and entry binders. -/
def WalkBinding.renameEntry {D : Deklaration} {shape : WalkShape} {V : Vertrag D}
    {outer Γ : Ctx} {resources : List (Res D)} (binding : WalkBinding D shape)
    (rename : WalkRen outer Γ) :
    WalkRen outer (binding.entryTy :: .index (D.count binding.iterator) :: Γ) :=
  fun x => .there (.there (rename x))

/-- The complete root-to-entry path at one generated level, in declaration order. -/
def WalkBinding.fullPath {D : Deklaration} {shape : WalkShape} {V : Vertrag D}
    {outer Γ : Ctx} {resources : List (Res D)} (binding : WalkBinding D shape)
    (path : List (Expr D Γ resources (.index shape.arity))) :
    List (Expr D (binding.entryTy :: .index (D.count binding.iterator) :: Γ) resources
      (.index shape.arity)) :=
  path.map (fun value => value.weaken.weaken) ++ [(binding.levelIndex (Γ := Γ)).weaken]

/-- The non-leaf continuation of one generated level: descend conditionally through the checked
    optional child, or stop at the last level. -/
def WalkBinding.otherwise {D : Deklaration} {shape : WalkShape} {V : Vertrag D}
    {outer Γ : Ctx} {resources : List (Res D)} (binding : WalkBinding D shape)
    (code : WalkCode binding V outer resources)
    (rename : WalkRen outer Γ)
    (path : List (Expr D Γ resources (.index shape.arity)))
    (down : Option (∀ {Δ : Ctx}, WalkRen outer Δ →
      Expr D Δ resources (.index (D.count binding.nodes)) →
      List (Expr D Δ resources (.index shape.arity)) → Stmt D V true Δ resources resources)) :
    Block D V true (binding.entryTy :: .index (D.count binding.iterator) :: Γ) resources resources :=
  match down with
  | none => .nil
  | some recurse =>
    .cons (.ite (code.descend (binding.renameEntry rename) (.var .here))
      (.cons (.onOption (.prodGet (.var .here) binding.child)
        (.cons (recurse (fun x => .there (binding.renameEntry rename x)) (.var .here)
          ((binding.fullPath path).map (fun value => value.weaken))) .nil) .nil) .nil) .nil

/-- One generated level: traverse bounded indices, capture the containing entry once, test leaf first,
    then descend conditionally through the checked optional child. A last-level pass has no down branch. -/
def WalkBinding.levelBody {D : Deklaration} {shape : WalkShape} {V : Vertrag D}
    {outer Γ : Ctx} {resources : List (Res D)} (binding : WalkBinding D shape)
    (guard : darf D binding.nodes resources) (code : WalkCode binding V outer resources)
    (level : Nat) (rename : WalkRen outer Γ)
    (node : Expr D Γ resources (.index (D.count binding.nodes)))
    (path : List (Expr D Γ resources (.index shape.arity)))
    (down : Option (∀ {Δ : Ctx}, WalkRen outer Δ →
      Expr D Δ resources (.index (D.count binding.nodes)) →
      List (Expr D Δ resources (.index shape.arity)) → Stmt D V true Δ resources resources)) :
    Block D V true (.index (D.count binding.iterator) :: Γ) resources resources :=
  .bind (binding.readEntry guard node.weaken (binding.levelIndex (Γ := Γ)))
    (.cons (.ite (code.leaf (binding.renameEntry rename) (.var .here))
      (code.visit (binding.renameEntry rename) level
        (binding.fullPath path) (.var .here))
      (binding.otherwise code rename path down)) .nil)

/-- The existing finite-index statement owns the loop and every invariant boundary. -/
def WalkBinding.expandLevel {D : Deklaration} {shape : WalkShape} {V : Vertrag D}
    {outer Γ : Ctx} {resources : List (Res D)} {loop : Bool} (binding : WalkBinding D shape)
    (guard : darf D binding.nodes resources) (code : WalkCode binding V outer resources)
    (level : Nat) (rename : WalkRen outer Γ)
    (node : Expr D Γ resources (.index (D.count binding.nodes)))
    (path : List (Expr D Γ resources (.index shape.arity)))
    (down : Option (∀ {Δ : Ctx}, WalkRen outer Δ →
      Expr D Δ resources (.index (D.count binding.nodes)) →
      List (Expr D Δ resources (.index shape.arity)) → Stmt D V true Δ resources resources)) :
    Stmt D V loop Γ resources resources :=
  .traverse binding.iterator (code.invariant rename level path) (binding.levelBody guard code level rename node path down)

/-- Finite expansion into existing G statements, with one traverse per visited level. -/
def WalkBinding.expand {D : Deklaration} {shape : WalkShape} {V : Vertrag D}
    {outer : Ctx} {resources : List (Res D)} (binding : WalkBinding D shape)
    (guard : darf D binding.nodes resources) (code : WalkCode binding V outer resources) :
    (level : Nat) → {Γ : Ctx} → {loop : Bool} → WalkRen outer Γ →
      Expr D Γ resources (.index (D.count binding.nodes)) →
      List (Expr D Γ resources (.index shape.arity)) → Stmt D V loop Γ resources resources
  | 0, _, _, rename, node, path => binding.expandLevel guard code 0 rename node path none
  | level + 1, _, _, rename, node, path =>
    binding.expandLevel guard code (level + 1) rename node path
      (some (fun {Δ} rename child prefix => binding.expand guard code level rename child prefix))

/-- Capture the root once before entering any generated loop. -/
def WalkBinding.walk {D : Deklaration} {shape : WalkShape} {V : Vertrag D}
    {Γ : Ctx} {resources : List (Res D)} {loop : Bool} (binding : WalkBinding D shape)
    (guard : darf D binding.nodes resources) (code : WalkCode binding V Γ resources)
    (root : Expr D Γ resources (.index (D.count binding.nodes))) : Block D V loop Γ resources resources :=
  .bind root (.cons (binding.expand guard code (shape.levels - 1) (fun x => .there x) (.var .here) []) .nil)

/-- The expansion runs the canonical G traverse semantics, including its invariant checks and outcomes.
    This equation does not replace the outstanding list-of-mappings preservation theorem. -/
theorem WalkBinding.expandLevel_run {D : Deklaration} {shape : WalkShape} {V : Vertrag D}
    {outer Γ : Ctx} {resources : List (Res D)} {loop : Bool} (binding : WalkBinding D shape)
    (guard : darf D binding.nodes resources) (code : WalkCode binding V outer resources)
    (level : Nat) (rename : WalkRen outer Γ)
    (node : Expr D Γ resources (.index (D.count binding.nodes)))
    (path : List (Expr D Γ resources (.index shape.arity)))
    (down : Option (∀ {Δ : Ctx}, WalkRen outer Δ →
      Expr D Δ resources (.index (D.count binding.nodes)) →
      List (Expr D Δ resources (.index shape.arity)) → Stmt D V true Δ resources resources))
    (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (state : World D) (env : Env D Γ) :
    execStmt oracle passes calls (l := loop) (binding.expandLevel guard code level rename node path down) state env =
      traverseLauf (fun state env => execBlock oracle passes calls (binding.levelBody guard code level rename node path down) state env)
        (fun state env => let invariant := code.invariant rename level path
                          let read := state.lese resources invariant.orte
                          (read, wahr? (eval read invariant read env)))
        (alleIndizes (D.count binding.iterator)) state env := by
  rfl

end Gabbro.Grammatik
