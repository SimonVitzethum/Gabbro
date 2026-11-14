module

public import Grammatik.Niedrig.Konstrukte.SichtScope
public import Grammatik.Kern.Syntax.Satz.T4.Teil1

@[expose] public section

namespace Gabbro.Grammatik.LowLevel.Construct

variable {D : Deklaration}

/-- Hardware-only until A1 introduces the environment origin. An unresolved
    item or hardware item without its named evidence is refused. Existing
    RufPasst, answer admissibility and write guards remain additional premises. -/
def CtxOriginOk (item : D.Ax) : Prop :=
  D.axHerkunft item = some .hardware ∧ (D.axBeleg item).isSome = true

instance (item : D.Ax) : Decidable (CtxOriginOk item) := by
  unfold CtxOriginOk
  infer_instance

def ctxOriginB (item : D.Ax) : Bool := decide (CtxOriginOk item)

theorem ctxOriginB_iff (item : D.Ax) :
    ctxOriginB item = true ↔ CtxOriginOk item := by
  simp only [ctxOriginB, decide_eq_true_eq]

theorem ctxOrigin_evidence {item : D.Ax} (checked : CtxOriginOk item) :
    D.axHerkunft item = some .hardware ∧ ∃ named, D.axBeleg item = some named := by
  cases evidence : D.axBeleg item with
  | none =>
    have present := checked.2
    rw [evidence] at present
    cases present
  | some named => exact ⟨checked.1, named, rfl⟩

/-- Static linear data, without pretending to identify a source inventory with
    an arbitrary ghost context. G8 discharges that dynamic linkage. -/
def CtxMoveOk (mark : D.Marke) (stage : Nat) (before after : OwnerBindings D.Marke)
    (source into : Nat) : Prop :=
  ({ binder := source
     mark := mark
     stage := stage } : OwnerBinding D.Marke) ∈ before ∧
  OwnerBindings.move before source into = some after

instance (mark : D.Marke) (stage : Nat) (before after : OwnerBindings D.Marke) (source into : Nat) :
    Decidable (CtxMoveOk mark stage before after source into) := by
  unfold CtxMoveOk
  infer_instance

def ctxMoveB (mark : D.Marke) (stage : Nat) (before after : OwnerBindings D.Marke)
    (source into : Nat) : Bool := decide (CtxMoveOk mark stage before after source into)

theorem ctxMoveB_iff (mark : D.Marke) (stage : Nat) (before after : OwnerBindings D.Marke)
    (source into : Nat) :
    ctxMoveB mark stage before after source into = true ↔ CtxMoveOk mark stage before after source into := by
  simp only [ctxMoveB, decide_eq_true_eq]

def BindCtxOk (item : D.Ax) (mark : D.Marke) (stage : Nat) (before after : OwnerBindings D.Marke)
    (source into : Nat) : Prop := CtxOriginOk item ∧ CtxMoveOk mark stage before after source into

instance (item : D.Ax) (mark : D.Marke) (stage : Nat) (before after : OwnerBindings D.Marke)
    (source into : Nat) : Decidable (BindCtxOk item mark stage before after source into) := by
  unfold BindCtxOk
  infer_instance

def bindCtxB (item : D.Ax) (mark : D.Marke) (stage : Nat) (before after : OwnerBindings D.Marke)
    (source into : Nat) : Bool := decide (BindCtxOk item mark stage before after source into)

theorem bindCtxB_iff (item : D.Ax) (mark : D.Marke) (stage : Nat) (before after : OwnerBindings D.Marke)
    (source into : Nat) :
    bindCtxB item mark stage before after source into = true ↔ BindCtxOk item mark stage before after source into := by
  simp only [bindCtxB, decide_eq_true_eq]

/-- Existing argument evaluation/read tracing and existing fallible foreign
    decoding. The outer Option refuses an invalid linear move before invoking
    the item. The inner Option remains G's hardware-stop answer classification.
    The returned inventory is retained on BOTH value and reason answers. -/
def bindCtxStep {Γ : Ctx} {resources : List (Res D)}
    (oracle : Orakel D) (item : D.Ax) (mark : D.Marke) (stage : Nat)
    (args : Args D Γ resources (D.aparams item)) (env : Env D Γ)
    (before after : OwnerBindings D.Marke) (source into : Nat)
    (_checked : BindCtxOk item mark stage before after source into) (world : World D) :
    Option (OwnerBindings D.Marke × World D × Option (ErgVal D (D.aerg item) ⊕ Fin (D.agruende item))) :=
  match OwnerBindings.move before source into with
  | none => none
  | some moved =>
    let readWorld := world.lese resources args.orte
    some (moved, axiomAntwortSonst oracle item readWorld (evalArgs readWorld args readWorld env))

theorem bindCtxStep_eq {Γ : Ctx} {resources : List (Res D)}
    (oracle : Orakel D) (item : D.Ax) (mark : D.Marke) (stage : Nat)
    (args : Args D Γ resources (D.aparams item)) (env : Env D Γ)
    (before after : OwnerBindings D.Marke) (source into : Nat)
    (checked : BindCtxOk item mark stage before after source into) (world : World D) :
    bindCtxStep oracle item mark stage args env before after source into checked world =
      some (after, axiomAntwortSonst oracle item (world.lese resources args.orte)
        (evalArgs (world.lese resources args.orte) args (world.lese resources args.orte) env)) := by
  simp only [bindCtxStep, checked.2.2]

theorem bindCtxStep_linear (item : D.Ax) (mark : D.Marke) (stage : Nat)
    (before after : OwnerBindings D.Marke) (source into : Nat)
    (checked : BindCtxOk item mark stage before after source into) :
    OwnerBindings.Valid after ∧
    List.Perm (OwnerBindings.resources (D := D) before) (OwnerBindings.resources (D := D) after) :=
  ⟨OwnerBindings.move_valid checked.2.2, OwnerBindings.move_resource_perm checked.2.2⟩

theorem bindCtxStep_resource (item : D.Ax) (mark : D.Marke) (stage : Nat)
    (before after : OwnerBindings D.Marke) (source into : Nat)
    (checked : BindCtxOk item mark stage before after source into) :
    Res.marke mark stage ∈ OwnerBindings.resources (D := D) after :=
  (OwnerBindings.move_resource_perm (D := D) checked.2.2).mem_iff.mp
    (List.mem_map.mpr
      ⟨({ binder := source
          mark := mark
          stage := stage } : OwnerBinding D.Marke), checked.2.1, rfl⟩)

/-- Supply the source half of LinearContextStep once the induction has the
    actual AuthorityStep. This never invents a protocol step from source data. -/
def bindCtxLinear {P I : Type} {a : Authority D} {c next : Context D P I}
    {result : Option (View D)} (step : AuthorityStep a c result next)
    (before after : OwnerBindings D.Marke) (source into : Nat)
    (checked : CtxMoveOk a.token.mark a.token.stage before after source into) : LinearContextStep a c result next :=
  { protocol := step
    before := before
    after := after
    source := source
    into := into
    bound := checked.1
    moved := checked.2 }

/-- The canonical G frame/trace argument, reused before result dispatch.
    In particular a reason answer receives the very same frame guarantee. -/
theorem bindCtxCall_gut {Γ : Ctx} {resources : List (Res D)}
    (oracle : Orakel D) (good : GutO oracle) (item : D.Ax)
    (args : Args D Γ resources (D.aparams item)) (env : Env D Γ) (world : World D)
    (writes : D.Tab → Bool) (globals : D.Glob → Bool)
    (effect : ∀ table, D.aschreibt item table = true → writes table = true)
    (globalEffect : ∀ global, D.agschreibt item global = true → globals global = true)
    (allowed : ∀ table, D.aschreibt item table = true → darf D table resources)
    (globalAllowed : ∀ global, D.agschreibt item global = true → gdarf D global resources)
    (held : HeldIn resources world.haelt) :
    Gut writes globals world
      (axiomAntwortSonst oracle item (world.lese resources args.orte)
        (evalArgs (world.lese resources args.orte) args (world.lese resources args.orte) env)).1 := by
  have reads := gut_lese (W := writes) (G := globals) world resources _ args.orte_darf held
  have call := axiomAntwort_gut oracle good item (world.lese resources args.orte)
    (evalArgs (world.lese resources args.orte) args (world.lese resources args.orte) env)
    allowed globalAllowed (reads.heldIn held)
  rw [← axiomAntwortSonst_fst] at call
  exact reads.trans (Gut.weiter effect globalEffect call)

/-- Callee effects are the ordinary signature predicates, represented as sets
    rather than silently enumerating possibly infinite carrier types. -/
def CtxReads (arguments : List (D.Tab ⊕ D.Glob)) (place : D.Tab ⊕ D.Glob) : Prop :=
  place ∈ arguments

def CtxWrites (item : D.Ax) : D.Tab ⊕ D.Glob → Prop
  | .inl table => D.aschreibt item table = true
  | .inr global => D.agschreibt item global = true

/-- Exact bindAxiomOptElse analogues in Block and Endblock position. -/
def bindCtxCost (args err rest : Nat) : Nat := 4 + args + err + rest

def bindCtxEndCost (args err rest : Nat) : Nat := 1 + args + err + rest

theorem bindCtxCost_bound (args err rest : Nat) :
    args + err + rest + 1 ≤ bindCtxCost args err rest := by unfold bindCtxCost; omega

theorem bindCtxEndCost_bound (args err rest : Nat) :
    args + err + rest + 1 ≤ bindCtxEndCost args err rest := by unfold bindCtxEndCost; omega

end Gabbro.Grammatik.LowLevel.Construct
