module

public import Grammatik.Kern.Syntax.Konst.Programm
public import Grammatik.Kern.Syntax.Konst.Rang
public import Grammatik.Kern.Semantik.Semantik

@[expose] public section

namespace Gabbro.Grammatik

/-! ## Canonical world, oracle, work bound and checked call evaluation.

  Stage 4 of the C17 const-block design: `ConstCallResult` distinguishes
  value, contract violation, arithmetic/range failure, unresolved dependency
  and resource exhaustion. `evalConstCall` checks the structural work bound
  against the compiler limit BEFORE evaluation and then reduces existing
  canonical G semantics (`rufAt` over `execEnd`): no new interpreter, no
  Stage-0 evaluator. A successful evaluation carries its `ConstCallCertificate`
  with the canonical evaluation equation, proved by the match refinement. -/

/-- The canonical world of a closed const program: no globals exist, no
    fielded table exists, the trace starts empty. -/
@[expose] def constWelt (c : ConstProgram) : World c.D := { slots := fun t _ fld => (c.noFields t fld).elim, globs := fun g => (c.noGlobals g).elim, spur := [] }

/-- The canonical oracle of a closed const program: no axiom, register or
    shared global exists, so every answer channel is vacuous. -/
@[expose] def constOrakel (c : ConstProgram) : Orakel c.D := { wirkt := fun a _ _ => ((c.noOracles a).elim, 0), regLies := fun r _ => (c.noRegisters r).elim, regSchreib := fun r _ => (c.noRegisters r).elim, sichtbar := fun g _ => (c.noGlobals g).elim }

/-! ### Structural work bound.

  A conservative node count over canonical G terms, including predicate and
  nested-call positions. Admitted constructors recurse, every other form
  contributes one node: the bound only has to be checked, never to be tight. -/

mutual
def constExprAufwand (c : ConstProgram) {Γ : Ctx} {Λ : List (Res c.D)} {τ : Ty} : Expr c.D Γ Λ τ → Nat
  | .lit _ => 1
  | .tru => 1
  | .fls => 1
  | .var _ => 1
  | .widen _ _ e => 1 + constExprAufwand c e
  | .add a b => 1 + constExprAufwand c a + constExprAufwand c b
  | .sub a b => 1 + constExprAufwand c a + constExprAufwand c b
  | .neg a => 1 + constExprAufwand c a
  | .mul a b => 1 + constExprAufwand c a + constExprAufwand c b
  | .div _ _ a b => 1 + constExprAufwand c a + constExprAufwand c b
  | .rem _ _ a b => 1 + constExprAufwand c a + constExprAufwand c b
  | .sdiv _ a b => 1 + constExprAufwand c a + constExprAufwand c b
  | .srem _ a b => 1 + constExprAufwand c a + constExprAufwand c b
  | .band _ _ a b => 1 + constExprAufwand c a + constExprAufwand c b
  | .bor _ _ _ _ _ a b => 1 + constExprAufwand c a + constExprAufwand c b
  | .bxor _ _ _ _ _ a b => 1 + constExprAufwand c a + constExprAufwand c b
  | .shl _ _ _ _ _ a b => 1 + constExprAufwand c a + constExprAufwand c b
  | .shr _ _ _ _ _ a b => 1 + constExprAufwand c a + constExprAufwand c b
  | .lt a b => 1 + constExprAufwand c a + constExprAufwand c b
  | .le a b => 1 + constExprAufwand c a + constExprAufwand c b
  | .eq a b => 1 + constExprAufwand c a + constExprAufwand c b
  | .and a b => 1 + constExprAufwand c a + constExprAufwand c b
  | .or a b => 1 + constExprAufwand c a + constExprAufwand c b
  | .not a => 1 + constExprAufwand c a
  | .none _ => 1
  | .some e => 1 + constExprAufwand c e
  | .istSome e => 1 + constExprAufwand c e
  | .case _ _ payload => 1 + constPayloadAufwand c payload
  | .why _ _ => 1
  | .forallSlots _ body _ => 1 + constExprAufwand c body
  | .existsSlots _ body _ => 1 + constExprAufwand c body
  | .arrNil => 1
  | .arrCons a rest => 1 + constExprAufwand c a + constExprAufwand c rest
  | .arrGet a i => 1 + constExprAufwand c a + constExprAufwand c i
  | .arrSet a i v => 1 + constExprAufwand c a + constExprAufwand c i + constExprAufwand c v
  | .strLit _ _ => 1
  | .strLen s => 1 + constExprAufwand c s
  | .strCat s t => 1 + constExprAufwand c s + constExprAufwand c t
  | .strGet s i => 1 + constExprAufwand c s + constExprAufwand c i
  | .strEq s t => 1 + constExprAufwand c s + constExprAufwand c t
  | .strLt s t => 1 + constExprAufwand c s + constExprAufwand c t
  | .strWeit _ s => 1 + constExprAufwand c s
  | .wenn condition a b => 1 + constExprAufwand c condition + constExprAufwand c a + constExprAufwand c b
  | .eng e _ _ fallback => 1 + constExprAufwand c e + constExprAufwand c fallback
  | .intBuiltin1 _ a => 1 + constExprAufwand c a
  | .intBuiltin2 _ a b => 1 + constExprAufwand c a + constExprAufwand c b
  | .count _ body => 1 + constExprAufwand c body
  | .prod _ args => 1 + constArgsAufwand c args
  | .prodGet v _ => 1 + constExprAufwand c v
  | .prodSet v _ e => 1 + constExprAufwand c v + constExprAufwand c e
  | _ => 1
def constPayloadAufwand (c : ConstProgram) {Γ : Ctx} {Λ : List (Res c.D)} {k : Option Ty} : NutzlastExpr c.D Γ Λ k → Nat
  | .empty => 1
  | .val e => 1 + constExprAufwand c e
def constArgsAufwand (c : ConstProgram) {Γ : Ctx} {Λ : List (Res c.D)} {ts : List Ty} : Args c.D Γ Λ ts → Nat
  | .nil => 1
  | .cons e rest => 1 + constExprAufwand c e + constArgsAufwand c rest
def constErgAufwand (c : ConstProgram) {Γ : Ctx} {Λ : List (Res c.D)} {τ : Option Ty} : ErgExpr c.D Γ Λ τ → Nat
  | .empty => 1
  | .val e => 1 + constExprAufwand c e
def constStmtAufwand (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {Λ Λout : List (Res c.D)} : Stmt c.D V l Γ Λ Λout → Nat
  | .assignVar _ e => 1 + constExprAufwand c e
  | .ite condition yes no => 1 + constExprAufwand c condition + constBlockAufwand c yes + constBlockAufwand c no
  | .onOption value present absent => 1 + constExprAufwand c value + constBlockAufwand c present + constBlockAufwand c absent
  | .onTag value arms => 1 + constExprAufwand c value + constArmsAufwand c arms
  | .onWhy reason arms => 1 + constExprAufwand c reason + constReasonAufwand c arms
  | .ret value _ => 1 + constErgAufwand c value
  | .call _ args _ _ => 2 + constArgsAufwand c args
  | _ => 1
def constBlockAufwand (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {Λ Λout : List (Res c.D)} : Block c.D V l Γ Λ Λout → Nat
  | .nil => 1
  | .cons stmt rest => 1 + constStmtAufwand c stmt + constBlockAufwand c rest
  | .bind value rest => 1 + constExprAufwand c value + constBlockAufwand c rest
  | .bindCall _ args _ _ _ rest => 2 + constArgsAufwand c args + constBlockAufwand c rest
  | _ => 1
def constEndAufwand (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {Λ : List (Res c.D)} : Endblock c.D V l Γ Λ → Nat
  | .ret value _ => 1 + constErgAufwand c value
  | .cons stmt rest => 1 + constStmtAufwand c stmt + constEndAufwand c rest
  | .bind value rest => 1 + constExprAufwand c value + constEndAufwand c rest
  | .ite condition yes no => 1 + constExprAufwand c condition + constEndAufwand c yes + constEndAufwand c no
  | .bindCall _ args _ _ _ rest => 2 + constArgsAufwand c args + constEndAufwand c rest
  | _ => 1
def constArmsAufwand (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {Λ Λout : List (Res c.D)} {cs : List (Option Ty)} : Arms c.D V l Γ Λ Λout cs → Nat
  | .nil => 1
  | .cons body rest => 1 + constBlockAufwand c body + constArmsAufwand c rest
def constReasonAufwand (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {Λ Λout : List (Res c.D)} {n : Nat} : GrundArms c.D V l Γ Λ Λout n → Nat
  | .nil => 1
  | .cons body rest => 1 + constBlockAufwand c body + constReasonAufwand c rest
end

/-- The checked work bound of one const call: body size plus a per-callee
    step. Exceeding the compiler limit refuses compilation, never supplies
    a value; it is independent of source `costs`. -/
@[expose] def constArbeitsSchranke (c : ConstProgram) (f : c.D.Fn) : Nat :=
  constEndAufwand c (c.P.rumpf f) + (constCallees c f).length * 8 + 8

/-- The fuel of one checked call: one level per declared function plus one.
    `rufAt` always terminates at finite fuel; too little fuel answers
    `abstieg`, which the evaluator reports as resource exhaustion. -/
@[expose] def constTiefenSchranke (c : ConstProgram) : Nat := c.functions.length + 1

/-! ### Certificate and result. -/

/-- A checked const call: source function identity, typed closed arguments,
    exact clauses/body derivation is carried by the caller (`ConstElaborates`),
    while this records the value, the bounds, the canonical equation and the
    successful predicate checks behind that equation. -/
@[expose] structure ConstCallCertificate (c : ConstProgram) (f : c.D.Fn) (args : Env c.D (c.D.params f)) where
  value : ErgVal c.D (c.D.erg f)
  bound : Nat
  world : World c.D
  source : Nat
  equation : rufAt c.P (constOrakel c) 0 bound f (constWelt c) args = RufAusgang.ok world value

/-- The five outcomes of a checked const call: a certified value, a contract
    violation naming the guilty function, an arithmetic/range failure, an
    unresolved dependency, or resource exhaustion with used and allowed work. -/
@[expose] inductive ConstCallResult (c : ConstProgram) (f : c.D.Fn) (args : Env c.D (c.D.params f)) where
  | value (cert : ConstCallCertificate c f args) : ConstCallResult c f args
  | contract (guilty : c.D.Fn) : ConstCallResult c f args
  | range (guilty : c.D.Fn) : ConstCallResult c f args
  | dependency (guilty : c.D.Fn) : ConstCallResult c f args
  | exhausted (used allowed : Nat) : ConstCallResult c f args

/-- Boolean projectors for kernel witnesses over evaluation outcomes. -/
@[expose] def ConstCallResult.istWert : ConstCallResult c f args → Bool
  | .value _ => true
  | _ => false

@[expose] def ConstCallResult.istVertrag : ConstCallResult c f args → Bool
  | .contract _ => true
  | _ => false

@[expose] def ConstCallResult.istBereich : ConstCallResult c f args → Bool
  | .range _ => true
  | _ => false

@[expose] def ConstCallResult.istAbhaengigkeit : ConstCallResult c f args → Bool
  | .dependency _ => true
  | _ => false

@[expose] def ConstCallResult.istErschoepfung : ConstCallResult c f args → Bool
  | .exhausted _ _ => true
  | _ => false

/-- Checked const-call evaluation: the work bound is checked against the
    limit BEFORE any reduction; then the canonical call runs at the canonical
    world and oracle. `.ok` projects to a certified value; a failed
    requires/ensures maps to a contract violation, exhausted fuel to resource
    exhaustion, residual logic failures to range failure, and hardware or
    reason-channel outcomes (impossible in the admitted fragment) to an
    unresolved dependency. No saturation, wrapping, clipping or default. -/
@[expose] def evalConstCall (c : ConstProgram) (f : c.D.Fn) (args : Env c.D (c.D.params f)) (limit : Nat) : ConstCallResult c f args :=
  let aufwand := constArbeitsSchranke c f
  if aufwand ≤ limit then
    match h : rufAt c.P (constOrakel c) 0 (constTiefenSchranke c) f (constWelt c) args with
    | .ok welt wert => .value ⟨wert, constTiefenSchranke c, welt, c.sourceId f, h⟩
    | .logik (.vorbedingung schuld) => .contract schuld
    | .logik (.nachbedingung schuld) => .contract schuld
    | .logik (.abstieg _) => .exhausted aufwand limit
    | .logik _ => .range f
    | .hardware _ => .dependency f
    | .why _ _ => .dependency f
  else .exhausted aufwand limit

end Gabbro.Grammatik
