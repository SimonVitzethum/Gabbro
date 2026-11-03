module
public import Grammatik.Parser.Elab.UebersetzeAllg3
@[expose] public section

namespace Gabbro.Grammatik.Parser.ExportPreservation
open Uebersetze UebersetzeAllg UebersetzeAllg2

/-- Both operands retain their original predicate context; neither old/result nor a binder is
    invented by implication expansion. Failed operand exports stay failures. -/
theorem implication_export (ctx : UCtx) (p q : SExpr) (a b : UEns)
    (hp : uSichert ctx p = .ok a) (hq : uSichert ctx q = .ok b) :
    uSichert ctx (.ext .imp [] [p, q]) = .ok (.imp a b) := by
  simp only [uSichert, hp, hq]

/-- The same typed expression, including its resource context and result position, reaches G. -/
theorem implication_lower (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (er : Option Ty) (a b : UEns) (p q : Expr (declOf u) Γ Λ .bool)
    (hg : u.exportGate = .ok ())
    (hp : lowEns u Γ Λ fn er a = .ok p) (hq : lowEns u Γ Λ fn er b = .ok q) :
    lowEns u Γ Λ fn er (.imp a b) = .ok (Expr.impl p q) := by
  simp only [lowEns, hg, bind, Except.bind, hp, hq, pure, Except.pure, Expr.impl]

/-- Actual implication emission admits only a checked original-source duty set. -/
theorem implication_gate (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (er : Option Ty) (a b : UEns) (value : Expr (declOf u) Γ Λ .bool)
    (h : lowEns u Γ Λ fn er (.imp a b) = .ok value) : u.exportGate = .ok () := by
  cases hg : u.exportGate with
  | error e => simp only [lowEns, hg, bind, Except.bind] at h; contradiction
  | ok v => cases v; rfl

/-- Evaluation and ordered read footprint coincide with canonical implication. -/
theorem implication_meaning {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (p q : Expr D Γ Λ .bool) (entry state : World D) (env : Env D Γ) :
    eval entry (Expr.impl p q) state env =
      (!wahr? (eval entry p state env) || wahr? (eval entry q state env)) ∧
    (Expr.impl p q).orte = p.orte ++ q.orte := ⟨rfl, rfl⟩

/-- Implication retains the old/result prohibition in executable bodies. -/
theorem implication_scope (a b : UEns) :
    ensAltErg (.imp a b) = (ensAltErg a || ensAltErg b) := by rfl

theorem implication_export_zeuge :
    let ctx : UCtx := {
      names := ["ready"], kinds := [.bool], types := [.bool], tabs := [], locks := [],
      held := [], res := some (0, 42), fname := "sample", alias := [], lits := [] }
    uSichert ctx (.ext .imp [] [.variable "ready", .bin "==" .res (.lit 42)]) =
      .ok (.imp (.var "ready") (.cmp "==" .erg (.lit 42))) ∧
    uBool ctx (.ext .imp [] [.variable "ready", .bin "==" .res (.lit 42)]) =
      .error "result without result" := by exact ⟨rfl, rfl⟩

/-- A successfully reified Held fact is backed by a real resource, never just its spelling. -/
theorem held_lower (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (name : String)
    (value : Expr (declOf u) Γ Λ .bool) (h : lowHeld u Γ Λ name = .ok value) :
    u.exportGate = .ok () ∧
      ∃ lock, lockIdx u.locks name = .ok lock ∧ Res.held lock ∈ Λ ∧ value = .tru := by
  have hg : u.exportGate = .ok () := by
    cases hs : u.exportGate with
    | error e => simp only [lowHeld, hs, bind, Except.bind] at h; contradiction
    | ok v => cases v; rfl
  simp only [lowHeld, hg, bind, Except.bind] at h
  refine ⟨hg, ?_⟩
  cases hi : lockIdx u.locks name with
  | error e => simp only [hi] at h; contradiction
  | ok lock =>
    simp only [hi] at h
    split at h
    · rename_i held
      exact ⟨lock, rfl, held, (Except.ok.inj h).symm⟩
    · contradiction

/-- Under the canonical world/resource invariant, reification states an actual held fact. -/
theorem held_meaning (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (name : String)
    (value : Expr (declOf u) Γ Λ .bool) (h : lowHeld u Γ Λ name = .ok value)
    (entry state : World (declOf u)) (env : Env (declOf u) Γ) (hh : HeldIn Λ state.haelt) :
    ∃ lock, lockIdx u.locks name = .ok lock ∧ lock ∈ state.haelt ∧ eval entry value state env = true := by
  obtain ⟨_, lock, hi, possession, same⟩ := held_lower u Γ Λ name value h
  subst value
  exact ⟨lock, hi, hh lock possession, rfl⟩

def heldUnit : UProg := { tabs := [], fns := [], locks := [{name := "L", rank := 3, guard := []}] }

theorem held_lower_zeuge :
    lowHeld heldUnit [] [.held ⟨0, by decide⟩] "L" = .ok .tru ∧
    lowHeld heldUnit [] [] "L" = .error "Held predicate without possession" := by exact ⟨rfl, rfl⟩

/-- The hidden result parameter keeps the exact type and all original parameter positions. -/
theorem result_scope (u : UProg) (fn : UFn) (ty : Ty) (out : UFn)
    (h : ergAlsParam u fn (some ty) = .ok out) :
    ∃ kind, resultKind fn ty = .ok kind ∧ out.params = ("#erg", ty) :: fn.params ∧
      out.kinds = kind :: fn.kinds ∧ resultContextGate u (some ty) = .ok () := by
  unfold ergAlsParam at h
  cases hk : resultKind fn ty with
  | error e => simp only [hk, bind, Except.bind] at h; contradiction
  | ok kind =>
    simp only [hk, bind, Except.bind] at h
    cases hg : resultContextGate u (some ty) with
    | error e => simp only [hg, bind, Except.bind] at h; contradiction
    | ok v =>
      cases v
      simp only [hg, bind, Except.bind, pure, Except.pure] at h
      cases h
      exact ⟨kind, rfl, rfl, rfl, rfl⟩

theorem result_scope_zeuge :
    let fn : UFn := {
      name := "sample", params := [("flag", .bool)], kinds := [.bool], res := none, resOpt := some (1, 2), held := [], puts := [], gives := [], body := [], ret := .opt .nichts }
    ergAlsParam heldUnit fn (some (.opt 2)) = .ok (fn.mitOpt "#erg" 1 2) ∧
    resultKind fn (.opt 3) = .error "result option count mismatch" := by
  exact ⟨rfl, rfl⟩

/-- The actual Endblock dispatcher passes both scopes and all callee checks to the existing
    constructor. The error body is parsed from the real source tail, with its own reason binder. -/
theorem nested_else_lower {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx)
    (fn : UFn) (fuel : Nat) (Λ : List (Res (declOf u))) (top : AtTop u caller Λ)
    (y callee reason : String) (args : List UArg) (source tail remaining : List UStmt)
    (k : RufKopf u caller Γ Λ) (τ : Ty)
    (hg : u.exportGate = .ok ())
    (hk : lowRufKopf u caller Γ fn Λ callee args = .ok k)
    (hr : 0 < (declOf u).gruende k.callee) (he : (declOf u).erg k.callee = some τ)
    (err : Endblock (declOf u) (verOf u caller) l (Ty.why ((declOf u).gruende k.callee) :: Γ) (nach (declOf u) k.callee Λ))
    (body : Endblock (declOf u) (verOf u caller) l (τ :: Γ) (nach (declOf u) k.callee Λ))
    (herr : lowEndL (l := l) u caller (Ty.why ((declOf u).gruende k.callee) :: Γ)
      (fn.mitWhy reason 0 ((declOf u).gruende k.callee)) fuel (nach (declOf u) k.callee Λ) top source = .ok (err, .blkEnd :: tail))
    (hbody : lowEndL (l := l) u caller (τ :: Γ) (fn.mitTy y τ) fuel (nach (declOf u) k.callee Λ) top tail = .ok (body, remaining)) :
    lowEndL (l := l) u caller Γ fn (fuel + 1) Λ top (.bindElse y callee args reason :: source) =
      .ok (nestedElse u caller Γ Λ k τ he hr err body, remaining) := by
  simp only [lowEndL_succ, lowEndStep, lowStufe_ende, hg, bind, Except.bind, hk, hr, ↓reduceIte, withErg, herr]
  split
  · rename_i hn
    rw [he] at hn
    contradiction
  · rename_i τ' ht
    have same : τ' = τ := Option.some.inj (ht.symm.trans he)
    subst τ'
    simp only [hbody, bind, Except.bind]

/-- Successful dispatch through the new Endblock case has consumed the unit's source duty gate. -/
theorem nested_else_gate {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx)
    (fn : UFn) (n : Nat) (Λ : List (Res (declOf u))) (top : AtTop u caller Λ)
    (y callee reason : String) (args : List UArg) (source : List UStmt)
    (output : Endblock (declOf u) (verOf u caller) l Γ Λ × List UStmt)
    (h : lowEndL (l := l) u caller Γ fn (n + 1) Λ top
      (.bindElse y callee args reason :: source) = .ok output) : u.exportGate = .ok () := by
  cases hg : u.exportGate with
  | error e => simp only [lowEndL_succ, lowEndStep, hg, bind, Except.bind] at h; contradiction
  | ok v => cases v; rfl

/-- Canonical call semantics retained by the exported nested continuation. Both paths use
    the post-call world, and the callee is evaluated exactly once at the original argument footprint. -/
theorem nested_else_meaning {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (callee : D.Fn) (args : Args D Γ Λ (D.params callee)) (τ : Ty)
    (he : D.erg callee = some τ) (hp : RufPasst D V (D.signatur callee) Λ)
    (hr : 0 < D.gruende callee)
    (err : Endblock D V l (Ty.why (D.gruende callee) :: Γ) (nach D callee Λ))
    (body : Endblock D V l (τ :: Γ) (nach D callee Λ)) (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (state : World D) (env : Env D Γ) :
    execEnd O passes R (.bindCallElse callee args he hp hr err body) state env =
      (let readState := state.lese Λ args.orte
       match R callee readState (evalArgs readState args readState env) with
       | .ok next value => (execEnd O passes R body next (.cons (ergWert he value) env)).schrumpf
       | .why next reason => (execEnd O passes R err next (.cons reason env)).schrumpf
       | .logik error => .logik error
       | .hardware error => .hardware error) := by rfl

end Gabbro.Grammatik.Parser.ExportPreservation
