module
public import Grammatik.Bausteine.Arena.Ownership.Body.Check.Program
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuhe
@[expose] public section


/-! **The ownership checks across the idle root.** The goal statement runs the
program `P.mitRuhe`: the same syntax with the idle root added, types shifted
only at function pointers (`tyR`), every expression translated constructor
by constructor (`ruE`). An arena of `D` is an arena of `D.mitRuhe` (`liftA`),
and every check of the ownership judgment gives the same answer on the
translated syntax as on the original. -/

namespace Gabbro.Grammatik.ArenaOwnership.Ruhe

open Source Body

variable {D : Deklaration}

/-- **An arena of `D` as an arena of `D.mitRuhe`**: the same table, words and link. -/
def liftA (A : FreiForm D) : FreiForm D.mitRuhe where
  tab := A.tab
  feld := A.feld
  zaehl := A.zaehl
  hz := by show tyR (D.gtyp A.zaehl) = _; exact congrArg tyR A.hz
  hpos := A.hpos
  komm := A.komm
  hk := by show tyR (D.gtyp A.komm) = _; exact congrArg tyR A.hk
  hzwei := A.hzwei
  kopf := A.kopf
  hkopf := by show tyR (D.gtyp A.kopf) = _; exact congrArg tyR A.hkopf
  nxt := A.nxt
  hnxt := by show tyR (D.typ A.tab A.nxt) = _; exact congrArg tyR A.hnxt
  hk1 := A.hk1
  hk2 := A.hk2
  hf := A.hf

theorem varR_unten : ∀ {Γ : Ctx} {τ : Ty} (x : Var Γ τ), (varR x).unten = x.unten
  | _ :: Γ, _, .here => by simp only [varR, Var.unten, List.length_map]
  | _ :: _, _, .there x => by simp only [varR, Var.unten]; exact varR_unten x

theorem reference_varR (c : Context) {Γ : Ctx} {τ : Ty} (x : Var Γ τ) : c.reference (varR x) = c.reference x := by
  simp only [Context.reference, varR_unten]

section Expr

variable {Γ : Ctx} {Λ : List (Res D)}

theorem origin_ruE (c : Context) {τ : Ty} (e : Expr D Γ Λ τ) : origin c (ruE e) = origin c e := by
  induction e using Expr.rec (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True) with
  | var x => simp only [origin, expressionOrigin, ruE, varR_unten]
  | widen h0 h1 e ih => exact ih
  | empty => trivial
  | val => trivial
  | nil => trivial
  | cons => trivial
  | _ => rfl

theorem exprGlob_ruE {τ : Ty} (e : Expr D Γ Λ τ) : exprGlob (ruE e) = exprGlob e := by
  cases e <;> rfl

theorem exprVarPos_ruE {τ : Ty} (e : Expr D Γ Λ τ) : exprVarPos (ruE e) = exprVarPos e := by
  induction e using Expr.rec (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True) with
  | var x => simp only [exprVarPos, ruE, varR_unten]
  | widen h0 h1 e ih => exact ih
  | empty => trivial
  | val => trivial
  | nil => trivial
  | cons => trivial
  | _ => rfl

theorem exprLit_ruE {τ : Ty} (e : Expr D Γ Λ τ) : exprLit (ruE e) = exprLit e := by
  cases e <;> rfl

theorem exprSucc_ruE {τ : Ty} (e : Expr D Γ Λ τ) : exprSucc (ruE e) = exprSucc e := by
  induction e using Expr.rec (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True) with
  | add a b iha ihb =>
    show (if exprLit (ruE b) = some 1 then exprVarPos (ruE a) else none) =
      (if exprLit b = some 1 then exprVarPos a else none)
    rw [exprLit_ruE b, exprVarPos_ruE a]
  | widen h0 h1 e ih => exact ih
  | empty => trivial
  | val => trivial
  | nil => trivial
  | cons => trivial
  | _ => rfl

theorem exprSlotRead_ruE {τ : Ty} (e : Expr D Γ Λ τ) : exprSlotRead (ruE e) = exprSlotRead e := by
  cases e <;> first | rfl | (simp only [exprSlotRead, ruE]; exact congrArg _ (exprVarPos_ruE _))

end Expr

section Check

variable {Γ : Ctx} {Λ : List (Res D)} (A : FreiForm D) (c : Context)

theorem payloadRequirements_cast {D' : Deklaration} {Γ' : Ctx} {Λ' : List (Res D')}
    {c₁ c₂ : Option Ty} (h : c₁ = c₂) (n : NutzlastExpr D' Γ' Λ' c₁) :
    payloadRequirements (h ▸ n) = payloadRequirements n := by
  subst h; rfl

theorem requirementsArgs_cast {D' : Deklaration} {Γ' : Ctx} {Λ' : List (Res D')}
    {τs₁ τs₂ : List Ty} (h : τs₁ = τs₂) (a : Args D' Γ' Λ' τs₁) :
    requirementsArgs (h ▸ a) = requirementsArgs a := by
  subst h; rfl

theorem and_congr' {a b a' b' : Bool} (h1 : a = a') (h2 : b = b') : (a && b) = (a' && b') := by
  rw [h1, h2]

theorem access_ruE (t : D.Tab) (i : Expr D Γ Λ (.index (D.count t))) :
    Requirement.check (liftA A) c (.access t (ruE i)) = Requirement.check A c (.access t i) := by
  simp only [Requirement.check, liftA, accessCheck]
  erw [origin_ruE c i]
  by_cases h : t = A.tab <;> simp [h]

theorem requirements_ruE {τ : Ty} (e : Expr D Γ Λ τ) :
    (requirements (ruE e)).all (Requirement.check (liftA A) c) = (requirements e).all (Requirement.check A c) := by
  induction e using Expr.rec
    (motive_2 := fun _ _ _ n => (payloadRequirements (ruN n)).all (Requirement.check (liftA A) c) =
      (payloadRequirements n).all (Requirement.check A c))
    (motive_3 := fun _ _ _ a => (requirementsArgs (ruA a)).all (Requirement.check (liftA A) c) =
      (requirementsArgs a).all (Requirement.check A c)) with
  | var x => simp only [ruE, requirements, List.all_cons, Requirement.check, reference_varR, List.all_nil, Bool.and_true]
  | slot t f i hL ih =>
    simp only [requirements, ruE, List.all_cons]
    exact and_congr' (access_ruE A c t i) ih
  | thru p t ht f i hL ihp ihi =>
    simp only [requirements, ruE, List.all_cons, List.all_append]
    exact and_congr' (access_ruE A c t i) (and_congr' ihp ihi)
  | thruOwn p t ht f i m s ho he hg hL ihp ihi =>
    simp only [requirements, ruE, List.all_cons, List.all_append]
    exact and_congr' (access_ruE A c t i) (and_congr' ihp ihi)
  | oldS t f i hL ih =>
    simp only [requirements, ruE, List.all_cons]
    exact and_congr' rfl ih
  | getBytes t f hf n i hlo hhi hL ih =>
    simp only [requirements, ruE, List.all_cons]
    exact and_congr' rfl ih
  | slotRef r t ht ho f hL ih =>
    simp only [requirements, ruE, List.all_cons]
    exact and_congr' rfl ih
  | case cs i nutz ih =>
    simp only [requirements, ruE, payloadRequirements_cast]
    exact ih
  | prod r args ih =>
    simp only [requirements, ruE, requirementsArgs_cast]
    exact ih
  | empty => rfl
  | val e ih => exact ih
  | nil => rfl
  | cons e rest ihe ihr =>
    simp only [ruA, requirementsArgs, List.all_append]
    exact and_congr' ihe ihr
  | _ =>
    first
      | rfl
      | (simp only [requirements, ruE, List.all_append]
         repeat' first | done | assumption | congr 1)

theorem checkExpression_ruE {τ : Ty} (e : Expr D Γ Λ τ) :
    checkExpression (liftA A) c (ruE e) = checkExpression A c e :=
  requirements_ruE A c e

theorem checkArguments_ruA : ∀ {params : Ctx} (args : Args D Γ Λ params),
    checkArguments (liftA A) c (ruA args) = checkArguments A c args
  | _, .nil => rfl
  | _, .cons e rest => by simp only [ruA, checkArguments, checkExpression_ruE, checkArguments_ruA rest]

theorem originList_ruA : ∀ {params : Ctx} (args : Args D Γ Λ params),
    originList c (ruA args) = originList c args
  | _, .nil => rfl
  | _, .cons e rest => by simp only [ruA, originList, origin_ruE, originList_ruA rest]

theorem consume_ruE {τ : Ty} (e : Expr D Γ Λ τ) : consume c (ruE e) = consume c e := by
  simp only [consume, origin_ruE]

theorem storeCheck_ruE (t : D.Tab) {lo hi : Int} (i : Expr D Γ Λ (.int lo hi)) :
    storeCheck (liftA A) c t (ruE i) = storeCheck A c t i := by
  simp only [storeCheck, liftA, accessCheck]
  erw [origin_ruE c i]
  by_cases h : t = A.tab <;> simp [h]

theorem notLink_lift {t : D.Tab} {f : D.Feld t} : NotLink (liftA A) t f ↔ NotLink A t f := Iff.rfl

theorem notMetaGlob_lift {g : D.Glob} : NotMetaGlob (liftA A) g ↔ NotMetaGlob A g := Iff.rfl

theorem axiomFree_lift {a : D.Ax} : AxiomFree (liftA A) a ↔ AxiomFree A a := Iff.rfl

/-- The result kind of a function, across the idle root. -/
def outR {erg : Option Ty} : Flow.Output A erg → Flow.Output (liftA A) (erg.map tyR)
  | .plain => .plain
  | .owner => .owner

theorem isOwner_outR {erg : Option Ty} (out : Flow.Output A erg) :
    Flow.Output.isOwner (outR A out) = Flow.Output.isOwner out := by
  cases out <;> rfl

theorem checkErg_ruErg {e : Option Ty} (x : ErgExpr D Γ Λ e) :
    Flow.checkErg (liftA A) c (ruErg x) = Flow.checkErg A c x := by
  cases x with
  | empty => rfl
  | val e => exact checkExpression_ruE A c e

theorem check_outR {erg : Option Ty} (out : Flow.Output A erg) (x : ErgExpr D Γ Λ erg) :
    (outR A out).check (liftA A) c (ruErg x) = out.check A c x := by
  cases out with
  | plain => simp only [outR, Flow.Output.check, checkErg_ruErg]
  | owner =>
    cases x with
    | val e =>
      show (checkExpression (liftA A) c (ruE e) && match origin c (ruE e) with
        | none => false
        | some i => decide (c.rights i = some .owned) && finish c (some i)) = _
      simp only [checkExpression_ruE, origin_ruE]
      rfl

end Check

end Gabbro.Grammatik.ArenaOwnership.Ruhe
