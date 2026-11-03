module
public import Grammatik.Logik.Vertraege.ObjektRahmen.T1
@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}
/-! ## 3. The object discipline of a body -/

/-- A slot store at table `t` with index `i` is admitted: `i` is the index variable of a
    writable object parameter on `t`. -/
def SchreibOk (ps : List (ObjPar D)) (t : D.Tab) {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (i : Expr D Γ Λ τ) : Prop :=
  ∃ x : Var Γ τ, i = .var x ∧ ∃ op ∈ ps, op.rw = true ∧ op.tab = t ∧ op.idx = x.unten

/-- An assignment to `x` overwrites no index variable of a writable object parameter. -/
def VarFrei (ps : List (ObjPar D)) {Γ : Ctx} {τ : Ty} (x : Var Γ τ) : Prop :=
  ∀ op ∈ ps, op.rw = true → op.idx ≠ x.unten

/-- The bottom position of an expression that is a bare variable. -/
def Expr.varUnten? {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} : Expr D Γ Λ τ → Option Nat
  | .var x => Option.some x.unten
  | _ => Option.none

/-- The argument handed to the callee's parameter at bottom position `j`, if it is a bare
    variable: its bottom position in the caller. -/
def Args.anUnten {Γ : Ctx} {Λ : List (Res D)} : {τs : List Ty} → Args D Γ Λ τs → Nat → Option Nat
  | _, .nil, _ => none
  | _ :: τs, .cons e rest, j => if j = τs.length then e.varUnten? else rest.anUnten j

/-- A call is admitted: every writable object parameter of the callee is handed the index
    variable of a writable object parameter of the caller, at the same table. -/
def ObjRufOk (objs : D.Fn → List (ObjPar D)) (ps : List (ObjPar D)) (f : D.Fn) {Γ : Ctx}
    {Λ : List (Res D)} (args : Args D Γ Λ (D.params f)) : Prop :=
  ∀ op' ∈ objs f, op'.rw = true →
    ∃ op ∈ ps, op.rw = true ∧ op.tab = op'.tab ∧ args.anUnten op'.idx = some op.idx

/-- An axiom that writes no table. -/
def KeinTabAx (a : D.Ax) : Prop := ∀ t, D.aschreibt a t = false

section Disziplin
variable (objs : D.Fn → List (ObjPar D)) (ps : List (ObjPar D))

mutual

/-- **The object discipline of a statement** (nested blocks included). -/
def oS {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Stmt D V l Γ Λ Λ' → Prop
  | .assignSlot t _ i _ _ _ => SchreibOk ps t i
  | .assignThru _ t _ _ i _ _ _ => SchreibOk ps t i
  | .assignThruOwn _ t _ _ i _ _ _ _ _ _ _ _ => SchreibOk ps t i
  | .assignSlotRef .. => False
  | .assignGlob .. => True
  | .putBytes .. => False
  | .assignVar x _ => VarFrei ps x
  | .shift t _ _ i _ _ _ _ _ _ => SchreibOk ps t i
  | .ite _ t e => oB t ∧ oB e
  | .onOption _ p a => oB p ∧ oB a
  | .onTag _ arms => oA arms
  | .onWhy _ arms => oG arms
  | .call f args _ _ => ObjRufOk objs ps f args
  | .callInd .. => False
  | .callIndElse .. => False
  | .locks _ _ body => oB body
  | .breaking _ body => oB body
  | .traverse _ _ body => oB body
  | .consumeTraverse _ _ _ _ _ _ body => oB body
  | .retry _ _ body ueber => oB body ∧ oB ueber
  | .forever _ _ body => oB body
  | .axiomCall a .. => KeinTabAx a
  | .axiomCallElse _ a _ _ _ _ _ _ err => KeinTabAx a ∧ oE err
  | .regWrite .. => True
  | .transition .. => True
  | .publish .. => True
  | .advances .. => True
  | .retires .. => True
  | .ret .. => True
  | .retWhy .. => True
  | .retScoped .. => True
  | .retWhyScoped .. => True
  | .leave _ => True
  | .next _ => True

def oB {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Block D V l Γ Λ Λ' → Prop
  | .nil => True
  | .cons s rest => oS s ∧ oB rest
  | .bind _ rest => oB rest
  | .bindCall f args _ _ _ rest => ObjRufOk objs ps f args ∧ oB rest
  | .bindCallInd .. => False
  | .bindCallIndElse .. => False
  | .bindCallElse f args _ _ _ err rest => ObjRufOk objs ps f args ∧ oE err ∧ oB rest
  | .bindAxiom a _ _ _ _ _ _ rest => KeinTabAx a ∧ oB rest
  | .bindAxiomElse a _ _ _ _ _ _ _ err rest => KeinTabAx a ∧ oE err ∧ oB rest
  | .bindAxiomOpt _ a _ _ _ _ _ rest => KeinTabAx a ∧ oB rest
  | .bindAxiomOptElse _ a _ _ _ _ _ _ err rest => KeinTabAx a ∧ oE err ∧ oB rest
  | .regRead _ _ rest => oB rest
  | .regReadElse _ _ _ sonst rest => oE sonst ∧ oB rest
  | .awaits _ _ _ _ _ rest => oB rest
  | .exchange _ _ _ _ rest => oB rest
  | .narrow _ _ _ sonst rest => oE sonst ∧ oB rest
  | .narrowRequired _ _ _ rest => oB rest
  | .check _ sonst rest => oE sonst ∧ oB rest
  | .float _ _ _ _ _ rest => oB rest
  | .floatLit _ _ _ rest => oB rest
  | .floatOf _ _ _ rest => oB rest
  | .floatNarrow _ _ _ sonst rest => oE sonst ∧ oB rest

def oE {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} : Endblock D V l Γ Λ → Prop
  | .ret .. => True
  | .retWhy .. => True
  | .retScoped .. => True
  | .retWhyScoped .. => True
  | .leave _ => True
  | .next _ => True
  | .cons s rest => oS s ∧ oE rest
  | .bind _ rest => oE rest
  | .bindCall f args _ _ _ rest => ObjRufOk objs ps f args ∧ oE rest
  | .bindCallElse f args _ _ _ err rest => ObjRufOk objs ps f args ∧ oE err ∧ oE rest
  | .bindAxiom a _ _ _ _ _ _ rest => KeinTabAx a ∧ oE rest
  | .bindAxiomElse a _ _ _ _ _ _ _ err rest => KeinTabAx a ∧ oE err ∧ oE rest
  | .bindAxiomOpt _ a _ _ _ _ _ rest => KeinTabAx a ∧ oE rest
  | .bindAxiomOptElse _ a _ _ _ _ _ _ err rest => KeinTabAx a ∧ oE err ∧ oE rest
  | .regRead _ _ rest => oE rest
  | .regReadElse _ _ _ sonst rest => oE sonst ∧ oE rest
  | .awaits _ _ _ _ _ rest => oE rest
  | .bindCallInd .. => False
  | .bindCallIndElse .. => False
  | .narrow _ _ _ sonst rest => oE sonst ∧ oE rest
  | .narrowRequired _ _ _ rest => oE rest
  | .exchange _ _ _ _ rest => oE rest
  | .ite _ t e => oE t ∧ oE e

def oA {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option Ty)} :
    Arms D V l Γ Λ Λ' cs → Prop
  | .nil => True
  | .cons b rest => oB b ∧ oA rest

def oG {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} :
    GrundArms D V l Γ Λ Λ' n → Prop
  | .nil => True
  | .cons b rest => oB b ∧ oG rest

end

end Disziplin
/-- **The object discipline of a program**: every body keeps it over its own object
    parameters, whose pairs are faithful to the signature. -/
def ProgObjOk (objs : D.Fn → List (ObjPar D)) (P : Programm D) : Prop :=
  ∀ f, oE objs (objs f) (P.rumpf f) ∧ LenOk (objs f) (D.params f) ∧
    ∀ op ∈ objs f, ObjParTreu D (D.params f) op

/-- **The handler keeps the frame over objects**: a completed call writes only the objects of
    the callee's writable object parameters, as its entry environment names them. -/
def ObjTreuR (objs : D.Fn → List (ObjPar D))
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) : Prop :=
  ∀ f σ ρ σ', (R f σ ρ).welt = some σ' → SlotRahmen (WVon (objs f) ρ) σ σ'

/-! ## 4. Values through bare variables and argument lists -/

theorem varUnten_eval {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ) {b : Nat}
    (h : e.varUnten? = some b) (σ0 σ : World D) (ρ : Env D Γ) :
    intVon τ (eval σ0 e σ ρ) = ρ.unten b := by
  cases e <;> simp only [Expr.varUnten?, reduceCtorEq] at h
  case var x =>
    simp only [Option.some.injEq] at h
    subst h
    rw [Env.unten_get]; rfl

theorem evalArgs_unten {Γ : Ctx} {Λ : List (Res D)} : ∀ {τs : List Ty} (args : Args D Γ Λ τs)
    {j b : Nat}, args.anUnten j = some b → ∀ (σ0 σ : World D) (ρ : Env D Γ),
    (evalArgs σ0 args σ ρ).unten j = ρ.unten b
  | _, .nil, _, _, h, _, _, _ => by simp only [Args.anUnten, reduceCtorEq] at h
  | _ :: τs, .cons e rest, j, b, h, σ0, σ, ρ => by
      simp only [Args.anUnten] at h
      simp only [evalArgs, Env.unten]
      by_cases hj : j = τs.length
      · rw [if_pos hj] at h ⊢; exact varUnten_eval e h σ0 σ ρ
      · rw [if_neg hj] at h ⊢; exact evalArgs_unten rest h σ0 σ ρ

/-- A call admitted by `ObjRufOk` hands the callee a frame inside the caller's. -/
theorem objRufOk_rahmen {objs : D.Fn → List (ObjPar D)} {W : D.Tab → Int → Prop}
    {ps : List (ObjPar D)} {f : D.Fn} {Γ : Ctx} {Λ : List (Res D)} {args : Args D Γ Λ (D.params f)}
    {ρ : Env D Γ} (hok : ObjRufOk objs ps f args) (hinv : ObjInv W ps ρ) (σ0 σ1 : World D) :
    ∀ t k, WVon (objs f) (evalArgs σ0 args σ1 ρ) t k → W t k := by
  rintro t k ⟨op', hop', hrw', htab', hk'⟩
  obtain ⟨op, hop, hrw, htab, han⟩ := hok op' hop' hrw'
  rw [evalArgs_unten args han] at hk'
  have := hinv op hop hrw k hk'
  rw [htab, htab'] at this
  exact this

/-- A store admitted by `SchreibOk` lands inside the frame. -/
theorem schreibOk_in {W : D.Tab → Int → Prop} {ps : List (ObjPar D)} {Γ : Ctx} {Λ : List (Res D)}
    {t : D.Tab} {lo hi : Int} {x : Var Γ (.int lo hi)} {ρ : Env D Γ} (hinv : ObjInv W ps ρ)
    {op : ObjPar D} (hop : op ∈ ps) (hrw : op.rw = true) (htab : op.tab = t)
    (hidx : op.idx = x.unten) (σ0 σ1 : World D) :
    W t (eval σ0 (Expr.var (Λ := Λ) x) σ1 ρ).n := by
  have h := hinv op hop hrw (ρ.get x).n (by rw [hidx, Env.unten_get]; rfl)
  rw [htab] at h
  exact h

/-! ## 5. Outcomes -/

/-- **What a run keeps**: the slot frame `W` from its entry world, and -- where it goes on
    -- index variables that still name objects inside `W`. -/
def ObjA (W : D.Tab → Int → Prop) (ps : List (ObjPar D)) (σ : World D) {V : Vertrag D} {l : Bool}
    {Γ : Ctx} : Ausgang V l Γ → Prop
  | .ok σ' ρ' => SlotRahmen W σ σ' ∧ ObjInv W ps ρ'
  | .zurueck σ' _ => SlotRahmen W σ σ'
  | .why σ' _ => SlotRahmen W σ σ'
  | .leave _ σ' ρ' => SlotRahmen W σ σ' ∧ ObjInv W ps ρ'
  | .next _ σ' ρ' => SlotRahmen W σ σ' ∧ ObjInv W ps ρ'
  | .logik _ => True
  | .hardware _ => True

def ObjE (W : D.Tab → Int → Prop) (ps : List (ObjPar D)) (σ : World D) {V : Vertrag D} {l : Bool}
    {Γ : Ctx} : EndAusgang V l Γ → Prop
  | .zurueck σ' _ => SlotRahmen W σ σ'
  | .why σ' _ => SlotRahmen W σ σ'
  | .leave _ σ' ρ' => SlotRahmen W σ σ' ∧ ObjInv W ps ρ'
  | .next _ σ' ρ' => SlotRahmen W σ σ' ∧ ObjInv W ps ρ'
  | .logik _ => True
  | .hardware _ => True

section Ausgaenge
variable {W : D.Tab → Int → Prop} {ps : List (ObjPar D)} {V : Vertrag D} {l : Bool}

theorem ObjA.vor {Γ : Ctx} {σ σ1 : World D} {o : Ausgang V l Γ} (h1 : SlotRahmen W σ σ1)
    (h : ObjA W ps σ1 o) : ObjA W ps σ o := by
  cases o <;> simp only [ObjA] at h ⊢
  all_goals first
    | exact h1.trans h
    | exact ⟨h1.trans h.1, h.2⟩

theorem ObjE.vor {Γ : Ctx} {σ σ1 : World D} {o : EndAusgang V l Γ} (h1 : SlotRahmen W σ σ1)
    (h : ObjE W ps σ1 o) : ObjE W ps σ o := by
  cases o <;> simp only [ObjE] at h ⊢
  all_goals first
    | exact h1.trans h
    | exact ⟨h1.trans h.1, h.2⟩

theorem ObjA.schrumpf {τ : Ty} {Γ : Ctx} {σ : World D} {o : Ausgang V l (τ :: Γ)}
    (h : ObjA W ps σ o) : ObjA W ps σ o.schrumpf := by
  cases o <;> simp only [ObjA, Ausgang.schrumpf] at h ⊢
  all_goals first
    | exact h
    | exact ⟨h.1, h.2.tail⟩

theorem ObjE.schrumpf {τ : Ty} {Γ : Ctx} {σ : World D} {o : EndAusgang V l (τ :: Γ)}
    (h : ObjE W ps σ o) : ObjE W ps σ o.schrumpf := by
  cases o <;> simp only [ObjE, EndAusgang.schrumpf] at h ⊢
  all_goals first
    | exact h
    | exact ⟨h.1, h.2.tail⟩

theorem ObjE.zuAusgang {Γ : Ctx} {σ : World D} {o : EndAusgang V l Γ} (h : ObjE W ps σ o) :
    ObjA W ps σ o.zuAusgang := by
  cases o <;> simp only [ObjE, ObjA, EndAusgang.zuAusgang] at h ⊢
  all_goals exact h

theorem ObjA.schrumpfArm {Γ : Ctx} {σ : World D} (c : Option Ty)
    {o : Ausgang V l (ArmCtx Γ c)} (h : ObjA W ps σ o) : ObjA W ps σ (o.schrumpfArm c) := by
  cases c with
  | none => exact h
  | some _ => exact h.schrumpf

theorem ObjA.gibt {Γ : Ctx} {σ : World D} (L : D.Lock) {o : Ausgang V l Γ}
    (h : ObjA W ps (σ.nimmt L) o) : ObjA W ps σ (o.mapWelt (·.gibt L)) := by
  cases o <;> simp only [ObjA, Ausgang.mapWelt] at h ⊢
  all_goals first
    | trivial
    | exact h
    | exact ⟨h.1, h.2⟩

theorem ObjA.welt {Γ : Ctx} {σ σ' : World D} {o : Ausgang V l Γ} (h : ObjA W ps σ o)
    (hw : o.welt = some σ') : SlotRahmen W σ σ' := by
  cases o <;> simp only [ObjA, Ausgang.welt, Option.some.injEq, reduceCtorEq] at h hw
  all_goals first
    | (subst hw; exact h)
    | (subst hw; exact h.1)

end Ausgaenge
/-! ## 6. The three loop combinators -/


end Gabbro.Grammatik
