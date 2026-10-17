/-
  File:      Grammatik/Logik/Vertraege/ObjektRahmen.lean
  Subject:   **THE FRAME OVER OBJECTS AT THE MODEL'S CALL** -- `own`/separation slice 2b,
             the run half of `Objekte.lean`.

  THE ENCODING (no change to machine G). A pointer to ONE object of table `t` is a pair of
  parameters G already has: the capability `ptr n rw` with `D.tabNr n = some t` and an
  index `index (D.count t)`. `ObjPar` names such a pair: `idx` (the index parameter),
  `cap` (the capability), both counted from the BOTTOM of the context (`Var.unten`), so a
  position stays the same under every `let` a body pushes; `rw` is the right of the
  capability (`own` travels as read-write, `lean_g.rs::param_ty`). In an environment `ρ`
  the pair names the object `⟨tab, value of idx⟩` (`ObjPar.obj`). The identity is a VALUE
  the caller chooses -- which the type alone could not say (slice 2's obstruction 1).

  THE DECLARED FRAME OVER THE WRITABLE PARAMETERS, AT OBJECT GRANULARITY. A body keeps the
  object discipline (`oS`/`oB`/`oE`, a syntactic check over the WHOLE grammar) when:
    * every slot store (`assignSlot`, `assignDurch`, `uebergang`) indexes with a writable
      object parameter's own index variable, at that parameter's table (`SchreibOk`);
    * no assignment overwrites such an index variable (`VarFrei`);
    * every call hands each writable object parameter of the callee a writable object
      parameter of its own, at the same table (`ObjRufOk`) -- the frame is inherited;
    * no axiom it calls writes a table (`KeinTabAx`); indirect calls and multi-slot byte
      stores (`schreibBytes`) are not admitted (stated, not hidden: `False` there).
  `ProgObjOk` asks it of every body of a program, with the pairs faithful to the
  signature (`ObjParTreu`: the capability and the index have the declared types).

  WHAT IS PROVED (generic: every declaration, every program, every world, every depth):
    * `stmt_obj` .. `grund_obj` -- the induction over the whole grammar: a run changes no
      slot outside the objects of the writable parameters (`SlotRahmen (WVon ..)`), and
      the index variables keep their values.
    * `rufAt_obj` -- the model's own call `rufAt` keeps that frame at every depth, under
      the hardware's frame premise `TreuO` only (H1, as `rufAt_treu`).
    * **`obj_ruf_rahmen`** -- THE FRAME AT A SEPARATED CALL: if the call frame is
      `ObjGetrennt` (the argument-to-object map injective on the pairs with a writable
      side), every run leaves every field of the object of every READ-ONLY object
      parameter unchanged -- also when it lies in the very table the call writes.
    * `umsicht_behaelt` -- the borrow rule in the model: a function whose body answers one
      of its object parameters' index (`return k;`, a re-view at one table) answers the
      SAME object it was handed; `objGetrennt_nicht_bei_einem` (`Objekte.lean`) then says
      the re-view and its source are not separated.
-/
import Grammatik.Logik.Vertraege.Objekte

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Positions from the bottom of a context -/

/-- The position of a variable counted from the BOTTOM of its context: the parameters of a
    body keep their position under every binder the body pushes above them. -/
def Var.unten : {Γ : Ctx} → {τ : Ty} → Var Γ τ → Nat
  | _ :: Γ, _, .hier => Γ.length
  | _ :: _, _, .dort x => x.unten

theorem Var.unten_lt : ∀ {Γ : Ctx} {τ : Ty} (x : Var Γ τ), x.unten < Γ.length
  | _ :: _, _, .hier => by simp [Var.unten]
  | _ :: _, _, .dort x => by have := Var.unten_lt x; simp only [Var.unten, List.length_cons]; omega

/-- The integer a value carries, where its type is a number. -/
def intVon : (τ : Ty) → Wert D τ → Option Int
  | .int _ _, v => some v.n
  | _, _ => none

/-- The integer at bottom position `j` of an environment. -/
def Env.unten : {Γ : Ctx} → Env D Γ → Nat → Option Int
  | _, .nil, _ => none
  | _ :: Γ, .cons v ρ, j => if j = Γ.length then intVon _ v else ρ.unten j

theorem Env.unten_lt : ∀ {Γ : Ctx} (ρ : Env D Γ) {j : Nat} {n : Int}, ρ.unten j = some n →
    j < Γ.length
  | _, .nil, _, _, h => by simp [Env.unten] at h
  | _ :: Γ, .cons v ρ, j, n, h => by
      simp only [Env.unten] at h
      by_cases hj : j = Γ.length
      · simp only [List.length_cons]; omega
      · rw [if_neg hj] at h
        have := Env.unten_lt ρ h
        simp only [List.length_cons]; omega

theorem Env.unten_cons {τ : Ty} {Γ : Ctx} (v : Wert D τ) (ρ : Env D Γ) {j : Nat} (hj : j < Γ.length) :
    (Env.cons v ρ).unten j = ρ.unten j := by
  simp only [Env.unten]; rw [if_neg (by omega)]

theorem Env.unten_cons_some {τ : Ty} {Γ : Ctx} (v : Wert D τ) (ρ : Env D Γ) {j : Nat} {n : Int}
    (h : ρ.unten j = some n) : (Env.cons v ρ).unten j = some n := by
  rw [Env.unten_cons v ρ (Env.unten_lt ρ h)]; exact h

theorem Env.unten_tail_some {τ : Ty} {Γ : Ctx} (ρ : Env D (τ :: Γ)) {j : Nat} {n : Int}
    (h : ρ.tail.unten j = some n) : ρ.unten j = some n := by
  cases ρ with
  | cons v ρ => exact Env.unten_cons_some v ρ h

theorem Env.unten_get : ∀ {Γ : Ctx} {τ : Ty} (ρ : Env D Γ) (x : Var Γ τ),
    ρ.unten x.unten = intVon τ (ρ.get x)
  | _ :: Γ, _, .cons v ρ, .hier => by simp [Env.unten, Var.unten, Env.get]
  | _ :: _, _, .cons _ ρ, .dort x => by
      simp only [Env.unten, Var.unten, Env.get]
      rw [if_neg (by have := Var.unten_lt x; omega)]
      exact Env.unten_get ρ x

theorem Env.unten_set : ∀ {Γ : Ctx} {τ : Ty} (ρ : Env D Γ) (x : Var Γ τ) (v : Wert D τ) {j : Nat},
    j ≠ x.unten → (ρ.set x v).unten j = ρ.unten j
  | _ :: _, _, .cons _ _, .hier, _, _, h => by
      simp only [Env.set, Env.unten, Var.unten] at h ⊢; rw [if_neg h, if_neg h]
  | _ :: Γ, _, .cons _ ρ, .dort x, v, j, h => by
      simp only [Env.set, Env.unten, Var.unten] at h ⊢
      by_cases hj : j = Γ.length
      · rw [if_pos hj, if_pos hj]
      · rw [if_neg hj, if_neg hj]; exact Env.unten_set ρ x v h

/-! ## 2. Object parameters, the objects of a call frame, the declared frame -/

/-- **An object parameter**: the index parameter at bottom position `idx` together with the
    capability at bottom position `cap`, on table `tab`, with right `rw` (writable or `own`). -/
structure ObjPar (D : Deklaration) where
  idx : Nat
  cap : Nat
  tab : D.Tab
  rw : Bool

/-- The pair is faithful to the context: the index has the generated index type of its
    table, and the capability is a pointer to that table with the pair's right. -/
def ObjParTreu (D : Deklaration) (Γ : Ctx) (op : ObjPar D) : Prop :=
  Γ.reverse[op.idx]? = some (.index (D.count op.tab)) ∧
    ∃ n, Γ.reverse[op.cap]? = some (.ptr n op.rw) ∧ D.tabNr n = some op.tab

/-- The object the pair names in an environment: its table, at the value of its index. -/
def ObjPar.obj {Γ : Ctx} (op : ObjPar D) (ρ : Env D Γ) : Option (Obj D) :=
  (ρ.unten op.idx).map fun k => ⟨op.tab, k⟩

/-- The argument-to-object map of a call frame. -/
def objVon {Γ : Ctx} (ps : List (ObjPar D)) (ρ : Env D Γ) : Fin ps.length → Option (Obj D) :=
  fun i => (ps.get i).obj ρ

/-- Which object parameters count for separation. -/
def rwVon (ps : List (ObjPar D)) : Fin ps.length → Bool := fun i => (ps.get i).rw

/-- **`ObjGetrennt` on a call frame**: the objects the writable-or-`own` parameters name differ
    from every other parameter's object. -/
def ObjGetrennt {Γ : Ctx} (ps : List (ObjPar D)) (ρ : Env D Γ) : Prop :=
  ObjGetrenntL (rwVon ps) (objVon ps ρ)

/-- **The declared frame over the writable parameters**: the slots a call with object
    parameters `ps` at entry `ρ` may write -- the objects of its writable parameters. -/
def WVon {Γ : Ctx} (ps : List (ObjPar D)) (ρ : Env D Γ) (t : D.Tab) (k : Int) : Prop :=
  ∃ op ∈ ps, op.rw = true ∧ op.tab = t ∧ ρ.unten op.idx = some k

/-- A run keeps a slot frame `W`: every slot outside `W` is as it was. -/
def SlotRahmen (W : D.Tab → Int → Prop) (σ σ' : World D) : Prop :=
  ∀ t k (f : D.Feld t), ¬ W t k → σ'.slots t k f = σ.slots t k f

theorem SlotRahmen.refl (W : D.Tab → Int → Prop) (σ : World D) : SlotRahmen W σ σ :=
  fun _ _ _ _ => rfl

theorem SlotRahmen.trans {W : D.Tab → Int → Prop} {a b c : World D} (h1 : SlotRahmen W a b)
    (h2 : SlotRahmen W b c) : SlotRahmen W a c :=
  fun t k f hn => (h2 t k f hn).trans (h1 t k f hn)

theorem SlotRahmen.mono {W W' : D.Tab → Int → Prop} {a b : World D}
    (hW : ∀ t k, W t k → W' t k) (h : SlotRahmen W a b) : SlotRahmen W' a b :=
  fun t k f hn => h t k f (fun hw => hn (hW t k hw))

theorem slotRahmen_gleich {W : D.Tab → Int → Prop} {σ σ' : World D} (h : σ'.slots = σ.slots) :
    SlotRahmen W σ σ' := fun t k f _ => by rw [h]

/-- One slot store inside the frame keeps it. -/
theorem slotRahmen_schreib {W : D.Tab → Int → Prop} (σ σ1 : World D) (hs : σ1.slots = σ.slots)
    {t : D.Tab} {k : Int} (f : D.Feld t) (v : Wert D (D.typ t f)) (Λ : List (Res D))
    (hw : W t k) : SlotRahmen W σ (σ1.schreibSlot t Λ k f v) := by
  intro t' k' f' hn
  show (σ1.storeSlot t k f v).slots t' k' f' = σ.slots t' k' f'
  rw [← hs]
  by_cases ht : t' = t
  · subst ht
    have hk : k' ≠ k := fun h => hn (h ▸ hw)
    exact storeSlot_anderer_slot σ1 t' k f v k' hk f'
  · exact storeSlot_andere σ1 t k f v t' ht k' f'

/-- The index variables of the writable parameters still name objects inside `W`. -/
def ObjInv {Γ : Ctx} (W : D.Tab → Int → Prop) (ps : List (ObjPar D)) (ρ : Env D Γ) : Prop :=
  ∀ op ∈ ps, op.rw = true → ∀ k, ρ.unten op.idx = some k → W op.tab k

/-- The writable pairs lie inside the context. -/
def LenOk (ps : List (ObjPar D)) (Γ : Ctx) : Prop := ∀ op ∈ ps, op.rw = true → op.idx < Γ.length

theorem LenOk.cons {ps : List (ObjPar D)} {Γ : Ctx} (h : LenOk ps Γ) (τ : Ty) : LenOk ps (τ :: Γ) :=
  fun op hop hrw => by have := h op hop hrw; simp only [List.length_cons]; omega

theorem LenOk.arm {ps : List (ObjPar D)} {Γ : Ctx} (h : LenOk ps Γ) (c : Option (Int × Int)) :
    LenOk ps (ArmCtx Γ c) := by
  cases c with
  | none => exact h
  | some p => obtain ⟨lo, hi⟩ := p; exact h.cons _

section Inv
variable {W : D.Tab → Int → Prop} {ps : List (ObjPar D)}

theorem objInv_eigen {Γ : Ctx} (ps : List (ObjPar D)) (ρ : Env D Γ) : ObjInv (WVon ps ρ) ps ρ :=
  fun op hop hrw _ hk => ⟨op, hop, hrw, rfl, hk⟩

theorem ObjInv.cons {τ : Ty} {Γ : Ctx} {ρ : Env D Γ} (hlen : LenOk ps Γ) (h : ObjInv W ps ρ)
    (v : Wert D τ) : ObjInv W ps (Env.cons v ρ) := by
  intro op hop hrw k hk
  rw [Env.unten_cons v ρ (hlen op hop hrw)] at hk
  exact h op hop hrw k hk

theorem ObjInv.tail {τ : Ty} {Γ : Ctx} {ρ : Env D (τ :: Γ)} (h : ObjInv W ps ρ) :
    ObjInv W ps ρ.tail :=
  fun op hop hrw k hk => h op hop hrw k (Env.unten_tail_some ρ hk)

theorem ObjInv.arm {Γ : Ctx} {ρ : Env D Γ} (hlen : LenOk ps Γ) (h : ObjInv W ps ρ)
    {c : Option (Int × Int)} (nutz : Nutzlast c) : ObjInv W ps (armEnv nutz ρ) := by
  cases c with
  | none => exact h
  | some p => obtain ⟨lo, hi⟩ := p; exact h.cons hlen _

end Inv

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
  | .assignDurch _ t _ _ i _ _ _ => SchreibOk ps t i
  | .assignGlob .. => True
  | .schreibBytes .. => False
  | .assignVar x _ => VarFrei ps x
  | .uebergang t _ _ i _ _ _ _ _ _ => SchreibOk ps t i
  | .ite _ t e => oB t ∧ oB e
  | .onOption _ p a => oB p ∧ oB a
  | .onTag _ arms => oA arms
  | .onGrund _ arms => oG arms
  | .call f args _ _ => ObjRufOk objs ps f args
  | .callInd .. => False
  | .locks _ _ body => oB body
  | .breaking _ body => oB body
  | .traverse _ _ body => oB body
  | .retry _ _ body ueber => oB body ∧ oB ueber
  | .forever _ _ body => oB body
  | .axiomCall a .. => KeinTabAx a
  | .regSchreib .. => True
  | .transition .. => True
  | .publish .. => True
  | .advances .. => True
  | .retires .. => True
  | .ret .. => True
  | .retGrund .. => True
  | .leave _ => True
  | .next _ => True

def oB {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Block D V l Γ Λ Λ' → Prop
  | .nil => True
  | .cons s rest => oS s ∧ oB rest
  | .bind _ rest => oB rest
  | .bindCall f args _ _ _ rest => ObjRufOk objs ps f args ∧ oB rest
  | .bindCallInd .. => False
  | .bindCallElse f args _ _ _ err rest => ObjRufOk objs ps f args ∧ oE err ∧ oB rest
  | .bindAxiom a _ _ _ _ _ _ rest => KeinTabAx a ∧ oB rest
  | .bindAxiomElse a _ _ _ _ _ _ _ err rest => KeinTabAx a ∧ oE err ∧ oB rest
  | .regLies _ _ rest => oB rest
  | .regLiesElse _ _ _ sonst rest => oE sonst ∧ oB rest
  | .awaits _ _ _ _ rest => oB rest
  | .exchange _ _ _ _ rest => oB rest
  | .narrow _ _ _ sonst rest => oE sonst ∧ oB rest
  | .pruefung _ sonst rest => oE sonst ∧ oB rest
  | .gleit _ _ _ _ _ rest => oB rest
  | .gleitLit _ _ _ rest => oB rest
  | .gleitVon _ _ _ rest => oB rest
  | .gleitNarrow _ _ _ sonst rest => oE sonst ∧ oB rest

def oE {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} : Endblock D V l Γ Λ → Prop
  | .ret .. => True
  | .retGrund .. => True
  | .leave _ => True
  | .next _ => True
  | .cons s rest => oS s ∧ oE rest
  | .bind _ rest => oE rest
  | .bindAxiom a _ _ _ _ _ _ rest => KeinTabAx a ∧ oE rest
  | .bindAxiomElse a _ _ _ _ _ _ _ err rest => KeinTabAx a ∧ oE err ∧ oE rest

def oA {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} :
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
  | _, .nil, _, _, h, _, _, _ => by simp [Args.anUnten] at h
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
  | .grund σ' _ => SlotRahmen W σ σ'
  | .leave _ σ' ρ' => SlotRahmen W σ σ' ∧ ObjInv W ps ρ'
  | .next _ σ' ρ' => SlotRahmen W σ σ' ∧ ObjInv W ps ρ'
  | .logik _ => True
  | .hardware _ => True

def ObjE (W : D.Tab → Int → Prop) (ps : List (ObjPar D)) (σ : World D) {V : Vertrag D} {l : Bool}
    {Γ : Ctx} : EndAusgang V l Γ → Prop
  | .zurueck σ' _ => SlotRahmen W σ σ'
  | .grund σ' _ => SlotRahmen W σ σ'
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

theorem ObjA.schrumpfArm {Γ : Ctx} {σ : World D} (c : Option (Int × Int))
    {o : Ausgang V l (ArmCtx Γ c)} (h : ObjA W ps σ o) : ObjA W ps σ (o.schrumpfArm c) := by
  cases c with
  | none => exact h
  | some p => obtain ⟨_, _⟩ := p; exact h.schrumpf

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

section Schleifen
variable {W : D.Tab → Int → Prop} {ps : List (ObjPar D)} {V : Vertrag D} {l : Bool}

theorem traverseLauf_obj {τ : Ty} {Γ : Ctx} (hlen : LenOk ps Γ)
    (schritt : World D → Env D (τ :: Γ) → Ausgang V true (τ :: Γ))
    (inv : World D → Env D Γ → World D × Bool)
    (hs : ∀ σ ρ, ObjInv W ps ρ → ObjA W ps σ (schritt σ ρ))
    (hi : ∀ σ ρ, SlotRahmen W σ (inv σ ρ).1) :
    ∀ (ks : List (Wert D τ)) (σ : World D) (ρ : Env D Γ), ObjInv W ps ρ →
      ObjA W ps σ (traverseLauf (l := l) schritt inv ks σ ρ) := by
  intro ks
  induction ks with
  | nil =>
      intro σ ρ hρ
      simp only [traverseLauf]
      split
      · exact ⟨hi σ ρ, hρ⟩
      · trivial
  | cons k ks ih =>
      intro σ ρ hρ
      simp only [traverseLauf]
      split
      · trivial
      · have hstep := hs (inv σ ρ).1 (.cons k ρ) (hρ.cons hlen k)
        split
        · rename_i σ1 ρ1 hs1
          rw [hs1] at hstep
          exact ObjA.vor ((hi σ ρ).trans hstep.1) (ih σ1 ρ1.tail hstep.2.tail)
        · rename_i σ1 ρ1 hs1
          rw [hs1] at hstep
          exact ObjA.vor ((hi σ ρ).trans hstep.1) (ih σ1 ρ1.tail hstep.2.tail)
        · rename_i σ1 ρ1 hs1
          rw [hs1] at hstep
          split
          · exact ⟨((hi σ ρ).trans hstep.1).trans (hi σ1 ρ1.tail), hstep.2.tail⟩
          · trivial
        · rename_i σ1 v hs1
          rw [hs1] at hstep
          exact (hi σ ρ).trans hstep
        · rename_i σ1 r hs1
          rw [hs1] at hstep
          exact (hi σ ρ).trans hstep
        · trivial
        · trivial

theorem retryLauf_obj {Γ : Ctx} (schritt : World D → Env D Γ → Ausgang V true Γ)
    (bis : World D → Env D Γ → World D × Bool) (ueberlauf : World D → Env D Γ → Ausgang V l Γ)
    (hs : ∀ σ ρ, ObjInv W ps ρ → ObjA W ps σ (schritt σ ρ))
    (hb : ∀ σ ρ, SlotRahmen W σ (bis σ ρ).1)
    (hu : ∀ σ ρ, ObjInv W ps ρ → ObjA W ps σ (ueberlauf σ ρ)) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ), ObjInv W ps ρ →
      ObjA W ps σ (retryLauf schritt bis ueberlauf n σ ρ) := by
  intro n
  induction n with
  | zero =>
      intro σ ρ hρ
      simp only [retryLauf]
      split
      · exact ⟨hb σ ρ, hρ⟩
      · exact ObjA.vor (hb σ ρ) (hu _ ρ hρ)
  | succ n ih =>
      intro σ ρ hρ
      simp only [retryLauf]
      split
      · exact ⟨hb σ ρ, hρ⟩
      · have hstep := hs (bis σ ρ).1 ρ hρ
        split
        · rename_i σ1 ρ1 hs1
          rw [hs1] at hstep
          exact ObjA.vor ((hb σ ρ).trans hstep.1) (ih σ1 ρ1 hstep.2)
        · rename_i σ1 ρ1 hs1
          rw [hs1] at hstep
          exact ObjA.vor ((hb σ ρ).trans hstep.1) (ih σ1 ρ1 hstep.2)
        · rename_i σ1 ρ1 hs1
          rw [hs1] at hstep
          exact ⟨(hb σ ρ).trans hstep.1, hstep.2⟩
        · rename_i σ1 v hs1
          rw [hs1] at hstep
          exact (hb σ ρ).trans hstep
        · rename_i σ1 r hs1
          rw [hs1] at hstep
          exact (hb σ ρ).trans hstep
        · trivial
        · trivial

theorem foreverLauf_obj {Γ : Ctx} (a : D.Annahme) (schritt : World D → Env D Γ → Ausgang V true Γ)
    (inv : World D → Env D Γ → World D × Bool)
    (hs : ∀ σ ρ, ObjInv W ps ρ → ObjA W ps σ (schritt σ ρ))
    (hi : ∀ σ ρ, SlotRahmen W σ (inv σ ρ).1) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ), ObjInv W ps ρ →
      ObjA W ps σ (foreverLauf (l := l) a schritt inv n σ ρ) := by
  intro n
  induction n with
  | zero => intro σ ρ _; simp only [foreverLauf]; trivial
  | succ n ih =>
      intro σ ρ hρ
      simp only [foreverLauf]
      split
      · trivial
      · have hstep := hs (inv σ ρ).1 ρ hρ
        split
        · rename_i σ1 ρ1 hs1
          rw [hs1] at hstep
          exact ObjA.vor ((hi σ ρ).trans hstep.1) (ih σ1 ρ1 hstep.2)
        · rename_i σ1 ρ1 hs1
          rw [hs1] at hstep
          exact ObjA.vor ((hi σ ρ).trans hstep.1) (ih σ1 ρ1 hstep.2)
        · rename_i σ1 ρ1 hs1
          rw [hs1] at hstep
          exact ⟨(hi σ ρ).trans hstep.1, hstep.2⟩
        · rename_i σ1 v hs1
          rw [hs1] at hstep
          exact (hi σ ρ).trans hstep
        · rename_i σ1 r hs1
          rw [hs1] at hstep
          exact (hi σ ρ).trans hstep
        · trivial
        · trivial

end Schleifen

/-- A completed call admitted by `ObjRufOk` stays inside the caller's frame. -/
theorem ruf_rahmen_in {objs : D.Fn → List (ObjPar D)} {W : D.Tab → Int → Prop}
    {ps : List (ObjPar D)} {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f}
    (hR : ObjTreuR objs R) {Γ : Ctx} {Λ : List (Res D)} {f : D.Fn}
    {args : Args D Γ Λ (D.params f)} {ρ : Env D Γ} (hok : ObjRufOk objs ps f args)
    (hinv : ObjInv W ps ρ) (σ σ1 : World D)
    (hw : (R f (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)).welt =
      some σ1) : SlotRahmen W σ σ1 :=
  (hR f (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) σ1 hw).mono
    (objRufOk_rahmen hok hinv _ _)

/-- An axiom that writes no table changes no slot. -/
theorem axiom_rahmen {O : Orakel D} (hO : TreuO O) {W : D.Tab → Int → Prop} {a : D.Ax}
    (hok : KeinTabAx a) (σ : World D) (ρ : Env D (D.aparams a))
    {σ1 : World D} (h : (axiomAntwort O a σ ρ).1 = σ1) : SlotRahmen W σ σ1 := by
  have h1 := axiomAntwort_treu O hO a σ ρ
  rw [h] at h1
  exact fun t k f _ => h1.1.1 t (hok t) k f

/-! ## 7. THE INDUCTION over the whole grammar -/

section Rumpf
variable (O : Orakel D) (passes : Nat)
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable (objs : D.Fn → List (ObjPar D)) (W : D.Tab → Int → Prop) (ps : List (ObjPar D))
variable (hR : ObjTreuR objs R) (hO : TreuO O)
include hR hO
set_option linter.unusedSectionVars false

mutual

/-- **The frame over objects of one statement**, at EVERY world. -/
theorem stmt_obj {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    ∀ (s : Stmt D V l Γ Λ Λ'), oS objs ps s → ∀ (σ : World D) (ρ : Env D Γ),
    LenOk ps Γ → ObjInv W ps ρ → ObjA W ps σ (execStmt O passes R s σ ρ)
  | .assignSlot t f i e hw hL, hok, σ, ρ, _, hinv => by
      obtain ⟨x, rfl, op, hop, hrw, htab, hidx⟩ := hok
      simp only [execStmt]
      exact ⟨slotRahmen_schreib σ _ rfl f _ Λ (schreibOk_in hinv hop hrw htab hidx _ _), hinv⟩
  | .assignDurch p t _ f i e hw hL, hok, σ, ρ, _, hinv => by
      obtain ⟨x, rfl, op, hop, hrw, htab, hidx⟩ := hok
      simp only [execStmt]
      exact ⟨slotRahmen_schreib σ _ rfl f _ Λ (schreibOk_in hinv hop hrw htab hidx _ _), hinv⟩
  | .assignGlob g e hw hL, _, σ, ρ, _, hinv => by
      simp only [execStmt]
      exact ⟨slotRahmen_gleich rfl, hinv⟩
  | .schreibBytes .., hok, _, _, _, _ => hok.elim
  | .assignVar x e, hok, σ, ρ, _, hinv => by
      simp only [execStmt]
      refine ⟨slotRahmen_gleich rfl, ?_⟩
      intro op hop hrw k hk
      rw [Env.unten_set ρ x _ (hok op hop hrw)] at hk
      exact hinv op hop hrw k hk
  | .uebergang t f hτ i von nach hn he hw hL, hok, σ, ρ, _, hinv => by
      obtain ⟨x, rfl, op, hop, hrw, htab, hidx⟩ := hok
      simp only [execStmt]
      split
      · exact ⟨slotRahmen_schreib σ _ rfl f _ Λ (schreibOk_in hinv hop hrw htab hidx _ _), hinv⟩
      · trivial
  | .ite c t e, hok, σ, ρ, hlen, hinv => by
      simp only [execStmt]
      split
      · exact ObjA.vor (slotRahmen_gleich rfl) (block_obj t hok.1 _ ρ hlen hinv)
      · exact ObjA.vor (slotRahmen_gleich rfl) (block_obj e hok.2 _ ρ hlen hinv)
  | .onOption o p a, hok, σ, ρ, hlen, hinv => by
      simp only [execStmt]
      split
      · rename_i k _
        exact ObjA.vor (slotRahmen_gleich rfl)
          (block_obj p hok.1 _ (.cons k ρ) (hlen.cons _) (hinv.cons hlen _)).schrumpf
      · exact ObjA.vor (slotRahmen_gleich rfl) (block_obj a hok.2 _ ρ hlen hinv)
  | .onTag v arms, hok, σ, ρ, hlen, hinv => by
      simp only [execStmt]
      exact ObjA.vor (slotRahmen_gleich rfl) (arms_obj arms hok _ _ ρ hlen hinv)
  | .onGrund r arms, hok, σ, ρ, hlen, hinv => by
      simp only [execStmt]
      exact ObjA.vor (slotRahmen_gleich rfl) (grund_obj arms hok _ _ ρ hlen hinv)
  | .call f args hp hr, hok, σ, ρ, _, hinv => by
      simp only [execStmt]
      split
      · rename_i σ1 v hR1
        exact ⟨ruf_rahmen_in hR hok hinv σ σ1 (by rw [hR1]; rfl), hinv⟩
      · rename_i σ1 r _; exact keinGrund hr r
      · trivial
      · trivial
  | .callInd .., hok, _, _, _, _ => hok.elim
  | .locks L hr body, hok, σ, ρ, hlen, hinv => by
      simp only [execStmt]
      exact ObjA.gibt L (block_obj body hok (σ.nimmt L) ρ hlen hinv)
  | .breaking _ body, hok, σ, ρ, hlen, hinv => by
      simp only [execStmt]
      exact block_obj body hok σ ρ hlen hinv
  | .traverse t inv body, hok, σ, ρ, hlen, hinv => by
      simp only [execStmt]
      exact traverseLauf_obj hlen _ _ (fun σ ρ h => block_obj body hok σ ρ (hlen.cons _) h)
        (fun _ _ => slotRahmen_gleich rfl) _ σ ρ hinv
  | .retry n bis body ueberlauf, hok, σ, ρ, hlen, hinv => by
      simp only [execStmt]
      exact retryLauf_obj _ _ _ (fun σ ρ h => block_obj body hok.1 σ ρ hlen h)
        (fun _ _ => slotRahmen_gleich rfl) (fun σ ρ h => block_obj ueberlauf hok.2 σ ρ hlen h)
        n σ ρ hinv
  | .forever a inv body, hok, σ, ρ, hlen, hinv => by
      simp only [execStmt]
      exact foreverLauf_obj a _ _ (fun σ ρ h => block_obj body hok σ ρ hlen h)
        (fun _ _ => slotRahmen_gleich rfl) passes σ ρ hinv
  | .axiomCall a args _ hw hg hd hgd, hok, σ, ρ, _, hinv => by
      simp only [execStmt]
      split
      · rename_i σ1 v ha
        refine ⟨?_, hinv⟩
        exact axiom_rahmen hO hok (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) (by rw [ha])
      · trivial
  | .regSchreib r _ e, _, σ, ρ, _, hinv => by
      simp only [execStmt]
      exact ⟨slotRahmen_gleich rfl, hinv⟩
  | .transition .., _, σ, ρ, _, hinv => by
      simp only [execStmt]
      exact ⟨SlotRahmen.refl _ _, hinv⟩
  | .publish g e _ _ hw hL, _, σ, ρ, _, hinv => by
      simp only [execStmt]
      exact ⟨slotRahmen_gleich rfl, hinv⟩
  | .advances .., _, σ, ρ, _, hinv => by
      simp only [execStmt]
      exact ⟨SlotRahmen.refl _ _, hinv⟩
  | .retires .., _, σ, ρ, _, hinv => by
      simp only [execStmt]
      exact ⟨SlotRahmen.refl _ _, hinv⟩
  | .ret e _, _, σ, ρ, _, _ => by
      simp only [execStmt]
      exact slotRahmen_gleich rfl
  | .retGrund .., _, σ, ρ, _, _ => by
      simp only [execStmt]
      exact SlotRahmen.refl _ _
  | .leave _, _, σ, ρ, _, hinv => by
      simp only [execStmt]
      exact ⟨SlotRahmen.refl _ _, hinv⟩
  | .next _, _, σ, ρ, _, hinv => by
      simp only [execStmt]
      exact ⟨SlotRahmen.refl _ _, hinv⟩

/-- **The frame over objects of a block.** -/
theorem block_obj {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    ∀ (b : Block D V l Γ Λ Λ'), oB objs ps b → ∀ (σ : World D) (ρ : Env D Γ),
    LenOk ps Γ → ObjInv W ps ρ → ObjA W ps σ (execBlock O passes R b σ ρ)
  | .nil, _, σ, ρ, _, hinv => by
      simp only [execBlock]
      exact ⟨SlotRahmen.refl _ _, hinv⟩
  | .cons s rest, hok, σ, ρ, hlen, hinv => by
      simp only [execBlock]
      have hs := stmt_obj s hok.1 σ ρ hlen hinv
      split
      · rename_i σ1 ρ1 hs1
        rw [hs1] at hs
        exact ObjA.vor hs.1 (block_obj rest hok.2 σ1 ρ1 hlen hs.2)
      · exact hs
  | .bind e rest, hok, σ, ρ, hlen, hinv => by
      simp only [execBlock]
      exact ObjA.vor (slotRahmen_gleich rfl)
        (block_obj rest hok _ _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
  | .bindCall f args he hp hr rest, hok, σ, ρ, hlen, hinv => by
      simp only [execBlock]
      split
      · rename_i σ1 v hR1
        exact ObjA.vor (ruf_rahmen_in hR hok.1 hinv σ σ1 (by rw [hR1]; rfl))
          (block_obj rest hok.2 σ1 _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
      · rename_i σ1 r _; exact keinGrund hr r
      · trivial
      · trivial
  | .bindCallInd .., hok, _, _, _, _ => hok.elim
  | .bindCallElse f args he hp _ err rest, hok, σ, ρ, hlen, hinv => by
      simp only [execBlock]
      split
      · rename_i σ1 v hR1
        exact ObjA.vor (ruf_rahmen_in hR hok.1 hinv σ σ1 (by rw [hR1]; rfl))
          (block_obj rest hok.2.2 σ1 _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
      · rename_i σ1 r hR1
        exact ObjA.vor (ruf_rahmen_in hR hok.1 hinv σ σ1 (by rw [hR1]; rfl))
          (end_obj err hok.2.1 σ1 _ (hlen.cons _) (hinv.cons hlen _)).schrumpf.zuAusgang
      · trivial
      · trivial
  | .bindAxiom a args he hw hg hd hgd rest, hok, σ, ρ, hlen, hinv => by
      simp only [execBlock]
      split
      · rename_i σ1 v ha
        exact ObjA.vor (axiom_rahmen hO hok.1 (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) (by rw [ha]))
          (block_obj rest hok.2 σ1 _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
      · trivial
  | .bindAxiomElse a args he hr hw hg hd hgd err rest, hok, σ, ρ, hlen, hinv => by
      simp only [execBlock]
      split
      · rename_i σ1 v ha
        exact ObjA.vor (axiom_rahmen hO hok.1 (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
            (by rw [← axiomAntwortSonst_fst, ha]))
          (block_obj rest hok.2.2 σ1 _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
      · rename_i σ1 r ha
        exact ObjA.vor (axiom_rahmen hO hok.1 (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
            (by rw [← axiomAntwortSonst_fst, ha]))
          (end_obj err hok.2.1 σ1 _ (hlen.cons _) (hinv.cons hlen _)).schrumpf.zuAusgang
      · trivial
  | .regLies r _ rest, hok, σ, ρ, hlen, hinv => by
      simp only [execBlock]
      split
      · split
        · exact (block_obj rest hok σ _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
        · trivial
      · trivial
  | .regLiesElse r _ zusage sonst rest, hok, σ, ρ, hlen, hinv => by
      simp only [execBlock]
      split
      · split
        · exact ObjA.vor (slotRahmen_gleich rfl)
            (block_obj rest hok.2 _ _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
        · exact ObjA.vor (slotRahmen_gleich rfl) (end_obj sonst hok.1 _ ρ hlen hinv).zuAusgang
      · trivial
  | .awaits g _ _ hL rest, hok, σ, ρ, hlen, hinv => by
      simp only [execBlock]
      split
      · exact ObjA.vor (slotRahmen_gleich rfl)
          (block_obj rest hok _ _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
      · trivial
  | .exchange g neu hw hL rest, hok, σ, ρ, hlen, hinv => by
      simp only [execBlock]
      exact ObjA.vor (slotRahmen_gleich rfl)
        (block_obj rest hok _ _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
  | .narrow e lo' hi' sonst rest, hok, σ, ρ, hlen, hinv => by
      simp only [execBlock]
      split
      · exact ObjA.vor (slotRahmen_gleich rfl)
          (block_obj rest hok.2 _ _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
      · exact ObjA.vor (slotRahmen_gleich rfl) (end_obj sonst hok.1 _ ρ hlen hinv).zuAusgang
  | .pruefung c sonst rest, hok, σ, ρ, hlen, hinv => by
      simp only [execBlock]
      split
      · exact ObjA.vor (slotRahmen_gleich rfl) (block_obj rest hok.2 _ ρ hlen hinv)
      · exact ObjA.vor (slotRahmen_gleich rfl) (end_obj sonst hok.1 _ ρ hlen hinv).zuAusgang
  | .gleit op a b lo hi rest, hok, σ, ρ, hlen, hinv => by
      simp only [execBlock]
      split
      · exact ObjA.vor (slotRahmen_gleich rfl)
          (block_obj rest hok _ _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
      · trivial
  | .gleitLit q lo hi rest, hok, σ, ρ, hlen, hinv => by
      simp only [execBlock]
      split
      · exact (block_obj rest hok σ _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
      · trivial
  | .gleitVon e lo hi rest, hok, σ, ρ, hlen, hinv => by
      simp only [execBlock]
      split
      · exact ObjA.vor (slotRahmen_gleich rfl)
          (block_obj rest hok _ _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
      · trivial
  | .gleitNarrow e lo hi sonst rest, hok, σ, ρ, hlen, hinv => by
      simp only [execBlock]
      split
      · exact ObjA.vor (slotRahmen_gleich rfl)
          (block_obj rest hok.2 _ _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
      · exact ObjA.vor (slotRahmen_gleich rfl) (end_obj sonst hok.1 _ ρ hlen hinv).zuAusgang

/-- **The frame over objects of an end block.** -/
theorem end_obj {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    ∀ (b : Endblock D V l Γ Λ), oE objs ps b → ∀ (σ : World D) (ρ : Env D Γ),
    LenOk ps Γ → ObjInv W ps ρ → ObjE W ps σ (execEnd O passes R b σ ρ)
  | .ret e _, _, σ, ρ, _, _ => by
      simp only [execEnd]
      exact slotRahmen_gleich rfl
  | .retGrund .., _, σ, ρ, _, _ => by
      simp only [execEnd]
      exact SlotRahmen.refl _ _
  | .leave _, _, σ, ρ, _, hinv => by
      simp only [execEnd]
      exact ⟨SlotRahmen.refl _ _, hinv⟩
  | .next _, _, σ, ρ, _, hinv => by
      simp only [execEnd]
      exact ⟨SlotRahmen.refl _ _, hinv⟩
  | .cons s rest, hok, σ, ρ, hlen, hinv => by
      simp only [execEnd]
      have hs := stmt_obj s hok.1 σ ρ hlen hinv
      split
      · rename_i σ1 ρ1 hs1
        rw [hs1] at hs
        exact ObjE.vor hs.1 (end_obj rest hok.2 σ1 ρ1 hlen hs.2)
      all_goals first
        | trivial
        | (rename_i hs1; rw [hs1] at hs; exact hs)
  | .bind e rest, hok, σ, ρ, hlen, hinv => by
      simp only [execEnd]
      exact ObjE.vor (slotRahmen_gleich rfl)
        (end_obj rest hok _ _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
  | .bindAxiom a args he hw hg hd hgd rest, hok, σ, ρ, hlen, hinv => by
      simp only [execEnd]
      split
      · rename_i σ1 v ha
        exact ObjE.vor (axiom_rahmen hO hok.1 (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) (by rw [ha]))
          (end_obj rest hok.2 σ1 _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
      · trivial
  | .bindAxiomElse a args he hr hw hg hd hgd err rest, hok, σ, ρ, hlen, hinv => by
      simp only [execEnd]
      split
      · rename_i σ1 v ha
        exact ObjE.vor (axiom_rahmen hO hok.1 (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
            (by rw [← axiomAntwortSonst_fst, ha]))
          (end_obj rest hok.2.2 σ1 _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
      · rename_i σ1 r ha
        exact ObjE.vor (axiom_rahmen hO hok.1 (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
            (by rw [← axiomAntwortSonst_fst, ha]))
          (end_obj err hok.2.1 σ1 _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
      · trivial

theorem arms_obj {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} :
    ∀ (arms : Arms D V l Γ Λ Λ' cs), oA objs ps arms → ∀ (v : Wert D (.sum cs)) (σ : World D)
    (ρ : Env D Γ), LenOk ps Γ → ObjInv W ps ρ → ObjA W ps σ (execArms O passes R arms v σ ρ)
  | .cons b _, hok, ⟨⟨0, _⟩, nutz⟩, σ, ρ, hlen, hinv =>
      (block_obj b hok.1 σ (armEnv nutz ρ) (hlen.arm _) (hinv.arm hlen nutz)).schrumpfArm _
  | .cons _ rest, hok, ⟨⟨_ + 1, _⟩, _⟩, σ, ρ, hlen, hinv => arms_obj rest hok.2 _ σ ρ hlen hinv

theorem grund_obj {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} :
    ∀ (arms : GrundArms D V l Γ Λ Λ' n), oG objs ps arms → ∀ (r : Fin n) (σ : World D)
    (ρ : Env D Γ), LenOk ps Γ → ObjInv W ps ρ → ObjA W ps σ (execGrund O passes R arms r σ ρ)
  | .cons b _, hok, ⟨0, _⟩, σ, ρ, hlen, hinv => block_obj b hok.1 σ ρ hlen hinv
  | .cons _ rest, hok, ⟨_ + 1, _⟩, σ, ρ, hlen, hinv => grund_obj rest hok.2 _ σ ρ hlen hinv

end

end Rumpf

/-! ## 8. THE CALL: `rufAt` keeps the frame over objects, and the frame at a separated call -/

theorem foldl_lese_slots_obj (P : Programm D) :
    ∀ (is : List D.Inv) (σ : World D),
      (is.foldl (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte) σ).slots = σ.slots
  | [], _ => rfl
  | i :: is, σ => foldl_lese_slots_obj P is (σ.lese (invSicht D i) (P.invariante i).orte)

/-- **The model's call keeps the frame over objects, at every depth and every world.** The
    only premise besides the program's discipline is the hardware's frame (H1). -/
theorem rufAt_obj (P : Programm D) (O : Orakel D) (passes : Nat) (hO : TreuO O)
    (objs : D.Fn → List (ObjPar D)) (hP : ProgObjOk objs P) :
    ∀ fuel, ObjTreuR objs (rufAt P O passes fuel) := by
  intro fuel
  induction fuel with
  | zero => intro f σ ρ σ' h; simp [rufAt, RufAusgang.welt] at h
  | succ n ih =>
      intro f σ ρ σ' h
      simp only [rufAt] at h
      split at h
      · simp [RufAusgang.welt] at h
      · have hb := end_obj (O := O) (passes := passes) (R := rufAt P O passes n) (objs := objs)
          (W := WVon (objs f) ρ) (ps := objs f) ih hO (P.rumpf f) (hP f).1
          (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ (hP f).2.1
          (objInv_eigen _ ρ)
        split at h
        · rename_i σ2 v hs
          rw [hs] at hb
          split at h
          · simp [RufAusgang.welt] at h
          · split at h
            · simp [RufAusgang.welt] at h
            · simp only [RufAusgang.welt, Option.some.injEq] at h
              subst h
              intro t k fld hn
              rw [foldl_lese_slots_obj]
              exact hb t k fld hn
        · rename_i σ2 r hs
          simp only [RufAusgang.welt, Option.some.injEq] at h
          subst h
          rw [hs] at hb
          exact hb
        · rename_i hl _ _ _; exact absurd hl (by decide)
        · rename_i hl _ _ _; exact absurd hl (by decide)
        · simp [RufAusgang.welt] at h
        · simp [RufAusgang.welt] at h

/-- **THE FRAME AT A SEPARATED CALL.** For every program that keeps the object discipline,
    every function `f`, every depth, world and entry environment `ρ` whose call frame is
    `ObjGetrennt`, and every READ-ONLY object parameter `i` of `f` naming object `o`: every
    run of the model's call leaves every field of `o` as it was -- also when `o` lies in a
    table the call writes. -/
theorem obj_ruf_rahmen (P : Programm D) (O : Orakel D) (passes fuel : Nat) (hO : TreuO O)
    (objs : D.Fn → List (ObjPar D)) (hP : ProgObjOk objs P) (f : D.Fn)
    (σ : World D) (ρ : Env D (D.params f)) (σ' : World D)
    (h : (rufAt P O passes fuel f σ ρ).welt = some σ')
    (hG : ObjGetrennt (objs f) ρ) (i : Fin (objs f).length) (hi : ((objs f).get i).rw = false)
    {o : Obj D} (ho : objVon (objs f) ρ i = some o) :
    ∀ fld : D.Feld o.tab, σ'.slots o.tab o.nr fld = σ.slots o.tab o.nr fld := by
  intro fld
  apply rufAt_obj P O passes hO objs hP fuel f σ ρ σ' h
  rintro ⟨op, hop, hrw, htab, hk⟩
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hop
  have hij : i ≠ j := by
    intro e; subst e; rw [hj] at hi; rw [hi] at hrw; cases hrw
  have hz : (rwVon (objs f) i || rwVon (objs f) j) = true := by
    simp only [rwVon, hj, hrw, Bool.or_true]
  have hoj : objVon (objs f) ρ j = some o := by
    simp only [objVon, ObjPar.obj, hj, hk, Option.map_some]
    exact congrArg some (Obj.ext' htab rfl)
  exact objGetrennt_paarweise hG i j hij hz ho hoj rfl

/-! ## 9. The borrow rule in the model: a re-view answers the object it was handed -/

/-- The integer of an answer, where the answer is a number. -/
def ergInt : (e : Option Ty) → ErgVal D e → Option Int
  | some τ, v => intVon τ v
  | none, _ => none

/-- The bottom position of an answer that is a bare variable. -/
def ErgExpr.varUnten? {Γ : Ctx} {Λ : List (Res D)} {e : Option Ty} : ErgExpr D Γ Λ e → Option Nat
  | .wert x => x.varUnten?
  | .keine => Option.none

theorem ergVarUnten_eval {Γ : Ctx} {Λ : List (Res D)} {e : Option Ty} (x : ErgExpr D Γ Λ e) {b : Nat}
    (h : x.varUnten? = some b) (σ0 σ : World D) (ρ : Env D Γ) :
    ergInt e (evalErg σ0 x σ ρ) = ρ.unten b := by
  cases x with
  | keine => simp [ErgExpr.varUnten?] at h
  | wert ex => exact varUnten_eval ex h σ0 σ ρ

/-- **A re-view keeps the object** (the borrow rule `R014` assumes, now a theorem of the
    model). For every program and every function `f` whose body is `return k;` with `k` a
    bare parameter at bottom position `b` -- the shape of a re-view at one table in the
    encoding -- every completed call answers the integer `ρ` holds at `b`: the answer names
    the SAME object as the argument. -/
theorem umsicht_behaelt (P : Programm D) (O : Orakel D) (passes n : Nat) (f : D.Fn)
    (x : ErgExpr D (D.params f) (Signatur.anfang D (D.signatur f)) (vertragVon D f).erg)
    (hΛ : (Signatur.anfang D (D.signatur f)).Perm (vertragVon D f).ende)
    (hr : P.rumpf f = .ret x hΛ) {b : Nat} (hx : x.varUnten? = some b)
    (σ : World D) (ρ : Env D (D.params f)) (σ' : World D) (v : ErgVal D (D.erg f))
    (h : rufAt P O passes (n + 1) f σ ρ = .ok σ' v) : ergInt (D.erg f) v = ρ.unten b := by
  simp only [rufAt] at h
  rw [hr] at h
  simp only [execEnd] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · cases h
        exact ergVarUnten_eval x hx _ _ ρ

#print axioms Gabbro.Grammatik.stmt_obj
#print axioms Gabbro.Grammatik.block_obj
#print axioms Gabbro.Grammatik.end_obj
#print axioms Gabbro.Grammatik.rufAt_obj
#print axioms Gabbro.Grammatik.obj_ruf_rahmen
#print axioms Gabbro.Grammatik.umsicht_behaelt

#print axioms Gabbro.Grammatik.evalArgs_unten
#print axioms Gabbro.Grammatik.traverseLauf_obj

end Gabbro.Grammatik
