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
  | _ :: Γ, _, .here => Γ.length
  | _ :: _, _, .there x => x.unten

theorem Var.unten_lt : ∀ {Γ : Ctx} {τ : Ty} (x : Var Γ τ), x.unten < Γ.length
  | _ :: _, _, .here => by simp only [unten, List.length_cons, Nat.lt_add_one]
  | _ :: _, _, .there x => by have := Var.unten_lt x; simp only [Var.unten, List.length_cons]; omega

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
  | _, .nil, _, _, h => by simp only [unten, reduceCtorEq] at h
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
  | _ :: Γ, _, .cons v ρ, .here => by simp only [unten, Var.unten, ↓reduceIte, get]
  | _ :: _, _, .cons _ ρ, .there x => by
      simp only [Env.unten, Var.unten, Env.get]
      rw [if_neg (by have := Var.unten_lt x; omega)]
      exact Env.unten_get ρ x

theorem Env.unten_set : ∀ {Γ : Ctx} {τ : Ty} (ρ : Env D Γ) (x : Var Γ τ) (v : Wert D τ) {j : Nat},
    j ≠ x.unten → (ρ.set x v).unten j = ρ.unten j
  | _ :: _, _, .cons _ _, .here, _, _, h => by
      simp only [Env.set, Env.unten, Var.unten] at h ⊢; rw [if_neg h, if_neg h]
  | _ :: Γ, _, .cons _ ρ, .there x, v, j, h => by
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
  | .assignThru _ t _ _ i _ _ _ => SchreibOk ps t i
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
  | .locks _ _ body => oB body
  | .breaking _ body => oB body
  | .traverse _ _ body => oB body
  | .retry _ _ body ueber => oB body ∧ oB ueber
  | .forever _ _ body => oB body
  | .axiomCall a .. => KeinTabAx a
  | .regWrite .. => True
  | .transition .. => True
  | .publish .. => True
  | .advances .. => True
  | .retires .. => True
  | .ret .. => True
  | .retWhy .. => True
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
  | .regRead _ _ rest => oB rest
  | .regReadElse _ _ _ sonst rest => oE sonst ∧ oB rest
  | .awaits _ _ _ _ _ rest => oB rest
  | .exchange _ _ _ _ rest => oB rest
  | .narrow _ _ _ sonst rest => oE sonst ∧ oB rest
  | .check _ sonst rest => oE sonst ∧ oB rest
  | .float _ _ _ _ _ rest => oB rest
  | .floatLit _ _ _ rest => oB rest
  | .floatOf _ _ _ rest => oB rest
  | .floatNarrow _ _ _ sonst rest => oE sonst ∧ oB rest

def oE {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} : Endblock D V l Γ Λ → Prop
  | .ret .. => True
  | .retWhy .. => True
  | .leave _ => True
  | .next _ => True
  | .cons s rest => oS s ∧ oE rest
  | .bind _ rest => oE rest
  | .bindCall f args _ _ _ rest => ObjRufOk objs ps f args ∧ oE rest
  | .bindCallElse f args _ _ _ err rest => ObjRufOk objs ps f args ∧ oE err ∧ oE rest
  | .bindAxiom a _ _ _ _ _ _ rest => KeinTabAx a ∧ oE rest
  | .bindAxiomElse a _ _ _ _ _ _ _ err rest => KeinTabAx a ∧ oE err ∧ oE rest
  | .regRead _ _ rest => oE rest
  | .regReadElse _ _ _ sonst rest => oE sonst ∧ oE rest
  | .awaits _ _ _ _ _ rest => oE rest
  | .bindCallInd .. => False
  | .narrow _ _ _ sonst rest => oE sonst ∧ oE rest
  | .exchange _ _ _ _ rest => oE rest
  | .ite _ t e => oE t ∧ oE e

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


end Gabbro.Grammatik
