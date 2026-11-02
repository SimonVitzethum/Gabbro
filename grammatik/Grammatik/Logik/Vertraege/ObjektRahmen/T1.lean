/-
  File:      Grammatik/Logik/Vertraege/ObjektRahmen.lean
  Subject:   **THE FRAME OVER OBJECTS AT THE MODEL'S CALL** -- `own`/separation slice 2b,
             the run half of `Objekte.lean`.

  THE ENCODING (no change to machine G). A pointer to ONE object of table `t` is a pair of
  parameters G already has: the capability `ptr n rw` with `D.tabNr n = some t` and an
  index `index (D.count t)`. `ObjPar` names such a pair: `idx` (the index parameter),
  `cap` (the capability), both counted from the BOTTOM of the context (`Var.unten`), so a
  position stays the same under every `let` a body pushes; `rw` is the right of the
  capability's ordinary write flag. Exclusive owner rights are refused by the Lean exporter
  until checked ownership flow is connected. In an environment `ρ`
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
module
public import Grammatik.Logik.Vertraege.Objekte
@[expose] public section


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
    capability at bottom position `cap`, on table `tab`, with ordinary write flag `rw`. -/
structure ObjPar (D : Deklaration) where
  idx : Nat
  cap : Nat
  tab : D.Tab
  rw : Bool
  read : Bool := true
  space : Nat := 0
  owner : Option Nat := none

/-- The pair is faithful to the context: the index has the generated index type of its
    table, and the capability is a pointer to that table with the pair's right. -/
def ObjParTreu (D : Deklaration) (Γ : Ctx) (op : ObjPar D) : Prop :=
  Γ.reverse[op.idx]? = some (.index (D.count op.tab)) ∧
    ∃ n, Γ.reverse[op.cap]? = some (.ptr ⟨op.space, ⟨op.read, op.rw, op.owner⟩, .table n⟩) ∧ D.tabNr n = some op.tab

/-- The object the pair names in an environment: its table, at the value of its index. -/
def ObjPar.obj {Γ : Ctx} (op : ObjPar D) (ρ : Env D Γ) : Option (Obj D) :=
  (ρ.unten op.idx).map fun k => ⟨op.tab, k⟩

/-- The argument-to-object map of a call frame. -/
def objVon {Γ : Ctx} (ps : List (ObjPar D)) (ρ : Env D Γ) : Fin ps.length → Option (Obj D) :=
  fun i => (ps.get i).obj ρ

/-- Which object parameters count for separation. -/
def rwVon (ps : List (ObjPar D)) : Fin ps.length → Bool := fun i => (ps.get i).rw

/-- **`ObjGetrennt` on a call frame**: the objects the writable parameters name differ
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

theorem LenOk.arm {ps : List (ObjPar D)} {Γ : Ctx} (h : LenOk ps Γ) (c : Option Ty) :
    LenOk ps (ArmCtx Γ c) := by
  cases c with
  | none => exact h
  | some p => exact h.cons _

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
    {c : Option Ty} (nutz : Nutzlast D.Fn D.passt c) : ObjInv W ps (armEnv nutz ρ) := by
  cases c with
  | none => exact h
  | some p => exact h.cons hlen _

end Inv

end Gabbro.Grammatik
