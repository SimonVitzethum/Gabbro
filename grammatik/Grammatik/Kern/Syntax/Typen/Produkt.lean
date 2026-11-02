module

public import Grammatik.Kern.Syntax.Typen.Teil1

@[expose] public section

/-
  File:       Grammatik/Kern/Syntax/Typen/Produkt.lean
  Subject:    C01, typed PRODUCTS (records) as values: the nominal product `Ty.prod`, the typed field
              position `FieldAt`, and get/replace of a field on a value with its frame lemmas.

  A product is the nominal wrapper `Ty.prod name fs` over its ordered field types `fs : List Ty`.
  `Val F passt (.prod _ fs) = ProdVal F passt fs`, the heterogeneous tuple of the field values in
  declaration order; the empty product has one value (`()`). `FieldAt` is proof-relevant and typed,
  so a projection or a replacement needs no cast. Elaboration resolves a field name to such a
  position; there are no runtime field names.
-/

namespace Gabbro.Grammatik

/-- The nominal product `name` with the given field types. -/
def Ty.prodOf (name : Nat) (fs : List Ty) : Ty := .prod name fs

/-- The position of one field `σ` in the field list `fs`: `head` is the first field, `tail` skips one. -/
inductive FieldAt : List Ty → Ty → Type where
  | head {σ : Ty} {rest : List Ty} : FieldAt (σ :: rest) σ
  | tail {σ τ : Ty} {rest : List Ty} : FieldAt rest σ → FieldAt (τ :: rest) σ

/-- Two distinct field positions of one field list (they never name the same field). -/
inductive FieldAt.Disj : {fs : List Ty} → {σ τ : Ty} → FieldAt fs σ → FieldAt fs τ → Prop where
  | headTail {σ τ : Ty} {rest : List Ty} (j : FieldAt rest τ) :
      FieldAt.Disj (FieldAt.head : FieldAt (σ :: rest) σ)
        (FieldAt.tail j : FieldAt (σ :: rest) τ)
  | tailHead {σ τ : Ty} {rest : List Ty} (i : FieldAt rest σ) :
      FieldAt.Disj (FieldAt.tail i : FieldAt (τ :: rest) σ)
        (FieldAt.head : FieldAt (τ :: rest) τ)
  | tailTail {σ τ ρ : Ty} {rest : List Ty} {i : FieldAt rest σ} {j : FieldAt rest τ} :
      FieldAt.Disj i j →
      FieldAt.Disj (FieldAt.tail i : FieldAt (ρ :: rest) σ)
        (FieldAt.tail j : FieldAt (ρ :: rest) τ)

section Werte

variable {F : Type} {passt : F → Nat → Bool}

/-- The value of a field list from its first field and the value of the rest. -/
def ProdVal.pcons {τ : Ty} {rest : List Ty} (a : Val F passt τ) (b : ProdVal F passt rest) :
    ProdVal F passt (τ :: rest) := (a, b)

/-- The first field of a non-empty field-list value. -/
def ProdVal.hd {τ : Ty} {rest : List Ty} (v : ProdVal F passt (τ :: rest)) : Val F passt τ :=
  Prod.fst v

/-- The rest of a non-empty field-list value. -/
def ProdVal.tl {τ : Ty} {rest : List Ty} (v : ProdVal F passt (τ :: rest)) :
    ProdVal F passt rest := Prod.snd v

@[simp] theorem ProdVal.hd_pcons {τ : Ty} {rest : List Ty} (a : Val F passt τ)
    (b : ProdVal F passt rest) : ProdVal.hd (ProdVal.pcons a b) = a := rfl

@[simp] theorem ProdVal.tl_pcons {τ : Ty} {rest : List Ty} (a : Val F passt τ)
    (b : ProdVal F passt rest) : ProdVal.tl (ProdVal.pcons a b) = b := rfl

theorem ProdVal.pcons_hd_tl {τ : Ty} {rest : List Ty} (v : ProdVal F passt (τ :: rest)) :
    ProdVal.pcons (ProdVal.hd v) (ProdVal.tl v) = v := rfl

theorem ProdVal.pcons_congr {τ : Ty} {rest : List Ty} {a a' : Val F passt τ}
    {b b' : ProdVal F passt rest} (ha : a = a') (hb : b = b') :
    ProdVal.pcons a b = ProdVal.pcons a' b' := by
  subst ha
  subst hb
  rfl

/-- The field at a position of a product value. -/
def prodGetW : {fs : List Ty} → {σ : Ty} → FieldAt fs σ → ProdVal F passt fs → Val F passt σ
  | _, _, .head, v => ProdVal.hd v
  | _, _, .tail i, v => prodGetW i (ProdVal.tl v)

/-- The product value with the field at a position replaced; every other field stays. -/
def prodSetW : {fs : List Ty} → {σ : Ty} → FieldAt fs σ → ProdVal F passt fs →
    Val F passt σ → ProdVal F passt fs
  | _, _, .head, v, x => ProdVal.pcons x (ProdVal.tl v)
  | _, _, .tail i, v, x => ProdVal.pcons (ProdVal.hd v) (prodSetW i (ProdVal.tl v) x)

/-- Get after set: the replaced field reads back the new value. -/
theorem prodGetW_prodSetW :
    ∀ {fs : List Ty} {σ : Ty} (i : FieldAt fs σ) (v : ProdVal F passt fs) (x : Val F passt σ),
      prodGetW i (prodSetW i v x) = x
  | _, _, .head, _, _ => rfl
  | _, _, .tail i, v, x => prodGetW_prodSetW i (ProdVal.tl v) x

/-- Frame: replacing one field leaves every other field of the product unchanged. -/
theorem prodGetW_prodSetW_of_disj :
    ∀ {fs : List Ty} {σ τ : Ty} {i : FieldAt fs σ} {j : FieldAt fs τ}, FieldAt.Disj i j →
      ∀ (v : ProdVal F passt fs) (x : Val F passt σ),
        prodGetW j (prodSetW i v x) = prodGetW j v
  | _, _, _, _, _, .headTail _, _, _ => rfl
  | _, _, _, _, _, .tailHead _, _, _ => rfl
  | _, _, _, _, _, .tailTail h, v, x => prodGetW_prodSetW_of_disj h (ProdVal.tl v) x

/-- Setting a field to the value it already has changes nothing. -/
theorem prodSetW_prodGetW :
    ∀ {fs : List Ty} {σ : Ty} (i : FieldAt fs σ) (v : ProdVal F passt fs),
      prodSetW i v (prodGetW i v) = v
  | _, _, .head, _ => rfl
  | _, _, .tail i, v => by
      have h := prodSetW_prodGetW i (ProdVal.tl v)
      show ProdVal.pcons (ProdVal.hd v) (prodSetW i (ProdVal.tl v) (prodGetW i (ProdVal.tl v))) = v
      exact (congrArg (ProdVal.pcons (ProdVal.hd v)) h).trans (ProdVal.pcons_hd_tl v)

/-- **Extensionality**: two values of a field list that agree at every field are equal. -/
theorem ProdVal.prod_ext :
    ∀ {fs : List Ty} (v w : ProdVal F passt fs),
      (∀ {σ : Ty} (i : FieldAt fs σ), prodGetW i v = prodGetW i w) → v = w
  | [], _, _, _ => rfl
  | _ :: _, v, w, hx => by
      have h1 : ProdVal.hd v = ProdVal.hd w := hx FieldAt.head
      have h2 : ProdVal.tl v = ProdVal.tl w :=
        ProdVal.prod_ext (ProdVal.tl v) (ProdVal.tl w) (fun i => hx (FieldAt.tail i))
      calc v = ProdVal.pcons (ProdVal.hd v) (ProdVal.tl v) := rfl
        _ = ProdVal.pcons (ProdVal.hd w) (ProdVal.tl w) := by rw [h1, h2]
        _ = w := rfl

end Werte

end Gabbro.Grammatik
