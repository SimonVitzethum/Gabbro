/-
  File:      Grammatik/Logik/Vertraege/Objekte.lean
  Subject:   **OBJECTS BELOW A TABLE** -- `own`/separation, slice 2b (Simon's decision of
             2026-10-17: "the Lean model gets finer objects below a table";
             `dokumente/A1-OWN-PAPER.md` section 6, slice 2b).

  WHY. Slice 2 (`Getrennt.lean`) separates CARRIERS: in machine G a pointer type
  `Ty.ptr n rw` names its table in the TYPE and a pointer value is `Unit`, so two
  parameters of one table type are one carrier whatever their roots, and the checker's
  rule `R014` (distinct ROOTS, `m3.rs::getrennte_wurzeln`) had no model statement.

  THE CHOICE: AN OBJECT IS A SLOT. `Obj D` is a pair (carrier `tab`, identity `nr`), and
  it covers exactly the slot `nr` of `tab` -- all fields of it. Why this granularity and
  no other:
    * the world of machine G is ALREADY indexed this way (`World.slots t k f`), so the
      object layer needs no second memory, no new world and no change to G: every
      theorem about G reads the same `World`;
    * a slot is what a record pointer into a table names in the source (one record),
      and every slot store of G (`assignSlot`, `assignDurch`, `uebergang`) writes exactly
      one field of exactly one slot -- so "a store through `k` writes `k`'s object" has a
      statement;
    * a field would be FINER than what a record pointer names (two pointers to one
      record are one object), and a whole table is slice 2's reading -- the special case
      of one object per carrier (`objGetrennt_ein_obj_iff`, a theorem below).
    A record INSIDE a slot (a sub-record of a slot's fields) is not carried: G's fields
    are flat (`D.Feld t`) and no G form addresses a part of a slot.

  HOW A POINTER VALUE NAMES ONE OBJECT, WITHOUT CHANGING G. G has no pointer value that
  carries an identity, and this file adds none. A pointer to one object is the PAIR of
  parameters G already has: the capability `ptr n rw` (the right to address table
  `D.tabNr n`) and an index `index (D.count t)` (which slot). The identity is a VALUE,
  chosen by the CALLER -- exactly what the type alone could not say. `ObjPar` names such
  a pair by the position of its index parameter, counted from the BOTTOM of the context
  (`Var.unten`), so that it stays the same under every `let` a body pushes above it.

  WHAT IS PROVED (generic: every declaration, every program, every world):
    * `ObjGetrenntL` (the argument-to-object map is injective on every pair with a
      writable or `own` side), `objGetrennt_paarweise`, and
      `objGetrennt_schreiben_trennt`: a store into the object of one such parameter
      leaves every field of the object of the other.
    * `objGetrennt_ein_obj_iff`: with ONE object per carrier, `ObjGetrennt` IS slice 2's
      `ParamGetrennt`; `getrennt_objGetrennt`: carrier separation implies object
      separation for every map whose objects lie in the carriers the types name.
    The frame at the model's call is `ObjektRahmen.lean`, the roots `ObjektWurzel.lean`.
-/
import Grammatik.Logik.Vertraege.Getrennt

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Objects -/

/-- **An object below a table**: the carrier `tab` and the identity `nr` -- the slot `nr`
    of `tab`, all of its fields. -/
structure Obj (D : Deklaration) where
  tab : D.Tab
  nr : Int

theorem Obj.ext' {o o' : Obj D} (ht : o.tab = o'.tab) (hn : o.nr = o'.nr) : o = o' := by
  cases o; cases o'; simp only at ht hn; subst ht; subst hn; rfl

/-- A store into one slot leaves every field of every OTHER slot of the same table. -/
theorem storeSlot_anderer_slot (σ : World D) (t : D.Tab) (k : Int) (f : D.Feld t)
    (v : Wert D (D.typ t f)) (k' : Int) (hk : k' ≠ k) (f' : D.Feld t) :
    (σ.storeSlot t k f v).slots t k' f' = σ.slots t k' f' := by
  simp only [World.storeSlot, ↓reduceDIte, hk, ↓reduceIte]

/-- **A store into object `o` leaves every field of every other object `o'`.** -/
theorem storeObj_andere (σ : World D) (o : Obj D) (f : D.Feld o.tab) (v : Wert D (D.typ o.tab f))
    (o' : Obj D) (h : o' ≠ o) (f' : D.Feld o'.tab) :
    (σ.storeSlot o.tab o.nr f v).slots o'.tab o'.nr f' = σ.slots o'.tab o'.nr f' := by
  obtain ⟨t, k⟩ := o
  obtain ⟨t', k'⟩ := o'
  simp only at f v f' ⊢
  by_cases ht : t' = t
  · subst ht
    have hk : k' ≠ k := fun hk => h (by subst hk; rfl)
    exact storeSlot_anderer_slot σ t' k f v k' hk f'
  · exact storeSlot_andere σ t k f v t' ht k' f'

/-! ## 2. `ObjGetrennt` -- the predicate on a call frame -/

/-- **Object separation of a call frame**: `a i` is the object the `i`-th pointer argument
    names (`none`: no object), `w i` whether separation matters for it (writable or `own`).
    For every pair of different positions with a writable side, the objects differ. Two
    read-only positions are free -- the paper's S-1, now at the granularity of objects. -/
def ObjGetrenntL {n : Nat} (w : Fin n → Bool) (a : Fin n → Option (Obj D)) : Prop :=
  ∀ i j, i ≠ j → (w i || w j) = true → a i = none ∨ a i ≠ a j

/-- Under `ObjGetrennt` two different positions with a writable side name different objects. -/
theorem objGetrennt_paarweise {n : Nat} {w : Fin n → Bool} {a : Fin n → Option (Obj D)}
    (hG : ObjGetrenntL w a) (i j : Fin n) (hij : i ≠ j) (hz : (w i || w j) = true)
    {o o' : Obj D} (ho : a i = some o) (ho' : a j = some o') : o ≠ o' := by
  intro h
  rcases hG i j hij hz with h1 | h1
  · rw [ho] at h1; cases h1
  · exact h1 (by rw [ho, ho', h])

/-- **A store through the one leaves the object of the other**: under `ObjGetrennt`, a slot
    store into the object of position `i` changes no field of the object of position `j`. -/
theorem objGetrennt_schreiben_trennt {n : Nat} {w : Fin n → Bool} {a : Fin n → Option (Obj D)}
    (hG : ObjGetrenntL w a) (i j : Fin n) (hij : i ≠ j) (hz : (w i || w j) = true)
    {o o' : Obj D} (ho : a i = some o) (ho' : a j = some o')
    (σ : World D) (f : D.Feld o.tab) (v : Wert D (D.typ o.tab f)) (f' : D.Feld o'.tab) :
    (σ.storeSlot o.tab o.nr f v).slots o'.tab o'.nr f' = σ.slots o'.tab o'.nr f' :=
  storeObj_andere σ o f v o' (fun h => objGetrennt_paarweise hG i j hij hz ho ho' h.symm) f'

/-- Two positions naming ONE object, one of them writable, are not separated -- the shape
    of a re-view passed together with its source (the borrow rule, `ObjektRahmen.lean`). -/
theorem objGetrennt_nicht_bei_einem {n : Nat} {w : Fin n → Bool} {a : Fin n → Option (Obj D)}
    (i j : Fin n) (hij : i ≠ j) (hz : (w i || w j) = true) {o : Obj D}
    (ho : a i = some o) (ho' : a j = some o) : ¬ ObjGetrenntL w a :=
  fun hG => objGetrennt_paarweise hG i j hij hz ho ho' rfl

/-! ## 3. Slice 2 is the case of one object per carrier -/

/-- The writable flags of a parameter list, as slice 2 reads them. -/
def wVon (ps : List Ty) : Fin ps.length → Bool := fun i => zaehltFuerTrennung (ps.get i)

/-- **One object per carrier**: every pointer parameter names the object `0` of the table
    its type names -- what machine G's pointer (`Unit`, the capability over the whole
    table) is at this granularity. -/
def einObj (D : Deklaration) (ps : List Ty) : Fin ps.length → Option (Obj D) :=
  fun i => (traegerVon D (ps.get i)).map fun t => ⟨t, 0⟩

theorem einObj_inj {a b : Option D.Tab} :
    a.map (fun t => (⟨t, 0⟩ : Obj D)) = b.map (fun t => (⟨t, 0⟩ : Obj D)) ↔ a = b := by
  cases a <;> cases b <;> simp only [Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq, Obj.mk.injEq, and_true]

/-- **`ParamGetrennt` (slice 2) is `ObjGetrennt` with one object per carrier.** -/
theorem objGetrennt_ein_obj_iff (ps : List Ty) :
    ObjGetrenntL (wVon ps) (einObj D ps) ↔ ParamGetrenntL D ps := by
  constructor
  · intro h i j hij hz
    rcases h i j hij hz with h1 | h1
    · left
      cases ht : traegerVon D (ps.get i) with
      | none => rfl
      | some t => simp only [einObj] at h1; rw [ht] at h1; cases h1
    · right
      intro h2
      exact h1 (by simp only [einObj]; rw [h2])
  · intro h i j hij hz
    rcases h i j hij hz with h1 | h1
    · left; simp only [einObj]; rw [h1]; rfl
    · right
      intro h2
      exact h1 (einObj_inj.mp h2)

/-- **Carrier separation implies object separation**: for every argument-to-object map
    whose objects lie in the carriers the parameter types name (`hin`), slice 2's
    `ParamGetrennt` gives `ObjGetrennt`. The converse is false -- two objects of one table
    (`ObjektZeuge.lean`, `zeuge_obj_feiner`). -/
theorem getrennt_objGetrennt {ps : List Ty} (hG : ParamGetrenntL D ps)
    (a : Fin ps.length → Option (Obj D))
    (hin : ∀ i o, a i = some o → traegerVon D (ps.get i) = some o.tab) :
    ObjGetrenntL (wVon ps) a := by
  intro i j hij hz
  cases hai : a i with
  | none => exact .inl rfl
  | some o =>
      right
      intro h
      have hj : a j = some o := h.symm
      have h1 := hin i o hai
      have h2 := hin j o hj
      rcases hG i j hij hz with h3 | h3
      · rw [h1] at h3; cases h3
      · exact h3 (by rw [h1, h2])

#print axioms Gabbro.Grammatik.storeObj_andere
#print axioms Gabbro.Grammatik.objGetrennt_paarweise
#print axioms Gabbro.Grammatik.objGetrennt_schreiben_trennt
#print axioms Gabbro.Grammatik.objGetrennt_nicht_bei_einem
#print axioms Gabbro.Grammatik.objGetrennt_ein_obj_iff
#print axioms Gabbro.Grammatik.getrennt_objGetrennt

end Gabbro.Grammatik
