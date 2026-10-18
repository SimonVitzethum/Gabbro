import Grammatik.Kern.Semantik.Semantik
import Grammatik.Code.Model.Facts
import Grammatik.Code.Model.Layout
import Grammatik.Code.Lower.Arith

/-
  File:      Grammatik/Code/Lower/Rep.lean
  Subject:   TRACK L, PHASE L1 -- THE REPRESENTATION RELATION between machine G's world and the
             IR's memory, and the layout assumptions it rests on.

  G's `World` holds, per table, slot index and field, a value of the declared type, and per
  global one value. The IR holds blocks of bytes. The relation `Rep lay σ m` says: the
  table `t` is the global block `gblk t` laid out as `[count x R]` for a record `R`, field `f`
  of slot `k` sits at the offset `gep [count x R], 0, k, fidx f` computes, and the bytes there
  decode to the encoding of `σ.slots t k f`; a global `g` is the cell of block `ggblk g`.
  Locals live in `alloc` blocks, one per variable of the context (`EnvRep`).

  THE CORRESPONDENCE ASSUMPTIONS, as hypotheses and not axioms (the structure `LayoutOk`):
    * the global of a table has type `[count x R]`, and every SUPPORTED field of `R` (an integer
      range that fits 128 bits, a `bool`, a pointer) has the memory type `memTy` at the position
      `fidx` (`Ty.fieldOff`), different fields at different positions;
    * different tables and globals are different blocks.
  The widths are `Ar.wid`; the trace (`World.spur`) has no image in the IR and is ignored.
-/

namespace Gabbro.Code.Lower

open Gabbro.Grammatik (Deklaration World Env Wert Zahl Ctx Var)

abbrev GTy := Gabbro.Grammatik.Ty

variable [Conf]

/-- The types the L1 lowering carries: ranges that fit 128 bits, `bool`, table pointers. -/
def supp : GTy → Bool
  | .int lo hi => decide (Ar.Fits lo hi 128)
  | .bool => true
  | .ptr _ _ => true
  | .opt n => decide (Ar.Fits (-1) (n - 1) 128)
  | .why n => decide (Ar.Fits 0 ((n : Int) - 1) 128)
  | _ => false

/-- The register type. An `opt n` is the integer `-1` (absent) or the index, in `-1 .. n - 1`; a
    `why n` is the number of the reason, in `0 .. n - 1`. -/
def regTy : GTy → Ty
  | .int lo hi => .int (Ar.wid lo hi)
  | .bool => .int 1
  | .ptr _ _ => .ptr
  | .opt n => .int (Ar.wid (-1) (n - 1))
  | .why n => .int (Ar.wid 0 ((n : Int) - 1))
  | _ => .void

/-- The memory type (a `bool` is a byte in memory). -/
def memTy : GTy → Ty
  | .bool => .int 8
  | τ => regTy τ

theorem memTy_scalar {τ : GTy} (h : supp τ = true) : (memTy τ).scalar = true := by
  cases τ <;> simp_all [supp, memTy, regTy, Ty.scalar]

/-- Where everything lives. -/
structure Layout (D : Deklaration) where
  gblk : D.Tab → Nat
  tty : D.Tab → Ty
  rty : D.Tab → Ty
  fidx : (t : D.Tab) → D.Feld t → Nat
  ggblk : D.Glob → Nat
  /-- The number of the IR function that is function `f` of the program. -/
  fno : D.Fn → Nat

/-- The assumptions about the layout. -/
structure LayoutOk {D : Deklaration} (lay : Layout D) : Prop where
  tab : ∀ t, lay.tty t = .arr (D.count t).toNat (lay.rty t)
  fld : ∀ t f, supp (D.typ t f) = true →
    ∃ off, Ty.fieldOff (lay.rty t) (lay.fidx t f) 0 = some (off, memTy (D.typ t f))
  inj : ∀ t (f g : D.Feld t), supp (D.typ t f) = true → supp (D.typ t g) = true →
    lay.fidx t f = lay.fidx t g → f = g
  tinj : ∀ t u, lay.gblk t = lay.gblk u → t = u
  gdis : ∀ t g, lay.gblk t ≠ lay.ggblk g
  ginj : ∀ g h, lay.ggblk g = lay.ggblk h → g = h
  /-- field positions stay far below the signed word range -/
  fsm : ∀ t f, lay.fidx t f < 2 ^ (Conf.wbits - 2)

variable {D : Deklaration}

/-- The byte offset of field `f` of slot `k` of table `t` in its global. -/
def Layout.off (lay : Layout D) (t : D.Tab) (k : Int) (f : D.Feld t) : Int :=
  (((lay.tty t).gepOff [0, k, (lay.fidx t f : Int)]).map (·.1)).getD 0

theorem Layout.off_eq {lay : Layout D} (hL : LayoutOk lay) (t : D.Tab) (k : Int) (f : D.Feld t)
    (hs : supp (D.typ t f) = true) :
    ∃ fo : Nat, lay.off t k f = k * ((lay.rty t).size : Int) + (fo : Int) ∧
      Ty.fieldOff (lay.rty t) (lay.fidx t f) 0 = some (fo, memTy (D.typ t f)) := by
  obtain ⟨fo, h⟩ := hL.fld t f hs
  refine ⟨fo, ?_, h⟩
  unfold Layout.off
  rw [hL.tab t, Ty.gepOff_slot _ _ k _ fo _ h]
  rfl

theorem Layout.gep_eq {lay : Layout D} (hL : LayoutOk lay) (t : D.Tab) (k : Int) (f : D.Feld t)
    (hs : supp (D.typ t f) = true) :
    ∃ ty, (lay.tty t).gepOff [0, k, (lay.fidx t f : Int)] = some (lay.off t k f, ty) := by
  obtain ⟨fo, h⟩ := hL.fld t f hs
  have := Ty.gepOff_slot (D.count t).toNat (lay.rty t) k _ fo _ h
  refine ⟨memTy (D.typ t f), ?_⟩
  unfold Layout.off
  rw [hL.tab t, this]
  rfl

/-- A G boolean as a Lean `Bool`. -/
def wbool (v : Wert D .bool) : Bool := v

/-- The image of a value in a register. -/
def encR (lay : Layout D) : (τ : GTy) → Wert D τ → Val
  | .int lo hi, v => Val.ofInt (Ar.wid lo hi) v.n
  | .bool, b => Val.bool b
  | .ptr n _, _ => match D.tabNr n with
      | some t => .ptr (lay.gblk t) 0
      | none => .ptr nullBlk 0
  | .opt n, v => Val.ofInt (Ar.wid (-1) (n - 1)) (Gabbro.Grammatik.roh v)
  | .why n, v => Val.ofInt (Ar.wid 0 ((n : Int) - 1)) (Gabbro.Grammatik.roh v)
  | _, _ => Val.ofInt 1 0

/-- The image of a value in memory. -/
def encM (lay : Layout D) : (τ : GTy) → Wert D τ → Val
  | .bool, b => Val.ofInt 8 (if wbool b then 1 else 0)
  | τ, v => encR lay τ v

theorem encM_ty (lay : Layout D) {τ : GTy} (v : Wert D τ) (h : supp τ = true) :
    (encM lay τ v).ty = memTy τ := by
  cases τ <;> simp_all [supp, encM, encR, memTy, regTy, Val.ty, Val.ofInt, Val.bool]
  rename_i n rw
  cases D.tabNr n <;> simp [Val.ty]

theorem dec_enc_encM (lay : Layout D) {τ : GTy} (v : Wert D τ) (h : supp τ = true) :
    Ty.dec (memTy τ) (Val.enc (encM lay τ v)) = some (encM lay τ v) := by
  cases τ with
  | int lo hi => exact dec_enc_int _ _
  | bool => exact dec_enc_int _ _
  | ptr n rw =>
      simp only [memTy, regTy, encM, encR]
      cases D.tabNr n <;> exact dec_enc_ptr _ _
  | opt n => exact dec_enc_int _ _
  | why n => exact dec_enc_int _ _
  | _ => simp [supp] at h

/-! ## The world in memory -/

/-- Table slots and globals of `σ` are in the memory `m`. -/
def Rep (lay : Layout D) (σ : World D) (m : Mem) : Prop :=
  (∀ t (k : Int) (f : D.Feld t), supp (D.typ t f) = true → 0 ≤ k → k < D.count t →
      m.load (lay.gblk t) (lay.off t k f) (memTy (D.typ t f))
        = some (encM lay (D.typ t f) (σ.slots t k f))) ∧
  (∀ g, supp (D.gtyp g) = true →
      m.load (lay.ggblk g) 0 (memTy (D.gtyp g)) = some (encM lay (D.gtyp g) (σ.globs g)))

theorem load_blk_lt {m : Mem} (hw : m.Wf) {b : Nat} {o : Int} {t : Ty} {v : Val}
    (h : m.load b o t = some v) : b < m.next := by
  apply hw
  unfold Mem.load at h
  cases hb : m.blks b with
  | none => simp [hb] at h
  | some _ => rfl

/-- Two different fields (or slots) of one table do not overlap. -/
theorem Layout.off_disj {lay : Layout D} (hL : LayoutOk lay) (t : D.Tab) (k k' : Int)
    (f f' : D.Feld t) (hs : supp (D.typ t f) = true) (hs' : supp (D.typ t f') = true)
    (hk : 0 ≤ k) (hk' : 0 ≤ k') (hne : k ≠ k' ∨ f ≠ f') :
    lay.off t k f + ((memTy (D.typ t f)).store : Int) ≤ lay.off t k' f' ∨
    lay.off t k' f' + ((memTy (D.typ t f')).store : Int) ≤ lay.off t k f := by
  obtain ⟨fo, e1, h1⟩ := Layout.off_eq hL t k f hs
  obtain ⟨fo', e2, h2⟩ := Layout.off_eq hL t k' f' hs'
  have sz : ∀ i o (ty : Ty), Ty.fieldOff (lay.rty t) i 0 = some (o, ty) →
      o + ty.size ≤ (lay.rty t).size := by
    intro i o ty h
    cases hr : lay.rty t with
    | fld a b => rw [hr] at h; exact Ty.field_in_size a b i o ty h
    | _ => rw [hr] at h; simp [Ty.fieldOff] at h
  have s1 := sz _ _ _ h1
  have s2 := sz _ _ _ h2
  have st1 := Ty.store_le_size _ (memTy_scalar hs)
  have st2 := Ty.store_le_size _ (memTy_scalar hs')
  rw [e1, e2]
  rcases Int.lt_trichotomy k k' with hlt | heq | hgt
  · left
    have := Int.mul_le_mul_of_nonneg_right (show k + 1 ≤ k' by omega)
      (Int.natCast_nonneg (lay.rty t).size)
    rw [Int.add_mul] at this
    omega
  · subst heq
    have hf : f ≠ f' := by
      rcases hne with h | h
      · exact absurd rfl h
      · exact h
    have hi : lay.fidx t f ≠ lay.fidx t f' := fun h => hf (hL.inj t f f' hs hs' h)
    rcases Nat.lt_or_gt_of_ne hi with hlt | hgt
    · left
      have := Ty.fieldOff_disj _ _ _ 0 _ _ _ _ hlt h1 h2
      omega
    · right
      have := Ty.fieldOff_disj _ _ _ 0 _ _ _ _ hgt h2 h1
      omega
  · right
    have := Int.mul_le_mul_of_nonneg_right (show k' + 1 ≤ k by omega)
      (Int.natCast_nonneg (lay.rty t).size)
    rw [Int.add_mul] at this
    omega

/-- A store into a block that is no table and no global leaves the world's image alone. -/
theorem rep_store_other {lay : Layout D} {σ : World D} {m m' : Mem} (hR : Rep lay σ m)
    {b : Nat} {o : Int} {t : Ty} {v : Val} (h : m.store b o t v = some m')
    (hb : (∀ t, b ≠ lay.gblk t) ∧ (∀ g, b ≠ lay.ggblk g)) : Rep lay σ m' := by
  refine ⟨fun t' k f hs h0 h1 => ?_, fun g hs => ?_⟩
  · rw [load_store_other h (Or.inl (fun e => hb.1 t' e.symm))]
    exact hR.1 t' k f hs h0 h1
  · rw [load_store_other h (Or.inl (fun e => hb.2 g e.symm))]
    exact hR.2 g hs

/-- Allocation leaves the image alone. -/
theorem rep_alloc {lay : Layout D} {σ : World D} {m : Mem} (hw : m.Wf) (hR : Rep lay σ m)
    (n : Nat) (z : Bool) : Rep lay σ (m.alloc n z).1 := by
  refine ⟨fun t' k f hs h0 h1 => ?_, fun g hs => ?_⟩
  · have := hR.1 t' k f hs h0 h1
    have hlt := load_blk_lt hw this
    rw [alloc_load m n z _ (by omega)]
    exact this
  · have := hR.2 g hs
    have hlt := load_blk_lt hw this
    rw [alloc_load m n z _ (by omega)]
    exact this

/-- A slot store keeps the image: the world after `storeSlot`, the memory after the store. -/
theorem rep_store_slot {lay : Layout D} (hL : LayoutOk lay) {σ : World D} {m m' : Mem}
    (hR : Rep lay σ m) (t : D.Tab) (k : Int) (f : D.Feld t) (v : Wert D (D.typ t f))
    (hs : supp (D.typ t f) = true) (hk0 : 0 ≤ k) (hk1 : k < D.count t)
    (h : m.store (lay.gblk t) (lay.off t k f) (memTy (D.typ t f)) (encM lay _ v) = some m') :
    Rep lay (σ.storeSlot t k f v) m' := by
  refine ⟨fun t' k' f' hs' h0' h1' => ?_, fun g hs' => ?_⟩
  · by_cases ht : t' = t
    · subst ht
      by_cases hkk : k' = k
      · subst hkk
        by_cases hff : f' = f
        · subst hff
          have e : (σ.storeSlot t' k' f' v).slots t' k' f' = v := by simp [World.storeSlot]
          rw [e]
          exact load_store_of h (dec_enc_encM lay v hs)
        · have e : (σ.storeSlot t' k' f v).slots t' k' f' = σ.slots t' k' f' := by
            simp [World.storeSlot, hff]
          rw [e, load_store_other h (Or.inr (by
            rcases Layout.off_disj hL t' k' k' f' f hs' hs h0' h0' (Or.inr hff) with d | d
            · exact Or.inl d
            · exact Or.inr d))]
          exact hR.1 t' k' f' hs' h0' h1'
      · have e : (σ.storeSlot t' k f v).slots t' k' f' = σ.slots t' k' f' := by
          simp [World.storeSlot, hkk]
        rw [e, load_store_other h (Or.inr (by
          rcases Layout.off_disj hL t' k' k f' f hs' hs h0' hk0 (Or.inl hkk) with d | d
          · exact Or.inl d
          · exact Or.inr d))]
        exact hR.1 t' k' f' hs' h0' h1'
    · have e : (σ.storeSlot t k f v).slots t' k' f' = σ.slots t' k' f' := by
        simp [World.storeSlot, ht]
      rw [e, load_store_other h (Or.inl (fun e => ht (hL.tinj _ _ e)))]
      exact hR.1 t' k' f' hs' h0' h1'
  · have e : (σ.storeSlot t k f v).globs g = σ.globs g := rfl
    rw [e, load_store_other h (Or.inl (fun e => hL.gdis t g e.symm))]
    exact hR.2 g hs'

/-- A global store keeps the image. -/
theorem rep_store_glob {lay : Layout D} (hL : LayoutOk lay) {σ : World D} {m m' : Mem}
    (hR : Rep lay σ m) (g : D.Glob) (v : Wert D (D.gtyp g)) (hs : supp (D.gtyp g) = true)
    (h : m.store (lay.ggblk g) 0 (memTy (D.gtyp g)) (encM lay _ v) = some m') :
    Rep lay (σ.storeGlob g v) m' := by
  refine ⟨fun t' k' f' hs' h0' h1' => ?_, fun g' hs' => ?_⟩
  · have e : (σ.storeGlob g v).slots t' k' f' = σ.slots t' k' f' := rfl
    rw [e, load_store_other h (Or.inl (fun e => hL.gdis t' g e))]
    exact hR.1 t' k' f' hs' h0' h1'
  · by_cases hg : g' = g
    · subst hg
      have e : (σ.storeGlob g' v).globs g' = v := by simp [World.storeGlob]
      rw [e]
      exact load_store_of h (dec_enc_encM lay v hs)
    · have e : (σ.storeGlob g v).globs g' = σ.globs g' := by simp [World.storeGlob, hg]
      rw [e,
        load_store_other h (Or.inl (fun e => hg (hL.ginj _ _ e)))]
      exact hR.2 g' hs'

end Gabbro.Code.Lower
