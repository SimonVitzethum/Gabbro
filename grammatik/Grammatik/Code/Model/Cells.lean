import Grammatik.Code.Model.Types
import Grammatik.Bausteine.Gleitkomma.GleitkommaBits

/-
  File:      Grammatik/Code/Model/Cells.lean
  Subject:   TRACK L, PHASE L0 -- THE MEMORY of the IR: BLOCK-STRUCTURED, BYTE-ADDRESSED.

  A pointer is a block and a byte offset (`Val.ptr b o`). Memory is a map from block ids to
  blocks, a block is a size and a map from byte offsets to CELLS, and a cell is a data byte or
  one byte of a stored pointer (a FRAGMENT, as in CompCert: a pointer is stored as eight
  fragments and read back only if all eight are its own). Consequences that are theorems here,
  not conventions:
    * two different allocations never alias (`store_blks_other`, `load_store_other`);
    * a store changes the cells it covers and nothing else (`load_store_other`);
    * a load of what was just stored returns it (`load_store_int`, `load_store_ptr`,
      `load_store_flt`);
    * `alloc` gives a fresh block and leaves every old one as it was (`alloc_load`).
  Reading a cell never written (an `alloc` is uninitialised) or reading outside a block is
  `none`: the semantics gets STUCK, which is the model's word for undefined behaviour.
-/

namespace Gabbro.Code

open Gabbro.Grammatik.Gleitkomma

/-- A cell of memory. -/
inductive Cell where
  | byte (b : Nat)
  /-- Byte number `i` of a stored pointer to block `blk`, offset `off`. -/
  | frag (blk : Nat) (off : Int) (i : Nat)
  deriving DecidableEq

/-- An allocation: its size in bytes and its cells (`none` = never written). -/
structure Blk where
  size : Nat
  cells : Nat → Option Cell

/-- The memory: blocks by id, and the next fresh id. -/
structure Mem where
  blks : Nat → Option Blk
  next : Nat

/-- Every existing block has an id below `next`: a fresh id is really fresh. -/
def Mem.Wf (m : Mem) : Prop := ∀ b, (m.blks b).isSome = true → b < m.next

def Mem.empty : Mem := ⟨fun _ => none, 0⟩

theorem Mem.empty_wf : Mem.empty.Wf := by
  intro b h; simp only [empty, Option.isSome_none, Bool.false_eq_true] at h

/-! ## 1. Cells -/

/-- Write the cells `cs` at offsets `o, o+1, …`. -/
def putCells (f : Nat → Option Cell) (o : Nat) (cs : List Cell) : Nat → Option Cell :=
  fun k => if o ≤ k ∧ k < o + cs.length then cs[k - o]? else f k

/-- Read `n` cells from offset `o`; `none` if one was never written. -/
def getCells (f : Nat → Option Cell) (o : Nat) : Nat → Option (List Cell)
  | 0 => some []
  | n + 1 =>
      match f o with
      | some c => (getCells f (o + 1) n).map (c :: ·)
      | none => none

theorem getCells_congr {f g : Nat → Option Cell} (o n : Nat)
    (h : ∀ k, o ≤ k → k < o + n → f k = g k) : getCells f o n = getCells g o n := by
  induction n generalizing o with
  | zero => rfl
  | succ n ih =>
      have h0 : f o = g o := h o (Nat.le_refl _) (by omega)
      simp only [getCells, h0]
      have := ih (o + 1) (fun k hk1 hk2 => h k (by omega) (by omega))
      rw [this]

theorem getCells_put_same (f : Nat → Option Cell) (o : Nat) (cs : List Cell) :
    getCells (putCells f o cs) o cs.length = some cs := by
  induction cs generalizing o with
  | nil => rfl
  | cons c cs ih =>
      have h0 : putCells f o (c :: cs) o = some c := by simp only [putCells, Std.le_refl, List.length_cons, Nat.lt_add_right_iff_pos, Nat.zero_lt_succ, and_self,
  ↓reduceIte, Nat.sub_self, getElem?_pos, List.getElem_cons_zero]
      have h1 : getCells (putCells f o (c :: cs)) (o + 1) cs.length = some cs := by
        rw [getCells_congr (g := putCells f (o + 1) cs) (o + 1) cs.length]
        · exact ih (o + 1)
        · intro k hk1 hk2
          simp only [putCells, List.length_cons]
          have e : k - o = (k - (o + 1)) + 1 := by omega
          rw [if_pos (by omega), if_pos (by omega), e]
          simp only [List.getElem?_cons_succ]
      simp only [List.length_cons, getCells, h0, h1]
      rfl

theorem getCells_put_disj (f : Nat → Option Cell) (o : Nat) (cs : List Cell) (o' n' : Nat)
    (h : o' + n' ≤ o ∨ o + cs.length ≤ o') : getCells (putCells f o cs) o' n' = getCells f o' n' := by
  apply getCells_congr
  intro k hk1 hk2
  simp only [putCells]
  rw [if_neg (by omega)]

/-! ## 2. Encoding -/

/-- The `k` little-endian bytes of `v`. -/
def natBytes : Nat → Nat → List Cell
  | 0, _ => []
  | k + 1, v => .byte (v % 256) :: natBytes k (v / 256)

/-- The number a list of data bytes denotes (little endian); `none` if a cell is no data byte. -/
def bytesNat : List Cell → Option Nat
  | [] => some 0
  | .byte b :: r => (bytesNat r).map fun x => b % 256 + 256 * x
  | .frag .. :: _ => none

theorem natBytes_length (k v : Nat) : (natBytes k v).length = k := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih => simp only [natBytes, List.length_cons, ih, Nat.add_left_cancel_iff]

theorem bytesNat_natBytes (k v : Nat) : bytesNat (natBytes k v) = some (v % 256 ^ k) := by
  induction k generalizing v with
  | zero => simp only [natBytes, bytesNat, Nat.pow_zero, Nat.mod_one]
  | succ k ih =>
      simp only [natBytes, bytesNat, ih, Option.map_some, Nat.pow_succ]
      congr 1
      have := Nat.mod_mul (x := v) (a := 256) (b := 256 ^ k)
      rw [Nat.mul_comm (256 ^ k) 256, this, Nat.mod_mod]

variable [Conf]

/-- The cells a value is stored as, least significant byte first. -/
def Val.encLE : Val → List Cell
  | .int w v => natBytes ((w + 7) / 8) v.toNat
  | .flt g => natBytes 4 (zuBits f32 g)
  | .dbl g => natBytes 8 (zuBits f64 g)
  | .ptr b o => (List.range Conf.wb).map (Cell.frag b o)

/-- The value a list of cells is when read as type `t`. -/
def Ty.decLE : Ty → List Cell → Option Val
  | .int w, cs =>
      if cs.length = (w + 7) / 8 then (bytesNat cs).map fun n => Val.int w (BitVec.ofNat w n) else none
  | .flt, cs => if cs.length = 4 then (bytesNat cs).map fun n => Val.flt (ausBits f32 n) else none
  | .dbl, cs => if cs.length = 8 then (bytesNat cs).map fun n => Val.dbl (ausBits f64 n) else none
  | .ptr, cs =>
      match cs with
      | .frag b o 0 :: _ => if cs = (List.range Conf.wb).map (Cell.frag b o) then some (.ptr b o) else none
      | _ => none
  | _, _ => none

theorem Val.encLE_length (v : Val) : v.encLE.length = v.ty.store := by
  cases v <;> simp only [encLE, natBytes_length, Ty.store, ty, List.length_map, List.length_range]

theorem decLE_encLE_int (w : Nat) (v : BitVec w) : Ty.decLE (.int w) (Val.encLE (.int w v)) = some (.int w v) := by
  simp only [Ty.decLE, Val.encLE, natBytes_length, bytesNat_natBytes, if_true, Option.map_some]
  congr 2
  have h1 : v.toNat < 2 ^ w := v.isLt
  have h2 : 2 ^ w ≤ 256 ^ ((w + 7) / 8) := by
    have : 256 ^ ((w + 7) / 8) = 2 ^ (8 * ((w + 7) / 8)) := by
      rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]
    rw [this]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h1 h2)]
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem decLE_encLE_ptr (b : Nat) (o : Int) : Ty.decLE .ptr (Val.encLE (.ptr b o)) = some (.ptr b o) := by
  obtain ⟨n, hn⟩ : ∃ n, Conf.wb = n + 1 := ⟨Conf.wb - 1, by have := Conf.wb_pos; omega⟩
  simp only [Ty.decLE, Val.encLE, hn, List.range_succ_eq_map, List.map_cons, List.map_map, ↓reduceIte]

/-- A well-formed float triple stays below `2^(1 + ebits + fracBits)`. -/
theorem zuBits_lt (F : Format) (hF : F.dicht) (g : GBits F) (hw : wf F g) :
    zuBits F g < 2 ^ (F.ebits + F.fracBits + 1) := by
  unfold zuBits
  obtain ⟨h1, h2⟩ := hw
  unfold Format.dicht Format.bexpMax at hF
  unfold Format.bexpMax at h1
  have e1 : g.bexp < 2 ^ F.ebits := by omega
  have hp : 0 < 2 ^ F.fracBits := Nat.pow_pos (by decide)
  have e2 : g.bexp * 2 ^ F.fracBits + g.frac < 2 ^ F.ebits * 2 ^ F.fracBits := by
    have : (g.bexp + 1) * 2 ^ F.fracBits ≤ 2 ^ F.ebits * 2 ^ F.fracBits :=
      Nat.mul_le_mul_right _ e1
    rw [Nat.add_mul] at this
    omega
  rw [Nat.pow_succ, Nat.pow_add]
  split <;> omega

theorem decLE_encLE_flt (g : F32) (hw : wf f32 g) :
    Ty.decLE .flt (Val.encLE (.flt g)) = some (.flt g) := by
  have hlt := zuBits_lt f32 f32_dicht g hw
  have : (f32.ebits + f32.fracBits + 1) = 32 := by decide
  rw [this] at hlt
  simp only [Ty.decLE, Val.encLE, natBytes_length, bytesNat_natBytes, if_true, Option.map_some]
  rw [Nat.mod_eq_of_lt (by simpa using hlt), ausBits_zuBits f32 f32_dicht g hw]

theorem decLE_encLE_dbl (g : F64) (hw : wf f64 g) :
    Ty.decLE .dbl (Val.encLE (.dbl g)) = some (.dbl g) := by
  have hlt := zuBits_lt f64 f64_dicht g hw
  have : (f64.ebits + f64.fracBits + 1) = 64 := by decide
  rw [this] at hlt
  simp only [Ty.decLE, Val.encLE, natBytes_length, bytesNat_natBytes, if_true, Option.map_some]
  rw [Nat.mod_eq_of_lt (by simpa using hlt), ausBits_zuBits f64 f64_dicht g hw]
/-! ## Byte order -/

/-- Cells in memory order: the target's byte order is a parameter. -/
def order (cs : List Cell) : List Cell := if Conf.big then cs.reverse else cs

theorem order_order (cs : List Cell) : order (order cs) = cs := by
  by_cases h : Conf.big = true <;> simp only [order, h, ↓reduceIte, List.reverse_reverse, Bool.false_eq_true]

theorem order_length (cs : List Cell) : (order cs).length = cs.length := by
  by_cases h : Conf.big = true <;> simp only [order, h, ↓reduceIte, List.length_reverse, Bool.false_eq_true]

/-- The cells a value is stored as, in memory order. -/
def Val.enc (v : Val) : List Cell := order v.encLE

/-- The value a list of cells in memory order is when read as type `t`. -/
def Ty.dec (t : Ty) (cs : List Cell) : Option Val := t.decLE (order cs)

theorem Val.enc_length (v : Val) : v.enc.length = v.ty.store := by
  unfold Val.enc; rw [order_length]; exact Val.encLE_length v

theorem dec_enc_int (w : Nat) (v : BitVec w) : Ty.dec (.int w) (Val.enc (.int w v)) = some (.int w v) := by
  unfold Ty.dec Val.enc; rw [order_order]; exact decLE_encLE_int w v

theorem dec_enc_ptr (b : Nat) (o : Int) : Ty.dec .ptr (Val.enc (.ptr b o)) = some (.ptr b o) := by
  unfold Ty.dec Val.enc; rw [order_order]; exact decLE_encLE_ptr b o

theorem dec_enc_flt (g : F32) (hw : wf f32 g) :
    Ty.dec .flt (Val.enc (.flt g)) = some (.flt g) := by
  unfold Ty.dec Val.enc; rw [order_order]; exact decLE_encLE_flt g hw

theorem dec_enc_dbl (g : F64) (hw : wf f64 g) :
    Ty.dec .dbl (Val.enc (.dbl g)) = some (.dbl g) := by
  unfold Ty.dec Val.enc; rw [order_order]; exact decLE_encLE_dbl g hw

end Gabbro.Code
