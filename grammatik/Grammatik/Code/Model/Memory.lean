import Grammatik.Code.Model.Cells

/-
  File:      Grammatik/Code/Model/Memory.lean
  Subject:   TRACK L, PHASE L0 -- THE MEMORY of the IR: BLOCK-STRUCTURED, BYTE-ADDRESSED.
             (Cells, byte encodings and their round trips: `Cells.lean`.)

  A pointer is a block and a byte offset (`Val.ptr b o`). Memory is a map from block ids to
  blocks, a block is a size and a map from byte offsets to CELLS, and a cell is a data byte or
  one byte of a stored pointer (a FRAGMENT, as in CompCert: a pointer is stored as eight
  fragments and read back only if all eight are its own). Consequences that are theorems here,
  not conventions:
    * two different allocations never alias (`store_blks_other`, `load_store_other`);
    * a store changes the cells it covers and nothing else (`load_store_other`);
    * a load of what was just stored returns it (`load_store_int`, `load_store_ptr`,
      `load_store_flt`, `load_store_dbl`);
    * `alloc` gives a fresh block and leaves every old one as it was (`alloc_load`).
  An access is aligned or stuck (`Mem.inside`).
  Reading a cell never written (an `alloc` is uninitialised) or reading outside a block is
  `none`: the semantics gets STUCK, which is the model's word for undefined behaviour.
-/

namespace Gabbro.Code

open Gabbro.Grammatik.Gleitkomma

/-- Replace block `b` by `blk`. -/
def Mem.setBlk (m : Mem) (b : Nat) (blk : Blk) : Mem :=
  { blks := fun b' => if b' = b then some blk else m.blks b', next := m.next }

/-- Allocate a block of `n` bytes: zero filled (a global) or never written (an `alloc`).
    Returns the new memory and the block id. -/
def Mem.alloc (m : Mem) (n : Nat) (zero : Bool) : Mem × Nat :=
  let blk : Blk := ⟨n, fun k => if k < n ∧ zero = true then some (.byte 0) else none⟩
  ({ (m.setBlk m.next blk) with next := m.next + 1 }, m.next)

variable [Conf]

/-- The guard of a scalar access of type `t` at offset `o` in a block of size `n`: inside the
    block, and ALIGNED -- an unaligned access is stuck (no ISA is asked to do one). -/
def Mem.inside (n : Nat) (o : Int) (t : Ty) : Prop :=
  0 ≤ o ∧ t.scalar = true ∧ o.toNat + t.store ≤ n ∧ o % (t.align : Int) = 0

instance (n : Nat) (o : Int) (t : Ty) : Decidable (Mem.inside n o t) := by
  unfold Mem.inside; exact inferInstance

/-- Read a scalar of type `t` at byte offset `o` of block `b`. Stuck (`none`) outside the block,
    on a negative offset, on a never written cell and on a cell of the wrong kind. -/
def Mem.load (m : Mem) (b : Nat) (o : Int) (t : Ty) : Option Val :=
  match m.blks b with
  | none => none
  | some blk =>
      if Mem.inside blk.size o t then (getCells blk.cells o.toNat t.store).bind t.dec else none

/-- Write the scalar `v` of type `t` at byte offset `o` of block `b`. -/
def Mem.store (m : Mem) (b : Nat) (o : Int) (t : Ty) (v : Val) : Option Mem :=
  match m.blks b with
  | none => none
  | some blk =>
      if Mem.inside blk.size o t ∧ v.ty = t then
        some (m.setBlk b { blk with cells := putCells blk.cells o.toNat v.enc })
      else none

theorem setBlk_same (m : Mem) (b : Nat) (blk : Blk) : (m.setBlk b blk).blks b = some blk := by
  simp [Mem.setBlk]

theorem setBlk_other (m : Mem) (b : Nat) (blk : Blk) (b' : Nat) (h : b' ≠ b) :
    (m.setBlk b blk).blks b' = m.blks b' := by
  simp [Mem.setBlk, h]

/-- What a successful store says: the block exists, the access is inside it, the value has the
    type, and the new memory is the old one with that block's cells overwritten. -/
theorem store_some {m m' : Mem} {b : Nat} {o : Int} {t : Ty} {v : Val}
    (h : m.store b o t v = some m') :
    ∃ blk, m.blks b = some blk ∧ Mem.inside blk.size o t ∧ v.ty = t ∧
      m' = m.setBlk b { blk with cells := putCells blk.cells o.toNat v.enc } := by
  unfold Mem.store at h
  split at h
  · simp at h
  · rename_i blk hblk
    split at h
    · rename_i hc
      refine ⟨blk, hblk, hc.1, hc.2, ?_⟩
      simp at h
      exact h.symm
    · simp at h

theorem alloc_wf {m : Mem} (h : m.Wf) (n : Nat) (z : Bool) : (m.alloc n z).1.Wf := by
  intro b hb
  simp only [Mem.alloc, Mem.setBlk] at hb ⊢
  by_cases e : b = m.next
  · omega
  · simp only [e, if_false] at hb
    have := h b hb
    omega

theorem alloc_fresh {m : Mem} (h : m.Wf) (n : Nat) (z : Bool) (b : Nat)
    (hb : (m.blks b).isSome = true) : b ≠ (m.alloc n z).2 := by
  have := h b hb
  simp only [Mem.alloc]
  omega

theorem alloc_blks_old (m : Mem) (n : Nat) (z : Bool) (b : Nat) (hb : b ≠ m.next) :
    (m.alloc n z).1.blks b = m.blks b := by
  simp [Mem.alloc, Mem.setBlk, hb]

theorem alloc_load (m : Mem) (n : Nat) (z : Bool) (b : Nat) (hb : b ≠ m.next) (o : Int) (t : Ty) :
    (m.alloc n z).1.load b o t = m.load b o t := by
  simp only [Mem.load, alloc_blks_old m n z b hb]

theorem alloc_size (m : Mem) (n : Nat) (z : Bool) :
    ((m.alloc n z).1.blks (m.alloc n z).2).map Blk.size = some n := by
  simp [Mem.alloc, Mem.setBlk]

theorem store_next {m m' : Mem} {b : Nat} {o : Int} {t : Ty} {v : Val}
    (h : m.store b o t v = some m') : m'.next = m.next := by
  obtain ⟨blk, _, _, _, e⟩ := store_some h
  rw [e]; rfl

theorem store_blks_other {m m' : Mem} {b : Nat} {o : Int} {t : Ty} {v : Val}
    (h : m.store b o t v = some m') (b' : Nat) (hb : b' ≠ b) : m'.blks b' = m.blks b' := by
  obtain ⟨blk, _, _, _, e⟩ := store_some h
  rw [e]; exact setBlk_other _ _ _ _ hb

theorem store_wf {m m' : Mem} {b : Nat} {o : Int} {t : Ty} {v : Val}
    (h : m.store b o t v = some m') (hw : m.Wf) : m'.Wf := by
  intro b' hb'
  rw [store_next h]
  obtain ⟨blk, hblk, _, _, e⟩ := store_some h
  by_cases eb : b' = b
  · subst eb
    exact hw b' (by simp [hblk])
  · rw [store_blks_other h b' eb] at hb'
    exact hw b' hb'

theorem store_size {m m' : Mem} {b : Nat} {o : Int} {t : Ty} {v : Val}
    (h : m.store b o t v = some m') (b' : Nat) :
    (m'.blks b').map Blk.size = (m.blks b').map Blk.size := by
  by_cases eb : b' = b
  · subst eb
    obtain ⟨blk, hblk, _, _, e⟩ := store_some h
    rw [e, setBlk_same, hblk]; rfl
  · rw [store_blks_other h b' eb]

/-- A scalar read right after its write returns it, given that decoding inverts encoding. -/
theorem load_store_of {m m' : Mem} {b : Nat} {o : Int} {t : Ty} {v : Val}
    (h : m.store b o t v = some m') (hd : t.dec v.enc = some v) : m'.load b o t = some v := by
  obtain ⟨blk, hblk, hin, hty, e⟩ := store_some h
  have hlen : v.enc.length = t.store := by rw [Val.enc_length, hty]
  simp only [Mem.load, e, setBlk_same]
  rw [if_pos hin]
  have : getCells (putCells blk.cells o.toNat v.enc) o.toNat t.store = some v.enc := by
    rw [← hlen]; exact getCells_put_same _ _ _
  rw [this]
  exact hd

theorem load_store_int {m m' : Mem} {b : Nat} {o : Int} {w : Nat} {v : BitVec w}
    (h : m.store b o (.int w) (.int w v) = some m') : m'.load b o (.int w) = some (.int w v) :=
  load_store_of h (dec_enc_int w v)

theorem load_store_ptr {m m' : Mem} {b : Nat} {o : Int} {b2 : Nat} {o2 : Int}
    (h : m.store b o .ptr (.ptr b2 o2) = some m') : m'.load b o .ptr = some (.ptr b2 o2) :=
  load_store_of h (dec_enc_ptr b2 o2)

theorem load_store_flt {m m' : Mem} {b : Nat} {o : Int} {g : F32} (hw : wf f32 g)
    (h : m.store b o .flt (.flt g) = some m') : m'.load b o .flt = some (.flt g) :=
  load_store_of h (dec_enc_flt g hw)

theorem load_store_dbl {m m' : Mem} {b : Nat} {o : Int} {g : F64} (hw : wf f64 g)
    (h : m.store b o .dbl (.dbl g) = some m') : m'.load b o .dbl = some (.dbl g) :=
  load_store_of h (dec_enc_dbl g hw)

/-- A store leaves every disjoint read as it was: another block, or another byte range. -/
theorem load_store_other {m m' : Mem} {b : Nat} {o : Int} {t : Ty} {v : Val}
    (h : m.store b o t v = some m') {b' : Nat} {o' : Int} {t' : Ty}
    (hd : b' ≠ b ∨ o' + (t'.store : Int) ≤ o ∨ o + (t.store : Int) ≤ o') :
    m'.load b' o' t' = m.load b' o' t' := by
  by_cases eb : b' = b
  · subst eb
    obtain ⟨blk, hblk, hin, hty, e⟩ := store_some h
    have hd' : o' + (t'.store : Int) ≤ o ∨ o + (t.store : Int) ≤ o' := by
      rcases hd with hd | hd
      · exact absurd rfl hd
      · exact hd
    simp only [Mem.load, e, setBlk_same, hblk]
    by_cases hi : Mem.inside blk.size o' t'
    · rw [if_pos hi, if_pos hi]
      have : getCells (putCells blk.cells o.toNat v.enc) o'.toNat t'.store
          = getCells blk.cells o'.toNat t'.store := by
        apply getCells_put_disj
        have h1 : 0 ≤ o' := hi.1
        have h0 : 0 ≤ o := hin.1
        have hl : v.enc.length = t.store := by rw [Val.enc_length, hty]
        rw [hl]
        omega
      simp only [this]
    · rw [if_neg hi, if_neg hi]
  · simp only [Mem.load, store_blks_other h b' eb]

end Gabbro.Code
