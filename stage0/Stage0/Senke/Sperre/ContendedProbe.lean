/- A real-memory witness for the contended lock prefix. The foreign holder,
   recursion depth and existing waiters are all nonzero, outside `SyncOK`. -/
module
public import Stage0.Senke.Sperre.Contended
public import Stage0.Senke.Sperre.Paar
public import Stage0.Senke.BildLese
public import Grammatik.Parser.Elab.UebersetzeAllg
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice
@[expose] public section


namespace Gabbro.Stage0.Senke.ContendedProbe
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
open Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg

set_option maxRecDepth 100000

def unit : UProg := {
  tabs := []
  locks := [{ name := "L", rank := 0, guard := [] }]
  fns := [{ name := "main", params := [], kinds := [], res := none, held := [], puts := [], gives := [], body := [], ret := .empty }]
}

abbrev D := declOf unit

def layout : Lay D where
  col t := Fin.elim0 t
  ga g := Fin.elim0 g
  lo := 8192
  hi := 8192
  tor a := Fin.elim0 a
  byte t := Fin.elim0 t
  sb := 4096
  st := 4096
  lk _ := 8192
  sye := 8216

def code : List II := nimmC layout 8192 4

def memory : Mem where
  b a := if a.toNat = 4120 then 77
    else if a.toNat = 8192 then 2
    else if a.toNat = 8200 then 3
    else if a.toNat = 8208 then 5
    else ((code.flatMap encII)[a.toNat]?).getD 0
  rd _ := true
  wr _ := true

theorem environment : LE memory 0 4096 4 8192 code := by
  refine ⟨⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩,
    by decide, by decide, by decide, rfl, rfl, rfl, ?_, ?_⟩
  · apply codeAt_bytes code 0 (by decide +kernel)
    intro i hi
    have length : (code.flatMap encII).length = 768 := by decide +kernel
    refine ⟨rfl, rfl, ?_⟩
    simp only [memory, Nat.zero_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega),
      ite_eq_right (show i ≠ 4120 by omega),
      ite_eq_right (show i ≠ 8192 by omega),
      ite_eq_right (show i ≠ 8200 by omega),
      ite_eq_right (show i ≠ 8208 by omega),
      List.getElem?_eq_getElem hi, Option.getD_some]
  · unfold CodeFar
    decide +kernel

/-- The emitted code reaches its actual wait branch. The CAS observed owner 2,
    not this thread (1); count 3, waiters 5 and the protected frame word 77 stay.
    All execution/memory premises are supplied together for every runner kernel. -/
theorem nimm_contended_zeuge [Kern] :
    LE memory 0 4096 4 8192 code ∧
    MeOK layout 4096 ∧ (2 : W) ≠ meW layout 4096 ∧
    ∃ m' f', Star ⟨0, 4096⟩ memory ⟨352, 4096⟩ m' ∧
      LS memory m' 4096 4 8192 f' 2 3 5 ∧
      m'.rd64 (slot 4096 4) = some 1 ∧
      m'.rd64 (slot 4096 8) = some 2 ∧
      m'.rd64 (slot 4096 3) = some 77 := by
  have me : MeOK layout 4096 := ⟨by decide, by decide, by decide, by decide, by decide⟩
  have foreign : (2 : W) ≠ meW layout 4096 := by decide
  obtain ⟨f, initial⟩ := ls_init environment
    (o := 2) (c := 3) (w := 5) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  obtain ⟨m', f', steps, state, owner, seen, _⟩ :=
    nimm_contended environment initial (At.whole code) me (by decide) foreign
  refine ⟨environment, me, foreign, m', f', steps, state, ?_, ?_, ?_⟩
  · simpa [owner, meW, layout] using state.sl 0 (by decide)
  · simpa [seen] using state.sl 4 (by decide)
  · have bytes : ∀ j, j < 8 → m'.b ((slot 4096 3) + BitVec.ofNat 64 j) =
        memory.b ((slot 4096 3) + BitVec.ofNat 64 j) := by
      intro j hj
      have position : ((slot 4096 3) + BitVec.ofNat 64 j).toNat = 4120 + j := by
        change ((4120 : W) + BitVec.ofNat 64 j).toNat = 4120 + j
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]
        change (4120 + j % 2 ^ 64) % 2 ^ 64 = 4120 + j
        omega
      apply state.ag.b
      · change ¬ (4128 ≤ ((slot 4096 3) + BitVec.ofNat 64 j).toNat ∧
          ((slot 4096 3) + BitVec.ofNat 64 j).toNat < 4272)
        rw [position]
        omega
      · unfold InLk
        rw [position]
        omega
    rw [rd64_keep state.ag.rd bytes]
    decide +kernel

end Gabbro.Stage0.Senke.ContendedProbe
