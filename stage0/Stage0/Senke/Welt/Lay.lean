/-
  File:      stage0/Stage0/Senke/Welt/Lay.lean
  Subject:   Where the world lies in memory: every column of a table (field `f` of table `t`, its elements one after the
             other from `col t f`) and every global (`ga g`, one word).

  A column of bytes (type `0 .. 255`) holds one byte per element, so a buffer a system call reads or writes is the
  column itself; every other column holds one word per element. All of it lies in `[lo, hi)`.
-/
import Grammatik.Kern.Semantik.Semantik

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik

structure Lay (D : Deklaration) where
  col : (t : D.Tab) → D.Feld t → Nat
  ga : D.Glob → Nat
  lo : Nat
  hi : Nat

/-- A column of bytes. -/
def byteCol {D : Deklaration} (t : D.Tab) (f : D.Feld t) : Bool := D.typ t f == .int 0 255

/-- The bytes of one element of a column. -/
def stride {D : Deklaration} (t : D.Tab) (f : D.Feld t) : Nat := if byteCol t f then 1 else 8

/-- The address of element `k` of the column `f` of table `t`. -/
def Lay.elem {D : Deklaration} (L : Lay D) (t : D.Tab) (f : D.Feld t) (k : Nat) : Nat := L.col t f + stride t f * k

end Gabbro.Stage0.Senke
