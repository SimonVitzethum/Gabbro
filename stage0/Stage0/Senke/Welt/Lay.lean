/-
  File:      stage0/Stage0/Senke/Welt/Lay.lean
  Subject:   Where the world lies in memory: every column of a table (field `f` of table `t`, its elements one after the
             other from `col t f`) and every global (`ga g`, one word).

  Every element of every column is one word, also in a column of bytes: a system call's buffer is packed into
  bytes at the call (`PLAN-SELF-HOSTING.md` §2.1.4), so every cell of the world is one aligned word. All of it lies
  in `[lo, hi)`.
-/
import Grammatik.Kern.Semantik.Semantik

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik

structure Lay (D : Deklaration) where
  col : (t : D.Tab) → D.Feld t → Nat
  ga : D.Glob → Nat
  lo : Nat
  hi : Nat

/-- The address of element `k` of the column `f` of table `t`. -/
def Lay.elem {D : Deklaration} (L : Lay D) (t : D.Tab) (f : D.Feld t) (k : Nat) : Nat := L.col t f + 8 * k

end Gabbro.Stage0.Senke
