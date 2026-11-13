/- Shared encoded-memory fixtures for the sequential ticket-lock witnesses. -/
module
public import Stage0.Senke.Sperre.Warten.Wait
public import Stage0.Senke.Sperre.Paar
public import Stage0.Senke.Images.BildLese
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


namespace Gabbro.Stage0.Senke.WartenProbe
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

def takeCode : List II := nimmT layout 8192 4

def wakeCode : List II := gibT layout 8192 4

/-- Real encoded code, a protected frame word and three real lock words.
    Only their low bytes are nonzero in this fixture. -/
def memory (wake : Bool) : Mem where
  b a := if a.toNat = 4120 then 77
    else if a.toNat = 8192 then (if wake then 2 else 1)
    else if a.toNat = 8200 then 0
    else if a.toNat = 8208 then (if wake then 1 else 0)
    else (((if wake then wakeCode else takeCode).flatMap encII)[a.toNat]?).getD 0
  rd _ := true
  wr _ := true

theorem environment (wake : Bool) :
    LE (memory wake) 0 4096 4 8192 (if wake then wakeCode else takeCode) := by
  refine ⟨⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩,
    by decide, by decide, by decide, rfl, rfl, rfl, ?_, ?_⟩
  · apply codeAt_bytes (if wake then wakeCode else takeCode) 0 (by cases wake <;> decide +kernel)
    intro i hi
    have length : ((if wake then wakeCode else takeCode).flatMap encII).length ≤ 560 := by
      cases wake <;> decide +kernel
    refine ⟨rfl, rfl, ?_⟩
    simp only [memory, Nat.zero_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega),
      ite_eq_right (show i ≠ 4120 by omega),
      ite_eq_right (show i ≠ 8192 by omega),
      ite_eq_right (show i ≠ 8200 by omega),
      ite_eq_right (show i ≠ 8208 by omega),
      List.getElem?_eq_getElem hi, Option.getD_some]
  · unfold CodeFar
    cases wake <;> decide +kernel

end Gabbro.Stage0.Senke.WartenProbe
