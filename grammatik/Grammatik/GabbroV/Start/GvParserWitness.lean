module

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
public import Grammatik.Parser.Elab.Uebersetze

-- Concrete witnesses execute the actual empty check/static gates.
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil12
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Erzeuge
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Torhuelle
import all Grammatik.Parser.Elab.Generic.StaticConformance
import Grammatik.Kern.Taktik.KernelRfl

@[expose] public section

namespace Gabbro.Grammatik.GabbroV.GvParserFragment

open Gabbro.Grammatik.Parser
open Gabbro.Grammatik.Parser.Uebersetze

/-! ## 108 elaborates -/

/-- **108's parsed items** (`beispiele/0108-disjoint-start-locks.gab`,
    printed by `.tmp/probe_repr108.lean`, pasted in the tree's dotted
    style like `items104`): one table, two readers, and the single
    `concurrent` item (the thread roots). -/
def w108items : List SItemTief :=
  [.modT "beispiel::disjoint_start_locks"
    [.tableT "T" .none (.some (.lit 4)) .none .none false
      [.tSlot [{ fname := "v", ftyp := .atom "u32", pos := .none, bezug := .none, wo := .none, reserviert := false, byOps := false }]],
    .fnT
      { art := "impl", name := "read_a", params := [], res := .some (.atom "u32"), fehler := .none, klauseln := [.effs [.reads (.field (.variable "T") "slots")], .cost (.lit 4)] }
      (.block []
        (.some (.ret (.some (.field
          (.index (.field (.variable "T") "slots") (.lit 0)) "v"))))),
    .fnT
      { art := "impl", name := "read_c", params := [], res := .some (.atom "u32"), fehler := .none, klauseln := [.effs [.reads (.field (.variable "T") "slots")], .cost (.lit 4)] }
      (.block []
        (.some (.ret (.some (.field
          (.index (.field (.variable "T") "slots") (.lit 1)) "v"))))),
    .concT [(["read_a"], []), (["read_c"], [])]]]

/-- **108's elaborated program** (same probe, pasted):
    the table and both readers, the `concurrent` members as thread roots. -/
def w108prog : UProg :=
  { tabs := [{ name := "T", count := 4, cols := [("v", 0, 4294967295)], bools := [] }], locks := [], fns := [{ name := "read_a", params := [], kinds := [], res := .some (0, 4294967295), resBool := false, held := [], puts := [], gives := [], body := [], ret := .val (.tab "T" "v" (.lit 0)) }, { name := "read_c", params := [], kinds := [], res := .some (0, 4294967295), resBool := false, held := [], puts := [], gives := [], body := [], ret := .val (.tab "T" "v" (.lit 1)) }], roots := ["read_a", "read_c"] }

/-- **108 elaborates**: `elabU` yields exactly the pasted program, the `concurrent` members as its thread
    roots (and `lowerAllg` succeeds on it). -/
theorem w108_elab : beqElabU (elabU w108items) (.ok w108prog) = true := by
  kernel_rfl

#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment.w108_elab

end Gabbro.Grammatik.GabbroV.GvParserFragment
