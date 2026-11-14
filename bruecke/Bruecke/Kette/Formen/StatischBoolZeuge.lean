module
public import Bruecke.Kette.Formen.ZeugenSchritte
import all Init.Data.String.Length
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.Repr
import all Init.Data.String.Decode
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
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
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil12
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Erzeuge
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Torhuelle
import all Grammatik.Parser.Elab.Generic.StaticConformance
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil5
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest1
import all Grammatik.Parser.Elab.UebersetzeAllg3.Body
@[expose] public section

/-! # Witnesses for `bool` statics: gates, reader forms and narrow failure branches

The fixture is a hand-built unit (no parser run). It shows that the extended gates admit a
writable `bool` static while still refusing atomic ones and out-of-range initialisers, that the
reader turns a `bool` static write into a Body global store and a `bool` static condition into a
Body global read, and that a narrow failure branch which sets the static is read. -/

namespace Gabbro.Bruecke.StatischBoolZeuge

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

set_option maxRecDepth 100000
set_option maxHeartbeats 400000

def setter : UFn :=
  { name := "fail", params := [], kinds := [], res := none, held := [], puts := [],
    gputs := ["err"], gives := [], body := [.assignGlobB "err" .tru], ret := .empty }

def reader : UFn :=
  { name := "clear", params := [], kinds := [], res := none, held := [], puts := [],
    gputs := ["err"], gives := [],
    body := [.ifBeg (.globB "err"), .assignGlobB "err" .fls, .ifElse, .blkEnd], ret := .empty }

def narrowing : UFn :=
  { name := "digit", params := [("x", .int 0 255)], kinds := [.int], res := none, held := [],
    puts := [], gputs := ["err"], gives := [],
    body := [.narrowBeg "x" 0 9, .assignGlobB "err" .tru, .ret .empty, .blkEnd], ret := .empty }

def unit : UProg :=
  { tabs := [], locks := [], fns := [setter, reader, narrowing],
    globs := [{ name := "err", ty := .bool, init := 0, var := true }] }

/-- A writable `bool` static passes both unit gates; an atomic one and an initialiser other
    than `0`/`1` are refused. -/
theorem gates_zeuge :
    staticsB unit = true ∧ nullB unit = true ∧
      staticsB { unit with globs := [{ name := "err", ty := .bool, init := 0, atomic := true }] } = false ∧
      nullB { unit with globs := [{ name := "err", ty := .bool, init := 2 }] } = false := by
  cbv

/-- The static has the Body shape `bool` in the world typing. -/
theorem shape_zeuge : globShape unit "err" = some .bool ∧ globShape unit "missing" = none := by
  cbv

/-- A static write is a Body global store, and a static condition a Body global read. -/
theorem reader_forms_zeuge :
    zuBodyZ unit setter = some [.assignGlobal "err" (.lit (.bool true))] ∧
      zuBodyZ unit reader =
        some [.ite (.global "err") [.assignGlobal "err" (.lit (.bool false))] []] := by
  exact ⟨by cbv, by cbv⟩

/-- A narrow failure branch that sets the static and returns is read. -/
theorem narrow_zeuge : (zuBodyZ unit narrowing).isSome = true := by
  cbv

end Gabbro.Bruecke.StatischBoolZeuge
