/-
  File:      Grammatik/Gen/Fein/Mitglieder.lean
  Subject:   THE DECLARATIONS OF THE FINE CELLS: a child of an expression position of any type needs a carrier, a
             parameter, a register of every type class. They are built from one representative type per class
             (`vertreter`, one per constructor of `Ty`), not written per cell.
-/
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
public import Grammatik.Gen.Abdeckung.Waehlen
public import Grammatik.Gen.Fein.Zellen
import all Init.Data.Repr
@[expose] public section


namespace Gabbro.Grammatik.Gen.Fein

open Gabbro.Grammatik Gabbro.Grammatik.Gen

/-- One representative type per type class, in the order of `Ty.kopf`. -/
def vertreter : List Ty :=
  [.int 0 0, .bool, .opt 1, .sum [none, some (.int 0 1)], .why 2, .never, .fl (0, 1) (1, 1), .fnptr 0, .ptr (.table 0 (true, true))]
