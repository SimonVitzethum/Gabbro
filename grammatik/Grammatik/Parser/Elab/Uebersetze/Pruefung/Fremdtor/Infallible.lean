/- The infallible foreign gate: retain each checker component as its own
   kernel-checked certificate, so one conversion never retains every reduction. -/
module

public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Fremdtor.Source
import Grammatik.Kern.Taktik.KernelRfl
import all Init.Data.Int.Repr
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

namespace Gabbro.Grammatik.Parser.Uebersetze

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Zielsatz

set_option Elab.async false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The exact source unit passes every component of the strict atomic checker. -/
theorem fremd_akzeptiert :
    AkzeptiertX checkPFremd (Cover.Differenz.sperrFamilie uFremd)
      (List.finRange uFremd.fns.length) [] [] [] [] checkChecksFremd = true := by
  decide +kernel

end Gabbro.Grammatik.Parser.Uebersetze
