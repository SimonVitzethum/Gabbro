module
public import Grammatik.Parser.Elab.UebersetzeAllg3.Measures.Fixtures
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest1
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

namespace Gabbro.Grammatik.Parser.Measures.Fixtures
open Uebersetze UebersetzeAllg UebersetzeAllg2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- Recover the body through the generic function certificate; do not reduce program assembly. -/
private theorem countP_rumpf : countP.rumpf 0 =
    .cons (.ite (.lt (.lit 0) (.var .here))
      (.cons (.call 0 (.cons (.widen (by decide) (by decide) (.lit 0)) .nil)
        (rufPasstB_ok (u := countdown) (by decide)) (by rfl)) .nil) .nil)
      (.ret .empty (List.Perm.refl [])) := by
  apply program_rumpf_of_lowerFn (ens := .tru) (req := .tru)
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The left member calls the right member with the literal zero. -/
private theorem mutualP_rumpf_zero : mutualP.rumpf 0 =
    .cons (.ite (.lt (.lit 0) (.var .here))
      (.cons (.call 1 (.cons (.widen (by decide) (by decide) (.lit 0)) .nil)
        (rufPasstB_ok (u := mutualU) (by decide)) (by rfl)) .nil) .nil)
      (.ret .empty (List.Perm.refl [])) := by
  apply program_rumpf_of_lowerFn (ens := .tru) (req := .tru)
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The right member calls the left member with the literal zero. -/
private theorem mutualP_rumpf_one : mutualP.rumpf 1 =
    .cons (.ite (.lt (.lit 0) (.var .here))
      (.cons (.call 0 (.cons (.widen (by decide) (by decide) (.lit 0)) .nil)
        (rufPasstB_ok (u := mutualU) (by decide)) (by rfl)) .nil) .nil)
      (.ret .empty (List.Perm.refl [])) := by
  apply program_rumpf_of_lowerFn (ens := .tru) (req := .tru)
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- Both calls survive lowering, including the call before the final call. -/
private theorem nonTailP_rumpf : nonTailP.rumpf 0 =
    .cons (.ite (.lt (.lit 0) (.var .here))
      (.cons (.call 0 (.cons (.widen (by decide) (by decide) (.lit 0)) .nil)
        (rufPasstB_ok (u := nonTail) (by decide)) (by rfl))
        (.cons (.call 0 (.cons (.widen (by decide) (by decide) (.lit 0)) .nil)
          (rufPasstB_ok (u := nonTail) (by decide)) (by rfl)) .nil)) .nil)
      (.ret .empty (List.Perm.refl [])) := by
  apply program_rumpf_of_lowerFn (ens := .tru) (req := .tru)
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
private theorem acyclicP_rumpf : acyclicP.rumpf 0 = .ret .empty (List.Perm.refl []) := by
  apply program_rumpf_of_lowerFn (ens := .tru) (req := .tru)
  rfl

set_option maxRecDepth 100000 in
/-- The actual exported component is the widened entry parameter, with its original footprint proof. -/
private theorem countM_mass : countM.mass 0 =
    [⟨1, .widen (by decide) (by decide) (.var .here), rfl⟩] := by rfl

set_option maxRecDepth 100000 in
private theorem mutualM_mass_zero : mutualM.mass 0 =
    [⟨1, .widen (by decide) (by decide) (.var .here), rfl⟩] := by rfl

set_option maxRecDepth 100000 in
private theorem mutualM_mass_one : mutualM.mass 1 =
    [⟨1, .widen (by decide) (by decide) (.var .here), rfl⟩] := by rfl

set_option maxRecDepth 100000 in
private theorem nonTailM_mass : nonTailM.mass 0 =
    [⟨1, .widen (by decide) (by decide) (.var .here), rfl⟩] := by rfl

end Gabbro.Grammatik.Parser.Measures.Fixtures
