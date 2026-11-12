/-
  Witnesses of the hold-bound soundness theorem on the fixture of `HeldBindingZeuge`
  (one table, one lock, one function whose body is one section of the lock):

  * `holds100_zeuge`: a declared bound of 100 holds on the lowered fixture unit
    (closed computation, as in `holds_zeuge`);
  * `holds_sectionsE_zeuge`: on that unit, every function body satisfies the section
    property of `HeldBindingSatz` -- the conclusion of `holds_sectionsE` on a
    non-degenerate fixture (a real lowered unit with a real section whose bound holds,
    and where a bound of 1 is refused, so the statement is not vacuous).
-/
module
public import Grammatik.Parser.Elab.Export.Held.Satz
public import Grammatik.Parser.Elab.Export.HeldBindingZeuge
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

namespace Gabbro.Grammatik.Parser.HeldBinding
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg
  Gabbro.Grammatik.Parser.UebersetzeAllg2

set_option maxRecDepth 100000 in
/-- A bound of 100 holds on the lowered fixture unit (closed computation). -/
theorem holds100_zeuge :
    ((lowerAllg sectionUnit).toOption.map fun r =>
      holds (Tafel.von _ [("L", 100)]) (Tafel.von _ []) sectionUnit r.1 0) = some true := by
  decide +kernel

/-- **The section bound is not vacuous.** On the lowered fixture unit, whose lock `L`
    declares a bound of 100, every function body satisfies the section property. -/
theorem holds_sectionsE_zeuge {r : Programm (declOf sectionUnit) × List (declOf sectionUnit).Fn}
    (hr : (lowerAllg sectionUnit).toOption = some r) (g : Fin sectionUnit.fns.length) :
    sectionsOkE (boundOf (Tafel.von _ [("L", 100)]) sectionUnit)
      (CostBinding.decl (Tafel.von _ []) sectionUnit)
      (fun x => (CostBinding.costOf (Tafel.von _ []) sectionUnit x).isSome)
      0 (r.1.rumpf g) := by
  exact holds_sectionsE _ _ _ _ _ (by
    have h := holds100_zeuge
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq] at h
    exact h) g

end Gabbro.Grammatik.Parser.HeldBinding
