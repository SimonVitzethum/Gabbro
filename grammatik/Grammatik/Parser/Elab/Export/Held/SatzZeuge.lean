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
public import Grammatik.Logik.Fortschritt.Halten.Ruhe
public import Grammatik.Logik.Fortschritt.Halten.Haltezeit
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
  have projected := congrArg (Option.map (fun checks : Bool × Bool × Bool => checks.1)) holds_zeuge
  simpa only [Option.map_map, Function.comp_def, Option.map_some] using projected

/-- **The section bound is not vacuous.** On the lowered fixture unit, whose lock `L`
    declares a bound of 100, every function body satisfies the section property. -/
theorem holds_sectionsE_zeuge {r : Programm (declOf sectionUnit) × List (declOf sectionUnit).Fn}
    (hr : (lowerAllg sectionUnit).toOption = some r) (g : Fin sectionUnit.fns.length) :
    sectionsOkE (boundOf (Tafel.von _ [("L", 100)]) sectionUnit) (kostenEpilog r.1 g)
      (CostBinding.decl (Tafel.von _ []) sectionUnit)
      (fun x => (CostBinding.costOf (Tafel.von _ []) sectionUnit x).isSome)
      0 (r.1.rumpf g) := by
  exact holds_sectionsE _ _ _ _ _ (by
    have h := holds100_zeuge
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq] at h
    exact h) g

/-- **The existing section fixture discharges the waiting check from exporter acceptance.**
    The hold check really inspects a section (and refuses the bound 1); K001 is accepted with
    an empty cost table because that section calls no function. No `haltPasst` computation
    replaces the connection theorem here. -/
theorem holds_haltPasst_zeuge {r : Programm (declOf sectionUnit) × List (declOf sectionUnit).Fn}
    (hr : (lowerAllg sectionUnit).toOption = some r) :
    haltPasst r.1 0 (fun _ => 100) (CostBinding.decl (Tafel.von _ []) sectionUnit)
      (List.finRange sectionUnit.fns.length) (CostBinding.members (Tafel.von _ []) sectionUnit) = true := by
  have hh := holds100_zeuge
  rw [hr] at hh
  simp only [Option.map_some, Option.some.injEq] at hh
  have hc : CostBinding.holds (Tafel.von _ []) sectionUnit r.1 0 = true := by rfl
  have total : ∀ L, boundOf (Tafel.von _ [("L", 100)]) sectionUnit L = some 100 := by
    intro L
    have index : L = ⟨0, by decide⟩ := by
      apply Fin.ext
      change L.val = 0
      have bound := L.isLt
      change L.val < 1 at bound
      omega
    subst L
    simp [boundOf, lockAt, sectionUnit, Tafel.finde, Tafel.von,
      strEq_eq_schnell, strEqSchnell]
  exact holds_haltPasst _ _ _ r.1 0 (fun _ => 100) total hc hh

/-- The same accepted fixture meets the runtime-program check without checking `mitRuhe`
    by computation: the source acceptance above and the generic idle-root lift suffice. -/
theorem holds_haltPasst_mitRuhe_zeuge
    {r : Programm (declOf sectionUnit) × List (declOf sectionUnit).Fn}
    (hr : (lowerAllg sectionUnit).toOption = some r) :
    haltPasst r.1.mitRuhe 0 (fun _ => 100)
      (fun g => g.elim 0 (CostBinding.decl (Tafel.von _ []) sectionUnit))
      (fsRuhe (List.finRange sectionUnit.fns.length))
      ((CostBinding.members (Tafel.von _ []) sectionUnit).map some) = true :=
  haltPasst_mitRuhe _ _ _ _ _ _ (holds_haltPasst_zeuge hr)

/-- **Joint, non-vacuous exporter witness.** The fixture really lowers, and the same
    lowered program satisfies the source and runtime checks derived above. -/
theorem accepted_hold_fixture :
    ∃ r : Programm (declOf sectionUnit) × List (declOf sectionUnit).Fn,
      (lowerAllg sectionUnit).toOption = some r ∧
      haltPasst r.1 0 (fun _ => 100) (CostBinding.decl (Tafel.von _ []) sectionUnit)
        (List.finRange sectionUnit.fns.length) (CostBinding.members (Tafel.von _ []) sectionUnit) = true ∧
      haltPasst r.1.mitRuhe 0 (fun _ => 100)
        (fun g => g.elim 0 (CostBinding.decl (Tafel.von _ []) sectionUnit))
        (fsRuhe (List.finRange sectionUnit.fns.length))
        ((CostBinding.members (Tafel.von _ []) sectionUnit).map some) = true := by
  cases lowered : (lowerAllg sectionUnit).toOption with
  | none =>
    have hh := holds100_zeuge
    rw [lowered] at hh
    cases hh
  | some r =>
    exact ⟨r, rfl, holds_haltPasst_zeuge lowered, holds_haltPasst_mitRuhe_zeuge lowered⟩

/-- On the existing exported section fixture, hold time follows with the syntactic premise
    discharged solely by acceptance. The remaining premises are precisely the run-side
    premises of `haltezeit_aus`; there is no assumed hold time. -/
theorem holds_haltezeit_zeuge
    {r : Programm (declOf sectionUnit) × List (declOf sectionUnit).Fn}
    (hr : (lowerAllg sectionUnit).toOption = some r)
    {O : Orakel (declOf sectionUnit)} (R : PlanLauf r.1 O 0)
    (hO : GutO O) (hSt : StufenM r.1) (sp : Speicher (declOf sectionUnit))
    (init : Faden → Σ f : (declOf sectionUnit).Fn, Env (declOf sectionUnit) ((declOf sectionUnit).params f))
    (empty : ∀ t, (declOf sectionUnit).haelt (init t).1 = [])
    (start : RufErreichbarG r.1 O 0 (RufStartG r.1 sp init) (R.M 0)) :
    Haltezeit R (haltSchranke (List.finRange sectionUnit.locks.length) (fun _ => 100))
      (haltSchranke (List.finRange sectionUnit.locks.length) (fun _ => 100)) :=
  haltezeit_aus R hO hSt sp init empty start (fun L => List.mem_finRange L)
    (fun g => List.mem_finRange g) (holds_haltPasst_zeuge hr)

end Gabbro.Grammatik.Parser.HeldBinding

#print axioms Gabbro.Grammatik.Parser.HeldBinding.holds_haltPasst_zeuge
#print axioms Gabbro.Grammatik.Parser.HeldBinding.holds_haltPasst_mitRuhe_zeuge
#print axioms Gabbro.Grammatik.Parser.HeldBinding.holds_haltezeit_zeuge
#print axioms Gabbro.Grammatik.Parser.HeldBinding.accepted_hold_fixture
