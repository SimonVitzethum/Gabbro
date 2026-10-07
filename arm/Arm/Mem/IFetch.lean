/-
  File:      Arm/Mem/IFetch.lean
  Subject:   Minimal instruction-fetch ordering for self-modifying and freshly
             loaded code: fetch events, DC CVAU / DSB / IC IVAU / ISB events,
             and the architectural maintenance recipe as a decidable predicate.
  Model:     the Arm ARM cache-maintenance recipe (write code; DC CVAU;
             DSB; IC IVAU; DSB; ISB) and ISB context synchronisation, from the
             agent's knowledge of the published architecture, NOT a measured
             copy (no Arm ARM text on this machine). Extends the frozen
             `Event.lean` vocabulary WITHOUT editing it: own event wrapper
             over the shared `Rel`.
-/
import Arm.Mem.Event

namespace Arm

/-- One step of the instruction-side story: a code write, one maintenance
    operation, or an instruction fetch. `dsb`/`isb` carry no address. -/
inductive IMntKind where
  | writeCode
  | dcCvau
  | dsb
  | icIvau
  | isb
  | fetch
  deriving DecidableEq, Repr

/-- One instruction-side event. `addr` is the code address (0 for barriers). -/
structure IFEv where
  id   : Nat
  core : CoreId
  kind : IMntKind
  addr : Addr
  deriving DecidableEq, Repr

/-- A candidate instruction-side execution: events plus program order, which
    is `po` per core, TRANSITIVELY closed (same convention as `Exec`). -/
structure IFExec where
  evs : List IFEv
  po  : Rel
  deriving Repr

/-- The kind of the event with `id`, if present. -/
def kindOf (x : IFExec) (i : Nat) : Option IMntKind :=
  (x.evs.find? fun e => e.id == i).map fun e => e.kind

/-- Event `i` has kind `k` (false if missing). -/
def hasKind (x : IFExec) (k : IMntKind) (i : Nat) : Bool :=
  match kindOf x i with
  | some k' => k' == k
  | none => false

/-- `po` contains the pair `(a, b)`. -/
def poHas (x : IFExec) (a b : Nat) : Bool :=
  x.po.any fun p => p.1 == a && p.2 == b

/-- Events `i` and `j` target the same code address (false if missing). -/
def sameCodeAddr (x : IFExec) (i j : Nat) : Bool :=
  match x.evs.find? (fun e => e.id == i), x.evs.find? (fun e => e.id == j) with
  | some a, some b => a.addr == b.addr
  | _, _ => false

/-- Completed data-side maintenance at one address: DC CVAU, then a DSB,
    then IC IVAU, in `po` order. This is the "earlier completed cache
    maintenance" that a later ISB makes visible to instruction fetches
    (ISB context synchronisation). -/
def maintDone (x : IFExec) (dc ic : Nat) : Bool :=
  hasKind x .dcCvau dc && hasKind x .icIvau ic && sameCodeAddr x dc ic &&
    x.evs.any fun d =>
      hasKind x .dsb d.id && poHas x dc d.id && poHas x d.id ic

/-- Architectural guarantee: the fetch `f` observes the code write `w`.
    True exactly for the full recipe at one address:
    write -po-> DC CVAU -po-> DSB -po-> IC IVAU -po-> DSB -po-> ISB -po->
    fetch. `false` does NOT mean "the fetch is stale" — it means a stale
    fetch is architecturally ALLOWED (Arm leaves the outcome free without
    the recipe, so the predicate must not resolve it to one value). -/
def fetchSeesWrite (x : IFExec) (w f : Nat) : Bool :=
  hasKind x .writeCode w && hasKind x .fetch f && sameCodeAddr x w f &&
    x.evs.any fun dc => x.evs.any fun ic => x.evs.any fun d2 =>
      x.evs.any fun ib =>
        maintDone x dc.id ic.id &&
        poHas x w dc.id && poHas x ic.id d2.id &&
        hasKind x .dsb d2.id && hasKind x .isb ib.id &&
        poHas x d2.id ib.id && poHas x ib.id f

/-- The full architectural recipe on one core at address `A`: write the
    code, clean it (DC CVAU), order (DSB), invalidate the instruction cache
    (IC IVAU), order (DSB), synchronise context (ISB), then fetch. -/
def xFullRecipe : IFExec :=
  { evs := [⟨0, 0, .writeCode, 0#64⟩, ⟨1, 0, .dcCvau, 0#64⟩,
            ⟨2, 0, .dsb, 0#64⟩, ⟨3, 0, .icIvau, 0#64⟩,
            ⟨4, 0, .dsb, 0#64⟩, ⟨5, 0, .isb, 0#64⟩,
            ⟨6, 0, .fetch, 0#64⟩]
    po := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6),
           (1, 2), (1, 3), (1, 4), (1, 5), (1, 6),
           (2, 3), (2, 4), (2, 5), (2, 6),
           (3, 4), (3, 5), (3, 6), (4, 5), (4, 6), (5, 6)] }

/-- With the full recipe the fetch is guaranteed to see the new code. -/
theorem recipe_complete_sees_new :
    fetchSeesWrite xFullRecipe 0 6 = true := by decide

/-- Planted case: the DC CVAU is missing (clean never happens). -/
def xDropDc : IFExec :=
  { evs := [⟨0, 0, .writeCode, 0#64⟩, ⟨1, 0, .dsb, 0#64⟩,
            ⟨2, 0, .icIvau, 0#64⟩, ⟨3, 0, .dsb, 0#64⟩,
            ⟨4, 0, .isb, 0#64⟩, ⟨5, 0, .fetch, 0#64⟩]
    po := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5),
           (1, 2), (1, 3), (1, 4), (1, 5),
           (2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (4, 5)] }

/-- Without the clean a stale fetch is allowed. -/
theorem drop_dc_allows_stale :
    fetchSeesWrite xDropDc 0 5 = false := by decide

/-- Planted case: the DSB between DC and IC is missing (clean not ordered). -/
def xDropDsb1 : IFExec :=
  { evs := [⟨0, 0, .writeCode, 0#64⟩, ⟨1, 0, .dcCvau, 0#64⟩,
            ⟨2, 0, .icIvau, 0#64⟩, ⟨3, 0, .dsb, 0#64⟩,
            ⟨4, 0, .isb, 0#64⟩, ⟨5, 0, .fetch, 0#64⟩]
    po := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5),
           (1, 2), (1, 3), (1, 4), (1, 5),
           (2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (4, 5)] }

/-- Without the first DSB a stale fetch is allowed. -/
theorem drop_dsb1_allows_stale :
    fetchSeesWrite xDropDsb1 0 5 = false := by decide

/-- Planted case: the IC IVAU is missing (stale line never invalidated). -/
def xDropIc : IFExec :=
  { evs := [⟨0, 0, .writeCode, 0#64⟩, ⟨1, 0, .dcCvau, 0#64⟩,
            ⟨2, 0, .dsb, 0#64⟩, ⟨3, 0, .dsb, 0#64⟩,
            ⟨4, 0, .isb, 0#64⟩, ⟨5, 0, .fetch, 0#64⟩]
    po := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5),
           (1, 2), (1, 3), (1, 4), (1, 5),
           (2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (4, 5)] }

/-- Without the invalidate a stale fetch is allowed. -/
theorem drop_ic_allows_stale :
    fetchSeesWrite xDropIc 0 5 = false := by decide

/-- Planted case: the DSB between IC and ISB is missing (invalidate not
    ordered before context synchronisation). -/
def xDropDsb2 : IFExec :=
  { evs := [⟨0, 0, .writeCode, 0#64⟩, ⟨1, 0, .dcCvau, 0#64⟩,
            ⟨2, 0, .dsb, 0#64⟩, ⟨3, 0, .icIvau, 0#64⟩,
            ⟨4, 0, .isb, 0#64⟩, ⟨5, 0, .fetch, 0#64⟩]
    po := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5),
           (1, 2), (1, 3), (1, 4), (1, 5),
           (2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (4, 5)] }

/-- Without the second DSB a stale fetch is allowed. -/
theorem drop_dsb2_allows_stale :
    fetchSeesWrite xDropDsb2 0 5 = false := by decide

/-- Planted case: the ISB is missing (completed maintenance exists but no
    context synchronisation makes it visible to the fetch). -/
def xDropIsb : IFExec :=
  { evs := [⟨0, 0, .writeCode, 0#64⟩, ⟨1, 0, .dcCvau, 0#64⟩,
            ⟨2, 0, .dsb, 0#64⟩, ⟨3, 0, .icIvau, 0#64⟩,
            ⟨4, 0, .dsb, 0#64⟩, ⟨5, 0, .fetch, 0#64⟩]
    po := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5),
           (1, 2), (1, 3), (1, 4), (1, 5),
           (2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (4, 5)] }

/-- Without the ISB a stale fetch is allowed, even though the maintenance
    itself completed: `maintDone` holds while `fetchSeesWrite` fails. -/
theorem drop_isb_allows_stale :
    fetchSeesWrite xDropIsb 0 5 = false := by decide

/-- The ISB case isolates context synchronisation: maintenance completed. -/
theorem drop_isb_maintenance_completed :
    maintDone xDropIsb 1 3 = true := by decide

end Arm

/-
CUTS: full recipe guarantees the new fetch; each single dropped step allows
a stale fetch (`false` = allowed, never one observed value). NOT modelled:
multicore visibility of maintenance (all fixtures single-core), PoU vs PoC
distinction, shareability domains of the DSBs, instruction-cache line size
and associativity effects, exceptions/interrupts between the steps.
-/

#print axioms Arm.recipe_complete_sees_new
#print axioms Arm.drop_dc_allows_stale
#print axioms Arm.drop_dsb1_allows_stale
#print axioms Arm.drop_ic_allows_stale
#print axioms Arm.drop_dsb2_allows_stale
#print axioms Arm.drop_isb_allows_stale
#print axioms Arm.drop_isb_maintenance_completed
