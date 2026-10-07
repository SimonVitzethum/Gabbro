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

end Arm

/-
CUTS: skeleton; recipe predicate and fixtures follow.
-/
