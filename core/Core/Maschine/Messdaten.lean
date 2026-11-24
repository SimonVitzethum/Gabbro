module


@[expose] public section

namespace Gabbro.Core.Beobachtung


/-- Timing declarations identify the required hardware duration row and the cost of the fallback. -/
structure Zeitdeklaration where
  zeile : Nat
  frist : Nat
  lateKosten : Nat

/-- The active body, its completed deadline check, or the fallback selected by that check.
    Indices refer to hardware cuts, with the first cut identifying this activation. -/
inductive Zeitphase where
  | rumpf
  | rechtzeitig (geprueft : Nat)
  | late (geprueft : Nat)
  deriving DecidableEq

structure Zeitmarke where
  block : Nat
  anfang : Nat
  phase : Zeitphase

/-- Elaborated declarations and layout interpretation. A missing optional resource bound is open.
    The form implementing a timed block exposes its live activations in the local state. -/
structure Schrankendaten (L Lok : Type) where
  kosten : Option Nat := none
  speicher : Option Nat := none
  stapel : Option Nat := none
  halten : L → Option Nat := fun _ => none
  stapelTiefe : Lok → Nat := fun _ => 0
  zeit : Nat → Option Zeitdeklaration := fun _ => none
  zeitstand : Lok → List Zeitmarke := fun _ => []

def Schrankendaten.leer : Schrankendaten L Lok := {}

end Gabbro.Core.Beobachtung
