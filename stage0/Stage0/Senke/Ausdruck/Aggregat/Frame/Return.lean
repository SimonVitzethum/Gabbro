/- Complete return values stay internal until the shared ensures/invariant epilogue succeeds. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Frame.Layout
public import Stage0.Senke.Stopp
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR

/-- The only successful normal-return publication tail, shared by every value width. -/
def publishC (layout : FrameLayout) : List II :=
  copyWords (resultWords layout.result) layout.canonicalResult layout.internalResult ++
    [ci 1 layout.canonicalStatus 1 0, ci 2 2 layout.canonicalResult 0, ci 21 0 0 0]

/-- All normal returns use the checked epilogue and the canonical publication tail. -/
def retC (layout : FrameLayout) (source : Nat) (ens : List II) : List II :=
  copyWords (resultWords layout.result) layout.internalResult source ++ ens ++
    publishC layout

/-- Reasons bypass ensures, preserving the existing source semantics. -/
def retWhyC (layout : FrameLayout) (reason : Nat) : List II :=
  (constWords (integerEncoding (valueWords (.why layout.reasons)) reason) layout.canonicalResult).1 ++
    [ci 2 2 layout.canonicalResult 0, ci 1 layout.canonicalStatus 0 0, ci 21 0 0 0]

def retTop (layout : FrameLayout) : Nat := layout.internalStatus + 8

end Gabbro.Stage0.Senke
