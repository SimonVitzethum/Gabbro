/-
  File:      Grammatik/X86/OptCoalesceMove.lean
  Subject:   Copy coalescing rule lemma (lane 880).

  DESIGN section 7 row "Layout / allocation" + section 7 example 1 + §3 text:
  copies coalesce ONLY under recomputed avail + dominance (§7 example 1:
  `v1 = add w64 a b; v2 = copy v1; v3 = add w64 v2 c` drops the copy with
  premise avail + dominance + width); certificate is the layer-A local
  rewrite record plus layer-B recomputed analysis citations; the failure
  case "address-taken spill via call arg" refuses.

  Stated over the REUSED canonical vocabulary (`Typen`, `Syntax`,
  `Semantik`, `ReferenzB`, `X86.Typen`, `X86.Wort`): no second IR, no
  second evaluator, no per-program rule. The single accepted source model
  (`Syntax`/`Semantik` `exec`) is the reference per decision 594/606.
-/
import Grammatik.Typen
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.ReferenzB
import Grammatik.X86.Typen
import Grammatik.X86.Wort

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- Layer-A local rewrite record: WHICH copy of WHICH source value, at
    one width. `quelle` is the available dominating definition `v1`,
    `kopie` the copy `v2` removed; `gleicheWeite` is the validator-decided
    same-type/same-width check (DESIGN "width"). -/
structure CoalRewrite where
  quelle : Nat
  kopie : Nat
  gleicheWeite : Bool
  deriving DecidableEq, Repr

/-- Layer-B recomputed analysis citations, re-decided by the validator
    from the block lists, never trusted from a Rust print: `avail` (the
    source value is available at the use: no redefinition between, §7
    example-1 counterexample), `dominiert` (the definition dominates the
    use), `adressGenommen` (the slot was address-taken: spill must stay),
    `callArg` (the slot travels as a call argument: callee-visible). -/
structure CoalAnalyse where
  avail : Bool
  dominiert : Bool
  adressGenommen : Bool
  callArg : Bool
  deriving DecidableEq, Repr

/-- Admission: every side condition holds. A refused OPTIONAL optimisation
    falls back to another certified translation, never to a warning. -/
def coalZulassen (rw : CoalRewrite) (an : CoalAnalyse) : Bool :=
  rw.gleicheWeite && an.avail && an.dominiert && (!an.adressGenommen) && (!an.callArg)

end Gabbro.Grammatik.X86
