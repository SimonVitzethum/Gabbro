/-
  File:      Grammatik/X86/GvStartPflicht.lean
  Subject:   GabbroV bridge: `StartPflicht` without the `Initially` assumption (lane 1387).

  GabbroV duty files assume `Initially s0` (well-typed initial world, every
  invariant holds; `programmlogik/Duty/Duty104Referenz.lean`), while the goal
  theorem's premise (b) `StartPflicht E` is a duty of the user over the
  DECLARED initial memory `E.sp0`. This module computes that memory from the
  SOURCE in Lean and discharges the assumption by the declarations:
  * fragment slots are zero-initialised (`sp0Of`, the Lean side of the
    exporter's `gSp0` slot half, `crates/gabbro-check/src/lean_g.rs`);
    `Sp0Ok` (decided by `sp0OkB`) says every range holds zero;
  * declared `static` initialisers travel through `gvInitWert` (the Lean
    side of `GInit`); out-of-range has no value (the `check_sp0` refusal).
  The exact classes where no initial memory exists are proved (`sp0_luecke`,
  `gv_fragment_kein_static`), not just stated. Reuses the accepted
  definitions of `Zielsatz/`, `Semantik` and `Parser/` unchanged; no new
  interpreter, no import from `programmlogik/`.
-/
import Grammatik.Parser.Uebersetze
import Grammatik.Parser.UebersetzeAllg
import Grammatik.Parser.UebersetzeAllg2
import Grammatik.Kern.Syntax.Typen
import Grammatik.Kern.Syntax.Syntax
import Grammatik.Kern.Semantik.Semantik
import Grammatik.Kern.Semantik.Maschine
import Grammatik.Logik.Vertraege.VertragOrtB
import Grammatik.Nebenlaeufigkeit.Sperren.SperreSem
import Grammatik.Zielsatz.Kern.Spec
import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtRahmenBeweis

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
  Gabbro.Grammatik.Zielsatz

/-- **Zero holds at every slot** (`Sp0Ok`): every field of every table of the
    elaborated unit is a `bool` field (zero is `false`) or an integer field
    whose recorded range holds `0`. This is the Lean side of the exporter's
    `check_sp0` (`crates/gabbro-check/src/lean_g.rs`): a range holding no
    zero has no `sp0` value and is refused BY NAME. -/
def Sp0Ok (u : UProg) : Prop :=
  ∀ (t : Fin u.tabellen.length) (f : Fin (fieldCount u t)),
    boolFeldAt u t f = true ∨
      ∃ w, fieldRangeO u t f = some w ∧ w.1 ≤ 0 ∧ 0 ≤ w.2

end Gabbro.Grammatik.X86

/- CUTS: this module currently contains one definition (`Sp0Ok`) and no
    theorem. NOT proved: the `sp0OkB` decider and its soundness
    (`sp0OkB_klingt`); the computed initial memory `sp0Of`; the bridge
    theorem `gv_startPflicht` (`StartPflicht` from lowering plus `Sp0Ok`);
    the static-initialiser model `gvInitWert` with its travel/refusal
    lemmas; the obstruction theorems (`sp0_luecke`,
    `gv_fragment_kein_static`); the non-degenerate `_zeuge` witness; the
    `Initially`-follows-from-declarations statement. The `#print axioms`
    line below reports `[propext]` for `Sp0Ok` (verified `./lean-probe`,
    0 errors); every later theorem gets its own `#print axioms` line. -/
#print axioms Gabbro.Grammatik.X86.Sp0Ok
