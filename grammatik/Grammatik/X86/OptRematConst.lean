/-
  File:      Grammatik/X86/OptRematConst.lean
  Subject:   Rematerialisation rule lemma (lane 881).

  DESIGN section 7 row: local premise "constant cheap, no faulting form,
  spill weight favours remat, `bruch` = `rundeBruch`", certificate "local
  rewrite record plus recomputed analysis citations (literal shape,
  spill weight)", failure case "rematerialise a faulting form above its
  guard (div-by-zero, cross-MXCSR float); remat where the spill is
  cheaper", phase E, cost O(sites).

  What is proved here, over the REUSED canonical vocabulary (`Typen`,
  `Syntax`, `Semantik`, `ReferenzB`, `X86.Typen`, `X86.Wort`,
  `X86.CostSummary`, `X86.InvariantenOpt`): an admitted cheap constant
  recomputed at its use site instead of spilled and reloaded preserves
  the evaluated value, takes the same `execStmt`/`execEnd` outcome (no
  fault added or removed, same successor world), reads back whole
  through the canonical word, costs no more than the spill/reload pair
  it replaces, and the admitted float recomputation preserves value and
  `gleitPasst` outcome in one rounding scope. Every DESIGN failure case
  is refused by `rematZulassen`. No `ensures` is derived, no refusal
  becomes a warning, no faulting form is speculated above its guard.
-/
import Grammatik.Typen
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.ReferenzB
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.CostSummary
import Grammatik.X86.InvariantenOpt

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- Recomputed spill weight: what the rematerialised sequence costs
    against what the spill store plus reload costs. Both counts are
    recomputed by the validator, never trusted from Rust. -/
structure RematGewicht where
  rematKosten : Nat
  spillKosten : Nat
  deriving DecidableEq, Repr

/-- Validator-decided spill-weight check: remat fires only where it
    costs no more than the spill/reload pair it replaces. -/
def gewichtOk (g : RematGewicht) : Bool :=
  decide (g.rematKosten ≤ g.spillKosten)

/-- The validator-decided side conditions for one rematerialisation
    site (DESIGN section 7 row): the constant is cheap, the form cannot
    fault, the spill weight favours remat, and a float recomputation is
    the single `rundeBruch` in one rounding scope. -/
structure RematCert where
  billigOk : Bool
  keinFehler : Bool
  g : RematGewicht
  einfachGerundet : Bool
  gleicheRundung : Bool
  deriving DecidableEq, Repr

/-- Admission: every side condition holds. A refused OPTIONAL
    optimisation falls back to another certified translation (the
    spill), never to a warning. -/
def rematZulassen (c : RematCert) : Bool :=
  c.billigOk && c.keinFehler && gewichtOk c.g && c.einfachGerundet && c.gleicheRundung

/- CUTS:
    - Skeleton only: refusals, weight bound, value/word/float lemmas,
      cost expansions, the `OptRematConst_verbindung` rule lemma and its
      joint witness follow in small steps.
-/

#print axioms gewichtOk
#print axioms rematZulassen

end Gabbro.Grammatik.X86
