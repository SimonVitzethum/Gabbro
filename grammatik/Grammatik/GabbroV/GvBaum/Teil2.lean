module

public import Grammatik.Kern.Semantik.Semantik
public import Grammatik.GabbroV.GvTreeParent
public import Grammatik.GabbroV.GvStore
public import Grammatik.GabbroV.GvVerkettung
public import Grammatik.GabbroV.GvBaum.Teil1

@[expose] public section

namespace Gabbro.Grammatik.GabbroV
open Gabbro.Grammatik
open Gabbro.Grammatik.GabbroV
variable {D : Deklaration}

theorem baumWurzel_hat_kind :
    ((kantenBild baumD baumWelt () .Kind hfKind 0).map Zahl.n) = some 1 := by
  decide

/-- Non-leaf-first run: victim 0 (cutting off the subtree), then 1. -/
def laufB : Nat → World baumD
  | 0 => baumWelt
  | 1 => ((baumWelt.storeSlot () 0 .Belegt false).storeSlot () 0 .Naechstes none).storeSlot
    () 0 .Kind none
  | _ => ((baumWelt.storeSlot () 0 .Belegt false).storeSlot () 0 .Naechstes none).storeSlot
    () 0 .Kind none

/-- Planted failure: after cutting the root, node 1 is unreachable --
    the traverse cannot reach its next victim, so the call obligation
    has no premise to fire on. A deletion of a non-leaf is not covered. -/
theorem baumSchnitt_widerlegt :
    erreichtProj baumD (laufB 1) () .Naechstes hfNaechstes 0 1 = false := by
  decide

/-
   CUTS: what is not proved.
   - Proved: `baumD` (3 slots, 3 edge fields + occupancy); occupancy
     commutation both shapes; the `TreeState` record `baumBild`; the
     frame-lift `frame_ausser_opfer`; the generic run lift with link
     corollaries; the conditional call obligation
     (`blatt_rufsicher_bedingt`); the leaf-first witness
     (`baumBlatt_zeuge`: victim occupied at call time) and the
     non-leaf planted failure (`baumSchnitt_widerlegt`: cutoff victim
     unreachable, plus `baumWurzel_hat_kind` recording the non-leaf).
   - Only stated: `baumWelt`/`baumLauf`/`laufB` fixture shapes.
   - Not modelled: per-step `elternKonsistent` preservation across
     relink stores (the open relink work -- the lifts take it as an
     explicit premise); runs past the contract bound in one go;
     `GvTraversal`/`GvSplits`/`GvParserFragment` reconciliation.
   - No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` anywhere; every
     premise is used; no premise has type `Prop` itself.
-/

#print axioms frame_ausser_opfer
#print axioms blatt_rufsicher_bedingt
#print axioms baumBlatt_zeuge

end Gabbro.Grammatik.GabbroV
