/-
  File:      Grammatik/ZielOrtGanz.lean
  Subject:   THE ONE GOAL THEOREM `ziel_ort_ganz` -- callee frames, registers
             and `awaits`, declared axiom ensures, AND the stuck hole closed:
             the user obligation now excludes every `logik` outcome of the
             body, and the conclusion says that no reachable machine is
             stuck at a `logik` check of G.

  The hole (verdict `messung/URTEIL-OPUS-2026-09-13.md`, probe A): machine G
  checks a loop invariant (`travNext`/`travDone`/`ewigWeiter`/
  `dannLeaveTrav`) and a `state` pre-state (`uebergang`, a leaf that `blatt`
  fires only on an `ok` outcome) and BLOCKS where the check fails. The old
  obligation `KoerperGutR` constrains `zurueck` outcomes and the
  `vorbedingung` outcome only; a body that runs into `logik schleife` meets
  it vacuously, G stops before any return is logged, and `VertragAmOrtG`
  holds on every reachable machine -- while the emitted C, which does not
  check invariants, runs on and returns with every `ensures` false.

  The repair keeps the obligation a SEQUENTIAL per-function triple against
  handlers (the user's own logic): `KeineLogik` asks that the body, run from
  its `requires` against any frame-respecting handler that itself answers
  no `logik` outcome (`OhneLogik`), never ends in a `logik` outcome. Since a
  body's own `logik` outcomes are exactly the loop invariant (`schleife`)
  and the pre-state (`vorzustand`) -- `nachbedingung`, `invariante`,
  `abstieg` and `vorbedingung` arise only in a CALL (`rufAt`, `torRuf`),
  i.e. in the handler -- this is "the loop invariants hold where they are
  checked and every transition finds its pre-state", nothing more. The
  replay then gives: the head's sequential prediction is never a `logik`
  outcome (`kopfR_keineLogik`), and at every `logik` check of G the check
  passes at the machine world (`KeinLogikHaltG`) and the rule fires
  (`schritt_an_pruefung`, given `HeldGenau` of the head).

  Why the obligation and not the machine: making G continue past a false
  invariant (as the emitted C does) would leave the replay without the
  invariant the user's loop reasoning needs, and every adequacy file would
  have to follow a G that no longer means what the sequential semantics
  means. Keeping G's checks and asking the user to prove the invariants
  they wrote turns each check into a theorem: on G's runs the check always
  passes, so the C's not checking it is harmless there.
-/

import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtGanz.T1
import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtGanz.T2
import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtGanz.T3
