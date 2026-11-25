/-
  File:      core/Core/Ziel/Korrektheit/Beweise/ProtokollAbschluss.lean
  Subject:   CLOSURE OF THE PROTOCOL RUN PROOFS. The two pinned run statements are obtained by applying the
             conditional run theorems to the proved step preservation statement. The start statement
             `ProtokollStartGutAussage` is already proved as `protokoll_start_gut` in `ProtokollLauf.lean`;
             nothing here re-proves or changes it.

  Both implications are one-line instantiations: `protokoll_gut_im_lauf_aus` and
  `ideal_protokoll_gut_im_lauf_aus` take `ProtokollSchrittErhaeltAussage` as their only premise, and
  `protokoll_schritt_erhaelt` discharges it. The statements are left exactly as pinned in `Maschine.lean`.
-/
module

public import Core.Ziel.Korrektheit.Beweise.ProtokollLauf
public import Core.Ziel.Korrektheit.Beweise.ProtokollSchritt

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core Maschine

/-- THE INVARIANTS HOLD AT EVERY CUT OF EVERY IMPLEMENTATION RUN (`ProtokollGutImLaufAussage`): the conditional
    run theorem applied to the proved step preservation statement `protokoll_schritt_erhaelt`. -/
theorem protokoll_gut_im_lauf : ProtokollGutImLaufAussage := by
  exact protokoll_gut_im_lauf_aus protokoll_schritt_erhaelt

/-- THE INVARIANTS HOLD AT EVERY CUT OF EVERY IDEAL RUN (`IdealProtokollGutImLaufAussage`): the conditional ideal
    run theorem applied to the same proved step preservation statement. -/
theorem ideal_protokoll_gut_im_lauf : IdealProtokollGutImLaufAussage := by
  exact ideal_protokoll_gut_im_lauf_aus protokoll_schritt_erhaelt

end Gabbro.Core.Ziel.Korrektheit
