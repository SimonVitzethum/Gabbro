# Owner application: the producer path (`eigner` theorems, D026)

Lane p23. `SYNTAX.md:1625` booked the state: the Lean theorems about `eigner`
are true but unapplied, and until the producer stands `D026` is the whole
implementation. This note records the application -- what now stands, where,
and what still waits.

## What was applied

`eigner_nie_erzeugt` (`Syntax.lean:149`): no signature produces an owner mark.
Two new sections apply it to the producer path, one per level. Both are
standalone (no imports, no `sorry`) and touch only `eigner`/`owner` definitions;
`Bau`, the `Tab`/`Glob` split and the world-partition regions are other waves'
and are read, never modified.

- `grammatik/Grammatik/Typen.lean` §5 (lines 349-437, value level). `OwnerSig`
  mirrors one signature's consumed/produced marks with the never-produced
  theorem as a premise; `ownerNachRuf` mirrors the call step `nachSig`.
  Proved: `eigner_nachRuf_aus_anfang` (an owner mark after the call was held
  before it), `eigner_lauf_aus_anfang` (along a run, from the start),
  `eigner_aus_leer_nie` (from empty holdings, never -- the sentence form of
  the `D026` refusal). Axioms: `propext` only.
- `grammatik/Grammatik/Geteilt.lean` §9 (lines 516-594, sharing level).
  `OwnerAnfang` names the owner marks per carrier, the entry's initial
  holdings (the `Signaturkopf` answer of `Marken.lean` cut C4) and the produced
  marks per function, with the never-produced theorem as a premise. Proved:
  `eigner_nie_in_welt` (the reachable producer path carries no owner mark),
  `eigner_erster_aus_anfang` (the first mark comes from the entry),
  `eigner_ungeteilt_ein_faden` (`geteilt_treu` for the owner-guarded,
  unshared carrier). Axioms: `propext`/`Quot.sound`, plus `Classical.choice`
  on the third -- the same footprint as the existing `geteilt_treu`.

## What the probes pin

- `beispiele/gift/778-eigner-mit-erzeuger.gab` -- an `owner` table beside a
  function whose signature RETURNS the mark. Falls with `D026` and nothing
  else (5 items, 1 error). A return type is not an initial holding.
- `beispiele/gift/779-eigner-mit-haltung.gab` -- the same table beside a body
  that holds the mark through the whole discipline (produced once, consumed
  once). Falls with `D026` and nothing else (7 items, 1 error). The refusal
  fires by name, not by use.
- Control: `gift/694` still falls with `D026` alone (3 items, 1 error).

Measured 2026-09-11 against the unchanged checker
(`target/debug/gabbro`, built locally -- server unreachable through the jump
host, `free -g` beside the run: 31 total, 11 available).

## What still waits

`D026` stands. The application names WHERE the first mark must come from (the
entry's initial holdings) but does not wire it: instantiating `OwnerSig` /
`OwnerAnfang` against a real `Deklaration` (the `D.eigner` fold, the
`Signatur.anfang` holdings) is downstream work, as is the `own`-sugar
producer story (`SYNTAX.md:370`). Until then the refusal is the honest answer,
and these two probes hold its two neighbours.
