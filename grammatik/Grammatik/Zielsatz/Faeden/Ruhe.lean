/-
  File:      Grammatik/Zielsatz/Ruhe.lean
  Subject:   The checker's facts and the admissible starts on `P.mitRuhe`
             (the program with the runtime's idle root, MitRuhe.lean).

  * `akzeptiertSpec_mitRuhe`: every field of `AkzeptiertSpec` for `P` gives
    the same field for `P.mitRuhe` (functions `fsRuhe fs`, starts
    `wsRuhe ws`, lock invariants `S.mitRuhe`).
  * `akzeptiert_mitRuhe`: the checker's Bool on `P.mitRuhe` follows from the
    Bool on `P`.
  * `ruhig_mitRuhe`: the root `none` is an idle start of `P.mitRuhe`.
  * `startZulaessig_mitRuhe`: "declared starts on their threads, the idle
    root on every other thread" is an admissible start of `P.mitRuhe`, given
    the starts' `requires` and the lock invariants at the start memory;
    `startZulaessig_ruhe`: the idle root on EVERY thread is admissible as
    soon as some memory meets the lock invariants.
  * The runtime's start of Spec (`Laufzeit`, A4; 2026-09-15):
    `laufzeit_initRuhe`/`laufzeit_voll` (the runtime's exact start,
    `initRuhe E.starts`, meets it -- since fix lane F10 with no side
    condition: a routine on two threads is declared twice); `laufzeit_ruhe` (the root everywhere: the
    run class is never empty); `laufzeit_nur_erklaert` (a user function runs
    only if declared); `laufzeit_ohne_starts` (no declared start: the root
    on every thread).
-/
module

public import Grammatik.Zielsatz.Faeden.Ruhe.Teil1
public import Grammatik.Zielsatz.Faeden.Ruhe.Teil2
