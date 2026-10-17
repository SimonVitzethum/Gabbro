/-
  File:      Grammatik/SperreSem.lean
  Subject:   LOCK INVARIANTS -- the sequential semantics a user proves a body
             against when shared state is protected by `locks L { … }` blocks
             (verdict item 2, `messung/URTEIL-OPUS-2026-09-13.md`).

  The shape is that of concurrent separation logic / Owicki-Gries resource
  invariants. A lock `L` protects a list of carriers `S.orte L` (each guarded
  by `L`) and carries an invariant `S.inv L` over them. In the SEQUENTIAL
  semantics of this file (`execStmtH`):
  * ACQUIRE: `locks L { body }` first lets the environment move (`U L`, an
    arbitrary `Umwelt` in the class `HavocOk S`): the protected carriers of
    `L` may take any values at which `S.inv L` holds, everything else and the
    trace stay. The body is then run from there.
  * RELEASE: when the body ends (normally, or by `leave`/`next`), `S.inv L`
    must hold; otherwise the run ends in `logik schleife` -- the invariant of
    the lock is checked at its boundary like a loop invariant.
  The user obligation stays a per-function SEQUENTIAL triple: it quantifies
  over the environment moves as it quantifies over call handlers and
  oracles (`KoerperGutS`, `SperreBeweis.lean`), and "no `logik` outcome"
  (the `KeineLogik` clause of `ziel_ort_ganz`) now also says "every release
  re-establishes the invariant".

  With the empty family (`SperrInv.leer`: no protected carriers, invariant
  `true`) every environment move is the identity and the semantics IS
  `execStmt` (`execStmtH_leer`), so today's theorem is the special case.

  This file: the family and its well-formedness (`SperrInvOk`), the class of
  environment moves (`HavocOk`), the semantics and its frame semantics
  (`weiterH`/`semH`) with the residue step lemmas, one per rule of G (copies
  of `ZielOrtVollSem.lean` §5 and `ZielOrtGeraetSem.lean` §6 for the new
  semantics, plus the acquire and release lemmas).
-/

import Grammatik.Nebenlaeufigkeit.Sperren.SperreSem.T1
import Grammatik.Nebenlaeufigkeit.Sperren.SperreSem.T2
import Grammatik.Nebenlaeufigkeit.Sperren.SperreSem.T3
import Grammatik.Nebenlaeufigkeit.Sperren.SperreSem.T4
