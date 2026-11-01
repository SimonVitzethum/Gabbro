/-
  File:      Grammatik/Speichermodell/AtomarSem.lean
  Subject:   THE SEQUENTIAL SEMANTICS WITH A HAVOC AT EVERY SHARED ATOMIC READ -- the "rely"
             of OFFEN O25 (Opus lane O25b, 2026-09-26). Standalone: `Zielsatz/Spec.lean` does
             not import this file.

  WHAT THE USER WOULD PROVE AGAINST. `execStmtH` (SperreSem.lean) runs a body alone; a lock
  take lets the environment move the protected carriers (`Umwelt`, `HavocOk`). On a program
  whose threads race on an UNGUARDED atomic (a flag, a counter, a per-core cell), another
  thread may change the atomic between any two reads, and machine W may even present an older
  message (`w_nicht_sc`). So a read of such an atomic may return ANY value. `execStmtHA` is
  `execStmtH` with ONE change: every read (`World.lese`, the only place a statement reads
  memory) goes through an ATOMIC ENVIRONMENT `A : AUmwelt D`, a function of the read list and
  the world after the read events, which may replace the value of every read carrier in a set
  `T` -- and nothing else (`HavocA T A`). The obligation quantifies over every such `A`
  (`KoerperGutSA`, Zielsatz/AtomarPflicht.lean): the user proves the body against every value
  another thread or the weak memory can show at a shared atomic read.

  WHY THE HAVOC SITS AT `lese`. A read list `X` of a step is recorded as read events in the
  trace, so the world after them has a trace strictly longer than any earlier one whenever `X`
  is not empty. A havoc that may change only carriers of `X` is the identity when `X` is empty
  (`HavocA`), so every POINT at which the environment may act has a fresh key -- the replay can
  record the machine's presented value there as a function of the key, as it records an
  acquire (`UEintrag`) and a callee answer.

  `awaits g` tests visibility AFTER its read of `g` here (`execStmtH` tests before): with a
  havoc the test must see the value the read returns, and under `RegLokal` (visibility depends
  on `g` only) the two orders agree (`Block.execHA_frei`).

  PROVED HERE: `leseA_frei` (a havoc over a read list outside `T` is no havoc) and the
  EMBEDDING `Stmt.execHA_frei`/`Block.execHA_frei`/`Endblock.execHA_frei`: on a body none of
  whose reads is in `T`, `execStmtHA` IS `execStmtH` for every havoc in the class; in
  particular for `T` empty or the identity havoc (`execEndHA_id`).
-/
module

public import Grammatik.Speichermodell.Atomar.AtomarSem.Teil1
public import Grammatik.Speichermodell.Atomar.AtomarSem.Teil2
