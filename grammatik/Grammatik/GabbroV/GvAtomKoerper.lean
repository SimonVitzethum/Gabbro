/-
  File:      Grammatik/GabbroV/GvAtomKoerper.lean
  Subject:   GabbroV: atomic-bearing bodies whose rely duty follows from a
              per-body flag duty (agent 05, follow-up).

  Agent 1385's accepted obstruction (`gv_rely_braucht_atomfreiheit`): without
  atomic-freedom the transfer from the plain duty to the arbitrary-value duty
  FAILS (`hP`/`zaehlB`: sequential duty holds, rely duty fails at `aFuenf`).
  THIS FILE proves the next step: for bodies of the `hP` shape -- one store
  of a shared atomic into a slot, one flag test over it, both branches
  covered -- the duty over ARBITRARY atomic values (`KoerperGutSA`) follows
  from a duty the person states per body (pinned-memory runs, one per
  read site, with a case split over the test outcome).

  Design (all engines reused, nothing duplicated): `istFlagKoerper` is the
  decidable shape predicate; `flagKoerperLesen` computes every orte outside
  the two pinned reads; `pinA` answers those two reads from two fixed
  memories (in `HavocA T` by `mischT`); `FlagPersonenPflicht` is the
  person's duty over pinned runs; `flagKoerper_relyDuty` is the transfer.
-/
module

public import Grammatik.GabbroV.GvAtomKoerper.Teil1
public import Grammatik.GabbroV.GvAtomKoerper.Teil2
