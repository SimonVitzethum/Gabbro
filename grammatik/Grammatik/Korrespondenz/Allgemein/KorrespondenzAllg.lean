/-
  File:      Grammatik/KorrespondenzAllg.lean
  Subject:   T2 PROPER: ONE decidable correspondence check for EVERY program
             whose emitted forms it covers, and its soundness down to the
             callee relation at every call depth (plan
             `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` §3 item 2, stage (a)).

  Before this file the correspondence certificate was checked in two ways,
  neither generic:
  * `certOk`/`certOkG` (Korrespondenz104.lean, Schlusssatz104.lean) compare
    the printed rows with 104's rows -- a check of ONE program;
  * `gbodyOk` (Korrespondenz.lean) decides shape and hygiene of general
    rows, but the link row <-> Gabbro statement is a PROOF (`REnd`) that a
    human writes per body.

  Here the link is DECIDED. `korrOk EL fnum c P fs` walks every body of
  `P` together with its printed rows and asks, statement by statement,
  whether the row is the emitted form of that statement: the slot store
  through a pointer or at a named table (`assignDurch`, `assignSlot`), the
  store to a local (`assignVar`), the compound assignment `x op= e`
  (`setOp`, the same C statement), the store to a plain file-scope scalar
  (`assignGlob`), the direct call with its arguments (`call`), `let`
  (`bind`), the `(void)x;` of an unused parameter, and the return of an
  expression or nothing (`ret`, falling off a `void` body).
  Expressions: literals, `true`/`false`, locals, widenings, slot loads
  through a pointer or at a named table (`slot`, `durch`), table pointers
  (`ptrOf`), plain globals, the arithmetic `+ - * / %` (signed and
  unsigned), the bitwise `& | ^ << >>`, the comparisons `< <= == > >=` and
  the boolean `&& || !`. Every other form makes the Bool `false` -- a
  refusal, never an admission.

  WIDENED 2026-09-15 (`OPUS-BERICHT-KORROK.md`). The check was NARROWER
  THAN ITS OWN STOCK OF PROVED LEMMAS: `ecorr_add` … `ecorr_shr`,
  `ecorr_lt` … `ecorr_eq`, `ecorr_nicht`, `ecorr_und`, `ecorr_oder`,
  `ecorr_glob`, `scorr_assignGlob` and the four `Zucker` compound
  assignments were all proved in `CFormenI.lean`/`CFormenM.lean` and all
  fell through `_ => false`. Nineteen arms moved inside the certificate
  with no new model reasoning; the ONE new lemma is `ecorr_geSwap` (the C
  operator `>=` for Gabbro's `le b a`), and it is `ecorr_cmp` with its
  operator fact. Every arm has a positive probe and a PLANTED DEFECT in
  `KorrespondenzWeitZeuge.lean` -- an arm that accepts a wrong row is worse
  than a missing arm.

  BLOCK STRUCTURE 2026-09-15 (`OPUS-BERICHT-BLOCK.md`). The check walks
  BLOCKS as well as terminal blocks: `if (c) { … } else { … }`
  (`GRow.ite` against `Stmt.ite`) is decided arm by arm, and inside a
  block `T y = g(a);` (`GRow.call` with a destination against
  `Block.bindCall`) binds the callee's answer to a fresh C local; the
  `traverse` header `for (T v = 0; v < N; v += 1) { … }` (`GRow.forTrav`
  against `Stmt.traverse`) is decided with its bound, its loop variable's
  freshness and the body's hygiene. A row that
  carries rows needs a recursion, and the recursion is STAGED, not
  mutual: `stOk0` (flat, no recursion) -> `blOk` (self-recursive over the
  rows, structurally) -> `stOk` (`stOk0` plus the block arms) -> `enOk`
  (unchanged). *It has to stay structural*: `korrOk` is settled by
  `decide` in every chain instance, and a well-founded definition does
  not reduce in the kernel. The soundness runs on a plain measure
  (`rowSize`), which a proof may do because a proof never reduces.

  THE DEVICE 2026-09-16 (`OPUS-BERICHT-GERAET.md`). Gabbro exists for an
  operating system, and until this day the certificate refused every form
  that can end a call in the model's `Hardware` class -- which is why no
  driver-shaped program could be certified. THREE of the five are carried
  now: the register STORE (`GRow.storeReg`, `R = e;`), the register READ
  (`GRow.loadReg`, `let x = R;`) and the CHECKED read (`GRow.loadRegElse`,
  `let x = R else (c) { return e; }`), whose `requires … else` channel is the
  interesting one: **a broken device promise becomes a BRANCH in the program
  rather than a stop**, and that branch has to correspond like any other row.
  What no certificate can decide stands in ONE named premise, `GerAnnahme`
  (§1c), and what a device chain then claims is exactly this: *if the profile
  holds and the register answers inside its declared type, every run of the
  emitted C corresponds.* NOTHING about the device is claimed.

  The device rows need to know WHICH register an address belongs to, and that
  is the emitter's layout and not the program text, so `korrOk` carries a LAST
  parameter `GT : GerTafel D` -- plain data, no proof field, with a default of
  the EMPTY table under which every device row is refused. Every call written
  before this day is unchanged, character for character, and decides what it
  decided before. `awaits`, the axiom call and `forever` stay REFUSED, by name
  (CUTS).

  THE SOUNDNESS (`korrOk_fnCorr`): a certificate that checks gives, for
  EVERY function and at EVERY call depth `n` and `forever` budget, the
  callee relation `FnCorr` between Gabbro's `rufAt P O passes n` and the
  C call `CallAt … (kProg c) n` of the unit the certificate elaborates
  to. Nothing is re-proved: each row is one existing T4 lemma
  (`scorr_assignDurch`, `scorr_assignVar`, `scorr_call`, `ecorr_slotVia`,
  `cCorr_ruf`, `cCorr_end`, …); the one new lemma is the argument passing
  of a call (`argsTo_of`), stated once for every argument list.

  THE LOCALS MAP is the EXPORTER'S: Gabbro variable `j` of a function is C
  local `vm[j]`, a pointer parameter is an ordinary variable whose value
  is the table's address (`ValCorr` at a pointer type). A callee's map
  must be exactly its C parameter list (`callMapOk`) -- the map the model
  of the source text has, not `refD`'s index-fixed map.
-/

import Grammatik.Korrespondenz.Allgemein.KorrespondenzAllg.T1
import Grammatik.Korrespondenz.Allgemein.KorrespondenzAllg.T2
import Grammatik.Korrespondenz.Allgemein.KorrespondenzAllg.T3
import Grammatik.Korrespondenz.Allgemein.KorrespondenzAllg.T4
import Grammatik.Korrespondenz.Allgemein.KorrespondenzAllg.T5
