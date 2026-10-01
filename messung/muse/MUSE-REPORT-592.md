# MUSE-REPORT-592: Independent exact-candidate connection review of 574

## Scope and method (read-only; report owns only this file)

- Verified clone `/home/simon/Dokumente/gabbro-muse/a592`, branch `muse/592`. No other clone touched.
- Candidate pinned from `.tmp/review/SNAPSHOT.json`: author 574, HEAD
  `90ffeb0c328359fe4a90a716f7b96c1f064116fa`, base
  `377b290e6a6196a3b6810f3c1b897bbcf69a5946`, 3 files, clean.
  Confirmed `git rev-parse FETCH_HEAD` (fetched from `a574`) equals the pinned HEAD.
- Inspected the exact candidate bytes via `git show FETCH_HEAD:...`
  (never checked out into the working tree): full 470-line
  `grammatik/Grammatik/X86/BridgeRead.lean`, the one-line additive
  umbrella import in `grammatik/Grammatik.lean`, `MUSE-REPORT-574.md`,
  and `BUILD-EVIDENCE.json` (15 queued-wrapper entries, first-failing to
  final-green, no evidence editing).
- Diff `base..HEAD --stat` confirms exactly 3 files: report, one
  umbrella import line (`import Grammatik.X86.BridgeRead`), the new file.
  No source checker / Spec / goal / emitter change, no
  `OptimizationRules`/`OptimizationWitnesses` edit, no duplicated
  IR/executor (imports only: `TSO`, `TSOHistory`, `SourceMemory`,
  `Speichermodell.Sicht/MaschineW/AtomarSem`).

## Forbidden-pattern and hygiene checks (on exact candidate bytes)

- `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`: CLEAN (the only
  `axiom` hits are the required `#print axioms` lines, one per main theorem).
- No `Prop`-typed premise; the single `→ Prop` occurrence is the
  `HavocA` set parameter `T`, not a premise.
- No `intro _` / `have _ :=` on theorem premises. Note (not a finding):
  both simulations conclude `LiestG ... → (Lesbar ∧ TraegerGleich)` and
  prove the consequent from the link premises with the recording-step
  hypothesis unused (`fun _ =>`). The statement still ties the same
  thread/carrier/message indices, and the file honestly claims only the
  `lies` consequent, never a full `SchrittW` — see bounded claim below.
- Every premise of every new theorem is used (checked by hand):
  `ladeWort8_ohne_weiterleitung` (hMiss per byte via `load_ohne_eintrag`,
  hRd via `lesbar8_hit` + `read64` guard), `gruppenwert_rep`
  (target side §1 + `RepSlot` + `zahlWort_wortZahl` + hv),
  `wLesbar_aus_gruppe` / `wLesbar_aus_weiterleitung` (value legs +
  hMem/hProj/hTs/hTraeger for the consequent), `havoc_erhaelt_gruppenwert`
  (hA applied at `.inl t`, hTnot discharging the touch condition, hV rewritten).
- No contract-parameter/result quantification (`forall rho/v`): absent.
  `Lesbar` is derived at the actual message
  `⟨ts, σw.speicher, Sicht.null⟩` under the actual view `W.sicht u`,
  never assumed for the desired read.
- No guessed ISA: only existing vocabulary (`loadByte`, `bytesWort`,
  `addrOff`, `neuestens`, `lesbar8`, `read64`, `TSOEintrag`,
  `TSOErreichbar`, `sb*`/`hS*`, `RepSlot`, `HavocA`) — all resolve in
  accepted master modules (`TSO`, `TSOHistory`, `SourceMemory`,
  `FenceDrain`, `AtomicPayload`, `BridgeWrite` cross-checked by grep).
- CUTS block present (lines 433–454); 13 `#print axioms` lines, one per
  main theorem.

## Connection assessment (producer/consumer reality, not decoration)

- REAL new execution facts: `ladeWort8` executes eight real `loadByte`s;
  `ladeWort8_ohne_weiterleitung` proves the committed group equals the
  canonical `read64` word; `ladeByte_ist_jüngste` names the accepted
  youngest-buffer split per position; `gruppenwert_rep` parses the group
  to exactly the source slot value via the accepted representation
  roundtrip. This is a genuine per-access target→source value bridge for
  the committed case, not a premise restatement.
- `wLesbar_aus_gruppe` packages value identity plus the `SchrittW.lies`
  consequent (`Lesbar` from membership + `Nat.le_trans hProj hTs`, plus
  `TraegerGleich`) under explicit history/view-link premises
  (hMem/hProj/hTs/hTraeger) — exactly the premise shape the owner task
  prescribes. The links themselves are assumed, so the run-relation
  projection (`hProj` from the run) remains consumer duty; the report
  and CUTS say so plainly with a measurable next check (a real
  `SchrittW.lies` field fed by `.2`).
- Forwarded case is CONDITIONAL and labelled: `wLesbar_aus_weiterleitung`
  assembles the group and exhibits youngest splits for real, but the
  cross-side value identity `hWert` is an explicit premise assigned to the
  lowering certificate / write side (lane 573). Mixed
  committed/forwarded footprints have no value simulation (tearing
  refusal). I accept this split as coherent — the write side owns
  forwarded values — but it bounds the claim (below).
- Width/grouping/atomicity guards: explicit `hLo : 0 ≤ lo`,
  `hHi : hi < 2^64`, 8-byte footprint, and a group-is-NOT-atomic stance
  with two proved refusals + one stale positive:
  `stale_lesbar_sb` (stale committed byte is `Lesbar`, by accepted
  `load_lesbar_ohne_weiterleitung`), `gruppe_reisst_fremd` (forwarding
  core `(1,1)` vs foreign core torn `(1,0)`, joint reachability +
  memory change, all `decide`/witness-closed), and
  `gruppe_fremd_weiterleitung_uneinig` (fence-ready core reads committed
  zeros while another core forwards `1` — local drain ≠ foreign drain).
- Atomic-rely duty: `havoc_erhaelt_gruppenwert` keeps a non-`T` carrier
  read through every `HavocA` environment (the exact `NutzerPflichtA`
  rely class). Real, minimal, correctly scoped.
- Joint witness `wLesbar_aus_gruppe_zeuge`: all premises instantiated
  jointly on `sbGespült` (reached two-core state: two issues + flush),
  slot value 0 at address 8, timestamp-0 message with empty covered view;
  non-degenerate (`witD.schreibt () () = true` by `rfl`,
  `sb_flush_aendert_speicher`, byte-change inequality). The memory change
  is beside the read footprint (at `sbX`, read at address 8) — allowed by
  the rule as stated, recorded here for precision.
- `schwach_ist_gX` cited, never applied; no fairness/progress/timing/
  device claim; single `.int`-slot representation only. All correctly
  disclaimed in CUTS.

## Build and axiom evidence

- Author `BUILD-EVIDENCE.json` final entries: `./lean-probe` 0 errors
  with all 13 theorems at `[propext]` or `[propext, Quot.sound]`;
  `./lean-bau` `Build completed successfully (441 jobs).` Intermediate
  entries show real development failures (unknown tactics, unsolved
  goals) converging to green — credible, not forged.
- Own base check (this clone, unmodified tree): `./lean-bau`
  `Build completed successfully (443 jobs).` (443 vs 441: base master is
  two modules ahead of the candidate base; candidate adds one module.)
- I did not rebuild the candidate tree (report-only ownership:
  `MUSE-REPORT-592.md` is my sole file); verification is exact-byte
  inspection plus the author's queued-wrapper evidence above. No
  red flag found that would require a reproduction build.

## Bounded accepted claim

Committed 8-byte TSO group loads at a represented `.int` slot simulate
source W reads (value identity via `RepSlot` roundtrip; `lies`
consequent from explicit history/view-link premises); forwarded groups
assemble with per-byte youngest splits but take their value link as an
explicit lowering-certificate premise; tearing and foreign-drain are
proved refusals, stale reads proved allowed; joint non-degenerate
two-core memory-changing witness included. NOT claimed: full
`SchrittW`/`RufSchrittW`, `schwach_ist_gX` application, mixed-footprint
values, carriers beyond one int-slot, run induction, `valX86_sound`,
source-to-final-bytes closure.

## Minimal repairs

None required for acceptance. Two non-blocking notes for consumers:
(1) the unused `LiestG` hypothesis shape — keep the conditional form,
it matches the requested "for every recording G step" interface;
(2) `hProj` (run-relation projection) and forwarded `hWert` (write-side
certificate) are the exact handoff obligations for lanes 573/validator.

CANDIDATE: 574 90ffeb0c328359fe4a90a716f7b96c1f064116fa
VERDICT: ACCEPT
