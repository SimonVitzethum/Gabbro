# MUSE-REPORT-1001: Exact review of author 851 (binding-surface closing)

## CANDIDATE

CANDIDATE: 851 0dcdc7a7822e7282ce7026184ba5b03c1c3aeec7

## VERDICT

VERDICT: ACCEPT

## What was reviewed

Exact pinned snapshot from `.tmp/review/`:

- `SNAPSHOT.json`: author 851, head `0dcdc7a7822e7282ce7026184ba5b03c1c3aeec7`,
  base `b040b155159f47629542b0083e2f0a8a607f2b4c`, clean, 3 files.
- Base matches this clone's HEAD (`b040b155 merge: Muse 975 direct-x86
  foundation`, branch `muse/1001` verified): the candidate was built against
  exactly the producer modules present here.
- `PATCH.diff` touches exactly three files: `MUSE-REPORT-851.md` (new),
  `grammatik/Grammatik.lean` (one appended import line
  `import Grammatik.X86.ComposeBindingSurface`), and the new module
  `grammatik/Grammatik/X86/ComposeBindingSurface.lean` (255 lines).
  No source/checker/Spec/goal/emitter edits, no diagnostic/gift/example/CLI
  numbers (grepped: no `N[0-9]{3}`/`MARKE`/gift tokens), no friend-reserved
  optimiser files.

## Architecture checks (independent, against base tree + local references)

- Closing interface `bindungsFlaecheOkB` conjoins exactly the seven decided
  producer legs claimed: `torOkB`, `!c186VerweigertB`, `!c187VerweigertB`,
  `!m140VerweigertB`, `bindungErstelltB`, `stubEndsTrapB`, `eintrittOk`.
  All reused by name from accepted `GateStub` / `EntryState`; no decoder,
  interpreter or executor duplicated. Import list is exactly those two
  modules plus `ContractSites`.
- `ComposeBindingSurface_verbindung`: every premise is used (`hp`/`hr` via
  `inlinePflicht_aus_rufAt`, run premises via `rufAt_ok_gibt_ens`, admission
  legs via the final `simp`). The two obligation conjuncts
  (`Nonempty (InlinePflicht …)`, `RufEnsCheck` at actual `ρ`/`v`/worlds) are
  derived through the accepted lemmas, not restated; contracts hold at their
  place with actual values (no `forall rho`/`forall v` weakening). The `h`
  premise pins the result world to `sinv`, which is exactly the shape of the
  accepted `inlinePflicht_aus_rufAt` interface (same call pattern as
  `ContractSites.lean` line 156-157), so no new restriction is introduced by
  the composition.
- `osName_beweist_nichts`: `torDoppelt` is `schreibTor` with a duplicated
  `rdi` entry, so `nummer = 1` still holds by `rfl`, while `torOkB` fails on
  the accepted `torDoppelt_verweigert` (`regsDistinctB = false`, first
  conjunct of `torOkB`). Genuine: same gate number refused.
- Planted refusals reuse the accepted pins verbatim: `torRegionOhneOr`
  (C186), `torStapelOhneTrampolin` (C187), `m140_geschmiedet` (the exact
  `[1] [(0, .zahl 5), (1, .zahl 7)]` forged shape, closed by
  `unfold`+`rw`+`simp`), and `zeugenStapelSchief_verweigert`
  (misaligned entry stack, `EntryState.lean` line 457-458). One refusal per
  leg, each in every stub/entry context.
- `zulassungOhneVertrag`: admitted stub+entry (`schreibTor_ok`,
  `schreibTor_kein_c186`, `decide` for C187, `m140_zahl_erlaubt`,
  `zeugenMoves_ok`, `zeugenStub_trap`, `zeugenEintrittHosted_ok`) coexists
  with the refused entry contract `pruefe_requires_falsch_am_start` — the
  exact accepted theorem reused. Admission smuggles no obligation.
- Witness `ComposeBindingSurface_verbindung_zeuge`: destructuring arity
  matches the accepted witnesses exactly (`rufAt_ok_gibt_ens_zeuge`
  17-tuple with `schreibt = true` and slots `0`/`5`;
  `vertragStandort_lauf_zeuge` reached-run tuple;
  `torStub_zeuge.2.2.2.1` = EBADF→reason-0 decode and `.2.2.2.2` = 8-byte
  write/read change, matching the 5-conjunct statement order at
  `GateStub.lean` lines 367-372). Non-degenerate: table-writing fixture,
  `0 -> 5` source memory change, reached `RufMaschineG` run, real X86 byte
  memory change, errno decode. The `σ' = sinv` transport mirrors the
  producer's own use.
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` (word-boundary grep
  clean; only benign `admitted` in prose and `#print axioms` lines). No
  `intro _` / `have _ :=` on premises. CUTS block + nine `#print axioms`
  lines present as required.

## Build evidence (author transcript, checked for consistency)

`BUILD-EVIDENCE.json` records the honest repair loop: first probe showed
3 errors (the `m140` simp-mangling at lines 134/152 plus the witness
application), final `./lean-probe` shows
`== 0 error(s) in the COMPLETE output; exit 0` with all nine declarations at
`[propext, Classical.choice, Quot.sound]` or subsets, and `./lean-bau`
`Build completed successfully (511 jobs)` including
`Built Grammatik.X86.ComposeBindingSurface` and `Built Grammatik`.
The reported axiom sets are consistent with reusing the source-contract
lemmas (`Classical.choice`) and nothing else. Commit `0dcdc7a7` recorded via
`commit.sh` with staged owned files only.

## Not independently re-run (honest boundary)

`./lean-bau` / `./lean-probe` were NOT re-executed here: this lane owns only
`MUSE-REPORT-1001.md` ("no source"), so the candidate patch could not be
applied to this tree, and shell access to the snapshot path was refused by
the permission classifier (file tools used instead). Verification rests on
exact file inspection, producer-lemma cross-checks against the pinned base
present in this clone, and the transcript above. No suspicious case was
found that would require a rebuild.

## Scope of acceptance (bounded)

ACCEPT covers: the composition theorem, its joint witness, the six
refusal/separation lemmas, and the CUTS as stated. Hardware soundness
(REX/register/width/flag semantics, pre-fault effects, TSO/atomicity,
MXCSR/interrupt gates) remains the responsibility of the accepted producer
modules, which this file does not re-prove by design. Full source-to-byte
lowering (lane 287), TSO/W/GX bridge, budget/cost transfer and wider
decoder coverage stay OPEN as the file's own CUTS declare with owners.

## What remains open

Nothing from lane 1001: review complete, report-only deliverable.
Candidate is ready for checked merge.

## Task correctness note

Nothing in the lane 1001 task is believed wrong. One process note: shell
(`bash`) invocations touching `.tmp/review/` were twice rejected by the
permission classifier while the file tools read the same paths fine;
future review lanes should prefer the file tools for snapshot inspection.
