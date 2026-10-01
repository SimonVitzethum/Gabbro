# MUSE-REPORT-387: Independent exact-candidate C5 review of 349 ValidatorSkeleton

## Scope verified

- Clone `/home/simon/Dokumente/gabbro-muse/a387`, branch `muse/387`, HEAD
  `ebdec41d` at review time. No other clone read; no agent/network calls.
- Candidate snapshot (` .tmp/review/SNAPSHOT.json`): author 349, HEAD
  `6562026148f4016294f34ef00d5421f4783ab58c`, base `ee1071b8`, files
  `MUSE-REPORT-349.md`, `grammatik/Grammatik.lean`,
  `grammatik/Grammatik/X86/ValidatorSkeleton.lean`, clean tree.
- Inspected: `author-349/OWNER-TASK.md`, `MUSE-REPORT-349.md`, `PATCH.diff`,
  `BUILD-EVIDENCE.json`, supplied `ValidatorSkeleton.lean` (342 lines), and the
  actual accepted vocabulary in this clone (`Bild`, `Codec`, `Byteschritt`,
  `GateStub`, `TableLayout`, `ValidationBudget`, `Typen`).

## Method

- Staged ONLY the candidate module plus the additive import privately in this
  clone, ran `./lean-probe` (file), `./lean-bau` (full), and a `gabbro_ziel`
  axiom probe, then fully restored (staged file removed, `Grammatik.lean`
  restored byte-identical, `git status` clean before writing this report).
- Never trusted the displayed tail: used the first `COMPLETE error count` line.

## Findings (all checked against actual source)

- Task done as specified: `valX86 p bild := wohlgeformt p bild && bildDeckung bild`
  (checked mapping AND full decode coverage of every executable section via
  canonical `decodeFuel`/`validAllFuel` with fuel `dateiLen + 1`; data sections
  not decoded), full half `valX86Voll` (gates via `torOkB`, layout via
  `layoutOk`), extern bookkeeping (`externOk` refuses without proved flag),
  pointer mirror (`valZeigerOk` over `m140VerweigertB`), transfer check
  (`transferOk` over `abteilFinden`), extension interface (`ErwDec`/`decodeErw`
  canonical-first with `decodeErw_kanonisch` no-shadowing proof), fetch tie
  (`valZeuge_fetch_ret` over real `fetchDekodiert` on canonically loaded state).
- Generic real semantics, no toy/second model: every definition reuses the
  accepted canonical vocabulary; no second IR, decoder, evaluator, or state.
  All 17 theorems proved by `decide`/`unfold`+`exact`/`rw` over actual definitions.
- Name checks against this clone all resolve: `groesseOk`/`dateiOk`/`virtuellOk`/
  `relokOk`/`wohlgeformt`/`abteilFinden`/`geladen` (`Bild`), `decode`/`natByte`
  (`Codec`), `fetchDekodiert` (`Byteschritt`), `torOkB`/`torAusClobber`/
  `schreibTor`/`m140VerweigertB` (`GateStub`), `layoutOk` (`TableLayout`),
  `decodeFuel`/`validAllFuel` (`ValidationBudget`). The "14 pilot forms" count
  matches the 14 `Befehl` constructors in `Typen.lean` (verified by reading).
- Physical facts derived, not assumed: `ret = byte 195` (0xC3) and single-byte
  `[0]` decode refusal are `decide` proofs against the canonical decoder and
  were REPRODUCED locally — `./lean-probe` on the staged file returned
  `0 error(s)` with axiom lines identical to the author's evidence.
- Axioms reproduced exactly: 13 theorems `[propext]`, 2 `[propext, Quot.sound]`
  (`valZeiger_geschmiedet_verweigert`, `valZeuge_gelenk` via BitVec), 2 with no
  axioms (`valFremd_verweigert`, `valTransfer_unlisted_verweigert`) — all within
  the standard goal set.
- Full build with candidate staged: `Build completed successfully (421 jobs)`
  (author recorded 417 on base `ee1071b8`; the +4 is base drift in this newer
  clone, not candidate content). Goal probe with candidate staged:
  `gabbro_ziel` on `[propext, Classical.choice, Quot.sound]` — unchanged.
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` (the only substring hits
  are the English word "admits" in comments). No Prop-typed premise; every
  premise used (projections via `Bool.and_eq_true_iff`, `rw [h]` in
  `decodeErw_kanonisch`); no `intro _`/`have _ :=` discard; no
  conclusion-as-premise (the `valX86*` lemmas project conjuncts of the stated
  definition); no quantified-away contracts (no contract/site quantification at
  all); the only "semantics" claims bottom out in `exec`-adjacent real memory
  (`geladen`/`write64`/`read64`).
- Witness is non-degenerate and joint: `valZeuge_gelenk` ties acceptance +
  one-byte-mutation refusal to the REUSED real memory-changing run
  `Bild.schreibLese_zeuge` (read in source: nonzero `write64` at `0x2000` over
  loaded image memory, reads back, bytes observably differ). No `_zeuge`
  companion is owed (no syntax-universal premise, no `ZEUGE:` target), and the
  owner-task witness direction (minimal prefix + mutation refusal) is delivered.
- Safety corrections honoured: W^X refusal documented as validator admission,
  not hardware fault; gate/OS contracts as user logic (`ExternStelle` docs);
  no alignment/latency/cost/hardware claims; per-byte TSO, silicon, FP/NaN,
  loader-observed BSS, control-flow legality all in CUTS as OPEN.
  `valX86_sound` appears in CUTS only, never as a premise — verified by reading.
- Bounded claim is truthful: report claims a syntactic skeleton with proved
  refusals for all seven sec. 15 shapes, not a closed validator or any
  source/hardware correspondence. Ownership respected: new file + one additive
  import only; no canonical vocabulary touched; no source admission tightened.
- No material defect found. No repair direction owed. Nits (not verdict-relevant):
  identifiers mix project-German vocabulary (`valZeuge`, `ValFehler`) consistent
  with the reused modules; comments and report English.

## Reproduction record (this clone, candidate staged privately, then restored)

- `./lean-probe grammatik/Grammatik/X86/ValidatorSkeleton.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`, axiom lines identical to
  BUILD-EVIDENCE.
- `./lean-bau`: `Build completed successfully (421 jobs).`, exit 0.
- Goal axiom probe: `gabbro_ziel` on `[propext, Classical.choice, Quot.sound]`.
- Post-restore `git status --short` and `git diff --stat`: empty (only this
  report remains as the owned deliverable).

CANDIDATE: 349 6562026148f4016294f34ef00d5421f4783ab58c
VERDICT: ACCEPT
