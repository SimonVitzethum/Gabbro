# MUSE-REPORT-472: Independent exact-candidate review of 424

Lane 472, independent exact-candidate review. Clone
`/home/simon/Dokumente/gabbro-muse/a472`, branch `muse/472` — verified
at start (`git branch --show-current` = `muse/472`, clean tree).
Owns ONLY this file.

## 1. Candidate under review

- Author lane: 424. Pinned candidate HEAD:
  `6fe66837c9d796a366485182b3e99c75f61f8aac` (base
  `0b3132b7bb8bf108b3fd1613c70bc0955051f130`, snapshot `clean: true`).
- Files: `MUSE-REPORT-424.md`, `grammatik/Grammatik.lean` (one additive
  import), `grammatik/Grammatik/X86/FeatureProfile.lean` (NEW, 241 lines).
- Bounded claim: a small generic FINITE admitted performance-feature
  profile separating silicon support from control-state readiness, with
  proved fail-closed strict selection/refusal over the existing canonical
  width/FP/vector interfaces and a proved scalar fallback. No native
  extension bridge, no source lowering, no concurrency claim, no speed
  claim. Explicit CUTS block.

## 2. What was inspected

- `.tmp/review/SNAPSHOT.json`, `author-424/OWNER-TASK.md`,
  `author-424/MUSE-REPORT-424.md`, `author-424/PATCH.diff` (full text),
  `author-424/BUILD-EVIDENCE.json` (all 30 entries).
- Supplied `FeatureProfile.lean` reproduced in THIS clone: staged the
  exact supplied file plus one additive umbrella import, ran queued
  checks, then fully restored (tree clean again: `git status --short`
  empty; scratch logs under ignored `.tmp/opencode/`).
- Dependency names resolved from this clone's accepted files, not from
  claims: `MXCSR`/`mxcsrGueltig` (`Gleitprofil.lean`), `Breite`/`Breite.bits`
  (`Typen.lean`), `write64`/`read64`/`lesbar8`/`write_read_zeuge`
  (`Speicher.lean`), `vLo`/`vecHiAddr`/`OhneUmbruch16`/`vecWrite_teilt`
  (`Vektor.lean`). All exist with the used signatures.

## 3. Reproduction results (this clone, current master base)

- `./lean-probe grammatik/Grammatik/X86/FeatureProfile.lean`: exit 0,
  `== 0 error(s)`. Axiom lines reproduced exactly as reported: twelve
  `[propext]`, one axiom-free (`skalar_fallback_breite`), two
  `[propext, Quot.sound]` (`aufnahme_kein_atomar`, `profil_skalar_zeuge`
  via reused Speicher/Vektor lemmas). All subsets of the standard set.
- `./lean-bau` with candidate staged: exit 0,
  `Build completed successfully (416 jobs)` (current master has more
  files than the candidate's 393-job base; integration is clean here too).
- Forbidden-pattern scan (word-boundary regex over the staged file): no
  `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`; no `intro _` /
  `have _ :=`; no Prop-sorted premise; CUTS block and `#print axioms`
  for all 14 theorems present. (Naive substring hits were only English
  words like "admits" in comments.)
- Name-collision scan against current master: no existing
  `hat`/`bereit`/`waehle`/`fallback`/`PerfMerkmal`/`merkmalZugelassen`/etc.
  definitions (only distinct names like `zaunBereit`, `zugelassen` in
  `MulDiv.lean` — the collision the author already repaired by renaming
  to `merkmalZugelassen`). Staged build confirms no duplicate-definition
  error.

## 4. Material semantic checks (against accepted models, not formatting)

- `hat_ohne_bereit_verweigert`: `hat = true` by `rfl` correct for the
  all-true `HwProfil`; `bereit = false` holds because `mxcsrGueltig 0x9F80
  = false` (FTZ bit set — matches proved `mxcsr_ftz_verweigert` in
  `Gleitprofil.lean`). Genuine separation witness, not vacuous.
- `basis_skalar_zugelassen` (`rfl`): `0x1F80` valid per proved
  `mxcsr_standard`, OS state on — checks out.
- `sse_verweigert_ohne_profil`: both premises (`hh`, `hmx`) consumed by
  the `simp`; general over all control words, FTZ instance closed by
  `decide`. No unused premise.
- `paket_braucht_os`, `skalar_braucht_silizium`: each side alone refuses;
  proofs consume their premises. Fail-closed in both directions.
- `waehle_*` pair: strict Option, admitted returns exactly `some m`,
  refused returns `none`; `fallback_verweigert_bleibt_skalar` pins the
  default to `.skalar64`. No silent substitution anywhere.
- `profil_skalar_zeuge`: joint witness — baseline admission AND a nonzero
  `write64`/`read64` round-trip that observably changes memory, via the
  accepted `write_read_zeuge`. Non-degenerate (nonzero value, changed
  byte). Exceeds the letter of rule 13 (no syntax-quantified theorems
  here, so no witness was strictly required).
- Trust boundaries respected: `hat` is a data predicate over a claimed
  profile, never presented as a hardware probe; CUTS disclaims executed
  bytes, decoder output, measured speed, source lowering, budget transfer,
  call-log effects, TSO granularity, GX refinement, sticky flags, NaN
  payloads, AVX tiers. The report claims nothing beyond the file.
- Scope discipline: imports only the four named canonical interfaces;
  no checker/Spec/goal/Rust/emitter/friend-file change in the PATCH.
  `merkmalBreite .paketInt128 = .b32` is a lane-width modelling choice
  with no semantics attached beyond the scalar-only width theorem —
  documented, not a defect.

## 5. Observation (not a defect, no repair required)

- `aufnahme_kein_atomar` is `vecWrite_teilt` restated verbatim: its
  premises mention no profile/admission hypothesis, so the English gloss
  ("the admitted packed tier still…") is carried by the reuse context
  rather than the statement. This is honest bridging (documented as a
  reuse, all premises used, proof exact), and the fail-safe direction is
  the right one — nothing here claims admission yields atomicity. If a
  follow-up wants the link explicit, the repair direction is to add an
  admission hypothesis `(h : merkmalZugelassen hw b .paketInt128 = true)`
  alongside the existing premises; the current statement stays true
  either way. Not a ground for REPAIR: the delivered bounded claim holds
  as stated.

## 6. Build-evidence audit

- The author's `BUILD-EVIDENCE.json` is unusually complete: it shows the
  real failure history (name collision with `MulDiv.zugelassen`, two
  red `lean-probe` iterations on the FTZ lemma, the exit-134
  `failed to create thread` environmental episode reproduced on
  unmodified master, and the final green `bau424e.log` + `probe_ziel2.log`
  with `gabbro_ziel` on exactly
  `[propext, Classical.choice, Quot.sound]`). The history is consistent
  with the final PATCH (rename present, FTZ by closed `decide`) and with
  my independent green reproduction. No forged evidence found. The
  report's "exit 0, not the error-count line" lesson is sound — I
  verified exit codes throughout.

## 7. Open / out of scope (as declared, not defects)

Native extension bridge, source lowering, concurrency beyond sequential
reuse, MXCSR bit positions vs physical hardware, fifth and further
features. All in CUTS. Full compiler closure is neither claimed nor
reviewed here.

## 8. Believed-wrong items in the author task

None found. The owner task's constraints (no second IR, no mini-machine,
cuts stated, bounded claim only) are met.

CANDIDATE: 424 6fe66837c9d796a366485182b3e99c75f61f8aac
VERDICT: ACCEPT
