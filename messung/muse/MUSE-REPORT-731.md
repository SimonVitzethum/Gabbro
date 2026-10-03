# MUSE-REPORT-731: Independent review of author 730 (SIB / RIP-relative addresses to effects)

CANDIDATE: 730 d2060cfd1e5546c1b5b278f3154e288d8f1ec449
VERDICT: ACCEPT

## Clone / branch verification

- This clone: `/home/simon/Dokumente/gabbro-muse/a731`, `.git/HEAD` reads
  `ref: refs/heads/muse/731`. Match: proceed.
- Author 730 task/source/PATCH taken from the pinned snapshot
  `.tmp/review/author-730/` (exact-candidate review inputs, not a live clone):
  `OWNER-TASK.md`, `PATCH.diff`, `grammatik/.../AddressedHardwareExecution.lean`,
  `MUSE-REPORT-730.md`, `BUILD-EVIDENCE.json`, `SNAPSHOT.json`.
- Snapshot HEAD re-verified this turn; no author change, no stale verdict.
  No new definitions or theorems by this reviewer (report-only lane).

## What was reviewed

Author 730 owns exactly three files (per `SNAPSHOT.json`, confirmed in
`PATCH.diff` headers): `MUSE-REPORT-730.md` (new), `grammatik/Grammatik.lean`
(one additive import line, `import Grammatik.X86.AddressedHardwareExecution`,
nothing else), and `grammatik/Grammatik/X86/AddressedHardwareExecution.lean`
(new, 709 lines). No existing file or theorem is touched; no weakening is
possible by construction.

The module builds an ordered effective-address adapter (`adrPruefe`:
canonical, then no-wrap, then per-direction permission) over the accepted
`AddressEncoding` selected forms, generic checked access (`adrLade` /
`adrSpeichere` over real `read64`/`write64`), an extended LOCK XADD decoder
(`decodeLockAdr`: LOCK + reused `rexLockBits` + 0F + XADD + reused
`parseAdrTail`) and its execution (`lockXaddAdr`, mirroring the accepted
`lockSchrittVoll` XADD arm), plus fetched witnesses (`lockXaddGeholt` over
`geholt`), negatives, and alias pins.

## Evidence checked (all against the a731 base tree, which holds the producers)

- Reuse is genuine, not parallel invention: `rexLockBits`,
  `parseAdrTail` (`AddressEncoding.lean`), `adrEff` / `adrEff_basisForm` /
  `basisForm` / `skaliertForm` / `ripForm` / `fussZugelassen` /
  `kanonisch48`, `lockSchrittVoll` / `decodeLock` / `decodeLockModrm`,
  `geholt` (executable-prefix fetch, `Byteschritt.lean`), `ripNach` /
  `laengeOk` (`Ausfuehrung.lean`), `ausgerichtet8`, `write64_verweigert` /
  `write64_erhaelt_berechtigungen` (`Speicher.lean`) all exist in base.
- REX.X = 0 claim is accurate: accepted `rexLockBits` admits only
  0x48/0x49/0x4C/0x4D, i.e. X = 0 by construction; the author passes `x = 0`
  to `parseAdrTail` and books REX.X = 1 rows as OPEN in CUTS. Lawful reuse,
  not a silent subset.
- Disjointness both ways is structural AND machine-checked: the producer's
  `decodeLockModrm` accepts only plain disp32 or degenerate SIB 36, so
  scaled/RIP tails cannot decode there; pilot encodings are refused by the
  reused `parseAdrTail` here. Both directions pinned by `decide` on closed
  bytes (`decoder_weist_pilot_basis_zurueck`,
  `decoder_weist_pilot_sib_zurueck`, `produzent_weist_skaliert_zurueck`,
  `produzent_weist_rip_zurueck`).
- `lockXaddAdr_basisForm` (canonical + no-wrap + aligned overlap) is proved
  from equations, including the subtle write-without-permission branch via
  the accepted `write64_verweigert` lemma (producer reads fine but its
  `write64` fails; adapter refuses up front; both yield `speicherFehler`).
  No successor assumption, no desired-correctness premise.
- Witness arithmetic independently recomputed: scaled `r8 + rcx*8 + 0` =
  8192 + 8 = 8200; RIP-relative `ripNext + 4095` = 4105 + 4095 = 8200;
  word 8192 = 0x2000 little-endian makes byte 8201 = 32; RIP advances are
  4103/4105 for the 7/9-byte images. Both `..._zeuge` theorems are joint
  (pre-state byte AND post-state observation in one statement) and
  memory-changing (`decide`-checked). The pure `ripForm_beobachtung` pin
  holds without touching memory, as labelled.
- Fault order proved: canonical before wrap before permission
  (`adrPruefe_ordnung_kanonisch/umbruch`, `adrPruefe_loch` pins
  canonical-first under fully permissive memory on the closed 2^47 hole);
  length first, own-buffer before address (`lockXaddAdr_puffer_zuerst`);
  failed read behind admitted checks is `speicherFehler`, never a value.
- Banned-token grep over the candidate module: no `sorry` / `admit` /
  `axiom` / `native_decide` / `unsafe` tactics, no `intro _` /
  `have _ :=` (hits are prose: "admits"/"admitted"). Every theorem's
  premises are all consumed by its proof (checked individually, including
  the `hali` side condition in `lockXaddAdr_lesefehler` and the
  `hkan/hwrap/hali` triple in `lockXaddAdr_basisForm`).
- Rule 13: premises quantify over X86 hardware syntax (`AdrForm`,
  `Register`), none of the listed Gabbro program-syntax types, so no
  mechanical `_zeuge` duty; the task's own witness demand is met by the two
  joint fetched memory-changing witnesses.
- Provenance: "Intel SDM 325462-093US" matches clone-local
  `.tmp/HARDWARE-REFERENCES/REFERENCES.json` (edition 325462-093US,
  verified 2026-10-02); the report's "no silicon claim" matches the
  reference scope note (AMD unavailable). Architecture-as-model, correctly
  caveated.
- Build evidence (`BUILD-EVIDENCE.json`) is a credible iterative trail:
  intermediate `lean-probe` failures (4, 1, 3, 1, 2, 1 errors) each repaired
  to `== 0 error(s)`; last `./lean-bau` result line:
  `Build completed successfully (482 jobs).` Axiom dump shows all main
  theorems within `[propext, Classical.choice, Quot.sound]`. CUTS block +
  32 `#print axioms` lines present (see nit (c) below on the "31" count).
- This reviewer did NOT re-execute the candidate build: applying the patch
  in this clone would dirty files outside the owned
  `MUSE-REPORT-731.md`. Verification is static against base producers plus
  the recorded whole-build evidence, whose failure-then-green trail is not
  fabricable by inspection. This clone's own tree is untouched.

## Findings (all non-blocking, none contradicts a proved claim)

- (a) Alignment-vs-permission order differs from the producer on the
  unaligned AND unpermitted overlap: the producer checks alignment first
  (yields `verweigert`) while the adapter checks `adrPruefe` first (yields
  `speicherFehler`). Outside `lockXaddAdr_basisForm`'s scope (it requires
  `hali`), and both outcomes are refusals, so no silent success and no
  false claim. Suggested follow-up, not a repair condition: move the
  alignment guard ahead of `adrPruefe` in `lockXaddAdr` for full overlap
  equality without `hali`, or extend the theorem.
- (b) `lockXaddGeholt` length accounting (`fetched.length - rest.length`)
  assumes `rest` is a suffix of the fetched window (true for `parseAdrTail`
  by construction); no general length-consistency theorem is claimed, only
  closed-window witnesses. A one-line CUTS entry could name it.
- (c) Nit: the report says "31 main theorems" but the file carries 32
  `#print axioms` lines for 32 theorems. Count only; coverage is complete.
- OPEN items honestly carried in CUTS (REX.X = 1 rows, LOCK CMPXCHG through
  full forms, no generic all-pairs round trip, no TSO/GX bridge, no source
  correspondence) match the task's "lawful adapter or precise obstruction"
  alternative and claim no closure.

## Remaining open (for the wave, not this candidate)

TSO/GX per-access bridge, CMPXCHG full-form connection, REX.X = 1 rows,
generic round trip, and the alignment-order follow-up (a) above.

## Task issue

None material. The owner task's scope (adapter + one fetched
memory-changing integer/LOCK form beyond base+disp + RIP-relative witness +
negatives + consumer API + lawful-adapter-or-obstruction) is met; the
"accepted narrower legacy decoders must not be silently treated as complete"
requirement is discharged by proof (both-direction disjointness pins), not
by assertion.
