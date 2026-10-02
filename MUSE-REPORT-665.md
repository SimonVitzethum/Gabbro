# Muse Report 665: exact review of author 664 (address encodings)

CANDIDATE: 664 ff7fb88821ecb9774405cf6d9058e60c558258ff
VERDICT: ACCEPT (bounded; no repairs required of this candidate)

## Scope and method

Review-only lane. Owns only this file; no source, control or network touched.
Verified clone `/home/simon/Dokumente/gabbro-muse/a665`, branch `muse/665`.
Pinned snapshot: `.tmp/review/SNAPSHOT.json` names author 664, head
`ff7fb88821ecb9774405cf6d9058e60c558258ff`, base `1d087115`, files
`MUSE-REPORT-664.md`, `grammatik/Grammatik.lean`,
`grammatik/Grammatik/X86/AddressEncoding.lean`.
The snapshot module file hashes exactly to the pinned commit blob
(sha256 `90c15898e91d8b9e2c7628882729ddcf8495ef3778c7011399281065e9d45b9c`
on both). The umbrella diff is one additive import line. No other file is
touched; no friend-reserved optimiser file is imported. The seven modules the
candidate builds on (Typen, Wort, Speicher, Codec, Ausfuehrung, Byteschritt,
ControlFlow) are byte-identical between the candidate base and this review
base, so reproduction here is faithful.

## Independent reproduction (queued wrappers, this clone)

- Transiently installed the exact pinned bytes, then removed them afterwards;
  final tree holds only this report.
- `./lean-probe grammatik/Grammatik/X86/AddressEncoding.lean`:
  `== 0 error(s) in the COMPLETE output`.
- `./lean-bau`: `Build completed successfully (461 jobs).`
- `#print axioms` output for every main theorem: only `propext`,
  `Quot.sound`, or fewer (a subset of the `gabbro_ziel` standard; no
  `Classical.choice` is introduced or needed).
- Word-boundary grep for `sorry | admit | axiom | native_decide | unsafe`:
  no tactic use (only English "admit" inside two doc comments).
- Reviewer probe file (transient, deleted after the run, 0 errors) pinned
  three suspicious cases independently of the author's pins:
  1. SIB byte 36 with REX.X=1 parses to index `r12` (not absent), base
     `rsp`, disp32: the documented no-index/high-index disambiguation is
     correct.
  2. A RIP-relative tail decodes on the 0x89 store path
     (`decodeStoreIdx [72,137,5,249,15,0,0]` gives `ripForm 4089`).
  3. A fetched store through a noncanonical base (`2^47`) FIRES when the
     permission predicate allows it. The step inherits the accepted
     `Speicher.write64` contract (per-byte permissions only; modular
     wrap; no canonicality check). This is a documented admission gap,
     not an introduced unsoundness; see below.

## Manual cross-check (local snapshot, Intel SDM 325462-093US)

Checked against `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`
(SDM combined vols 1-4, verified 2026-10-02): RIP-relative = next-RIP plus
signed disp32 (§2.2.1.6, Table 2-7); mod=00 r/m=101 stays RIP-relative even
with REX.B=1 (the R13 note); SIB base=101 with mod=00 is disp32-only;
index=100 is absent (REX.X extends the index field); REX is 0100WRXB with
R=reg, X=index, B=base, W=64-bit operand (Table 2-4); LEA "Flags Affected:
None". The candidate matches every checked rule, including the author's
`rv/4, /2%2, %2` REX-bit split and the parser returning `ripForm` without
consulting the B bit. The author cited no manual pages (their clone lacked
`REFERENCES.json`) and claims no silicon correspondence; the encodings
nevertheless verify. Follow-up producers should record exact heading/page
citations; absence here is honest bounding, not a defect.

## Architecture findings

- Byte forms: REX.W enforced on both new paths (0x8D LEA, 0x89 store);
  ModRM/SIB/disp8/disp32 shapes per selected scope; legacy 0x66 and missing
  REX.W refused by `decide`-pins. Over-refusals (0x67 truncation, 32-bit
  LEA) are all in the safe direction.
- No shadowing: the parser refuses pilot mod=10 base-only and SIB-36 rows,
  the encoder returns `none` there, and the pilot refuses all REX.X bytes
  and every 0x8D form; both directions are machine-checked. Pilot files are
  unchanged.
- Semantics: `adrEff` is pure word arithmetic (no memory read); LEA
  preserves flags, memory and foreign registers with a bridge theorem to
  accepted `leaAnwenden`; the store advances RIP past the exact consumed
  length only on `write64` success (fault before RIP advance); RIP-relative
  uses the post-decode RIP. No feature/MXCSR/interrupt gates are needed for
  these integer forms, and none are invented.
- No desired-correctness premises found: sign-extension, scale round trip,
  canonical pins, compact-choice savings (4 vs 7 bytes at provably the same
  address) and the wrong-signed-displacement inequality are all closed
  `decide` facts; every multi-premise theorem uses all its hypotheses.
- Witnesses are reached and non-degenerate: the fetched LEA computes
  `8192 + 8 + 5 = 8205` from executable memory with flags/memory/RIP pins
  plus past-image refusal; the fetched high-register scaled store
  (`r8 + r9*8`) lands 42 at 8200 with read-back, from-zero start and RIP
  advance. Malformed-byte, missing-SIB, prefix, wrap-edge, noncanonical-hole
  and dark-permission refusals are planted and green.
- `fussZugelassen` (canonical + no-wrap + per-direction rights) is proved
  as an admission predicate but is NOT a precondition of `adrStoreSchritt`
  (see probe 3). Direction is over-approximation, consistent with the
  accepted `Speicher` foundation; the CUTS block discloses it. Recommended
  follow-up: gate the new steps on `fussZugelassen` or prove the refinement.
- `extByteschritt` integration is correctly absent: wiring the unified
  dispatcher would require editing another author's file, which this task
  forbids. The module exports the stable API named in the task (`adrEff`,
  `dispWortArt`, `encodeAdr`, `parseAdrTail`, `decodeLea`,
  `decodeStoreIdx`, `leaFormSchritt`, `leaGeholtSchritt`,
  `adrStoreSchritt`, `kanonisch48`, `fussZugelassen`) for the integration
  owner instead.

## What remains open (not charged to this candidate)

No silicon correspondence; no generic 256-pair round trip or uniform
length-bound theorem (per-shape pins only); base-only disp0/disp8 compact
rows live here while the pilot keeps disp32; width/branch/immediate forms
with integer666/locked662/FP668 (nonexistent lanes in this tree);
TSO/GX bridge; source/ABI/loader/entry/budget claims. All are stated
precisely in the file CUTS block. Nothing in the task text appears wrong;
the `ExtendedExecution575`-dispatcher sentence cannot be satisfied inside
the file-ownership rule and is rightly deferred to integration.

## Final state

`git status` is clean except this report. Last `./lean-bau` on the
candidate-augmented tree: `Build completed successfully (461 jobs).`
Lean green, standard-or-fewer axioms, independent manual spot-checks pass,
no guarantee weakened, no fake closure. Bounded ACCEPT as stated above.
