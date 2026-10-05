# MUSE-REPORT-1180: Exact review of candidate 1179 (HwBildFamilien)

CANDIDATE: 1179 94a8dfd02639f6ff1aca5842a63b3cfb1ef623c3

## Identity

- Clone verified: `/home/simon/Dokumente/gabbro-muse/a1180`, branch `muse/1180`. No mismatch, no STOP.
- Candidate reviewed: author lane 1179, pinned HEAD `94a8dfd02639f6ff1aca5842a63b3cfb1ef623c3`
  (base `0ddf527d050ae9edced5f26e90172293b059eaf2`), from `.tmp/review/SNAPSHOT.json`.
- Review basis: candidate diff only — `.tmp/review/author-1179/PATCH.diff` (684 lines) and the
  snapshot file `.tmp/review/author-1179/grammatik/Grammatik/X86/HwBildFamilien.lean` (593 lines).
  Per the lane's OWN ONLY rule the candidate was NOT applied in this clone.

## Diff scope

Exactly three files, matching the snapshot manifest (`clean: true`):

- `MUSE-REPORT-1179.md` (new, report only).
- `grammatik/Grammatik.lean`: exactly one added line, `import Grammatik.X86.HwBildFamilien`.
- `grammatik/Grammatik/X86/HwBildFamilien.lean`: new file, no other existing file touched.

## Checks performed

- **No forbidden tactics/axioms.** Grep over the snapshot tree for
  `sorry|admit|axiom|native_decide|unsafe|sorryAx`: the only hits in the new Lean file are the
  required `#print axioms` lines and one comment word (`adapterBild`, docstring of
  `hwBildFamilien_schritt_wf`). No `sorry`, `admit`, `axiom` declaration, `native_decide`
  or `unsafe` in code.
- **Axioms standard.** Author build evidence shows `[propext]` for every theorem except
  `hwBildFamilien_schritt_wf` (`[propext, Quot.sound]`, inherited via the reused
  `hwSchritt_wf`). Both are subsets of the goal-theorem standard
  (`propext`, `Classical.choice`, `Quot.sound`); nothing extra.
- **Every premise used.** Checked theorem by theorem: `istErweitert_nicht_pilot` uses `h`
  (pilot case) and `heq` (all other cases); `decodeExt_nicht_pilot_zeigt_decode_none` uses
  `h` and `hnp`; `hwBildFamilien_erweitert_ohne_pilot` uses `hf` (via `fetchExt_erfolg`) and
  `hnp`; each of the six obstruction corollaries passes its `hf` and a constructor
  inequality; each of the six `fetch_*` liftings uses every `h1..hN` (dispatch chain),
  `hsum` (length equation), `hok` (length guard) and `hexe` (execute permission); each of
  the six `*_bild` agreements uses `hmem/hrip/hreg/hfl` (via `hwBild_geholt_gleich`) and
  forwards all decoder/length/permission premises; `hwBildFamilien_schritt_wf` uses both
  `h` and `hwf`. No premise has type `Prop` itself; no `intro _` or discarded `have`.
- **Lifted, not copied.** The only new definition is `istErweitert`, a trivial match
  predicate (pilot vs. rest), not a model. Every decoder, fetch, step, loader and pin is
  reused by name and verified present in this tree with matching signatures/statements:
  `decodeExt_kanonisch`, `decodeExt_muldiv/shift/setcc/cmov/fp/vec`, `fetchExt_erfolg`,
  `hwBild_geholt_gleich`, `hwSchritt_wf`, all seven `pin_ext_*` and all seven
  `pin_pilot_weist_*_zurueck`, `hwBild_zeuge`. The six per-family proofs are one-line
  applications of the generic theorem, as tasked; no proof is copied.
- **Planted refusals really refuse.** The joint witness `hwBildFamilien_zeuge` conjoins
  seven closed `decodeExt` pins (lengths 3/3/4/4/4/4/5, verified byte-for-byte against
  `ExtendedExecution.lean`) with the seven matching `decode = none` pilot refusals; each
  pin in the tree is proved by `decide` on closed bytes.
- **Witness non-degeneracy.** The decode-level premises for all six extension families
  (+ narrow) are jointly witnessed on real byte rows. The reached two-core
  memory-changing run (owner-only forwarding of 42, drain 0 to 42 observed from both
  cores) is inherited from `hwBild_zeuge` (verified in `HwLoadedImage.lean`), cited not
  duplicated — consistent with SILICON FIRST / REUSE DON'T DUPLICATE, and the witness
  rows are all register-register forms that touch no memory, so there is no per-family
  memory run to duplicate here. The author openly discloses that per-family REACHED
  `fetchExt`-success instances on concrete `FpZustand`/images are not established beyond
  narrow and files exactly that as follow-up work. That is an honest open item, not a
  hidden gap.
- **Silicon facts.** No new encodings, fault classes or ordering rules are introduced;
  everything rests on the accepted pins and dispatch lemmas. No silicon claim to check
  against the SDM extracts beyond reuse, and none is made.
- **CUTS honest, claim within proof.** The CUTS block claims the generic inversion, the
  generic obstruction + six corollaries, six fetch liftings, six image agreements,
  well-formedness survival and the joint decode witness — and explicitly disclaims
  hardware correspondence, per-access W/GX simulation, whole-word atomicity, source/IR/
  ABI/loader/entry/budget links and LOCK RMW. No W/GX or hardware-correspondence claim.
- **Build.** Author evidence: `./lean-probe` 0 errors, `./lean-bau` exit 0 (618 jobs).
  Reviewer run in this clean clone (candidate not applied, per OWN ONLY):
  `./lean-bau` ends with `Build completed successfully (619 jobs).`
  The one-job drift versus the author's 618 is master drift after the candidate base,
  not a candidate failure; I did not rebuild the candidate tree itself.

## Minor observation (not a refusal reason)

The docstring of `hwBildFamilien_schritt_wf` says the family adapters admit through
`adapterBild`, but the proof is the one-line lift of `hwSchritt_wf` and exercises no
adapter. Cosmetic inaccuracy in a comment; the theorem statement and proof are correct
and the CUTS block does not repeat the claim. Suggest fixing the comment on a later
touch, no repair needed.

## What remains open (carried from the candidate, agreed)

- Per-family REACHED `fetchExt`-success instances on concrete images (six small
  `hwBildStart`-style images, one family row each), as the author already filed.
- No hardware correspondence, no W/GX bridge, no LOCK RMW path — all explicitly
  disclaimed.

VERDICT: ACCEPT
