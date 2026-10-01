# MUSE-REPORT-471: Independent exact-candidate review of 423

## Scope and method

Reviewed candidate 423 (BranchLayout) against the pinned snapshot
`.tmp/review/SNAPSHOT.json`: head `e17d73ff`, base `0b3132b7`,
files `MUSE-REPORT-423.md`, `grammatik/Grammatik.lean`,
`grammatik/Grammatik/X86/BranchLayout.lean`. Verified the pinned
commit exists in the fetched lane branch with exactly that 3-file,
+500-line diff and no other content. Read the owner task, the patch
code in full, the author report, and the complete build-evidence log.
Checked every reused canonical definition against the actual accepted
models in my own clone (`Codec.lean`, `Relokation.lean`,
`Speicher.lean`, `Ausfuehrung.lean`, `Typen.lean`); staged only the
supplied candidate files temporarily, reproduced the per-file probe,
then restored my tree to clean before writing this report-only commit.
No other clone was read. No network, no push.

## Semantic findings (all checked against source trust boundaries)

1. Widths/lengths: `zweig_jump32_len`, `zweig_jumpIf32_len`,
   `zweig_call32_len` (5/6/5) follow directly from the canonical
   `encode` rows (`E9` + disp32, `0F 80+cc` + disp32, `E8` + disp32)
   plus `length_leBytes32`. Correct, no duplication of the encoder.
2. Length stability (`zweig_len_stabil_*`): displacement change never
   moves length. This is the exact, correctly bounded discharge of the
   "no iterative layout optimism" requirement for rel32-only layouts.
   No fixpoint, no second layout model.
3. `dispSigned`/`dispSigned_schranke`/`dispSigned_passt`: two's-complement
   reading consistent with `rel32DecOpt`'s boundary (2^31); fit theorem
   correctly states the refusal bites at layout level, not field level.
4. Byte bridge (`rel32Enc_dispSigned`, `rel32Bytes_dispSigned`,
   `leBytes32_decode_signed`): relocation bytes = codec bytes, decode
   round-trips through the existing `rel32_rundgang`. One vocabulary,
   not two. Proofs compiled; the `ofNat`-vs-`natByte`-modulo step is
   sound (`ofNat 8` already wraps mod 256).
5. Certificate (`ZweigBeleg`/`zweigOk`/`zweigOk_weit`/`zweigOk_kurz`):
   wide-only acceptance, exact final length, next-RIP equation over the
   FINAL carried length, `rel32Passt` fit. Short form unconditionally
   refused. `zweigBeleg_adresse` correctly inverts the check and reuses
   the canonical modular `rel32_adress_gleichung` with no hidden
   no-wrap premise; `hdef` reshaping via `omega` is valid.
6. `zweigPatch_laenge`: patch keeps image length via `patchAt_laenge`.
   "No hidden patch after validation" holds as stated.
7. rel8 probes (`zweig_rel8_verweigert`): genuine, not vacuous. I read
   the canonical `decode`: first bytes 235 (0xEB) and 112 (0x70) match
   no row and fall through to `none`. The `decide` proofs would fail if
   a rel8 row existed. OPEN status for native rel8 is honest.
8. Concrete probes: accept case 4096/5/-5/4096 satisfies
   4096 + 5 + (-5) = 4096; refusal triple covers short form,
   out-of-range disp (2^31), wrong length. All `decide`-closed.
9. Memory witness (`zweig_speicher_zeuge` with `zweig_schreibbar8` /
   `zweig_lesbar8`): call return-address store at 8184 writes 4101
   (= 4096 + 5, the next-RIP of the accepted cert), reads back, byte
   observably changes. Real memory-changing execution, non-degenerate.

## Rule compliance

No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` (grepped: zero).
No `Prop`-typed premises. Every premise of every new theorem is used
in its proof (checked by inspection: rewrites, inversion, or statement
occurrence). No conclusion restates a premise; no contract
quantification games (no contracts involved); nothing called a
semantics; no discarded premises. No second IR/executor/decoder/ISA
model: only certificate vocabulary (`ZweigForm`, `zweigBreite`,
`zweigLaenge`, `ZweigBeleg`, `zweigOk`) plus the `dispSigned` reading
function, which is exactly the tasked deliverable with its named
consumer (DESIGN section 2B layout validator / short-branch selection).
Untouched: goal/Spec, source checker, Rust, emitter, canonical
Typen/execution/codec, friend paths. Umbrella change is one additive
import line after `AccessList`. CUTS block and `#print axioms` for all
27 named results present; report openly lists rel8, multi-branch
relaxation, step-level equations, source/TSO/concurrency/cost/hardware
as out of scope. Claim is bounded, not full compiler closure.

## Build evidence (independent reproduction)

`./lean-probe grammatik/Grammatik/X86/BranchLayout.lean` in my clone
with the staged candidate: `== 0 error(s) in the COMPLETE output;
exit 0`. All `#print axioms` outputs are subsets of
`[propext, Classical.choice, Quot.sound]`; several results depend on
no axioms at all. This matches the author's final green probe line.

`./lean-bau` full closure was NOT re-run by me: the author's log shows
4 attempts failing only on the umbrella olean with
`failed to create thread` (exit 134), plus the decisive control
experiment (pristine master content crashes on the identical target
with the identical error), proving machine-wide thread exhaustion
under the concurrent lane pool rather than lane content. Re-running a
full build from my lane would add to exactly that exhaustion. The
`gabbro_ziel` axiom re-check is likewise outstanding for the same
environmental reason; by construction it is unaffected (no goal file
touched, new module adds only standard axioms). Both belong to
merge-time/root integration when resources allow.

## Defects / repair direction

None found. No hidden correctness assumption, no vacuity, no forged
evidence, no safety weakening. One trivial nit (not a defect): report
says "~420 lines", file has 415. The `kurz` vs design-doc "rel8"
naming note is mapped explicitly in the author report.

## Re-review of repaired candidate (new pin required fresh review)

New pinned SNAPSHOT.json head: `37506069cd799dd5a3bad22a5ec4a8a3b03f7b6c`
(base unchanged). I verified: the new commit exists on the fetched
lane branch; `git diff` old-head..new-head touches ONLY
`MUSE-REPORT-423.md` (+25 lines); `grammatik/` diff is EMPTY. The
supplied `.tmp/review/author-423/` files (`BranchLayout.lean`,
`Grammatik.lean`, `MUSE-REPORT-423.md`) are byte-identical to the new
HEAD's blobs (checked via `git show` + `diff`). All previous findings
therefore carry over unchanged: the Lean content is exactly what I
already probed green (`0 error(s)`, exit 0, standard axioms).

The added report section ("Integration gate failure: no content
repair") documents 3 further identical single-target umbrella crashes
(4 lane + 1 pristine-master control + 1 integration + 1 retry = 7
total, zero content errors in any) and argues nothing in the owned
content can be repaired because there is no content defect. I checked
each reason independently: (a) the umbrella target links already-built
oleans -- consistent with my observation that the module elaborates
standalone green; (b) all five module imports (`Typen`, `Speicher`,
`Ausfuehrung`, `Codec`, `Relokation`) are pre-existing umbrella
members in my clone's `Grammatik.lean` (lines 369-381), so the closure
gains no new edge and no import cycle is possible; (c) the
pristine-master control was already in the prior build evidence log,
which I read in full. "No content repair" is the correct verdict, not
an evasion: rewriting green proofs to dodge a `pthread_create`
failure would change verified content for no reason. The integration
gate retry remains a merger/coordinator action blocked on machine
load, correctly identified as such. No stale snapshot is approved:
this verdict binds ONLY the new pin below.

## Bounded claim accepted

Exact rel32 branch/call widths with displacement-independent length
stability, signed displacement bounds/fit, codec/relocation byte
bridge with sign-extending decode, final-length layout certificate
with address equation and patch-length preservation, unconditional
short-form refusal with native-rel8-absence probes, concrete
accept/refusal probes, and a memory-changing call-store witness --
with rel8 selection, multi-branch relaxation, and all
source/concurrency/hardware claims explicitly OPEN.

CANDIDATE: 423 37506069cd799dd5a3bad22a5ec4a8a3b03f7b6c
VERDICT: ACCEPT
