# MUSE-REPORT-423: BranchLayout (continuous Lean proof reserve)

## What was done

Created the new reusable module `grammatik/Grammatik/X86/BranchLayout.lean`
(~420 lines) plus one additive umbrella line
(`import Grammatik.X86.BranchLayout` after `AccessList` in
`grammatik/Grammatik.lean`). It proves signed displacement
bounds/layout facts for the existing rel32 branch/call encodings and
shapes the future short-branch selection certificate, reusing the
canonical `Codec` bytes, `Relokation` fit/patch arithmetic and
`Ausfuehrung` witness memory. No second IR, executor, decoder or ISA
model; no existing file touched except the one umbrella import line;
friend paths untouched.

Definitions: `dispSigned`, `ZweigForm` (`weit`/`kurz`), `zweigBreite`,
`zweigLaenge`, `ZweigBeleg` (final start/length/form/displacement/target),
`zweigOk` (wide-only, exact final length, next-RIP equation over the
FINAL length, `rel32Passt` reuse).

Theorems (all premises used, no `Prop`-typed premises):
widths/lengths: `zweig_jump32_len`, `zweig_jumpIf32_len`,
`zweig_call32_len` (5/6/5), `zweig_len_stabil_jump32`,
`zweig_len_stabil_jumpIf32`, `zweig_len_stabil_call32` (displacement
change never moves length: no layout optimism for rel32-only layouts);
bounds/fit: `dispSigned_schranke`, `dispSigned_passt`;
byte bridge: `rel32Enc_dispSigned`, `rel32Bytes_dispSigned`
(relocation bytes = codec bytes), `leBytes32_decode_signed`
(sign-extending decode through the existing round-trip);
certificate: `zweigBreite_weit`, `zweigLaenge_weite`,
`zweigLaenge_codec_jump32/jumpIf32/call32` (carried lengths = encoder
lengths), `zweigOk_weit` (acceptance), `zweigOk_kurz` (short refused),
`zweigBeleg_adresse` (accepted cert satisfies the canonical rel32
target equation at final start+final length, via inversion of the
check plus `rel32_adress_gleichung`), `zweigPatch_laenge` (patch keeps
image length: no hidden patch after validation);
probes: `zweig_zeuge_akzeptiert` (4096/5/-5/4096),
`zweig_zeuge_verweigert` (short form, out-of-range disp, wrong length),
`zweig_rel8_verweigert` (EB/127, 0x70/5 refused by canonical decode),
`zweigBeleg_adresse_zeuge` (joint concrete address equation),
`zweig_schreibbar8`, `zweig_lesbar8`, `zweig_speicher_zeuge`
(call return-address store reads back, byte observably changes 0 -> 5).

## Check results (exact)

- `./lean-probe grammatik/Grammatik/X86/BranchLayout.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0` (verified after fixing
  4 elaboration errors: 3 length-agreement goals needed a closing
  `decide`, and `Nat.cast_add` does not exist in this core toolchain,
  replaced by `omega`). Every `#print axioms` is a subset of
  `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.
- `./lean-bau` (4 attempts): RED on exactly ONE target, the final
  `Grammatik` umbrella olean, with
  `lean::exception: failed to create thread`, exit 134. All 391 other
  targets (including `BranchLayout` itself, whose `#print` lines emit
  inside the full build) succeed.
- Control experiment: with my umbrella line stashed (pristine master
  content), `./lean-bau` crashes on the IDENTICAL target with the
  IDENTICAL error. The failure is machine-wide thread exhaustion
  (swap full, dozens of concurrent lanes), not lane content.
- `gabbro_ziel` axiom re-check could not run (same environmental
  crash blocks any full-closure elaboration). By construction it is
  unaffected: `git diff` touches no goal file (only +1 umbrella
  import line), and the new module adds only standard axioms.

## What remains open (also in file CUTS)

Native rel8 selection (no codec row/decoder/stability proof,
unconditionally refused); multi-branch bounded relaxation (DESIGN
§2B fuel rounds, cross-site compression stability, fall-through);
step-level `direktZiel` equations stay in `ControlFlow`, section
mapping in `Bild`, modular target equation in `Relokation`; no
source/TSO/concurrency/cost/hardware claim; validation runs on final
bytes only.

## Task critique

The task is sound and I found nothing wrong in it: the "avoid
iterative layout optimism" requirement is discharged precisely by
length stability + final-length-carrying certificates, and the
"rel8 absent -> OPEN" requirement by unconditional refusal at both
decoder-probe and certificate level. One naming note: the design doc
calls the future form "rel8"/"short Jcc/JMP" while the certificate
calls it `kurz`; the report maps them explicitly.

## Integration gate failure (post-acceptance review): no content repair

The integration gate in `/home/simon/Dokumente/Gabbro` failed with
the byte-identical signature: my module's 27 `#print axioms` lines
all emit inside the integration build (it elaborates cleanly there),
then the single umbrella target `Grammatik` dies with
`lean::exception: failed to create thread`, exit 134. Two further
local `./lean-bau` retries since show the same single-target crash,
for 7 identical failures total (4 lane + 1 pristine-master control +
1 integration + 1 retry), with zero content errors in any of them.

Repair verdict: there is nothing to repair in the owned content, so
nothing was changed in it. Reasons: (a) the umbrella step only loads
already-built oleans, so my tactics cannot re-run or cost threads
there; (b) my imports (`Typen`, `Speicher`, `Ausfuehrung`, `Codec`,
`Relokation`) are all pre-existing umbrella members, so the closure
is unchanged in kind and no cycle is possible; (c) pristine master
crashes identically. Rewriting green proofs to dodge a
`pthread_create` failure would be theater and would risk the verified
content. Concrete blocker for the merger: machine-wide thread
exhaustion (swap full, dozens of concurrent lanes) kills the one
~400-import umbrella elaboration; retry the gate when load dips. No
claim is made about the full source/binary chain. Fresh independent
review is required for the new commit (this report section).
