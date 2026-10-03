# MUSE-REPORT-976: exact review of author 826 (relocation-to-redecode closing)

## Clone / branch

- Clone `/home/simon/Dokumente/gabbro-muse/a976`, branch `muse/976`: verified, match.
- Owned file only: `MUSE-REPORT-976.md`. No source or live-control file touched.

## Pinned snapshot

CANDIDATE: 826 822160c2da462a8718537c1bec334b6487b6887e
- Pinned base `e7c75908456285d1e37c18dc32d4f9c0e10d1fa4` equals this clone's
  HEAD at review time. Snapshot `clean: true`.
- Files: `MUSE-REPORT-826.md`, `grammatik/Grammatik.lean` (one appended
  import line), `grammatik/Grammatik/X86/ComposeRelocRedecode.lean` (new,
  265 lines). No other file in the PATCH.

## Independent verdict

VERDICT: ACCEPT

Acceptance is bounded as documented in the note below.

The candidate genuinely closes the stated gap: finite file-byte patching
(`Relokation.patchAt`) to re-decoding through the canonical decoder, plus
layout-hint re-decision. The core composition is generic over arbitrary
inputs, reuses only accepted producer theorems by name, creates no second
decoder/loader/executor/ISA model/IR, and carries planted refusals plus
explicit CUTS. One limitation (run conjunct is instruction-class
disconnected, see below) is real but formally harmless, accurately
documented, and explicitly cut -- it is recorded here as a bounded-acceptance
note with a follow-up direction, not a repair demand, because no claim made
is false and no guarantee is weakened.

## What was reviewed (exact names)

New definitions/theorems in `ComposeRelocRedecode.lean`:

- `redecodeFenster`: `len` bytes at file offset `off` of a patched image.
- `patchAt_segment`: successful `patchAt` writes exactly the patch bytes at
  the site window (induction matching `patchAt`'s recursion).
- `ComposeRelocRedecode_verbindung` (TARGET): patch success + site-equation
  block (`hdisp`, `hgleich`, `hfit`, `hnext`, `hziel`) + `hhint` imply
  re-decode through canonical `decode` to `relocBefehl s.art d` at its
  carried length, `direktZiel` word and Nat equal `s.ziel`, `hinweis =
  layoutFuer u basis ausr` with `layoutOk = true`, and the accepted
  relocated call run with observable stack write.
- `ComposeRelocRedecode_verbindung_zeuge` (companion): joint premise
  inhabitation on `siteVor` + `BitVec.ofNat 32 16` + `[233,16,0,0,0,255]`
  + `zeugenU` + recomputed layout hint, all premises by `decide`.
- `ComposeRelocRedecode_durchgehend`: closing applied to the witness values.
- Planted refusals: `relocRedecode_innen_verweigert` (interior target),
  `relocRedecode_aussen_verweigert` (out-of-range displacement),
  `relocRedecode_ueberlapp_verweigert` (overlap, patch and layout sides).

Reused by name, never re-proved: `patchAt`, `relocBytes_decode`,
`patchSite_ziel`, `ruf_schritt_zeuge`, `hinweisOk_layoutOk`,
`sonde_patchZwei_ueberlappung`, `ueberlapp_verweigert`, `decode`,
`direktZiel`. Each name was confirmed present in this checkout's base tree
(`Relokation.lean`, `RelocatedExecution.lean`, `TableLayout.lean`,
`ControlFlow.lean`).

## Architecture check (not just Lean green)

- Byte forms: witness `relocBytes .sprung 16` = `E9 10 00 00 00`
  (`JMP rel32`, Intel encoding E9 + disp32, length 5); patched window
  `[233,16,0,0,0,255]` keeps one trailing file byte outside the site --
  the window/re-decode split is exactly at the carried length. Short/abs64
  forms are correctly NOT claimed (explicit producer-cut CUTS).
- REX/register/width/flag semantics: rel32 JMP/CALL carry no REX, ModRM or
  SIB; the closing routes length/opcode/target-start through the canonical
  decoder's own verdict and asserts no register or flag effects. Nothing is
  zeroed or ignored that the forms define.
- Operands: `direktZiel` computes next-RIP + sign-extended disp through the
  accepted `dispWort_bridge`; the site equation `4096 + 5 + 16 = 0x1015`
  was arithmetically verified. The implicit stack write lives only in the
  reused call witness and is not attributed to the jump -- see limitation.
- Pre-fault effects, memory order, TSO/atomicity, feature/MXCSR/interrupt
  gates: no claim made; CUTS explicitly leave `valX86_sound`, source/TSO-GX,
  concurrency, cost, FP and hardware behaviour to consumer lanes. No
  invented determinism over undefined state.
- Canonical execution interaction: re-decode uses canonical `decode`;
  execution reuses the accepted `byteschritt` witness. No parallel
  interpreter on the trust path.

## Premise use, witnesses, mutations, CUTS

- Every premise of the TARGET is load-bearing in the proof: `hpatch`
  drives `patchAt_segment` and the `rw`; the site-equation block drives
  `patchSite_ziel`; `hhint` drives `hinweisOk_layoutOk`; `suffix` shapes
  `relocBytes_decode`. No restated conclusion, no discarded premise, no
  `forall`-quantified contract value.
- Non-degeneracy: `zeugenU` is the table-`konto`-written-by-`setze` unit
  (`TableLayout.lean`); `siteVor` is the accepted forward-jump site
  (`vor_akzeptiert` in base). The `durchgehend` run changes memory
  observably (stack slot `0x1FF8` written, read back as `0x1005`, bytes
  differ from initial). Joint inhabitation holds on concrete values.
- Negative mutations: interior target patches but is refused by
  `patchSiteOk`; `2^31` computes no bytes and is refused with the site;
  overlap is refused on both patch and layout sides via accepted producer
  witnesses. Patching alone admits nothing.
- CUTS block lists exactly what is proved and leaves `valX86_sound`,
  abs64/rel8/other-instruction site classes, multi-site convergence,
  fall-through/`DecodingCoverage`, and loader/entry/OS modelling OPEN with
  owning lanes named. Claim boundary is precise.
- Hygiene from full read of the candidate file: no `sorry`/`admit`/`axiom`/
  `native_decide`/`unsafe`; English only; no diagnostic/gift/example/CLI
  numbers, no MARKE changes, no source/checker/Spec/goal/emitter or
  friend-reserved file edits.

## Bounded-acceptance note (no repair required)

The conclusion's run conjunct is the closed, unconditional producer fact
`ruf_schritt_zeuge` (a CALL run through `siteRuf`), sharing no variable
with the generic site `s`. On the witness values the decoded instruction
is a JUMP (`siteVor.art = .sprung`) while the exhibited run is a CALL --
same reached target value `0x1015`, different instruction class. The formal
statement stays TRUE (an unconditional true conjunct), and the author's
report and file comments describe it accurately as "the accepted relocated
call run", never as "the patched site's own execution". A strictly
through-composed run (e.g. a `.ruf`-specialised closing deriving the run
from `patchSite_ruf_schritt` under explicit state/window/write premises)
remains a worthwhile follow-up, but demanding it here would change the
interface the task fixed. No fake closure: the novel composition
(patch bytes -> canonical re-decode -> intended target -> re-decided
layout) is generic and connected.

## Evidence and independent reproduction

- Author BUILD-EVIDENCE (from the author's own clone, inspected, not
  re-attributed): `./lean-probe .../ComposeRelocRedecode.lean` ==
  `0 error(s)`; `./lean-bau` == `Build completed successfully (509 jobs)`;
  closing and end-to-end on exactly `propext, Classical.choice,
  Quot.sound`; helpers `propext`-only or none.
- Independent reproduction by this reviewer: NOT performed by execution.
  The `bash` tool (needed for `./lean-probe`, `./lean-bau`, and `git
  apply --check`) was denied by the permission classifier during this
  lane, so no queued wrapper could be run and no build line of my own can
  be reported. Verification above rests on: complete line-by-line read of
  the candidate file (265 lines) and PATCH in `.tmp/review/author-826/`;
  producer-name and witness-value confirmation by search/read in this
  clone's base tree at the pinned base commit; arithmetic re-derivation of
  the witness target equation. This is the honest boundary of this review:
  architecture and proof-structure ACCEPT on full textual evidence, with
  machine re-execution left to the serial integration gate (which must
  still build green before any merge).
- No network, provider, other-clone, or key access was used. Only
  `MUSE-REPORT-976.md` is owned and committed by this lane.

## Open / follow-up

- Suggested (not blocking): a `.ruf`-specialised closing that derives the
  memory-changing run from `patchSite_ruf_schritt` for the actual patched
  site, so a future consumer gets a same-instruction-class run.
- Nothing in the owner task text is wrong. The author's clarification note
  (reuse of the accepted run witness vs. a forbidden second executor) is
  an accurate reading of the task constraint.
