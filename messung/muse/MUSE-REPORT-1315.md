# MUSE-REPORT-1315: Memory-operand addressing forms for rotates, carry forms and sign/xchg

## What was done

NEW FILE `grammatik/Grammatik/X86/IntMemForms.lean` (1996 lines, 191
def/theorem/inductive/structure declarations) plus one import line in
`grammatik/Grammatik.lean`. No existing file was otherwise touched;
no model was copied -- every family reuses its accepted evaluator.

The rotate (`IntRotate`), ADC/SBB/INC/DEC (`IntCarryForms`) and
sign-extend/XCHG (`IntegerCore` value layer, `XchgOrderNeed` swap
shape) families only admitted the pilot base-plus-disp32 memory shape.
This lane lifts all three to the full selected addressing set
(`AdrForm`/`adrEff` from `AddressEncoding`: SIB choice, RIP-relative,
disp8/disp0) following the accepted `HwAddressed` event pattern.

- §0: `intMemAddr` (selected address on the acting core) with the
  pilot bridge `intMemAddr_basisForm` (= `effAddr`); width codec bits
  `breitenCode`/`codeBreite` with `codeBreite_breitenCode`.
- §1: descriptors `RotVoll` (op/width/resolved count/full form/len),
  `CarryVoll` (`adcV`/`sbbV`/`adcIV`/`sbbIV`/`incV`/`decV`),
  `SignVoll` (8/16/32-bit source, 64-bit refused by `signVollOk`),
  `XchgVoll` (load-modify-store, no atomicity claim).
- §2: value agreement, never a second model: `rotVollNeu`/`rotVollFlags`
  (`rotVollNeu_rol/_ror/_rcl/_rcr`, `rotVollFlags_gleich`,
  `rotVollFlags_gueltig` reusing `rotFlags_gueltig`);
  `carryVollNeu` (`carryVollNeu_adcV/_sbbV/_adcIV/_sbbIV/_incV/_decV`,
  `carryVollNeu_inc_cf/_dec_cf`); `signVollNeu`
  (`signVollNeu_gleich` = `sext`, `signVollNeu_movsx8`);
  `xchgVollNeuReg` (`xchgVollNeuReg_gleich`, `_b64` = accepted swap shape).
- §3/§4: TSO load-modify-store events `rotVollSchritt`,
  `carryVollSchritt` (extractors `carryVollBreite/_Form/_Laenge`),
  `signVollSchritt` (pure load, flags kept, buffer kept),
  `xchgVollSchritt`. Each with exact-`entriesOf`-footprint,
  no-canonical-change, RIP, flags, well-formedness and planted
  refusals (bad length, refused load gate, 64-bit sign source).
- §5/§6: NEW canonical lifted bytes (tags 113 rotate, 114 carry,
  115 sign, 116 XCHG -- read by no accepted decoder, nothing
  shadowed) over the accepted `encodeAdr` tail with REX check:
  `rotVollEncode`/`decodeRotVoll`, `carryVollEncode`/`decodeCarryVoll`
  (incl. 8-byte immediates via `leBytes64`/`parseLe64`),
  `signVollEncode`/`decodeSignVoll` (64-bit source refused),
  `xchgVollEncode`/`decodeXchgVoll`. Pinned SIB and RIP-relative
  round trips per family (`rotVollRundweg_sib/_rip`,
  `carryVollRundweg_sib/_rip/_sibImm`, `signVollRundweg_sib/_rip`,
  `xchgVollRundweg_sib/_rip`), encode-needs-admission
  (`*_braucht_ok` via `encodeAdr_verweigert_ohne_ok`), unadmitted
  refusals (`rsp` index, `rbp` without displacement), LOCK refusal on
  every tag (`decode*_lock_verweigert`, LOCK 240 matches no tag).
- §7: `IntMemEreignis` + `adapterIntMem : HwAdapter IntMemEreignis`
  with exact step agreement (`adapterIntMem_rot/_carry/_sign/_xchg`),
  `adapterIntMem_wf`, length refusals, `adapterIntMem_verweigert`.
- §8: reached two-core witness `intMemWit_zeuge`: SIB INC then SIB
  ROL with owner-only forwarding and two observable drains (byte
  0->1->2 at 8200), RIP-relative XCHG (7 for 2, drained to 7) and a
  sign load back (rax=7) -- beside adapter agreement on the run
  (`intMemWit_adapter_m1`), LOCK refusal, SIB refusal and
  `intMemWitM0_wf`. Non-degenerate: three drains observably change
  shared memory; every buffered store is forwarded to the owner only.

## Verification

- `./lean-probe grammatik/Grammatik/X86/IntMemForms.lean`: 0 errors.
- `./lean-bau`: `Build completed successfully (688 jobs)`, exit 0.
- `#print axioms` for all 36 main theorems: only `propext` and
  `Quot.sound` (subset of the allowed set); no `sorry`, `admit`,
  `axiom`, `native_decide`, `unsafe` in the file (scanned).
- No `Grammatik.lean` change beyond the one import line; no other
  file touched (`git status` shows only `IntMemForms.lean` uncommitted
  before this report).

## What remains open (see CUTS)

- No hardware correspondence for the new tags 113-116 (self-consistency
  only); value shapes reuse the accepted families' silicon assumptions.
- No byte-fetched execution of the lifted tags (no `decodeExt` arm);
  no length-cap theorem beyond the pinned lengths 7/9/15.
- No atomicity for XCHG (load-modify-store events only); the locked
  leg stays with the locked families. No faults beyond gate refusals,
  no interrupts, no W/GX bridge, no source/ABI/loader/entry/budget link.

## Task feedback

Nothing in the task was wrong. Two apparatus notes: (1) Lean 4.33
rejects a multi-line `{ ... with ... }` structure update nested inside
a `fun`/`if` in this position -- reused the canonical `setKernDaten`
instead (also the better reuse). (2) `cases h : e` generalises
occurrences of `e` in the goal too, so existential load-equation
conjuncts are closed by `rfl` after the split (sound: the branch
equation sits in context and drives the footprint proof).
