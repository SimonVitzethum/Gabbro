# MUSE-REPORT-1240: exact review of candidate 1239 (AVX2 256-bit integer semantics)

Lane 1240, clone `/home/simon/Dokumente/gabbro-muse/a1240`, branch `muse/1240`
(verified). Owns only this report. Review object: clone-local snapshot
`.tmp/review/author-1239/` — CANDIDATE: author 1239, HEAD
`d4f4924c94988baa8d0781024fc3f706fde63399`, base `ca33ef1b`, files
`MUSE-REPORT-1239.md`, `grammatik/Grammatik.lean` (one import line),
`grammatik/Grammatik/X86/Avx2Ops.lean` (new, 757 lines). No author-clone
access was needed or used; the author clone was never touched.

## VERDICT: ACCEPT

## What was checked

1. Patch shape (`PATCH.diff` + `SNAPSHOT.json`): exactly the 3 declared
   files. `Grammatik.lean` hunk is one added line
   `import Grammatik.X86.Avx2Ops` at the end. Nothing else touched.
2. Forbidden tokens: `rg -nw 'sorry|sorryAx|admit|axiom|native_decide|unsafe'`
   over the candidate file: no matches (the 7 `admit*` hits of a substring
   search are English "admitted/admits" in comments only).
3. Independent typecheck: `./lean-probe <absolute .tmp path of Avx2Ops.lean>`
   against this clone's accepted oleans:
   `== 0 error(s) in the COMPLETE output; exit 0`. Full `#print axioms`
   output re-observed: every theorem depends at most on
   `propext, Classical.choice, Quot.sound` (most on subsets or none) —
   standard, same provenance as the accepted files (`beq_self_eq_true`,
   `mask_and_eq_mod`).
4. Baseline: `./lean-bau` in this clone (candidate not applied):
   `Build completed successfully (651 jobs).`
5. Read the candidate file in full (all 757 lines). Every definition and
   all ~50 theorems inspected; every premise is consumed (by `rw`, `simp_all`,
   or delegation to an accepted lemma). No `intro _`, no `have _ :=`,
   no `split_ifs`/`norm_num`/`ring_nf`.
6. Lift-not-copy, verified by grep over accepted `grammatik/`:
   `ymmAdd/Sub/And/Or/Xor/Cmpeq` halves are `rfl` over accepted
   `vecAdd/vecSub/vecAnd/vecOr/vecXor`; separation/lane laws delegate to
   accepted `vecAdd_allein/vecSub_allein/laneNat_add/laneNat_and/laneNat_or/
   laneNat_xor/laneGet_mk/laneMod_pos/laneNat_lt`; shifts proved equal to
   accepted `vecShlQ/vecShrQ` at `.b64`. `ymmAndn`/`vecCmpeq`/shift-imms are
   built from accepted `laneNat`/`vecMk` vocabulary only — confirmed no
   prior `vecAndn`/`vecCmpeq`/`ymm*`/`avx2Tier*` model exists in the tree,
   so nothing was duplicated and nothing could be lifted instead.
   Gate reuses accepted `CpuMerkmal/Xcr0Bild/KontrollBild/BereitProfil/
   HwProfil` vocabulary (`kontrollSseFrei`, `xcr0AvxBereit`,
   `merkmalZugelassen`, `vektorLegacyZugelassen`, `basisHw/vecZeugeBereit/
   basisCpu/basisXcr0/basisKontrolle`); `avx2Cpu = ⟨true,true⟩` is
   field-order safe (both true). Leaf-level `CpuFeatureHardwareForms.avx2Bereit`
   collision avoided by the `avx2Tier*` rename; no model duplicated.
7. Refusals are real: six `avx2Tier_ohne_*` theorems prove
   `avx2TierZugelassen … = false` from the matching negated input, plus
   `kontrollAvxFrei_braucht_legacy`, the refinement
   `avx2Tier_verfeinert_legacy`, and the `decide`d strictness pair
   (`avx2Tier_strikt`: legacy admits where Tier 3 refuses on the AVX-less
   baseline CPU). None restates a premise; each is a proved gate fact.
8. Witnesses: 9 `_spur` theorems (`decide`), each pinning concrete 256-bit
   values with overflow (`0xFF+1=0` low lane, `2^64-1+1=0`), borrow
   (`0-1=0xFF`), saturation-vs-mask (`ymmSll_spur_saettigung`), sign fill
   and admitted SRA values, compare masks, ANDN — in both halves with an
   independent lane alongside. Rule 13 needs no `_zeuge`: no premise
   quantifies over program syntax. Memory/two-core steps are not applicable
   ("where relevant"): the file defines pure functions with no memory ops.
9. Silicon, checked against clone-local
   `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`
   (325462-093US): VPANDN `DEST := NOT(SRC1) AND SRC2` (lines 74796,
   74800) matches `ymmAndn x y`; VPCMPEQ all-ones-on-equal (75960-75989)
   matches `vecCmpeq`; PSLLW/D saturation `COUNT > 15/31` zeroes
   (85668-85686) matches the `b.bits ≤ c → 0` boundary exactly; VEX.256
   PSRAW/D clamps COUNT to 16/32 (86306+) so sign fill matches the
   saturated branch of `vecSraImm`; VPSRAQ rows are EVEX-only (86175+,
   86511/86530), so W/D-only `ymmSra` is correct and `.b64` SRA is
   total-but-disclaimed, never claimed as an instruction (same for `.b8`
   shifts). `sraLane` is the correct two's-complement shift
   (`2^w − ceil((2^w−x)/2^c)` via Nat division); the admitted-range value
   `0xFF00 >> 4 = 0xFFF0` is `decide`d. No wrong-definition green proof found.
10. CUTS is honest: no decoder/register-file/VZERO/p-state rule, no loads/
    stores/TSO, no `HwAdapter`/`HwSchritt`/`HwWf`, no per-lane SRA equation
    beyond witnesses, no profile↔leaf bridge, no fault/timing claims, no W/GX.

## Known scope gap (declared, not hidden)

The owner task MECHANISM paragraph (HwAdapter, HwWf, two-core memory
`_zeuge`) is not discharged; the author states this in the report (issue 1)
and in CUTS bullet 1, assigning the adapter to the Mem/State integration.
This is the correct call: four independent pieces cannot each define the
machine adapter without duplicating it (rule 16). The FILE SCOPE —
pure semantics, lane separation, exact half-agreement, laws only where
true, carry/overflow witnesses — is delivered complete. Demanding the
adapter here would be the defect, not granting ACCEPT. Integration debt:
the `HwAdapter` + profile↔leaf bridge remain open for the Mem/State
integration lane.

## Reproduction

- `git status` clean except this report; tree work limited to read-only
  probes (one `./lean-bau`, two `./lean-probe`, greps, reads). A compound
  shell copy for an in-tree probe was refused by the tool gate, so the
  candidate was probed at its absolute `.tmp` path instead — imports resolve
  via project oleans, result `0 error(s)`.
- Author BUILD-EVIDENCE shows the path to green including two repaired
  red probes (wrong rewrite patterns; a wrong `decide`d lane value caught
  pre-commit) and the `avx2Bereit` name collision that motivated the rename.

No unsupported correctness premises, no weakened guarantees, no fake
closure. The claim is exactly the proof: self-consistent 256-bit integer
semantics lifting the accepted 128-bit evaluator, with a checked Tier-3
admission gate.
