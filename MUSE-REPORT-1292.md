# MUSE-REPORT-1292: Exact review of candidate 1291 (capstone byte-decoder disjointness)

Lane 1292, clone `/home/simon/Dokumente/gabbro-muse/a1292`, branch `muse/1292` (verified, clean).
Report-only exact review. Pinned head taken from `.tmp/review/SNAPSHOT.json`
(never inspected via git, per task rule):

CANDIDATE: 1291 5589ece657df46cc4141d6631a98f672f2eed39b
Owned file: only this report. No other file in this clone was modified.

## What was checked

Delivered files: `MUSE-REPORT-1291.md`, `grammatik/Grammatik.lean` (one added line),
new `grammatik/Grammatik/X86/HwKapsteinDecoder.lean` (994 lines: `kapDecode` priority
chain over `decodeMulDivWidth` / `s32Decode` / `mxcsrDecode` / `decodeLock` /
`decodeLockAdr` / `decodeC` / `decodeCore` / `Avx2Join.dekodiereAvx2`, agreement
lemmas `kapDecode_breit/s32/mxcsr/lock/lockAdr/kompakt/kern/avx2` + `kapDecode_nichts`
+ `kapDecode_deterministisch`, eight witnesses `kapW_*` with `kapW_*_akzeptiert`,
~50 refusal theorems, `kapKette_*`, overlaps `kapUeber_*`, partitions
`kap_lockModrm_gegen_adrTail` + `kap_lock_gegen_lockAdr`,
`kap_kompakt/kern_weist_sechs_zurueck`, joint `kapDecode_zeuge`).

- Forbidden tokens: grep over the delivered PATCH finds no `sorry`/`admit`/`axiom`
  declaration/`native_decide`/`unsafe` in the Lean code (only `#print axioms` lines and
  the author's prose denial). No `split_ifs`/`norm_num`/`ring_nf`. No `intro _`/`have _ :=`.
- Axioms (independently reproduced, see below): `[propext, Quot.sound]` throughout;
  `kapKette_mxcsr`, `kap_lockModrm_gegen_adrTail`, `kap_lock_gegen_lockAdr`,
  `kap_kompakt/kern_weist_sechs_zurueck`, `kapDecode_zeuge` additionally list
  `Classical.choice`, inherited from reused accepted lemmas. Standard set only, nothing new.
- Existing files: `Grammatik.lean` diff is exactly one added line
  `import Grammatik.X86.HwKapsteinDecoder` (PATCH lines 114-125). Nothing else touched.
- Premise use: every agreement lemma consumes all its hypotheses (`rw` chain);
  `kap_lockModrm_gegen_adrTail`, both §7 lifts and `kapDecode_zeuge` use all premises.
  No `Prop`-typed premises.
- Lifted, not copied: the only new definitions are the `KapDekodiert` wrapper inductive,
  the `kapDecode` chain and closed witness byte lists. All 15+ reused pins/round trips /
  dispatcher lemmas (`pin_wdmul_ecx_dekode`, `decodeMulDivWidth_nichts/wd/prefers_ext`,
  `s32Roundtrip_addssRR`, `mxcsrRoundtrip_ld`, `pin_lock_xadd/mfence_decodiert`,
  `decoder_nimmt_skaliert`, `produzent_weist_skaliert_zurueck`, `roundtripC_movImm32Zx`,
  `roundtrip_andReg64`, `Avx2Join.dekodiere_paddq`, `familien_disjunkt`,
  `wd_mul64_ist_mulRax`, `wd_div64_ist_divRax`, `pin_disp_f64_bleibt_vereinheitlicht`,
  width pins, `pinXadd`/`pinMfence`/`parseAdrTail`/`decodeLockModrm`) verified present in
  this clone's `grammatik/Grammatik/X86/`. No model duplicated.
- Refusals: the ~50 refusal theorems typecheck; `decide` evaluations genuinely evaluate,
  pin-based ones cite verified in-tree pins. They really refuse.
- Witness: `kapDecode_zeuge` reaches all eight arms on eight distinct closed strings;
  §4 shows each level reachable, none shadowed. Memory/two-core non-degeneracy is N/A:
  this lane defines no semantics or memory, and claims none.
- Silicon: no new hardware facts stated; encodings inherited from accepted pins; overlap
  meaning cites accepted evaluator-equivalence lemmas. No SDM re-check owed, none claimed.
- CUTS honest: open domain pairs named as witness-level only, system forms (no byte
  decoder) marked disjoint-by-construction, AVX2 four-row limit named, no W/GX, no
  hardware-correspondence, no source/checker/contract/loader/budget claim. Claim matches proof.
- Cosmetic observations (not verdict-relevant): the `Grammatik.lean` import sits mid-file
  in the X86 group rather than appended at the end; the CUTS block sits at lines 865-912
  with `kap_lock_gegen_lockAdr` defined after it (lines 945-992, with its own
  `#print axioms`). Both harmless; the CUTS prose already covers that theorem.

## Verification (this clone)

- `./lean-probe .tmp/review/author-1291/grammatik/Grammatik/X86/HwKapsteinDecoder.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0` (axiom lines reproduced exactly as above).
- `./lean-bau` (reviewer baseline, candidate not merged here):
  `Build completed successfully (677 jobs).`
- Author build evidence: final probe 0 errors after documented red→green iterations;
  integrated `./lean-bau` 677 jobs success; forbidden-token `rg` clean.

## What remains open (candidate's own CUTS, endorsed)

Full domain disjointness beyond the two proved partitions stays open (most ordered pairs
witness-level only); system forms have no byte decoder; AVX2 covers four pinned rows;
no silicon re-check and no W/GX bridge. The result is weaker than the literal "every
ordered pair" ask and says so plainly; no fake closure.

## Verdict

VERDICT: ACCEPT

No unsupported premises, no weakened guarantees, no closure beyond what is proved.
The known width/unified overlap keeps one evaluator meaning by cited accepted lemmas;
LOCK vs addressed-LOCK is proved disjoint; no divergent-meaning overlap is exhibited
or hidden.
