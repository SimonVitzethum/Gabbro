# MUSE-REPORT-659: Independent exact-candidate review of author 658

## Scope

Review-only lane. No source edits; this report is the only owned file.
Clone verified: `/home/simon/Dokumente/gabbro-muse/a659`, branch `muse/659`.
Candidate commit `76640820e62e1daf03a3471af9c5920a3adf623a` is not in this
clone's object store, so the review was done against the exact pinned
material in `.tmp/review/`: `SNAPSHOT.json` (author 658, that HEAD, base
`24e625c0`, files `MUSE-REPORT-658.md` + `grammatik/Grammatik.lean` +
`grammatik/Grammatik/X86/FloatValidatorAdmission.lean`, clean) and
`author-658/` (`OWNER-TASK.md`, `MUSE-REPORT-658.md`, `PATCH.diff`,
`BUILD-EVIDENCE.json`, pinned `grammatik/` copy).

Base `24e625c0` is an ancestor of this clone's HEAD, and every producer
file the candidate reuses is byte-identical between base and HEAD
(`git diff 24e625c0 HEAD` over all 14 producer paths: only
`Grammatik.lean` differs by one later import line). So all name/signature
checks below, done in this tree, apply exactly to the candidate's base.

## What was checked

1. **File set and touch boundary.** PATCH touches exactly the three
   snapshotted files. The `Grammatik.lean` hunk is one appended import
   line (`import Grammatik.X86.FloatValidatorAdmission`) at the end.
   No checker, Spec, goal, Rust, emitter, or friend-reserved
   (`OptimizationRules`/`OptimizationWitnesses`) edit. No second
   executor or decoder is introduced: `FpZustand`, `fpByteschritt`,
   `fpDecode`, `fpSchritt` are reused untouched.
2. **Every reused producer resolves with a matching signature:**
   `fpDecode`/`fpFetchDekodiert`/`fpByteschritt`/`fpGeholt`,
   `fpFetchDekodiert_erfolg` (4-conjunct shape matches the use in
   `valFp_gibt_bytes`), `fpByteschritt_profil_verweigert`,
   `fpSchritt_erhaelt_fp` (`t'.fp = t.fp`; the `exact hkeep` step closes
   `t'.fp = k` because `fpBildT ... k |>.fp` reduces to `k`),
   `fpSchritt_movsdSpeichere_erfolg` (argument order
   `d t base src disp m hok hfp h hwr` matches the `fpStore_schritt`
   call), `read64_nach_write64`, `null_beobachtung_zeuge`,
   `fpEintritt` (`mxcsrGueltig k.mxcsr`), `bereit` (the
   `.sseDoppel` arm is `mxcsrGueltig b.mxcsr && b.osXmm`, so
   `valFp_gibt_bereit`'s `simp [hg]` is a genuine transfer, not a
   vacuous close), `mxcsrOk`, `kontextReset`, `fpZeugeKern`,
   `bildZustand`, `storeFlags`, `wohlgeformt`, `eintragEnthalten`,
   `ladenAusfuehrbar`, `geladen`, `writeBytes`, `natByte`,
   `fpEncodeMovsdSpeichere`, `FpBefehl.movsdSpeichere`,
   `FpDecodiert.laenge`, `Profil.p48`, `Abschnitt`/`Bild`/
   `EintrittZustand`/`FPKontext` fields, `ripNach`, `effAddr`,
   `write64`/`read64`, `lesbar8`/`schreibbar8`, `laengeOk`,
   `ausfuehrbarN`, `vecJoin`, `xmmTief`.
3. **Decode is derived, never trusted.** `valFpEintrittStark` takes no
   `FpDecodiert` from the caller; the fetch leg is
   `(fpFetchDekodiert (fpBildT ...)).isSome`. `valFp_schritt` unfolds
   the real `fpByteschritt` (which matches on its own fetch, then the
   accepted `fpSchritt`) and rewrites with the fetched equation `hf`
   and the step equation `hs`. No forged fetched input can enter.
4. **No desired correspondence as premise.** `fpVal_gelenk_zeuge` has
   no premises at all: both sides are proved, and no lowering between
   loaded bytes and the source run is claimed. The 12-component
   destructure of `null_beobachtung_zeuge` lines up positionally
   (schreibt-D, schreibt-V, exec, before, after, x-ne, vgl, roh,
   passt, bits-ne); the needed conjuncts are supplied from the named
   ones. The source side is non-degenerate (reached one-step run,
   table written, slot `-0 -> +0` with disagreeing `zuBits`); the
   target side has a real memory change (`fpStore_aendert`, top
   footprint byte `0x00 -> 0x7F` for `+inf`).
5. **Refusals are planted and specific.** Truncated bytes (fetch
   `none` + check `false`), FTZ word refused at three doors
   (`fpByteschritt`, strengthened check, `mxcsrOk`), W^X map refused
   plus data-RIP fetching `none`, forged entry word (`k.mxcsr = z.mxcsr`
   binding) refused while bytes fetch and the word alone is valid.
   Each varies one leg; each is `decide`d on actual bytes/words.
6. **Hard-rules hygiene.** No `sorry`/`admit`/`axiom`/`native_decide`/
   `unsafe` (remaining grep hits are prose mentions and `#print
   axioms` lines); no `intro _` / `have _` discards; no `Prop`-typed
   premises; every premise of every theorem is used. No theorem takes
   a premise quantifying over source syntax, so rule 13 needs no
   per-theorem `_zeuge`; the joint witness covers inhabitation
   honestly. CUTS block and `#print axioms` for every main theorem are
   present. Reported axioms (`propext`, plus inherited `Quot.sound` /
   `Classical.choice`) are within the standard goal set.
7. **Claim size matches proof.** Optional new admission only; old
   `valX86`/checker untouched. CUTS disclaim `valX86_sound`,
   source-to-bytes closure, hardware correspondence, concurrency/TSO,
   and the canonical subset; ADDSD loaded consequence is named as the
   next task, not claimed. No inflated completion.
8. **ExtendedExecution note.** The author's remark that no
   `ExtendedExecution575` file existed is true for their base: that
   file arrived with the lane-575 merge after the base. No name in the
   candidate collides with anything in the current tree, and the
   shared `FpZustand`/`fpByteschritt` interface is untouched, so a
   later extension consumes it without conflict.
9. **Build evidence.** `BUILD-EVIDENCE.json` shows genuine incremental
   work (red `lean-probe` intermediates repaired step by step to
   `0 error(s)`, final `./lean-bau` green at 458 jobs). I did not
   re-run builds: this is a report-only lane (no source edits allowed,
   so the candidate file cannot be placed in this tree for probing),
   and static verification of every reuse above is exhaustive. The
   serial merge gate re-runs the full build before integration.

CANDIDATE: 658 76640820e62e1daf03a3471af9c5920a3adf623a

VERDICT: ACCEPT

Accepted bounded claim: the optional strengthened FP admission
`valFpEintrittStark` over actual loaded scalar FP bytes (checked
mapping AND entry containment AND execute byte AND derived
fetch-and-decode AND MXCSR profile admission AND entry discipline with
the control word bound to the entry word), with its seven projections,
feature-readiness transfer, generic entry-at-decoded-start consequence,
loaded-step consequence through the real `fpByteschritt`, four planted
refusal shapes, one admitted loaded MOVSD store of `+inf` with a real
memory change under untouched executable bytes and control word, and a
joint side-by-side witness with a reached source table write. Open cuts
are exactly as stated in the candidate's CUTS: no `valX86_sound`, no
source-to-final-bytes closure, no hardware or concurrency claim,
canonical subset only.

## Minimal follow-up (not a repair condition)

Prove the ADDSD register loaded-byte consequence through this admission,
or close the relocation-patched FP byte re-decoding leg, as the author
suggests. No repair is required for this candidate.
