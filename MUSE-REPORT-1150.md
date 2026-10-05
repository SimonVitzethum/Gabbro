# MUSE-REPORT-1150: Exact review of candidate 1149 (capstone coherent machine)

## Candidate

- Author lane 1149, pinned HEAD `8097310de1eebe2b20bf1fa3f590d2ae7e668a53`, base `515546d0`.

CANDIDATE: 1149 8097310de1eebe2b20bf1fa3f590d2ae7e668a53
- Snapshot files (`.tmp/review/SNAPSHOT.json`, `clean: true`): exactly 3 —
  `MUSE-REPORT-1149.md`, `grammatik/Grammatik.lean`, `grammatik/Grammatik/X86/HwKapstein.lean` (1023 lines).
- Review source: staged exact snapshot `.tmp/review/author-1149/` (`PATCH.diff`, `BUILD-EVIDENCE.json`,
  owner task, author report). The author clone itself was never touched
  (one `git -C` attempt was correctly refused by the permission classifier).

## Checks performed

1. **Forbidden tokens**: grep over staged `HwKapstein.lean` for `sorry`, `axiom` declarations,
   `native_decide`, `unsafe`, `sorryAx`, `split_ifs`, `norm_num`, `ring_nf`, `intro _`, `have _ :=`
   — clean. Only English comment substrings (`admitted`, `admit nothing`).
2. **Axioms**: `#print axioms` present for every main theorem (lines 976–1021).
   Build evidence shows `[propext, Quot.sound]` throughout (subset of the goal standard),
   `kap_tags_disjoint` axiom-free. Standard.
3. **Existing files**: `Grammatik.lean` diff is exactly one appended line
   (`import Grammatik.X86.HwKapstein`, PATCH.diff hunk at old line 644). Nothing else touched.
4. **Premise use**: every premise of every theorem is used (`kap_wf` cases on the step and
   applies `hwf` in all 21 arms; helpers consume `h`/`hwf`; embeddings are iffs over all binders;
   `kap_decode_prioritaet` uses `bs/i/rest/h`; `kap_tags_disjoint` universals are introduced
   and consumed by constructor discrimination). No `Prop`-typed premise, no discarded premise,
   no contract-parameter quantification (hardware events only — rule 13 `_zeuge` obligation
   does not trigger; `kap_zeuge` is premise-free and serves as the joint witness).
5. **Lifted, not copied**: all 21 union constructors carry the families' accepted adapter
   equations/relations (`HwSchritt`, `adapterLockRmw`, `adapterWort1147`, `stapelAdapter`,
   `adapterIsa`, `adapterAddr`, `adapterMulDivWidth`, `adapterLockFetch`,
   `HwDev1133.adapterUc1133/port`, `FpCtrlSchritt`, `HwFehlerSchritt`, `HwTorSchritt`,
   `HwVecSchritt`, `drainAdapter`, `fwdAdapter`, `adapterVerschachtelt`,
   `adapterInterrupt1125`, `adapterSystem`, `adapterBild`, `adapterInstanzen`).
   The three wf helpers unfold and cite accepted lemmas (`asyncSchritt_wf_allgemein`, …).
   No evaluator redefined.
6. **Refusals**: `kap_verweigert` cites five accepted refusal lemmas (DMA, fault-as-state-step,
   ISA/addressed refusal events, bare LOCK); `kap_zeuge` pins four concrete refusal instances
   (DMA `lese`, fault `abruf/pf`, `hwLockWit_reg_ud`, misaligned `stapelWit_ruf`). They really refuse.
7. **Witness non-degeneracy**: locked word 10→15, two-core eigen/fremd sights
   (`hwLockWit_nach1_eigen/fremd_sicht`), owner-only forwarding
   (`stapelWit_weiterleitung` + `fremd_alt`), drains changing shared memory observed from
   both cores (`hwWit_weiterleitung`, `hwWit_fremd_alt`, `hwWit_spülung_aendert_speicher`,
   both `spuelung_aendert_speicher` lemmas). 15 exhibited union steps; the 6 equation-only
   tags (`port`, `nested`, `int`, `system`, `bild`, `instanzen`) are openly listed in CUTS.
8. **Silicon**: no new silicon facts. Decoder pins reuse accepted pins
   (`pin_wdHw_wdmul32`, `pin_wdHw_ext_mul64`); `kap_decode_prioritaet` lifts
   `decodeMulDivWidth_prefers_ext`; fault/UC/vector steps reuse family witnesses.
   CUTS disclaims hardware correspondence beyond self-consistency. No W/GX claim anywhere.
9. **CUTS honesty / claim size**: the open list (equation-only tags, `HwBildFamilien`/`HwFeatureStep`
   without tags, byte-decoder disjointness beyond width-vs-unified, async snapshot boundary)
   matches the proved content. Two known partials are declared, not hidden:
   (a) tag disjointness proves base-vs-each-family (20 conjunctions) plus the width-vs-unified
   byte lemma — family-vs-family pairwise tag inequality and wider byte-decoder disjointness
   stay open in CUTS with "no unhandled overlap found";
   (b) six tags embed by equation only, successes exhibited in family files.
   Neither is claimed as proved. This is honest partial discharge, not fake closure.
10. **Build**: author evidence — final `./lean-probe` 0 errors, `./lean-bau` exit 0
    (`Build completed successfully (644 jobs)`). Own clone `./lean-bau`: green,
    `Build completed successfully (665 jobs)` (newer base; candidate file not in this tree,
    so this confirms base health — candidate build relies on author evidence plus the
    staged zero-error probe trail).

## Notes (not verdict-changing)

- N1: `kapTag` assigns distinct numbers 0–20 but injectivity/pairwise family inequality is
  not separately proved; only base-vs-each is. Mechanical follow-up, openly in CUTS scope.
- N2: author report's "What I believe is wrong in the task" (lane-number/module mismatch,
  partial decoder disjointness, async snapshot boundary) is accurate and consistent with CUTS.
- N3: one `./lean-bau | grep` re-run for the exact summary first-line was refused by the
  permission classifier; the completed-run last line above is reported instead.

## Verdict

VERDICT: ACCEPT

Candidate 1149 at `8097310de1eebe2b20bf1fa3f590d2ae7e668a53` is accepted as stated:
21-arm coherent union with exact per-family embeddings, `HwWf` preservation, proved refusals,
honest tag/decoder disjointness boundary, non-degenerate joint witness, standard axioms,
one-import-line footprint, and no claim beyond the proof.
