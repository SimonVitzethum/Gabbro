# MUSE-REPORT-1290: Exact review of candidate 1289 (capstone union steps)

## Verdict

CANDIDATE: 1289 27d7ccc4b2d704eee96b6cc53433e38f40698f99
VERDICT: ACCEPT

Candidate 1289 (`27d7ccc4b2d704eee96b6cc53433e38f40698f99`, base
`63e2ec3543deec0c4cce21e9431dfffba157ebd6`) is accepted as reviewed.
No unsupported desired-correctness premise, no weakened guarantee, no fake
closure found. Scope of the verdict: the delivered files only
(`MUSE-REPORT-1289.md`, one import line in `grammatik/Grammatik.lean`,
new `grammatik/Grammatik/X86/HwKapsteinSteps.lean`, 609 lines).

## What was checked and how

Clone/branch verified first: `/home/simon/Dokumente/gabbro-muse/a1290`,
branch `muse/1290`, clean tree. Author clone and pinned hash never touched;
all review input came from `.tmp/review/` files only.

1. **Forbidden tokens.** Grep over the delivered file for
   `sorry|admit|axiom |native_decide|unsafe`: 8 hits, all the English word
   "admitted" inside doc comments (e.g. "an admitted coherent port step").
   No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe` in code.
2. **Independent elaboration.** Direct copy into `grammatik/` is denied by
   this lane's ownership enforcement (own `MUSE-REPORT-1290.md` only), so I
   transcribed the delivered file faithfully to scratch
   `.tmp/probe1290/HwKapsteinSteps.lean` and ran
   `./lean-probe .tmp/probe1290/HwKapsteinSteps.lean`:
   `== 0 error(s) in the COMPLETE output; exit 0`. All 28 theorems
   elaborate against this clone's accepted modules, including the joint
   witness `kapSteps_zeuge` with every TSO/memory/refusal conjunct.
   A transcription error in this tightly constrained file (exact proof
   terms over exact accepted names) would almost surely fail elaboration;
   the green run corroborates fidelity.
3. **Axioms.** `#print axioms` output from the probe: every theorem depends
   only on `[propext, Quot.sound]` or a subset (`kapPort_fetch` none;
   `kapPortStart_wf`, `kapPlug_nested`, `kapPlug_int`, `kapSys_frei`,
   `kapSteps_tags_disjoint` fewer). No `Classical.choice` anywhere.
   Standard, nothing to record.
4. **Existing files untouched except one import line.** `SNAPSHOT.json`
   lists exactly 3 files; the `PATCH.diff` `Grammatik.lean` hunk appends
   only `import Grammatik.X86.HwKapsteinSteps` at the end (my clone's
   `Grammatik.lean` still ends with `HwMemTypesWC`, i.e. unmodified base).
5. **Every premise used.** Read every proof: `hsel.1` closes `kapPort_kern`;
   `hker` feeds `simp` in `kapPlug_port`; `hV` is consumed in both
   `kapPlug_nested` branches (none-branch derives `False` via `nestV_rip`;
   some-branch builds the conjunction from it); `h`/`h2` in `kapPlug_int`;
   `hS`/`hAus`/`hc` in all three `kapPlug_system` legs (failure legs
   contradict `sysWit_cli_if`); `hplug` in every `kapStep_*`; `h`/`hwf`
   via `kap_wf` in `kapSteps_wf`; `h` via the capstone iffs in
   `kapSteps_embedded`; `h`/`h2` in `kapSteps_tags_disjoint`. No `intro _`,
   no discarded hypothesis, no `Prop`-typed premise, no quantified-away
   contract parameter. All statements are ground existentials/conjunctions.
6. **Lifted, not copied.** The file defines only witness instantiations
   (`kapPortBytes`, `kapPortMem`, `kapPortKern`, `kapPortStart`,
   `kapPortDec`, `kapPortEv`, `kapSysEv`) plus theorems. No machine,
   evaluator, adapter, or step relation is redefined; every behavior flows
   through accepted lemmas, all verified present in this clone:
   `kap_port/nested/int/system/bild/instanzen/tor_embedded`, `kap_wf`,
   `kapTag` (`HwKapstein.lean`); `portAdapter_aus_fetch`,
   `portAdapter_falschDecodiert_verweigert` (`HwDevices.lean`);
   `nestVerschachtelt`, `nestV_rip`, `nestDritt_verweigert`,
   `nestStart_wf`, `nestTso_weiterleitung`, `nestTso_fremd_alt`
   (`HwNestedInterrupts.lean`); `witNmi_aendert_ss`,
   `witNmi_maskiert_verweigert`, `intWitStart_wf` (`HwInterrupts.lean`);
   `adapterSystem_ok`, `sysWit_cli_if`, `sysWitSteuer`, `sysWitEingaben`,
   `sysWitStart`, `sysWitStart_wf`, `sysWit_weiterleitung`
   (`HwSystemForms.lean`); `adapterBild_vereinbarung`
   (`HwLoadedImage.lean`); `inst_schritt_muldiv/vec`,
   `adapterInstanzen_vereinbarung`, `instStart_wf_muldiv/vec`,
   `inst_weiterleitung_muldiv` (`HwBildInstanzen.lean`);
   `hwStepTor_verbindung_zeuge` (`HwFeatureStep.lean`); `hwTorWitV`,
   `zeugeOut1`, `hwWitStart` (feature/hardware files).
7. **Planted refusals really refuse.** `kapPort_falschDecodiert_verweigert`
   applies the accepted refusal lemma fed with the machine's own proven
   fetch equation `kapPort_fetch` plus `decide` side conditions — a genuine
   firing refusal on the exhibited machine, not a vacuous `none`. The joint
   witness additionally conjoins the families' `witNmi_maskiert_verweigert`
   and `nestDritt_verweigert`, all elaborated green.
8. **Witness non-degenerate.** `kapSteps_zeuge` conjoins owner-only TSO
   forwarding (owner 42 / foreign 0 on three machines), post-flush 42
   visible to both cores, the NMI frame observably changing memory
   (`witNmi_aendert_ss`), six reached union steps plus the tor-arm
   refinement step, well-formedness of every start machine, and the three
   refusals. Two-core states throughout (`kapPortStart` has cores
   0/1; the rest are the families' own two-core witnesses in capstone
   shape, which the owner task's context endorses).
9. **Silicon.** `E6 ib — OUT imm8, AL` confirmed in the supplied Intel
   reference text (line 72012). The candidate's `E6 60` bytes, decode
   `⟨.aus, .p8, .imm 96⟩` (96 = 0x60), length 2 all agree.
10. **CUTS honest, claim not larger than proof.** The CUTS block claims
    exactly: six reached closed union steps, `kap_wf` preservation,
    both-direction embeddings on the exhibited steps, pairwise tag
    disjointness, the one-plug-two-tags identity (`familien_plug_gleich`
    by `rfl`) with all six `HwBildFamilien` rows through the instanzen tag
    and the feature-gate refinement through the tor tag, refusals, and the
    joint witness. It explicitly disclaims hardware correspondence beyond
    self-consistency, any W/GX bridge, source/checker/contract/entry/ABI/
    loader/budget/liveness claims. No hardware-correspondence or W/GX claim
    is made anywhere. The "joined into the capstone's non-degenerate
    two-core state" reading (per-family machines plus joint conjunction) is
    the faithful one and is disclosed in the author report.

## Build results

- `./lean-probe .tmp/probe1290/HwKapsteinSteps.lean` (candidate content):
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau` (this clone, clean baseline without the candidate file):
  `== exit 0; 0 error line(s)`, `Build completed successfully (676 jobs)`.
  The candidate adds exactly one file (author evidence: 677 jobs green),
  consistent with this baseline.
- Author `BUILD-EVIDENCE.json` (supporting, not sole basis): final probe
  0 errors, `lean-bau` green at 677 jobs, axiom prints matching mine.

## What remains open (not a defect)

Full-`lean-bau` with the candidate integrated was verified from author
evidence plus my independent file probe, not by a build in this clone
(the ownership rule forbids staging the candidate file here). The UC-load
leg, control-state snapshots, and all CUTS-listed non-claims stay open by
design. Scratch probe copy left at `.tmp/probe1290/` (private, untracked).

## Anything wrong in the task

Nothing blocking. Two notes: (1) the lane instruction to copy the Lean
file into the clone for probing conflicts with the mechanical own-only
enforcement — probing via `.tmp/` scratch works and should be stated as the
sanctioned path; (2) `OWNER-TASK.md` §27's generic family-plug mechanism
paragraph is boilerplate, while the actual owner task (§20–24) correctly
describes this capstone follow-up — no confusion resulted.
