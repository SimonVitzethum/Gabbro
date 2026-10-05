# MUSE-REPORT-1284: Exact review of candidate 1283 (Paging)

Clone `/home/simon/Dokumente/gabbro-muse/a1284`, branch `muse/1284`
(verified: `git rev-parse --abbrev-ref HEAD` = `muse/1284`, HEAD
`6a375b01503b447d79432316778f9fdf09c39f31`, clean tree).
Owned file only: this report. Report-only exact review; no source touched.

CANDIDATE: 1283 ace95322c4245b3beb3c0fcaf3df3b743ad615ad
Pinned base `738366545afbddf7ac664db92804703db24f8868`, reviewed from the
harness snapshot `.tmp/review/author-1283/` (`SNAPSHOT.json`,
`PATCH.diff` 1574 lines, file copies, `OWNER-TASK.md`, `MUSE-REPORT-1283.md`,
`BUILD-EVIDENCE.json`). The author clone `a1283` was not entered (outside
this lane's directory); the full `PATCH.diff` was read end to end and every
check below was run against the snapshot copies and this clone's tree.

Candidate content: new `grammatik/Grammatik/X86/HwPaging.lean` (1446 lines),
one appended import line in `grammatik/Grammatik.lean`, report. No other file.

## Gate checks

- No `sorry`/`sorryAx`/`admit`/`axiom`/`native_decide`/`unsafe` in the new
  file (grep over snapshot: only English "admits/admitted" in comments;
  `#print axioms` are commands, no declarations). No `split_ifs`,
  `norm_num`, `ring_nf`. `by_contra` avoided (unknown tactic), `by_cases`
  used instead.
- `#print axioms` standard: per `BUILD-EVIDENCE.json` final probe, every
  printed theorem depends on axioms within `[propext, Quot.sound]` (several
  on `[propext]` alone, defs on none) — a subset of the goal's
  `propext, Classical.choice, Quot.sound`.
- Existing files untouched except the single import append (diff-confirmed).
  The mid-lane `tabEintrag` collision with `JumpTableCert` (one red
  `lean-bau` in evidence) was fixed by rename to `seitenTabEintrag`
  (commit `4484de7e`); the final diff contains no bare `tabEintrag`.
- Every premise is used: `gangEbenen_kongr` rewrites all 21 equalities;
  the three refusal lemmas consume `hg` via the inversion lemmas;
  all `blatt_*`/`wort*` hypotheses occur in the `simp` closings.
  One benign exception: `flachStimmt_allwahr` introduces the walk equation
  and ignores it — vacuous truth over the all-permissive memory, not a
  fake closure. Noted, not verdict-relevant.
- Accepted evaluator lifted, never copied: `istKanonisch` via proved
  bridge `kanonischNat_bruecke`; `adrKlasse` via `gangGp_adrKlasse`;
  `seitenKlasse` via consensus `gangPf_seitenKlasse_eins`;
  `vektor_pf_vierzehn` via `gangPf_vektor`; `HwSchritt` via exact two-way
  embedding (`hwSeitenSchritt_einbettung_vor`,
  `hwSeitenSchritt_alt_invert`, `hwSeitenSchritt_einbettung_zurueck`);
  `verweigertAdapter`, `HwWf`/`hwSchritt_wf`, the full `hwWit*` family
  reused by name. All reused names verified present in this clone's tree
  (`HardwareExecution.lean`, `HardwareFaults.lean`,
  `ExceptionPriorityHardware.lean`).
- Planted refusals really refuse: `seitenGross_verweigert`,
  `seitenSteuer_verweigert`, `seitenGp_verweigert` prove no `gangOk`/`gangPf`
  step; `decide` witnesses pin the RO-write PF, the non-present hole, the
  noncanonical #GP, and A/D write-back facts.
- Witness is non-degenerate: two mappings (RW + RO leaves) of linear pages
  1/2 onto one physical frame 32; `hwSeiten_zeuge` joins `hwWitStart_wf`,
  both ok-walks, the RO-write fault, owner-only forwarding
  (`hwWit_weiterleitung`), foreign-load staleness (`hwWit_fremd_alt`), the
  memory-changing drain (`hwWit_spülung_aendert_speicher`), and flat
  agreement — two cores via the accepted run, as the task's mechanism
  paragraph requires for a family with no buffers of its own.
- Silicon facts cross-checked against the clone's Intel SDM text
  (combined volumes 1–4, edition 093): PTE bits P:0/RW:1/US:2/A:5/D:6/PS:7,
  XD:63 reserved when NXE=0, 9-bit indices at 39/30/21/12, 12-bit offset,
  40-bit frame field, 48-bit canonical rule, non-canonical → #GP, #PF code
  bits P:0/W-R:1/U-S:2/RSVD:3/I-D:4, WP-gated supervisor write fault.
  The model matches on all of them; check order (present → reserved →
  large-page → leaf) and the PML4-PS → RSVD-#PF treatment agree with the
  SDM walk description. The author honestly names bit-level correspondence
  a silicon assumption in CUTS.
- CUTS honest, no over-claim: large pages refused, SMEP/SMAP refused
  wholesale (WP modelled), no TLB, no fault delivery, no W/GX bridge, no
  timing, `FlachStimmt` for a real OS declared user logic. No
  hardware-correspondence claim anywhere.

## Thin spots (recorded, not verdict-changing)

- `gangPf_vektor` is a verbatim relabel of accepted `vektor_pf_vierzehn`.
  Legitimate consensus statement, zero new content.
- The flat bridge (`gangOk_flach_schreibbar`/`lesbar`) is conditional on
  `FlachStimmt`, which is inhabited only by the trivial all-permissive
  memory; `FlachStimmt witSeitenSteuer witTab witFlach` is NOT proved
  (witness flat facts and walk outcomes stand as separate conjuncts).
  The task's "explicit bridge theorem" exists in conditional form and the
  gap is CUTS-declared user logic — acceptable, but a follow-up should
  close the witness instance.
- A/D write-back on success only (faulting walks set no accessed bits) is
  a disclosed modeling choice, not silicon-exact behavior.

## Build evidence

- Author `BUILD-EVIDENCE.json` final entry: `./lean-bau` →
  `== exit 0; 0 error line(s) in the COMPLETE output`,
  `Build completed successfully (659 jobs).`, plus
  `./lean-probe grammatik/Grammatik/X86/HwPaging.lean` →
  `== 0 error(s) in the COMPLETE output; exit 0`. Intermediate red states
  are all accounted for in the evidence trail and fixed in later commits.
- Own `./lean-bau` in this clone (baseline WITHOUT the candidate, HEAD
  `6a375b01`): `Build completed successfully (672 jobs).` — green; the job
  count differs from the author's 659 only because this master is newer
  (contains e.g. `HwSegTlb.lean`). The candidate itself was reviewed from
  the pinned snapshot, not rebuilt here, since applying it would exceed
  this lane's owned files; the merge gate rebuilds it.

VERDICT: ACCEPT

The candidate delivers the tasked paging model with the required walk,
permission combination, WP handling, A/D rules, #PF codes, canonical/#GP
treatment, flat bridge in conditional form, exact machine embedding,
refusals, and a non-degenerate two-mapping/two-core witness — green,
axiom-clean, import-only footprint, CUTS-honest. Recommended follow-up
(non-blocking): prove `FlachStimmt` for the witness tables.

Co-Authored-By: muse-agent-1284 <muse-agent-1284@noreply.invalid>
