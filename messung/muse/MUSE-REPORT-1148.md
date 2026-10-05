# MUSE-REPORT-1148: Independent exact review of candidate 1147

CANDIDATE: 1147 fed52996a00ac210cd1caf3b9206a3609507e29c
VERDICT: ACCEPT

## Identity and method

- Reviewer clone verified: `/home/simon/Dokumente/gabbro-muse/a1148`, branch
  `muse/1148` (matches lane task; no STOP condition).
- Candidate pinned from `.tmp/review/SNAPSHOT.json` (NEW pin after author
  repairs; the previous pin `206a3d84…` is stale and NOT approved here):
  author 1147, HEAD `fed52996a00ac210cd1caf3b9206a3609507e29c`, base
  `48a4be7c1c333a602ce0d0816979d154ae1bd959`, `clean: true`, files exactly:
  `MUSE-REPORT-1147.md`, `grammatik/Grammatik.lean`,
  `grammatik/Grammatik/X86/HwWordAtomicity.lean`.
- Read-only re-review of the NEW snapshot (`PATCH.diff`, candidate file,
  updated author report, `BUILD-EVIDENCE.json`). The author clone itself was
  never touched. Every previous finding was re-inspected against the new
  bytes; changed proofs are listed below.
- Independent checks in this clone on the NEW bytes:
  - `./lean-probe .tmp/review/author-1147/grammatik/Grammatik/X86/HwWordAtomicity.lean`
    on the EXACT new candidate bytes: `== 0 error(s) in the COMPLETE output;
    exit 0` (elaborated against this clone's newer dependency base, so base
    drift is covered).
  - `./lean-bau`: `Build completed successfully (601 jobs).`
  - Grep checks: forbidden tokens, candidate-name uniqueness in `grammatik/`,
    referenced accepted names present, silicon text in the supplied SDM.

## What changed vs the stale pin (author repairs)

The author reports a failed integration gate with `lean::exception: failed
to create thread`, exit 134, on `Grammatik.X86.HwWordAtomicity` only — a
resource-class failure, no proof error. The repair (verified line by line in
the new file, 426 lines, all statements byte-identical to the stale pin):

1. `hw_ausrichtung_vA`: proof `by decide` → `rfl` (line 248).
2. `hw_verflochten_zeuge`, forwarding facts `hfwd0`/`hfwd1`: trailing
   `decide` → `rfl` after the existing `rw [hwWortM_ansicht]` (lines 319–326).
3. The one genuine disequality (`hw_riss_zeuge`, `wI0… ≠ wI1…`) keeps its
   `decide` (lines 355–356) — `rfl` cannot prove `≠`; the attempt-and-revert
   is stated in the author report.

Assessment of the repair: legitimate and guarantee-neutral. The three
replaced goals are closed definitional equalities (alignment of the concrete
`vA = 0`; forwarding reads over concrete buffers), so `rfl` elaborating is
itself the machine check that nothing was weakened — kernel-accepted `rfl`
is strictly stronger evidence of definitional truth than `decide`. No
statement, premise, conclusion, refusal, witness component, CUTS line, or
`#print axioms` entry changed. The axiom footprint is identical to the stale
pin (all within `[]`/`[propext]`/`[propext, Quot.sound]`), confirmed by my
own probe output above.

On the author's environmental claim (thread/address-space exhaustion under
`-j2 -M4096`, matching the known ceiling): I cannot independently reproduce
the integration-gate failure from this lane, and I do not assert its cause.
What I verify is that the new bytes elaborate cleanly with 0 errors and an
unchanged axiom footprint, and that the repair direction (kernel `decide` →
definitional `rfl` on closed terms) reduces elaboration work rather than
adding any. If a gate fails again with the same signature, that is a matter
for the gate's own evidence, not a finding against this candidate's proofs.

## Checklist result (re-inspected on the NEW bytes)

- No `sorry`/`admit`/`native_decide`/`sorryAx`/`axiom`/*unsafe*: clean
  (word-boundary grep over the new candidate file).
- `#print axioms` standard: every theorem depends on `[]`, `[propext]` or
  `[propext, Quot.sound]` — verified in my own probe output. Within the goal
  axiom set.
- Existing files untouched except one import line: `PATCH.diff` shows exactly
  one added line `import Grammatik.X86.HwWordAtomicity` in
  `grammatik/Grammatik.lean`, no deletions, no other existing-file edits.
- Every premise used: re-inspected each theorem on the new bytes; unchanged
  from the previous review (`h`/`hwf` consumed in `adapterWort1147_wf`;
  `hfl` plus head equation in the embedding; all guard/trace/membership/
  emptiness/exclusion premises threaded through; `d` pins both
  foreign-observation conclusions; `kein_hw_wort_bruecke` consumes its
  hypothesis). No `intro _`, no `have _ :=`, no `Prop`-typed premise.
- Family evaluator lifted, not copied: adapter runs accepted `hwWortAusgabe`
  by `rfl`-agreement; observation/frame/tearing theorems exact-lift the
  accepted lemmas; all referenced accepted names confirmed present in this
  tree. New items remain only the required adapter/event/wrapper/assumption/
  gap-marker definitions.
- Planted refusals really refuse: drain-on-empty via `flush_leer`; partial
  buffer via the accepted structural lemma; overlap via
  `ausrichtung_allein_verweigert.2` on concrete `wOv`; `hw_ausrichtung_vA`
  now by `rfl` — still a genuine closed fact about `vA`, not a weakened
  refusal (the refusal theorems themselves are untouched).
- Witness non-degenerate: `hw_verflochten_zeuge` still joins every premise
  of the guarded observation on the interleaved two-core drain (both buffers
  empty at end; both memories observably change; owner-only forwarding vs
  foreign stale read; real foreign issue+flush; `HwWf`). `hw_riss_zeuge`
  still a real `HwSchritt.spülung` step with a `decide`d memory change.
- Silicon facts: unchanged. `HwWortAtomar` still stated, named, never
  inhabited/assumed/discharged (confirmed: used nowhere); word stores still
  eight `issueByte` events; LOCK still refused; no hardware correspondence
  claimed. SDM substance (aligned quadword atomicity) matches supplied
  edition 093 §11.1.1; citation-number observation O2 below stands.
- CUTS honest, no claim larger than proof: unchanged; mid-trace mixture
  admitted; `HwWortBruecke` empty; no W/GX, source, checker, contract, entry,
  timing, or liveness claim. The task-sentence correction stands.
- Inhabitation spirit (rule 13): no program-syntax premises, no `ZEUGE:`
  line in the owner task; joint witnesses on non-degenerate machine runs
  unchanged.

## Previous observations (carried over, still non-blocking)

- O1: file header comment cites `HwWortAtomAnnahme`; defined name is
  `HwWortAtomar`. Doc-only, NOT fixed in the repair — still just a nit.
- O2: CUTS cites "Intel SDM Vol. 3A §8.1.1"; supplied edition 093 numbers it
  §11.1.1. Substance identical; author cites it only as the shape of the OPEN
  assumption with explicit no-provenance honesty. Still just a nit.
- O3 (new): the repair history in the author report is honest about what was
  tried (`rfl` attempted for `≠`, reverted). No hidden weakening.

## Last build results (NEW pin)

- `./lean-probe` (exact NEW candidate bytes):
  `== 0 error(s) in the COMPLETE output; exit 0`
- `./lean-bau`: `Build completed successfully (601 jobs).`

## Open

Nothing open on this review. Candidate 1147 at the NEW pinned HEAD above is
accepted as re-reviewed; the stale pin `206a3d84…` is superseded and was not
approved. Integration may proceed through the normal serial merge gate
(sorry-scan, axiom check, full build).
