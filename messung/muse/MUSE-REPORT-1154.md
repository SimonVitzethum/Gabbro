# MUSE-REPORT-1154: Exact review of candidate 1153 (re-review of the new snapshot)

Lane 1154 (reviewer). Candidate: lane 1153, pipeline lowering onto the wider ISA.
Clone verified: `/home/simon/Dokumente/gabbro-muse/a1154`, branch `muse/1154`
(via `.git/HEAD`). Owned scope: ONLY this report. No Lean files added or edited here.
Review material (all in-clone, no author-clone access per HARD RULES):
`.tmp/review/SNAPSHOT.json` (new pin below), `.tmp/review/author-1153/` with
`PATCH.diff` (560 lines), `MUSE-REPORT-1153.md`, `OWNER-TASK.md`,
`BUILD-EVIDENCE.json`, and the candidate file copies. The candidate base is
`062b979a…`; this clone's tree is newer, so name-level facts were verified against
this tree and the author's green-build evidence corroborates elaboration.

CANDIDATE: 1153 9cde1314432379b96141514a365e34735f46974a
VERDICT: ACCEPT

## What was done (independent re-review, new snapshot only)

- Read the full `PATCH.diff`: new `grammatik/Grammatik/X86/PipelineWide.lean`
  (423 lines), exactly one added import line in `grammatik/Grammatik.lean`, new
  `MUSE-REPORT-1153.md`. No other existing file touched; optimiser files untouched.
- Scanned the candidate Lean source for forbidden tokens: no `sorry`,
  no `axiom` declarations, no `native_decide`, no `unsafe`, no `intro _`,
  no `have _ :=`. The string "admit" occurs only inside the English word
  "admitted" in a CUTS comment. The author's identical self-report is confirmed.
- Verified every external name the candidate relies on exists in the accepted
  tree: `kompaktWahl`, `kernGleich`, `OptRel`, `optRel_bind`, `laufI_cons`
  (shape reused by the new `lauf_cons`/`laufW_cons`), `kanon` (shape reused by
  `kanonP`), `laengeOk_encode`, `schritt`/`schrittC` success/refusal equation
  lemmas for movImm64/load64/store64 and their compact forms, `effAddr8`,
  `effAddr0_eq_effAddr`, `effAddr8_eq_effAddr`, `disp8Of`, `zextWort32`,
  `dispWort`, `encodeC_len`, and the shared witness state `cwZustand`
  (RAX=10, rsp=8192, zeroed memory — coherent with the witness claim of word 10
  read back at address 8200 with initial byte 0).
- Confirmed no duplication: this tree defines no `laufW`, `wideSelect`, or
  `wideDatOk`; no accepted compact runner exists to lift, so the minimal mirror
  `laufW` plus the two-line bind bridges are new glue, not a copied evaluator.
- Checked premise use by hand over the PATCH text: `wideSchritt` consumes both
  `hok` (via `wideOk_teile`) and `hg` in every covered arm; `wideSelect_korrekt`
  consumes `hsel` (via `wideSelect_cons`), `hg` (via `wideSchritt`) and the
  induction hypothesis; `wideSelect_cons`, `kanonW_ok`, `wideOk_teile`,
  `bind_some_elim` all consume their premises; refusals and the witness are
  premise-free `decide`/existential constructions, as required.
- Checked the six refusals are genuine decided evaluations of the accepted
  selector (register-register add, push, jump even where the branch selector
  would succeed, unrepresentable imm `0x100000001`, rbp-relative disp0 plus
  disp 200 outside the signed-8-bit range, covered-head/refused-tail), and the
  witness is non-degenerate (a real memory-changing store step, read-back 10
  versus initial byte 0, both successors agreeing). Single-core scope throughout,
  matching the pilot pipeline's CUTS, so no two-core witness shape applies.
- Checked silicon posture: the file states no new hardware facts; every
  behaviour comes from the accepted `kompaktWahl`/`kernGleich`/step lemmas.
  (SDM extracts were not supplied in-clone; the check performed is reuse, not
  re-derivation, which is what the checklist item requires of this family.)
- Checked claim scope: `wideSelect_korrekt` claims pilot-vs-compact run
  equivalence only; no source-`execBlock`, fetch-bridge, TSO, timing, or W/GX
  claim appears in any theorem name, statement, or CUTS text.
- Read `BUILD-EVIDENCE.json`: intermediate red probes during development, then
  final `./lean-probe` 0 errors with every main theorem at most
  `[propext, Quot.sound]` (`bind_some_elim` axiom-free), and final `./lean-bau`
  green. Two transient apparatus failures (thread-spawn exit 134, unreadable
  toolchain olean) cleared on retry with zero source changes — apparatus, agreed.
- Ran `./lean-bau` in this clone (report-only lane; candidate not integrated
  here by design): green, see result line below.

## Candidate theorems reviewed (exact names)

`kanonW_ok`, `kanonW_len`, `wideOk_teile`, `wideSchritt`, `kanonP_ok`,
`wideSelect_cons`, `lauf_cons`, `laufW_cons`, `wideSelect_korrekt`,
`wideSelect_refuses_add`, `wideSelect_refuses_push`, `wideSelect_refuses_jump`,
`wideSelect_refuses_imm`, `wideSelect_refuses_rbp`, `wideSelect_refuses_tail`,
`bind_some_elim`, `wideSelect_korrekt_zeuge`; definitions `wideDatOk`,
`kanonW`, `wideOk`, `wideSelect`, `laufW`, `kanonP`. File ends with CUTS plus
`#print axioms` for every main theorem.

## Previous findings disposition

- The earlier REPAIR verdict was process-level only (no candidate readable
  in-clone) and is superseded by this snapshot review — not reversed on the
  merits of unseen code, but replaced after actual inspection. No code finding
  was ever raised against the author, and none is raised now.
- Changed proofs since the old pin (`62dc6e00…`): author log shows the new head
  is a report-only refresh (response to the process block); the Lean delta
  reviewed here is unchanged. Nothing was weakened in response.

## Scope note (task sentence versus delivered fragment)

The task sentence names narrow widths, multiply/divide, shifts, and SETcc/CMOVcc
lowering plus a source-`execBlock`-style theorem. The candidate lowers the
compact imm/disp fragment for the three data-moving pilot forms and documents
the rest as refusals/CUTS with a precise obstruction: a 32-bit narrow op is not
observable-equal to any 64-bit pilot op, and the `ExtendedExecution` families
have no pilot source form to check a selection against. Manufacturing those
validators would violate the no-fake-closure rule, so the honest bounded
connection plus documented obstruction is accepted as satisfying the lane; the
gap is openly carried in CUTS and the author report, not silently dropped.

## Last `./lean-bau` result line (this clone, candidate not integrated here)

`Build completed successfully (610 jobs).`

Author-tree evidence for the candidate itself: `Build completed successfully
(608 jobs).`

## CUTS assessment

Honest and complete for what is claimed: covered fragment, decided refusals,
no narrow/muldiv/shift/SETcc/CMOVcc lowering, source leg stays with the pilot
pipeline, no compact fetch bridge, no TSO/time/control-flow beyond selection,
one core, model memory. No hardware-correspondence or W/GX claim made.

## What remains open

- Integration of the accepted file is coordinator business (serial checked
  publication); this lane changes no process and pushes nothing.
- Any future widening (narrow bridges, `ExtInstr` pilot source forms, fetch
  bridge, source-leg connection) needs its own lane with the Lean-first
  modelling the standing instructions require.
