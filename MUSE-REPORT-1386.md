# MUSE-REPORT-1386: Exact review of candidate 1385 (GabbroV bridge: shared-atomic rely)

Lane 1386, clone `/home/simon/Dokumente/gabbro-muse/a1386`, branch `muse/1386`
(verified: `.git/HEAD` = `ref: refs/heads/muse/1385` replaced by `muse/1386`;
`git status` clean at review time). No push (lane rule). No other agent/model calls.

Reviewed candidate: author lane 1385, pinned HEAD
`e6dade7fca32c712bc41badcf94ee220533e7705`
(read from `.tmp/review/SNAPSHOT.json` only; author clone never touched).
Delivered files reviewed: `PATCH.diff`, `OWNER-TASK.md`, `BUILD-EVIDENCE.json`,
`MUSE-REPORT-1385.md`, `grammatik/Grammatik.lean`,
`grammatik/Grammatik/X86/GvAtomRely.lean` (148 lines).

CANDIDATE: 1385 e6dade7fca32c712bc41badcf94ee220533e7705

VERDICT: REPAIR

The candidate is **UNMEASURED**: no green `./lean-probe` first line and no
`./lean-bau` result line exist for the exact candidate. Author (BUILD-EVIDENCE)
ran `./lean-probe` four times (~120 min total): zero output every time, killed
waiting in the shared `lean-slot`. Reviewer (this lane) ran
`./lean-probe .tmp/review/author-1385/grammatik/Grammatik/X86/GvAtomRely.lean`
once with a 30-minute timeout: **zero output**, terminated by timeout in the
same queue. Five attempts, ~150 min, not one error line and not one
`== N error(s)` line. Accepting an unmeasured candidate would claim more than
was measured, against project rules. Concrete repairs required:

1. **Green measurement.** `./lean-probe grammatik/Grammatik/X86/GvAtomRely.lean`
   first line (`== 0 error(s)`) plus the five `#print axioms` outputs showing
   exactly `propext`, `Classical.choice`, `Quot.sound`, plus a `./lean-bau`
   last result line with the candidate applied. (Reviewer note: lane 1386
   owns only this report, so it cannot stage the candidate file or the
   `Grammatik.lean` import line in its own clone; the author must supply the
   measurement once the slot drains. The zero-output failure is apparatus
   congestion, not a build result, for or against.)
2. **Witness gap (mechanical rule 13).**
   `gv_plain_gibt_relyDuty_parserfragment_zeuge` proves atomic-freedom, the
   plain duty (`oblig_nutzer`) and a memory-moving run (`oblig_ruf_bewegt`)
   but contains **no `TraegerSchreibt ... = true` conjunct**: the
   "at least one table that some function writes" half of non-degeneracy is
   argued, not stated (CUTS item 3 discloses this instead of closing it).
   Add the explicit conjunct for 104 (e.g. the `einzahlen`/Konto write) and
   prove it, as the second witness does with `hauptA`/`tabA`.
3. **Recheck on green (not defects, elaboration risks only a build settles).**
   (a) `TraegerSchreibt NFn.hauptA ...` omits `(D := nD)` where the accepted
   `atomar_nichtleer.1` writes it explicitly; (b) the anonymous-constructor
   assembly `⟨⟨h.logik, hlokS, hlokQ⟩, h.start⟩` relies on `GvRelyDuty`
   unfolding definitionally to the `LogikPflichtA` triple; (c) `.logik.1`
   projection in `gv_plain_gibt_relyDuty_parserfragment`. All three look
   correct on reading; none is verified.

## Static checks (all done by reading; no build available)

- **Forbidden tactics:** none in code. `sorry`/`admit`/`axiom`/`native_decide`/
  `unsafe` occur only in prose (task text, report, code comments naming the
  absence). PASS.
- **Existing files:** `PATCH.diff` touches exactly one existing file,
  `grammatik/Grammatik.lean`, with exactly one added line
  (`import Grammatik.X86.GvAtomRely`). (The doubled
  `import Grammatik.Zielsatz.Atomar.BeweisAtomar` above it is pre-existing,
  not the candidate's.) PASS.
- **Axioms:** file ends with the five required `#print axioms` lines.
  Standard-axiom status UNVERIFIED (no output ever produced). OPEN.
- **Name resolution:** every referenced name was verified to exist with a
  matching shape — `nutzerPflichtA_ohne_atomar` (BeweisAtomar.lean:379),
  `LogikPflichtA`/`NutzerPflichtA` (Spec.lean:2145-2154; the assembly matches
  the `((∀ passes f, triple) ∧ lokal ∧ lokal)` shape),
  `hP`/`hws`/`hRumpf`/`hTest`/`hEns`/`aFuenf`/`hP_seq`/`hP_rely_nicht`/
  `hP_konfig_geteilt`/`aFuenf_havoc` (namespace `AtomarXZeuge`, opened),
  `nD`/`NFn`/`NTab`/`NGlob` (`NIZeuge`, opened; `hauptA`, `tabA`, `konfig`,
  `zaehlB` all exist), `nS` (`SchwachZeuge`, opened), `axWahr` and
  `TraegerSchreibt` (`Gabbro.Grammatik` root, opened), `oblig_nutzer`/
  `oblig_ruf_bewegt`/`oO`/`rho7` (`Gabbro.Grammatik` root, qualified use
  correct), `g_einzahlen`/`GTab`/`GKontoFeld` (members of
  `G104_referenz_oblig`, qualified use correct). The 104-witness statement
  matches `oblig_ruf_bewegt` up to qualification. PASS on reading.
- **Premise use (rules 3-4):** every premise of the three theorems is used;
  no `Prop`-typed premise; no `intro _`/`have _ :=`. `gvDutyA_gibt_nutzerA`
  is definitional assembly, but that is what the task asked to define-then-
  prove, and the content sits in the other two theorems: the fragment
  transfer uses atomic-freedom essentially, and `gv_rely_braucht_atomfreiheit`
  proves it cannot be dropped. No manufactured premise. PASS on reading.
- **Claim vs proof:** CUTS is honest (UNMEASURED stated; duty construction
  from `Pflichten src`, TSO refinement, payload hand-off all OPEN). The
  report's "generic over every declaration" holds on reading
  (`nutzerPflichtA_ohne_atomar` is generic; 104 instantiates it). The
  branch-steering witness shape the task required is present (`hRumpf`/
  `hTest`: `zaehlB` stores shared `konfig`, `ite` steers 1 vs 2). PASS.
- **Two-model relation:** the bridge relates the plain duty to the rely duty
  *inside* `grammatik/` (reusing V5's `nutzerPflichtA_ohne_atomar`). The
  `programmlogik/` `Body`/`exec` side is not formally connected — this is
  task-imposed (no mathlib in `grammatik/`, `programmlogik/` not editable),
  honestly stated as OPEN, and not a repair item for this candidate.

## What remains open (unchanged from candidate CUTS)

Duty construction for atomic-bearing units from `Pflichten src`; per-access
x86-TSO refinement into W/GX; payload hand-off; and the green measurement
itself (repair item 1).

## Commit state

- `MUSE-REPORT-1386.md`: this file (only file owned, only file written).
- Own tree otherwise untouched: no candidate file staged, no `Grammatik.lean`
  edit, clean `git status` apart from this report.
- Last `./lean-bau` result line: NONE — no build completed in this lane
  (the single 30-min `./lean-probe` attempt returned zero output).
- Precise blocker: shared `lean-slot` congestion; `./lean-probe` yields no
  output within 30 min, matching the author's four attempts (~120 min).
  A later `locks/lean.pid` inspection was refused by the permission
  classifier, so holder-vs-queue cannot be distinguished from here.
