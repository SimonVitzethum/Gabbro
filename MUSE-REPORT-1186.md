# MUSE-REPORT-1186: Independent exact review of candidate 1185

Clone `/home/simon/Dokumente/gabbro-muse/a1186`, branch `muse/1186`: assumed
(the review snapshot is supplied in-clone; shell execution is blocked in this
session, see blocker note below, so branch verification was by task file, not
by `git`). Owned file only: this report. No Lean files added or touched.

Review object (pinned): CANDIDATE 1185, HEAD
`f95e81552256be451177d0a73ab8efa16e8687cc`, base
`4f906f555d739de5b9444364735eae29b6445ed6`
(`.tmp/review/SNAPSHOT.json`, `clean: true`). Files in candidate: exactly
`MUSE-REPORT-1185.md`, `grammatik/Grammatik.lean` (one import line),
`grammatik/Grammatik/X86/HwForwardingGeneric.lean` (new, 1176 lines).
Reviewed the full `PATCH.diff` hunks and the complete new file end to end.

## Checks performed (all inside this clone)

- Forbidden tokens over the candidate file: no `sorry`, `admit`, `axiom`,
  `native_decide`, `unsafe`, `sorryAx`, `split_ifs`, `norm_num`, `ring_nf`,
  `intro _`, `have _ :=`, no `Prop`-typed premise. The only matches for
  "admit" are the English word "admits" in comments.
- `grammatik/Grammatik.lean` diff: exactly one added line,
  `import Grammatik.X86.HwForwardingGeneric`, placed after the
  `HwStackCalls` import. No other existing file touched.
- Accepted-evaluator reuse: every lifted name resolves in this clone's
  tree — `WortGruppe`/`FremdFrei`/`wortEintraege`/`fuss_mem_offset`/
  `wort_gruppe_liest_zurueck` (`WordAccessGrouping.lean`),
  `addrOff_ne8`/`addrOff_inj8`/`addrOff_null`/`bytesWort_wortByte`/
  `read64`/`Fuss` (`Speicher.lean`), `neuestens_angehaengt`/
  `issue_verweigert` (`TSO.lean`), `wortEintraege_mem`/
  `stapelLadeWort_still`/`stapelByte_beob`/`issueListe_stern`/
  `issueListe_cons_none`/`stapelPop_unlesbar` (`HwStackCalls.lean`),
  `tsoAnsicht`/`tsoAnsicht_speicher`/`setTso_wf`/
  `hwWortAusgabe_puffer`/`hwWortAusgabe_kein_speicher`/
  `hwTeilwort_keine_gruppe`/`hwGruppe_verweigert_bei_fremdeintrag`
  (`HardwareExecution.lean`), witness vocabulary `zeugeFlags`/
  `kontextReset`/`basisHw`/`basisBereit` (used across accepted modules).
  No model redefined; the old evaluators are applied, never copied.
- `WortGruppe` is definitionally `puffer c = wortEintraege a v ∧
  FremdFrei s c a` (WordAccessGrouping.lean:41-42) — exactly the shape
  the candidate destructures, and deliberately alignment-free, which
  matches the candidate's honest misaligned treatment (group refusal
  plus byte mixing, no invented fault gate).
- Premise use: every theorem consumes every premise. Four `obtain
  ⟨shape, _⟩` sites (lines 183, 443, 462, 475) discard the `FremdFrei`
  conjunct where only the buffer shape is needed; the premise itself is
  used in each proof, and the joint theorem `fwdWeiterleitung_und_fremd`
  uses both halves. Checked, acceptable, not a rule-4(d) discard.
- List-orientation soundness (silicon-relevant): new entries append at
  the buffer end (`fwdSpeichere_puffer`), `neuestens` resolves the
  young (tail) match first — consistent with the accepted
  `neuestens_angehaengt` and with the witness shapes (`witFwdAlt`
  older-first, `witFwdJung` younger-last). No youngest/oldest
  inversion. TSO ordering claims (FIFO issue, youngest-own
  forwarding) are used as provenance, never as proved silicon fact;
  CUTS states this explicitly. No hardware-correspondence or W/GX
  claim anywhere.
- Refusals really fire: `fwdSpeichere_wache` (guard store → `none`
  via `issue_verweigert` + `issueListe_cons_none`),
  `fwdBeobachte_dunkel` (dark observe → `none` via
  `stapelPop_unlesbar`), misaligned/older/younger non-groups, and the
  mixed-word observation `fwd_juengerer_mischt` (needs `bNeu ≠
  wortByte v 3`, discharged by `decide` on the witness). Each is
  instantiated on concrete witness states in `fwdTso_zeuge`.
- Witness non-degeneracy: two cores (0 stores/forwards, 1 reads
  foreign); reached adapter run buffers exactly 8 entries
  (`witFwd_puffer8`, by `decide` on the adapter output); owner
  forwards 42 while foreign reads 0; eight chained `flushKern`
  drains change shared memory observably 0 → 42
  (`witFwd_anfang_null` + `witFwd_spuelung_aendert_speicher`),
  observed from both cores. The generic theorems fire on the pushed
  shape beside the run (`witFwd_generisch_eigen/fremd`). The
  adapter-output/hand-built-state link runs through decidable
  observables (buffer length, loads, drain bytes), the documented
  lane-1139 style, not an equality over function fields. Honest.
- Axioms: author's final `lean-probe` prints every main theorem
  within `{propext, Classical.choice, Quot.sound}` (standard set;
  `Classical.choice` enters via `witFwd_lesbar_all` and the joint
  witness only). Final probe: 0 errors. Intermediate red probes in
  `BUILD-EVIDENCE.json` are development history, all repaired
  before the pinned commit.
- CUTS block present and honest: claims generic forwarding,
  foreign-leg, overlap byte rules, negatives, adapter duties,
  embedding legs and the joint witness; disclaims silicon
  correspondence, the generic drain-equals-`write64` induction
  (correctly left with the cited `wort_gruppe_liest_zurueck`),
  LOCK/RMW/faults/interrupts/SIB/FP/SIMD/source/loader/budget/W-GX,
  and discloses the local `fwd_addrOff_add` mirror of accepted
  `Pipeline.addrOff_addrOff`.
- Extra premises beyond the guard (`hles` readability): mathematically
  necessary (`loadByte` checks `lesbar` first), used, and discharged
  on the witness. The task states no formal TARGET, so rule 12 does
  not attach; no weakening involved.

## Observations (non-blocking, for the record)

1. `fwd_addrOff_add` restates the accepted `Pipeline.addrOff_addrOff`
   with the same proof to avoid importing 2400-line `Pipeline.lean`.
   Disclosed in CUTS; statement-level only, no model duplication.
   Coordinator may collapse it later.
2. The file header comment says "torn buffers ... never group", but
   no named theorem covers a short (fewer-than-eight) buffer; the
   proved negatives are misaligned, nine-entry older overlap and
   nine-entry younger overlap (length contradictions). CUTS does not
   repeat the torn-buffer phrase. Minor comment overbreadth only.
3. The misaligned case is group-refusal plus byte mixing, not a fault
   gate — correct for this alignment-agnostic model, and the author
   flags exactly this in their report. No action.

## Blocker (precise, updated after shell access was restored)

Shell execution was permission-blocked during the previous turn, but
access was restored this turn: clone and branch verified by `git`
(`a1186`, `muse/1186`), and `./lean-bau | tail -n 8` run in this
clone. Last result line: **Build completed successfully (619 jobs).**
This build covers my clone's tree, which does NOT contain the
candidate's new module (candidate lives in the author clone; this
lane owns only the report, so the module was reviewed statically
from the pinned snapshot). The candidate module's own build evidence
is the author's: final `lean-probe` 0 errors with full `#print
axioms` output, and the module's `#print axioms` lines emitted inside
their 616–617-target build before the environmental root-aggregation
failure (varying toolchain `.olean` read errors, reproducing with the
import commented out). The merge gate MUST still re-verify the
integrated build before merging the candidate.

## VERDICT: ACCEPT

Candidate 1185 (HEAD `f95e81552256be451177d0a73ab8efa16e8687cc`):
generic word forwarding, foreign-leg, overlap byte rules, negatives,
adapter duties with embedding legs, planted refusals that fire, and a
joint non-degenerate two-core witness are all proved over the reused
canonical vocabulary, axioms standard, CUTS honest, no claim larger
than the proof. My `./lean-bau` is green on this tree (619 jobs);
the candidate module's integrated build rests on the author's
evidence and MUST be re-verified by the merge gate anyway.
