# MUSE-REPORT-990: Exact review of author 840 (flag-ledger closing)

Lane 990, clone `/home/simon/Dokumente/gabbro-muse/a990`, branch `muse/990`
(verified: `git branch --show-current` = `muse/990`, top commit `b040b155`).
Owned file only: `MUSE-REPORT-990.md` (this file). No source, no live controls.

CANDIDATE: 840 275ac0dc7366f48e47709487e90af6677e83462e

VERDICT: ACCEPT

## What was reviewed

Exact pinned snapshot `.tmp/review/author-840/` (SNAPSHOT.json: author 840,
head `275ac0dc…`, base `e7c75908…`, files `MUSE-REPORT-840.md`,
`grammatik/Grammatik.lean`, `grammatik/Grammatik/X86/ComposeFlagLedger.lean`,
clean tree): OWNER-TASK.md, MUSE-REPORT-840.md, PATCH.diff (3 files only),
BUILD-EVIDENCE.json, and the full 257-line candidate Lean file, against the
accepted modules in this tree plus the official local Intel SDM snapshot
(`intel-instruction-reference.txt`, edition 325462-093US).

## Independent verification (all performed, not copied)

- Reproduced with the queued wrapper: `./lean-probe
  .tmp/review/author-840/grammatik/Grammatik/X86/ComposeFlagLedger.lean`
  against this tree's accepted modules: `== 0 error(s) in the COMPLETE
  output; exit 0`. All 12 `#print axioms` lines match BUILD-EVIDENCE.json
  exactly (`[propext]` everywhere, `[propext, Quot.sound]` on the witness).
- Baseline `./lean-bau` in this tree: `Build completed successfully (510
  jobs)` (candidate built 509 at its base; master moved by one module since
  — the candidate still elaborates green against the newer tree).
- Architecture check against the Intel text: ADD (line 45330, all six set per
  result), AND (40767, OF/CF cleared, SF/ZF/PF per result, AF undefined),
  IMUL (58250, CF/OF set-or-cleared), DIV (50250, all six undefined),
  SHL/SHR/SAR (93489-93493, CF last-bit-out, OF only at 1-bit shifts,
  SF/ZF/PF per result, AF undefined, count 0 changes nothing). The
  candidate's `definiertFlag` is exactly the accepted bit-level `definiert`
  (ArchitecturalFlags, lane 692) projected onto the five named flags; AF is
  absent by construction (`FlagName` has exactly the 5 constructors, so the
  closing proof's `cases n` is mechanically exhaustive).
- Producer/consumer interface check: `ledger_mulU_trag`'s admitted set
  (`o/no/b/ae`) is literally the hypothesis row of the accepted
  `mulVerbrauch_sicher`; the witness reuses `zeuge_speicher_aendert_sich`
  (shape `.1/.2.1/.2.2` matches use), `probe_sprung_genommen` (statement
  matches verbatim: `je +16` on `zeugeGleich` to 4114), and
  `divVerbrauch_verweigert` (already the full existential). No `sorry`,
  `admit`, `axiom`, `native_decide`, `unsafe`, no `Prop`-typed premise, no
  discarded premise in the candidate file (read in full).
- Diff check: PATCH.diff touches exactly the 3 snapshotted files;
  `Grammatik.lean` gains one import line; no numbers, no MARKE, no
  source/checker/Spec/goal/emitter/optimiser-reserved edits.

## Why ACCEPT (no repair item found)

- All three premises of `ComposeFlagLedger_verbindung` are used (ledger
  per-flag extraction, liveness gate, producer agreement) and the conclusion
  is derived via the accepted rule lemma `bedingung_stabil`, not restated.
- No new machine/decoder/interpreter/executor; accepted internals are reused
  by name, never re-proved. No conjunction-counts-as-execution: the step goes
  through the rule lemma, and reached execution is shown (memory-changing
  `zeugeProg` run byte 0 -> 42, executed taken `je`).
- Negative mutations present at both levels: three ledger refusals
  (`ledger_div_verweigert`, `ledger_mulU_e_verweigert`,
  `ledger_shift_o_verweigert`, all by `decide`) plus the execution-level DIV
  twin (two admitted successors, opposite branches) inside the witness.
- No guarantee weakening: shift OF is refused conservatively with the
  narrower admission (`shiftVerbrauch_eins`) named in CUTS and never assumed;
  mulS/neg twins explicitly stay with the owning lane; no TSO/concurrency/
  source/Spec/goal claim. CUTS boundaries are precise.
- Inhabitation bar met: all premises jointly instantiated; non-degeneracy
  carried by the memory-changing run plus BOTH consumer pins (`.e` true on
  `zeugeFlagsGleich`, false on `zeugeFlags`, so the consumer genuinely
  discriminates) plus the executed branch plus the DIV refusal pair.

## Bounded scope and remarks (not repairs)

1. The witness instantiates the agreement premise at `f = g`, so agreement
   itself is trivial there; strength comes from the generic main theorem
   (arbitrary `f g`) and the non-trivial run/pins/refusals. A future witness
   could use two distinct words agreeing on defined flags only.
2. The shift CF/PF/ZF/SF `= true` map entries are unexercised by every proved
   lemma (only the OF refusal is used); any future shift-admission lemma
   needs count-nonzero evidence first (silicon leaves flags unchanged at
   count 0). Inert now, correctly CUT.
3. Report prose slightly overstates reuse: the file imports and executes
   only `Ausfuehrung`-level evidence (probe + run via accepted lemmas); no
   `ControlCodec` import and no literal `jcc*` witnesses appear in the file.
   Descriptive, not a proof defect.

## Open (unchanged, owned elsewhere)

Hardware correspondence (lane 692 rows), computed liveness analysis, signed-MUL
and NEG ledger twins, TSO/GX, full source-to-final-bytes validation. None
claimed; all CUT.

Co-Authored-By: muse-agent-990 <muse-agent-990@noreply.invalid>
