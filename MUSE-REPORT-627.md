# MUSE-REPORT-627: Independent review of lane 626 (FloatEntryState)

## Candidate

CANDIDATE: 626 0f580521282929dd802e75bcf0f3a4c7e2d05c75

Base of candidate: a71b7e638d008cab47f352326a09e37980cff314.
Diff against its own base is exactly three files, purely additive:

- `grammatik/Grammatik/X86/FloatEntryState.lean` (new, 557 lines)
- `grammatik/Grammatik.lean` (one additive import line)
- `MUSE-REPORT-626.md` (report)

No existing file touched otherwise; no executor, decoder, IR, source,
checker, emitter, or friend-reserved optimiser change.

## VERDICT: ACCEPT

## What was checked

1. **Exact candidate material.** Fetched `muse/626` from the author clone
   into `FETCH_HEAD`; pinned HEAD `0f58052...` matches
   `.tmp/review/SNAPSHOT.json` (`clean: true`). Reviewed the exact
   `FloatEntryState.lean` content and the author report. Producer modules
   (`ScalarFloat`, `EntryState`, `FeatureProfile`, `ContractSites`,
   `Gleitprofil`) are byte-identical between the candidate base and this
   reviewer's master, so a single-file probe here is faithful.
2. **Lean check.** Transplanted the exact candidate file into this clone
   (untracked path only, no tracked edit), ran `./lean-probe
   grammatik/Grammatik/X86/FloatEntryState.lean`: `== 0 error(s) in the
   COMPLETE output; exit 0`. Axiom report matches the author claim
   exactly: `eintrittFp` and `zeugenEintrittFpHosted_kontext` axiom-free,
   most theorems `propext` only, the five §3 step theorems
   `propext + Quot.sound` (inherited from the reused ScalarFloat
   equations), `floatEintritt_zeuge` the full standard triple
   `propext, Classical.choice, Quot.sound` (inherited from the source
   fixture). Transplant removed afterwards; working tree clean.
   Full-project evidence from the author log: `./lean-bau` 447 jobs
   green at candidate HEAD (plausible: base-era job count).
3. **Bans and rule 4.** `grep -nwE 'sorry|admit|axiom|native_decide|unsafe'`
   finds nothing (only English words containing "admit" as substrings:
   "admitted"/"admits"). No `intro _`, no `have _ :=`. No conclusion is a
   premise renamed; no contract parameter/result is quantified away;
   `eintrittFp` is a data projection, not a claimed semantics; memory
   changes come from actual `fpSchritt` steps and the actual
   `execStmt`/`rufAt`-derived source fixture.
4. **Real interfaces, no invented semantics.** Every consumed name
   resolves to an existing producer theorem/definition: `mxcsrOk`,
   `eintrittOk`, `bereit`, `merkmalZugelassen`, `fpEintritt`,
   `fpSchritt` + all fifteen arm equations, `mxcsr_ftz/daz_verweigert`,
   `mxcsr_runde_unten_verweigert`, `sse_verweigert_ohne_profil`,
   `fpZeugeKern/fpZeugeT/fpZeuge_schritt1/fpZeuge_schritt2/fpZeuge_liest/
   fpZeuge_speicher_aendert`, `vertragStandort_lauf_zeuge`,
   `write_read_zeuge`, `ReqAmEintritt`. The module consumes rather than
   duplicates: the pre-existing FTZ/DAZ/round-down rows are reused, not
   re-proved; the FP run reuses the certified producer witnesses.
5. **New connection (not a wrapper).** Genuine new content: the
   entry-word-as-context bridge `eintrittFp` with its profile identity;
   transfer theorems from `mxcsrOk`/`eintrittOk` to `fpEintritt` and
   `bereit`, and back from `merkmalZugelassen`; preservation of `t.fp`
   across all fifteen admitted `fpSchritt` forms proved arm-by-arm;
   bounded-admission readout (`fpSchritt_zugelassen_heisst`);
   no-installation (`kein_fpSchritt_installiert`); entry-level refusals
   lifting word refusals to `mxcsrOk`; the three-way FTZ refusal across
   entry, feature and FP admission; hosted + freestanding accepts.
6. **Witness (rule 13).** `floatEintritt_zeuge` is JOINT and
   non-degenerate on both sides: target side runs two reached admitted
   `fpSchritt` steps (`divsd` 1.0/+0.0 = +inf, `movsd` store) with
   read-back and an observable memory-byte change; source side reuses
   `vertragStandort_lauf_zeuge`, which I verified carries a reached run,
   `(eD.signatur eSetze).schreibt () = true` (a table some function
   writes), `ReqAmEintritt` at actual values, and slots `0 -> 5`, plus
   `write_read_zeuge` (eight-byte change, nonzero value). No lowering
   between the sides is claimed; CUTS says so explicitly.
7. **Refusals.** Concrete refused words proved at the entry predicate:
   FTZ `0x9F80`, DAZ `0x1FC0`, round-down `0x3F80`, round-up `0x5F80`,
   round-to-zero `0x7F80`, trap-on-exception `0x1F00`, cleared mask
   `0x1D80`, plus the generic `mxcsrOk_verweigert_ungueltig`. Accepts
   (`0x1F80` hosted and freestanding) proved by `decide`.
8. **No conflation.** FP special-case result reuses the producer's
   certified divide witness; NaN class-level gap inherited and stated,
   not upgraded. No byte/word atomicity claim: sequential `Speicher`
   only, TSO/GX explicitly out of scope in CUTS. No silicon/binary
   verification claimed. No OS content: hosted/freestanding differ only
   in IF/guard legs owned by `EntryState`.
9. **Honest CUTS.** The file ends with an exact CUTS block plus
   `#print axioms` for every new theorem. The byte-decoder gap is stated
   plainly (`FpDecodiert` arrives constructed; LDMXCSR/STMXCSR have no
   accepted byte form; establishment from entry bytes OPEN), matching the
   task's own fallback clause. Full source-to-final-loaded-bytes remains
   OPEN. Nothing in the task turned out wrong; the author's remark that
   "decoded" means constructed `FpDecodiert` values is accurate.

## Integration note for the merger (not a rejection)

The candidate branched from `a71b7e63`, which predates current master
`eb68896b`. Against current master the candidate HEAD textually lacks
later modules (`ExpressionLowering`, `ValidatorExecution`, lane/report
renames) that it never touched. A merge must rebase/re-apply the three
additive files onto current master (one new file + one import line);
it must NOT delete the newer modules. The candidate's own diff is clean
and conflict-free in intent (append-only import).

## What remains open

As recorded in the candidate CUTS: no FP byte decoder, no
control-word load/store form, no lowering between witness sides, no
concurrency/cost/timing transfer, sticky flags and NaN payloads
unmodelled (inherited). Full source-to-final-loaded-bytes validation
stays OPEN.
