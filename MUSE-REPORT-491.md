# MUSE-REPORT-491: Independent exact-candidate review of 411

## Scope and method

Review of candidate 411 (adversarial implementation audit DYNAMIC-REGIONS),
pinned HEAD `313d19db622acadf68a947e740022cd95c8857b5`, base
`0b3132b7bb8bf108b3fd1613c70bc0955051f130`, files
`MUSE-REPORT-411.md` + `dokumente/x86/AUDIT-DYNAMIC-REGIONS.md` (doc-only,
no Lean/Rust/central change). Clone verified: `/home/simon/Dokumente/gabbro-muse/a491`,
branch `muse/491`. Candidate commit not fetched locally; review conducted
against the supplied `.tmp/review/author-411/` PATCH (exactly 2 diffs, both
owned files), BUILD-EVIDENCE.json, and the base-tree files quoted by the
audit, all re-read at the pinned base via `git show`. No other clone read.
No candidate files staged into this tree; working tree stays clean except
this report.

## Checks performed

- File list: PATCH contains exactly the 2 SNAPSHOT files; no friend paths
  (`OptimizationRules`/`OptimizationWitnesses`), no checker/Spec/Rust/
  emitter/typ/codec changes. Ownership clean.
- Anchor spot-checks at base (all match the audit's line numbers within its
  "~"/hedged ranges): `Regionen.lean` 631 lines, `reserviere` 92-104,
  `reserviere_frisch`, `initialisiere` 231-239, `FreiStand`/`freiReserviere`
  426-442, witnesses 490-570, CUTS 572-595; `OverlapRefusal.lean` 415 lines,
  `zugriffOk` 44-47, `aliasZulassen` unknown=>refuse 95-98,
  `gegenbeispielC_verweigert`, CUTS 357-380; `AccessList.lean` CUTS 238-250
  (generic completeness, per-rule syntactic classification OPEN);
  `Typen.lean` `Speicher` 41-45, 14-constructor `Befehl` pilot, CUTS 81-86;
  `UebersetzeAllg.lean` `fieldRangeO`/`typAt`/`declOf` present as cited;
  `SchablonenOhneLibc.lean` `region_zugriff` + explicit NOT-proved list
  (kernel contract = premise (c); LG002/O37); `Spec.lean` arena-runtime
  comment block, premises (d) reserve/commit, M10, DynForm note, all present;
  `saetze.rs` sentences `syscall.stub` ~4319-4360, `zeiger.index_in_der_
  ausdehnung` ~4409, `fremd.ohne_code` ~4511, `klon.uebergabe` ~4651, M140
  references present; WORK-ALLOCATION B1/B2/C1/C2/C5 rows as cited.
- R1 verified: zero cites of `region_zugriff` in `grammatik/Grammatik/X86/`
  at base (`git grep` empty). R4 verified: zero cites of
  `accessList`/`AccessList` in `X86/Zugriffe.lean` at base. R2 consistent
  with `Regionen` CUTS ("No loader/image integration").
- Witness-theorem names cited in audit \u00a77 all exist at the quoted lines
  (`zeugenReserviere_erfolg`/`zeugenReserviere_voll` Regionen 511/520,
  `region_schreibLese_zeuge` 536, `nachbarTraeger_disjunkt`/
  `push_in_traeger_angenommen`/`store_in_traeger_angenommen`/
  `gegenbeispielC_verweigert` OverlapRefusal 223/229/238/287).
- Build evidence reproduced: `./lean-probe
  grammatik/Grammatik/X86/Regionen.lean` in this clone (file byte-identical
  base-vs-HEAD, `diff` exit 0) prints `== 0 error(s) in the COMPLETE
  output; exit 0` (first retry exceeded the 120 s queue timeout; retry with
  600 s budget succeeded). Axiom listings in BUILD-EVIDENCE (subsets of
  propext/Classical.choice/Quot.sound) are consistent with the reproduced
  output. No forgery found. Full `./lean-bau` not re-run: candidate adds no
  Lean/Rust file, so tree build state is unaffected by it; the recorded
  `Build completed successfully (392 jobs)` stands as author evidence only.
- Trust boundaries: audit correctly attributes the gate contract to user
  logic (premise (c)), distinguishes hardware faults from profile-admission
  refusals (OverlapRefusal CUTS), treats OS/software contracts as user
  logic, and reads `natAdresse` as target-internal offset arithmetic with an
  explicit precondition on R1/R3 rather than a finding. No safety weakening,
  no desired-correctness assumption, no second IR/toy machine/vacuous
  theorem, no closure claim (verdict: "sound in its parts and open in its
  joints", full source-to-final-bytes validation OPEN).

## Findings

No material defect. One freshness note for the coordinator (not a candidate
defect): audit \u00a73/R3 states `TableLayout.lean` is missing (true at base:
27 X86 modules, no such file). After the base, lane 345 landed C1
`TableLayout.lean` (245 lines, commit `c24590f7`; consumes
`fieldRangeO`/`typAt`/`declOf` exactly as R3 demands). On merge to current
master the "missing" sentence and R3 row go stale. Repair direction: after
merge, a follow-up refreshes \u00a73/R3 against the accepted `TableLayout.lean`
(check R3's disjoint-extent/`aligned N` claims, re-point R1's precondition);
no rework of anything the audit endorses. All other R-tasks (R1/R2/R4/R5)
verified still open at base and correctly marked WAITING/owned elsewhere.

## Deliverable

No new definitions or theorems (review lane; none added by candidate either).
This report is the only owned file. Lean build: `./lean-probe
grammatik/Grammatik/X86/Regionen.lean` -> `== 0 error(s) in the COMPLETE
output; exit 0`. Full `./lean-bau` not re-run (doc-only candidate; see above).
Nothing in the task believed wrong.

CANDIDATE: 411 313d19db622acadf68a947e740022cd95c8857b5
VERDICT: ACCEPT
