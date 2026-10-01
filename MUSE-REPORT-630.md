# MUSE-REPORT-630: Direct-source closure — SourceAccessCompleteness (G5)

Lane 630, clone `/home/simon/Dokumente/gabbro-muse/a630`, branch `muse/630`.
Owned files only: `grammatik/Grammatik/X86/SourceAccessCompleteness.lean`
(733 lines, new), one additive import in `grammatik/Grammatik.lean`, this report.

## What was done

G5 of `dokumente/x86/CONCURRENCY-CLOSURE-PLAN.md`, bounded form: the source
access enumeration of the small actually admitted lowering fragment — one
`Stmt.assignSlot` step on an `.int` slot with `repOk = true`, executed
through the real `execStmt` — proved complete against the actual G access
predicates and matched to realised target footprints, with every
unsupported rule/profile form refused. No claim about all ~70 G rules.
Full source-to-final-loaded-bytes remains OPEN.

New definitions (all in `Gabbro.Grammatik.X86`):
- `fragmentListe t orte`: the enumeration — write `(.inl t, true)` plus one
  read per carrier of the actual read footprint. Computed from actual
  source data, not a parallel machine or toy record.
- `fragmentProfilOk c ty base len off`: carrier admission (`repOk` for
  tables, always `false` for globals).
- `fragmentZielOk base off`: checked 8-alignment guard for one fragment word.
- `regelOk s`: rule admission (only `assignSlot`).
- `IstAssignSlot s`: classifier family for the admitted rule shape
  (an equation `s = assignSlot …` is ill-typed across statement indices,
  so the shape is a family; consumers invert it).
- `fragStore`, `fragStoreVor`, `fragLoad`, `fragLoadVor`: joint
  source/target witness states (realised store/load at the slot address).

New theorems:
- `fragmentDelta_voll`: an actual `execStmt` assignSlot step records
  exactly `fragmentListe t (i.orte ++ e.orte)` (trace delta via `take`).
- `blattFragment_voll`: the G access list IS the enumeration;
  the write is recorded (`SchreibG`); every read is a footprint carrier
  (`LiestG`); every access is the written table or a footprint carrier
  (`ZugriffG`); only the written table is ever written (slot ownership,
  via `schreibSlot_fremd_tab` plus globs-by-construction for the
  changed-memory disjunct).
- `fragmentStore_passt`: admitted source write + realised `store64` with
  matching address/register gives exactly the 8-byte slot footprint,
  length 8, the source value as stored word, and the read-back parse.
- `fragmentLoad_passt`: a realised `load64` at a represented slot loads
  exactly the source slot value, destination updated, memory unchanged.
- `regelOk_nur`: every admitted rule is `assignSlot` (generic case over
  the actual statement; all other forms refused).
- `repOk_opt/summe/grund/nie/float/fnzeiger/zeiger_verweigert`: the
  remaining non-`.int` profiles refused (`bool`/wide/out-of-region are
  pinned in `SourceMemory`).
- `fragmentProfil_global_verweigert`, `fragmentProfil_wit_ok`.
- `fragmentOhneUmbruch`: no 64-bit wrap, derived from `repOk` bounds.
- `fragmentZiel_ok_zeuge`, `fragmentZiel_schief_verweigert`.
- `fragmentFussEigentum_zeuge`: disjoint admitted slots own disjoint
  8-byte footprints (target side; source side is `rep_fremd_tab`).
- Helpers: `filterMap_leseEv`, `take_neuAppend`, `fragmentListe_invert`,
  `schreibG_zugriff`, `fragmentListe_schreibt`.

Joint non-degenerate witnesses (all on `witD`, one table its function
writes, with memory-changing steps): `fragmentDelta_voll_zeuge`,
`blattFragment_voll_zeuge` (G frame over `brueckenG`), 
`fragmentStore_passt_zeuge` (reached realised store, bytes changed both
sides), `fragmentLoad_passt_zeuge` (register observably changed),
`regelOk_nur_zeuge`. Every syntax-quantified theorem has its `_zeuge`.

## Checks

- `./lean-probe grammatik/Grammatik/X86/SourceAccessCompleteness.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau`: `Build completed successfully (447 jobs).`
- `#print axioms`: every theorem within `propext`, `Classical.choice`,
  `Quot.sound` (several use fewer). No `sorry`/`admit`/`axiom`/
  `native_decide`/`unsafe`.
- Commits on `muse/630`: `f3ad1083` (enumeration + delta),
  `979c1473` (G completeness), `120792c6` (store match),
  `300fa1ae` (load match), `e3f69606` (refusals + grouping/ownership).

## What remains open (see file CUTS)

Single-slot fragment only; no validator soundness (`valX86_sound`
OPEN); no per-access TSO refinement (consumer: `BrueckenProfil`/
`WortGuard`, reused unchanged); no full G-rule table; no hardware,
OS/loader or int->ptr claims; consumer interface documented in CUTS.

## Notes for the reviewer / coordinator

- No duplication: `AccessList.zugriffG_voll` proves generic completeness
  for every step; this lane ADDS the fragment enumeration computed from
  actual `execStmt` data, the realised-footprint match (`hAddr`/`hReg`/
  `hSlot` links), the rule/profile refusals and the grouping/alignment/
  ownership checks. Producer lemmas are cited (`rep_schritt_bleibt`,
  `realisiert_store64_fuss`, `realisiert_load64_gefunden`,
  `zugriff_store64_acht`, `disjunkt_von_layout`, `schreibSlot_fremd_tab`),
  never restated.
- Apparatus findings (all worked around, recorded for follow-ups):
  nested-`++` rewrite patterns (`?a ++ (?b ++ ?c)`) never match in
  `rw`/`simp only` here, even concretely — association was done via
  term-mode `trans` with explicit arguments plus the single-level
  `take_neuAppend`; the `set` tactic is unavailable (used `generalize`);
  structure-update `{ x with … }` failed to parse in two spots (used
  explicit constructors); a statement-level equation `s = assignSlot …`
  is ill-typed across statement indices (used the `IstAssignSlot`
  family); `simp only [regelOk]` does not split the catch-all (full
  `simp` does).
- Nothing in the task statement itself was found wrong; the "no ~70-rule
  assertion" scope was respected throughout.
