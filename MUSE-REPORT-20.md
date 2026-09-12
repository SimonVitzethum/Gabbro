# MUSE-REPORT-20: read-only audit of Ziel.lean lines 1200-end

Scope: `grammatik/Grammatik/Ziel.lean` lines 1200-2432 (sections 9b-continued,
10, 11, 12, 13). No existing file modified. One new demonstration file:
`messung/muse-audit/20/Audit20Shapes.lean`, checked with `./lean-probe`
(clean: no errors, no sorry; `#print axioms` shows only
`propext/Classical.choice/Quot.sound` for F1/F3, none for F4).

The slice contains 7 theorems: `ziel_nutzer_last_aus_pc_stabil` (1283),
`genEigen_wit_index` (1470), `kette_mit_zeugen_schritt` (1498),
`kette_mit_zeugen` (1709), `kette_mit_zeugen_orakel` (1787),
`hwitschritt_kleber_reuse` (1914), `hwitschritt_kleber_voll` (1969),
`kette_aus_lauf_bezeugt_closed` (2235), `ziel_nutzer_last_aus_pc_Q` (2324).
Checked for patterns (a)-(e): no `sorry/admit/axiom/native_decide/unsafe`
in the slice (only the words in prose); no premise of type `Prop` itself;
every theorem proof passes each premise to a callee (spot-checked the two
goal theorems and the chain steps argument-by-argument -- all premises
forwarded). The goal-conclusion conjuncts (Gesittet leg, zwei_fehler leg,
Einfaedig leg, unshared leg, world-count legs, frist leg, bound leg, HB leg)
are each discharged by a distinct imported lemma, not restated premises.

## Findings

| # | file:line | pattern | evidence (one sentence) | demo | status | severity |
|---|-----------|---------|-------------------------|------|--------|----------|
| F1 | Ziel.lean:1516 (`hsingle`), :1532, :1987; goal HB conjunct :1365/:2416 | (e) false-for-ordinary-programs premise | `hsingle : forall st in M.lauf, st.faden = f` forces a single-thread run while the goal conclusion carries a two-thread race disjunction over `g1 != g2`; on any run with steps of two threads the conjunction is empty. | `Audit20Shapes.lean`: `F1_two_threads_break_hsingle` (two-thread TestD run falsifies `hsingle` for every `f`) | VERIFIED (shape) | MEDIUM |
| F2 | Ziel.lean:1542, 2016 (`hlen`) | (b) unused premise/derivation | `have hlen : M.welten.length = J.schrittFaden.length + 1` is derived in both `kette_mit_zeugen_schritt` and `hwitschritt_kleber_voll` and never referenced afterwards (grep: exactly 2 occurrences, both `have`). | on-file grep evidence only | UNVERIFIED | LOW |
| F3 | Ziel.lean:1428-30, 1486-97, 1905-13 (headers: "UNCONDITIONAL table link") | (d) header claims more than Lean states | `SerialLink` (InterferenzAllgemein.lean:1721) is conditional per step (`TraegerSchreibt ... = true -> exists event`); a non-writing thread owes no witness, so "unconditional" overclaims. | `Audit20Shapes.lean`: `F3_link_needs_no_event_without_write` (vacuous leg, no run event needed) | VERIFIED (shape) | LOW |
| F4 | Ziel.lean:1914 (`hwitschritt_kleber_reuse`) | (b) conclusion = premise-class restatement | The reuse glue takes exactly the `kette_mit_zeugen_schritt` premises and concludes exactly its conclusion by one positional application -- pure forwarding, no new content. | `Audit20Shapes.lean`: `F4_forwarding_is_identity` (forwarding shape adds nothing) | VERIFIED (shape) | LOW |
| F5 | Ziel.lean:1869, 1893, 1962, 2008-2067 (headers citing `Ziel.lean:1466`, `:1357-1361`, `:1362-64`, `:1401-04`, `:1405-62`, `:1466-71`, `:1472-1513`; `MaschinenKette.lean:466`, `:1051`) | (d) doc references point at wrong lines | `Ziel.lean:1466` today is the `genEigen_wit_index` docstring, not the chain literal (now :1646/:2131); `1357-1373` is the goal-theorem conclusion, not the §10 proof; `MaschinenKette.lean:466` is mid-comment. Headers drifted as the file grew. | none possible | UNVERIFIED | LOW |

## What I checked and cleared (no finding)

- Pattern (a) conclusion=premise: the 12-conjunct goal conclusions are
  discharged by distinct lemmas per leg (`pc_gesittet`, `pc_konsistent` +
  `pc_gut_obs`, `stabil_aus_lauf`, `sampling_closes_frist`,
  `hLowering.begrenzt`, `zwei_fehler`, `pc_discharge_einfaedig`,
  `pc_discharge_unshared`, `genWelten_laenge/gut/letzte`, `pc_reduktion`).
  Each leg cites a different imported theorem; none restates a premise.
- Pattern (b) unused premise: all premises of the two goal theorems and the
  chain steps are forwarded positionally (verified by reading each
  application argument list). The `_`-prefixed binders live in
  MaschinenKette's `hWitSchritt`, outside the slice.
- Pattern (b) `Prop`-typed premise: none in the slice (checked signatures).
- Pattern (c) trivializing definitions: no new predicate definitions in the
  slice except the reuse/glue theorems; `SerialLink`/`SpecQ`/`QRequires`/
  `QEnsures` live outside the slice and quantify over actual functions,
  threads, and worlds (no `forall rho`/`forall v` degeneration of the
  `requires`/`ensures` BINDERS -- note `QEnsures` does quantify over return
  values and envs, but that is the contract-predicate definition, inherited
  from Extraktion, not introduced or widened here).
- Pattern (c) memory-frozen worlds: `weltenFalte`-style folds are outside
  the slice; the slice extends worlds via `M.welten ++ [sigma']` from
  `execStmt` outcomes.
- Section 13 (`ziel_nutzer_last_aus_pc_Q`): genuine instantiation, not a
  restatement -- `hAb`/`hMemAll` discharged by `haengtAb_vertrag_gesamt` /
  `speicherVertrag_aus_Q` with four explicit footprint premises; the
  footprint narrowing rides openly, not hidden.

## Caveats on the findings

- F1 is narrowed by the report's own CUTS: the HB disjunction needs two
  access EVENTS (possibly same thread at different indices), while `hsingle`
  forces one thread; the §12 header itself books "single-thread runs" as
  narrowing, and the goal theorems do NOT carry `hsingle` themselves -- the
  tension is real only where the §10/§11 steps feed the whole-run induction.
  I demonstrate the `hsingle`-vs-two-threads incompatibility, not an empty
  conjunction of any slice theorem.
- F2-F5 are hygiene, not soundness bugs: dead `have`, header wording, pure
  forwarding, stale line numbers. Zero soundness-critical (pattern a)
  findings: nothing in the slice concludes a premise under another name.

## Build status

- `./lean-probe messung/muse-audit/20/Audit20Shapes.lean`: green (no errors;
  one initial `omega` failure fixed by rewriting to `trans`+`simp`; one
  unused-variable linter warning fixed by dropping the binder).
- `./lean-bau`: green -- `Build completed successfully (29 jobs).` (run after
  the audit; `grammatik/` untouched, as required for a read-only lane).

## Open / for the owner

- Decide whether `hsingle` (single-thread) steps can ever feed the two-thread
  goal, or whether §12's induction genuinely stays single-thread (then the
  goal's HB leg is dead for those runs -- worth one booked line).
- Remove the two dead `hlen` haves or reference them; fix "UNCONDITIONAL" to
  "witnessed-conditional"; refresh stale line numbers in §11/§12 headers
  (or drop line citations -- they rot on every edit).
- `hwitschritt_kleber_reuse` is subsumed by `hwitschritt_kleber_voll`
  (same premises, 5 vs 7 conjuncts); consider deleting the reuse leg.

Co-Authored-By: muse-agent-20 <muse-agent-20@noreply.invalid>
