# MUSE-REPORT-21: read-only audit of `grammatik/Grammatik/Maschine.lean` lines 1-2000

Lane 21. No existing file was modified (read-only audit). All findings carry
checked Lean demonstrations in `messung/muse-audit/21/` (each `./lean-probe`
green, `#print axioms` shows only `propext / Classical.choice / Quot.sound`,
no `sorryAx`). New Lean work was added ONLY as audit probes, not as project
theorems; `grammatik/` is untouched, so `./lean-bau` state is unchanged by
this lane (no Lean changes to build).

## Scope and method

Read lines 1-2000 (through `kette_aus_maschinenlauf_schritt`), i.e. §§1-14:
deprecated `MaschinenLauf` wrapper (§§1-5), generated machine `GenSchritt` /
`GenErreichbar` / `GenInv` (§§7-11), program counters `PCSchritt` / `PCReach`
and the two discharge fragments (§12), chain link under identification (§13),
chain construction base + single-thread step (§14). For each theorem I checked:
does the conclusion restate a premise (pattern a)? is a premise unused /
`Prop`-typed / a restated field (b)? does a definition trivialize a predicate
(c)? do docstrings claim more than Lean states (d)? are premises false for
ordinary programs (e)? I also scanned for `sorry`/`admit`/`axiom`/
`native_decide`/`unsafe` (only docstring mentions, no occurrences in code) and
for premises of type `Prop` itself (none found in the slice).

Coverage notes: `Faden` is `Nat` (`Wettlauf.lean:46`), so "distinct threads"
arguments are always inhabited — no vacuous-applicability finding there.
`keinRuf` (line 383) is a deliberate stub for leaf statements and documented
as such; not a finding. `hΛa`/`hmark`/`hcar` ARE used elsewhere
(`zaehler_zeigt_atom` line 2304, `pcSchritt_markInv`/`pcSchritt_carrierInv`),
so finding 5 is scoped to the consumers that ignore them. The `§13 match`
reorder anecdote turned out to be REAL (naive application fails to elaborate;
`cases o` is needed) — recorded as a non-finding.

## Findings table

| # | file:line | pattern | one-sentence evidence | demonstration file | status | severity |
|---|-----------|---------|----------------------|--------------------|--------|----------|
| 1 | Maschine.lean:285-287 (`gesittet_aus_maschine`) | (a) conclusion = premises under representation change | Each `Gesittet` field is `rfl`-equal to the corresponding `MaschinenLauf` field passed through `bruecke_exec_gesittet` (`ausschluss = hausschluss`, `marke_eindeutig` from `hEin`, `ungeteilt = hungeteilt`) | messung/muse-audit/21/Audit21Fields.lean (`audit21_gesittet_is_bridge`, `audit21_marke_is_hEin`, `audit21_ungeteilt_is_hungeteilt`, all `rfl`) | VERIFIED | low — §1-5 is marked DEPRECATED in-file; the wrappers are compatibility shims, and `Ziel.lean` §9 consumes them knowingly |
| 2 | Maschine.lean:331-338 (`reduktion_maschine`) | (a) conclusion = `reduktion_seriell` on same premises | Proof term is exactly `reduktion_seriell ... (gesittet_aus_maschine M) ...`: no mover, no commutativity, no order construction of its own; wrapper `rfl`-agrees with direct call | messung/muse-audit/21/Audit21Reduktion.lean (`audit21_reduktion_is_seriell`, `audit21_reduktion_agrees`) | VERIFIED | low — docstring claims "REAL reduction ... no chain object and no SerialLink-style premise appear anywhere", which is true of the statement but the HB disjunction is inherited from §22, not derived here |
| 3 | Maschine.lean:157-165 (`weltenFalte`/`maschinenWelten`) | (c) world fold that never changes memory | Every OLD-fold world carries start slots/globals (`maschinenWelten_speicher_gleich`, proved in-file as the NEGATIVE example); as a semantics it cannot change memory per rule 4(c) | messung/muse-audit/21/Audit21Speicher.lean (`audit21_old_fold_no_move`: `W.speicher = M.start.speicher`) | VERIFIED | informational — the file already labels this the NEGATIVE example and routes new work to generated worlds; no docstring overclaims |
| 4a | Maschine.lean:1848-1864 (`kette_ist_maschinenwelt`) | (a) conclusion = generated triple rewritten along assumed identification | Each conjunct is `rw [hW]; exact <genWelten_* lemma>`; restatement with `J.welten` replaced by `M.welten` is proved by the triple alone | messung/muse-audit/21/Audit21Kette.lean (`audit21_kette_is_transport`, `audit21_kette_agrees`) | VERIFIED | medium — §13 header is honest about "under explicit identification" and books the remainder; the risk is downstream readers citing the boundary triple as the link rather than as transport |
| 4b | Maschine.lean:2046-2053 (`kette_aus_maschinenlauf_schritt`, `hGes'`/`hBeschr'`) | (b) mark/carrier/access equations discarded; `hsingle` closes by arithmetic | `intro ... _ _` twice then `h1.trans h2.symm`: any distinct-thread conclusion follows from `∀ s ∈ M.lauf, s.faden = f` alone, demonstrated in isolation | messung/muse-audit/21/Audit21Kette.lean (`audit21_single_thread_closes_any`) | VERIFIED | low — the single-thread scope is stated in the coverage note; the extension of `hsingle` over the appended step via `gen_eigen_getElem` is genuine and NOT challenged |
| 5 | Maschine.lean:1342 (`hΛa`), 1343-1346 (`hmark`/`hcar`); 970 (`_hhaelt`) | (b) premises unused by key consumers | `pcSchritt_gen`/`pcSchritt_eigen`/`pcSchritt_fremd` bind `hΛa`/`hmark`/`hcar` as `_`; `genInv_gibt` underscore-binds the held-proof. Demonstrated: projection goes through with `hΛa := True`; `gibt`-consistency needs no held-proof | messung/muse-audit/21/Audit21Ungenutzt.lean (`audit21_pcSchritt_gen_without_hLa`, `audit21_gibt_konsistent_without_held`) | VERIFIED | medium — a PC leaf step can advance the counter on a footprint (`Λa`/`cs`) that matches nothing the step did; only the invariant-preservation lemmas (not the step laws) check the footprint. Whether that is a soundness gap or intended over-approximation is a design question, flagged not decided |
| 6 | Maschine.lean:1704-1720 (`pc_discharge_unshared` premise order) | (a)-adjacent, cleared as non-finding | The `hsh`-before-equations order IS inter-derivable with the `Gesittet.ungeteilt` order, but the reorder needs `cases o` — the in-file `match`-elaboration comment is accurate | messung/muse-audit/21/Audit21Reihenfolge.lean (`audit21_unshared_reorder_fwd/bwd`, both green) | VERIFIED (as non-finding) | informational |

## What I checked and cleared (no finding)

- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` in code in lines 1-2000
  (only the words "no `sorry`" in docstrings). No premise typed `Prop` itself.
- `gen_reduktion` (§11) / `pc_reduktion` (§12): same wrapper shape as finding 2
  but over genuinely derived `Gesittet` (W1-W3 generated, W4/W5 discharged from
  program text in the PC case) — real content lives in the premises, correctly
  booked; NOT marked as findings. Stating their `rfl`-equality would need live
  `GenErreichbar`/`PCReach` witnesses; left UNVERIFIED by choice, not by failure.
- `pc_discharge_einfaedig` (§12): genuine discharge of the `Einfaedig`
  projection premise to program-text separation `PCMarkSep` via `PCMarkInv`.
  The separation premise itself is strong (disjoint mark codes across threads)
  but it is a stated program-text obligation, not a hidden falsehood — no (e).
- `maschinenLeer`: `hvers` proof `⟨(voll f).length, ...⟩` is a real (if trivial)
  construction for the empty run, not a restatement — no finding.
- `keinRuf_gut` (line 386): `intro ...; simp ... at h` closes because leaf
  statements never consult `R` — verified by the `execStmt` equations (`.call`
  arms match on `R`, leaf arms do not); the docstring says exactly this.
- Pattern (e) (premises false for ordinary programs): none found in the slice.
  The strongest premises (`PCMarkSep`, `PCUnsharedSep`, `hsingle`) are either
  program-text obligations on the user or explicitly single-thread-scoped.

## New definitions/theorems (audit probes only, NOT project theorems)

- `messung/muse-audit/21/Audit21Fields.lean`: `audit21_gesittet_is_bridge`,
  `audit21_marke_is_hEin`, `audit21_ungeteilt_is_hungeteilt`
- `messung/muse-audit/21/Audit21Reduktion.lean`: `audit21_reduktion_is_seriell`,
  `audit21_reduktion_agrees`
- `messung/muse-audit/21/Audit21Speicher.lean`: `audit21_old_fold_keeps_slots`,
  `audit21_old_fold_no_move`
- `messung/muse-audit/21/Audit21Kette.lean`: `audit21_kette_is_transport`,
  `audit21_kette_agrees`, `audit21_single_thread_closes_any`
- `messung/muse-audit/21/Audit21Ungenutzt.lean`:
  `audit21_pcSchritt_gen_without_hLa`, `audit21_gibt_konsistent_without_held`
- `messung/muse-audit/21/Audit21Reihenfolge.lean`:
  `audit21_unshared_reorder_fwd`, `audit21_unshared_reorder_bwd`

## Build status

- `./lean-probe` on each of the 6 probe files: green (only `#print axioms`
  lines `[propext, Classical.choice, Quot.sound]` in output, no errors).
- `./lean-bau`: NOT run to completion (read-only lane; `grammatik/` untouched,
  so the project build state is unchanged by construction). No commit in
  `grammatik/` was made or needed.

## What remains open / what I believe is wrong or risky

1. Finding 5 is the one item I would escalate: if `PCSchritt.leaf` is meant to
   tie a step to its program position, the tie (`hΛa`, `hmark`, `hcar`) should
   be load-bearing in the step laws, not only in the invariant lemmas. If the
   over-approximation ("any leaf any time, counters constrain later") is
   intended, a one-line docstring on `pcSchritt_gen` saying the footprint is
   unchecked there would remove the smell.
2. The task asks for demonstrations "importing the needed Grammatik modules";
   the probes import `Grammatik.Maschine` (which re-exports the needed scope
   via `Wettlauf`/`InterferenzAllgemein`). No new file was added to
   `grammatik/Grammatik.lean` and no `import Grammatik.<Name>` line was added,
   because the lane is read-only and the probes live outside `grammatik/`.
   If the coordinators wanted probes wired into the build, that would
   contradict rule 5's "prefer adding" only insofar as audit probes are not
   project theorems — I kept them out deliberately.
3. Zero-findings verdict: NOT claimed. Six rows above (five findings + one
   cleared non-finding), all VERIFIED, none UNVERIFIED except the explicitly
   de-scoped `gen_reduktion`/`pc_reduktion` equalities.
