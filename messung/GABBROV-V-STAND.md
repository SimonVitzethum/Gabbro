# GabbroV lead (Sonnet V) -- state log

Branch `worktree-agent-aee96f1083a70ddef`. Muse agents 02 (parser/elaboration) and 04 (linked
structures, chains, splits) work in their own clones and are integrated here by copy.

## 2026-10-08 -- first integration

Integrated (copied from the agents' committed clones, reviewed by reading headers, `sorry`
grep, axioms lines in the build output):

| From | Files | What |
|---|---|---|
| 01 | `GvStartPflicht` (60 -> 342 lines), `GvLuecken` | `StartPflicht` without the `Initially` assumption for the parser fragment (`gv_startPflicht`, `sp0Of`), review gaps L_a..L_f as theorems (`gvLuecke_*`), incl. `elabU` refuses statics |
| 02 | `GvParserFragment3`, `GvParserFragment4` | `elabU03` (prototype drop), `elabU04` (exclusive-bound normalisation), `elabU05` (ground drop), `elabU06` (format drop), each with agreement (+104) / refusal / decided witness |
| 04 | `GvVerkettung`, `GvKetten` | `randOk_gibt_hrand` (linked-structure step), `rufKette_invariant` (generic call chain, 147/148 shape), `disjunkt_einmal` (126) |
| 05 | `GvAtomKoerper` | full rely duty for atomic-bearing bodies (two pinned read sites) |

Not yet integrated: 02's `GvParserFragment5` (refusal theorem unverified), 04's `GvBruecke`
(`kette_gleicht`, agreed by agent, uncommitted when copied), 05's `GvPinStellen` (untracked).

Measured: `./lean-bau` -> `Build completed successfully (739 jobs)`; `gabbro_ziel` and siblings on
exactly `propext, Classical.choice, Quot.sound`; `lean-layout --check` OK; `pruefe-kein-sorry`
0 violations.

Corpus elaboration by the Lean parser (agent 02, tip `elabU06`, 157 files): OK 10, parse
refused 48, elab refused 99. Bridge closed (premise (b), `bruecke/`): 2 (104, 108).
Honest reading: the elaborator tally has moved from 2 to 10 OK units, but the bridge to (b)
exists only for the `UStmt` fragment (writes + calls); the 8 further OK units are not bridged.

Open (assigned): V-02 all-refusals census + `elabU08`; V-04 store-level bridges (`World` ->
`RufKette`/edge map), the gap behind every conditional discharge of 01/55/F01/kapraum/147/148.

## 2026-10-08 (later) -- second integration

Integrated: 04 `GvStore` (store frames, `kantenBild` commutation, `zahl_tick_vertrag`, witnesses),
`GvBruecke` (`kette_gleicht`), updated `GvKetten` (RufKette over abstract states); 02 `GvZensus`
(continue-on-refusal census, `zensus104_leer`, `zensusMulti_exakt`). `./lean-bau` 742 jobs green,
no `sorryAx` in the output. Review note: the first build failed because `GvKetten` was copied
before 04's generalisation; fixed by copying the matching version (the agent's clone was fine).

Census (02, 157 files): parse-refused 48; presence markers return 124, let 80, if 53, bool 56,
locks 39, static 38, reason 28. Ranked flip constructs: bare syscalls 11, quantifiers 11, syscall
clauses 6, bounded strings 5, lock invariants 4 (all parser-level or model-level; the verified
singletons 63/64, 27/38, 72, 03, 131 need extern/static/format models or are unsound to accept).
Finding: no single remaining elaboration case flips any corpus unit.

Assigned next: 02 V-02b parse-level acceptance of the nine ranked syntax forms (elab keeps
refusing by name) then re-census; 04 V-04b `GvLauf` (world-run induction, closing the conditional
discharges of 01/F01/kapraum/147/148 given per-call contracts).

## 2026-10-08 (evening) -- GvLauf integrated

04 `GvLauf`: `weltLauf_uebereinstimmung` and `weltLauf_invariant` (a run of N contract-respecting
world steps agrees with the abstract `rufLauf`; invariant on the final World), witness
`kettenLauf_invariant_zeuge` (2 real writes) and planted failure `weltLauf_ohne_vertrag_bricht`.
Effect: the counter halves of 147/148/01/F01/kapraum are theorems given per-call contracts and the
initial-state premise. Build 742 jobs green, standard axioms, no sorryAx. Review lesson: copying
files piecemeal from an agent's clone produced sorryAx/errors when companion files (GvKetten,
GvStore) had moved; always copy the whole agent GabbroV set and check for `sorryAx` in the output.
Next: 04 V-04c TreeState projection (kapraum `blatt_loeschen`), 02 V-02b parse-level acceptance.
