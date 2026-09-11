# Measurement baseline for the goal (Phase 0, docs only)

Branch `p02-ziel`, base `2dc02ad` (`Lanes 131-150: adopt the design into
checker and emitter`). Recorded 2026-09-11T13:24:34Z in worktree
`.claude/worktrees/p02`. No code changed, no builds run, no instruments
beyond the four light text guardians. Every number below carries the exact
command that recomputes it (all read-only; run from the worktree root).

## Machine and server state

- Local memory at recording time (`free -g`): 31 GB total, 12 GB available.
  Above the 6 GB local-work floor, so light read-only measurement is fine;
  no build was started anyway (Phase 0).
- Server `ki-pc-fisch-101`: ordered DOWN for this mission, all work stayed
  local. Observation, not an action: a single `ssh -o ConnectTimeout=5
  ki-pc-fisch-101 'echo alive'` probe returned `alive`. The mission
  constraint (work local) was kept regardless; no remote session opened.

## Light text guardians (as found, unmodified tree)

| guardian | exact command | result |
|---|---|---|
| todo | `python3 instrumente/pruefe-todo.py` | EXIT 2 — aborts inside its own speech test (`Giftliste` 6 ok, `Saubere Liste` 1 finding = false red, plus EN-label drift); everything behind the cut unmeasured |
| kennungen | `python3 instrumente/pruefe-kennungen.py` | EXIT 0 — ALL PASS, 300 identifiers assigned |
| englisch | `python3 instrumente/pruefe-englisch.py` | EXIT 1 — four ratchets broken (7904 vs 7881 German comment lines in checker sources, 1085 vs 1069 in instruments, 24 vs 23 German feeders, 1 vs 0 German sink messages); run cuts off after the language figure |
| syntax | `bash instrumente/pruefe-syntax.sh` | EXIT 0 — ALL PASS, EBNF 161 rules defined with 0 open, 221 terminals vs 221 table words |

## Goal numbers

| # | quantity | measured | booked | exact recompute command |
|---|---|---|---|---|
| 1 | open ruling-table slots (Lean `tafel` status `.offen`) | 8 of 30 | 30 open except `bedingt` (stale doc comment on `tafel`) | `grep -n "^\s*[.]luecke [.a-zA-Z]* [.]offen,$" grammatik/Grammatik/Erhaltung.lean` (the 8: `zeigerArithmetik cInclude cTypedef cDefine cEnum voidTyp cAttribut cSizeof`); denominator `grep -c "| OffeneForm" grammatik/Grammatik/Erhaltung.lean` cf. the 30-variant inductive at lines 211-241 |
| 2 | `sorry` count in checked-in Lean sources | 23 text mentions, 0 admitted proofs (2 mechanism uses inside tactic definitions) | 24 `sorry` over 192 generated corpus modules | mentions: `grep -rn "sorry" --include="*.lean" programmlogik grammatik \| wc -l`; mechanism: `Body.lean:3106,3112` (`all_goals sorry` inside the `gabbro_auto` tactic definitions, by design); booked figure: `Body.lean:2776`, recomputed by `instrumente/pruefe-lean-beweis.sh` (heavy: builds all generated modules — NOT run in Phase 0) |
| 3 | open CForms (census slots without adopted ruling) | 8 (5 ruled on paper but not adopted into `tafel`, 3 with no ruling file at all) | 30 census findings (26 under the generous reading); 19 paper rulings; "12 slots flipped" (merge message) | paper rulings: `ls messung/CFORM-REGEL-*.md \| wc -l` (= 18 files, all `Status: ruled`, plus the worked `?:` template in `CFORM-ABARBEITUNG.md` §3 = 19); adopted: 30 minus the 8 from row 1; no-file triple: `zeigerArithmetik cInclude cSizeof` (no `CFORM-REGEL-*` match); paper-but-offen five: `VOID ATTRIBUT TYPEDEF DEFINE ENUM` (`grep -h "^Status" messung/CFORM-REGEL-*.md`) |
| 4 | LESESTELLE gaps (parser-mapping draft) | 10 gap names, 26 LESESTELLE rows | 25 rows under ten gap names; 124 core + 12 SUGAR + 25 = 161 | rows: `grep -c "| LESESTELLE" messung/SYNTAX-PARSER-ENTWURF.md` (= 26); names: `grep -o "G-[A-Z]*" messung/SYNTAX-PARSER-ENTWURF.md \| sort -u` (G-LEX G-NAME G-FILTER G-LAYOUT G-SPACE G-SCHEME G-HELD G-COST G-CONC G-RELABEL); total rows `grep -c "^\| \`" = 161 and `grep -c "| SUGAR |"` = 12, so core-kind rows are 123, not the booked 124; G-RELABEL names zero rows |
| 5 | specified-but-unwired modules | 5 (`absenkung tearing certemit corrcert kostenledger`), 0 code references outside their own files | same 5 in the merge message of `2dc02ad` | per module M: `grep -rn "M::" crates/ --include="*.rs" \| grep -v "src/M.rs" \| wc -l` (= 0 for all five); declared-but-uncalled: `grep -n "pub mod" crates/gabbro-check/src/lib.rs`; `bau` is NOT unwired — separate CLI module (`mod bau` in `gabbro-cli/src/main.rs`, reachable via `gabbro build`, emits nothing); `H022` is NOT unwired either — wired in `lib.rs:400-404` (timed) and `:440-444` despite the merge message saying "(unwired)"; the integration wired it |

## Discrepancies found while measuring (recorded, not fixed — Phase 0)

1. `tafel` cites three ruling files that do not exist anywhere in the tree:
   `messung/CFORM-REGEL-SENKUNG-142.md`, `ZULASSUNG-143` batch,
   `messung/CFORM-REGEL-SENKUNG-144.md` (7 cite comments on 6 rows,
   `Erhaltung.lean:308-318`; `find . -name "*SENKUNG-14*"` and
   `-name "*ZULASSUNG*"` return nothing). Comment-only cites, no build
   impact, but the cites are not recomputable.
2. Five paper rulings (`VOID ATTRIBUT TYPEDEF DEFINE ENUM`, all
   `Status: ruled 2026-09-11, admit with price, no emitter change`) are not
   adopted into `tafel` (still `.offen`). Either the table lags the paper
   or the paper is not accepted — the baseline cannot tell which.
3. The `tafel` doc comment ("the 30 census slots open -- except `bedingt`")
   predates the 21 further adoptions; the prose count in
   `SYNTAX-PARSER-ENTWURF.md` (25 LESESTELLE / 124 core) is off by one row
   against the tables (26 / 123).
4. Guardian state at base: `pruefe-todo.py` EXIT 2 in its speech test and
   `pruefe-englisch.py` EXIT 1 on four broken ratchets. Any later green/red
   against these two must be differenced against THIS baseline, not against
   "all pass".
