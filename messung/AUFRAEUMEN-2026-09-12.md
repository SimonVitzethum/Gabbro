# Cleanup 2026-09-12: Python script census (lane 118)

Scope: all 83 tracked `*.py` files (69 under `instrumente/`, 14 under `messung/`).
Rule: a script may be deleted ONLY if its basename appears nowhere else in the
tracked tree (zero references outside itself and its own `__pycache__`, which is
git-ignored and untracked). Guardians (`pruefe-*.py`), anything `abnahme.py` or a
`.sh` calls, and anything a test calls always stay. A document citing a script as
the command that produced a number counts as a use.

## Method (per row)

```sh
b=$(basename <file>)
git grep -l --fixed-strings "$b" -- .   # references; the file itself excluded
git log -1 --format=%cs -- <file>       # last commit date
# deletion candidates additionally:
git grep -n --fixed-strings "<stem>" -- .  # import/call without suffix
```

Branch state at measurement: `muse/118` (waves 1-3 merged, plus wave-4/5 lanes).
Dates below are the last commit touching the file.

## Result

81 of 83 stay. 2 deleted (zero references, evidence in §3):

- `messung/gabbrov/ziehung.py`
- `messung/gegenrechnung/rumpflaengen.py`

## Table

Columns: script | last commit | refs (n, self excluded) | who references it | verdict.
Doc citations beyond 8 are counted, not listed (`+N docs`); code callers are
always listed in full.

| script | last | n | who | verdict |
|---|---|---|---|---|
| instrumente/abnahme.py | 2026-09-01 | 65 | called by: pruefe-emission.sh, pruefe-sonden.sh, mutiere-pruefer.py, miss-erschoepfung.py, 30+ pruefe-/zaehle-*.py; cited by CLAUDE.md, README.md, TODO.md, DONE.md, crates/gabbro-cli (bau.rs, tests/bausystem.rs), dokumente (7), messung (20+) | STAY (acceptance runner) |
| instrumente/abschnitt.py | 2026-08-31 | 29 | imported by abnahme.py, mutiere-pruefer.py, 20+ pruefe-/zaehle-*.py; called by abschnitt.sh; cited by WERKZEUGKASTEN.md, RUECKLAUFWERTE.md, VORRICHTUNGEN.md, PLAN-ENGLISCH.md | STAY (shared cut notice) |
| instrumente/erzeuge-mutationen.py | 2026-08-31 | 7 | called by mutiere-pruefer.py, pruefe-waechter.py; cited by TODO.md, DONE.md, WERKZEUGKASTEN.md, RUECKLAUFWERTE.md, VORRICHTUNGEN.md | STAY |
| instrumente/fuzze-erzeuger.py | 2026-09-03 | 31 | called by fuzze-grenzen.py, pruefe-emission.sh, pruefe-waechter.py; cited by 7 gift probes, crates (emit.rs, umgebung.rs, tests/rechenwerk.rs), TODO.md, DONE.md, +12 docs | STAY |
| instrumente/fuzze-grenzen.py | 2026-09-03 | 26 | called by fuzze-erzeuger.py, pruefe-waechter.py; cited by 4 gift probes, crates (emit.rs, m1.rs, namen.rs, tests korpus/paesse/rechenwerk.rs), TODO.md, DONE.md, +9 docs | STAY |
| instrumente/korpus.py | 2026-09-04 | 1+stem | basename cited by messung/WORTSTELLUNG.md:219,246; stem `import korpus` in miss-c-signaturen.py:38, pruefe-kennungen.py:29, pruefe-saetze.py:46 (plus sondendeckung/unfalsifizierbar/vergleiche per their own refs) | STAY (shared tracked-file filter) |
| instrumente/leite-grammatik.py | 2026-09-07 | 4 | called by miss-grammatikdeckung.py; cited by GRAMMATIK-AUS-DEM-CODE-2026-09-07.md, MUSE-REPORT-60.md, MUSE-REPORT-88.md | STAY |
| instrumente/miss-c-signaturen.py | 2026-09-04 | 13 | called by pruefe-waechter.py, pruefe-zitate.py, korpus.py; cited by 3 gift probes, crates (cnamen.rs, namen.rs, saetze.rs), PLAN-HARDWARE.md, WERKZEUGKASTEN.md, VORRICHTUNGEN.md, probe-c-namen-frei.gab | STAY |
| instrumente/miss-erschoepfung.py | 2026-09-01 | 5 | called by miss-c-signaturen.py; cited by gift/593-cost-of-a-call-in-an-index.gab, crates (kosten.rs, tests/paesse.rs), VORRICHTUNGEN.md | STAY |
| instrumente/miss-grammatikdeckung.py | 2026-09-12 | 3 | cited by GRAMMATIK-AUS-DEM-CODE-2026-09-07.md, MUSE-REPORT-60.md, MUSE-REPORT-88.md | STAY (cited as command) |
| instrumente/miss-lean-gegen-isabelle.py | 2026-09-02 | 2 | cited by LEAN-REICHWEITE.md, gabbrov/MANIFEST-COMPLETENESS.md | STAY |
| instrumente/miss-lean-reichweite.py | 2026-09-02 | 2 | cited by LEAN-REICHWEITE.md, gabbrov/MANIFEST-COMPLETENESS.md | STAY |
| instrumente/miss-lean-traeger.py | 2026-09-02 | 1 | cited by LEAN-REICHWEITE.md | STAY |
| instrumente/miss-zeremoniedifferenz.py | 2026-09-07 | 1 | cited by KLEMPNEREI-2026-09-07.md | STAY |
| instrumente/mutiere-pruefer.py | 2026-09-10 | 60+ | called by abnahme.py, pruefe-waechter.py, pruefe-luecken.py, pruefe-zahlen.py +8; cited by CLAUDE.md, commit.sh, TODO.md, DONE.md, README.md, crates (6), beweise/Table_Indexschranke.thy, +30 docs | STAY (mutation runner) |
| instrumente/nachpruefer.py | 2026-09-11 | 4 | cited by grammatik/Grammatik/Erhaltung.lean, KOSTEN-LEDGER.md, WAECHTER-STUFE0.md, MUSE-REPORT-67.md | STAY |
| instrumente/pruefe-abstieg.py | 2026-09-10 | 19 | run by abnahme.py; called by pruefe-reichweite.py; cited by crates (emit.rs, namen.rs, pflichten.rs, tests/rechenwerk.rs), TODO.md, DONE.md, PLAN-AUTONOM.md, PLAN.md, WERKZEUGKASTEN.md, +7 docs | STAY (guardian) |
| instrumente/pruefe-aufloesung.py | 2026-09-01 | 8 | run by abnahme.py; cited by TODO.md, DONE.md, PLAN-AUTONOM.md, ABNAHME-VOLL.md, AUFLOESUNG-BEZUGSGROESSE.md, RUECKLAUFWERTE.md, VORRICHTUNGEN.md | STAY (guardian) |
| instrumente/pruefe-ausnahmen.py | 2026-09-03 | 3 | called by pruefe-zahlen.py (register entry); cited by AUSNAHMEN.md, UNFALSIFIZIERBAR.md, GABBROV-AUFTRAG.md | STAY (guardian) |
| instrumente/pruefe-deckung.py | 2026-09-08 | 9 | cited by crates/gabbro-check/src/lean.rs, PLAN-UMSETZUNG.md, GRAMMATIK-VOLLSTAENDIG-2026-09-08.md, PORT-PFLICHT.md, WAECHTER-STUFE0.md, MUSE-REPORT-64.md, MUSE-REPORT-75.md, programmlogik/Gabbro/Coverage.lean, programmlogik/PLAN.md | STAY (guardian) |
| instrumente/pruefe-englisch.py | 2026-09-12 | 60+ | run by abnahme.py; called by pruefe-zahlen.py (2 register entries), pruefe-umwandlungen.py; cited by TODO.md, DONE.md, README.md, crates (saetze.rs, tests/fahnen.rs), +40 docs | STAY (guardian) |
| instrumente/pruefe-gestalt.py | 2026-09-11 | 3 | cited by WAECHTER-STUFE0.md, MUSE-REPORT-67.md, MUSE-REPORT-75.md | STAY (guardian) |
| instrumente/pruefe-grammatiktafel.py | 2026-09-10 | 40+ | run by abnahme.py; called by pruefe-emission.sh, pruefe-waechter.py, zaehle-absagen.py, zaehle-empfindlichkeit.py; cited by TODO.md, DONE.md, SYNTAX.md, PLAN-*.md, +25 docs | STAY (guardian) |
| instrumente/pruefe-gruende.py | 2026-09-01 | 19 | called by pruefe-zahlen.py (3 register entries); cited by TODO.md, HISTORIE.md, MESSUNGEN.md, WERKZEUGKASTEN.md, crates (domaene.rs, m1.rs), +10 docs | STAY (guardian) |
| instrumente/pruefe-kennungen.py | 2026-09-04 | 40+ | run by abnahme.py; called by pruefe-zahlen.py, pruefe-todo.py; cited by TODO.md, DONE.md, crates (6), +25 docs | STAY (guardian) |
| instrumente/pruefe-klauseln.py | 2026-09-12 | 40+ | called by pruefe-zahlen.py, pruefe-konstrukte.py; cited by 12 gift probes, crates (9), TODO.md, README.md, +15 docs | STAY (guardian) |
| instrumente/pruefe-konstrukte.py | 2026-08-31 | 19 | run by abnahme.py; called by pruefe-zahlen.py, pruefe-klauseln.py, pruefe-reichweite.py; cited by 5 gift probes, crates (namen.rs, tests/korpus.rs), +10 docs | STAY (guardian) |
| instrumente/pruefe-luecken.py | 2026-09-02 | 17 | run by abnahme.py (SCHWER); called by pruefe-waechter.py, pruefe-umwandlungen.py; cited by CLAUDE.md, TODO.md, DONE.md, PLAN-AUTONOM.md, PLAN.md, WERKZEUGKASTEN.md, +6 docs | STAY (guardian) |
| instrumente/pruefe-manifest.py | 2026-09-04 | 10 | called by pruefe-sondendeckung.py, zaehle-p6.py; cited by crates/pflichten.rs, OFFEN.md, +7 docs | STAY (guardian) |
| instrumente/pruefe-notation.py | 2026-09-04 | 14 | called by pruefe-waechter.py; cited by TODO.md, DONE.md, MESSUNGEN.md, PFLICHTEN.md, PLAN.md, WERKZEUGKASTEN.md, +8 docs | STAY (guardian) |
| instrumente/pruefe-praemisse.py | 2026-09-12 | 9 | cited by PRAEMISSEN-PROBE.md, muse-audit/46 fixtures (2), MUSE-REPORT-106/18/46/53/58/61.md | STAY (guardian) |
| instrumente/pruefe-reichweite.py | 2026-09-02 | 13 | run by abnahme.py; cited by TODO.md, DONE.md, gift/203, crates (blindstellen.rs, namen.rs, tests/korpus.rs), HISTORIE.md, PLAN-AUTONOM.md, +5 docs | STAY (guardian) |
| instrumente/pruefe-saetze.py | 2026-09-12 | 30+ | called by pruefe-zahlen.py (2 register entries); cited by CLAUDE.md, TODO.md, DONE.md, README.md, crates (lib.rs, saetze.rs, bau.rs), PLAN-AUTONOM.md, +20 docs | STAY (guardian) |
| instrumente/pruefe-schablonen.py | 2026-09-01 | 14 | called by pruefe-zahlen.py; cited by TODO.md, crates (main.rs), PLAN-AUTONOM.md, +10 docs | STAY (guardian) |
| instrumente/pruefe-sondendeckung.py | 2026-09-12 | 17 | called by pruefe-zahlen.py (4 register entries), pruefe-emission.sh, pruefe-sonden.sh; cited by CLAUDE.md, DONE.md, PLAN.md, SONDENDECKUNG.md, korpus.py, +9 docs | STAY (guardian) |
| instrumente/pruefe-todo.py | 2026-09-12 | 40+ | run by abnahme.py; called by pruefe-zahlen.py, pruefe-kennungen.py, pruefe-waechter.py; cited by CLAUDE.md, TODO.md, DONE.md, README.md, +25 docs | STAY (guardian) |
| instrumente/pruefe-uebersetzerfamilie.py | 2026-09-04 | 13 | called by pruefe-emission.sh, pruefe-zahlen.py; cited by BERICHT-UEBERSETZERFAMILIE.md, UEBERSETZUNGSREICHWEITE.md, +9 docs | STAY (guardian) |
| instrumente/pruefe-umwandlungen.py | 2026-09-01 | 4 | called by pruefe-englisch.py, pruefe-waechter.py, pruefe-luecken.py; cited by ERZEUGERREST.md, VORRICHTUNGEN.md | STAY (guardian) |
| instrumente/pruefe-unfalsifizierbar.py | 2026-09-04 | 11 | called by pruefe-zahlen.py (2 register entries), pruefe-emission.sh, pruefe-sondendeckung.py; cited by DONE.md, PLAN.md, SONDENDECKUNG.md, UNFALSIFIZIERBAR.md, korpus.py, +4 docs | STAY (guardian) |
| instrumente/pruefe-vergabe.py | 2026-09-03 | 26 | run by abnahme.py; called by pruefe-zahlen.py, pruefe-waechter.py, pruefe-zitate.py; cited by TODO.md, 3 gift probes, crates (m1.rs, namen.rs, parse.rs), PLAN-AUTONOM.md, +15 docs | STAY (guardian) |
| instrumente/pruefe-waechter.py | 2026-09-02 | 40+ | imported by abnahme.py; called by pruefe-zahlen.py (2 register entries); cited by TODO.md, DONE.md, README.md, crates/main.rs, PLAN-*.md, +25 docs | STAY (guardian registry) |
| instrumente/pruefe-widerruf.py | 2026-09-03 | 28 | run by abnahme.py; called by pruefe-zahlen.py (2 register entries); cited by TODO.md, DONE.md, README.md, crates/main.rs, +20 docs | STAY (guardian) |
| instrumente/pruefe-wortschatz.py | 2026-09-12 | 40+ | run by abnahme.py; called by pruefe-waechter.py, pruefe-syntax.sh; cited by TODO.md, DONE.md, crates (saetze.rs, schablonen.rs, tests/wortschatz.rs), SYNTAX.md, PLAN-*.md, +25 docs | STAY (guardian) |
| instrumente/pruefe-zahlen.py | 2026-09-12 | 40+ | cited by CLAUDE.md, TODO.md, DONE.md, crates (pflichten.rs, umgebung.rs, tests beispiele/paesse.rs), PLAN-*.md, +30 docs | STAY (guardian) |
| instrumente/pruefe-zitate.py | 2026-09-10 | 11 | called by pruefe-englisch.py, pruefe-umwandlungen.py, pruefe-vergabe.py, miss-c-signaturen.py; cited by TODO.md, PLAN-AUTONOM.md, +6 docs | STAY (guardian) |
| instrumente/vergleiche-binaerprogramme.py | 2026-09-04 | 6 | called by pruefe-waechter.py, korpus.py; cited by crates/tests/hinweise.rs, PLAN-UMSETZUNG.md, AUDIT-K100-2026-09-04.md, EINHEITENSICHT.md, VORRICHTUNGEN.md | STAY |
| instrumente/zaehle-absagen.py | 2026-09-04 | 12 | called by pruefe-grammatiktafel.py, zaehle-c-formen.py, zaehle-empfindlichkeit.py, zaehle-gifttreffer.py; cited by TODO.md, ABSAGEFORMEN.md, GRAMMATIKTAFEL.md, REICHWEITE-DER-REGEL.md, ABNAHME-VOLL.md, +5 docs | STAY (counter, in abnahme.py) |
| instrumente/zaehle-b3.py | 2026-09-04 | 13 | run by abnahme.py; called by pruefe-kennungen.py, pruefe-waechter.py, zaehle-absagen.py; cited by TODO.md, DONE.md, MESSUNGEN.md, WERKZEUGKASTEN.md, +7 docs | STAY |
| instrumente/zaehle-bereichspflichten.py | 2026-09-02 | 11 | called by pruefe-waechter.py, pruefe-zahlen.py; cited by TODO.md, DONE.md, FRAGMENTE.md, MESSUNGEN.md, PLAN.md, WERKZEUGKASTEN.md, +4 docs | STAY |
| instrumente/zaehle-bloecke.py | 2026-09-01 | 3 | cited by ABNAHME-VOLL.md, PROBENZWEIGE.md, VORRICHTUNGEN.md as the command | STAY |
| instrumente/zaehle-c-formen.py | 2026-09-12 | 40+ | called by pruefe-waechter.py, pruefe-zahlen.py, fuzze-erzeuger.py; cited by TODO.md, DONE.md, crates/emit.rs, BEWEIS.md, OFFEN.md, PLAN-BITS.md, PLAN-HARDWARE.md, Erhaltung.lean, +25 docs | STAY |
| instrumente/zaehle-empfindlichkeit.py | 2026-08-31 | 5 | called by pruefe-waechter.py, zaehle-absagen.py; cited by PLAN.md, ABNAHME-VOLL.md, PROBENZWEIGE.md, VORRICHTUNGEN.md | STAY |
| instrumente/zaehle-formate.py | 2026-08-31 | 5 | called by pruefe-zahlen.py (3 register entries: TODO.md `@version` figures); cited by TODO.md, WERKZEUGKASTEN.md, ABNAHME-VOLL.md, VORRICHTUNGEN.md | STAY |
| instrumente/zaehle-fragmente.py | 2026-09-01 | 12 | called by pruefe-zahlen.py (2 register entries: fragmente/README.md figures), pruefe-emission.sh, zaehle-absagen.py; cited by TODO.md, PLAN-HARDWARE.md, PFLICHTEN.md, PLAN.md, +6 docs | STAY |
| instrumente/zaehle-fremdpflichten.py | 2026-08-31 | 4 | cited by TODO.md, ABNAHME-VOLL.md, FREMDPFLICHTEN.md, VORRICHTUNGEN.md | STAY |
| instrumente/zaehle-fremdverengung.py | 2026-08-31 | 7 | called by pruefe-zahlen.py (2 register entries); cited by TODO.md, zaehle-fremdpflichten.py, ABNAHME-VOLL.md, FREMDPFLICHTEN.md, FREMDVERENGUNG.md, VORRICHTUNGEN.md | STAY |
| instrumente/zaehle-gifttreffer.py | 2026-09-02 | 21 | called by pruefe-emission.sh; cited by gift/411, crates/main.rs, +18 docs | STAY |
| instrumente/zaehle-karten.py | 2026-09-03 | 26 | run by abnahme.py; called by pruefe-zahlen.py (2 register entries), pruefe-waechter.py, zaehle-narrow.py; cited by TODO.md, crates (domaene.rs, emit.rs, umgebung.rs), +18 docs | STAY |
| instrumente/zaehle-lean.py | 2026-09-08 | 20 | called by pruefe-lean-beweis.sh, miss-lean-reichweite.py, pruefe-deckung.py; cited by crates (lean.rs, pflichten.rs), MESSUNGEN.md, PLAN-*.md, LEAN-REICHWEITE.md, +10 docs | STAY |
| instrumente/zaehle-narrow.py | 2026-09-04 | 10 | called by pruefe-waechter.py, zaehle-karten.py; cited by TODO.md, MESSUNGEN.md, WERKZEUGKASTEN.md, +6 docs | STAY |
| instrumente/zaehle-netz.py | 2026-09-01 | 5 | called by pruefe-zahlen.py (netz/README.md figure); cited by TODO.md, ABNAHME-VOLL.md, VORRICHTUNGEN.md, netz/README.md | STAY |
| instrumente/zaehle-p6.py | 2026-09-02 | 13 | called by mutiere-pruefer.py, pruefe-manifest.py, pruefe-p6-beweis.sh; cited by TODO.md, crates (lean.rs, pflichten.rs), +8 docs | STAY |
| instrumente/zaehle-pflichten.py | 2026-09-10 | 40+ | called by pruefe-zahlen.py (12 register entries), pruefe-emission.sh, pruefe-manifest.py, pruefe-notation.py, pruefe-todo.py, pruefe-waechter.py, zaehle-fragmente.py; cited by TODO.md, DONE.md, PFLICHTEN.md, GABBROV.md, +25 docs | STAY |
| instrumente/zaehle-probenzweige.py | 2026-09-02 | 7 | run by abnahme.py; called by pruefe-waechter.py, zaehle-verdrahtung.py; cited by TODO.md, ABNAHME-STELLEN.md, PROBENZWEIGE.md, UNTERE-GRENZE.md, VORRICHTUNGEN.md | STAY |
| instrumente/zaehle-theorien.py | 2026-08-31 | 10 | called by pruefe-zahlen.py (3 register entries); cited by TODO.md, beweise/Table_Zaehlung.thy, crates/schablonen.rs, MESSUNGEN.md, +5 docs | STAY |
| instrumente/zaehle-traversierungen.py | 2026-09-02 | 4 | called by pruefe-zahlen.py (2 register entries: TODO.md traversal figures), zaehle-zeremonie.py; cited by TODO.md, ABNAHME-VOLL.md, VORRICHTUNGEN.md | STAY |
| instrumente/zaehle-verdrahtung.py | 2026-08-31 | 7 | called by pruefe-klauseln.py, zaehle-probenzweige.py, zaehle-wortschatz.py; cited by TODO.md, crates (kontexte.rs, saetze.rs), PLAN.md, ANNAHMEKONJUNKTIONEN.md, VORRICHTUNGEN.md | STAY |
| instrumente/zaehle-wortschatz.py | 2026-09-12 | 30+ | called by pruefe-waechter.py, pruefe-englisch.py, zaehle-verdrahtung.py; cited by DONE.md, crates (ast.rs, kw.rs, tests/wortschatz.rs), SYNTAX.md, PLAN-*.md, +20 docs | STAY |
| instrumente/zaehle-zeremonie.py | 2026-09-01 | 9 | called by pruefe-zahlen.py (6 register entries: README.md/ZEREMONIE.md figures), miss-zeremoniedifferenz.py, zaehle-traversierungen.py; cited by TODO.md, README.md, SCHREIBLAST-EFFECTS.md, ABNAHME-VOLL.md, ZEREMONIE.md, VORRICHTUNGEN.md | STAY |
| messung/gabbrov/cert-theorien.py | 2026-09-10 | 1 | cited by messung/gabbrov/GABBROV-ZERTIFIKAT.md as the producing command | STAY |
| messung/gabbrov/erzeuge-L05.py | 2026-09-03 | 3 | called by messung/gabbrov/lauf-L05.sh and ohne-schranke/lauf.sh; cited by GABBROV-AUFTRAG.md | STAY |
| messung/gabbrov/ohne-schranke/gen-probe.py | 2026-09-03 | 2 | called by ohne-schranke/lauf.sh; cited by GABBROV-AUDIT.md | STAY |
| messung/gabbrov/ohne-schranke/gen-rank.py | 2026-09-03 | 2 | called by ohne-schranke/lauf.sh; cited by GABBROV-AUDIT.md | STAY |
| messung/gabbrov/ratschenschluessel.py | 2026-09-03 | 3 | called by pruefe-waechter.py (lauf-L05.sh context); cited by GABBROV.md, OFFEN.md, BERICHT-O3-RATSCHE.md | STAY |
| messung/gabbrov/ziehung.py | 2026-09-03 | 0 | NOBODY. Stem grep `ziehung` hits only the German word `Beziehung` (unrelated). GABBROV-AUFTRAG.md §2.1 records the draw (seed, algorithm, THE FIVE) WITHOUT naming the script. | DELETE (§3) |
| messung/gegenrechnung/audit-umfang.py | 2026-08-28 | 1 | cited by messung/GEGENRECHNUNG.md | STAY |
| messung/gegenrechnung/klassentabelle.py | 2026-08-28 | 1 | cited by messung/GEGENRECHNUNG.md | STAY |
| messung/gegenrechnung/rumpflaengen.py | 2026-08-28 | 0 | NOBODY. Stem grep `rumpflaengen` hits nothing. Analyzes a foreign `kernel/src/...` tree that is not in this repository. | DELETE (§3) |
| messung/gegenrechnung/schleifen.py | 2026-08-28 | 1 | cited by messung/GEGENRECHNUNG.md | STAY |
| messung/gegenrechnung/spez-gegen-beweis.py | 2026-08-28 | 1 | cited by messung/GEGENRECHNUNG.md | STAY |
| messung/gegenrechnung/vier-toepfe.py | 2026-08-28 | 2 | cited by messung/BAUGATTER.md, messung/GEGENRECHNUNG.md | STAY |
| messung/ordnung/tore.py | 2026-08-28 | 3 | cited by crates/gabbro-check/src/saetze.rs (comment), WERKZEUGKASTEN.md, ORDNUNGSFINDER.md | STAY |
| messung/ordnung/ungeordnet.py | 2026-08-28 | 1 | cited by messung/ORDNUNGSFINDER.md | STAY |

## 3. Deletion evidence (the only two files with zero references)

### 3a. `messung/gabbrov/ziehung.py` (57 lines, last touched 2026-09-03)

One-off blind-draw script for `GABBROV-AUFTRAG.md` §3 (Gate 2, mandate says stop).

```sh
git grep -l --fixed-strings "ziehung.py" -- .        # -> only itself
git grep -n "ziehung" -- . | grep -v Beziehung        # -> nothing (all hits are Beziehung)
```

- Hardcodes a dead agent worktree as its input root:
  `W = Path("/home/simon/Dokumente/Gabbro/.claude/worktrees/agent-abde0442a4bb8e45c")`
  (does not exist on this machine; the script cannot run here).
- The draw it produced is recorded VERBATIM in `GABBROV-AUFTRAG.md` §2.1/§9
  (seed `b15ef79`, hash order, `THE FIVE: L01 L05 L23 L39 L40`) WITHOUT naming the
  script — the record is self-contained (public seed + stated algorithm + input
  `programmlogik/gabbrov/V1.lean`, still in the tree). Deleting the instrument does
  not delete the evidence. Flagged as the riskier of the two deletions; it is one
  commit and reverts cleanly.

### 3b. `messung/gegenrechnung/rumpflaengen.py` (39 lines, last touched 2026-08-28)

```sh
git grep -l --fixed-strings "rumpflaengen.py" -- .   # -> only itself
git grep -n "rumpflaengen" -- .                       # -> only itself
```

- Analyzes function-body lengths of a FOREIGN tree (`kernel/src/threads/...`,
  `WHOLE` set, German stdout) that is not in this repository (`ls kernel` -> nothing).
- Oldest script in the census (2026-08-28); no caller, no citation, no register entry.

## 4. Root and directory decisions (same lane, same evidence rule)

Root keep-list (per task): README.md, LICENSE, LIZENZ-ZUSATZ.md, CLAUDE.md,
TUTORIAL.md, TODO.md, DONE.md, Cargo.toml, Cargo.lock, commit.sh, .gitignore.
(`cargo-pruef`, `lean-bau`, `lean-probe`, `emission-pruef`, `.tmp/` are NOT tracked —
they live in `.git/info/exclude` — so they are outside this cleanup.)

| path | references | decision |
|---|---|---|
| `fallen-klassifikation.tsv` | live: `instrumente/zaehle-fallen.sh` (`D=...`), `dokumente/PLAN.md:80` + `dokumente/WERKZEUGKASTEN.md:8` (relative links `../fallen-klassifikation.tsv`); prose: `ABNAHME-VOLL.md:418`, `VORRICHTUNGEN.md:173` | MOVE to `messung/fallen-klassifikation.tsv`, fix script path + 2 links |
| `halde.gab` | live: `pruefe-emission.sh` `MARKE_EMIT_X=1` (stage 9 `*)` bucket); historical: `ABNAHME-STELLEN.md:91-94`, `REICHWEITE-DER-REGEL.md:41,213`, `WILDCARD-ZWEIGE.md:5`, 3 `.gab` comments (basename-stable, untouched) | MOVE to `beispiele/halde.gab` (checker-clean: `pruefe` 0 errors 0 hints, zeugnis has no UNZUGEORDNET); fix `MARKE_EMIT` 75→77 and `MARKE_EMIT_X` 1→0 with decomposed comments |
| `Claude outputs/` (15 files) | live: NONE (`git grep "Claude outputs/"` -> only 3 historical doc mentions: `GRAMMATIK-VOLLSTAENDIG-2026-09-08.md:14` quotes `PLAN.md`, `MUSE-REPORT-75/87.md` note the stray); counted: stage-9 `*)` bucket (7 of its 8 `.gab` emit; baseline `NEUE WURZEL ... 8 statt 1`) | DELETE all 15, fix `MARKE_EMIT_X` (see above) |
| `messungen/` (15 files) | live: `MARKE_EMIT_N=2`, `REICHWEITE-DER-REGEL.md`, `GRAMMATIKTAFEL.md`, `zaehle-formate.py` glob, `fahnen.rs` word list | STAY (measurement tree with ratchets) |
| `sonden/` (20 files) | live: `SONDEN_MIT_PROGRAMM` (manifest.rs), `pruefe-sonden.sh`, `SONDENDECKUNG.md`, `SYNTAX.md`, Lean `Ziel.lean` | STAY (probe source tree) |
| `passlogik/` (14 files) | live: `PLAN-SICHERHEIT.md` (137 theorems), `programmlogik/Gabbro/*.lean`, `INSTALLATION.md` | STAY (Lean source tree) |

Historical records (dated measurement logs) are NOT rewritten: their quotes were true
at measurement time. Only live links/paths/marks are fixed.
