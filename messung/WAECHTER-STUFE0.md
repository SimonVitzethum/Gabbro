# Watcher stage 0: bilingual patterns first, cell moves booked

Status: PROPOSAL ONLY for every cell below, RECORD for every fix above.
No cell in any watched document has been changed. No source file has been changed.
Base: `ebeb27e4` on branch `n02-waechterstufe0`, worktree `.claude/worktrees/n02`, clean tree.
Measured: 2026-09-12. Local only, `free -g` beside the run (31 GB total, 6 available).
All prose in this file is English. Quoted lines below are VERBATIM copies of the
current document text (quoting is not rephrasing); they are shown only so the
proposed edit is exact. Same proposal format as `messung/ZAHLEN-ABGLEICH.md`.

## 1. Guardian results

| Guardian | Before | After | Verdict now |
|---|---|---|---|
| `instrumente/pruefe-todo.py` | exit 2, ABORT in its own speech test | exit 1, measures | 4 genuine findings (§4: P17–P19) |
| `instrumente/pruefe-todo.py --probe` | exit 2 | exit 0 | ALL probe directions hold |
| `instrumente/pruefe-klauseln.py` | exit 1, stale table (`version` risen) | exit 0 | ALL PASS, 12 booked, none new |
| `instrumente/pruefe-zahlen.py` | exit 1, 90 of 91 recomputed, 1 dead search path | exit 1, 91 of 91 recomputed | 17 stale numbers (§4: P01–P16) |
| `instrumente/pruefe-englisch.py` | exit 1, sink hit invisible | exit 1, sink hit printed | 4 broken ratchets, all attributed (§6) |
| `instrumente/pruefe-kennungen.py` | exit 0 | exit 0 | ALL PASS, 303 issued |
| `instrumente/pruefe-syntax.sh` | exit 0 | exit 0 | ALL PASS (161 rules, 221 terminals) |
| `instrumente/pruefe-sondendeckung.py` | exit 0 | exit 0 | ALL PASS (17 of 50) |
| `instrumente/pruefe-widerruf.py` | exit 0 | exit 0 | ALL PASS (13 entries) |
| `instrumente/pruefe-grammatiktafel.py` | exit 0 | exit 0 | GREEN (0 of 221 uncovered) |
| `instrumente/pruefe-waechter.py` | exit 1 | exit 1 | 3 open partial measurements (§6) |

Evidence: full logs of the runs in sections 2–3 are the measurement record
(`/tmp/opencode/n02-*.log` during the session; reproduce with the commands named
per finding). `cargo run` based entries needed no build: `target/debug/gabbro`
in this worktree is newer than the sources.

## 2. Fixed instruments (behavior before/after)

### F1 — `pruefe-todo.py`: the speech test graded invented lists against a live file

- Expectation: the clean template yields 0 findings in both languages.
- Tree fact: `DONE.md:1562` books `500 poison probes`, the corpus holds 549
  (`ls beispiele/gift/*.gab`). Rule 8 read the LIVE `DONE.md` even for invented
  templates, so the clean half reported 1 finding and the guardian aborted with
  exit 2 — over its own subject, not over `TODO.md`.
- Fix (`instrumente/pruefe-todo.py`): `pruefe()` takes `done_text=None`; `None`
  reads the live file (real run unchanged), the speech test passes an invented
  clean text (`_leere_done()`, counts derived, never typed). Before: clean list
  1 finding (`DONE.md: '500 Giftproben' -- es sind 549`), EN-clean 1, EN-labels
  1 of them right — three red directions from one stale file. After: gift 5/5,
  clean 0/0, EN-gift 5, EN-clean 0, EN-labels 3 wrong + 0 right — every direction
  holds, thresholds (`>= 5`, `>= 3`) met exactly, not loosely.
- The stale `500` itself is NOT fixed here: it is P19/P20 below.

### F2 — `pruefe-klauseln.py`: `version` never rose, a ledger field did

- Expectation: the booked table holds; a risen row means a pass reads the clause.
- Tree fact: the only `.version` accesses in checker sources are
  `crates/gabbro-check/src/kostenledger.rs:226,229,456`, all on `Ledger`
  (`pub version: u32`, the ledger format version, `kostenledger.rs:198`). The
  AST clause is `Format.version: Option<u128>` (`ast.rs:1599`, the `@version`
  of a format declaration). Different struct, different type, same field name —
  the `kosten` trap of 2026-08-28 in this tool's own header, one field over.
  No pass names `Format` at all. The verdict `Eintrag loeschen` was wrong.
- Fix (`instrumente/pruefe-klauseln.py`, `HOMONYME`): `version` booked against
  `Ledger` for `kostenledger.rs`, with the reason. The booking bites by
  construction: the self-test falls if the access leaves the booked file.
  Before: exit 1, class table never printed. After: exit 0,
  `ZUSAGE 0` printed — which restores the number guardian's P10 search path
  (`dokumente/PLAN.md:3464` books **0**): `pruefe-zahlen.py` went from 90 of 91
  recomputed with one dead path to 91 of 91, and the dead-path finding is gone.
- Side effect, measured: the `91 vs 90` finding `pruefe-todo.py` reported before
  F2 is gone as well — it was an artifact of the dead path, not a stale cell,
  and is therefore booked nowhere.

### F3 — `pruefe-englisch.py`: the red path hid its own evidence

- Expectation: a red guardian says WHERE (W17, this file's own feeder half).
- Tree fact: the German sink hits printed only BELOW the ratchet verdicts, so a
  broken comment ratchet (exit 1 above) hid the one German sink message. The
  feeders printed only their last eight.
- Fix (`instrumente/pruefe-englisch.py`): all sink hits and all feeder hits
  print BEFORE the verdicts; the verdict paragraphs point upward instead of
  re-printing. Green path byte-identical (no hits, ALL PASS branch untouched).
  All twelve speech-test directions still hold (section `== Sprechprobe ==`
  through the comment test, all `ja`).

### F4 — `pruefe-zahlen.py`: 36 document labels bilingual, documents untouched

- Expectation (repo rule since 2026-08-31): patterns go bilingual BEFORE the
  document moves, or the first translation turns four guardians silently blind.
- Tree fact: 37 of 91 entries matched German-bound text; 36 of their patterns
  were German-only (the 37th, the netz probe pair, already carried both).
- Fix (`instrumente/pruefe-zahlen.py`, `EINTRAEGE` only, plus one header note):
  each of the 36 patterns carries an English alternative beside the German
  label — drafted, not quoted; the translator picks the wording on moving day.
  Exactly one capturing group per pattern before and after (group 1 stays the
  figure; checked mechanically over all 91 entries).
- Proof: 36 invented English lines, one per entry, each matched with the right
  figure in group 1 (36/36); the full guardian run after the change recomputes
  91 of 91 with no new `UNBEWACHT` and the same 17 stale-number findings; the
  multi-hit list stands at the same 3 entries as before.
- The `Sprachbindung` tail still reads 37 of 91 (29 in prose, 8 in blocks):
  the DOCUMENTS have not moved, which is the point — the patterns are ready,
  the cells are booked in section 4.
- Already bilingual, verified this run, needed nothing: `pruefe-widerruf.py`
  (speech test demands every entry fall in German AND English, 26 of 26),
  `pruefe-todo.py` (templates plus label probes in both languages),
  `pruefe-wortschatz.py` (read twice, second time with English row labels),
  `pruefe-sondendeckung.py` (keys on structural identifiers — `falsifier`,
  class names, program names — language-neutral by construction),
  `pruefe-grammatiktafel.py` (loads the bilingual `wortschatz` reader),
  `pruefe-klauseln.py` / `-deckung.py` / `-gestalt.py` (no German-word pattern
  over document text; checked mechanically).

## 3. Proposed cell edits (one per finding)

Convention: proposals follow the strikethrough-history style of the surrounding
lines (`~~old~~ new`), except in `messung/PASSREGISTER.md`, whose table keeps no
history. Each proposal gives file, line, the registered recomputation command,
the measured output, and an exact old/new pair. Only the guarded figure moves;
unguarded neighbours are listed in section 5.

### P01 — guardians that can abort mid-run (`messung/RUECKLAUFWERTE.md:232`)

- Register label (verbatim): `Waechter, die mitten im Lauf abbrechen koennen`
- Command: `./instrumente/pruefe-waechter.py`, pattern on its mid-run line.
- Measured: stands as 60, run says 61 (`== Ein Abbruch MITTEN im Lauf: 61 von 66`).

```diff
--- a/messung/RUECKLAUFWERTE.md	(line 232)
+++ b/messung/RUECKLAUFWERTE.md	(proposed)
@@
-~~59 von 64~~ **60 von 65** Wächtern können mitten im Lauf
+~~59 von 64~~ ~~60 von 65~~ **61 von 65** Wächtern können mitten im Lauf
```

Note: the denominator stands open in the pattern by decision (2026-09-01) and is
unguarded; the run says 66. Carried by hand, like the last nine moves.

### P02 — exit sites behind the first (`messung/RUECKLAUFWERTE.md:234`)

- Register label (verbatim): `Ausgangsstellen hinter dem jeweils ersten -- die Schnittflaeche`
- Command: `./instrumente/pruefe-waechter.py`, pattern on its exit-site line.
- Measured: stands as 369, run says 373.

```diff
--- a/messung/RUECKLAUFWERTE.md	(line 234)
+++ b/messung/RUECKLAUFWERTE.md	(proposed)
@@
-~~357~~ ~~365~~ **369 Ausgangsstellen** liegen hinter dem jeweils ersten. Abgelesen mit
+~~357~~ ~~365~~ ~~369~~ **373 Ausgangsstellen** liegen hinter dem jeweils ersten. Abgelesen mit
```

### P03 — source comment lines (`TODO.md:3992`)

- Register label (verbatim): `deutsche Kommentarzeilen im Pruefer -- die Ratsche der Uebersetzung`
- Command: `./instrumente/pruefe-englisch.py`, pattern on its `Quellsprache` line.
- Measured: stands as 7892, run says 7904 (`== Quellsprache: 7904 von 29667`).

```diff
--- a/TODO.md	(line 3992)
+++ b/TODO.md	(proposed)
@@
-~~7881~~ ~~7883~~ ~~7891~~ **7892 von 27237 Kommentarzeilen** im Pruefer sind deutsch
+~~7881~~ ~~7883~~ ~~7891~~ ~~7892~~ **7904 von 27237 Kommentarzeilen** im Pruefer sind deutsch
```

Note: the denominator (27237 vs 29667 measured) is unguarded prose, untouched.

### P04 — samples on an ambiguous identifier (`TODO.md:4165`)

- Register label (verbatim): `Giftproben auf einer mehrdeutigen Kennung`
- Command: `./instrumente/pruefe-vergabe.py`, pattern on its cost line.
- Measured: stands as 73, run says 75 (`== Was das RUECKWIRKEND kostet: 75 von 539`).

```diff
--- a/TODO.md	(line 4165)
+++ b/TODO.md	(proposed)
@@
-      ~~68~~ ~~70~~ ~~71~~ 73 Proben zeigen auf eine Kennung mit unaehnlichen Vergabestellen (von 440
+      ~~68~~ ~~70~~ ~~71~~ ~~73~~ 75 Proben zeigen auf eine Kennung mit unaehnlichen Vergabestellen (von 440
```

Note: the parenthetical denominator (440 vs 539 measured) is unguarded, untouched.

### P05 — sentences in the pass register (`messung/PASSREGISTER.md:19`)

- Register label (verbatim): `Saetze im Passregister`
- Command: `./instrumente/pruefe-saetze.py`.
- Measured: stands as 111, run says 117 (`117 Saetze beanspruchen 248 Kennungen`).

```diff
--- a/messung/PASSREGISTER.md	(line 19)
+++ b/messung/PASSREGISTER.md	(proposed)
@@
-| Sentences in the register | **111** | `gabbro paesse` |
+| Sentences in the register | **117** | `gabbro paesse` |
```

### P06 — codes without a sentence (`messung/PASSREGISTER.md:50`)

- Register label (verbatim): `Zahn 2 -- Kennungen ohne Satz`
- Command: `./instrumente/pruefe-saetze.py`.
- Measured: stands as 53, run says 55 (`== Zahn 2: 55 von 303 Kennungen ohne Satz ==`).

```diff
--- a/messung/PASSREGISTER.md	(line 50)
+++ b/messung/PASSREGISTER.md	(proposed)
@@
-| **Codes without a sentence — the ratchet** | **53** | `./instrumente/pruefe-saetze.py` |
+| **Codes without a sentence — the ratchet** | **55** | `./instrumente/pruefe-saetze.py` |
```

### P07 — guardians and instruments on the front page (`README.md:161`, one line, three moves)

- Register labels (verbatim): `Instrumente mit Frist, Sprechprobe und rotem Abbruch`, `Instrumente insgesamt`
- Commands: `./instrumente/pruefe-waechter.py` (static-carrier line, total line),
  `./instrumente/pruefe-kennungen.py` (guardian count via `pruefe-todo.py`).
- Measured: guardians 37 vs 38; carriers 64 of 65 vs 65 of 66.

```diff
--- a/README.md	(line 161)
+++ b/README.md	(proposed)
@@
-| **Guardians** | 37, and ~~62 of 63~~ ~~63 of 64~~ **64 of 65 instruments carry all five requirements** — four read statically (deadline · two-way speech test · red on abort · **pinned locale**), the fifth (**work quantity beside the verdict**, W17) measured only by `--lauf`, held by `./instrumente/pruefe-waechter.py` *(run 2026-09-04)* | **387 of 387 anchors hold** *(run 2026-09-03, `mutiere-pruefer.py --anker`)* |
+| **Guardians** | 38, and ~~62 of 63~~ ~~63 of 64~~ ~~64 of 65~~ **65 of 66 instruments carry all five requirements** — four read statically (deadline · two-way speech test · red on abort · **pinned locale**), the fifth (**work quantity beside the verdict**, W17) measured only by `--lauf`, held by `./instrumente/pruefe-waechter.py` *(run 2026-09-04)* | **387 of 387 anchors hold** *(run 2026-09-03, `mutiere-pruefer.py --anker`)* |
```

Note: the neighbouring `387 of 387 anchors` is stale against the run (391 of 409)
but no pattern binds it; untouched (see section 5).

### P08 — rejection identifiers (`TODO.md:4239`, guarded figure only)

- Register label (verbatim): `Absagekennungen`
- Command: `./instrumente/pruefe-kennungen.py`.
- Measured: stands as 295, run says 303 (`== Kennungen: 303 vergeben ==`).

```diff
--- a/TODO.md	(line 4239, only the guarded figure moves)
+++ b/TODO.md	(proposed)
@@
-sofort: *kein neuer Absagecode ohne seinen Satz* (2026-08-21 gebaut; heute 111 Sätze über 295 Codes, 53 Codes noch ohne — `D017`/`D018` kamen am 2026-08-31 mit ihrem Satz `d.domaenenort` im selben Commit).**Und der zweite Zahn hat am 2026-08-31 gegriffen:** `N042` kam mit seinem Satz im selben Commit— 241 → 242 Codes, 73 → 74 Sätze, und die 45 blieben stehen. *285 → 289 Codes, 101 → 105 Sätze, 51 → 53 ohne am 2026-09-09:* `D025`/`D026`/`K011`/`K012` kamen mit ihren Sätzen im selben Commit. *Genau die Bewegung, für die der
+sofort: *kein neuer Absagecode ohne seinen Satz* (2026-08-21 gebaut; heute 111 Sätze über ~~295~~ 303 Codes, 53 Codes noch ohne — `D017`/`D018` kamen am 2026-08-31 mit ihrem Satz `d.domaenenort` im selben Commit).**Und der zweite Zahn hat am 2026-08-31 gegriffen:** `N042` kam mit seinem Satz im selben Commit— 241 → 242 Codes, 73 → 74 Sätze, und die 45 blieben stehen. *285 → 289 Codes, 101 → 105 Sätze, 51 → 53 ohne am 2026-09-09:* `D025`/`D026`/`K011`/`K012` kamen mit ihren Sätzen im selben Commit. *Genau die Bewegung, für die der
```

Note: the adjacent 111 sentences move under P16; the adjacent 53 without a
sentence is bound by no pattern (see section 5).

### P09 — rejections whose text carries the reason (`TODO.md:824`)

- Register label (verbatim): `Absagen, deren Text den tragenden Grund nennt`
- Command: `./instrumente/pruefe-gruende.py`.
- Measured: stands as 132, run says 138 (`7 verdaechtig · 138 tragend · 107 unklar`).

```diff
--- a/TODO.md	(line 824)
+++ b/TODO.md	(proposed)
@@
-      Pfad"*) nennt. ~~129~~ ~~130~~ ~~131~~ 132 sind tragend, 7 verdächtig — und **87 Absagetexte sagen ihren Grund in
+      Pfad"*) nennt. ~~129~~ ~~130~~ ~~131~~ ~~132~~ 138 sind tragend, 7 verdächtig — und **87 Absagetexte sagen ihren Grund in
```

Note: the neighbouring 7 matches the run, so it does not move.

### P10 — rejections without a recognisable reason (`TODO.md:821`)

- Register label (verbatim): `Absagen ohne erkennbaren Grund`
- Command: `./instrumente/pruefe-gruende.py`.
- Measured: stands as 108, run says 107 (same summary line as P09).

```diff
--- a/TODO.md	(line 821)
+++ b/TODO.md	(proposed)
@@
-- [ ] ~~105~~ **108 Absagetexte sagen ihren Grund in KEINER der beiden Sprachen** (`./instrumente/pruefe-gruende.py`,      2026-08-20). Die billige Näherung sortiert jede Regel danach, ob ihre Begründung eine
+- [ ] ~~105~~ ~~108~~ **107 Absagetexte sagen ihren Grund in KEINER der beiden Sprachen** (`./instrumente/pruefe-gruende.py`,      2026-08-20). Die billige Näherung sortiert jede Regel danach, ob ihre Begründung eine
```

### P11 — mutation anchors (`TODO.md:1206`, guarded figure only)

- Register label (verbatim): `Mutationsanker, die im Pruefer wirklich sitzen`
- Command: `./instrumente/mutiere-pruefer.py --anker`.
- Measured: stands as 392, run says 391 (`== 391 von 409 Ankern greifen ==`).

```diff
--- a/TODO.md	(line 1206, only the guarded figure moves)
+++ b/TODO.md	(proposed)
@@
-      fällt. Mutationskatalog: **392 von 403 Ankern** greifen (`--anker`, nachgemessen 2026-09-09;
+      fällt. Mutationskatalog: ~~392~~ **391 von 403 Ankern** greifen (`--anker`, nachgemessen 2026-09-09;
```

Note: the denominator (403 vs 409 measured) stands open in the pattern by
decision and is unguarded; untouched.

### P12 — continuation lines (`TODO.md:927`, guarded figures only)

- Register label (verbatim): `Zeilenfortsetzungen -- die Flaeche der Klebeprobe`
- Command: `./instrumente/pruefe-englisch.py`, pattern on its readability line.
- Measured: stands as 3733, run says 3970 (`== Lesbarkeit: 3970 Zeilenfortsetzungen`).

```diff
--- a/TODO.md	(line 927, guarded figure only; the 2514-character history tail stands unchanged)
+++ b/TODO.md	(proposed)
@@
-      Heute ~~3299~~ ~~3303~~ ~~3324~~ ~~3328~~ ~~3355~~ ~~3358~~ ~~3423~~ ~~3426~~ ~~3499~~ ~~3538~~ ~~3629~~ ~~3631~~ ~~3630~~ ~~3697~~ ~~3729~~ **3733 Zeilenfortsetzungen** in den Quellen, **0 kleben**, **0 geplatzt**.
+      Heute ~~3299~~ ~~3303~~ ~~3324~~ ~~3328~~ ~~3355~~ ~~3358~~ ~~3423~~ ~~3426~~ ~~3499~~ ~~3538~~ ~~3629~~ ~~3631~~ ~~3630~~ ~~3697~~ ~~3729~~ ~~3733~~ **3970 Zeilenfortsetzungen** in den Quellen, **0 kleben**, **0 geplatzt**.
```

Note: `0 kleben` and `0 geplatzt` match the run; only the head figure moves.

### P13 — files read by the revocation guardian (`TODO.md:579`)

- Register label (verbatim): `Dateien, die der Widerrufwaechter liest`
- Command: `./instrumente/pruefe-widerruf.py`.
- Measured: stands as 299, run says 325
  (`== Widerrufene Saetze: 13 Eintraege, 325 Dateien ==`).

```diff
--- a/TODO.md	(line 579)
+++ b/TODO.md	(proposed)
@@
-      heute **13 Widerrufe** über 299 Dateien, und keiner davon ist eine Teilmengenbeziehung.
+      heute **13 Widerrufe** über ~~299~~ 325 Dateien, und keiner davon ist eine Teilmengenbeziehung.
```

Note: the neighbouring 13 matches the run. Whoever applies this re-measures:
this very file adds one more (`messung/*.md` counts), so the figure to book is
326, not 325 (see section 7).

### P14 — direct looks at the environment maps (`TODO.md:469`)

- Register label (verbatim): `direkte Blicke auf die Karten der Umgebung`
- Command: `./instrumente/zaehle-karten.py`.
- Measured: stands as 47, run says 49.

```diff
--- a/TODO.md	(line 469)
+++ b/TODO.md	(proposed)
@@
-      ~~46~~ **47 direkte Blicke** auf die Karten aus 27 Passdateien, davon fünf in einer
+      ~~46~~ ~~47~~ **49 direkte Blicke** auf die Karten aus 27 Passdateien, davon fünf in einer
```

### P15 — looks without a module candidate (`TODO.md:470`)

- Register label (verbatim): `Blicke ohne Modulkandidaten -- jeder ein moegliches M103-Loch`
- Command: `./instrumente/zaehle-karten.py`.
- Measured: stands as 42, run says 44.

```diff
--- a/TODO.md	(line 470)
+++ b/TODO.md	(proposed)
@@
-      Kandidatenschleife und ~~41~~ **42 davon unqualifiziert**.
+      Kandidatenschleife und ~~41~~ ~~42~~ **44 davon unqualifiziert**.
```

### P16 — sentences over the passes, trigger 1 for goal 9 (`TODO.md:55`, guarded figure only)

- Register label (verbatim): `Saetze ueber den Paessen -- Ausloeser 1 fuer Ziel 9`
- Command: `cargo run -q --bin gabbro -- paesse` (run by the number guardian).
- Measured: stands as 111, run says 117 (`SENTENCES: 117 over 12 passes`).

```diff
--- a/TODO.md	(line 55, guarded figure only; the dated measurement note in parentheses is unchanged)
+++ b/TODO.md	(proposed)
@@
-| **9** | der Prüfer als Mathematik, in Lean 4 | **D** | **wartet auf einen gemessenen Auslöser, nicht auf einen Termin.** *Erst der Satz, dann der Beweis* — **seit PL.1 (2026-08-21) stehen ~~110~~ 111 Sätze über 12 von 12 Pässen (52 am 2026-08-21, 96 und 98 im Lauf davor, 100 davor), keiner bewiesen** *(gemessen 2026-09-03 mit `cargo run -q --bin gabbro -- paesse`: `SENTENCES: 94 over 12 passes -- 87 measured, 2 ARGUED, 5 CONJECTURED, 0 proved`, 228 Codes beansprucht, 275 vergeben; die Zahl steht im Register von `pruefe-zahlen.py`).*
+| **9** | der Prüfer als Mathematik, in Lean 4 | **D** | **wartet auf einen gemessenen Auslöser, nicht auf einen Termin.** *Erst der Satz, dann der Beweis* — **seit PL.1 (2026-08-21) stehen ~~110~~ ~~111~~ 117 Sätze über 12 von 12 Pässen (52 am 2026-08-21, 96 und 98 im Lauf davor, 100 davor), keiner bewiesen** *(gemessen 2026-09-03 mit `cargo run -q --bin gabbro -- paesse`: `SENTENCES: 94 over 12 passes -- 87 measured, 2 ARGUED, 5 CONJECTURED, 0 proved`, 228 Codes beansprucht, 275 vergeben; die Zahl steht im Register von `pruefe-zahlen.py`).* |
```

Note: the parenthetical dated note is stale prose, not a guarded figure; untouched.

### P17 — rejection identifiers on the front page (`README.md:157`)

- Register label (verbatim): `Absagekennungen` (held by `pruefe-todo.py`)
- Command: `./instrumente/pruefe-kennungen.py`.
- Measured: stands as 295, run says 303.

```diff
--- a/README.md	(line 157)
+++ b/README.md	(proposed)
@@
-| **Compiler** | 12 passes, 3 complete, **9 carried with a named residue**, 0 partial, 0 open | ~~289~~ ~~293~~ ~~294~~ 295 diagnostics · `gabbro paesse` |
+| **Compiler** | 12 passes, 3 complete, **9 carried with a named residue**, 0 partial, 0 open | ~~289~~ ~~293~~ ~~294~~ ~~295~~ 303 diagnostics · `gabbro paesse` |
```

### P18 — poison files on the front page (`README.md:163`, guarded figure only)

- Register label (verbatim): corpus poison count (held by `pruefe-todo.py`)
- Command: `ls beispiele/gift/*.gab`.
- Measured: stands as 500, run says 549. The neighbouring 71 clean examples
  match the run (`ls beispiele/*.gab`).

```diff
--- a/README.md	(line 163, guarded figure only; the 2665-character row is otherwise unchanged)
+++ b/README.md	(proposed)
@@
-| **Corpus** | 71 clean examples, ~~471~~ ~~479~~ ~~488~~ ~~498~~ 500 poison files, 451 tests *(run 2026-09-10, `ki-pc-fisch-101` unreachable through the jump host — local lane, `free -g` beside every run)* — the newest is `beispiele/71-frist-und-zaehlung.gab`,
+| **Corpus** | 71 clean examples, ~~471~~ ~~479~~ ~~488~~ ~~498~~ ~~500~~ 549 poison files, 451 tests *(run 2026-09-10, `ki-pc-fisch-101` unreachable through the jump host — local lane, `free -g` beside every run)* — the newest is `beispiele/71-frist-und-zaehlung.gab`,
```

Note: the neighbouring 451 tests are bound by no pattern; untouched (section 5).

### P19 — poison probes in the closing line (`DONE.md:1562`, guarded figure only)

- Register label (verbatim): `Giftproben` (held by `pruefe-todo.py`, rule 8)
- Command: `ls beispiele/gift/*.gab`.
- Measured: stands as 500, run says 549. The neighbouring 71 clean examples
  match the run. This is the stale cell that aborted the guardian (F1).

```diff
--- a/DONE.md	(line 1562, guarded figure only; the rest of the 441-character line stands)
+++ b/DONE.md	(proposed)
@@
-**71 clean examples, ~~471~~ ~~479~~ ~~488~~ ~~498~~ 500 poison probes, 451 tests · 55 translation units** —`cargo test` · `cargo run --bin gabbro -- pruefe beispiele/*.gab` · `./instrumente/pruefe-emission.sh`>
+**71 clean examples, ~~471~~ ~~479~~ ~~488~~ ~~498~~ ~~500~~ 549 poison probes, 451 tests · 55 translation units** —`cargo test` · `cargo run --bin gabbro -- pruefe beispiele/*.gab` · `./instrumente/pruefe-emission.sh`>
```

Note: the neighbouring 451 tests and 55 translation units are bound by no
pattern; untouched (section 5).

## 4. Ordering: why none of P01–P19 is applied here

Repo rule: bilingual patterns FIRST, then cells. Section 2 (F4) is that first
step for the 36 labels; the applier moves each cell with its pattern, in the
mandated order. This file registers the alignment so the owning pass can apply
it. The worktree touched only `instrumente/` plus this file; no tracked
document, no source, no proof was edited.

## 5. Adjacent figures observed but NOT proposed

These stand next to a proposed figure, are bound by no pattern, and stay out:

- P01 denominator: 65 booked vs 66 measured (open in the pattern by decision).
- P03 denominator: 27237 booked vs 29667 measured (unguarded prose).
- P04 denominator: 440 booked vs 539 measured (unguarded prose).
- P07 neighbour: `387 of 387 anchors` vs 391 of 409 measured (no pattern binds it).
- P08 neighbours: 111 sentences (moves under P16) and 53 without a sentence
  (bound by no pattern in this file; the pass-register tooth P06 covers its own).
- P11 denominator: 403 booked vs 409 measured (open in the pattern by decision).
- P13 neighbours: the 13 matches; the applier books 326 (section 7), not 325.
- P16 parenthetical: the dated `SENTENCES: 94 ... 228 Codes ... 275 vergeben`
  note is stale prose, not a guarded figure.
- `messung/PASSREGISTER.md`: `Codes in the checker **274**` vs 303 issued —
  bound by no pattern (the register's own sentences entry covers line 19 only).
- `README.md:163` / `DONE.md:1562`: 451 tests, 55 translation units — bound by
  no pattern.
- ZUSAGE (`dokumente/PLAN.md:3464`, booked **0**): recomputed **0** after F2 —
  no proposal; the search path, not the figure, was broken.

## 6. Standing red around this register (not caused by this file)

- `pruefe-englisch.py` exits 1 with four broken ratchets. Every rise is
  attributed to its lane; none is raised here (a raised mark without a
  translation is a rubber band, and this file says so where the marks live):
  - checker comments 7904 vs 7881 (+23): all of it arrived after the 2026-09-10
    booking, spread over the p04–p27 lane batch — `paarung.rs` +8 (107→115),
    `absenkung.rs` +4 (new file), `kostenledger.rs` +4 (new file),
    `ableitung.rs` +2 (new), `nebeneinander.rs` +2 (new), `certemit.rs` +1
    (new), `corrcert.rs` +1 (new), `geteilt.rs` +1 (267→268). Measured by
    counting German comment lines per file at `615349b6` vs `HEAD`; the deltas
    sum to exactly +23. Translation belongs to the owning lanes (`crates/`
    is out of scope here).
  - instrument comments 1085 vs 1069 (+16): `pruefe-gestalt.py` +13 (new file,
    lane 100), `nachpruefer.py` +1 (new file), `pruefe-abstieg.py` +1,
    `pruefe-grammatiktafel.py` +1. Measured the same way against `27681e08`;
    deltas sum to exactly +16. Three of the four are untranslatable by
    construction, not by neglect: `nachpruefer.py:71` quotes a German
    diagnostic verbatim (evidence — a translated quote is none),
    `pruefe-abstieg.py`'s delta line quotes the code identifier `` `Wenn` ``
    (a name, not prose), and `pruefe-grammatiktafel.py:200` continues a
    half-English sentence. The thirteen in `pruefe-gestalt.py` are the owning
    lane's fresh design prose. Rewriting another lane's words in a
    watcher-stage commit would trade a loud red for a quiet meaning change;
    the ratchet stays red and keeps naming its cause.
  - feeders 24 vs 23 (+1): `crates/gabbro-check/src/certemit.rs:436-438`,
    `guard darf = {}` inside a report string. `darf`/`gdarf` name no variable
    and no field anywhere in `crates/` (only the doc comments at
    `certemit.rs:76,85` and these two report lines) — a German word in an
    English report, half-translated in exactly the sense this guardian was
    built against. One-word fix in `crates/`, out of scope here; remainder for
    the owning lane.
  - sink messages 1 vs 0 (+1): `crates/gabbro-cli/src/main.rs:713`,
    the `hilfe()` text, word `mit` in the flag `--mit-beweis`
    (`gabbro emit [--with L.gabi]… [--proved|--mit-beweis]`). The flag is REAL:
    parsed at `main.rs:1047`, tested at `tests/fahnen.rs:201`. So the hit is a
    proper NAME (a flag spelling), same class as the booked file names and
    mutation keys — the guardian counts function words and cannot tell a name
    from prose (its declared W10 coarsening). Whether a German flag alias
    belongs on an English surface is a decision for the owning lane (rename or
    book like the 23 feeders); the guardian now at least PRINTS the site (F3).
- `pruefe-waechter.py` exits 1: 3 open partial measurements against ratchet 0 —
  `instrumente/pruefe-deckung.py:660`, `instrumente/pruefe-gestalt.py:205`,
  `instrumente/zaehle-pflichten.py:903`. None of the three runs under the
  `abschnitt.fahre` wiring (all end in bare `sys.exit(main())`), so their
  finding-exits stand without the announced-cut form. The repair is wiring
  each through `abschnitt` (`fertig()` before a complete verdict, trailer on a
  cut — green paths print nothing either way), verified by each tool's own
  speech test. Three small edits, three owners; remainder, not done here, so
  no green guardian changes shape in this commit.
- `pruefe-waechter.py` additionally carries its own note that 6 guardians are
  too heavy for its `--lauf` cast and stand beside it with reasons; untouched.

## 7. Verification after writing this file

- `pruefe-todo.py --probe`: exit 0 (was 2). Full run: exit 1 with exactly the 4
  findings booked as P17–P19 (plus the DONE half of P19); PLAN P-row clean
  (9 booked deviations, none new).
- `pruefe-klauseln.py`: exit 0 (was 1). `ZUSAGE 0` printed; the number
  guardian's ZUSAGE entry recomputes (91 of 91, was 90 of 91).
- `pruefe-zahlen.py`: speech test holds in both directions over all 91 entries
  (figure-tamper falls, label-removal reports `UNBEWACHT`); multi-hit list
  unchanged at 3; findings are exactly P01–P16 plus nothing else.
- `pruefe-englisch.py`: all twelve speech-test directions hold; the four
  ratchets break at the attributed numbers and now print their sites.
- Green guardians re-run after every edit in this commit: `-kennungen.py` 0,
  `-syntax.sh` 0, `-sondendeckung.py` 0, `-widerruf.py` 0,
  `-grammatiktafel.py` 0.
- No edited instrument added a German comment line: per-file German counts in
  the four touched files are byte-identical to base (todo 111, zahlen 75,
  klauseln 54, englisch 20); the tree total stands at 1085 for the reasons in
  section 6.
- Side effects of THIS file, measured and accepted (same class as section 6 of
  `ZAHLEN-ABGLEICH.md`): `pruefe-widerruf.py` counts `messung/*.md`, so its
  file figure moves 325 → 326 between the runs above and the applier's run —
  P13 already says to book 326. The reach census (`KENNZAHL` bold cells outside
  the five watched documents) gains exactly 6 cells from the quoted table rows
  (P05, P06, and the `| **9** |` goal ordinal carried as diff context in P16);
  that section is informational and feeds no exit code. Reproduce with
  `./instrumente/pruefe-widerruf.py` and `./instrumente/pruefe-zahlen.py`.
