# Number alignment register: proposals only

Status: PROPOSAL ONLY. No cell in any watched document has been changed.
Base: `2dc02ad` on branch `p32-ziel`, worktree `.claude/worktrees/p32`, clean tree.
Measured: 2026-09-11. All prose in this file is English. Quoted lines below are
VERBATIM copies of the current document text (quoting is not rephrasing); they are
shown only so the proposed edit is exact.

## 1. Guardian results on the clean base (before this file existed)

| Guardian | Exit | Verdict |
|---|---|---|
| `instrumente/pruefe-todo.py` | 2 | ABORT in its own self-test (pre-existing, see section 5) |
| `instrumente/pruefe-kennungen.py` | 0 | ALL PASS, 300 identifiers issued |
| `instrumente/pruefe-englisch.py` | 1 | 4 broken ratchets (comment lines, instrument comment lines, feeders, sink messages) |
| `instrumente/pruefe-syntax.sh` | 0 | ALL PASS (161 rules, 221 terminals) |
| `instrumente/pruefe-zahlen.py` | 1 | 11 findings, all listed in section 2 |

Evidence: full logs of these five runs are the measurement record. The number
guardian prints one finding per stale cell: the booked figure ("stands as") and
the recomputed figure ("the run says"). Cross-checks run separately:
`pruefe-englisch.py` prints 7904 source comment lines and 3852 continuations;
`pruefe-kennungen.py` prints 300; `pruefe-vergabe.py` prints 74;
`zaehle-karten.py` prints 49 direct and 44 unqualified; `pruefe-gruende.py`
prints 134 carrying; `pruefe-widerruf.py` prints 13 entries over 311 files
(310 before this file existed — it counts `messung/*.md`, see section 6);
`pruefe-klauseln.py` (exit 0) prints no line matching its registered pattern.

## 2. Proposed cell edits (one per finding)

Convention: proposals follow the strikethrough-history style of the surrounding
lines (`~~old~~ new`), except in `messung/PASSREGISTER.md`, whose table keeps no
history. Each proposal gives file, line, the registered recomputation command,
the measured output, and an exact old/new pair.

### P01 — source comment lines (`TODO.md:3992`)

- Register label (verbatim): `deutsche Kommentarzeilen im Pruefer -- die Ratsche der Uebersetzung`
- Command: `./instrumente/pruefe-englisch.py`, pattern on its `Quellsprache` line.
- Measured: stands as 7892, run says 7904.

```diff
--- a/TODO.md	(line 3992)
+++ b/TODO.md	(proposed)
@@
-~~7881~~ ~~7883~~ ~~7891~~ **7892 von 27237 Kommentarzeilen** im Pruefer sind deutsch
+~~7881~~ ~~7883~~ ~~7891~~ ~~7892~~ **7904 von 27237 Kommentarzeilen** im Pruefer sind deutsch
```

Note: only the guarded figure moves. The unguarded denominator (27237 vs 29022
measured) is not bound by any pattern and is left untouched; see section 4.

### P02 — samples on an ambiguous identifier (`TODO.md:4165`)

- Register label (verbatim): `Giftproben auf einer mehrdeutigen Kennung`
- Command: `./instrumente/pruefe-vergabe.py`, pattern on its cost line.
- Measured: stands as 73, run says 74 (`74 von 516 Giftproben`).

```diff
--- a/TODO.md	(line 4165)
+++ b/TODO.md	(proposed)
@@
-      ~~68~~ ~~70~~ ~~71~~ 73 Proben zeigen auf eine Kennung mit unaehnlichen Vergabestellen (von 440
+      ~~68~~ ~~70~~ ~~71~~ ~~73~~ 74 Proben zeigen auf eine Kennung mit unaehnlichen Vergabestellen (von 440
```

Note: the parenthetical denominator (440 vs 516 measured) is unguarded prose
and is left untouched; see section 4.

### P03 — sentences in the pass register (`messung/PASSREGISTER.md:19`)

- Register label (verbatim): `Saetze im Passregister`
- Command: `./instrumente/pruefe-saetze.py` (run by the number guardian; not
  re-run here because it gates on the built binary).
- Measured: stands as 111, run says 116.

```diff
--- a/messung/PASSREGISTER.md	(line 19)
+++ b/messung/PASSREGISTER.md	(proposed)
@@
-| Sentences in the register | **111** | `gabbro paesse` |
+| Sentences in the register | **116** | `gabbro paesse` |
```

### P04 — rejection identifiers (`TODO.md:4239`)

- Register label (verbatim): `Absagekennungen`
- Command: `./instrumente/pruefe-kennungen.py`, pattern on its count line.
- Measured: stands as 295, run says 300 (`Kennungen: 300 vergeben`).

```diff
--- a/TODO.md	(line 4239, only the guarded figure moves)
+++ b/TODO.md	(proposed)
@@
-sofort: *kein neuer Absagecode ohne seinen Satz* (2026-08-21 gebaut; heute 111 Sätze über 295 Codes, 53 Codes noch ohne — `D017`/`D018` kamen am 2026-08-31 mit ihrem Satz `d.domaenenort` im selben Commit).**Und der zweite Zahn hat am 2026-08-31 gegriffen:** `N042` kam mit seinem Satz im selben Commit— 241 → 242 Codes, 73 → 74 Sätze, und die 45 blieben stehen. *285 → 289 Codes, 101 → 105 Sätze, 51 → 53 ohne am 2026-09-09:* `D025`/`D026`/`K011`/`K012` kamen mit ihren Sätzen im selben Commit. *Genau die Bewegung, für die der
+sofort: *kein neuer Absagecode ohne seinen Satz* (2026-08-21 gebaut; heute 111 Sätze über ~~295~~ 300 Codes, 53 Codes noch ohne — `D017`/`D018` kamen am 2026-08-31 mit ihrem Satz `d.domaenenort` im selben Commit).**Und der zweite Zahn hat am 2026-08-31 gegriffen:** `N042` kam mit seinem Satz im selben Commit— 241 → 242 Codes, 73 → 74 Sätze, und die 45 blieben stehen. *285 → 289 Codes, 101 → 105 Sätze, 51 → 53 ohne am 2026-09-09:* `D025`/`D026`/`K011`/`K012` kamen mit ihren Sätzen im selben Commit. *Genau die Bewegung, für die der
```

Note: the adjacent figures on the same line (111 sentences, 53 without) are not
bound by this entry's pattern and are left untouched; see section 4.

### P05 — rejections whose text carries the reason (`TODO.md:824`)

- Register label (verbatim): `Absagen, deren Text den tragenden Grund nennt`
- Command: `./instrumente/pruefe-gruende.py`, pattern on its summary line.
- Measured: stands as 132, run says 134 (`7 verdaechtig, 134 tragend`).

```diff
--- a/TODO.md	(line 824)
+++ b/TODO.md	(proposed)
@@
-      Pfad"*) nennt. ~~129~~ ~~130~~ ~~131~~ 132 sind tragend, 7 verdächtig — und **87 Absagetexte sagen ihren Grund in
+      Pfad"*) nennt. ~~129~~ ~~130~~ ~~131~~ ~~132~~ 134 sind tragend, 7 verdächtig — und **87 Absagetexte sagen ihren Grund in
```

Note: the neighbouring 7 matches the run (7 suspect), so it does not move.

### P06 — continuation lines, the glue-test area (`TODO.md:927`)

- Register label (verbatim): `Zeilenfortsetzungen -- die Flaeche der Klebeprobe`
- Command: `./instrumente/pruefe-englisch.py`, pattern on its readability line.
- Measured: stands as 3733, run says 3852 (`Lesbarkeit: 3852 Zeilenfortsetzungen`).

Line 927 is quoted in full below (2514 characters); only the guarded figure
moves, the dated history tail after it is unchanged:

```diff
--- a/TODO.md	(line 927, in full)
+++ b/TODO.md	(proposed)
@@
-      Heute ~~3299~~ ~~3303~~ ~~3324~~ ~~3328~~ ~~3355~~ ~~3358~~ ~~3423~~ ~~3426~~ ~~3499~~ ~~3538~~ ~~3629~~ ~~3631~~ ~~3630~~ ~~3697~~ ~~3729~~ **3733 Zeilenfortsetzungen** in den Quellen, **0 kleben**, **0 geplatzt**. *3729 → 3733 am 2026-09-11:* dreißig Bahnen (H019/H020-Regeln mit Proben, Lean-Sätze, Messnotizen) bringen ihre Fortsetzungen mit — **vier mehr, 0 kleben**.  *3631 → 3630 am 2026-09-10:* die `Match`-Arm-Entschachtelung in `zaehlstellen_block` nimmt eine Fortsetzung wieder heraus — **eine weniger, 0 kleben**. *3629 → 3631 am 2026-09-10:* zwei Bahnen (`gabbrov`-Gerüst, P002-Hinweise) bringen ihre Fortsetzungen mit — **zwei Fortsetzungen mehr, 0 kleben**. *3538 → 3629 am 2026-09-09:* die vierte Syntaxfassung (`deadline`, `count`, `owner`, vier neue Absagecodes, fünf neue Sätze, sieben Gift- und Beispielprogramme) bringt ihre Bahnen mit — **einundneunzig Fortsetzungen mehr, 0 kleben**. *3426 → 3499 am 2026-09-08:* die beiden Regeln dieses Laufs — `M146` (eine Bruchschranke an einem Ganzzahltyp) und `S009` (eine `-> never`-Routine, die zurückkehrt) — bringen ihre zwei Sätze im Passregister, ihre zwei Giftproben und drei Prüfungen mit **einer Bahn je Stelle, an der ein Bereich stehen darf**: dreiundsiebzig Fortsetzungen mehr, **0 kleben**. *3358/3423 → 3426 am 2026-09-08:* **zwei Bahnen haben dieselbe Zahl bewegt, und die zusammengeführte ist keine von beiden** — der Lean-Kanal (+3) und die Binderregel `D022`/`D023` (+68) standen einzeln bei 3358 und 3423; nachgemessen im gemeinsamen Baum sind es **3426**. *Eine Zahl, die zwei Zweige einzeln buchen, ist beim Zusammenführen zu MESSEN und nicht zu addieren.* *3355 → 3358 am 2026-09-08:* der Lean-Kanal bekam die Lochphase in `gabbro_calls` und die zwei weiteren Schleifenformen der Rekursion — **drei Fortsetzungen mehr, 0 kleben.** *3328 → 3355 am 2026-09-08:* der Lean-Kanal bekam den Passzähler und die sechs neuen Absagegründe — **siebenundzwanzig Fortsetzungen mehr, 0 kleben.** *3299 → 3303 am 2026-09-04:* die `queue`-Absage in `emit.rs` wurde berichtigt und ist von zwei auf sechs Zeilen gewachsen — **vier Fortsetzungen, kein Text mehr an anderer Stelle.**      *Am 2026-08-31 fiel die Zahl erst von 2102 auf 2101* — eine übersetzte Parsermeldung      kam mit einer Fortsetzung weniger aus — *und stieg dann auf 2120*, weil die vier      Domänenproben fortgesetzte Quelltexte tragen. **Und noch am selben Tag auf 2127**, weil      das Schablonenregister übersetzt wurde und zwei Zeichenketten dabei aus einer einzigen
+      Heute ~~3299~~ ~~3303~~ ~~3324~~ ~~3328~~ ~~3355~~ ~~3358~~ ~~3423~~ ~~3426~~ ~~3499~~ ~~3538~~ ~~3629~~ ~~3631~~ ~~3630~~ ~~3697~~ ~~3729~~ ~~3733~~ **3852 Zeilenfortsetzungen** in den Quellen, **0 kleben**, **0 geplatzt**. *3729 → 3733 am 2026-09-11:* dreißig Bahnen (H019/H020-Regeln mit Proben, Lean-Sätze, Messnotizen) bringen ihre Fortsetzungen mit — **vier mehr, 0 kleben**.  *3631 → 3630 am 2026-09-10:* die `Match`-Arm-Entschachtelung in `zaehlstellen_block` nimmt eine Fortsetzung wieder heraus — **eine weniger, 0 kleben**. *3629 → 3631 am 2026-09-10:* zwei Bahnen (`gabbrov`-Gerüst, P002-Hinweise) bringen ihre Fortsetzungen mit — **zwei Fortsetzungen mehr, 0 kleben**. *3538 → 3629 am 2026-09-09:* die vierte Syntaxfassung (`deadline`, `count`, `owner`, vier neue Absagecodes, fünf neue Sätze, sieben Gift- und Beispielprogramme) bringt ihre Bahnen mit — **einundneunzig Fortsetzungen mehr, 0 kleben**. *3426 → 3499 am 2026-09-08:* die beiden Regeln dieses Laufs — `M146` (eine Bruchschranke an einem Ganzzahltyp) und `S009` (eine `-> never`-Routine, die zurückkehrt) — bringen ihre zwei Sätze im Passregister, ihre zwei Giftproben und drei Prüfungen mit **einer Bahn je Stelle, an der ein Bereich stehen darf**: dreiundsiebzig Fortsetzungen mehr, **0 kleben**. *3358/3423 → 3426 am 2026-09-08:* **zwei Bahnen haben dieselbe Zahl bewegt, und die zusammengeführte ist keine von beiden** — der Lean-Kanal (+3) und die Binderregel `D022`/`D023` (+68) standen einzeln bei 3358 und 3423; nachgemessen im gemeinsamen Baum sind es **3426**. *Eine Zahl, die zwei Zweige einzeln buchen, ist beim Zusammenführen zu MESSEN und nicht zu addieren.* *3355 → 3358 am 2026-09-08:* der Lean-Kanal bekam die Lochphase in `gabbro_calls` und die zwei weiteren Schleifenformen der Rekursion — **drei Fortsetzungen mehr, 0 kleben.** *3328 → 3355 am 2026-09-08:* der Lean-Kanal bekam den Passzähler und die sechs neuen Absagegründe — **siebenundzwanzig Fortsetzungen mehr, 0 kleben.** *3299 → 3303 am 2026-09-04:* die `queue`-Absage in `emit.rs` wurde berichtigt und ist von zwei auf sechs Zeilen gewachsen — **vier Fortsetzungen, kein Text mehr an anderer Stelle.**      *Am 2026-08-31 fiel die Zahl erst von 2102 auf 2101* — eine übersetzte Parsermeldung      kam mit einer Fortsetzung weniger aus — *und stieg dann auf 2120*, weil die vier      Domänenproben fortgesetzte Quelltexte tragen. **Und noch am selben Tag auf 2127**, weil      das Schablonenregister übersetzt wurde und zwei Zeichenketten dabei aus einer einzigen
```

(The history tail of the 2514-character line stands unchanged inside the quoted pair above.)

### P07 — files read by the revocation guardian (`TODO.md:579`)

- Register label (verbatim): `Dateien, die der Widerrufwaechter liest`
- Command: `./instrumente/pruefe-widerruf.py`, pattern on its summary line.
- Measured: stands as 299, run says 311 (`Widerrufene Saetze: 13 Eintraege, 311 Dateien`
  at commit time; 310 at first measurement — the +1 is this very file, see section 6).

```diff
--- a/TODO.md	(line 579)
+++ b/TODO.md	(proposed)
@@
-      heute **13 Widerrufe** über 299 Dateien, und keiner davon ist eine Teilmengenbeziehung.
+      heute **13 Widerrufe** über ~~299~~ 311 Dateien, und keiner davon ist eine Teilmengenbeziehung.
```

Note: the neighbouring 13 matches the run (13 entries), so it does not move.

### P08 — direct looks at the environment maps (`TODO.md:469`)

- Register label (verbatim): `direkte Blicke auf die Karten der Umgebung` (pattern keeps the backticked form)
- Command: `./instrumente/zaehle-karten.py`, pattern on its direct-looks line.
- Measured: stands as 47, run says 49 (`direkte Blicke 49`).

```diff
--- a/TODO.md	(line 469)
+++ b/TODO.md	(proposed)
@@
-      ~~46~~ **47 direkte Blicke** auf die Karten aus 27 Passdateien, davon fünf in einer
+      ~~46~~ ~~47~~ **49 direkte Blicke** auf die Karten aus 27 Passdateien, davon fünf in einer
```

Note: the neighbouring 5 matches the run (`davon modulbewusst 5`), so it does not move.

### P09 — looks without a module candidate (`TODO.md:470`)

- Register label (verbatim): `Blicke ohne Modulkandidaten -- jeder ein moegliches M103-Loch` (pattern keeps the backticked form)
- Command: `./instrumente/zaehle-karten.py`, pattern on its unqualified line.
- Measured: stands as 42, run says 44 (`davon UNQUALIFIZIERT 44`).

```diff
--- a/TODO.md	(line 470)
+++ b/TODO.md	(proposed)
@@
-      Kandidatenschleife und ~~41~~ **42 davon unqualifiziert**.
+      Kandidatenschleife und ~~41~~ ~~42~~ **44 davon unqualifiziert**.
```

### P10 — readerless ZUSAGE clauses (`dokumente/PLAN.md:3464`) — NO NUMBER CHANGE

- Register label (verbatim): `ZUSAGE-Klauseln ohne Leser -- das Tor von «NL»`
- Command: `./instrumente/pruefe-klauseln.py`, pattern `^\s+ZUSAGE\s+(\d+)\s`.
- Measured: the command prints NO such line (exit 0, output ends in a stale-table
  notice about one grown entry). The search path is dead, not the figure.

```diff
--- a/dokumente/PLAN.md	(line 3464)
+++ b/dokumente/PLAN.md	(proposed)
@@
 (no cell change proposed — the booked **0** is not contradicted by any new count)
```

Proposed action instead: repair or re-point the registered command (restore the
`ZUSAGE <n>` output line in the clause guardian, or register its replacement).
That change belongs to `instrumente/pruefe-zahlen.py` and is out of scope here.

### P11 — sentences over the passes, trigger 1 for goal 9 (`TODO.md:55`)

- Register label (verbatim): `Saetze ueber den Paessen -- Ausloeser 1 fuer Ziel 9`
- Command: `cargo run -q --bin gabbro -- paesse` (run by the number guardian).
- Measured: stands as 111, run says 116.

```diff
--- a/TODO.md	(line 55, guarded figure only; the dated measurement note in parentheses is unchanged)
+++ b/TODO.md	(proposed)
@@
-| **9** | der Prüfer als Mathematik, in Lean 4 | **D** | **wartet auf einen gemessenen Auslöser, nicht auf einen Termin.** *Erst der Satz, dann der Beweis* — **seit PL.1 (2026-08-21) stehen ~~110~~ 111 Sätze über 12 von 12 Pässen (52 am 2026-08-21, 96 und 98 im Lauf davor, 100 davor), keiner bewiesen** *(gemessen 2026-09-03 mit `cargo run -q --bin gabbro -- paesse`: `SENTENCES: 94 over 12 passes -- 87 measured, 2 ARGUED, 5 CONJECTURED, 0 proved`, 228 Codes beansprucht, 275 vergeben; die Zahl steht im Register von `pruefe-zahlen.py`).* **Das ist die einzige LEBENDE Zahl, die der Reichweitendurchgang von heute falsch fand** — und der Reichweitenzähler sieht sie nicht, weil sie in einem Fließtext steht und nicht fettgedruckt in einer Tabellenzelle. Auslöser 1 ist damit erfüllt; es hält Auslöser 2 (Zahn 3 auf 6) |
+| **9** | der Prüfer als Mathematik, in Lean 4 | **D** | **wartet auf einen gemessenen Auslöser, nicht auf einen Termin.** *Erst der Satz, dann der Beweis* — **seit PL.1 (2026-08-21) stehen ~~110~~ ~~111~~ 116 Sätze über 12 von 12 Pässen (52 am 2026-08-21, 96 und 98 im Lauf davor, 100 davor), keiner bewiesen** *(gemessen 2026-09-03 mit `cargo run -q --bin gabbro -- paesse`: `SENTENCES: 94 over 12 passes -- 87 measured, 2 ARGUED, 5 CONJECTURED, 0 proved`, 228 Codes beansprucht, 275 vergeben; die Zahl steht im Register von `pruefe-zahlen.py`).* **Das ist die einzige LEBENDE Zahl, die der Reichweitendurchgang von heute falsch fand** — und der Reichweitenzähler sieht sie nicht, weil sie in einem Fließtext steht und nicht fettgedruckt in einer Tabellenzelle. Auslöser 1 ist damit erfüllt; es hält Auslöser 2 (Zahn 3 auf 6) |
```

## 3. Ordering: why none of this is applied here

Repo rule: bilingual patterns must come FIRST, before any document moves,
because four guardians go silently blind on a rephrased cell. Applying P01–P11
means touching German cells in `TODO.md`, `messung/PASSREGISTER.md`, and
`dokumente/PLAN.md`. That step — patterns first, then cells — is out of scope
for this worktree by mission order. This file registers the alignment so the
owning pass can apply it in the mandated order.

## 4. Adjacent figures observed but NOT proposed

These stand next to a proposed figure, are not bound by the same entry pattern,
and therefore stay out of every proposal above:

- P01 denominator: 27237 booked vs 29022 measured (unguarded prose).
- P02 denominator: 440 booked vs 516 measured (unguarded prose).
- P04 neighbours on the same line: 111 sentences and 53 without (a separate
  entry covers the sentence figure in `TODO.md:55`, proposed as P11; the 53 has
  no finding against it in this run).
- P11 parenthetical: the dated measurement note inside the same cell is stale
  prose, not a guarded figure; untouched.

## 5. Standing red around this register (not caused by this file)

- `pruefe-todo.py` exits 2 on the CLEAN base: its self-test fails three ways
  (clean list shows 1 finding, clean English list shows 1 finding, English-label
  coverage shows 4 against 1). The abort fires before any measurement, so
  everything behind it is unmeasured, not passing. Fixing the self-test belongs
  to whoever owns that guardian; it is out of scope here and untouched.
- `pruefe-englisch.py` exits 1 with four broken ratchets (comment lines 7904 vs
  7881 booked; instrument comment lines 1085 vs 1069; feeders 24 vs 23 with
  eight named sites; sink messages 1 vs 0). Note the comment-line booking (7881)
  differs from the number-guardian booking (7892): two registers over one thing.
- `pruefe-zahlen.py` additionally reports 37 of 91 labels as German (22 in
  `TODO.md`), 29 of them in prose — the backlog this alignment will eventually
  have to translate, pattern-first.

## 6. Verification after writing this file

- `pruefe-kennungen.py`: ALL PASS, exit 0 (identifier scan covers only
  `crates/**/*.rs`; a new measurement file cannot move it).
- `pruefe-todo.py`: exit 2, byte-identical self-test output to the pre-file run
  (it reads `TODO.md`/`DONE.md`/`README.md` plus corpus counts only).
- Reach census side effect: this file quotes two guarded table rows verbatim
  (P03 old+new, P11 old+new), which the reach counter counts as bold
  numbers in table cells. Measured: 782 cells in 97 files before this file,
  786 in 98 after (+4 cells, all quoted here; the new file itself is the +1).
  That section is informational only and does not feed any exit code.
- Widerruf population side effect: `pruefe-widerruf.py` counts `messung/*.md`
  as files under watch, so creating this file moved its file figure 310 -> 311
  between the two guardian runs (both other figures identical, all other
  guardians byte-identical output). P07 above already books 311. Whoever applies
  P01–P11 re-measures anyway; the figure is a population size, not a finding.
