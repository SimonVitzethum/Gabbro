# Guardian-booked figures, carried over from the old TODO.md

*Moved here on 2026-09-15, when `TODO.md` was rewritten from scratch (the old 5,441-line file is
in the git history). `instrumente/pruefe-zahlen.py` holds each figure below against the command
that measures it; the lines are quoted VERBATIM from the old file, in their original language,
because the guardian's patterns read them. This is a ledger of measured figures, not a work
list -- the work list is `TODO.md`. Update a figure here when its command moves.*

## Paesse, ueber denen die Saetze stehen

| **9** | der Prüfer als Mathematik, in Lean 4 | **D** | **wartet auf einen gemessenen Auslöser, nicht auf einen Termin.** *Erst der Satz, dann der Beweis* — **seit PL.1 (2026-08-21) stehen ~~118~~ ~~122~~ ~~144~~ ~~146~~ ~~149~~ ~~150~~ 157 Sätze über 12 von 12 Pässen (52 am 2026-08-21, 96 und 98 im Lauf davor, 100 davor), keiner bewiesen** *(gemessen 2026-09-14 mit `cargo run -q --bin gabbro -- paesse`: `SENTENCES: 157 over 12 passes -- 149 measured, 2 ARGUED, 6 CONJECTURED, 0 proved`, 330 Codes beansprucht, ~~358~~ ~~369~~ ~~371~~ 381 vergeben (2026-09-14); die Zahl steht im Register von `pruefe-zahlen.py`).* **Das ist die einzige LEBENDE Zahl, die der Reichweitendurchgang von heute falsch fand** — und der Reichweitenzähler sieht sie nicht, weil sie in einem Fließtext steht und nicht fettgedruckt in einer Tabellenzelle. Auslöser 1 ist damit erfüllt; es hält Auslöser 2 (Zahn 3 auf 6) |

## direkte Blicke auf die Karten der `Umgebung`

      ~~46~~ *(struck before 2026-09-15)* **47 direkte Blicke** auf die Karten aus 27 Passdateien, davon fünf in einer

## Blicke ohne Modulkandidaten -- jeder ein moegliches `M103`-Loch

      ~~46~~ *(struck before 2026-09-15)* **47 direkte Blicke** auf die Karten aus 27 Passdateien, davon fünf in einer
      Kandidatenschleife und ~~41~~ *(struck before 2026-09-15)* **42 davon unqualifiziert**.

## `metis`/`blast`/`smt` -- Suchen, die einmal liefen

      Wachhund:** `./instrumente/zaehle-theorien.py` zählt **31 eingefrorene Suchergebnisse**

## gebuchte Widerrufe / Dateien, die der Widerrufwaechter liest

      heute **13 Widerrufe** über 299 Dateien, und keiner davon ist eine Teilmengenbeziehung.

## besetzte Zellen der Tafel -- die Zahl, die „gedeckt" heissen soll / Zellen, die NUR im Giftkorpus vorkommen

      ~~169~~ ~~170~~ ~~25~~ ~~171~~ **172 besetzte Zellen** stehen daneben, **25 nur im Gift** (2026-09-14, lane 170: `traverse in traverse` turns covered -- `beispiele/122` nests two `elems of` loops; 2026-09-13, lane 152: `atomic × written` and `tagged × return (body)` turn poison-only, `atomic × read` turns covered) — und `gabbro blindstellen`

## Absagen ohne erkennbaren Grund

- [ ] ~~105~~ ~~108~~ **117 Absagetexte sagen ihren Grund in KEINER der beiden Sprachen** (`./instrumente/pruefe-gruende.py`,      2026-08-20). Die billige Näherung sortiert jede Regel danach, ob ihre Begründung eine

## Absagen, deren Text den tragenden Grund nennt / Absagen, die sich ueber die DARSTELLUNG begruenden

      Pfad"*) nennt. ~~129~~ ~~130~~ ~~131~~ ~~132~~ ~~139~~ 143 sind tragend, 8 verdächtig — und **~~87~~ ~~107~~ 117 Absagetexte sagen ihren Grund in

## Item-Arten, die ein Pass anfasst

      *(2026-08-19, nachgemessen 2026-08-20)*. **28 von 28 Item-Arten** sind „gelesen" —

## klebende Nahtstellen

      Heute ~~3299~~ ~~3303~~ ~~3324~~ ~~3328~~ ~~3355~~ ~~3358~~ ~~3423~~ ~~3426~~ ~~3499~~ ~~3538~~ ~~3629~~ ~~3631~~ ~~3630~~ ~~3697~~ ~~3729~~ ~~3733~~ **~~4634~~ 4677 Zeilenfortsetzungen** in den Quellen, **0 kleben**, **0 geplatzt**. *4634 → 4677 am 2026-09-14:* dreiundvierzig Bahnen der Fusswache2 (N290-N294, Satz, acht Pruefungen) — **dreiundvierzig mehr, 0 kleben**. *3733 → 4634 am 2026-09-13:* Wellenstand seither plus neunundzwanzig Bahnen der Fusswache (E245-E249, Satz, neun Pruefungen) — **neunhunderteins mehr, 0 kleben**. *3729 → 3733 am 2026-09-11:* dreißig Bahnen (H019/H020-Regeln mit Proben, Lean-Sätze, Messnotizen) bringen ihre Fortsetzungen mit — **vier mehr, 0 kleben**.  *3631 → 3630 am 2026-09-10:* die `Match`-Arm-Entschachtelung in `zaehlstellen_block` nimmt eine Fortsetzung wieder heraus — **eine weniger, 0 kleben**. *3629 → 3631 am 2026-09-10:* zwei Bahnen (`gabbrov`-Gerüst, P002-Hinweise) bringen ihre Fortsetzungen mit — **zwei Fortsetzungen mehr, 0 kleben**. *3538 → 3629 am 2026-09-09:* die vierte Syntaxfassung (`deadline`, `count`, `owner`, vier neue Absagecodes, fünf neue Sätze, sieben Gift- und Beispielprogramme) bringt ihre Bahnen mit — **einundneunzig Fortsetzungen mehr, 0 kleben**. *3426 → 3499 am 2026-09-08:* die beiden Regeln dieses Laufs — `M146` (eine Bruchschranke an einem Ganzzahltyp) und `S009` (eine `-> never`-Routine, die zurückkehrt) — bringen ihre zwei Sätze im Passregister, ihre zwei Giftproben und drei Prüfungen mit **einer Bahn je Stelle, an der ein Bereich stehen darf**: dreiundsiebzig Fortsetzungen mehr, **0 kleben**. *3358/3423 → 3426 am 2026-09-08:* **zwei Bahnen haben dieselbe Zahl bewegt, und die zusammengeführte ist keine von beiden** — der Lean-Kanal (+3) und die Binderregel `D022`/`D023` (+68) standen einzeln bei 3358 und 3423; nachgemessen im gemeinsamen Baum sind es **3426**. *Eine Zahl, die zwei Zweige einzeln buchen, ist beim Zusammenführen zu MESSEN und nicht zu addieren.* *3355 → 3358 am 2026-09-08:* der Lean-Kanal bekam die Lochphase in `gabbro_calls` und die zwei weiteren Schleifenformen der Rekursion — **drei Fortsetzungen mehr, 0 kleben.** *3328 → 3355 am 2026-09-08:* der Lean-Kanal bekam den Passzähler und die sechs neuen Absagegründe — **siebenundzwanzig Fortsetzungen mehr, 0 kleben.** *3299 → 3303 am 2026-09-04:* die `queue`-Absage in `emit.rs` wurde berichtigt und ist von zwei auf sechs Zeilen gewachsen — **vier Fortsetzungen, kein Text mehr an anderer Stelle.**      *Am 2026-08-31 fiel die Zahl erst von 2102 auf 2101* — eine übersetzte Parsermeldung      kam mit einer Fortsetzung weniger aus — *und stieg dann auf 2120*, weil die vier      Domänenproben fortgesetzte Quelltexte tragen. **Und noch am selben Tag auf 2127**, weil      das Schablonenregister übersetzt wurde und zwei Zeichenketten dabei aus einer einzigen

## Zeilenfortsetzungen -- die Flaeche der Klebeprobe

      Heute **3183 Zeilenfortsetzungen** in den Quellen, **0 kleben**, **0 geplatzt**.      *Am 2026-08-31 fiel die Zahl erst von 2102 auf 2101* — eine übersetzte Parsermeldung      kam mit einer Fortsetzung weniger aus — *und stieg dann auf 2120*, weil die vier      Domänenproben fortgesetzte Quelltexte tragen. **Und noch am selben Tag auf 2127**, weil      das Schablonenregister übersetzt wurde und zwei Zeichenketten dabei aus einer einzigen

## Zeilen der eigenen Isabelle-Theorien

      ist. Heute: **3512 Zeilen** in fünfzehn Theorien, **101 Sätze** darin — und klassifiziert:

## die Haelfte, die einer Verus-Zeilenzahl gegenuebersteht

      **1336 Zeilen Modell und Beweis** sind das, was einer Verus-Zeilenzahl gegenübersteht —

## Mutationsanker, die im Pruefer wirklich sitzen

      fällt. Mutationskatalog: **386 von 413 Ankern** greifen (`--anker`, nachgemessen 2026-09-14; +4 Lane 177, alle vier greifen; die 27 toten standen schon vor diesem Lauf so — 17 in `lean.rs`, 10 anderswo — *ein toter Anker misst nichts und faellt trotzdem unter `ungueltig`, also laeuft die Quote sonst ueber einer schrumpfenden Bezugsgroesse und liest sich wie Deckung.* 397 → 398 an diesem Tag: `binder-ohne-typ` musste MITWANDERN, weil `binder_typ` seine vierte Domaene bekam, und `elems-binder-ohne-schranke` kam als eigener Anker daneben; 2026-09-07; die Zahl stand am selben Tag noch bei 385 —

## Schablonen im Register / Schablonen, die unbewiesen dastehen

      Das Schablonenregister führt **21 Einträge**, **11 davon unbewiesen** (`gabbro

## Zellen der Tafel insgesamt

Konstrukt — und **die Fehler sitzen an den Kombinationen**: ~~79~~ *(struck before 2026-09-15)* 78 blinde Zellen von 285. Jedes echte

## Zahn 3 -- Praemissen bewiesener Schablonen ohne Pass

Marke 6 — eine Ratsche, keine Zielzahl · 0 ohne Adresse

## fremde Ruempfe im Korpus / fremde Ruempfe, die ihre Pflicht AUSSPRECHEN

**122 fremde Rümpfe im Korpus, 11 sprechen ihre Pflicht aus — und genau EINE verengt wirklich

## Traversierungsruempfe im Korpus -- das N zur Duplikatzahl (W11)

      22 Traversierungsruempfe stehen heute im Korpus

## duplizierte Traversierungsruempfe -- der gemessene Bedarf fuer Generizitaet

       0 duplizierte Ruempfe  — streng UND unter der weitesten Lesart, die zu verteidigen ist

## deutsche Kommentarzeilen im Pruefer -- die Ratsche der Uebersetzung

~~7881~~ ~~7883~~ ~~7891~~ **7892 von 27237 Kommentarzeilen** im Pruefer sind deutsch

## Giftproben auf einer mehrdeutigen Kennung

      ~~68~~ ~~70~~ ~~71~~ ~~73~~ 84 Proben zeigen auf eine Kennung mit unaehnlichen Vergabestellen (von 440

## Absagekennungen

sofort: *kein neuer Absagecode ohne seinen Satz* (2026-08-21 gebaut; heute 160 Sätze über 393 Codes, 55 Codes noch ohne — `D017`/`D018` kamen am 2026-08-31 mit ihrem Satz `d.domaenenort` im selben Commit).**Und der zweite Zahn hat am 2026-08-31 gegriffen:** `N042` kam mit seinem Satz im selben Commit— 241 → 242 Codes, 73 → 74 Sätze, und die 45 blieben stehen. *285 → 289 Codes, 101 → 105 Sätze, 51 → 53 ohne am 2026-09-09:* `D025`/`D026`/`K011`/`K012` kamen mit ihren Sätzen im selben Commit. *Genau die Bewegung, für die der

## `@version`-Textstellen -- die Menge, auf die sich Entscheidung 12 beruft

      16 `@version`-Textstellen in Korpus + FRAGMENTE:  12 × „1", 2 × „17"

## verschiedene `@version`-Deklarationen -- die 14 zaehlt sieben doppelt

       8 VERSCHIEDENE Deklarationen — `messung/fragmente/` ist byteidentisch mit FRAGMENTE.md

## gemessene Formatentwicklungen -- die NULL, die die Absage traegt

       0 Formate mit einer zweiten Fassung        — `./instrumente/zaehle-formate.py`

# Figures `pruefe-todo.py` holds against its own measurement

*Also moved from the old TODO.md on 2026-09-15; `pruefe-todo.py` reads this file together with
`TODO.md` for these patterns.*

## Kennzahlen mit Befehl

| **`./instrumente/pruefe-zahlen.py`** | das Register der Befehle. ~~64~~ ~~70~~ ~~76~~ ~~78~~ ~~79~~ ~~83~~ ~~85~~ ~~91~~ **89 Kennzahlen mit Befehl** *(Stand 2026-09-02: die neunundsiebzigste bindet die Mutationszahl auf der VORDERSEITE, `README.md`, die als `340 mutations, 372 anchors` ungebunden neben dem gebundenen `TODO.md`-Eintrag stand; 78 am 2026-08-31, 76 am 2026-08-30, 64 am 2026-08-21, 12 am Vormittag des 2026-08-20)* — und es zählt daneben, was es *nicht* bewacht. Sprechprobe über alle, in beide Richtungen. **Seine EIGENE Reichweite kann es nicht bewachen** — der Fixpunktriegel verbietet es mechanisch (W18) —, also hält sie seit heute `pruefe-todo.py`: ein anderes Werkzeug, und das ist der ganze Ausweg |

## Kennzahlen mit Befehl (Prosa)

      **`pruefe-zahlen.py` führt heute 89 Kennzahlen mit Befehl** und zählt daneben

## unbewachte fettgedruckte Zahlen

      **179 fettgedruckte Zahlen in Tabellenzellen ohne einen**. *Und diese beiden Zahlen hält seit dem

## EBNF-Regeln / EBNF-Terminale

      170 EBNF-Regeln und 233 Terminale gegen die Wortschatztabelle — *er misst die Grammatik

## EBNF-Regeln (heute-Klammer) / EBNF-Terminale (heute-Klammer)

| **5** | **Stale numbers from P1**: 117 rules, 187 terminals (today 170 / 233) | taken out along with the entry |
