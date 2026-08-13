# Gabbro — offene Punkte

**Ausschliesslich Offenes.** Erledigtes steht in den Entwurfsdateien, Widerlegtes in
[`HISTORIE.md`](HISTORIE.md). Die Reihenfolge folgt [`PLAN.md`](PLAN.md).

---

## P0 — Papier, keine Zeile Code. Jeder Punkt kann die These töten

- [x] **`revoke` in den Konstrukten ausdrücken — GEFAHREN 2026-08-13**, Ergebnis in
      [`P0-1-REVOKE.md`](P0-1-REVOKE.md): **bedingt ja**, und die Bedingung ist ein fehlendes
      Konstrukt (`by consuming`, verbrauchende Traversierung). Nebenbefund wichtiger als das
      Ergebnis: **die Zählregel war kaputt.**
- [x] **P0.1b — Zeugenordnung: GEFAHREN.** Der Zeuge trägt Zugehörigkeit, `delete_leaf` braucht
      **Blattheit**, und die ist zeitabhängig. Trägt nur über **Post-Ordnung**, und die verlangt,
      dass der Rumpf die Menge **ausschliesslich durch Verbrauch** verändert.
- [ ] **`touches` ist zu grob** — es braucht eine Form für „verändert die Menge nur durch
      Verbrauch". Ohne sie hängt die Ordnung an einer Zusage statt an einer Bedingung.
- [ ] **`by consuming` in [`SYNTAX.md`](SYNTAX.md) aufnehmen — ERST NACH P0.2 UND P0.3.**
      Nach eigener Regel: ein Konstrukt aus einem Testtag verträgt einen zweiten, bevor es Grammatik
      wird. Die Selbstbindung „kein Entwurfstext vor P0.2/P0.3" galt auch für diesen Posten und
      hätte ihn beinahe vorgezogen.
- [ ] **P0.4 (NEU): derselbe Papiertest am IPC-Fastpath.** `revoke` fällt heraus, weil seine
      Nachbedingung eine Aussage über **Zugehörigkeit** ist — und Zugehörigkeit trägt ein linearer
      Zeuge. Der Fastpath hat eine Nachbedingung über **Werten**. **Er entscheidet die
      10 %-Annahme, nicht `revoke`.**
- [ ] **`vtd.rs` (1 448 Zeilen) als `device`-Block hinschreiben.** Tor: Faktor ≥ 5 kleiner. Sonst
      ist die Knappheitsthese widerlegt.
- [ ] **`space.rs` zweimal hinschreiben** — als Gabbro-Quelle und mit dem, was ein Beweiser darüber
      hinaus bräuchte. Die erste echte Zahl für die Kennzahl.
- [ ] **Die Basisrate zählen.** Wie viele Formate hat Caprock wirklich, wie oft ändern sie sich,
      wie viele Fehler dieser Klasse pro Jahr (aus `done.md` auszählbar)? Fällt sie klein aus, ist
      das ehrlichste Ergebnis „die Falle ist zu selten für eine Sprache".

## P1 — `check` ohne Sprache

- [ ] **`check` als Rust-Makrobibliothek**, rückwirkend gegen die 33 Messdisziplin-Fallen, jede mit
      Mutation. Tor: **≥ 5 gefangen**. Nützlich auch dann, wenn Gabbro nie entsteht.

---

## Die Frage, die über den Kern entscheidet

- [ ] **Echte Linearität ist der einzige Mechanismus, den kein vorhandenes Werkzeug liefert** —
      gemessen: Verus' `tracked` ist **affin**, Rust ist affin, SPARKs Leckprüfung hängt an einer
      **Allokation**. An ihr hängen die Bootphase, `Parked` und die lineare Prüfpflicht.
      **Offen: reicht ein Mechanismus, um eine Sprache zu rechtfertigen?** Die billigere Antwort
      wäre ein Beitrag an Verus (linear statt affin). Das ist die teuerste offene Frage des Ordners.
- [ ] **ATS ist der nächste Verwandte für den Kern und ungeprüft** — lineare Typen plus Beweise,
      kompiliert nach C. Dieselbe Logik wie das Verus-Tor: *der nächste Verwandte ist gebaut, der
      Ordner nicht.* Vor P2 zu fahren.
- [ ] **Für jeden weiteren Mechanismus die Gegenrechnung führen.** M2 am Sperrbeleg und M1 sind am
      2026-08-13 gegen den Ordner ausgegangen. **M3 ist gegen die richtige Grundlinie zu messen:
      nicht Verus, sondern `tock-registers`/`svd2rust`** — typisierte Registerzugriffe sind eine
      Rust-Bibliothek. Die Frage ist, was ihr fehlt: Übergänge über Bits, Bedingungen über
      Registergrenzen, Barrierendomäne im Typ.

---

## Syntax — offene Entscheidungen (Einzelheiten in [`SYNTAX.md`](SYNTAX.md))

- [ ] **Variable Längen in `format`** — die harten 20 %, keine Schreibweise vorhanden.
- [ ] **Versionsevolution:** Absage oder Migration?
- [ ] **Generizität** — ohne sie braucht jede Tabelle ihren eigenen `traverse`; mit ihr die Frage,
      wie Verträge parametrisiert werden.
- [ ] **Die Sperrordnung fehlt in der Syntax.** `locks CAPS` nennt die Sperre, nicht die **Stufe**.
- [ ] **Der Vorrat an Quantoren in `spec fn` ist unentschieden — und genau dort wandert die Linie**,
      wenn niemand aufpasst.
- [ ] **Fehlerfortpflanzung:** ohne `?` wird jeder Aufruf drei Zeilen, mit `?` gibt es verborgenen
      Kontrollfluss. Beides widerspricht einer Entwurfsregel.
- [ ] **Schlüsselwortsprache** steht auf Englisch, weil das der Bestand ist. Preis: Bruch mit dem
      deutschen Fliesstext. Reversibel (eine Tabelle im Lexer).

## Entwurf — offene Entscheidungen

- [ ] **Variable Längen** — die harten 20 % jedes Parser-Erzeugers. Eine Syntax dafür gibt es nicht.
- [ ] **Versionsevolution.** Liest ein `@version 3`-Leser auch v2 — **Absage oder Migration**?
      Beides vertretbar, keins entschieden.
- [ ] **Roundtrip** `lesen(schreiben(x)) == x` gehört in den Differenztest.
- [ ] **Kostenangabe je Invariante** und an `by unbesucht`: welche Struktur, wer setzt sie zurück,
      was kostet der Reset, darf sie unter dem Lock leben.
- [ ] **Die Axiomschicht beziffern.** Wie viele Axiome braucht ein x86- und ein aarch64-Kernel?
      **Solange die Zahl fehlt, ist „speichersicher unter A1…An" eine Form ohne Inhalt.**
- [ ] **Fortschritt/Aushungern** (Caprocks D8) fällt unter **keinen** Mechanismus. Offen, ob das
      so bleibt oder ob es einen sechsten braucht.
- [ ] **B3 beziffern: welche Rümpfe lassen sich NICHT als Traversierung schreiben?** IPC-Fastpath,
      `revoke`, Warteschlangenchirurgie des Schedulers sind die Kandidaten. **Jeder von ihnen kostet
      5 : 1 auf seinem Anteil** — 5 % des Kernels sind +0,25 auf die Kennzahl, 10 % sind +0,5.
      Das ist die Zahl, die früh gebraucht wird und die niemand hat: sie sagt, **wie weit vom Boden
      entfernt** der Entwurf landet.

---

## Prüfer und Erzeuger

- [ ] **Mutationsprobe auf der ANNOTATIONSEMISSION**, nicht nur auf der Codeemission. Der stimmig
      abgeschwächte Fall (Code **und** Vertrag) wird von **keinem** Beweis gefangen — nur vom
      Differenztest gegen die Handschrift. Das ist dessen benannte Aufgabe.
- [ ] **Annahmenmenge ins Erzeugnis emittieren** („bewiesen unter A1…An"), als **Menge von Namen**
      mit Klasse, nicht als Zahl. Eine Ratsche über einer Kardinalzahl greift nicht gegen Austausch.
- [ ] **Jeder Falsifikator braucht seine eigene Sprechprobe:** *kann er überhaupt fehlschlagen?*
- [ ] **Der Geltungsbereich in [`SPRACHE.md`](SPRACHE.md) ist neu — Gegenprobe fahren:** ein Konstrukt suchen,
      dessen Zeile zu stark ist. Die Tabelle hat dieselbe Vorgeschichte wie die zwei
      Überschreibungen in `HISTORIE.md`.

---

## Nachzuprüfen, weil aus dem Gedächtnis zitiert

- [x] **Die seL4-Aufteilung — BESTÄTIGT:** abstrakte Spezifikation ~4 900 Zeilen Isabelle gegen
      ~8 700 Zeilen C (**≈ 0,56 : 1**), ausführbare Spezifikation ~13 000, Beweise im `l4v`-Repo
      ~200 000. Die Herleitung des Bodens hält.
- [x] **Die SPARK-Übernahmeleiter — BESTÄTIGT:** volle funktionale Korrektheit ist **Platinum**,
      Gold sind Integritätseigenschaften plus Schlüsselinvarianten.
- [ ] **Die Namensfreiheit „Gabbro"** über Paketregister, GitHub und Sprachlisten — mitsamt dem,
      was gefunden wurde. „Ich habe nichts gefunden" ist ein Nullbefund ohne Grösse.

---

## Später

- [ ] **Binärverifikation** — der einzige Weg, der die Absenkung aus der Vertrauensbasis nimmt.
      Eigenes Projekt.
- [ ] **Wiederverwendbare Spezifikationstheorien** — helfen dem **zweiten** Projekt. Dürfen in
      keiner Kostenrechnung mitgezählt werden, solange es einen Kernel gibt.
