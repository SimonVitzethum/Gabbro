# Gabbro — offene Punkte

**Ausschliesslich Offenes.** Erledigtes steht in den Entwurfsdateien, Widerlegtes in
[`HISTORIE.md`](HISTORIE.md). Die Reihenfolge folgt [`PLAN.md`](PLAN.md).

---

## P0 — Papier, keine Zeile Code. Jeder Punkt kann die These töten

- [ ] **`revoke` in den Konstrukten ausdrücken.** Entscheidet Zuschnitt (c) **und** die Kennzahl:
      bleibt `revoke` handgeschrieben, kehrt die Invariantenerhaltung als Beweisposten zurück und
      0,5 : 1 an diesem Tag verloren ist. **Der billigste Punkt des ganzen Ordners.**
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

- [ ] **Die seL4-Aufteilung** (rund 0,5 : 1 abstrakte Spezifikation, 19,5 : 1 Beweis). Sie trägt die
      ganze Kennzahl-Herleitung.
- [ ] **Die SPARK-Übernahmeleiter** (Stone/Bronze/Silber/Gold/Platinum und was jede Stufe bedeutet).
      Sie trägt das Argument, dass „Gold" zwei Bedeutungen hat.
- [ ] **Die Namensfreiheit „Gabbro"** über Paketregister, GitHub und Sprachlisten — mitsamt dem,
      was gefunden wurde. „Ich habe nichts gefunden" ist ein Nullbefund ohne Grösse.

---

## Später

- [ ] **Binärverifikation** — der einzige Weg, der die Absenkung aus der Vertrauensbasis nimmt.
      Eigenes Projekt.
- [ ] **Wiederverwendbare Spezifikationstheorien** — helfen dem **zweiten** Projekt. Dürfen in
      keiner Kostenrechnung mitgezählt werden, solange es einen Kernel gibt.
