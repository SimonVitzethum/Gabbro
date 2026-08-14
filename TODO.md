# Gabbro — offene Punkte

## Was fehlt, um Caprock VOLLSTAENDIG in Gabbro zu schreiben (Stand 2026-08-14)

**Bekannte Blocker: keiner mehr.** Die zwei gemessenen „passt nicht" aus `FRAGMENTE.md` sind zu —
`forever` hat mit `leaves`/`leave` einen Ausgang, `transition` schreibt mit `transset` **mehrere
Orte in einem Zug** (`caller` und `reply_owner` nie halb gesetzt).

**Was fehlt, ist deshalb keine Konstruktliste, sondern MESSUNG:**

- [ ] **Vier von zehn Bereichen sind nie ausgeschrieben worden:** **Scheduler**, **MMU/
      Seitentabellen**, **Lader/`SYS_LOAD`**, **Parser/Checkpoint**. Kein Urteil, kein Fragment —
      und ein Bereich ohne Fragment ist eine Vermutung.
- [ ] **Die sechs vorhandenen Fragmente sind gegen die ZWEITE Fassung geschrieben**, die Grammatik
      ist bei der vierten. Sie muessen nachgezogen und neu beurteilt werden.
- [ ] **Fuenf der elf Klempnerei-Klassen liegen nur im Scratchpad** — rund 6 der 19 haengenden
      Pflichten sind damit **nicht gegen die Sprache pruefbar**.
- [ ] **`programs/` brach 4 von 4** — aber die Messung ist **aelter als die Konstrukte**, die es
      betreffen (`leaves`, `transition publishes`). Ungeprueft, ob es heute traegt.
- [ ] **Die `narrow`-Vollzaehlung**, besonders der Schnitt, bei dem Pruefung und Verwendung in
      **verschiedenen Funktionen** liegen.

**Und getrennt davon, weil es nicht die Ausdruckskraft betrifft:** es gibt **keinen Uebersetzer**
(P2–P7), die **C-Formentabelle** (40–60 Eintraege) ist ungeschrieben, und die
**Beweisschablonen** sind benannt, nicht entworfen.

> **Seit [`SPRACHE.md`](SPRACHE.md) (2026-08-14) sind die neun Entwurfsfragen entschieden.**
> Was hier steht, ist ueberwiegend **Messung**, nicht Entwurf.

- [ ] **P0 IST TEILWEISE GEFAHREN** ([`MESSUNGEN.md`](MESSUNGEN.md), 2026-08-14). Ergebnis:
      **Ordering-Stichprobe bestanden, 36/36, kein vierter Ausgang.** `19 → 0` ist
      **nicht entscheidbar**, weil **fuenf der elf Klassen nur im Scratchpad liegen** — das ist ein
      Befund ueber das **Protokoll**, nicht ueber die Sprache, und woertlich Falle 80.
      `narrow` ≤ 24 ist offen, nur die Formpruefung war fahrbar.
- [ ] **DER NAECHSTE SCHRITT IST KEINE ZEILE RUST: die fuenf Scratchpad-Klassen mit Fundstellen ins
      Repo**, dann Teil 1 wiederholen. Vorher bleibt das Tor unentscheidbar.
- [ ] **Die `narrow`-Vollzaehlung** mit robusterem Muster — **und gezielt nach dem Schnitt suchen,
      bei dem Pruefung und Verwendung in VERSCHIEDENEN Funktionen liegen.** V-Fakten sterben an der
      Funktionsgrenze; ob dieser Fall vorkommt, entscheidet, ob `requires a >= b` als Vertrag reicht.
- [ ] **Eager-FP je Architektur oder global entscheiden.** Berichtigt: auf **x86 ist es eager**
      (`system.rs:1215`, mit genau der CVE-Begruendung der Ergaenzung); **lazy ist der
      aarch64-Pfad**. Das Dekret trifft also die andere Architektur, wo das Argument nicht in
      derselben Form greift.
- [ ] **Protokoll der Ordering-Klassifikation um K1–K3 ergaenzen** — sie sind **Wegfaelle**, keine
      Widerlegungen: unter Sperre entfaellt das Atomic (K1, ein Teil der 2 231 verschwindet),
      Konstruktinneres zaehlt in die Schablonenflaeche statt in die Stichprobe (K2), und
      `accumulates` mit Verbund ist an `sync:572-592` **strikt besser als das Original** (K3).
- [ ] **~~P0 — DIE MESSUNG~~** (urspruengliche Fassung): Die 74-Pflichten-Messung gegen
      Festlegung + beide Ergaenzungen wiederholen: **haengende Klempnerei 19 → 0**; dazu eine
      **Ordering-Stichprobe** (≥ 30 der 2 231 Fundstellen, geschichtet nach Datei) — jede ist
      Paarung, Zaehler oder benannter `seq`-Fall, **ein vierter Ausgang widerlegt die Paarung**;
      dazu die **`narrow`-Zaehlung ≤ 24**. Abnahme ist nicht Zustimmung.
- [x] **P1 — Grammatikvereinigung: GEFAHREN 2026-08-14.** Festlegung + beide Ergaenzungen sind in
      der EBNF: **117 Regeln, 0 offen, jede von `program` erreichbar, 187 Terminale gegen 187
      Wortschatzwoerter**, beide Waechter gruen. *Die Reihenfolgeregel „keine Pruefzeile vor Tor P1"
      ist damit eingehalten.*
- [ ] **Abnahme der dritten Ergaenzung** (§6): Katalog gegen Zaehlung — **jeder gezaehlte Befehl
      hat ein Axiom oder ein Konstrukt, jede Zeile einen Befehl**; die Mode-Leiter als Sprechprobe
      (vertauschtes `write_cr0(PG)` **muss** brechen); die vorberechneten Boot-Tabellen byteidentisch
      gegen das, was das heutige Trampolin zur Laufzeit baut.
- [ ] **P2–P7** aus [`SPRACHE.md`](SPRACHE.md) §6 — Lexer/Parser, M1+V1–V3, M2 samt
      Schablone, C-Emission, Paarungs-Pass mit Litmus-Sonden, ein Caprock-Modul end-to-end.
      **Jede Stufe verbraucht das Ergebnis der vorigen, wie eine `Duty`.**

**Ausschliesslich Offenes.** Erledigtes steht in den Entwurfsdateien, Widerlegtes in
[`HISTORIE.md`](HISTORIE.md). Die Reihenfolge folgt [`PLAN.md`](PLAN.md).

---

## P0 — Papier, keine Zeile Code. Jeder Punkt kann die These töten

- [x] **`revoke` in den Konstrukten ausdrücken — GEFAHREN 2026-08-13**, Ergebnis in
      [`MESSUNGEN.md`](MESSUNGEN.md): **bedingt ja**, und die Bedingung ist ein fehlendes
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

## Induktion — eingetragen, und die eine Zahl fehlt

- [x] **`by induction over <domain>` steht in der Grammatik** (2026-08-14): **ein** neues Wort
      (`over` wiederverwendet), zwei Produktionen, an `fndecl` und an `invariant`. Kein Lemma,
      kein Beweisschritt, keine rekursive `spec fn` — das Schema wird **genannt**, nicht geraten.
- [ ] **Die Zahl, die alles entscheidet:** wieviele der **17 gemessenen Logik-Pflichten** brauchen
      `by induction over`, wieviele kommen ohne aus, **wieviele brauchen rekursive `spec fn` oder
      Lemmata**? Ein einziger Fall in der letzten Spalte setzt die Decke tiefer. **Dieselbe Messung
      ist der Falsifikator der L3-Entscheidung, die auf n = 1 ruht.**
- [ ] **Das erzeugte Schema muss einmal nach Isabelle** — es ist eine Schablone im Sinne von L3 und
      damit der Posten, der die Vertrauensbasis **verkleinert**.
- [ ] **Wohlfundiertheit hängt an einer Invariante, die man beweisen will.** Die Deklaration muss
      nennen, welche — und das Mass (Zahl der Abkömmlinge) ist Voraussetzung, nicht Ergebnis.

## Aus dem Kriterium ([`BEWEIS.md`](BEWEIS.md))

- [ ] **Beide Messungen nach Logik/Klempnerei aufschlüsseln** — `delete_leaf` (3,6–6 : 1) und
      `Endpoint::call` (1,8–2,3 : 1). **Ohne diese Aufteilung ist eine Zahl kein Messwert.**
      Das ist der nächste Papierschritt.
- [ ] **Zwei Klempnerei-Pflichten stehen heute schon offen** und sind je eine Widerlegung des
      Kriteriums an ihrer Stelle: `self.queues[p]` nach `31 - leading_zeros()`
      (`caprock-sched/src/lib.rs:1996`) braucht die Datenstruktur-Invariante; und **jedes
      Verfeinerungslemma**, falls die Absenkung nicht flach genug ist.
- [ ] **Die Trennlinie an einem Grenzfall streiten.** „Nennt nur die Maschine" ist scharf genug für
      die heutigen Fälle — der erste Streitfall gehört in `BEWEIS.md`, nicht in eine Fussnote.

## Aus der Umkehrung der Frage ([`SPRACHE.md`](SPRACHE.md))

- [ ] **Die achtzehn Umwandlungen sind Behauptungen über Absenkbarkeit, keine Belege.** Jede braucht
      ihre C-Absenkung hingeschrieben — vor der Kanonisierung in [`SYNTAX.md`](SYNTAX.md).
- [ ] **`retry` mit `bounded`/`progress`/`on_exceeded` ist der Ersatz für „unbegrenztes Warten".**
      Offen: reicht eine Zahl, oder braucht es zwei Schranken (Versuche **und** Ticks)?
- [ ] **Nr. 14 verlangt eine `publishes`-Klausel an 2 231 Stellen.** Ob das trägt, entscheidet keine
      Papierübung — das ist der grösste Einzelposten der ganzen Umstellung.
- [ ] **`breaking I { … }` legalisiert eine Invariantenverletzung.** Der Preis ist Sichtbarkeit
      statt Verstecken; ob das reicht, ist unentschieden.

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
