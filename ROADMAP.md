# Gabbro — Fahrplan

**Jede Phase liefert eine ZAHL, und die Zahl entscheidet über die nächste.** Nicht der Vorsatz.
Wer eine Phase ohne ihre Kennzahl abschließt, hat sie nicht abgeschlossen.

Stand: 2026-08-13. **Phase 0 hat noch nicht begonnen.**

---

## Phase 0 — Die Vorfrage: gibt es das schon?

**Kennzahl:** eine Ja/Nein-Antwort mit Beleg, nicht mit Eindruck.

**EverParse** (Microsoft Research, F\*) erzeugt verifizierte Parser aus Beschreibern und wird im
Windows-Netzwerkstapel eingesetzt. Es ist der nächste Verwandte, und es ist gebaut, während Gabbro
ein Ordner mit drei Dateien ist.

- [ ] EverParse an **einem echten Caprock-Format** ausprobieren — dem Manifest-Eintrag, weil er
      Versionskopf, reservierte Bytes und eine `where`-Bedingung auf einmal hat.
- [ ] Drei Fragen beantworten: Erzeugt es `no_std`-taugliches C? Sind die Absagen **benannt** oder
      ein gemeinsamer Formfehler? Wie groß ist die Werkzeugkette (F\*-Abhängigkeit im Bauweg)?
- [ ] **Trägt es, ist dieser Ordner erledigt** — und das wäre das beste Ergebnis. Trägt es nicht,
      steht in `TODO.md`, an welchem der drei Punkte es scheiterte, und *das* ist die
      Daseinsberechtigung von Gabbro.

> Diese Phase steht zuerst, weil dieses Projekt einmal einen halben Tag an eine Lücke verloren hat,
> die es nicht gab (`Kani` deckte `sync` längst ab, nur die CI beschrieb sich falsch).

---

## Phase 1 — Ein Format, von Hand, als Maßstab

**Kennzahl:** Zyklen je Aufruf und `.text`-Größe der **handgeschriebenen** Referenz.

Bevor irgendetwas erzeugt wird, muss feststehen, wogegen gemessen wird.

- [ ] Den Manifest-Leser in C von Hand schreiben, so wie ein guter Systemprogrammierer ihn
      schriebe — mit allen Prüfungen, die Gabbro später erzwingen soll.
- [ ] Zyklen je Aufruf messen (Median, ruhige Maschine, TSC), dazu `.text`.
- [ ] **Diese Zahl ist der Maßstab für alles Weitere.** Ein Erzeuger, der 30 % langsamer ist,
      ist gescheitert, auch wenn sein Erzeugnis bewiesen ist — die Alternative wäre dann
      handgeschriebener Code plus Prüfer.

---

## Phase 2 — Der kleinste Übersetzer, der etwas Echtes kann

**Kennzahl:** erzeugtes C gegen Phase 1 — Zyklen **und** Bytes, beide Richtungen genannt.

Umfang bewusst winzig: **nur `format`**, keine Tabellen, keine Aufzählungen.

- [ ] Übersetzer in sicherem Rust (`forbid(unsafe_code)`, benannte Abhängigkeitsliste — dieselbe
      Regel, die Caprock für Handler-Module durchsetzt).
- [ ] Feste Breiten, ausgesprochene Bytereihenfolge, `reserved`-Felder, `where` auf Feldern,
      Versionskopf mit **benannter** Absage je Grund.
- [ ] Erzeugt: C-Header + Quelle, `no_std`-tauglich, ohne Allokation.
- [ ] **Gegen Phase 1 messen.** Ist es langsamer, sagen **warum** — und ob es behebbar ist.
- [ ] Ein **Differenztest** gegen den handgeschriebenen Leser: dieselben Bytes rein, dasselbe
      Urteil raus, über zufällige und über bösartig gewählte Eingaben.

**Tor:** Ist der erzeugte Code langsamer als die Referenz **und** die Ursache nicht behebbar,
endet Gabbro hier. Das wäre ein Ergebnis, kein Scheitern.

---

## Phase 3 — Die Eigenschaft, für die es das alles gibt

**Kennzahl:** Anzahl der Eigenschaften, die **per Konstruktion** gelten, gegen die Anzahl, die
noch eine Prüfung braucht.

- [ ] **Totalität**: kein erzeugter Leser kann endlos laufen. Belegt durch die Grammatik, nicht
      durch einen Test.
- [ ] **Bereichssicherheit**: jeder Versatz steht gegen eine Länge im Geltungsbereich.
- [ ] **Absage statt Deutung**: für jeden Abweisungsgrund ein eigener Code; kein Vorgabezweig.
- [ ] Nachweis, dass die Bereichsprüfungen im erzeugten C **entfernbar** sind (`-O2`-Ausgabe
      lesen, nicht hoffen).
- [ ] **Eine Mutationsprobe je Eigenschaft**: Eigenschaft im Erzeuger absichtlich brechen, prüfen,
      dass genau die zugehörige Zeile fällt. Ein Erzeuger, der nur den gesunden Zustand kennt,
      belegt nichts.

---

## Phase 4 — Das zweite Muster: Tabellen mit Invarianten

**Kennzahl:** Findet der erzeugte Prüfer die zwei bekannten Cap-Space-Fehler?

Das ist die schärfste denkbare Abnahme, weil die Antwort schon feststeht:

- [ ] `table` mit `index into`, `option index`, `chain … bounded by` und `invariant`.
- [ ] Den Cap-Space als Beschreiber ausdrücken.
- [ ] **S1a** — die ungeprüfte `first_child`-Indizierung — **muss** unformulierbar sein.
- [ ] **S1b** — `refcount -= 1` ohne Bedingung — **muss** eine Absage oder ein ausgesprochenes
      `wrapping` verlangen.
- [ ] **S2d** — `priority: u8` gegen `[ListHead; 8]` — **muss** an der Bereichsprüfung scheitern.
- [ ] Findet er sie nicht, ist der Sprachentwurf zu schwach, und das gehört in `TODO.md`.

---

## Phase 5 — Einbau in Caprock, an genau einer Stelle

**Kennzahl:** die Abnahme-Reihe bleibt grün, und die Prüfzeilen sind **byte-identisch**.

- [ ] Ein Format ersetzen — der Manifest-Eintrag, weil er die meisten Absagen hat.
- [ ] Der erzeugte Leser muss dieselben Fehlercodes liefern wie der heutige; die Suiten dürfen
      keinen Unterschied sehen.
- [ ] `tools/eingeschlossenheit.py` muss das erzeugte Modul akzeptieren, ohne dass jemand die
      Regel lockert.
- [ ] **Tor:** Verlangt der Einbau eine Ausnahme in einem Wächter, ist der Entwurf falsch, nicht
      der Wächter.

---

## Später, ausdrücklich nicht jetzt

* **Aufzählungen mit `exhaustive`** — nützlich, aber die kleinste Ersparnis.
* **Seitentabellen-Beschreiber.** Verlockend (das fehlende `US` auf der Zwischenebene wäre nicht
  formulierbar gewesen), aber Seitentabellen sind Hardwareverträge; ein falscher Beschreiber
  erzeugt einen beweisbar korrekten falschen Kernel.
* **Rust-Ausgabe neben C.** Erst, wenn C trägt. Zwei Ziele verdoppeln die Prüffläche.
* **Binärverifikation** (seL4-Art, erzeugtes C gegen Maschinencode). Der Weg existiert, aber er
  ist ein eigenes Projekt.

---

## Die Abbruchbedingungen — hier, damit sie nicht verhandelt werden

Gabbro endet, wenn **eines** davon eintritt:

1. **EverParse trägt** (Phase 0).
2. **Der erzeugte Code ist dauerhaft langsamer** als die handgeschriebene Referenz und die Ursache
   ist nicht behebbar (Phase 2).
3. **Der erzeugte Prüfer findet die drei bekannten Fehler nicht** (Phase 4).

Ein Ordner, der seine eigenen Abbruchbedingungen nicht nennt, wird nie beendet — nur vergessen.
