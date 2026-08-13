# Gabbro — offene Punkte

Nur **noch nicht Erledigtes**. Reihenfolge innerhalb eines Abschnitts = Priorität.
`[~]` = teilweise, Rest benannt.

**Stand 2026-08-13: es ist noch keine Zeile Code geschrieben.** Alles hier ist offen; nichts
davon ist eine Erfolgsmeldung.

---

## Vor allem anderen

- [ ] **EverParse prüfen, bevor hier irgendetwas gebaut wird.** Es erzeugt verifizierte Parser aus
      Beschreibern und ist im Windows-Netzwerkstapel im Einsatz — also gebaut, während Gabbro drei
      Dateien sind. Drei Fragen entscheiden: `no_std`-taugliches C? **Benannte** Absagen oder ein
      gemeinsamer Formfehler? Wie schwer wiegt die F\*-Abhängigkeit im Bauweg?
      **Trägt es, ist dieser Ordner erledigt — und das wäre das beste Ergebnis.**
      *(Dieses Projekt hat einmal einen halben Tag an eine Lücke verloren, die es nicht gab.)*

- [ ] **Den Maßstab zuerst messen, nicht danach.** Manifest-Leser von Hand in C, Zyklen je Aufruf
      (Median, ruhige Maschine) und `.text`. Ohne diese Zahl ist jede spätere Aussage über
      Leistung ein Gefühl.

---

## Sprachentwurf — was noch nicht entschieden ist

- [ ] **Wie werden Felder variabler Länge ausgedrückt?** Ein `len`-Feld, das eine folgende Reihe
      begrenzt, ist der häufigste Fall (Manifest-Einträge, virtio-Ketten) — und die Stelle, an der
      Regel 1 (Totalität) und Regel 2 (Versatz gegen Länge) sich berühren. Der Entwurf im README
      zeigt nur feste Breiten.
- [ ] **Verschachtelte Formate mit eigenem Versionskopf** — trägt der äußere die Absage des
      inneren weiter, oder hat jeder seine eigene? Zwei Fehlercodes für dieselbe Ursache sind so
      schlecht wie einer für zwei Ursachen.
- [ ] **`where` über mehrere Felder** (`entry_len == sizeof(Self)` geht; `hash != 0 || flags & 1`
      ist offen). Je mehr das kann, desto näher rückt es an eine Allzwecksprache — und damit an
      die Spezifikationslast, der Gabbro ausweichen soll. **Die Grenze gehört ausgesprochen.**
- [ ] **Schreibrichtung**: Erzeugt Gabbro auch Schreiber, und gilt für sie dieselbe Absage-Regel?
      Ein Schreiber, der eine ungültige Struktur ausgeben kann, entwertet den Leser.
- [ ] **Fehlercode-Vergabe**: fortlaufend vom Erzeuger, oder im Beschreiber genannt? Fortlaufend
      ist bequem und bricht bei jeder Umsortierung die ABI.

---

## Übersetzer

- [ ] Sicheres Rust, `#![forbid(unsafe_code)]`, **benannte** Abhängigkeitsliste — dieselbe Regel,
      die Caprock für seine Handler-Module durchsetzt. Ein Erzeuger, der ausbrechen kann, macht
      die Eigenschaft seines Erzeugnisses wertlos.
- [ ] **Ein Wächter, der die Regel hält**, nicht nur ein Vorsatz — mit Sprechprobe in beide
      Richtungen und einer Ratsche als **Menge von Namen**, nicht als Zahl.
- [ ] **Differenztest gegen den handgeschriebenen Leser**: dieselben Bytes rein, dasselbe Urteil
      raus — über zufällige **und** über bösartig gewählte Eingaben (Länge 0, Länge 1 unter dem
      Kopf, Versionsfeld = 0xFFFF_FFFF, reserviertes Byte gesetzt).
- [ ] **Eine Mutationsprobe je Spracheigenschaft.** Ein Erzeuger, der nur den gesunden Zustand
      kennt, belegt nichts — dieselbe Disziplin wie bei jedem Caprock-Wächter.

---

## Leistung

- [ ] **Bereichsprüfungen müssen im `-O2`-Ergebnis verschwinden.** Nachlesen im Assembler, nicht
      hoffen. Wenn nicht: warum nicht, und ist es der Formulierung anzulasten oder LLVM?
- [ ] **`restrict` aus dem Beschreiber ableiten**, wo Nichtüberlappung strukturell folgt — nicht
      als Zusage des Aufrufers.
- [ ] **Geradlinig statt schleifend** bei konstanter Länge (32-Byte-Hash kopieren, nicht zählen).
- [ ] **Jedes erzeugte Format bringt seine Messzeile mit.** Ohne Gegenzahl ist „schnell" ein
      Gefühl.

---

## Was noch niemand geprüft hat

- [ ] **Wie groß ist die erzeugte `.text` gegenüber der handgeschriebenen?** Ein Erzeuger, der
      dreimal so viel Code produziert, kostet i-Cache — und in einem Kernel ist das eine echte
      Größe.
- [ ] **Trägt der Ansatz bei virtio-Deskriptorringen?** Dort sind Felder **gerätesichtbar** und
      ändern sich nebenläufig — Gabbro beschreibt Daten, nicht Abläufe. Möglicherweise ist das
      die Grenze der Domäne, und dann gehört sie ins README.
- [ ] **Was passiert bei einem Formatfehler im Beschreiber selbst?** Gabbro beweist, dass der
      Leser dem Beschreiber entspricht — nicht, dass der Beschreiber der Wirklichkeit entspricht.
      Ein Gegenmittel wäre ein **Falsifikator** je Format (eine echte Byte-Folge aus der Praxis,
      die gelesen werden **muss**), nach dem Vorbild der Caprock-Identitätsgründe.

---

## Bewusst NICHT auf dieser Liste

Damit später niemand denkt, es sei vergessen worden:

* **Allzweck-Konstrukte** (Funktionen, Schleifen, Arithmetik über Feldern). Sobald Gabbro rechnen
  kann, kehrt die Spezifikationslast zurück, der es ausweicht.
* **Nebenläufigkeit.** Auch SPARK kann „der Aufrufer hält den Spinlock" nicht ausdrücken.
* **V−1: `check` als Rust-MAKROBIBLIOTHEK, ohne Sprache** — der billigste Test des ganzen
  Vollsprachen-Zweigs. Rückwirkend gegen die 33 M-Fallen halten, jede mit Mutation. **Fängt sie
  weniger als 5, fällt die einzige Begründung, die Gabbro allein gehört.** Steht vor jeder
  Übersetzerarbeit — und ist auch dann nützlich, wenn Gabbro nie entsteht.
* **GEFAHREN für Stufe 1 und 3 (2026-08-13): beide Kennzahlen fielen gegen den Zweig.** Verus
  findet S1a/S1b am echten Code für 0 Zeilen, und „der Aufrufer hält den Lock" ist dort eine
  Bedingung. Offen bleibt nur: **Sperrordnung ⇒ Deadlockfreiheit** (Falle 41) und
  **`haelt_hoechstens`** (Falle 93) — beides in Verus **nicht** gemessen, und beides ist das, was von
  Stufe 1 übrig ist.
* **Stufe 2 gegen die richtige Grundlinie messen: NICHT Verus, sondern `tock-registers`/`svd2rust`.**
  Typisierte Registerzugriffe sind eine Rust-Bibliothek. Die Frage ist, was ihr fehlt — Übergänge
  über Bits, Bedingungen über Registergrenzen, Barrierendomäne im Typ.
* **Für jede weitere Stufe die Gegenrechnung führen: was können Rust + Verus + Loom heute schon?** `Parked`
  hat Rust gefunden, die abgeschwächte Ordnung fand Loom, Ressourcen-Invarianten kann Verus über
  lineare Ghost-Permissions. Nur der Rest rechtfertigt eine Sprache. Ohne diese Rechnung je Stufe
  ist `VOLLDECKUNG.md` ein Plan gegen einen Gegner, den niemand gemessen hat.
* **Die Deckungsquote ist gemessen (2026-08-13): ≤ 9 % von 66 651 Zeilen Caprock**, hart 4,6 %,
  bei Zuschnitt (a) noch 3,0 %. Damit hat der Kernel-Zweig erstmals eine Zahl — und sie sagt Nein
  zum Wort *Rewrite*. **Offen ist die Umkehrung, die die nützlichere Frage ist:** lohnt ein
  Übersetzer für genau diese 3 081 Zeilen? Das ist Phase −1 (Basisrate), jetzt mit einem Nenner.
* **Die drei Fehler prüfen, die Gabbro WIRKLICH getötet hätte** — statt der Liste dessen, was
  fehlt. Kandidaten: **D0** (lauffähig vor `bind_pd` — ein `state`-Übergang, den es nicht gäbe),
  **S1a/S1b** (`traverse`/Arithmetik-Vorbedingung), **C9e** (5 Seiten in einen 4-Farben-Streifen —
  eine Breitenvorbedingung). Gegenprobe zu jedem: hätte **Rust-heute oder Verus** es auch gefunden?
  Bei D0 lautet die Antwort vermutlich ja (`Parked` hat es strukturell erledigt) — dann zählt es
  wie `Parked` **gegen** den Zweig.
* **Der Geltungsbereich der Beweisbarkeit steht jetzt in `DESIGN.md` als Tabelle** — offen ist die
  Gegenprobe: **ein Konstrukt suchen, dessen Zeile zu stark ist.** Die Tabelle ist neu und hat
  dieselbe Vorgeschichte wie die zwei Überschreibungen in `HISTORIE.md`.
* **Mutationsprobe auf der ANNOTATIONSEMISSION**, nicht nur auf der Codeemission. Ein Erzeuger, der
  abgeschwächte Verträge ausgibt, erzeugt einen grünen Beweis über eine schwächere Aussage. Der
  stimmig abgeschwächte Fall (Code **und** Vertrag) wird von **keinem** Beweis gefangen — nur vom
  Differenztest gegen die Handschrift. Das ist dessen benannte Aufgabe.
* **Annahmenmenge ins Erzeugnis emittieren** („bewiesen unter A1…An"), als **Menge von Namen** mit
  Klasse, nicht als Zahl. Ein Beweis, dessen Annahmenmenge der Verbraucher nicht kennt, hat keine
  Reichweite.
* **Die SPARK-Übernahmeleiter nachprüfen** (Stone/Bronze/Silber/Gold/Platinum und was jede Stufe
  bedeutet). Sie trägt in `README` und `DESIGN.md` ein Argument und ist aus dem Gedächtnis zitiert;
  von dieser Maschine aus war keine Dokumentation greifbar.
* **Für den Kernel-Zweig: der TAL-Teil hat keinen nachgelagerten Beweiser.** Verus beweist keine
  Inline-Assembler-Semantik, Frama-C/WP erst recht nicht; ein TAL-Typsystem im Erzeuger prüft sich
  selbst. Die haltbare Aussage ist „vertrauenswürdige Fläche schrumpft von 153 Stellen auf eine",
  nicht „geprüft". Offen: ob das reicht, um das Tor zu rechtfertigen.

* **Rust-Ausgabe.** Erst wenn C trägt — zwei Ziele verdoppeln die Prüffläche, **und die zweite
  Emission ist nicht nur Aufwand, sondern eine unbewiesene Entsprechung** (bewiesen in Rust,
  ausgeliefert in C). Die Reihenfolge „C zuerst" stammt aus der alten These; unter der neuen ist
  sie zu prüfen, weil der nächstliegende Beweiser Verus ist und Rust will. S. `ROADMAP.md`.
* **Seitentabellen-Beschreiber.** Verlockend, aber Hardwarevertrag: ein falscher Beschreiber
  erzeugt einen beweisbar korrekten falschen Kernel.
