# NLnet Restack — Leitfaden für den Antrag

**Frist: 3. November 2026, 12:00 CET (Mittag, nicht Mitternacht).**
Office Hour: Mittwoch 30. September 2026, 16:00 CEST, Matrix-Raum, Fragen vorab per Cryptpad.

---

## 0. Wie dieser Leitfaden gemeint ist

Er enthält **keine Sätze zum Einsetzen**, sondern je Feld: was dahinter gefragt wird, welches
deiner Materialien am stärksten ist, und was zu vermeiden ist.

Das hat einen Grund. NLnets GenAI-Richtlinie erlaubt KI-Hilfe beim Schreiben, verlangt dann aber
ein Protokoll mit **Modell, Zeitpunkt, den Prompts und den unbearbeiteten Ausgaben**. Selbst
geschrieben ist der saubere Weg — und bei einem Projekt, dessen Prüfstein *„Beitragende müssen
ihre Entwurfsentscheidungen verstehen und erklären können"* lautet, ist ein Antrag in deinen
eigenen Worten auch inhaltlich besser.

---

## 1. Drei Dinge im Repository, vor dem Schreiben

**1.1 README-Abschnitt zur Entwicklungsmethode.** Die Richtlinie verlangt bei substanzieller
GenAI-Nutzung eine **grobe Beschreibung, typischerweise im README**, plus Dokumentation auf
Commit-Ebene.

Den Commit-Teil erfüllst du bereits vorbildlich: jeder Commit trägt `Co-Authored-By` mit
Modellversion und Sitzungslink. Was fehlt, ist der README-Abschnitt.

*Warum das wichtig ist:* ein Gutachter klont das Repository und sieht tausende Commits mit
Modell-Koautorschaft. **Unerklärt liest sich das als generiertes Projekt. Erklärt liest es sich
als vorbildliche Befolgung.** Es gibt keine dritte Möglichkeit, und du entscheidest, welche.

**1.2 Die Zehn-Minuten-Nachprüfung auf die Vorderseite.** Klonen, bauen, Axiomenliste sehen —
in den ersten Bildschirm des README. Das ist der erste Klick des Gutachters, und es ist dein
stärkstes Argument. Es darf nicht auf Seite drei stehen.

**1.3 Die Zahlen nachmessen.** Alles unten in §4 ist über die letzten Tage gemessen, und dein
Baum bewegt sich um zweistellige Commitzahlen am Tag. Vor dem Einreichen alles neu fahren — das
ist ohnehin deine eigene Regel.

---

## 2. Die Felder

### Fund

**Restack.** CodeSupply ist Lieferketten-Metadaten und Regulierungs-Compliance — nicht deins.

### Proposal title

Nenne den **Liefergegenstand, nicht die Sprache**. Der Titel soll sagen, was am Ende existiert
und benutzbar ist. „Gabbro" als Name gehört in den Text, nicht in die Titelzeile — ein Gutachter
liest hundert Titel und muss bei deinem wissen, was hinterher da ist.

### Project website(s) / repositories

Der GitHub-Link. Siehe §1.2 — dieser Link ist das Feld mit der höchsten Wirkung im ganzen
Formular, weil er als einziges nachprüfbar ist.

### Summary (max. 1000 Zeichen)

Das schwerste Feld, weil 1000 Zeichen sehr wenig sind. Reihenfolge, die funktioniert:

1. **Was am Ende existiert** — der verifizierte Paketfilter, lauffähig.
2. **Warum das jemandem nützt, der dich nicht kennt** — er läuft auf gewöhnlichem Linux.
3. **Woran man sieht, dass es tragen wird** — ein Nebensatz zum bewiesenen Zielsatz.

Führe mit dem Artefakt, nicht mit der Sprache. „Eine Sprache, die Verifikation billig macht" ist
eine Behauptung; „eine Firewall, deren Umgehungsfreiheit maschinengeprüft ist" ist ein Ding.

**Nicht** hineinnehmen: CaprockOS, die Cloud-Plattform, die elf Klassen, die Übersetzungs-
validierung im Detail. Alles davon gehört in spätere Felder.

### Proposed effort

**50 000.** Das ist die Obergrenze für einen Erstantrag. Darüber verlangt NLnet ein
Sicherheitsaudit und kann Auszahlungen von dessen Ergebnis abhängig machen — für einen Erstantrag
unnötige Umstände.

Zur Einordnung für deine Dreijahresplanung: Folgeanträge bis 150 000, Lebenszeitgrenze je
Empfänger 500 000. Der Weg ist **gestaffelt gedacht** — liefern, dann wiederkommen.

### Budget breakdown (max. 4000 Zeichen)

Sie fragen drei Dinge: **Aufgaben mit Aufwand · den Satz · die Auslagen.** Also genau diese drei
Blöcke, in dieser Reihenfolge, ohne Prosa dazwischen.

**Aufgaben:** vier bis sechs, jede benannt, jede mit grober Stundenzahl. Sie sollen wie
Meilensteine aussehen, weil NLnet gegen Meilensteine auszahlt. Eine Aufgabe, die man nicht als
erledigt oder nicht erledigt erkennen kann, ist keine.

**Satz:** einer, genannt. Nicht mehrere, nicht verschachtelt.

**Auslagen**, und hier die drei Fallen:

- **Die Bauserverzeile als öffentliche Nachprüfbarkeit begründen, nicht als Entwicklerbedarf.**
  Der Satz, der sie trägt: *wenn das Nachprüfen des Beweises eine Maschine braucht, die niemand
  hat, ist „jeder kann es nachrechnen" falsch.* Eine öffentliche CI, die bei jedem Commit neu
  baut und die Axiomenliste veröffentlicht, ist damit ein Ergebnis und kein Gemeinkostenposten.
  Vorher messen (siehe §5), damit eine Zahl danebensteht.
- **Keine Position „KI-Abonnements" als Blickfang.** Restack schließt KI-*Projekte* aus; das
  trifft dich nicht, aber eine fettgedruckte KI-Zeile zieht Aufmerksamkeit, die du woanders
  brauchst. Als Teil einer Werkzeugzeile ist es unauffällig und ehrlich — es *ist*
  Entwicklungswerkzeug.
- **Keine drei Jahre.** Das Arbeitsprogramm ist zwölf Monate. Laufende Kosten für drei Jahre in
  einem Zwölfmonatsantrag passen strukturell nicht, und der Folgeantrag ist vorgesehen.

### Comparison with other efforts (max. 4000 Zeichen)

**Dein stärkstes Feld. Hier die meiste Sorgfalt.** Ein Gutachter, der Verifikation kennt, liest
zuerst hier, und ein dünner Vergleich erledigt einen Antrag schneller als jede technische
Schwäche.

Der Kern in einer Achse — und das ist der Satz, um den herum das Feld gebaut wird:

> **Die anderen machen den Beweis billiger. Gabbro nimmt ihn weg.**

Die Vergleichspunkte stehen in §3. Nimm alle, je zwei bis drei Zeilen; Vollständigkeit ist hier
wichtiger als Tiefe, weil sie zeigt, dass du das Feld kennst.

**Und beantworte den Nebensatz ausdrücklich:** *„Have you considered contributing to any of the
others?"* Wer ihn übergeht, fällt auf. Deine ehrliche Antwort ist eine gute: der Unterschied
liegt auf genau der Achse, die die Hypothese ausmacht — zu SPARK oder Verus beizutragen hätte
sie nicht geprüft, sondern umgangen.

### Technical challenges (max. 4000 Zeichen)

**Nenne die, zu denen du Zahlen hast.** Ein Abschnitt mit Messungen liest sich als Kompetenz,
einer mit Allgemeinheiten als Pflichtübung — und Gutachter sehen sehr viele Pflichtübungen.

Die echten, in der Reihenfolge ihrer Größe:

- **T2 existiert nicht.** Der Korrespondenz-Nachprüfer ist das Stück, das die Kette schließt,
  und es ist entworfen, nicht gebaut. Ohne ihn trägt kein Programm ein Zertifikat durchgehend.
- **Der nebenläufige Teil ist forschungsgroß** und ausdrücklich außerhalb dieses Antrags —
  Modelllauf gegen C-Lauf mit Verschränkung. Das *zu sagen* ist ein Stärkezeichen, kein
  Schwächezeichen.
- **Zeremonie- und Absagequote auf echtem fremdem Code.** Die Zahl, die historisch über Projekte
  dieser Art entscheidet; ATS ist daran gestorben, nicht an Unsolidität. Du misst sie bereits.
- **Beweisprüfzeit und Speicherbedarf**, mit den gemessenen Werten.
- **Der C-Compiler bleibt in der Vertrauensbasis**, mit CompCert als benannter realistischer
  Antwort und der Messung „die erzeugten Formen gegen CompCerts Teilmenge halten" als Schritt.

**Nichts kleinreden.** Dein ganzer Ordner ist darauf gebaut, das Gegenteil zu tun; das soll man
dem Antrag anmerken.

### Ecosystem (max. 2000 Zeichen)

**Dein schwächstes Feld — hier arbeite am härtesten.** Die Frage dahinter lautet: *hängt das an
einer Person, und wer außer ihr profitiert?*

- **Abhängigkeiten:** Lean 4, Isabelle, ein C-Compiler, sonst nichts. Null externe
  Rust-Abhängigkeiten ist hier ein Verkaufsargument — es gibt keine Lieferkette zu vertrauen.
- **Nutzer:** Caprock; die unabhängige kommerzielle Plattform, die es einsetzen will; und mit
  dem Paketfilter jeder, der eine verifizierte Komponente auf Linux laufen lassen will, ohne die
  Sprache zu lernen.
- **Engagement — werde konkret, mit Namen und Zeitpunkten.** Die seL4- und Lean-Gemeinden sind
  die naheliegenden Gegenüber; beide haben offene Kanäle. „Wir werden die Community einbinden"
  ist nichts, „wir stellen das Ergebnis dort und dort vor" ist etwas.

Wenn du bis dahin **eine zweite Person** benennen kannst, und sei es für Review, gehört sie
hierher. Es ist die Antwort auf die Frage, die sonst unbeantwortet bleibt.

### Background (max. 2000 Zeichen)

Das Repository ist die Antwort: ein Compiler, ein Korpus, ein bewiesener Zielsatz, in zwei
Monaten. Zahlen aus §4.

**Und hier gehört die Entwicklungsmethode hin**, in eigenen Worten: wie du mit Agenten arbeitest,
dass jeder Commit es ausweist, und — als Beleg, dass ein Mensch versteht, was dort steht — der
Zielsatz mit seiner Axiomenliste. Die Richtlinie verlangt genau diese menschliche
Rechenschaftsfähigkeit; du erfüllst sie, also sag es, statt zu hoffen, dass es niemandem
auffällt.

### Other funding sources (max. 1000 Zeichen)

Velves Unterstützung **und** der Prototype-Fund-Antrag, falls du ihn stellst. Beides offenlegen.

Ein später entdeckter Parallelantrag ist ungleich schlimmer als ein genannter — und
Doppelförderung derselben Stunden ist ein administratives Problem, das man vorher klärt und nicht
nachher.

### AI disclosure

Ehrlich, und es kostet dich nichts. Wenn du den Antrag selbst schreibst: das sagen, dazu die
Entwicklungsmethode und der Verweis auf den README-Abschnitt aus §1.1.

---

## 3. Die Vergleichspunkte, je mit ihrer Unterscheidung

| | Was es ist | Dein Unterschied |
|---|---|---|
| **seL4** | verifizierter Mikrokernel, ~20:1, verifizierte Konfiguration einkernig ohne DMA | bei dir sind Mehrkern und DMA gesetzt, nicht vertagt |
| **LionsOS** | System aus verifizierbaren Komponenten auf seL4, von derselben Gruppe | im eigenen Wortlaut *„does not have a concrete verification story yet"* — das Feld ist offen |
| **Pancake** | imperative Tiefsprache, verifizierter Compiler auf CakeML-Unterbau, für Treiber, frei | macht interaktives Beweisen billiger; du nimmst den Beweis weg |
| **Ironclad** | Unix-artiger Kernel in SPARK/Ada, teilweise verifiziert, NLnet-gefördert | SPARK ist SMT-gestützt — dieselbe Achse |
| **CertiKOS** | verifizierter nebenläufiger Kernel, akademisch | die Referenz dafür, dass Nebenläufigkeit beweisbar ist |
| **ProvenCore** | kommerzieller verifizierter Mikrokernel und TEE-OS | der kommerzielle Bezugspunkt |
| **SPARK, Verus, Dafny** | SMT-gestützte Verifikation, industriell erprobt | Vorhersagbarkeit statt Zeitschranken; Amortisation statt Arbeit je Programm |
| **ATS** | abhängige und lineare Typen, übersetzt nach C | dieselbe Ambition, am Beweisaufwand für den Nutzer gescheitert |
| **Ivy** | Verifikation im entscheidbaren Fragment | der dritte Weg: Löser, der terminiert. Kennen und benennen |
| **Vigor-Linie** | verifizierte Netzwerkfunktionen und NATs | dein Vergleichsmaßstab für den Paketfilter |

**Zur Instabilität**, falls du sie belegen willst statt sie zu behaupten: es gibt eine eigene
*Instability Track* bei SMT-COMP, eine POPL-2025-Arbeit zur Beweisstabilität, ein Werkzeug namens
Cazamariposas nur zum Aufspüren, und Dafnys eigenen Blogbeitrag zur Verifikationsbrüchigkeit.
Wenn ein Feld eine Wettbewerbskategorie für seine eigene Unzuverlässigkeit braucht, ist das ein
Beleg und kein Vorwurf.

---

## 4. Zahlen zum Danebenlegen

**Alle über die letzten Tage gemessen — vor dem Einreichen neu fahren.**

**Der Zielsatz**
`gabbro_ziel`, `ziel_aus`, `gabbro_ziel_zeuge`, `zweiFaeden_erfuellbar_gilt`,
`zweiFaeden_bewegt_gilt` — alle `[propext, Classical.choice, Quot.sound]`. Kein `sorryAx`, kein
`ofReduceBool`, kein eigenes Axiom. Null `sorry` in allen neun Dateien des Zielsatz-Moduls.
Positiver Zeuge auf einem nebenläufigen Programm, Nichtdegeneriertheit als eigener Satz.

**Der Prüfer**
12 Pässe, 3 vollständig, 9 getragen · 386 Diagnosen · 177 EBNF-Regeln, Vokabular deckt jedes
Terminal · 155 Passsätze, 147 gemessen, 2 argumentiert, 6 vermutet, 0 bewiesen

**Der Korpus**
105 saubere Beispiele · 661 Giftdateien · 883 Tests · 232 von 232 Einheiten übersetzen unter
`-Werror` bei `-O0` und `-O2`, 35 zusätzlich gegen Handschrift geprüft

**Die Qualitätsmessung**
409 Mutationen, 383 Anker greifen, 375 von 376 gültigen Mutationen gefangen ·
Blindstellen 74 blind · 174 besetzt · 24 nur im Gift · 12 ohne Zelle, von 285 Paaren

**Der Baum**
~127 000 Zeilen Rust über drei Crates, `forbid(unsafe_code)`, **null externe Abhängigkeiten** ·
15 Isabelle-Theorien, 3 512 Isar-Zeilen, 21 Schablonen davon 10 maschinengeprüft ·
über 2 400 Commits seit dem 13. August 2026

---

## 5. Vor dem Einreichen

- [ ] README-Abschnitt zur Entwicklungsmethode (§1.1) — **das Wichtigste auf dieser Liste**
- [ ] Zehn-Minuten-Nachprüfung auf die README-Vorderseite (§1.2)
- [ ] Alle Zahlen aus §4 neu messen
- [ ] Speicherspitze des Lean-Baus messen: `lake build -j1` gegen `-j4` gegen voreingestellt —
      entscheidet die Größe der Serverzeile, und eine Budgetzahl ohne Messung daneben ist in
      deinem Ordner ohnehin keine
- [ ] Fragen fürs Office Hour ins Cryptpad (§6)
- [ ] Prototype-Fund-Antrag entscheiden — Bewerbungsfenster 1. Oktober bis 30. November, eine
      Runde im Jahr, Förderung ab Juni 2027

---

## 6. Office Hour, 30. September 16:00 CEST

Matrix-Raum, Textchat, keine Anmeldung, Fragen vorab per Cryptpad — du musst nicht live dabei
sein. **Sie begutachten dort ausdrücklich keine Anträge vorab**, also keine Fragen der Form
„passt mein Projekt". Allgemeine Fragen, deren Antworten ändern, was du schreibst:

1. **Die GenAI-Richtlinie in der Praxis.** Was muss die grobe Beschreibung im README enthalten,
   wenn ein Projekt mit Agenten entwickelt wird und jeder Commit die Modellversion bereits
   ausweist? *Das Risiko mit dem größten vermeidbaren Schaden.*
2. **Budgetzusammensetzung.** Wie werden Hardware- und Infrastrukturposten im Verhältnis zur
   Arbeitszeit gesehen?
3. **Parallelanträge.** Wie offenlegen, und schadet es?
4. **Der gestaffelte Weg.** Wie läuft der Folgeantrag praktisch, und was macht ihn
   wahrscheinlich?
