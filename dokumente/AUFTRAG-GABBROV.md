# Auftrag — Manifest tragfähig machen und GabbroV bauen

Für eine frische Claude-Code-Sitzung im Gabbro-Baum. Ausgelegt auf autonome Arbeit über
Stunden: die Reihenfolge steht, die Tore stehen, §9 sagt, wann anzuhalten ist. Alles
außerhalb dieser Liste entscheidest du selbst.

Vorher lesen: `CLAUDE.md`, `SPRACHE.md` §0 · §8.3 · §15, `PFLICHTEN.md` (besonders die
«B13»-Zeile in F1), `GABBROV.md`, `programmlogik/gabbrov/V1.lean`.

---

## 0. Antworte zuerst, baue danach

Vier Sätze, bevor du etwas anfasst:

1. Warum die Umbuchung der drei `progress`-Klauseln in `zaehle-pflichten.py` gehört und
   nicht in die Tafel von `PFLICHTEN.md`.
2. Warum „vier Zeilen über Reihenfolge nicht sagbar" **keine** Lücke des Lean-Fragments ist.
3. Warum `aushaengen :: ensures #1` den eigenen Satz von §15 verletzt.
4. Warum eine rote Zeile in der Korrespondenztafel ein Fehlschlag ist und eine gelbe nicht
   (§7) — und warum das etwas anderes ist als eine unerfuellbare Forderung.

Weicht dein Verständnis ab, sag es und warte.

---

## 1. Die drei Erfolgskriterien

GabbroV hat **drei** Kriterien, nicht eines. Sie messen verschiedene Dinge und dürfen nicht
gegeneinander verrechnet werden.

### E1 — Vollständigkeit der Behandlung. Hart, ohne Ausnahme.

**Jede `obligation`-Zeile des Manifests bekommt ein Urteil.** Keine wird still übersprungen,
keine fällt bei einem Parserfehler durch, keine verschwindet, weil das Fragment sie nicht
ausdrücken kann — sie bekommt dann *unentschieden* mit Grund.

Prüfbar mit einem Kommando: Zeilenzahl im Manifest gegen Zeilenzahl im Ergebnis. **Gilt in
jedem Lauf, nicht nur am Ende.** Eine Abweichung ist ein Fehlschlag, kein Hinweis.

Das ist die Fassung von „ohne was zu vergessen", die tatsächlich prüfbar ist.

### E2 — Entscheidungsanteil. Mit namentlicher Ausnahmeliste.

Wie viele der behandelten Pflichten enden mit *bestanden* oder *widerlegt* statt
*unentschieden*.

**Anspruch: alle, außer den strukturell Unentscheidbaren — und die stehen namentlich da.**
Heute sind das vier: die Großschritt-Zeilen. `exec` hat keinen Zwischenzustand, also gibt es
keinen zu benennen; kein Fragment und kein Löser ändert das.

**Namentlich, nicht als Prozentsatz.** Ein Prozentsatz lässt die Ausnahmeliste still mit
jeder Pflicht wachsen, die sich als schwer erweist.

**Mechanik, damit das hält:** die Liste steht in `AUSNAHMEN.md`, eine Zeile je Pflicht mit
Name, Grund und Datum. Ein Wächter zählt sie und fällt, wenn die Zahl ohne einen Eintrag in
`HISTORIE.md` steigt. Ohne diesen Wächter ist E2 eine Absichtserklärung.

Eine Pflicht kommt nur auf die Liste, wenn der Grund **strukturell** ist — Semantik, nicht
Schwierigkeit. „Der Löser kommt nicht durch" ist *unentschieden*, keine Ausnahme.

### E3 — Kanaltreue. Hart, ohne Ausnahme.

**Die Korrespondenztafel (§7) hat keine rote Zeile.** Eine Spezifikation, die etwas sagt, das
kein Gabbro-Programm behaupten kann, ist ein Fehlschlag — nicht ein Befund, nicht ein
Haltepunkt.

E3 gilt für das Fragment, nicht je Lauf: die Prüfung findet statt, bevor eine Spezifikation
geschrieben wird. Ein Wächter hält die beiden Listen gegeneinander.

---

## 2. Erst die Bücher

Kein Code. Bringt die Zahlen in Ordnung, bevor neue dazukommen.

<!-- widerruf:aus -->
**2.1 G1 hatte nie eine Schwelle.** Der alte Auftrag schrieb „ein nennenswerter Teil", also
keine Zahl. „G1 feuert nicht" bei 56 von 66 ist ein Urteil, keine Messung. So nach
`HISTORIE.md`. **Setze keine Schwelle nachträglich** — das ist die eine Änderung, die alle
Zahlen gleichzeitig verbessert. E1 und E2 sind ab jetzt die Kriterien, und sie stehen vorher.
<!-- widerruf:an -->

*Ausgeführt am 2026-09-03; der ausgenommene Block darüber zitiert den widerrufenen Satz und
ist darum von `WG1` in `pruefe-widerruf.py` ausgenommen — die Anweisung, nicht der Befund.*

**2.2 Die Umbuchung bewegt den Nenner.** Drei `progress`-Klauseln sind in der Quelle bereits
`assume` und werden ein zweites Mal als Logikpflicht gebucht. Ergebnis heißt damit **56 von
64**. Beide Zahlen nennen, mit dem Grund dazwischen. **Die Änderung gehört in
`zaehle-pflichten.py`, nicht in die Tafel** — am 2026-08-20 standen drei Zahlen über einer
Sache, und die mit dem Suchweg war die falsche. `pruefe-zahlen.py` muss danach grün sein.

**2.3 Der Großschritt ist ein eigener Eintrag.** Nach `OFFEN.md` **und** als die vier ersten
Zeilen in `AUSNAHMEN.md`. Mit der Zuspitzung: genau diese Klasse — *„die Invariante fällt
dazwischen"* — ist der Kern von §8.3, also die Stelle, an der GabbroV den größten Wert
schaffen sollte. Nicht unter „vier Zeilen nicht sagbar" begraben.

**Tor 1:** `pruefe-zahlen.py` grün, neuer Nenner aus dem Befehl, `AUSNAHMEN.md` mit Wächter,
drei Einträge geschrieben.

---

## 3. Der Tagesversuch — vor dem Bau

**Fünf Pflichten aus den 56, Spezifikation in Lean, und nachsehen, ob ein SMT-Löser sie
überhaupt anfasst.** Kein Werkzeug, kein Gerüst, Handarbeit.

Die fünf werden **vor dem Ansehen** gezogen und protokolliert: nicht die leichtesten,
sondern durchmischt, darunter mindestens eine mit Tabellenidentität und eine
Zweizustandsrelation. Wenn dir eine auffällig gut passt, ist das ein Grund, sie **nicht** zu
nehmen.

Das beantwortet die Frage, die den Umfang des ganzen Projekts bestimmt: **wird GabbroV ein
Prüfer oder ein Vorsortierer?** Die interessanten Pflichten sind die, für die noch niemand
einen Beweis hat, und das sind meist die schweren. Ein Werkzeug, das die leichten schafft und
bei den schweren *unentschieden* sagt, hat den Zustand nicht verändert — die schweren waren
vorher offen und sind es nachher.

**Tor 2:** fünf Ergebnisse, je mit Löserausgabe. Berichten und **anhalten** — die Zahl
entscheidet, wie viel Bauaufwand gerechtfertigt ist, und das ist keine Agentenentscheidung.

---

## 4. Das Manifest trägt den Pflichttext

Defekt bei GabbroC, nicht bei GabbroVs Entwurf. §15 verspricht *„Nothing is silently lost"*;
eine Ordnungszahl, aus der man den Text nur durch Lesen der Quelle rekonstruiert, hält das
nicht.

Ziel je `obligation`-Zeile: **Name · Pflichttext · Anker (`Datei:Zeile`) · Klasse · Zustand**.

**Reihenfolge, und sie ist die halbe Regel.** `CLAUDE.md` hält fest, was passiert, wenn ein
Dokument sich vor seinen Wächtern bewegt: sieben lesen mit, vier werden still blind.

1. **Versionsfeld zuerst.** Jeder Leser verweigert eine unbekannte Version, statt sie zu
   missdeuten. Ohne das ist jede Formatänderung ein stiller Bruch.
2. Alle Leser auf beide Formate vorbereiten.
3. Erst dann das Format ändern.

Gegenprobe an fünf echten Zeilen aus `PFLICHTEN.md`, darunter eine aus F1 mit
Tabellenidentität: der Text muss ohne Blick in die Quelle verständlich sein.

**Tor 3:** Manifest trägt Text und Anker, Versionsfeld greift, alle Leser grün, volle
`abnahme.py` grün.

---

## 5. GabbroV — Gerüst

```
gabbrov pruefe --manifest <datei> --spez <Lean-Datei>
```

Drei Ausgänge: **bestanden** (geprüft, nicht vermutet) · **widerlegt** (mit Gegenbeispiel als
konkretem Zustand) · **unentschieden** (mit Pflichtname und Grund). *Unentschieden* schreibt
die Pflicht als `offen` zurück — der Zustand, in dem sie war.

**E1 ist im Werkzeug verdrahtet, nicht angehängt:** der Lauf endet mit einem Vergleich der
beiden Zeilenzahlen und bricht bei Abweichung ab. Ein Werkzeug, das seine eigene
Vollständigkeit nicht prüft, hat sie nicht.

**Solide, nicht vollständig.** *Bestanden* muss immer stimmen; *unentschieden* darf oft
vorkommen. Jede Optimierung, die diese Asymmetrie antastet, ist ein Fehler — auch wenn sie
E2 verbessert.

**Tor 4:** eine Pflicht durch alle drei Ausgänge, je ein Test. E1-Prüfung fällt, wenn man
ihr künstlich eine Zeile unterschlägt.

---

## 6. Vakuität — die billige Hälfte von V2

Braucht keine formalisierten Annahmen, und der Grund gehört ausformuliert in den Bericht:

> Annahmen verkleinern die Modellmenge. Ist eine Vorbedingung **ohne** sie unerfüllbar, ist
> sie es **mit** ihnen erst recht. Die Prüfung ist **solide in der Erkennungsrichtung und
> unvollständig**: sie findet einen Teil der vakuösen Fälle und meldet nie fälschlich einen.

Sonst liest später jemand „keine Vakuität gefunden" als „keine vorhanden" — dieselbe Klasse
wie ein Messlauf, der beim ersten Treffer abbricht. Die acht Annahmen bleiben deutsche Prosa;
**formalisiere sie nicht**, das steht auf der Halteliste.

**Tor 5:** über alle Pflichten der zehn Fragmente gelaufen, Befund protokolliert,
Richtungsaussage im Bericht.

---

## 7. Beide Kanäle bewegen sich zusammen — oder keiner

**Die Regel, die alles Weitere bindet:** eine Spezifikation, die etwas sagt, das kein
Gabbro-Programm behaupten kann, **gilt als Fehlschlag**. Nicht als Warnung, nicht als
Haltepunkt. Sie erzeugt eine Pflicht, die kein Programm erfüllen kann — die Lücke wandert
eine Ebene weiter und sieht dabei aus wie Fortschritt.

### Die Korrespondenztafel

Eine Laufzeitablehnung käme zu spät: dann steht die Divergenz schon im Fragment und jemand
hat sie eingebaut. Also eine Tafel, `programmlogik/gabbrov/KORRESPONDENZ.md`, eine Zeile je
Konstrukt des Lean-Fragments mit seinem benannten Gegenpart in Gabbros `pred`/`expr` — und
ein Wächter, der beide Listen gegeneinander hält. Dieselbe Form wie
`pruefe-grammatiktafel.py`.

**Zwei Richtungen, zwei Härten:**

| Divergenz | Bedeutung | Härte |
|---|---|---|
| Lean kann, Gabbro nicht | Spezifikation behauptet Unbehauptbares | **rot** — Fehlschlag, Fragment zurücknehmen oder Gabbro-Seite zuerst bauen |
| Gabbro kann, Lean nicht | Programm sagt etwas, worüber die Spezifikation schweigt | **gelb** — die Pflicht endet zwangsläufig *unentschieden*; nach `OFFEN.md` mit Namen |

Heute steht genau eine Zeile auf gelb: `PredArt::Erreicht` (7.2). Rot muss leer sein und
bleiben.

**Der Unterschied zur Unerfüllbarkeit.** „Kein Programm *kann es sagen*" ist die
Kanalfrage und Sache dieser Tafel. „Kein Programm *kann es erfüllen*" ist etwas anderes —
eine ausdrückbare, aber unerfüllbare Forderung — und fällt in die Erfüllbarkeitsprüfung aus
§6. Beide sind Fehlschläge, aber sie werden verschieden gefunden, und sie zu vermengen
verdeckt beide.

### Die drei Erweiterungen

Alle aus dem Gang durch die 66 belegt.

**7.1 Zweizustandsrelationen.** 20 der 66 nehmen Vor- und Nachzustand; `GABBROV.md` §7 sagt
„Prädikate über Werten" und ist zu eng. Reine Fragmentarbeit, kein Gabbro-Eingriff — `ensures`
kennt den Vorzustand bereits, die Korrespondenz steht also. Korrigiere auch den
Dokumenttext, nicht nur den Code.

**7.2 Beschränkte Erreichbarkeit**, fünf Zeilen. Die heutige gelbe Zeile: `PredArt::Erreicht`
existiert, eine Probe geht mit 0 Fehlern durch, der Lean-Kanal weist es beim Namen ab. Reine
Kanalarbeit, und sie räumt die Tafel.

**7.3 Aggregation — «B13», und zwingend in dieser Reihenfolge.** `refcount == count(s in
slots : s.object == o)` ist die Kernbuchhaltung des Capability-Systems. `PFLICHTEN.md` hat
die Ursache eingegrenzt: `count` ist reserviertes Wort ohne Produktion in `pred`/`expr`;
`anzahl(o)` parst an derselben Stelle. **Es kostet kein neues Sprachwort.** Der Rest ist
benannt: eine Kostenregel, eine Erzeugerschablone, ein Isabelle-Gegenstück. Bedarf gemessen
(W23): zwei saubere Korpusstellen, F1, und Caprocks K2, das `cap_space.rs` in Verus von Hand
trägt.

**Gabbro-Seite zuerst.** Umgekehrt wird die Tafel rot, und rot ist Fehlschlag — das ist
jetzt nicht mehr eine Bitte an dich, sondern ein Wächter.

### Kostentor für Sprachänderungen

Gabbro darf umgebaut werden, damit GabbroV trägt — aber „nicht zu teuer" braucht eine
Definition, sonst entscheidet sie sich selbst. Eine Änderung ist **billig genug**, wenn alle
vier gelten:

1. **kein neues Quellwort** — der Wortschatz ist geschlossen, 170 Terminale gegen 170 Vokabeln
2. **ein Passplatz** — sie passt in die bestehende Passfolge, ohne eine neue zu eröffnen
3. **Isabelle-Gegenstück baut** — gemessen mit `isabelle build`, nicht geschätzt
4. **`exec` bleibt unangetastet** — Großschrittigkeit trägt die vorhandenen Beweise mit

Fällt eine der vier, ist es ein Haltepunkt. **Die Kosten werden gemessen, nicht geschätzt:**
gebaut, gefahren, volle `abnahme.py`. Eine Kostenaussage ohne Lauf ist keine.

7.3 erfüllt alle vier nach heutigem Stand. Zeigt sich beim Bauen, dass eine fällt, halte an,
statt den Zuschnitt anzupassen.

**Tor 6:** Korrespondenztafel steht, Wächter grün, rote Spalte leer; V1.lean neu gefahren,
Zahl gestiegen, Datei druckt sie selbst; `AUSNAHMEN.md` unverändert.

---

## 8. Zertifikate — messen, nicht bauen

Z3 sucht, Leans Kern rechnet nach; ohne Zertifikat gilt *unentschieden*. Damit steht Z3 nicht
in der Vertrauensbasis, und das ist der ganze Zweck.

**In diesem Auftrag wird das nicht gebaut, sondern beziffert.** Die Zertifikatslage ist je
Theorie sehr verschieden — für Bitvektoren gibt es einen brauchbaren Weg, für Quantoren und
Arrays praktisch keinen. Ein Agent, der das als Bauauftrag bekommt, baut im Zweifel die
abgeschwächte Variante, in der Z3 doch geglaubt wird.

Also: **welcher Anteil der 56 fällt in Theorien mit brauchbarem Zertifikatspfad?** Eine Zahl
mit Ableitungskommando. Sie entscheidet G2, und G2 entscheidet zwischen zwei Wegen, die beide
unangenehm sind — Z3 in der Vertrauensbasis oder schwächere Automatisierung. Diese
Entscheidung gehört nicht dem Agenten.

**Tor 7:** die Zahl steht, mit Kommando. Berichten und anhalten.

---

## 9. Halteliste

Anhalten und fragen. Alles andere entscheidest du selbst.

- **Jede Schwellenänderung**, auch das nachträgliche Setzen einer fehlenden.
- **Jede Abschwächung eines Wächters.**
- **Jeder Zuwachs in `AUSNAHMEN.md`** über die vier Großschritt-Zeilen hinaus.
- **Jede rote Zeile in der Korrespondenztafel.** Sie ist ein Fehlschlag, kein Zustand, den
  man einträgt und weiterarbeitet. Entweder die Gabbro-Seite kommt zuerst, oder das Fragment
  wird zurückgenommen.
- **Jede Sprachänderung, bei der eines der vier Kostenkriterien fällt** (§7).
- **`exec`s Großschrittigkeit.** Sprachsemantik, trägt die Isabelle-Beweise mit.
- **Formalisierung der acht Annahmen.** Teure Hälfte, nicht in diesem Auftrag.
- **`../caprock-messbasis`** liegt schreibgeschützt. Vorschläge ins Protokoll.
- **`aarch64`** bleibt versiegelt.

Und nach Tor 2 und Tor 7 wird berichtet und gewartet, auch wenn nichts blockiert.

---

## 10. Arbeitsweise über Stunden

**Rechnen auf `ki-pc-fisch-101`, eigenes Verzeichnis** (`gabbro-v`), nie `gabbro-baum`. Vor
Laufbeginn `git checkout master && git pull --ff-only`. **Beide** Übertragungen in dasselbe
Verzeichnis, in dieser Reihenfolge:

```bash
rsync -rlpgoD --delete --exclude 'target/' --exclude '__pycache__/' --exclude '.claude/worktrees/' \
      ./ ki-pc-fisch-101:gabbro-v/
rsync -a beweise/ ki-pc-fisch-101:gabbro-v/beweise/
```

`-rlpgoD` und **nicht** `-a`: ohne das `t` bekommt jede übertragene Datei die aktuelle Zeit,
und genau das braucht `cargo`. Wer nur die erste fährt, bekommt `pruefe-beweise.sh`
**`OHNE NACHWEIS`** über tadellose Theorien — nach zwölf Minuten.

**Nicht mit `pgrep -f` warten.** Der Aufruf steht in der Kommandozeile der wartenden Shell,
das Muster findet sich selbst. `ps -C python3`, oder Ausgabe in eine Datei und deren letzte
Zeile lesen.

**`cargo test --no-fail-fast`**, immer. Kein Messlauf, der beim ersten Treffer abbricht — er
beantwortet „feuert mindestens eine" statt „welche feuern".

**Vor jedem lokalen Lauf `free -g` daneben.** Ein Abbruch aus Speichermangel ist kein Befund.

**Nach `abnahme.py --voll` ist die nächste `abnahme.py` rot**, und das ist kein Befund. Die
Heilung ist ein Bau, kein `touch` auf das Binärprogramm.

**Commit an jedem Tor**, über `arbeitsprotokoll/.commitmsg` + `./commit.sh` (R19). Ein Tor
ohne Commit läufst du beim nächsten Kontextverlust neu.

**`.md` im Baum ist Englisch.** Wächtermuster werden zweisprachig, **bevor** ein Dokument
sich bewegt.

**Jede Zahl mit Ableitungskommando** (W7).

**Wenn ein Tor blockiert**, geh zum nächsten unabhängigen Abschnitt und schreib das Hindernis
nach `OFFEN.md`. §2, §4 und §6 hängen nicht aneinander. Warte nur bei §9 und nach Tor 2 und 7.

**Selbstberichtigungen gehören in den Bericht, nicht still korrigiert.** Im letzten Lauf waren
zwei drin, und beide waren wertvoll.

---

## 11. Reihenfolge

§2 → §3 → **warten** → §4 → §5 → §6 → §7 → §8 → **warten**

§2 zuerst, weil dort keine Zeile Code entsteht und danach die Zahlen stimmen, gegen die alles
Weitere gemessen wird. §3 vor jedem Bau, weil sein Ergebnis bestimmt, wie viel Bau
gerechtfertigt ist.

Die Korrespondenztafel entsteht in §7, aber sie beschreibt einen Zustand, der schon heute
besteht. Wenn du beim Aufschreiben eine rote Zeile findest, die niemand kannte, ist das ein
Befund und gehört gemeldet, bevor du sie räumst.
