# Gabbro für ganz Caprock — und für beliebige Programme

**Was hier geplant wird, und was es kostet, steht vor dem Plan.**

Dieses Dokument verlässt den Zuschnitt, den `README.md` verteidigt. Es plant eine
**Allzweck-Systemsprache**. Damit fällt die Rechnung, die Gabbro billig machte — die geschlossene
Domäne —, und die Spezifikationslast kehrt zurück. **Die Linie wandert**, und `README.md` hat genau
das als den unbequemen Ausgang vorhergesagt: *dann ist Gabbro der Beweisassistent mit Syntax, dem es
ausweichen wollte.*

Die Messung dazu steht und wird nicht schöngeredet: die sieben Konstrukte decken heute **≤ 9 %** von
Caprock, hart **4,6 %**. Dieses Dokument plant die übrigen **91 %**.

> **Die Form ist eine SEHR ENGE Sprache, ungefähr so ausdrucksstark wie C** — nicht ein Katalog aus
> einem Schlüsselwort je Fehlerklasse. Die erste Fassung dieses Dokuments war genau das (zwanzig
> Konstrukte) und ist in §2 berichtigt. **Vier Mechanismen, zwei Deklarationsregeln**; alles andere
> fällt als Bibliothek heraus.

Stand 2026-08-13. **Nichts davon ist gebaut.**

---

## 1. Die Evidenz — 100 bezahlte Fallen, klassifiziert

Ein Plan aus Konstrukten, die jemand für gut hält, ist ein Wunschzettel. Die Konstrukte unten sind
aus der **Basisrate** abgeleitet: den 100 Einträgen der Liste „Fallen, die dieses Projekt bereits
bezahlt hat". Jeder Eintrag ist einzeln klassifiziert in
[`fallen-klassifikation.tsv`](fallen-klassifikation.tsv); die Zahlen unten sind mit
`./zaehle-fallen.sh` **abgeleitet**, nicht danebengeschrieben.

| Klasse | Anteil | heisst |
|---|---|---|
| **S** — Sprache | **36 %** | ein Konstrukt macht es unformulierbar |
| **M** — Messdisziplin | **36 %** | der Prüfer war das Problem, nicht der Code |
| **W** — Werkzeug/Prozess/Bau | **18 %** | CI, git, Cargo, Skripte — **keine Sprache hilft** |
| **B** — Bedeutung | **10 %** | der Beschreiber war falsch — **keine Sprache hilft je** |

**Damit ist die Obergrenze für den Sprachanteil 72 %, nicht 100 %.** 28 der 100 Fallen wären auch in
einer perfekten Sprache genauso passiert.

### Der Befund, der den Plan umstellt

Aufgeschlüsselt nach Konstrukt sieht die Verteilung so aus:

| Konstrukt | getötete Fallen |
|---|---|
| **`check`** (Messdisziplin als Konstrukt) | **33** |
| `linear` (echte Linearität) | 5 |
| `device` (Registerbeschreiber) | 5 |
| `assume`/`falsifier` | 3 |
| `lock`, `region`, `wirkung`, `einheit`, `grundmenge`, `absage`, `ableitung`, `stellentyp`, `arithmetik` | je 2 |
| `state`, `atomic`, `barrier`, `bitfeld`, `platzierung`, `menge`, `recht` | je 1 |

> **Das wertvollste Konstrukt einer Gabbro-Vollversion ist keine Typsystem-Eigenschaft.**
> Es ist die **Messdisziplin dieses Projekts, in die Sprache gezogen** — und sie tötet mehr Fallen
> (33) als alle Typkonstrukte zusammen (S = 36, verteilt auf zwanzig Konstrukte, das grösste mit 5).

Das passt zu der anderen Zahl, die beim Messen anfiel: **15,7 % von Caprock sind Berichts-, Mess-
und Selbsttestgerüst**, und das ist der Teil, der die Fehler gefunden hat. Keine vorhandene Sprache
— nicht Rust, nicht SPARK, nicht Verus, nicht F\*, nicht ATS — sagt darüber irgendetwas.

**Wenn dieser Ordner eine Daseinsberechtigung als Vollsprache hat, dann hier.** Alles andere ist
Nachbau von Vorhandenem.

---

## 2. BERICHTIGUNG: die erste Fassung war eine Merkmalsliste, keine Sprache

Sie führte **zwanzig** Konstrukte — `device`, `lock`, `atomic`, `barrier`, `bitfeld`, `einheit`,
`menge`, `recht`, `platzierung`, `grundmenge`, `ableitung`, `stellentyp`, `absage`, `region`,
`linear`, `wirkung`, `state`, `arithmetik`, `check` … — eines je Fehlerklasse. Das ist die
naheliegende Ableitung aus einer Fallenliste und der falsche Schluss: **eine Sprache, die für jeden
bezahlten Fehler ein Schlüsselwort bekommt, ist ein Katalog.** Sie wächst mit jedem Fund, und
niemand kann sie mehr im Kopf halten.

Gefragt ist das Gegenteil: **eine sehr enge Sprache, ungefähr so ausdrucksstark wie C**, aus deren
wenigen Mechanismen die zwanzig als **Bibliothek oder Deklaration** herausfallen.

> **Gabbro = C ohne seine Löcher, plus zwei Dinge.**
> Die zwei sind **Bereichstypen** und **lineare Werte (auch geisterhafte)**. Alles andere ist eine
> **Einschränkung** von C, keine Erweiterung.

---

## 3. Der Kern — vier Mechanismen und zwei Deklarationsregeln

### M1 — Bereichstypen

Ganzzahlen tragen ihren **Wertebereich**, und jede Operation muss darin bleiben. Das ist Adas
Trick, und **genau er** hat S1a/S1b gefunden — nicht „Ada ist sicherer".

```gabbro
type SlotIdx  = u32 in 0 .. NSLOTS-1
type Refcount = u32 in 0 .. u32'max
type Zyklen   = u64 in 1 .. u64'max      -- Null ist ein Befund, kein Messwert
```

### M2 — Lineare Werte, auch geisterhafte

Ein linearer Wert **muss** verbraucht werden; ein geisterhafter existiert nur im Beweis und wird
vor der Codeerzeugung gelöscht (**kein Byte, keine Halde** — an Verus gemessen).

```gabbro
linear       type Parked                 -- muss zugelassen werden
linear ghost type Hält(CAPS)             -- Sperrbeleg, kostenlos
linear ghost type Pflicht(check)         -- eine unerfuellte Pruefzusage
```

### M3 — Adressräume und Zugriffsrechte am Zeiger

Ein Zeiger trägt **wohin** er zeigt und **was** man damit darf. C hat das als Erweiterung; hier
ist es die Voreinstellung.

```gabbro
ptr<mmio, write_only>   gcmd            -- ein Lesen zum Zurueckschreiben ist nicht schreibbar
ptr<dma,  read_write>   puffer
ptr<code, execute@ring3> sonde
```

Barrieren gehören zum Adressraum, nicht zur Architektur — `dsb sy` gegen `dmb ish` ist keine
Stilfrage mehr, sondern folgt aus `mmio` gegen `normal`.

### M4 — Kein ungeprüfter Index, keine unbegrenzte Schleife

Indizieren geht nur mit einem Beleg der Zugehörigkeit; jede Schleife nennt ihr Abstiegsmass.
`traverse` ist die bequeme Schreibweise dafür, kein eigener Mechanismus.

### D1/D2 — die zwei Deklarationsregeln

* **Undurchsichtige Neutypen ohne implizite Umwandlung.** `Pa`, `Iova`, `Farben`, `MaskenBits`
  sind verschiedene Typen — C's `typedef` ist durchsichtig, das ist das Loch.
* **Vollständige Layouts, kein Auffangzweig.** Jedes Bit eines Wortes ist benannt, jede Aufzählung
  ist erschöpfend.

### Was C hat und bleibt

Funktionen, Zeiger, `struct`, feste Breiten, Kontrollfluss, Funktionszeiger, explizite Umwandlung
zwischen **verträglichen** Typen. **Was wegfällt:** implizite Umwandlung, `void*`, Zeigerarithmetik
ohne Grundlage, `goto`, Auffangzweige, `union` als Umdeutung (das kann M3), Präprozessor.

---

## 3b. Die zwanzig fallen heraus — als Bibliothek, nicht als Syntax

**Das ist der Test der Reduktion.** Bleibt eine Zeile ohne Ableitung, fehlt ein Mechanismus.

| vormals „Konstrukt" | folgt aus | wie |
|---|---|---|
| `einheit` (Pa/Iova/Farben) | **D1** | undurchsichtiger Neutyp |
| `arithmetik` (S1b) | **M1** | `Refcount` verlässt seinen Bereich nicht |
| `absage`, `grundmenge` | **D2** | erschöpfende Aufzählung, kein Auffangzweig |
| `bitfeld` (Marke auf Bit 63) | **D2** | vollständiges Layout — das Zahlenfeld ist belegt |
| `menge` statt Kardinalzahl | Bibliothek | ein Feldtyp über M1 |
| `ableitung` | `const`-Auswertung | hat C auch, nur ohne Prüfung |
| `stellentyp` (Konstruktor je Stelle) | **M2** + Modulgrenze | undurchsichtig, ein Erzeuger |
| `recht` (lesen ≠ schreiben) | **M3** | zwei Zeigerrechte, nicht eine Zeile mit zwei Richtungen |
| `device`, Registerklassen | **M3** + **D2** | `mmio` + `write_only` + vollständiges Layout |
| `barrier`-Domäne | **M3** | folgt aus dem Adressraum |
| `platzierung` (`.user_text`) | **M3** | `code`-Raum mit `execute@ring3` |
| `region`, Eigentum | **M2** | ein linearer Block ist seine Region |
| `linear` (`Parked`) | **M2** | der Mechanismus selbst |
| `state` (Typzustand, x2APIC) | **M2** | linearer Wert, dessen Typ den Zustand trägt |
| `lock` / `held(L)` | **M2** | `linear ghost Hält(L)` — an Verus **gemessen**, dass das trägt |
| Sperr**ordnung** ⇒ Deadlockfreiheit | **M2 + M1** | die Stufe ist ein Bereichstyp, Nehmen verlangt echt kleinere Stufe |
| `atomic`-Veröffentlichung | **M2** | `release` gibt einen Geisterbeleg ab, `acquire` nimmt ihn |
| `wirkung` (Global/Depends) | **M2** | Wirkungen **sind** geisterhafte Fähigkeiten im Parameter |
| `traverse` (S1a) | **M4** | Schreibweise, kein Mechanismus |
| `format` / `table` | Bibliothek | Deklarationen über M1/M3/D2 |
| **`check`** | **M2** | **s. u. — die schönste Ableitung** |

### `check` ist keine Sonderform, sondern eine lineare Pflicht

Das Konstrukt mit den 33 getöteten Fallen braucht **kein eigenes Schlüsselwort**:

* Ein `check` erzeugt ein `linear ghost Pflicht`. **Wer sie nicht verbraucht, übersetzt nicht** —
  das ist wörtlich „ein `check`, der in keiner Gatterliste steht, ist ein Fehler" (Falle 17, und
  das `all_done()`-Loch 21 gegen 24), und es fällt aus M2 heraus statt aus einer Sonderregel.
* Die **Sprechprobe** ist eine zweite Pflicht, die nur ein *fehlgeschlagener* Lauf verbraucht.
* Die **Untergrenze** ist M1: eine gemessene Grösse mit `in 1 ..` kann nicht null melden.
* „Der gemessene Pfad schreibt die Grösse selbst" ist ein **Schreibrecht** — M3.

**Damit bleibt die These dieses Ordners bestehen und wird kleiner:** das Wertvollste ist nicht ein
Prüf-Schlüsselwort, sondern dass **Prüfzusagen dieselben linearen Werte sind wie Ressourcen.**

### Was NICHT herausfällt — und darum ehrlich danebensteht

| | |
|---|---|
| **Verträge** (`requires`/`ensures` über deklarierte Prädikate) | nötig für Falle 1/2 (Bedingung über Registergrenzen). Damit ist die Linie gewandert, wie `README.md` vorhergesagt hat — und **allgemeine Quantoren über Rechenausdrücke bleiben trotzdem draussen** |
| **Der Eintritt (Assembler)** | M1–M4 sagen nichts über Registerabdrücke. Bleibt aussen, ohne Beweiser, und tötet **0** bezahlte Fallen |
| **Fortschritt** (Aushungern, D8) | kein Mechanismus adressiert ihn |

## 4. Was auch dann nicht besser wird — 28 %

| | | Beispiel |
|---|---|---|
| **W (18)** | Werkzeug, Bau, Prozess | `.git/info/exclude`; `grep -q` unter `pipefail`; ein CI-Gate im Format des falschen Servers; zwei Suiten, die dasselbe Gerät verschieden aufsetzen |
| **B (10)** | Bedeutung | „unten zuerst" war ein Zufall der Grössenrelation; der Lader meldet seinen eigenen Speicher als frei; eine Ablage je Rolle |

Dazu die Hardware: `assume`/`falsifier` macht Annahmen **zählbar**, nicht wahr.

**Ein Rewrite, der 100 % erwartet, rechnet mit 72 % — im besten Fall, bei perfekter Umsetzung
jeder Stufe.**

---

## 4b. AUSGELÖST 2026-08-13: Abbruchbedingung 2 hat für M2 gegriffen

Die Gegenrechnung „was können Rust + Verus + Loom heute schon?" ist für den schwersten Posten
gefahren, und sie ist **gegen** diesen Plan ausgegangen.

| Stufe | gemessener Stand gegen Verus/Rust heute |
|---|---|
| **M2 am Sperrbeleg** | **Kopfbegründung gefallen.** „Der Aufrufer hält den Lock" ist in Verus ein `tracked`-Zeuge: richtiger Kern `verified`, fremder Kern Beweisfehler, selbstgebauter Beleg Typfehler — `no_std`, ohne Byte im Erzeugnis. **Ungemessen bleiben** Sperrordnung ⇒ Deadlockfreiheit und `haelt_hoechstens`; Falle 41 und 93 sind damit noch nicht vergeben |
| **M1 + M2 (Arithmetik/Linearität)** | **Arithmetik und Indexgrenzen: gefallen.** Verus findet S1a und S1b am echten Code für **0 Zeilen** (ein Schalter). **Linearität: halb** — `tracked` ist affin, eine Leckprüfung kostet eine hingeschriebene Bilanz. Rusts `Parked` liefert die andere Hälfte zu null Kosten |
| **M3 (`device`)** | **ungemessen — und der Gegner ist gar nicht Verus.** Typisierte Registerzugriffe (`tock-registers`, `svd2rust`-Art) sind eine **Rust-Bibliothek**. Die Frage ist nicht „kann eine Sprache das", sondern „was fehlt der Bibliothek": Übergänge über Bits, Bedingungen über Registergrenzen, Barrierendomäne im Typ |
| **M3 (Platzierung)** | **ungemessen**, und `#[link_section]` gibt es. Die Lücke ist, dass niemand es **prüft** — das kann eine Lint |
| **Eintritt (TAL)** | tötet **0** bezahlte Fallen und hat nirgends einen Beweiser |
| **`check` über M2** | **kein Gegner gefunden.** Weder Rust noch SPARK noch Verus noch Loom sagt etwas über Sprechprobe, Gatterung, Untergrenze oder isolierende Gegenprobe |

> **Die ehrliche Bilanz nach der ersten Gegenrechnung: übrig bleiben die lineare Prüfpflicht
> (`check` über M2), die Sperrordnung und M3 — und M3s Gegner ist eine Rust-Bibliothek, keine
> Sprache.** Die lineare Prüfpflicht braucht als *Wirkung* keine Sprache: V−1 baut sie als
> Makrobibliothek. Was sie als *Mechanismus* braucht, ist echte Linearität — und die hat Rust nicht.

Damit ist die Reihenfolge nicht mehr „V−1 zuerst, weil billig", sondern **„V−1, weil alles andere
gerade seinen Gegner gefunden hat".**

## 5. Der Plan, mit Toren

Jede Phase liefert eine Zahl, die über die nächste entscheidet. Ohne Zahl kein Weiterbau.

| Phase | Inhalt | **Tor** |
|---|---|---|
| **V−1** | **`check` allein, als Rust-Makrobibliothek** — ohne eigene Sprache, ohne Übersetzer | Es rüstet die 33 Fallen in Caprock nach. **Fangen die Regeln mindestens 5 davon rückwirkend** (mit Mutation belegt), ist die These getragen. Fangen sie 0–1, ist `check` Ergonomie |
| **V0** | Stufe 0 + Stufe 6 als echte Sprache, ein Modul erzeugt | Spezifikationsverhältnis nach dem Protokoll 0b **an zwei Modulen**, beide berichtet |
| **V1** | Stufe 1 (Nebenläufigkeit) | `caprock-sync` + der Cap-Space-Lock übersetzt, **Loom-Beweise gehen durch**, Sperrordnung fängt eine eingebaute Verletzung |
| **V2** | Stufe 2 (`device`) | `vtd.rs` (1 448 Zeilen) übersetzt, **die DMA-Suite bleibt grün**, und vier Mutationen (Fallen 1, 2, 4, 5) übersetzen **nicht** |
| **V3** | Stufe 3 (Linearität/Regionen) | `Parked` und die Endowment-Kette; Mutation zu Falle 96 übersetzt nicht |
| **V4** | Stufe 4+5, Eintritt | ein Syscall-Eintritt ohne `asm!`, gemessen gegen die heutige Zyklenzahl |
| **V5** | Umstellung nach Strangler-Muster | s. u. |

### Die Umstellung nimmt zuerst das Werkzeug auseinander, das die Fehler findet

**Das ist das grösste Risiko des ganzen Vorhabens, und es folgt aus der eigenen Messung.** 15,7 %
von Caprock sind Prüfgerüst; ein Rewrite fasst genau das zuerst an — und für die Dauer der
Umstellung läuft die Abnahmereihe nicht, also die Disziplin, die **jeden** der 100 Einträge oben
gefunden hat.

Daraus folgt die einzige vertretbare Form: **Modul für Modul, beide Fassungen gleichzeitig lebendig,
Differenztest zwischen ihnen.** Nie ein grosser Schnitt. Und die Abnahmereihe bleibt in Rust, bis
`check` in Gabbro sie **nachweislich** ersetzt — nicht umgekehrt.

---

## 6. Die Kosten, ehrlich

**Der Übersetzer.** Die sieben Konstrukte waren „ein Erzeuger von Wochen". Stufe 0–6 sind die
Klasse ATS / F\*-Low\*-KaRaMeL / Verus — Arbeiten mehrerer Forschungsgruppen über Jahre.
**Eine belastbare Schätzung habe ich nicht**, und eine erfundene wäre schlimmer als keine; deshalb
stehen oben Tore statt eines Termins.

**Die Umstellung.** 66 651 Zeilen, und der Nenner ist kein Argument für sich: entscheidend ist,
dass jedes umgestellte Modul seinen Differenztest mitbringt.

**Die Gegenrechnung, die zuerst zu machen ist:** die Klasse S (36) und die Klasse M (36) sind heute
**nicht unadressiert**. Rust-heute hat `Parked` gefunden. Verus kann Ressourcen-Invarianten über
lineare Ghost-Permissions. Loom fand die abgeschwächte Ordnung, sobald die Zelle im Modell war.
**Für jede Stufe gehört beantwortet: was kann Rust+Verus+Loom heute schon, und was bleibt übrig?**
Nur der Rest rechtfertigt eine Sprache.

## 7. Abbruchbedingungen dieses Zweigs

1. **V−1 fängt weniger als 5 der 33 Fallen rückwirkend.** Dann ist `check` — das einzige Konstrukt
   ohne Vorbild — Ergonomie, und mit ihm fällt die einzige originelle Begründung.
2. **Rust + Verus + Loom decken eine Stufe bereits ab.** Dann wird diese Stufe nicht gebaut.
3. **Das Spezifikationsverhältnis nach Protokoll 0b verfehlt seine Schwellen** (2 : 1 bester,
   5 : 1 schlechtester Fall).
4. **Die Umstellung erzwingt einen grossen Schnitt.** Ein Vorhaben, das die Abnahmereihe abschaltet,
   um sich selbst zu bauen, hat keinen Prüfer mehr — und dieses Projekt hat gemessen, was dann
   passiert: zehn Tage rot, ohne dass es jemand sah.
