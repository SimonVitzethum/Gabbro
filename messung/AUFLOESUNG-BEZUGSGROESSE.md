# Die Ratsche von `pruefe-aufloesung.py` — die Bezugsgröße war nicht falsch geschnitten, **der Gegenstand war ein anderer**

*Gemessen am 2026-08-30. Die Frage war, ob Fach 1 eine Zahl oder ein Anteil sein muss. Die
Antwort ist keins von beidem: **26 der 28 Stellen waren nie auf dieser Karte.** Die Marke
fällt von 27 auf 2, und das ist eine Berichtigung, keine Arbeit (`PLAN-AUTONOM.md` §1.8).*

---

## 1. Der Auftrag und die drei ausgeschlossenen Ausgänge

Die Ratsche stand rot: **28 in Fach 1, erlaubt 27**, gebrochen zwischen `87b7f53` und
`6438b28`. Die neue Stelle: `emit.rs:8175`, `u.geraete.get(g)` — die **fünfte** Instanz einer
Form, die viermal danebensteht (5065, 6830, 6912, 7253).

`TODO.md` hielt alle drei üblichen Ausgänge für versperrt, und den dritten ausdrücklich:

> **Der Wächter misst etwas anderes als seinen Gegenstand** — das trifft hier NICHT zu, er
> misst genau, was er sagt.

**Dieser Satz ist der Fehler.** Er ist an der Ausgabe des Wächters geprüft worden und nicht an
seinem Gegenstand.

---

## 2. Was gemessen wurde

### 2.1 `u` ist in `emit.rs` keine `Umgebung` — in **keiner einzigen** Signatur

```bash
grep -c "u: &Namen"    crates/gabbro-check/src/emit.rs   # 61
grep -c "u: &Umgebung" crates/gabbro-check/src/emit.rs   #  0
```

`emit.rs` führt seinen **eigenen** Namensraum, `struct Namen` (emit.rs:47). Er trägt drei
Felder, die genauso heißen wie Felder der `Umgebung` — `funktionen`, `geraete`, `formate` —
und er ist es, den `u` in `emit.rs` bezeichnet. In `m1.rs` dagegen steht `u: &'a Umgebung`
(m1.rs:215).

### 2.2 Und die gleichnamigen Karten sind **entgegengesetzt** geschlüsselt

| | |
|---|---|
| `umgebung.rs:654` | `self.geraete.insert(q(&d.name.text), felder);` — **qualifiziert** |
| `emit.rs:652` | `namen.geraete.insert(d.name.text.clone(), …);` — **blank** |
| `emit.rs:649` | `namen.formate.insert(f.name.text.clone());` — **blank** |
| `emit.rs:838` | `namen.funktionen.insert(f.name.text.clone(), sig);` — **blank** |

In `umgebung.rs` steht **17-mal** `insert(q(…))` und kein einziges Mal ein blanker Schlüssel.
In `emit.rs` ist es genau umgekehrt.

> **Ein blanker Name auf einer blank gefüllten Karte ist richtig.** Er ist nicht die Falle —
> er ist ihr Gegenteil. Der alte Ausdruck traf auf den **Feldnamen** und konnte nicht sehen,
> welcher `struct` das `u` war.

### 2.3 Die Historie — 38 Commits, gegen vier Nenner

`Fach 1` je Commit, der `umgebung.rs` berührt, aus `git show` rekonstruiert (dieselbe
Bisektionsart, mit der die 28 gefunden wurde):

| Commit | Datum | Fach 1 roh | davon `emit.rs` | davon `m1.rs` | **korrigiert** | Karten | Zeilen `emit.rs` | Stellen ges. |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| `2296ae4` | 08-14 | 2 | 0 | 2 | **2** | 5 | — | 10 |
| `4603555` | 08-14 | 3 | 0 | 2 | **3** | 6 | — | 13 |
| `0a9408e` | 08-17 | 2 | 0 | 2 | **2** | 7 | — | 16 |
| `5735002` | 08-17 | 10 | 8 | 2 | **2** | 7 | 2 221 | 25 |
| `fc1033f` | 08-18 | 9 | 8 | 1 | **1** | 7 | 2 374 | 24 |
| `e87bff4` | 08-20 | 13 | 11 | 2 | **2** | 7 | 3 956 | 36 |
| `ca2a27b` | 08-20 | 26 | 24 | 2 | **2** | 7 | 6 015 | 49 |
| `100a978` | 08-20 | 27 | 25 | 2 | **2** | 8 | 6 115 | 52 |
| `2b7b331` | 08-28 | 27 | 25 | 2 | **2** | 9 | 7 926 | 61 |
| `aa17cb9` | 08-30 | 28 | 26 | 2 | **2** | 9 | 8 239 | 63 |

**Welcher Nenner hält die Fläche stabil, und welcher nicht:**

* **Gegen nichts (die rohe Zahl):** 2 → 28. Vierzehnfach in sechzehn Tagen. *Hält nicht.*
* **Gegen die Zeilenzahl von `emit.rs`:** der `emit.rs`-Anteil liegt durchweg bei **2,8 bis
  4,1 Stellen je 1 000 Zeilen** (3,6 · 2,8 · 4,0 · 4,1 · 3,2). *Hält — und das ist der
  Befund, nicht die Rettung:* eine Zahl, die sich als **Dichte in einer Datei** stabilisieren
  lässt, misst die Datei und nicht die Falle.
* **Gegen die Zahl der qualifizierten Karten** (5 → 9): 0,4 → 3,1. *Hält nicht.*
* **Gegen alle Zugriffe (Fach 1+2+3)** (10 → 63): 0,20 → 0,44. *Hält nicht.*
* **Korrigiert, gegen nichts:** **2 · 3 · 2 · 2 · 1 · 2 · 2 · 2 · 2 · 2.** Über 38 Commits,
  17 Tage, während `emit.rs` von null auf 8 239 Zeilen wuchs. *Hält.*

> **Ein Anteil hätte funktioniert — und wäre die falsche Antwort gewesen.** `Fach 1 / Zeilen
> emit.rs` ist stabil, weil `emit.rs` beide Größen erzeugt. Man hätte eine saubere Kennzahl
> bekommen und dabei festgeschrieben, dass der Erzeuger der Gegenstand ist.

### 2.4 Die drei Fälle, in denen die Falle wirklich zuschlug — **alle drei leben, und keiner ist in `emit.rs`**

| Fall | wo heute | `u` ist dort |
|---|---|---|
| `M103` — `globale.get("Kappenraum")` traf nie | `umgebung.rs:402` (die Reparatur samt Notiz) | `Umgebung` |
| `M108` — `aufruf_toetet_fakten` tat nichts | `m1.rs:2599`, `m1.rs:2673` | `Umgebung` |
| `ist_weltname` über `globale.contains_key` | `m1.rs:2657` | `Umgebung` |

**Drei von drei in `Umgebung`-Code. Null von drei im Erzeuger.** Die Fläche, auf der die Falle
je zuschlug, ist genau die Fläche, die die Korrektur behält.

### 2.5 Ist `emit.rs:8175` derselbe Fall wie ihre vier Geschwister? — **Ja, gelesen und nicht gezählt**

Alle fünf holen `g` auf demselben Weg, aus derselben Karte:

```rust
// emit.rs:8169-8171 (die neue Stelle)
let Some(g) = u.geraetezeiger.get(&o.basis.text)
    .or_else(|| u.geraetewerte.get(&o.basis.text)) else { return false; };
let Some(dev) = u.geraete.get(g) else { return false; };
```

Dasselbe bei 5014-5017, 6825, 6903-6905, 7241-7244. Und `geraetezeiger` wird in `emit.rs`
selbst gefüllt (4151, 4163, 4204) — **mit `n.text.clone()`, also blank.** Der Schlüssel `g`
ist ein blanker Gerätetypname, und `Namen::geraete` ist blank geschlüsselt. *Sie passen
zusammen; die fünfte so wie die vier.*

---

## 3. Die Entscheidung

**Der dritte Ausgang trifft zu: der Wächter maß etwas anderes als seinen Gegenstand** — bei
26 von 28 Stellen. Geheilt wird der **Wächter**, nicht der Prüfer.

`pruefe-aufloesung.py` bekommt ein **Fach 0**: „das `u` ist keine `Umgebung`, die Karte gehört
der Datei". Eine Stelle fällt dorthin nur, wenn **beide** Kriterien zutreffen —

1. die Datei schreibt nirgends `u: &Umgebung` (auch nicht mit Lebensdauer oder `mut`), **und**
2. sie füllt genau diese Karte selbst mit einem blanken Schlüssel.

Beide Kriterien stimmen über alle 38 Commits einzeln überein (Spalten `bE` und `bT` der
Messung). **Verlangt werden trotzdem beide** — eines allein genügte für `emit.rs`, aber eine
Datei, die eine echte `Umgebung` abfragt, ohne den Typ hinzuschreiben, fiele dann lautlos aus
der Zählung. *Ein Instrument, das verstummt, ist genau der Fehler, gegen den es steht.* Im
Zweifel bleibt die Stelle in Fach 1 und jemand muss hinsehen.

**`RATSCHE = 2`**, mit dem Grund in der Datei. Die Marke wurde **nicht gehoben** — sie fällt
um 25.

```
== Fach 1 -- bloss uebergebener Name auf qualifizierter Karte: 2 ==
   m1.rs:1401  u.funktionen.get(name)
   m1.rs:3552  u.funktionen.contains_key(n)
== Fach 0 -- das `u` ist KEINE `Umgebung`, die Karte gehoert der Datei: 26 ==
   je Datei: emit.rs 26
== Arbeitsmenge: 36 Dateien, 9 Karten, 63 Stellen, 5 Proben ==
```

**63 Stellen vorher, 63 nachher.** Nichts ist verschwunden, alles ist umsortiert — und Fach 0
wird **gedruckt**, nicht weggelassen. Die Sprechprobe hat eine fünfte Richtung bekommen: ein
erfundenes `u: &Namen` mit blank gefüllter gleichnamiger Karte muss in Fach 0 landen, und eine
Datei **ohne** eigenen blanken `insert` muss trotz fehlender Annotation in Fach 1 bleiben.

---

## 3a. Was die Korrektur sichtbar gemacht hat — **die zwei Überlebenden sind beide die echte Form**

Vorher waren es zwei Nadeln in 28. Jetzt stehen sie allein da, und beide sind lesbar:

**`m1.rs:1401` — `endet_immer`, und es ist die *stille* Richtung (M103-Form):**

```rust
let name = r.path().and_then(|p| p.teile.last()).map(|i| i.text.as_str()).unwrap_or_default();
matches!(self.u.funktionen.get(name).and_then(|s| s.ergebnis.clone()), Some(Typ::Nie))
```

`p.teile.last()` nimmt von `a::b::f` das **`f`**; `u.funktionen` ist unter `a::b::f`
geschlüsselt. **Innerhalb eines `module` liefert das `None`, immer** — ein Aufruf einer
`-> never`-Funktion wird dort nie als blockbeendend erkannt.

*Der Kommentar darüber nennt genau diese Antwort die sichere Richtung* („a body that does not
obviously end must still end properly, and the rule that says so keeps firing") — für den
INDIREKTEN Aufruf. Für den qualifizierten gilt dieselbe Folge, aber sie steht dort nicht.
**Konservativ, also nicht dringend — aber es ist die Form, die dreimal zugeschlagen hat.**

**`m1.rs:3552` — `name_aufloesen`, und daneben steht die Lösung schon:**

```rust
|| self.u.funktionen.contains_key(n)
|| self.u.tabellen.keys().any(|k| k == n || k.rsplit("::").next() == Some(n.as_str()))
```

Zwei Zeilen, zwei qualifizierte Karten, **eine mit und eine ohne Entqualifizierung**. Die
Richtung ist hier laut (ein `M119` „is declared nowhere" könnte falsch feuern), nicht still.

**Keine der beiden wurde angefasst** — Regel A, gemessener Bedarf: null. Sie sind gebucht
(`TODO.md`), und die Ratsche auf **2** hält sie fest: eine dritte Stelle fällt sofort auf.

---

## 4. Und was das NICHT heißt

* **Fach 0 ist kein Freispruch.** Es sagt, dass die Karte eine andere ist — nicht, dass der
  Zugriff stimmt. Wer `Namen` eines Tages qualifiziert füllt, muss die Trennung hier
  nachziehen; der Wächter merkt es nicht von selbst (W10).
* **Zwei gleichnamige Karten mit entgegengesetzter Schlüsselung sind eine eigene Falle**, und
  sie ist mit dieser Messung nicht beseitigt, nur benannt. `Namen::geraete` und
  `Umgebung::geraete` heißen gleich und meinen Gegenteiliges. Der Wächter ist daran
  gescheitert; ein Mensch kann es auch.
* **Der Prüfer wurde nicht angefasst.** Kein modulbewusster Auflöser an `emit.rs:8175` —
  Regel A, und die fünfte Stelle unterscheidet sich nicht von ihren vier Geschwistern.
* **Die 27 war fünf Tage lang falsch, und sie stand mit ihrer eigenen Widerlegung daneben:**
  *„27 Stellen, **25 davon im Erzeuger**"* (Kommentar vom 2026-08-25). Der Satz war der
  Befund. Er wurde geschrieben, gelesen und als Hintergrund verbucht.
