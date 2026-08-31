# Jede Giftprobe gegen ihre eigene Zusage: **230 sauber, 48 begleitet, 38 verdeckt** — und danach **7**

*Gemessen am 2026-08-31 lokal (31 GB, 20 Kerne; `free -g`: 31 gesamt, 18 verfügbar), über
alle **317** `beispiele/gift/*.gab`, mit `target/release/gabbro` aus dem Stand `5a7c8e2`.
Kein Bau am Prüfer, keine Zeile am Korpus geändert — **§1 bis §8 sind der Befund vor jedem
Eingriff.** Was danach geheilt und was benannt wurde, steht ab §9; die Zahlen oben bleiben
stehen, weil sie der Vergleichspunkt sind.*

`REICHWEITE-DER-REGEL.md` §10 hat den Posten offen gelassen:

> **„Nichts darüber, ob die 315 aus dem richtigen Grund abgewiesen werden."**

Hier steht die Antwort. Sie lautet **nicht** „ja" und **nicht** „nein":

> **Der erwartete Code fällt in allen 317 Proben. In 87 von ihnen fällt er nicht allein — und
> in 38 fällt vor ihm ein anderer.** Von diesen 38 gehen **26 auf vier Regeln zurück, die es
> zum Zeitpunkt der Probe noch nicht gab**: `N040`, `D011`, `N025`, `N028`. *Die Probe hat
> ihren Gegenstand behalten und sich einen zweiten Mangel eingefangen.*

---

## 1. Was der Testrahmen prüft — und was er nicht prüft

`crates/gabbro-check/tests/beispiele.rs::jedes_gift_faellt_mit_seinem_code` liest die erste
Zeile, trennt nach Stufe (`-- erwartet: Hinweis S007` gegen `-- erwartet: M104`) und fragt:

```rust
assert!(gefallen.contains(&erwartet.as_str()), …)
```

**`contains`, nicht `==` und nicht `[0]`.** Eine Probe ist grün, sobald ihr Code irgendwo in
der Liste steht — an erster Stelle, an vierzehnter, oder als einer von sechzehn. *Der Rahmen
misst die Anwesenheit einer Regel, nicht ihre Zuständigkeit.*

## 2. Das Maß

**Das Werkzeug dazu steht seit dem 2026-08-31 im Baum:** `./instrumente/zaehle-gifttreffer.py`
(`--lang` druckt jede nicht-saubere Probe einzeln, `--json` die ganze Tafel). Es trägt die
drei Marken aus §9 als Ratsche — *ohne sie wäre alles hier eine Momentaufnahme, und genau
diese Drift ist zweimal unbemerkt passiert.*

Je Probe ein eigener Prozess, damit sich die Dateien nicht über das Bindungsregister
beeinflussen (`gabbro pruefe` teilt es über eine Dateiliste hinweg):

```
gabbro pruefe  <datei>     fuer alle ausser `-- erwartet: C001`
gabbro emit    <datei>     fuer die elf `C001`-Proben -- so, wie der Testrahmen es tut
```

Gelesen wird der Kopf jeder Meldung: `error|hint: [CODE] datei:zeile:spalte: text`.
**Die Reihenfolge ist die Einfügereihenfolge der Pässe** — `Absagen::zeige` druckt
`self.absagen` in der Reihenfolge, in der die Pässe sie abgelegt haben, ohne nach Ort zu
sortieren. Das ist dieselbe Reihenfolge, die der Testrahmen sieht.

Die vier Klassen, mechanisch entschieden — **kein Urteil in der Einteilung, nur im Kommentar
danach**:

| Klasse | Kriterium |
|---|---|
| **sauber** | außer dem erwarteten fällt **nichts**. |
| **begleitet** | der erwartete ist **der erste seiner Stufe**; was sonst fällt, kommt danach. |
| **verdeckt** | vor dem erwarteten fällt ein Code **derselben Stufe**. |
| **zufällig** | der erwartete fällt aus einem Grund, den die Probe nicht meint. |

> **Die Stufe trennt zwei Töpfe, und der Rahmen tut das auch.** Ein `Hinweis E009` vor einem
> `Fehler K008` verdeckt nichts: die Zusicherung filtert erst nach Stufe und sucht dann. In
> den Tafeln unten steht ein `?` hinter jedem Hinweis.

## 3. Die Zahlen

| Klasse | Proben | Anteil |
|---|---:|---:|
| **sauber** | **230** | 72,6 % |
| **begleitet** | **48** | 15,1 % |
| **verdeckt** | **38** | 12,0 % |
| `-- erwartet: cc` (eigener Zweig, `413`) | 1 | 0,3 % |
| **zufällig** | **0** | — *(§7 — wie gesucht wurde)* |
| Summe | **317** | |

**Keine einzige Probe schweigt.** Es gibt keinen Fall, in dem der erwartete Code gar nicht
fällt — das wäre ein roter Test, und der Baum ist grün. Und es gibt keinen Fall, in dem der
erwartete Code nur mit der falschen Stufe fällt.

**Zehn Proben fallen mehrfach mit demselben Code und sonst nichts** (`127` zweimal `N016`,
`250` zweimal `H012`, …); sie zählen als **sauber**, denn kein zweiter Gegenstand steht
darin.

## 4. Der Ertrag: **vier Vorläufer tragen 26 der 38**

Welcher Code fällt vor dem erwarteten?

| Vorläufer | Proben | was er sagt |
|---|---:|---|
| **`N040`** | **13** | *„`T` names no type"* — die Probe nennt einen Typnamen, den sie nie deklariert |
| **`D011`** | **5** | *„declares `ops` but no `occupied` field"* |
| **`N025`** | **4** | *„is not `pub`, and … is outside …"* |
| **`N028`** | **4** | *„declares no `or <reason>`, so this `else` branch can never run"* |
| `M101` | 3 | der Bereich derselben Zeile |
| `S003` | 2 | *„`progress irgendwas` names no declared assumption"* |
| `S008` | 2 | *„`by consuming` names no `consumes` in its `touches`"* |
| `N027` · `N038` · `O010` · `E008` · `H007` | je 1 | |

Und die Vorläufer verteilen sich nicht zufällig über den Korpus, sondern über die
**Gerüstzeilen**: fünfzehn Proben nennen einen Typ, den es nicht gibt.

```
`T`           8   04 · 09 · 13 · 15 · 17 · 49 (dreimal)
`unit`        6   104 · 108 · 112 (zweimal) · 117 · 118
`Bericht`     3   50 · 51 · 52
`longdouble`  1   94
`Allok`       1   295 -- die Probe FUER `N040` selbst, kein Geruestmangel
```

**Sechzehn Dateien tragen `N040`, und nur EINE meint ihn** (`295-zeigerziel-ohne-typ`). In
`09` und `94` fällt er hinter dem erwarteten Code und macht die Probe `begleitet` statt
`verdeckt` — derselbe Mangel, eine andere Zeile in der Tafel.

> **Keine dieser fünfzehn Proben handelt von Namensauflösung.** `N040` gibt es seit dem
> 2026-08-25 (`SYNTAX.md`:1558); die Proben sind älter. *Ein Platzhalter, der beim Schreiben
> nichts kostete, ist über Nacht ein zweiter Gegenstand geworden.*

Dasselbe bei `D011`: fünf Proben schreiben `table … ops` ohne `occupied`-Feld, und keine
handelt davon — `37` und `60` meinen `D001`/`D002`, `226` und `249` meinen `breaking`, `58`
meint den `dma`-Raum.

## 5. Die 38 verdeckten, einzeln

Fett steht der erwartete Code; `@n` ist die Quellzeile; `?` markiert einen **Hinweis**.

| Probe | erwartet | n | die Kette, in Passreihenfolge |
|---|---|--:|---|
| `04-ohne-wirkungen.gab` | `E001` | 2 | N040@6 · **E001**@6 |
| `104-ensures-index-tippfehler.gab` | `M109` | 2 | N040@13 · **M109**@14 |
| `108-maintains-ins-leere.gab` | `M112` | 2 | N040@17 · **M112**@18 |
| `112-vorbedingung-ausgeschlossen.gab` | `M115` | 3 | N040@12 · N040@16 · **M115**@16 |
| `117-touches-deckt-nicht.gab` | `E011` | 2 | N040@16 · **E011**@21 |
| `118-abstiegsmass-konstant.gab` | `S005` | 2 | N040@19 · **S005**@22 |
| `13-pure-und-schreiben.gab` | `E002` | 4 | N040@6 · **E002**@6 · E005@7 · E008@6 |
| `140-gleicher-name-fremdes-modul.gab` | `E008` | 3 | N025@33 · **E008**@30 · K001@32 |
| `15-schleife-traegt-keine-fakten.gab` | `M104` | 3 | N040@10 · **M104**@15 · M101@15 |
| `155-messung-schreibt-sich-selbst.gab` | `N021` | 2 | N027@15 · **N021**@15 |
| `17-schleife-schreibt.gab` | `M104` | 3 | N040@14 · **M104**@21 · M101@21 |
| `182-verbrauch-in-der-schleife.gab` | `L108` | 3 | S007?@27 · S003@26 · **L108**@20 |
| `187-can-fail-schreibt.gab` | `N027` | 6 | N028@69 · **N027**@70 · N021@70 · M119@71 · M104@71 · M104@71 |
| `188-schritt-in-locks-in-schleife.gab` | `O006` | 7 | S007?@35 · S003@34 · L108@27 · L107@39 · **O006**@32 · K002@38 · K006@32 |
| `195-descendants-ohne-tree.gab` | `C001` | 2 | S008@21 · **C001**@21 |
| `196-descendants-nur-mit-elter.gab` | `C001` | 2 | S008@24 · **C001**@24 |
| `219-unaeres-minus.gab` | `C001` | 2 | M101@21 · **C001**@21 |
| `226-breaking-oeffnet-den-traeger-nicht.gab` | `D002` | 4 | D011@30 · **D002**@49 · D009@48 · D001@49 |
| `249-breaking-auf-ops-traeger.gab` | `D009` | 2 | D011@16 · **D009**@31 |
| `25-let-else-faellt-durch.gab` | `S002` | 2 | N028@13 · **S002**@13 |
| `250-sperrring-ueber-bibliotheken.gab` | `H012` | 16 | N025@56 · N025@58 · N038@37 · N038@38 · N038@48 · N038@49 · N038@61 · N038@61 · N038@62 · N038@62 · N038@72 · N038@72 · N038@73 · N038@73 · **H012**@66 · **H012**@77 |
| `251-sperre-ohne-deklaration.gab` | `H016` | 2 | N038@30 · **H016**@31 |
| `300-zeiger-auf-raw-fn.gab` | `O009` | 2 | O010@17 · **O009**@29 |
| `31-modul-verdeckt-signatur.gab` | `M101` | 2 | N025@24 · **M101**@24 |
| `37-b29-unter-ops.gab` | `D001` | 4 | D011@21 · **D001**@39 · M104@39 · M101@39 |
| `47-else-zweig-faellt-durch.gab` | `S002` | 3 | N028@13 · **S002**@13 · E008@12 |
| `49-pure-ruft-schreibend.gab` | `E008` | 4 | N040@6 · N040@7 · N040@8 · **E008**@8 |
| `50-verwaistes-awaits.gab` | `V002` | 3 | N040@6 · E010@9 · **V002**@9 |
| `51-verwaistes-publishes.gab` | `V001` | 3 | N040@6 · V008@9 · **V001**@9 |
| `52-relaxed-mit-nutzlast.gab` | `V004` | 2 | N040@5 · **V004**@8 |
| `56-geliehenes-verbraucht.gab` | `L102` | 2 | E008@11 · **L102**@11 |
| `58-ops-traeger-im-dma-raum.gab` | `R001` | 2 | D011@6 · **R001**@11 |
| `60-b29-unter-by-ops.gab` | `D002` | 5 | D011@16 · **D002**@29 · D001@29 · M104@29 · M101@29 |
| `63-gruppe-halb-gesperrt.gab` | `U003` | 3 | H007@54 · H008?@41 · **U003**@47 |
| `65-gruppe-austritt-durch-else.gab` | `U006` | 2 | N028@57 · **U006**@57 |
| `87-nan-ohne-verengung.gab` | `F001` | 2 | M101@12 · **F001**@12 |
| `92-halbe-schranke.gab` | `F001` | 2 | M101@13 · **F001**@13 |
| `98-undurchsichtig-umgangen.gab` | `D004` | 2 | N025@14 · **D004**@16 |

### Und drei davon sind KEINE Gerüstsache, sondern eine Ordnung derselben Zeile

`87`, `92` und `219` tragen ihren Vorläufer **auf demselben Ausdruck**: `M101` und `F001`
sagen beide etwas über `return x`, `M101` und `C001` beide über `-- x`. Heilt jemand `M101`,
fällt der erwartete weiter — die Reihenfolge ist Passreihenfolge und keine Abhängigkeit.
*Sie stehen in dieser Tafel, weil das Kriterium mechanisch ist; gefährlich sind sie nicht.*

## 6. Die 48 begleiteten

Der erwartete ist der erste seiner Stufe. **Harmlos für den Rahmen, aber nicht ohne
Auskunft:** in `09-schleife-ohne-mass.gab` und `94-long-double.gab` steht derselbe
`N040`-Gerüstmangel wie in den dreizehn verdeckten — er fällt nur später.

| Probe | erwartet | n | die Kette |
|---|---|--:|---|
| `01-unterlauf.gab` | `M104` | 2 | **M104**@10 · M101@10 |
| `05-auffangzweig.gab` | `P034` | 2 | **P034**@11 · P006@15 |
| `09-schleife-ohne-mass.gab` | `P001` | 2 | **P001**@7 · N040@6 |
| `10-marke-fehlt.gab` | `S001` | 2 | S007?@7 · **S001**@8 |
| `103-rueckgabe-im-lesebereich.gab` | `H011` | 2 | **H011**@16 · H015@16 |
| `12-ueberlauf-mal.gab` | `M104` | 2 | **M104**@7 · M101@7 |
| `125-fremder-zeiger-toetet.gab` | `M101` | 2 | **M101**@19 · E005@19 |
| `127-axiom-merkmal-ungetragen.gab` | `N016` | 4 | **N016**@20 · **N016**@20 · E009?@20 · K003@20 |
| `138-atomic-ohne-ordnung.gab` | `V005` | 2 | **V005**@18 · V002@25 |
| `14-fakt-stirbt.gab` | `M104` | 2 | **M104**@12 · M101@12 |
| `150-rekursion-ohne-mass.gab` | `K008` | 3 | E009?@11 · **K008**@11 · K001@11 |
| `151-mass-wird-durchgereicht.gab` | `K009` | 2 | E009?@13 · **K009**@13 |
| `152-eintritt-maskiert-ohne-annahme.gab` | `H013` | 2 | **H013**@17 · H101@17 |
| `16-fakt-stirbt-im-unterblock.gab` | `M104` | 2 | **M104**@22 · M101@22 |
| `167-ungleichheit-in-der-mitte.gab` | `M104` | 2 | **M104**@18 · M101@18 |
| `174-asm-ohne-pflichten.gab` | `A001` | 6 | **A001**@20 · A002@20 · A003@20 · A004@20 · N026?@20 · E001@20 |
| `184-mass-vertauscht.gab` | `K009` | 2 | E009?@18 · **K009**@18 |
| `214-registerbeziehung-traegt-nicht.gab` | `M104` | 2 | **M104**@31 · M101@31 |
| `22-globaler-fakt-nach-aufruf.gab` | `M104` | 3 | **M104**@18 · M101@18 · E010@16 |
| `221-ops-erfundenes-wort.gab` | `P039` | 2 | **P039**@24 · P006@27 |
| `223-self-im-ensures-ohne-traeger.gab` | `M120` | 2 | **M120**@18 · M111@18 |
| `227-tippfehler-in-aligned.gab` | `M109` | 2 | **M109**@19 · M111@19 |
| `229-tippfehler-unter-der-negation.gab` | `M109` | 2 | **M109**@20 · M111@20 |
| `23-aufruf-im-ausdruck.gab` | `M104` | 2 | **M104**@24 · M101@24 |
| `24-schieben-mit-vorzeichen.gab` | `M104` | 2 | **M104**@15 · M101@15 |
| `240-fnzeiger-ohne-effects.gab` | `N035` | 2 | **N035**@20 · E009?@24 |
| `243-fnzeiger-verspricht-locks.gab` | `N036` | 3 | **N036**@25 · E008@29 · H008?@21 |
| `245-ruf-ueber-ort-ohne-fnzeiger.gab` | `M129` | 3 | **M129**@22 · E009?@18 · K003@22 |
| `26-schieben-untere-ecke.gab` | `M104` | 2 | **M104**@13 · M101@13 |
| `261-rahmen-unter-zyklus.gab` | `E008` | 2 | E009?@29 · **E008**@29 |
| `262-gruppe-gleicher-rang.gab` | `U005` | 3 | H008?@19 · H008?@20 · **U005**@22 |
| `272-observes-tippfehler-in-der-domaene.gab` | `H017` | 4 | **H017**@32 · H007@33 · H009@33 · H008?@24 |
| `280-gruppe-mit-einem-traeger.gab` | `U004` | 3 | H008?@11 · **U004**@13 · U007@14 |
| `281-gruppe-nennt-keinen-traeger.gab` | `U001` | 3 | H008?@11 · **U001**@13 · U007@14 |
| `282-gruppentraeger-ohne-sperre.gab` | `U002` | 2 | H008?@11 · **U002**@13 |
| `284-konstruktor-ohne-feldmarken.gab` | `M107` | 3 | **M107**@11 · E009?@11 · K003@11 |
| `293-grund-an-fremdem-parameter.gab` | `M124` | 2 | **M124**@26 · E009?@25 |
| `303-occupied-zweimal.gab` | `P040` | 2 | **P040**@21 · P006@24 |
| `32-modul-verdeckt-typ.gab` | `M104` | 2 | **M104**@13 · M101@13 |
| `407-forever-mit-ausgang-faellt-durch.gab` | `L103` | 2 | **L103**@23 · L101@20 |
| `41-geteilt-erklaert-exklusiv-genommen.gab` | `E007` | 2 | **E007**@23 · H004?@15 |
| `44-uebergang-mit-zeigerpfeil.gab` | `P001` | 2 | **P001**@9 · P006@12 |
| `48-register-ohne-umlauf.gab` | `M104` | 2 | **M104**@10 · M101@10 |
| `70-bootschritt-vertauscht.gab` | `O003` | 2 | **O003**@35 · O004@28 |
| `90-gleitkomma-bitweise.gab` | `F005` | 2 | **F005**@12 · K001@11 |
| `91-schranke-wandert.gab` | `M101` | 2 | **M101**@18 · K001@17 |
| `94-long-double.gab` | `F006` | 2 | **F006**@11 · N040@11 |
| `99-ensures-nennt-nichts.gab` | `M109` | 2 | **M109**@11 · M111@11 |

### Das häufigste Paar ist kein Befund

`M104` gefolgt von `M101` steht **elfmal** da, immer auf derselben Zeile: die Operation
verlässt den Bereich (`M104`), und deshalb passt der Wert nicht in das Ziel (`M101`).
*Zwei Sätze über einen Ausdruck, nicht zwei Gegenstände.*

## 7. Warum die Klasse „zufällig" leer bleibt — und wie gesucht wurde

„Zufällig" hieße: der erwartete Code fällt, aber an einer Stelle, die die Probe nicht meint.
Drei Suchen, alle ohne Fund:

1. **Meldungstext gegen Dateinamen.** Für alle 38 verdeckten wurde der **Text** der erwarteten
   Meldung gegen den Dateinamen und den Kopfkommentar gehalten, einzeln und ausgeschrieben:
   `112` erwartet `M115` und bekommt *„`nimm` requires `x >= 1`, and the argument lies in
   0 .. 0"*; `117` erwartet `E011` und bekommt *„`fremd` is touched by this `traverse` … but
   stands in no `touches` effect"*; `58` erwartet `R001` und bekommt *„`r` points into the
   `dma` space"*. **Achtunddreißigmal derselbe Gegenstand, kein Treffer daneben.**
2. **Gerüst gegen Gegenstand.** Die fünfzehn `N040`-Proben und die fünf `D011`-Proben wurden
   daraufhin gelesen, ob ihr erwarteter Code am Platzhalter hängt. Er tut es in keiner:
   `N040` betrifft die Signatur, der Gegenstand steht im Rumpf. **§8 misst das nach, statt es
   zu behaupten** — der Platzhalter wird deklariert, und der erwartete Code muss bleiben.
3. **Stufe gegen Stufe.** Es gibt keine Probe, in der der erwartete Code nur mit der falschen
   Stufe fiele und der Rahmen ihn im anderen Topf fände — geprüft über alle 317, indem beide
   Töpfe getrennt geführt wurden.

> **Ein Nullbefund mit Suchweg ist etwas anderes als eine ungestellte Frage.** Diese Klasse
> ist leer, weil dreimal gesucht wurde, und nicht, weil das Kriterium sie nicht hergibt.

## 8. Was diese Tafel NICHT sagt

* **Nichts über die 230 sauberen jenseits der Anwesenheit.** Dass nur ein Code fällt, heißt
  nicht, dass er aus dem Grund fällt, den der Kommentar nennt. Gemessen ist der Ort, nicht
  das Argument.
* **Nichts über die Vollständigkeit des Korpus.** Eine Regel ohne Probe fällt hier nicht auf;
  das misst `zaehle-absagen.py`.
* **Nichts über `C001` jenseits der elf.** Für alle anderen Proben lief der Erzeuger nicht —
  genau wie im Testrahmen. Eine Probe, die zusätzlich ein `C001` auslöste, wäre hier
  unsichtbar.
* **Nichts über die Reihenfolge als Zusage.** Die Passreihenfolge ist eine Eigenschaft
  **dieses Binärprogramms**. Sie ist stabil genug, um sie zu messen, und nirgends versprochen.

---

# Der Eingriff: **38 → 7**, und **24 Regeln messen jetzt allein**

*Alles unter dieser Linie ist nach der Tafel entstanden. Die Zahlen oben bleiben stehen — sie
sind der Zustand am Morgen des 2026-08-31, und sie sind der Vergleichspunkt.*

## 9. Was geheilt wurde

| | vorher | nachher |
|---|---:|---:|
| **sauber** | 230 | **255** |
| **begleitet** | 48 | **54** |
| **verdeckt** | **38** | **7** |
| `-- erwartet: cc` | 1 | 1 |

**Einunddreißig Proben haben ihren Vorläufer verloren, und in 24 fällt jetzt genau ein
Code.** Zwanzig verschiedene Regeln werden damit zum ersten Mal ohne Nachbarn gemessen:

`E001` · `P001` · `M109` · `M112` · `M115` · `E011` · `S005` · `E008` · `L108` · `C001` ·
`D009` · `S002` · `H016` · `M101` · `V002` · `V001` · `V004` · `R001` · `U006` · `D004`

Die Heilungen, nach Familie — **jede ein Ergänzen, keine ein Weglassen des Gegenstands**:

| Familie | Proben | was ergänzt wurde |
|---|---|---|
| `N040` | `04` `09` `13` `15` `17` `49` `50` `51` `52` | `type T` / `table T` / `type Bericht` — der Platzhalter, deklariert |
| `N040` (`unit`) | `104` `108` `112` `117` `118` | `-> unit` gestrichen; **`unit` ist kein Typ dieser Sprache** |
| `D011` | `37` `58` `60` `226` `249` | `occupied benutzt;` / `occupied belegt;` neben der `ops`-Zeile |
| `N028` | `25` `47` `65` | `or <Grund>` an der Funktion, über die das `let … else` läuft |
| `N025`/`N038` | `31` `98` `140` `250` `251` | `pub` an Typ, Tabelle, Konstante, Sperre und `static` |
| `S008` | `195` `196` | `consumes t.slots` im `touches` der `by consuming`-Traversierung |
| `S003`/`S007` | `182` `188` | `assume irgendwas … falsifier …` und `extern fn aufgeben() -> never` |
| einzeln | `187` | ein `reason`, ein verengter Rückgabetyp, `static mut tiefe_max` |
| einzeln | `219` | der Parameter auf `i32 in -100 .. 100` verengt, damit `M101` nicht mitfällt |
| einzeln | `140` `188` | Kosten- und Sperrschranken angehoben, wo sie unbeabsichtigt rissen |

### Zwei Heilungen haben eine dritte Regel freigelegt

Wer den `or`-Grund ergänzt, bekommt `N034` — *„declares `or QuellFehler`, and its body never
returns a reason"*. Wer `pub` setzt, bekommt `N038` — *„is exported and names `Eng`, which is
not"*. **Beide sind richtig**, und beide standen hinter der ersten Absage.

> *Eine Heilung, die eine neue Absage hervorholt, hat nichts kaputtgemacht — sie hat einen
> Vorhang weggezogen.* Bei `251` waren es sogar zwei Lagen: `pub table T` holte
> `T names N, which is not`, und erst `pub const N` machte `H016` allein sichtbar.

### Und die Decke von `beispiele/gift/` hat sich nicht bewegt

`REICHWEITE-DER-REGEL.md` §7 führt `beispiele/gift/` als **Decke bei 2 emittierenden
Dateien** — eine mehr wäre ein Prüfer, der eine Probe durchlässt. Vor und nach dem Eingriff
sind es dieselben drei Dateien mit Rücklaufwert `0` (`166`, `286`, `413`), davon zwei
emittierende. **Jede geheilte Probe trägt ihren Fehler weiter und kommt am C-Tor nicht an.**
`cargo test`: 15 Sammlungen, alle grün.

`./instrumente/abnahme.py` nach dem Eingriff: **44 von 48 Wächtern haben gemessen, 43 grün,
1 rot** — und der eine ist `pruefe-grammatiktafel.py` mit seinen **vier `UNGEDECKT`-Zellen**,
die es vor diesem Zweig schon gab. *Kein Wächter ist an dieser Arbeit rot geworden, der es
vorher nicht war.* Drei sind es unterwegs geworden und wurden geheilt, nicht gezogen:
`pruefe-waechter.py` (das neue Werkzeug ohne `LC_ALL`), `pruefe-englisch.py` (eine deutsche
Kommentarzeile in `instrumente/`) und `pruefe-zahlen.py` (die Instrumentenzahl im README, die
**schon vorher** um eins danebenlag).

## 10. Was BENANNT wurde statt geheilt — die sieben, die bleiben

| Probe | erwartet | Kette | warum es nicht geht |
|---|---|---|---|
| `87-nan-ohne-verengung` | `F001` | M101@12 · **F001**@12 | |
| `92-halbe-schranke` | `F001` | M101@13 · **F001**@13 | **Ein Bereichstyp trägt die Endlichkeit mit.** `finite` gibt es nur hinter `narrow … to` (`SYNTAX.md`:368), also kann kein Rückgabetyp „nicht-NaN, aber beliebig groß" sagen. `M101` und `F001` sind zwei Hälften **einer** Deklaration. |
| `155-messung-schreibt-sich-selbst` | `N021` | N027@15 · **N021**@15 | **`N021` ist ohne `N027` nicht erreichbar.** Der gemessene Pfad steht im `can_fail`-Block, und jede Zuweisung dort ist `N027`. *Gemessen und nicht vermutet:* das Schreiben in die Torfunktion `gates tor` zu verlegen macht die Probe **völlig stumm** — `N021` sieht die Tore nicht. Der Versuch wurde zurückgenommen; **die Reichweite von `N021` ist damit ein eigener Befund.** |
| `187-can-fail-schreibt` | `N027` | **N027**@72 · N021@72 | dasselbe Paar, andersherum — und damit `begleitet` statt `verdeckt`. Zusammen sind die beiden Proben der Beleg: **das Paar ist nicht trennbar, in keiner Richtung.** |
| `56-geliehenes-verbraucht` | `L102` | E008@11 · **L102**@11 | **Der Vorläufer IST der Gegenstand.** `L102` heißt „geliehen und trotzdem verbraucht"; *geliehen* heißt genau, dass `consumes` in den `effects` fehlt — und dieselbe Auslassung ist `E008`. Wer `E008` heilt, löscht die Probe. |
| `63-gruppe-halb-gesperrt` | `U003` | H007@54 · H008?@41 · **U003**@47 | **Eine Sperre, zwei Regeln.** `H007` sieht den einzelnen Ort ohne seine Sperre, `U003` die Gruppe. Es gibt keine Schreibstelle an einem `PLAN`-geschützten Träger ohne `PLAN`, die `H007` nicht sieht. |
| `188-schritt-in-locks-in-schleife` | `O006` | L108@33 · L107@45 · **O006**@38 | **Ein Phasenschritt verbraucht eine lineare Marke.** Also ist jede Probe für *„Phasenschritt in einer Schleife"* zwangsläufig auch eine für *„lineare Marke in einer Schleife verbraucht"* (`L108`). Zwei unbeabsichtigte Nachbarn (`K002`, `K006`) sind weg; die zwei linearen bleiben. |
| `300-zeiger-auf-raw-fn` | `O009` | O010@17 · **O009**@29 | **Beide Auswege sind Absagen.** Ohne Marke sagt `O008` *„`raw fn` demands no `linear ghost` token"*, mit Marke sagt `O010` *„no function retires it"* — gemessen, indem beides gefahren wurde. Der dritte Weg ist ein `retires t from boot falsifier …`, und der verlangt einen `boot`-Block **und** eine Nachbedingung über die Abbildungen (`O012`, ebenfalls gemessen). *Mehr Gerüst, als die Probe groß ist.* |

> **Fünf der sieben sind keine Nachlässigkeit, sondern eine Aussage über die Sprache.**
> `F001`/`M101`, `N021`/`N027`, `L102`/`E008`, `U003`/`H007`, `O006`/`L108` — das sind
> Paare, bei denen der eine Fehler den anderen **mit sich bringt**. Eine Probe kann sie nicht
> trennen, weil die Sprache sie nicht trennt.

### Der Nebenbefund, den niemand gesucht hat

`N021` liest die `gates`-Funktionen eines `check` nicht. Schreibt die Torfunktion die
gemessene Größe, sagt **kein einziger Pass etwas** — die Datei geht mit null Absagen durch.
*Ob das eine Lücke ist oder die richtige Grenze, ist eine Frage an `SYNTAX.md` §13 und
nicht an diese Tafel;* hier steht nur, dass es gemessen wurde und dass keine Probe es hält.

> **BEANTWORTET am 2026-08-31, mit einem Lauf statt einer Ansicht:
> `messung/TORREICHWEITE.md`.** Zwölf kleinste Programme gegen den unveränderten Prüfer.
> Die Antwort ist **die richtige Grenze**: `gates` nennt, WER die `Duty` verbraucht,
> Verbrauch kommt nach Erzeugung, also liegt eine Schreibstelle im Tor **flussabwärts** von
> der Messung. Der Erzeuger schreibt `gates` als Kommentarzeile und sonst nirgendwohin
> (`emit.rs`:2781); der Rumpf von `pruefe_c()` **ist** `can_fail` (`emit.rs`:2807). *Eine
> Absage über schreibende Tore wäre eine ohne gemessenen Mangel — sie wurde nicht gebaut.*
>
> **Und derselbe Vorlauf hat gefunden, wonach niemand gesucht hatte:** `N021` und `N022`
> finden ihre Größe über einen **Namensvergleich gegen `measures`**, und `measures` löste
> niemand auf. `messung/tor-proben/t11` ist byteweise `155-messung-schreibt-sich-selbst.gab`
> mit `measures kk` — und `N021` ist weg. **Ein Buchstabe schaltete zwei Regeln ab.**
> Dagegen steht seit heute `N043` (`beispiele/gift/421-measures-ins-leere.gab`), und es fand
> bei seinem ersten Lauf zwei Fälle im eigenen Korpus: `187-can-fail-schreibt.gab` (zwei
> Träger beim Kürzen aus `beispiele/06` verloren, `measures` und `floor` nannten sie weiter
> — **`N022` schwieg dort über `floor kerne_gemessen >= 2`**) und `messung/fragmente/F06.gab`
> (`measures eich.leer, …` an einem Träger `eich`, den die Datei nicht hat).
>
> *Die Zeile von `187` in der Tafel oben ist damit `N027`@78 · `N021`@78 —* die zwei
> nachgetragenen Träger haben sie um sechs Zeilen verschoben. **Das Paar bleibt unverändert
> untrennbar;** `N043` macht nur die eine Umgehung unmöglich, mit der es jemand versucht hat.

## 11. Was dieser Eingriff NICHT gezeigt hat

* **Nichts darüber, ob die 255 sauberen aus dem richtigen Grund fallen.** §8 gilt weiter, nur
  über eine größere Menge. Dass ein Code allein fällt, macht ihn nicht zuständig.
* **Nichts über die Proben, die nie geschrieben wurden.** Vier Vorläufer waren Regeln, die
  nach ihrer Probe kamen; **wie viele Regeln gar keine Probe haben**, misst
  `zaehle-absagen.py` und nicht diese Tafel.
* **Nichts darüber, ob die Reparaturen die Proben SCHÄRFER gemacht haben.** Sie haben ihnen
  einen zweiten Gegenstand genommen — dass die verbleibende Zeile scharf ist, hat der
  Mutationslauf zu sagen, nicht dieser Eingriff.
* **Und der `-- erwartet: cc`-Zweig ist unberührt.** `413` hat nie einen Vorläufer gehabt: der
  Prüfer schweigt dort mit Absicht, und das ist die halbe Zusage der Probe.
