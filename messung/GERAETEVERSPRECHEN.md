# «B26» — das Geräteversprechen senkt ab: `requires … else` macht die Lesung fehlbar

*Entschieden am 2026-08-28, Bahn A, Schritt A2. Gemessen auf `ki-pc-fisch-101:gabbro-A`,
Binärprogramm `4dd17209`, **vor jeder Änderung**.*

> **W24 hat die Frage zum fünften Mal an diesem Tag umgedreht, und diesmal war es der PLAN
> selbst.** `dokumente/PLAN-AUTONOM.md` schreibt zu A2:
>
> > *„`let q = d.REG else (e) { … }` — und diese Form trägt der Erzeuger schon."*
>
> **Sie trägt er nicht.** Der Erzeuger weigert sich bei ihr *beim Namen*:
>
> ```
> Fehler: [C001] no lowering: `let … else` over a PLACE -- «B14b» opened the form for an
> option-valued place, and there the failure is `None`, which carries no reason for `e` to
> hold. That half is open; the call form is decided
> ```
>
> Der Satz stimmt für den Fall, für den er geschrieben wurde: ein `option`-wertiger Ort
> scheitert mit `None`, und `None` trägt keinen Grund. **Für ein Register mit `requires …
> else R::C` trägt es einen** — er steht in der Deklaration. *Der Einwand des Erzeugers
> entscheidet also nicht gegen die Form, er benennt genau die Bedingung, unter der sie
> geht.*

---

## 1. Der Befund, mit den Befehlen

```bash
ssh ki-pc-fisch-101 'cd gabbro-A && ./target/release/gabbro pruefe    ~/gabbro-A-w24/a2-heute.gab'
ssh ki-pc-fisch-101 'cd gabbro-A && ./target/release/gabbro pflichten ~/gabbro-A-w24/a2-heute.gab'
ssh ki-pc-fisch-101 'cd gabbro-A && ./target/release/gabbro pruefe    ~/gabbro-A-w24/a2-wunsch.gab'
ssh ki-pc-fisch-101 'cd gabbro-A && ./target/release/gabbro emit      ~/gabbro-A-w24/a2-letsonst.gab'
```

| Probe | geschrieben | gemessen |
|---|---|---|
| **A** | `reg QUEUE_SIZE : u16 @0x0c class r requires QUEUE_SIZE <= QMAX`, dazu `return d.QUEUE_SIZE;` | **0 Fehler.** `gabbro pflichten` druckt `D  Device promise at a register (1)` — **gezählt, und sonst nichts** |
| **B** | dieselbe Zeile mit `else Geraetelug::ZuGross` | `Fehler: [P026] … im `device`-Rumpf erwartet: mirrors, reg, bank, transition -- `else` gefunden` — **die Form fällt am PARSER** |
| **C** | `let q = d.QUEUE_SIZE else (e) { … }` über ein Register **ohne** `else` an der Deklaration | **`pruefe`: 0 Fehler.** Der `else`-Zweig ist unerreichbar, und kein Pass sagt es |
| **D** | dieselbe Datei durch `gabbro emit` | **`C001`, beim Namen abgelehnt** — die Zeile oben |

**Drei Befunde, und der dritte ist der teure.**

1. **Die Zählung hält, die Wirkung fehlt.** A ist genau die Hälfte, die am 2026-08-24
   geschlossen wurde: eine Klausel bekam eine Nummer. *Eine Buchung ist keine Erledigung.*
2. **`requires … else` gibt es nicht** (B) — ein echter Formmangel, kein falscher Eintrag.
3. **Und die Form, auf die der Plan gebaut hat, senkt NICHT ab** (C, D). C ist dabei die
   unangenehmere Zeile: der Prüfer lässt `let … else` über einen beliebigen Ort durch, und
   erst der Erzeuger sagt nein. *Eine Datei, die den Erzeuger nie erreicht, hört davon
   nichts.*

---

## 2. Die Formen, gegeneinander — je Form beide Seiten

### Form 1 — `requires <pred> else <R>::<case>` macht die LESUNG fehlbar

```gabbro
reg QUEUE_SIZE : u16 @0x0c class r requires QUEUE_SIZE <= QMAX else Geraetelug::ZuGross
let q = d.QUEUE_SIZE else (e) { return Geraetelug::ZuGross; }
```

**Dafür**

* **Es macht aus dem Versprechen keine Tatsache, sondern eine PRÜFUNG.** Genau der
  Unterschied, an dem «B33» hängt: das Register ist flüchtig, ein feindliches Gerät darf
  alles melden, und was der Übersetzer daraus annimmt, darf nichts sein, das er nicht
  nachgesehen hat.
* **Kein neues Wort.** `else` trägt diese Bedeutung an `let … else` und `narrow … else`
  schon, und es ist *dieselbe* Bedeutung: die Stelle, an der die Verletzung sichtbar wird,
  statt still umzulaufen (`SCHLEIFENINVARIANTE.md` §3).
* **Die Absenkung liest EINMAL.** Das erzeugte C bindet die volatile Lesung und prüft die
  Bedingung auf der Bindung — nicht auf einer zweiten Lesung.
* Rückwärtsverträglich: `requires` ohne `else` bleibt, was es war — eine gezählte Pflicht.

**Dagegen**

* Es macht `let … else` zu einer Form mit **zwei** Absenkungen (Ruf und fehlbares Register),
  und die dritte (`option`-wertiger Ort) bleibt offen. *Drei Fälle unter einem Wort, von
  denen zwei gebaut sind.*
* Der Name der Bindung muss in der Bedingung den Registernamen **ersetzen**, sonst stünde
  dort ein zweiter volatiler Zugriff. Das ist eine Karte im Erzeuger, die genau eine
  Bedingung lang lebt — ein Mechanismus, den es vorher nicht gab.

### Form 2 — `requires` bleibt, und ein Pass NIMMT die Bedingung AN

Der Prüfer trüge `QUEUE_SIZE <= QMAX` als Tatsache über jede Lesung.

**Dafür**

* **Nichts zu bauen** außer einer Zeile im Verengungspass; jede vorhandene Datei profitiert
  sofort, ohne eine Zeile Änderung.
* Es liest sich wie das, was die Klausel wörtlich sagt.

**Dagegen — und diese Zeile entscheidet die ganze Frage**

* **Es ist der «B33»-Fehler noch einmal, nur eine Ebene höher.** «B33» hat 2026-08-20
  festgestellt, dass ein Vergleich auf einer Registerstelle keine Tatsache gibt. Form 2
  gäbe eine — und zwar aus einer Quelle, die schwächer ist als ein Vergleich: aus dem, was
  der Gerätehersteller behauptet. *Ein Treiber, der einer Warteschlangengröße glaubt,
  indiziert damit an einer Tabelle vorbei.*
* Die Zeile in `PFLICHTEN.md` sagt es selbst, und sie stand da, bevor dieser Bau begann.

### Form 3 — ein `assume` je Register, mit `falsifier`

```gabbro
assume virtio_meldet_ehrlich "…" falsifier sonde_virtio;
```

**Dafür**

* Der Mechanismus ist gebaut (`N004`/`N005`) und trägt schon 36 Annahmen.
* Es sagt die Wahrheit über die Beweislage: *dies ist eine Aussage über die Umgebung.*

**Dagegen**

* **Eine Annahme ist keine Prüfung, sie ist ihr Gegenteil.** Sie verschiebt die Pflicht auf
  einen Menschen mit einer Sonde — und «B26» steht in `PFLICHTEN.md` gerade deshalb offen,
  *weil* die Zusage nichts kostet.
* Sie skaliert an der falschen Achse: je Register eine Annahme, und der Treiber hat zwanzig.

---

## 3. Die Entscheidung, und der Grund ist der Begriff

**Gewählt ist Form 1.**

Der Grund ist nicht der Preis, sondern der Begriff: **ein Geräteversprechen ist eine Aussage
des GERÄTS, nicht des Programms.** Ein Programm darf sie benutzen, aber nur, indem es sie
nachsieht — und die Stelle, an der ein Nachsehen scheitern darf, heißt in dieser Sprache seit
jeher `else`. *`requires` ohne `else` bleibt darum genau, was es war: eine gezählte Pflicht,
die ein Mensch trägt.*

**Zwei Kennungen, und beide in `m3.rs`:**

| | |
|---|---|
| `R010` | die Deklaration: das `else` nennt einen `reason`-Fall, den diese Einheit erklärt |
| `R011` | **der Falsifikator**: eine fehlbare Lesung außerhalb eines `let … else` wird abgelehnt |

`R011` ist die Zeile, die «B26» schließt. Ohne sie wäre `else` eine weitere gezählte Klausel
und die Zusage doch wieder eine Tatsache — *und einen Dekrement mit Buchführung zu kaufen ist
genau das, wogegen K100s zweites Tor steht.*

**Und die Absenkung ist der eigentliche Gegenstand:**

```c
uint16_t q;
{
    q = (*(volatile uint16_t *)(d->basis + 12));      /* EINE Lesung */
    if (!(q <= QMAX)) { *_grund = Geraetelug_ZuGross; return false; }
}
```

Die Bedingung steht auf `q` und nicht auf einem zweiten Zugriff. Dafür trägt der Erzeuger
seit heute `Namen::ersetzungen` — eine Karte, die genau eine Bedingung lang lebt. *Ohne sie
stünde `(*(volatile uint16_t *)(d->basis + 12)) <= QMAX` in der Bedingung, und die Prüfung
wäre über einen anderen Wert als die Bindung.*

---

## 4. Was diese Entscheidung NICHT kauft

* **Sie prüft nicht, ob das Gerät die Rede hält.** Sie prüft, dass das Programm nachsieht.
  *Das ist der ganze Unterschied zu Form 2, und er ist der Zweck.*
* **`e` trägt seinen Typ hier NICHT.** Im `else`-Zweig einer fehlbaren Registerlesung ist
  `e` deklariert, aber `M119` kennt ihn nicht — `return e;` fällt mit *„`e` is declared
  nowhere"*. Der Grund ist bekannt und liegt woanders: die Typbindung für `fehlername`
  hängt an der Signatur des Gerufenen und steht in `m1.rs`, **einer Datei, die diese Bahn
  nicht anfasst.** *Der Verlust ist klein und benannt: an einem Register gibt es genau EINEN
  erklärten Grund, und `return R::C;` sagt dasselbe wie `return e;`.*
* **Sie deckt nicht jede Lesestelle.** `R011` sieht die eigenen Ausdrücke einer Anweisung
  und die Argumente eines blanken Rufs. Ein Prädikat in einem `requires` der rufenden
  Funktion, ein `narrow`-Ort und die Schranke einer Schleife stehen nicht darin — dieselbe
  Reichweite, die `R005`/`R006` seit «B23» haben, und sie ist hier ausgeschrieben statt
  vorausgesetzt.
* **Sie öffnet `let … else` nicht für den `option`-wertigen Ort.** Diese dritte Hälfte
  bleibt offen und behält ihre `C001`-Absage; sie hat einen anderen Grund (`None` trägt
  keinen `reason`) und eine andere Antwort.
* **Sie sagt nichts über ein `requires` OHNE `else`.** Das bleibt eine gezählte Pflicht, und
  `gabbro pflichten` führt sie weiter als `D`. *Wer sie schließen will, schreibt ein `else`
  daneben — die Ratsche dafür ist die Pflichtenzählung selbst.*
