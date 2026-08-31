# Die Einheitensicht: `lean` klebt, `pruefe` schleift — und `use` löst längst auf

*Gemessen am 2026-08-31, lokal (`free -g`: 31 GB gesamt, 12 GB verfügbar, 20 Kerne), gegen
den **unveränderten** Prüfer am Stand `09d6c4f`.*

> **Der W24-Vorlauf hat den Befund zur Hälfte umgedreht.** Der Auftrag stand als *„`use` wird
> gelesen und nicht aufgelöst"*. Gemessen wird: **`use` wird gelesen UND aufgelöst** — der
> Resolver ist vollständig, modulbewusst und `use`-bewusst. Was fehlt, liegt eine Ebene
> höher: die andere Datei steht nie in derselben `Umgebung`.

---

## 1. Der W24-Vorlauf, wörtlich

`programmlogik/beispiel/betrieb.gab` sagt in seiner ersten Zeile über sich selbst: *„Datei 2
— die Rümpfe. Sie schreiben in eine Tabelle, die in Datei 1 steht."*

```
$ ./target/debug/gabbro pruefe programmlogik/beispiel/lager.gab programmlogik/beispiel/betrieb.gab
hint:  [H008] lager.gab:12:10: `HALLE` protects ["Faecher"] but is taken nowhere
lager.gab: 6 items, 0 errors, 1 hints
error: [N040] betrieb.gab:36:56: `Marken` names no type
error: [N040] betrieb.gab:45:51: `Menge` names no type
error: [M109] betrieb.gab:23:14: `Faecher` in `ensures` is not declared here
error: [M119] betrieb.gab:42:31: `Faecher` is declared nowhere
error: [H016] betrieb.gab:11:59: this `locks` effect names `HALLE`, and no `lock` declaration explains it
betrieb.gab: 9 items, 5 errors, 0 hints
exit=1
```

**Es sind FÜNF Absagen, nicht zwei.** Der Auftrag nannte `N040` und `M119`; dazwischen stehen
ein zweites `N040`, ein `M109` und ein `H016`. *Ein Griff ist keine Messung — und der Griff
war hier um mehr als die Hälfte zu klein.*

Derselbe Aufruf über den Lean-Kanal:

```
$ ./target/debug/gabbro lean programmlogik/beispiel/lager.gab programmlogik/beispiel/betrieb.gab
    @program 1  units 2  routines 4  bodies 4  refused 0  places 4
exit=0
```

**Null Absagen.** Dieselben zwei Dateien, derselbe Prüfer, dieselben Pässe.

## 2. Warum `lean` auflöst und `pruefe` nicht

Die Antwort steht nicht im Resolver. Sie steht im Treiber, und sie ist drei Zeilen lang.

**`main.rs`:304–316 (`"lean"`)** — die Dateien werden zu EINEM Text geklebt und EINMAL geparst:

```rust
let mut ganz = String::new();
for datei in rest {
    ganz.push_str(&format!("-- >>> {datei}\n"));
    ganz.push_str(&quelle);
}
let (baum, mut absagen) = gabbro_syntax::lies("<program>", &ganz);
gabbro_check::pruefe(&baum, &mut absagen);
```

**`main.rs`:751–768 (`befehl_pruefe`)** — eine Schleife, und je Durchlauf ein eigener Baum:

```rust
for datei in &dateien {
    let (baum, mut absagen) = gabbro_syntax::lies(datei, &ganz);
    let bericht = pruefe(&baum, &mut absagen);
}
```

> **Der Lean-Kanal baut keine „dateiübergreifende Sicht".** Er *konkateniert Text.* Was
> danach auflöst, löst auf, weil beide `module`-Blöcke in demselben Parsebaum stehen — und
> der Resolver war modulübergreifend schon immer.

**Der Resolver ist `umgebung.rs::kandidaten`** (Zeile 376–417), und er kann alles, was
gebraucht wird:

* er läuft die Modulkette von innen nach außen (`von` → `von`-Elter → … → Wurzel),
* und er folgt danach den `use`-Zeilen jedes Moduls auf diesem Weg:
  `if z.rsplit("::").next() == Some(kurz) { out.push(z.clone()) }`.

**Also taugt die Sicht.** Sie ist nicht „etwas anderes" — sie ist genau die gesuchte, und sie
wird dem Prüfer nur nie gegeben.

### Die Gegenprobe, die es zum Befund macht

`use` ist **nicht** Zierrat: nimmt man die vier `use`-Zeilen aus `betrieb.gab` heraus und
klebt trotzdem, fällt der geklebte Text wieder:

```
$ grep -v '^use ' betrieb.gab > betrieb-ohne-use.gab
$ ./target/debug/gabbro lean lager.gab betrieb-ohne-use.gab
error: [N040] <program>:53:56: `Marken` names no type
error: [N040] <program>:62:51: `Menge` names no type
error: [M109] <program>:40:14: `Faecher` in `ensures` is not declared here
exit=1
```

**Drei Absagen bleiben, zwei verschwinden.** Das ist die schärfere Hälfte der Messung: `use`
trägt `Marken`, `Menge` und den `ensures`-Namen — aber `M119` und `H016` verschwinden
**auch ohne `use`**, sobald der Text nur geklebt ist. *Zwei Pässe fragen den Resolver, zwei
fragen die Karte direkt* — dieselbe Klasse, die `umgebung.rs`:452 schon einmal an `M103`
gekostet hat («*Die Karte direkt zu befragen war ein Loch in `M103`*»).

## 3. Die Reichweite (W25 — die Zahl belegt ihren Nenner)

Über **alle 485** `.gab`-Dateien des Baums, gezählt und nicht geschätzt:

| Größe | Zahl |
|---|---|
| `.gab`-Dateien gesamt | **485** |
| davon mit mindestens einer `use`-Zeile | **10** |
| `use`-Zeilen gesamt | **25** |
| verschiedene Zielmodule | **12** |
| `use`-Zeilen, deren Zielmodul in DERSELBEN Datei steht (löst heute auf) | **8** |
| `use`-Zeilen, deren Zielmodul in einer ANDEREN Datei steht | **14** |
| `use`-Zeilen, deren Zielmodul im ganzen Baum **nirgends** steht | **3** |

Die drei Nirgends-Zeilen stehen alle in `messung/fragmente/F01.gab` und zeigen auf
`caprock::mem::Rights`, `caprock::mem::Region` — ein Modul, das dieser Baum nicht hat.
**Die müssen weiter fallen**, und sie tun es (siehe §4).

> **Der Nenner ist 485 und nicht 10.** Die Auflösung berührt **2,1 %** der Dateien. *Das ist
> keine kleine Zahl, weil sie klein ist, sondern eine ehrliche* — und die Gegenrichtung über
> die anderen 475 ist genau deshalb billig zu messen.

## 4. Wie viele Absagen verschwinden

Fünf Einheiten, die der Korpus selbst als Einheiten schreibt. Je Datei einzeln (`pruefe`)
gegen die Einheit gemeinsam (`lean`, der einzige Kanal, der heute klebt):

| Einheit | Dateien | einzeln | gemeinsam | Δ |
|---|---|---|---|---|
| `programmlogik/beispiel` | 2 | 5 | 0 | **−5** |
| `messung/abi-proben/dienst` | 2 | 2 | 0 | **−2** |
| `messung/abi-proben/mischt` | 3 | 4 | **2** | **−2** |
| `messung/abi-proben/nutzt-beide` | 3 | 2 | 0 | **−2** |
| `messung/fragmente/F01` | 2 | 1 | 1 | **0** |
| **Summe** | **12** | **14** | **3** | **−11** |

**Elf Absagen verschwinden.** Nach Kennung: `K003`×5, `H016`×4, `N040`×2, `M109`×1, `M119`×1
— minus die zwei, die neu **auftauchen**.

### Und zwei Absagen tauchen NEU auf — das ist der eigentliche Befund

`messung/abi-proben/mischt.gab` sagt in seiner Kopfzeile über sich selbst:

> *„Das ist der Zyklus, den weder `speicher` noch `geraet` allein sehen kann — jede hat ihren
> Rang für sich vergeben, und beide haben `rank 0` gewählt."*

Einzeln geprüft meldet die Datei `H016`×2 und `K003`×2 — **lauter Namensrauschen**, und den
Ring selbst **nicht**. Gemeinsam geprüft verschwindet das Rauschen und der Ring erscheint:

```
error: [H012] <program>:75:9: this call takes `GERAET` (rank 0) while `SPEICHER` (rank 0) is held here
error: [H012] <program>:86:9: this call takes `SPEICHER` (rank 0) while `GERAET` (rank 0) is held here
```

> **Die Einheitensicht ist nicht nur Schweigen gegen Rauschen.** Sie ist die Bedingung dafür,
> dass ein Sperrring über Bibliotheksgrenzen überhaupt **gefunden** wird. Heute ist er
> unsichtbar, und die Datei, die ihn trägt, weiß das über sich und sagt es in Zeile 1.
> *Der Korpus hat die Lücke vor dem Prüfer beschrieben.*

## 5. Was diese Messung NICHT sagt

* **Sie misst `lean` als Stellvertreter für ein geklebtes `pruefe`.** Beide rufen denselben
  `gabbro_check::pruefe` über denselben Baum; was `lean` zusätzlich tut (Lean-Export), kommt
  nach der Prüfung. *Aber gemessen ist der Stellvertreter, nicht die Sache.*
* **Sie sagt nichts über `pub`.** Ob `pub` heute entscheidet, was ein `use` erreichen darf,
  ist eine eigene Messung — `kandidaten` fragt nicht danach.
* **Sie sagt nichts über Namenskollisionen.** Zwei Module mit demselben Namen im geklebten
  Text sind ungemessen.
* **Die Zahl 11 gilt für 12 Dateien**, nicht für 485. Über die anderen 473 ist bisher nichts
  gemessen — genau das ist die Gegenrichtung, und sie steht noch aus.
