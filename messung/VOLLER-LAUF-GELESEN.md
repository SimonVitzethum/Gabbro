# Der volle Lauf, diesmal GELESEN — **eine Überlebende, und Stufe 10 ist grün**

*Gemessen am 2026-09-01, lokal (`free -g` vor dem Lauf: 31 GB gesamt, 14 verfügbar, 20 Kerne;
`ki-pc-fisch-101` nicht angefasst). Mutationslauf 06:24 → 06:37:23, **13 min 20 s**;
`pruefe-emission.sh` **33,2 s** Wanduhr / 24,5 s Nutzerzeit.*

Zwei Posten standen offen, und beide waren dieselbe Klasse: **ein Lauf, dessen Ausgabe
niemand gelesen hat.**

> `abnahme.py` verwirft die Ausgabe des Mutationslaufs; ein Nachlauf kostet 13 min.

> **Stufe 10 von `pruefe-emission.sh` (die Bibliothekskette) liegt hinter dem
> Stufe-9-Schnitt** und ist heute nicht ein einziges Mal gelaufen.

---

## 1 — Die Mutationen: **375 von 376 gefangen, EINE überlebt**

```
377 Mutationen im Katalog
  1 ungueltig  -- vorfahren-ohne-schranke (K003): uebersetzt nicht, zaehlt nicht mit
375 gefangen   -- 99 %
  1 UEBERLEBT
```

Das Gerüst hat sich vorher selbst geprüft: `Nullmutation: UEBERLEBT`,
`Giftmutation: gefangen` — eine Änderung ohne Wirkung bricht keine Probe, eine tote
Bereichsprüfung wird gefangen.

### Die Überlebende, mit Namen

```
ungelesene-bindung-bekommt-kein-void        emit.rs        Flaeche: code
```

Sie streicht die `(void)r2;`-Zeile für eine `let`-Bindung, die niemand liest. Das erzeugte C
trägt dann `unused variable`, und `cc -Wall -Werror` weist die Einheit zurück.

**Und sie ist kein blinder Fleck, sondern ein Fleck an der falschen Stelle:** der
Katalogeintrag nennt selbst den Wächter, der sie fängt — `pruefe-emission.sh` Stufe 9, an
`messung/proben/probe-let-ohne-leser.gab`. Der Mutationslauf fragt `cargo test`, und
`cargo test` übersetzt kein C.

> **`375 von 376` ist eine Aussage über die Testsammlung, nicht über den Baum.** Die eine
> Überlebende ist die einzige Regel im Katalog, deren Wächter außerhalb von `cargo test`
> steht — *sie überlebt nicht ungesehen, sie überlebt in einem anderen Zimmer.*

**Der Befund liegt in `crates/` und gehört der zweiten Bahn.** Gemeldet, nicht geheilt.

### Die Bezugsgröße, die `375 von 376` sonst verschweigt

| Fläche | Mutationen | |
|---|---:|---|
| `pruefer` | 243 | die Absagen. Gebaut, mutierbar. |
| `code` | 92 | die C-Emission; 25 Übersetzungseinheiten, 6 davon Fragmente |
| `annotation` | 39 | der Wunschform-Kanal (`gabbro pflichten --isabelle`) |
| `schablone` | 3 | überwiegend ENTWORFEN — was kein Code ist, fängt keine Mutation |

*Eine Fläche mit 0 Mutationen ist nicht gedeckt, sondern unbeschädigbar.*

### Zwei Zahlen daneben, die gealtert sind

* **`CLAUDE.md` sagt `340` Mutationen und `10 min 25 s`** (nachgemessen 2026-08-30). Heute
  sind es **377** und **13 min 20 s**. *Ein Katalog, der wächst, macht jede Zahl daneben zu
  einer Jahreszahl* — genau der Satz, der in `CLAUDE.md` über der Zahl steht.
* **`mutiere-pruefer.proben_laufen()` fährt `cargo test` OHNE `--no-fail-fast`.** Für die
  Frage *fällt irgendeine Probe?* ist das richtig und billiger; für die Frage *welche
  fallen?* wäre es falsch. **Die zweite Frage stellt dieses Werkzeug nicht** — es druckt je
  Mutation `gefangen` oder `UEBERLEBT`, nicht die Liste der gefallenen Proben. *Die Regel
  aus `CLAUDE.md` ist hier bewusst nicht verletzt, sondern nicht anwendbar.*

## 2 — Stufe 10: die Bibliothekskette, **acht von acht grün**

Die einzige Stufe mit einem **Binder** — und damit die einzige, die überhaupt messen kann,
welcher Name nach außen bindet. Sie lief heute zum ersten Mal.

```
== Stufe 10: die Bibliothekskette, mit Binder ==
  1. abi:           ok (zwei .gabi, je mit Marke)
  1b. Ausfuhr:      ok (Traeger drin, die beiden privaten Helfer nicht)
  2. pruefe:        ok (0 errors, 0 hints ueber die Grenze)
  3. cc -Werror:    ok (drei Einheiten, getrennt uebersetzt)
  4. Bindung:       ok (drei pub-Namen aussen, begrenze/verdopple nicht)
  5. binden:        ok (-O0 und -O2, ein Programm aus drei Objekten)
  6. Ergebnis:      ok (2007 65535 -- der private Helfer hat gedeckelt)
  7. Sprechprobe A: ok (verfaelschter privater Helfer aendert das Ergebnis)
  8. Sprechprobe B: ok (N039 sagt ab, und der Binder haette es sonst getan)

== EMISSION: ALL PASS -- 25 durchgestochen, 112 von 112 uebersetzen, 1 umgekehrte Probe ==
```

**Kein Befund — und das ist einer.** Die Erwartung war die Klasse von `pruefe-luecken.py`
vom Vorabend: *fünfzehn Verdrehungen, nie gefahren, und der erste Lauf fand zwei tote Anker.*
Hier hält der ungefahrene Abschnitt. `nm` fragt den Binder und nicht den Erzeuger, und die
Antwort ist die richtige: `lege_ab lies mische` außen, `begrenze` und `verdopple` nicht.

### Der Befund liegt eine Ebene höher: **die Rechnung von gestern ist abgelaufen**

`messung/ABNAHME-STELLEN.md` hat am 2026-09-01 ausgerechnet, was es kostete, den
Schnelllauf um `pruefe-emission.sh` zu erweitern:

> ```
> + pruefe-emission.sh   +32,8 s   zwischen 38 und 92 von 94   (40–98 %)
>                        = +15 %   obere Grenze +45, untere Grenze +0
> ```
> **Die untere Grenze bewegt sich nicht**, weil der Wächter heute selbst abgeschnitten ist —
> seine 45 Stellen wandern von *„nicht gefahren"* nach *„gefahren, aber nicht erreicht"*.

**Er ist nicht mehr abgeschnitten.** Er läuft bis zum Ende durch, `rc=0`, in 33,2 s. Damit
ist er weder `TEILMESSUNG` noch halb gefahren, seine 45 Stellen sind nicht unsicher, und
dieselben 33 Sekunden kaufen jetzt **beide** Grenzen:

```
heute                            zwischen 40 und 47 von 94    43 bis 50 %
+ pruefe-emission.sh (gruen)     zwischen 85 und 92 von 94    90 bis 98 %
                                 +33 s (+15 %)   untere Grenze +45, nicht +0
```

> **Die Zahl war richtig, als sie geschrieben wurde, und sie war es zwölf Stunden lang.**
> Der Hebel, der gestern *nichts Sicheres* kaufte, kauft heute 45 von 94 auf der unteren
> Grenze — nicht weil jemand ihn verbessert hat, sondern weil der Wächter dahinter grün
> geworden ist (`ff9d29a`, `112 von 112`).

**Gebaut wurde daraufhin trotzdem nichts, und der Grund ist der, der schon gestern galt:**
`pruefe-emission.sh` steht in `SCHWER`, weil es **`cargo run` je Einheit** fährt und die
Rechenlast auf `ki-pc-fisch-101` gehört (`CLAUDE.md`) — *eine Ausnahme, deren Grund der ORT
ist, lässt sich mit einer Zeitmessung nicht aufheben.* Was sich geändert hat, ist nicht die
Entscheidung, sondern **ihr Preis**, und der stand mit einer falschen Zahl daneben.

## Nachgemessen: **fängt Stufe 9 sie wirklich?**

Der Katalogeintrag NENNT den Wächter. *Ein Wächtername in einem Kommentar ist eine
Behauptung* — also wurde sie gefahren: Mutation angewandt, gebaut, `pruefe-emission.sh`
darüber, Quelle byteweise zurückgestellt und gegen SHA-256 geprüft.

```
== Stufe 9: jede Datei, die emittiert, muss auch uebersetzen ==
  UEBERSETZT NICHT: messung/proben/probe-let-ohne-leser.gab
  /tmp/…/regel.c:19:14: error: unused variable 'r2' [-Werror=unused-variable]
  111 von 112 emittierenden Dateien uebersetzen
== ABGESCHNITTEN in: Stufe 9 -- Ruecklaufwert 1 ==
```

**Der Eintrag stimmt, bis auf die Datei genau.** Die Überlebende ist damit keine unbewachte
Regel, sondern eine, deren Wächter in einer anderen Kette steht — *und diese Kette lief
heute zum ersten Mal seit ihrer Reparatur ganz durch.*

> **Zwei Läufe, die einander brauchen:** der Mutationslauf sagt, dass `cargo test` die Regel
> nicht hält; `pruefe-emission.sh` sagt, dass sie trotzdem gehalten wird. **Keiner der beiden
> sagt es allein**, und in einer Abnahme, die den einen ausläßt und die Ausgabe des anderen
> verwirft, sagt es niemand.

## Was hier NICHT gemessen ist

1. **Ob die 375 gefangenen Mutationen von der RICHTIGEN Probe gefangen werden.** Gemessen
   ist, dass *irgendeine* fällt — `proben_laufen()` liest den Rücklaufwert von `cargo test`,
   nicht die Liste. *Eine Regel kann von der Probe einer anderen Regel gedeckt sein.*
2. **Die 6 Fragmente**, die `pruefe-emission.sh` baut, sind nicht dieselben wie die vier, die
   niemand fährt (`F01`, `F03`, `F05`, `F09`). Was niemand fährt, kann keine Mutation fangen.
3. **`25 durchgestochen` ist nicht `112 übersetzen`.** Durchgestochen heißt erzeugt,
   übersetzt, AUSGEFÜHRT und mit einer Handschrift verglichen; die 112 sagen nur, dass `cc`
   die Ausgabe annimmt. *Ein Programm, das übersetzt und falsch rechnet, fällt der zweiten
   Regel nicht auf* — der Wächter druckt diesen Satz selbst.
