# Zwei Blindstellen, an derselben Datei gefunden und nicht auf sie beschränkt

*Gemessen am 2026-08-31, Bahn F5, Posten 2. `F05`s `cc`-Absagen sind drei; die erste
(`exit`) steht in [`C-NAMEN.md`](C-NAMEN.md). **Diese beiden treffen nicht nur `F05`**, und
sie haben verschiedene Antworten bekommen — eine Absage und eine Absenkung. Der Unterschied
ist gemessen und nicht gewählt.*

---

## 1. Der `W24`-Vorlauf, beide Formen durch den UNVERÄNDERTEN Prüfer

### 1.1 Ein Feldzugriff auf etwas, das keine Felder hat

```gabbro
extern fn recv(ep : u64) -> u64 effects { reads ep } costs <= 4 ops;

impl fn dienst(ep : u64) -> u64 effects { reads ep } costs <= 16 ops
{
    let m = recv(ep);
    return m.op;
}
```

```
3 items, 0 errors, 0 hints
  M1 saw 3 expressions, 1 of them without a type (67 % coverage)
```

**Der Prüfer hat die Lücke GEZÄHLT und nicht benannt.** Der Erzeuger schreibt 21 Zeilen C mit
`return m->op;`, und `cc` antwortet *invalid type argument of `->` (have `uint64_t`)*.

> *Eine Deckungszahl ist keine Absage.* Die Zeile `1 of them without a type` stand in
> derselben Ausgabe wie `0 errors` — **das Werkzeug wusste es und sagte es an der falschen
> Stelle.**

### 1.2 Und der Nachbarfall ist schlimmer: ein Feldname, den es nicht gibt

```gabbro
type Nachricht = { op : u64, };
impl fn dienst(m : Nachricht) -> u64 effects { pure } { return m.gibt_es_nicht; }
```

```
3 items, 0 errors, 0 hints
```

**Auch ein DEKLARIERTER Verbund wurde nicht befragt.** `cc`: *`Nachricht` has no member named
`gibt_es_nicht`*.

**Die Ursache steht in einer Zeile Rust**, `umgebung.rs::feld_von`: sie gibt `Typ::Unbekannt`
zurück — für **drei** verschiedene Lagen.

| Lage | was sie heißt |
|---|---|
| der Träger hat dieses Feld nicht | **ein Mangel** |
| der Träger hat gar keine Felder | **ein Mangel** |
| der Typ des Trägers hat sich nie aufgelöst | ein ehrliches Nichtwissen |

*Solange eine Funktion sie zusammenwirft, kann kein Pass die zwei benennen, ohne die dritte
falsch abzuweisen.* **`Feldurteil` trennt sie**, und `M134` weist die ersten beiden ab.

### 1.3 Eine `let`-Bindung, die nie gelesen wird

```gabbro
impl fn dienst(a : u64) -> u64 effects { writes a } costs <= 16 ops
{
    let r2 = spuelen(a);
    return 0;
}
```

```
3 items, 0 errors, 0 hints    und 21 Zeilen C
cc: error: unused variable 'r2' [-Werror=unused-variable]
```

---

## 2. `M134` — die Absage, und was der Korpus an ihr berichtigt hat

Über die 418 Dateien fällt `M134` in **einer**: `messung/fragmente/F05.gab`:173, und die ist
schon zweimal abgewiesen. *Die Regel kostet den Baum nichts.*

> ### Der erste Bau war FALSCH, und `F04` hat es in derselben Minute gesagt
>
> Er kannte die Registerfelder und die Verbundfelder — und nicht die **Parameterliste eines
> `device`**. `messung/fragmente/F04.gab`:146 schreibt `q.AVAIL_IDX % q.n`, und
> `device Virtq(base : Iova, n : u16 in 1 .. QMAX)` erklärt `n` dort. **`F04` ist
> DURCHGESTOCHEN** — es erzeugt, übersetzt unter `-Werror` und läuft.
>
> *Eine Absage an einer Datei, die läuft, kann nur der Fehler der Regel sein.* Die
> Parameterliste eines `device` IST sein Konstruktor, und ihre Namen sind lesbare Orte — der
> Kommentar dazu steht seit dem 2026-08-14 in `umgebung.rs`, drei Funktionen weiter oben.

**Was `M134` NICHT erreicht** (W10): einen Feldzugriff, dessen Träger ein `tagged type`, ein
Feld, ein Funktionszeiger oder `never` ist. Die geben `Unklar` und sind **ungemessen, nicht
freigesprochen.**

---

## 3. Die ungelesene `let`-Bindung — eine Absage GEBAUT, GEMESSEN und ZURÜCKGENOMMEN

Der naheliegende Schluss war eine Absage, und er hatte ein gutes Argument: der Erzeuger
schreibt für einen ungelesenen **Parameter** schon `(void)k;`, und der Kommentar an jener
Stelle begründet es so —

> *„Der Anwender hat die erzeugte Zeile nicht geschrieben; eine Warnung darin sagt nichts über
> ihn."*

**Bei einem `let` ist es umgekehrt: die Zeile ist seine.** Und dieselbe Wirkung ist ohne
Bindung schreibbar — ein nackter Ruf ist eine Anweisung der Sprache, prüft sauber, senkt ab
und übersetzt (gemessen). Also: absagen.

**Gebaut, über die 418 Dateien gemessen — und die Messung hat das Argument umgeworfen.**

| Lauf | fällt in | davon Mängel |
|---|---:|---:|
| erster Bau (eigener Namensläufer) | **22** | 0 |
| Indizes in Schreibzielen mitgezählt | **21** | 0 |
| mit `emit::benutzte_namen`, dem Läufer des Erzeugers | **17** | **0** |

**Siebzehn Dateien, und keine davon ein Mangel:** dreizehn Giftproben, vier `fnptr`-Proben,
eine Messdatei. *Eine Bindung zu setzen und den Wert nicht zurückzulesen ist etwas, das dieser
Korpus schreibt* — in Giftproben, weil eine Regel etwas anderes messen soll, und in
Zwischennamen.

> **Regel A schneidet hier andersherum.** Der Mangel, den die Absage verhindert hätte, hat
> **null** Instanzen, die überhaupt emittieren; die Absage selbst hätte **17** gekostet. *Kein
> Konstrukt ohne gemessenen Bedarf — und keine ABSAGE ohne gemessenen Mangel.*

**Gebaut wurde stattdessen die Absenkung: `(void)r2;`**, genau die Zeile des ungelesenen
Parameters, **aus demselben Läufer**. `emit::benutzte_namen` ist jetzt `pub(crate)`, und es
gibt weiterhin nur einen — *eine zweite Antwort auf dieselbe Frage ist die Drift, die diese
Datei im ersten Anlauf selbst vorgeführt hat.*

### 3.1 Zwei Zwischenbefunde aus den drei Läufen, und beide gehören dem Prüfer

* **`crate::eigene_ausdruecke` gibt für `StmtArt::Ruf` `Vec::new()` zurück.** Ein nackter Ruf
  trägt seine Argumente also für jeden Pass, der über diesen Helfer liest, nicht bei —
  `let p5 = verifizierer_starten(p4); root_task_starten(p5);` sah für ihn wie eine ungelesene
  Bindung aus. Dieselbe Bauart wie der `Schleife => Vec::new()`-Zweig, den der Kommentar der
  Funktion selbst als fail-open festhält. *Hier hat er vier Dateien FALSCH abgewiesen statt
  etwas durchzulassen — dieselbe Ursache, die andere Richtung.*
* **Ein Schreibziel trägt Lesungen in seinen Indizes.** `q.AVAIL_RING[platz].e = head;` liest
  `platz`. Wer nur `o.basis` nimmt, verliert sie.

---

## 4. Was jetzt gemessen ist, und was es nicht sagt

```
Dateien, die emittieren und uebersetzen:   83 von 83   (cc -std=c11 -O0 -Wall -Wextra -Werror)
ungenutzte `let`-Bindung im erzeugten C:    0
Feldzugriff auf etwas ohne Felder:          0
andere `cc`-Fehler:                         0
```

`pruefe-emission.sh` Stufe 9 liest dieselbe Regel über `beispiele/*.gab` und `messung/*/*.gab`
und meldet **79 von 79, 0 benannte Ausnahmen**. *Die Marke `messung/*/` steigt von 22 auf 25 —
drei Gegenproben, je eine zu `N041`, `M134` und der `(void)`-Absenkung.*

**Was das NICHT sagt:**

* **Übersetzen ist nicht rechnen.** 79 Dateien nimmt `cc` an; **25** sind durchgestochen —
  erzeugt, übersetzt, ausgeführt und gegen eine Handschrift verglichen.
* **`M134` deckt drei Trägerarten, nicht alle** (§2).
* **Die `(void)`-Absenkung deckt die Bindung, nicht die Zuweisung.** Ein `let mut x = 0; x = 5;`
  ohne Leser fällt weiter an `cc -Wextra`s *unused-but-set-variable*. Der Korpus hat keinen
  solchen Fall — **ungemessen, nicht freigesprochen.**
