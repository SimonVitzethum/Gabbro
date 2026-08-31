# Soll ein Raum, der nichts absenkt, im Typ stehen? — die Rechnung, ohne Urteil

**Gemessen am 2026-08-31**, lokal (`free -g`: 31 GB gesamt, 14 verfügbar, 20 Kerne).
Binärprogramm: der Stand nach `fa6f056`.

`messung/ADRESSRAEUME.md` hat gezeigt, dass `ctyp` **keinen** Raum liest, hat `port` als
falsch abgesagt und die anderen fünf einzeln nachgerechnet: kein Mangel. Übrig blieb eine
Frage, die keine Messung war: *soll ein Raum, der nichts absenkt, überhaupt im Typ stehen?*

**Hier steht die Rechnung dazu und keine Entscheidung.** Was gemessen ist, ist gemessen;
was ein Urteil wäre, steht am Ende als Frage.

---

## §1 Fünf Räume, ein md5

Dieselbe Datei sechsmal, verschieden nur im Raumwort — ein Zeigerparameter, dereferenziert
und weitergereicht (die Probe steht darunter, das Raumwort ist das einzige Veränderliche):

```gabbro
pub extern fn fremd(p : ptr<S, r> Zelle) -> u32 effects { reads p } costs <= 2 ops;
pub impl fn liest(p : ptr<S, r> Zelle) -> u32 … { return fremd(p); }
```

`gabbro emit`, Kopf und Kommentare abgeschnitten, `md5sum`:

```
c4f956bf867fc47b50df0fd3a5cf0bde  c-boot.txt
c4f956bf867fc47b50df0fd3a5cf0bde  c-code.txt
c4f956bf867fc47b50df0fd3a5cf0bde  c-dma.txt
c4f956bf867fc47b50df0fd3a5cf0bde  c-mmio.txt
c4f956bf867fc47b50df0fd3a5cf0bde  c-normal.txt
```

**Fünf Räume, eine Prüfsumme.** `port` fällt als sechster heraus, aber nicht mit anderem
Text: `gabbro emit` endet mit **1** und `C001` (die Absage vom 2026-08-31).

*Und der Gegensatz steht daneben, im selben Typ:* das **Recht** senkt ab.

```c
uint32_t fremd(const Zelle *p);   /* ptr<normal, r>  */
uint32_t fremd(Zelle *p);         /* ptr<normal, rw> */
```

`ptr<S, R> T` trägt zwei Angaben. **Eine kommt im C an, die andere nicht.**

## §2 Wer `z.raum` überhaupt liest

`grep -rn '\.raum\|Raum::'` über `crates/`, ohne Parser und ohne die `enum`-Erklärung:

| Stelle | was sie tut | Gegenstand |
|---|---|---|
| `m3.rs`:120 | sammelt den Raum je Zeigerparameter | **`R008`** |
| `m3.rs`:626 | `z.raum == Raum::Dma` | **`R001`** |
| `m3.rs`:56–62, :658, :710 | der Raumname in der Absagenprosa | — |
| `emit.rs`:4575 | `z.raum == Raum::Port` | **`C001`** (Rumpf mit Portzeiger) |
| `emit.rs`:2507/2537/2548 | `d.raum` am **`device`** — ein anderes Feld | `C001` ×3 |
| `manifest.rs`:163–170 | der Raum eines `retires` — wieder ein anderes Feld | Stilllegungsannahme |
| `abi.rs`::`text_von` | schreibt die Quellzeile wörtlich in die `.gabi` | **die Schnittstelle** |

**Der Raum am ZEIGER hat genau drei Leser mit einem Urteil**: `R008`, `R001`, und seit
heute die `port`-Absage im Erzeuger.

## §3 `R008` ist eine VOLLSTÄNDIGE Partition — 36 Paare gefahren

Sechs mal sechs Programme: ein `extern fn` nimmt `ptr<Y, r>`, ein Rumpf reicht ein
`ptr<X, r>` hinein.

|  | normal | mmio | dma | code | boot | port |
|---|---|---|---|---|---|---|
| **normal** | · | R008 | R008 | R008 | R008 | R008 |
| **mmio** | R008 | · | R008 | R008 | R008 | R008 |
| **dma** | R008 | R008 | · | R008 | R008 | R008 |
| **code** | R008 | R008 | R008 | · | R008 | R008 |
| **boot** | R008 | R008 | R008 | R008 | · | R008 |
| **port** | R008 | R008 | R008 | R008 | R008 | · |

**30 von 30 gemischten Paaren fallen, 6 von 6 gleichen gehen durch.** Keine Ausnahme, keine
Halbordnung, keine Verträglichkeit zwischen zwei Räumen.

`R001` kommt für **genau einen** Raum dazu: ein `ops`-Träger hinter `ptr<dma, rw>` fällt,
hinter den anderen fünf nicht (je Raum eine Probe, alle sechs gefahren).

## §4 Und die Partition hält über die Bibliotheksgrenze

`gabbro abi` schreibt das Raumwort wörtlich in die `.gabi`:

```
pub extern fn nimmt(p : ptr<mmio, r> Zelle) -> u32 effects { reads p } costs <= 2 ops;
```

`gabbro pruefe --with bib.gabi nutzer.gab`, wo der Nutzer ein `ptr<normal, r>` hineinreicht:

```
error: [R008] nutzer.gab:17:9: `reicht` passes `p` in space `normal`
             to a parameter of `nimmt` declared `mmio`
```

Und die Gegenprobe, derselbe Nutzer mit `ptr<mmio, r>`: **`7 items, 0 errors, 0 hints`.**

*Der Raum ist damit kein internes Wort einer Übersetzungseinheit, sondern Teil der
Schnittstelle* — und er wird an der Grenze gehalten.

## §5 Was ein C-Werkzeug davon sehen könnte: nichts

Das ist eine **Folgerung aus §1** und keine eigene Messung, und sie steht als solche da: da
`ptr<normal, …>` und `ptr<mmio, …>` denselben C-Text erzeugen, gibt es im Erzeugnis nichts,
woran ein C-Werkzeug die Verwechslung erkennen könnte. **Es ist nicht so, dass `cc` sie
übersieht — sie steht dort nicht.**

Damit ist `R008` **die einzige Zeile** zwischen einem Programm, das einen gewöhnlichen
Zeiger für einen Geräteszeiger hält, und einem grünen Bau. Dieselbe Lage wie bei den
stillen Namenskollisionen von heute (`messung/STILLE-KOLLISIONEN.md`), nur aus dem
umgekehrten Grund: dort wird zu viel in denselben C-Namen abgebildet, hier zu viel in
denselben C-Typ.

## §6 Der Bedarf, gezählt (Regel A)

Über alle **446** `.gab`-Dateien des Baumes, Kommentare abgeschnitten:

| Raum | Zeigerstellen | davon in `gift/` | `device … at` | davon in `gift/` |
|---|---:|---:|---:|---:|
| `normal` | 249 | 83 | 1 | 0 |
| `mmio` | 28 | 10 | 33 | 16 |
| `dma` | 13 | 3 | 6 | 4 |
| `code` | 2 | 0 | 0 | 0 |
| `boot` | 1 | 0 | 0 | 0 |
| `port` | 3 | 1 | 1 | 1 |

Die seltenen einzeln, damit keine Zahl ohne Ort dasteht:

* `code`: `beispiele/22-bootstrecke.gab`:79 und `messung/fragmente/F07.gab`:23, beide
  `extern fn melde_roh(text : ptr<code, r> Text)`.
* `boot`: `messung/grammatik/raumworte.gab`:86, `impl fn grundtakt_lesen(b : ptr<boot, r> …)`.
* `port`: `messung/grammatik/geraeteworte.gab`:63 und `raumworte.gab`:100 — beide seit dem
  2026-08-31 `extern fn`, also ohne Rumpf — und `beispiele/gift/415`.
* `device … at normal`: **eine** Stelle, `messung/fragmente/F09.gab`:61 — ein Fragment, das
  nicht emittiert wird; `at normal` ist am Erzeuger abgesagt (`emit.rs`:2507).

## §7 Was es kostet, das Wort WEGZUNEHMEN

Die Frage lässt sich von der anderen Seite messen: welche Absagen verlieren ihren Eingang,
wenn `ptr<S, R> T` seinen Raum verliert?

| verliert seinen Eingang | Probe, die dann nicht mehr fällt |
|---|---|
| `R008` (`m3.rs`:120) | `beispiele/gift/259-raum-laeuft-durch.gab` |
| `R001` (`m3.rs`:626) | `beispiele/gift/58-ops-traeger-im-dma-raum.gab` |
| `C001` Rumpf mit Portzeiger (`emit.rs`:4575) | `beispiele/gift/415-portzeiger-im-eigenen-rumpf.gab` |

**Drei Giftproben, und die Grenze ist scharf:** die drei `device`-Absagen (`at normal`,
`at port`, `at dma`) lesen `d.raum` und nicht `z.raum` — sie überleben. `gift/416` bliebe
also stehen. Und über dem SAUBEREN Korpus kostet die Wegnahme **null Absagen**: keine der
**199** Zeigerstellen außerhalb von `gift/` mischt heute Räume — 296 insgesamt, 97 davon in
`gift/`, die zwei Spalten aus §6 aufaddiert.

*Das ist keine Entlastung, sondern die Eigenart der Regel.* `R008` ist eine Regel, deren
Ertrag darin besteht, dass ihr Fall im sauberen Korpus nicht vorkommt — genau wie `N041`
und `N042`. **Eine Regel an einer Verwechslung, die noch niemand gemacht hat, hat null
Treffer und nicht null Wert; ihr Nenner ist der Korpus, den es noch nicht gibt.**

## §8 Die Frage, unentschieden — und was an ihr hängt

Die Ausgangsfrage lautete *„soll ein Raum, der nichts absenkt, überhaupt im Typ stehen?"*
**Ihre Voraussetzung ist gemessen falsch, wenn „nichts tun" gemeint ist:** der Raum tut
etwas, nur nicht im Erzeugnis. Er partitioniert die Zeigertypen vollständig (§3), er reist
über die Bibliotheksgrenze (§4), und er trägt drei Absagen (§7).

Was übrig bleibt, ist die engere Frage, und sie ist ein **Urteil und keine Messung**:

> **Darf ein Wort im TYP stehen, dessen ganze Wirkung eine Prüferpartition ist?**

Zwei Dinge, die dabei zu wissen sind, und beide sind gemessen:

1. **Es gibt in C nichts, wohin es absenken könnte.** Der Raum ist eine Aussage über die
   **Herkunft** einer Adresse; C kennt keine Herkunft. `volatile` ist eine Aussage über die
   **Zugriffsform** und damit eine andere Aussage — `messung/ADRESSRAEUME.md` §3 rechnet
   nach, dass `mmio` heute nur deshalb richtig ankommt, weil jeder saubere `ptr<mmio, …>`
   auf einen `device`-Typ zeigt und das `volatile` von dort kommt. *Ein Raum, der nichts
   absenkt, ist hier keine Lücke in der Absenkung, sondern eine Eigenschaft ohne
   C-Gegenstück.*
2. **Der Baum kennt den Fall schon.** Ein `linear ghost type` kostet zur Laufzeit nichts;
   `pruefe-emission.sh` misst es an `F7` als eigene Stufe und stellt die Frage im Klartext
   („was kostet die Phasendisziplin zur Laufzeit — Antwort: nichts"). Der Unterschied: dort
   **verschwindet** etwas aus dem Erzeugnis, hier stand nie etwas darin.

**Was diese Rechnung ausdrücklich NICHT entscheidet**, und je ein Grund:

* **Ob `mmio` am Zeiger ein `volatile` bekommen soll.** Steht als Posten im `TODO.md`; es
  wäre eine Absenkung und keine Absage, und dafür fehlt der gemessene Fall — im sauberen
  Korpus zeigt kein `ptr<mmio, …>` auf einen Nicht-Geräte-Typ.
* **Ob `code` und `boot` bleiben sollen.** Zusammen **drei** Zeigerstellen, null
  `device`-Stellen. Das ist wenig; ob wenig zu wenig ist, ist eine Frage an die Sprache und
  nicht an diese Messung. *Wer sie streicht, streicht auch die zehn `R008`-Paare, die sie
  von den anderen vier trennen.*
* **Ob `R008` die richtige Härte hat.** Sie ist heute total: kein Paar ist verträglich, auch
  `normal` → `boot` nicht, obwohl `.boot` ein Linkerabschnitt gewöhnlichen Speichers ist
  (`SYNTAX.md`:1607). Eine Halbordnung wäre denkbar und ist nicht gemessen — es gibt im
  Korpus keinen einzigen Ruf, den sie erlauben würde und `R008` heute verbietet.
