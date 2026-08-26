# Die zwei ERZEUGER von Stufe 7 — gemessen, gebaut, und einer nicht gebaut

*Arbeitslauf 2026-08-21. Reihenfolge nach der Kopfzeile der Stufe: **erst der Erzeuger, dann
der Vertrag.** Vor jedem Bau steht eine Messung, und sie steht hier vor dem Bau, den sie
ausgelöst hat.*

Zwei Posten, dieselbe Gestalt: ein Kanal, der an der **Deklaration** existiert und keine
**Schreibform** hat. Der eine ist gebaut, der andere nicht — und die Null, die ihn stoppt, ist
keine Bedarfsnull, sondern eine **Konstruierbarkeitsnull**: das Programm, das Regel A
verlangt, lässt sich heute nicht schreiben.

> **NACHTRAG 2026-08-25 — Posten 2 ist ÜBERHOLT, und zwar am selben Tag.**
> Dieser Bericht buchte den zweiten Posten als **nicht gebaut**; **noch am 2026-08-21**
> wurden alle vier Hälften gebaut ([`FNPTR.md`](FNPTR.md)). *Die ZAHLEN unten stimmen
> weiter — `FNPTR.md` §1 rechnet sie nach und sie reproduzieren exakt; überholt ist die
> ENTSCHEIDUNG, nicht die Messung.* Der Wortlaut bleibt stehen, die Korrektur steht mit
> Datum daneben.
>
> **Warum das hier steht und nicht nur in `FNPTR.md`:** vier Tage lang trug der Kopf von
> Stufe 7 in `TODO.md` dieselbe überholte Zusage weiter — ein Satz, der wie ein Ergebnis
> aussieht und Arbeit verhindert, statt sie zu verzögern. *Er stand in zwei Dateien, und der
> Widerrufswächter las keine davon.* Seit heute liest er auch `messung/` (`WB2`).

<!-- widerruf:aus -->
| | Posten | Ergebnis |
|---|---|---|
| 1 | Ein `reason`-Wert hat keinen Erzeuger — «B9» ein zweites Mal | **gebaut**, 7 Absagen, 8 Giftproben, 10 Mutationen, 1 Beispiel |
| 2 | `fnptr` — die Sprache kennt kein `&f` | ~~**NICHT gebaut**, mit Zahl und Grund~~ — **gebaut am 2026-08-21**, siehe Nachtrag |
<!-- widerruf:an -->

---

## Posten 1 — der Grunderzeuger

### 1.1 Die Messung VOR dem Bau

Alles unten am 2026-08-21 erhoben, jede Zeile mit dem Befehl, der sie nachrechnet.

| Frage | Zahl | Befehl |
|---|---|---|
| `-> T or R`-Signaturen im sauberen Korpus | **6, alle an `extern fn`** | `grep -rn -e "-> .* or " beispiele/*.gab \| grep -v -e "-- "` |
| `reason`-Deklarationen im Korpus | **8** | `grep -rn -e "^reason " beispiele/*.gab \| wc -l` |
| Benutzungen eines Grundfall**namens** im Korpus | **0** | `grep -rn "KeinSlot" beispiele/` → nur die Deklaration selbst |
| `fehlername` (der Binder `e`) im Prüfer | **3 Zeilen, alle in `emit.rs`** | `grep -rn "fehlername" crates/` |

> **Die zweite Zeile ist die Aussage.** Acht `reason`-Deklarationen, und **kein einziger ihrer
> Fälle wird irgendwo genannt.** Der Erzeuger schrieb aus ihnen ein C-`enum`, und kein Pass
> wusste, dass die Namen darin existieren.

Und die dritte: **`fehlername` stand in genau einer Datei des Prüfers — im ERZEUGER.** Der
Binder war da, er band nichts. *Eine Klausel ohne Leser*, dieselbe Lochform wie `@version`,
`nested masked` und `lock … masks irqs`.

### 1.2 Die vier Handproben

Geschrieben, gelaufen, Ausgabe zitiert. Alle vier über
`ssh ki-pc-fisch-101 'cd gabbro-f && ./target/debug/gabbro pruefe <datei>'`.

```gabbro
-- P1
impl fn hol(x : u32) -> u32 or HolFehler … { if x == 0 { return HolFehler::Leer; } return x; }
```
> `Fehler: [M119] …:11:16: `HolFehler` is declared nowhere`
>
> **Die Form parste**, als `Ort` mit Feldsuffix — ein Ort namens `HolFehler` mit einem Feld
> `Leer`. *Sie war nicht verboten, sie war bedeutungslos.*

```gabbro
-- P2
impl fn hol(x : u32) -> u32 or HolFehler … { if x == 0 { return Leer; } return x; }
```
> `Fehler: [M119] …:11:16: `Leer` is declared nowhere` — der nackte Fallname ist nicht die Form.

```gabbro
-- P3
impl fn hol(x : u32) -> u32 or HolFehler … { return x; }
```
> `…p3-impl-mit-kanal.gab: 4 Items, 0 Fehler, 0 Hinweise`
>
> **Das ist das Loch in einer Zeile.** Eine Funktion erklärt einen Fehlerkanal, ihr Rumpf kann
> ihn nie benutzen, und nichts sagt es. Was der Erzeuger dazu schreibt, stand seit dem
> 2026-08-20 im erzeugten C:
> ```c
> (void)_grund; /* no Gabbro body can produce a reason -- the channel is declared, never written */
> ```
> *Der Befund stand im Erzeugnis und in keiner Absage.*

```gabbro
-- P4
let v = hol() else (e) { match e { Leer => …, Kaputt => … } }
```
> `Fehler: [M119] …:13:15: `e` is declared nowhere` — der Binder hatte keinen Typ.

### 1.3 Die Fläche — und sie ist nicht null, sondern stand im Ordner

**Regel B: die Schablone kommt von außen.** Sie kam, und zwar aus dem Fragmentkorpus, der aus
echtem Code übernommen ist:

| Stelle | Zeile | Befehl |
|---|---|---|
| `FRAGMENTE.md`:269 | `return Fehler::Buchfuehrung;` | `grep -n -E "return [A-Z][A-Za-z]*::" dokumente/FRAGMENTE.md` |
| `FRAGMENTE.md`:657 | `set_reg(f, SYSNO_RESULT, IpcResult::ErrQuiescing);` | `grep -n "IpcResult::" dokumente/FRAGMENTE.md` |
| caprock: `-> Result<` | **100** | `grep -rn --include=*.rs -e "-> Result<" /home/simon/Dokumente/caprock-messbasis \| wc -l` |

> **Die erste Zeile ist der Bedarfsbeleg, und sie ist älter als der Bau.** Die Freigabe eines
> Capability-Blattes schreibt im `else`-Zweig eines `narrow` genau die Form, die die Sprache
> nicht hatte. *Wer sie übernommen hat, hat den Bedarf vorweggenommen; die Zeile fiel mit
> `M119`.* Sie war die Vorlage für `beispiele/48`.

**Gemessen wurde auch die Umwidmungskosten:** zwei Pfadglieder mit Identifier-Basis und ohne
`(` kommen im Korpus **null Mal** vor (`u64::max` nimmt den Zweig der Integerwörter,
`beispiel::eintritt::syscall_verteiler` steht in einer `dispatch`-Klausel). Die Produktion
`reasonval` kostet damit keine bestehende Stelle.
`grep -rn "::" beispiele/*.gab | grep -v -e "-- " -e module -e use`

### 1.4 Was gebaut wurde

**Keine neue Anweisung und kein neues Wort.** `return R::F;` **ist** die Fehlerrückgabe, weil
ein Grundwert nie den Erfolgstyp haben kann — das ist die Bedingung, unter der diese Ersparnis
erlaubt ist. Wo sie nicht gälte, wäre es ein stiller Verleser, und die kosten in diesem Ordner
mehr als eine fehlende Form.

| Datei | was |
|---|---|
| `dokumente/SYNTAX.md` | `primary … \| reasonval`; `reasonval = ident "::" ident ;` |
| `dokumente/SPRACHE.md` | §8.1.1 — der Erzeuger, die drei Türen, `N034` neben `N028`/`N029` |
| `gabbro-syntax/src/ast.rs` | `ExprArt::Grund { grund, fall }` |
| `gabbro-syntax/src/parse.rs` | zwei Glieder ohne `(` → `Grund` |
| `gabbro-check/src/typen.rs` | `Typ::Grund(String)`, `text()` → `reason R` |
| `gabbro-check/src/umgebung.rs` | `gruende`, `erschoepfende_gruende`, `fehlerkanaele` + zwei Nachschlagehilfen |
| `gabbro-check/src/m1.rs` | `M120`–`M125`, der Typ von `e`, `grundstellung` |
| `gabbro-check/src/namen.rs` | `N034` im `fehlerkanal`-Pass |
| `gabbro-check/src/emit.rs` | `R_F`, `*_grund = …; return false;`, `match_grund`, bedingtes `(void)` |
| `gabbro-check/src/lib.rs`, `kosten.rs` | die erschöpfenden `match`es über `ExprArt` |

**Die sieben Absagen** (Kennungen 191 → 198, `python3 pruefe-kennungen.py`):

| Code | Regel |
|---|---|
| `M120` | `R::F` — `R` ist kein deklarierter `reason` |
| `M121` | `R::F` — `F` ist kein Fall von `R` |
| `M122` | ein Grund wird zurückgegeben, und die Signatur erklärt keinen oder einen anderen |
| `M123` | ein `match` über einem Grund lässt einen Fall aus oder erfindet einen |
| `M124` | die **Stellung** eines Grundwerts, und die **Typen** an einem Vergleich |
| `M125` | ein `match` über einem Grund, der `exhaustive` nicht sagt |
| `N034` | ein eigener Rumpf erklärt `or R` und kann nie scheitern |

### 1.5 Zwei Löcher, die der Bau selbst aufgemacht hat

*Beide gefunden durch Messung nach dem Bau, nicht durch Nachdenken davor.* Sie sind der
lehrreichste Teil dieses Laufs.

**(a) Der `match` über einem Grund war einen Lauf lang offen.** Sobald `e` einen Typ hatte,
wurde die Frage nach den Zweigen fällig — vorher war sie es nie, weil `e` nicht existierte:

```text
match e { GibtsGarNicht => { return 1; } }   ->  4 Items, 0 Fehler, 0 Hinweise
```

Geschlossen mit `M123`, und die Begründung ist wörtlich die von `D005` am `tagged type`.

**(b) Ein Grundwert ging an SIEBEN Stellungen still durch.**

```gabbro
let g = HolFehler::Leer;          nimm(HolFehler::Leer);
t.slots[HolFehler::Leer].w        z = HolFehler::Leer;
if HolFehler::Leer { … }          !HolFehler::Leer
ensures result == HolFehler::Leer
```
> `p8-alle-stellungen.gab: 13 Items, 0 Fehler, 0 Hinweise`

**Die Ursache ist allgemein und sie steht in einer Zahl: 53.** So viele `match`es über
`ExprArt` in diesem Prüfer tragen einen `_`-Zweig. *Eine neue Wertart öffnet jede Stellung, in
der eine Regel `_ =>` schreibt* — und der Übersetzer erzwang nur **fünf** erschöpfende Stellen.

```bash
# die Zählung, die das gesagt hat
python3 - <<'EOF'   # (im Bericht gekürzt; sucht `match …art {` mit ExprArt und `_ =>`)
EOF
```

Deshalb ist `M124` **strukturell** und nicht typweise gebaut: *ein Grund darf an genau drei
Stellen stehen*, und alles andere fällt, ohne dass irgendeine der 53 davon wissen muss.

| erlaubt | gehalten von |
|---|---|
| `return R::F;` | `M122` hält den Kanal dazu |
| `match e { … }` | `M123`/`M125` halten sie geschlossen |
| `a == b` / `a != b` | `M124` (Typhälfte) hält die Deklaration |

**Und die Regel hat zwei Hälften, weil ein Grund in zwei Gestalten dasteht:** geschrieben als
`R::F`, und **gebunden als das `e` eines `let … else`**. Die erste Fassung sah nur die
geschriebene — `e + 1` ging weiter durch. *Die Mutation, die das gemessen hat, steht als
`gebundener-grund-wird-nicht-erkannt` im Katalog.*

### 1.5a Ein drittes Loch, gefunden von einer ZAHL

`pruefe-zahlen.py` sah nach dem Bau *„Blicke ohne Modulkandidaten — jeder ein mögliches
`M103`-Loch"* von 32 auf 33 steigen. Nachgesehen: `Umgebung::fehlerkanaele` heftete den
`reason`-Namen mit `qualifiziere(pfad, …)` an das Modul der **Funktion**.

**Steht der `reason` eine Modulebene weiter außen, trägt diesen Schlüssel nichts** — `e` bekäme
keinen Typ, und `match e { … }` fiele mit `M119` an einem Programm, das in Ordnung ist.

*Der ganze Beispielkorpus deklariert `reason` und Rumpf im selben Modul, und `beispiele/48` tut
es auch.* **Keine Probe hätte es je gezeigt.** Aufgelöst wird jetzt zweimal — die Funktion vom
Rufort aus, ihr `reason` von ihrem Modul aus — und zwei Tests in `tests/paesse.rs` halten beide
Richtungen fest: *der äußere Grund löst auf*, und *er hält auch zu* (ein Fall zu wenig fällt mit
`M123`). **W10: nicht abgewiesen ist nicht bestätigt** — die erste Probe allein sähe genauso
aus, wenn `e` gar keinen Typ bekäme.

### 1.6 Ein totes Wort ist lebendig geworden — und der Wächter hat es gemeldet

`pruefe-klauseln.py` führte **`erschoepfend`** und **`fehlername`** als **TOT**. Nach dem Bau
sagte er von selbst:

```text
== KLAUSELN: DIE TABELLE IST VERALTET ==
   Diese Zeilen sind GESTIEGEN -- ein Pass liest sie jetzt. Eintrag loeschen.
   fehlername
```

**Das ist die Richtung, für die er gebaut wurde**, und er hat sie zuerst gesagt. `erschoepfend`
kam beim Nachlesen dazu: `SPRACHE.md`:531 sagt seit langem, was `exhaustive` heißt — *„der
erzeugte `switch` hat KEIN `default`, und ein neuer Wert bricht die Übersetzung"* — und **keine
Zeile tat es.** `M125` und der `default`-lose `switch` in `match_grund` sind zusammen sein
erster Leser. *Die Bedeutung ist nachgezogen, nicht erfunden* (R9).

### 1.7 Das Programm, das es gebraucht hat

`beispiele/48-grund-mit-erzeuger.gab` — nach der Vorlage aus `FRAGMENTE.md`:269.

```text
beispiele/48-grund-mit-erzeuger.gab: 12 Items, 0 Fehler, 0 Hinweise
  M1 saw 39 expressions, 0 of them without a type (100 % coverage)
cc -std=c11 -O0 -Wall -Wextra -Werror   ok
cc -std=c11 -O2 -Wall -Wextra -Werror   ok
cc -std=c11 -O1 -fsanitize=undefined    ok
```

Es benutzt alle drei Türen: `return Buchfehler::Unbelegt;` und `return Buchfehler::Buchfuehrung;`
im `else`-Zweig eines `narrow`, `match e { … }` beim Rufer, und `if e == Buchfehler::Unbelegt`.

Die Absenkung, zum Vergleich mit der Zeile, die vorher dastand:

```c
bool platz_freigeben(Griffe *restrict g, uint32_t s, uint32_t *_wert, Buchfehler *_grund) {
    if (!(g->slots[s].belegt)) { *_grund = Buchfehler_Unbelegt; return false; }
    if (!(g->slots[s].zaehler >= 1 && …)) { *_grund = Buchfehler_Buchfuehrung; return false; }
    …
    *_wert = g->slots[s].zaehler; return true;
}
```

### 1.8 Die Gegenproben

**Acht Giftproben**, `beispiele/gift/232`–`239`, jede fällt mit genau ihrem Code
(`cargo test --test beispiele`):

| 232 `M120` | 233 `M121` | 234 `M122` | 235 `M123` |
|---|---|---|---|
| **236 `M124`** (Stellung) | **237 `N034`** | **238 `M125`** | **239 `M124`** (Typen) |

**Zehn Mutationen**, Katalog 240 → 250, alle gefangen:

```text
ssh ki-pc-fisch-101 'cd gabbro-f && python3 fahre-stufe7.py'
== 10 von 10 Stufe-7-Mutationen gefangen ==

python3 mutiere-pruefer.py --anker
== 250 von 250 Ankern greifen ==   ALL PASS
```

> **`M124` hat zwei Mutationen, und das ist ein Befund über die Messung selbst.** Die erste
> Fassung zielte nur auf die Typhälfte — und Gift 236 fiel trotzdem, weil die Stellungshälfte
> es fing. *Eine einzelne Mutation hätte die andere Hälfte gedeckt aussehen lassen.*

---

<!-- widerruf:aus -->
## Posten 2 — `fnptr`: NICHT gebaut, und die Zahl steht daneben
<!-- widerruf:an -->

> **Überholt am 2026-08-21, dem Tag dieses Berichts** ([`FNPTR.md`](FNPTR.md)). Die Messung
> in 2.1 gilt und rechnet nach; die drei Löcher in 2.2 sind alle drei zu. *Was diesen Posten
> gestoppt hat, war nicht der Bedarf, sondern die Reihenfolge* — und die liess sich in einem
> Lauf einhalten. Der Abschnitt bleibt im Wortlaut, weil eine Messung, die man nachträglich
> umschreibt, keine Messung mehr ist.

### 2.1 Die Messung

| Frage | Zahl | Befehl |
|---|---|---|
| `fnptr`-Stellen im Korpus | **0** | `grep -rn "fnptr" beispiele/ \| wc -l` |
| steht der TYP in der Grammatik? | **ja** | `SYNTAX.md`:331, geparst in `parse.rs:945` |
| caprock: `fn(…)` als Feld-/Parametertyp | **11 Zeilen** | `grep -rn --include=*.rs -e ": fn(" -e "Option<fn(" /home/simon/Dokumente/caprock-messbasis \| wc -l` |
| caprock: Stellen, die einen **herstellen** | **4** | `grep -rn --include=*.rs -E "(bereit\|senden\|fence\|load\|delete_cap):\s*[A-Za-z_][A-Za-z0-9_:]*\s*[,}]"` + zwei `fence`-Argumente |
| davon auf `arch/x86_64`, der Messbasis | **1** | `x86_64/console.rs:91` — die `aarch64`-Zwillingszeile ist versiegelt |
| caprock: Aufrufe **durch** einen | **4** | `grep -rn --include=*.rs -E "\(\s*(self\|t)\.[a-z_]+\s*\)\s*\("` |
| caprock: `dyn SchedOps` / `dyn Park` | 10 / 9, **je EINE Implementierung** | schon gebucht, `MESSUNGEN.md` A2 |
| caprock: Abschlüsse `dyn FnMut`/`Fn` | 47 Zeilen | *keine `fnptr`-Frage* — unentschieden, A2 |

**Der Bedarf ist also nicht null**, und er ist genau der, den die Stufe nennt: eine
Treiber-`ops`-Struktur (`konsole::Treiber { bereit, senden }`). Er ist aber **klein und auf der
Messbasis einstellig.**

### 2.2 Warum trotzdem nicht gebaut — die Handprobe entscheidet

```gabbro
type Treiber = { bereit : fn() -> bool, senden : fn(u8), };
impl fn bauen() -> Treiber … { return Treiber(bereit: uart_bereit, senden: uart_senden); }
impl fn schicken(t : Treiber, b : u8) … { t.senden(b); }
```
```text
gabbro pruefe:
  Fehler: [P017] …:19:13: Zuweisung oder Aufruf erwartet, `(` gefunden
  Fehler: [M119] …:14:28: `uart_bereit` is declared nowhere
gabbro emit:
  Fehler: [C001] …:5:5: no lowering: field type
```

**Drei Löcher, nicht eines.** Der Typ steht in der Grammatik, und **alle drei anderen Hälften
fehlen**:

| | fehlt | Kennung |
|---|---|---|
| 1 | der **Erzeuger** — kein `&f`, ein Funktionsname ist kein Wert | `M119` |
| 2 | der **Aufruf durch einen Ort** — «B8», `call = path "(" …` | `P017` |
| 3 | die **Absenkung** — der Erzeuger kann ein `fnptr`-Feld gar nicht schreiben | `C001` |

### 2.3 Der Befund: die Reihenfolge im TODO ist richtig und **unvollständig**

> *„`fnptr` — erst der Erzeuger, dann der Vertrag."*

Das stimmt, und es verschweigt den Schritt dazwischen. **Ein `&f` ohne den Aufruf ist ein Wert,
den niemand benutzen kann** — genau der Erzeuger ohne Verbraucher, dessen Spiegelbild
(Vertrag ohne Einlöser) K100s zweites Tor abwehrt.

Und der Aufruf zwingt den Vertrag **sofort**, nicht danach: `PLAN.md`:1012 sagt, dass an jedem
Aufruf durch einen Funktionszeiger die Rahmenbedingung steht, dass die `effects`-Liste ihn
deckt. Ohne Vertrag am Typ macht ein solcher Aufruf **jede `effects`- und `costs`-Zusage des
Rufers zur unteren Schranke** — er nimmt `E008` zurück, den Posten, der `effects` am 2026-08-15
erst kompositional gemacht hat.

**Daraus folgt mechanisch, dass das Programm, das Regel A verlangt, heute nicht existieren
kann.** Eine saubere `.gab`-Datei, die `&f` benutzt, dadurch ruft und durch `gabbro pruefe`
geht, müsste entweder

* den Aufruf haben — dann fällt sie an `E009`/`K003`, denn der Gerufene ist unbekannt; oder
* den Aufruf **nicht** haben — dann benutzt sie das Konstrukt nicht, und Regel A ist verletzt.

> **Das ist keine Bedarfsnull, sondern eine Konstruierbarkeitsnull**, und sie ist die härtere
> von beiden: *sie sagt nicht „niemand braucht es", sondern „so, wie die Stufe es aufteilt,
> ist keiner der drei Teile für sich fertigstellbar."*

Die richtige Reihenfolge ist damit **vier** Schritte, und der zweite und dritte sind ein Paar:

```text
1. der TYP                    -- steht (SYNTAX.md:331)
2. der ERZEUGER  `&f`         --+
3. der AUFRUF durch einen Ort --+  zusammen, sonst ist 2 unbenutzbar
4. der VERTRAG am Typ         --   zwingend mit 3, sonst faellt E008
```

### 2.4 Und eine Buchung, die dem widerspricht

`MESSUNGEN.md`:1642 sagt seit dem 2026-08-16:

> **`fnptr` needs no contract.** The item from «B9» falls away, and the prohibition list grows
> instead of the grammar.

`TODO.md` führt «B9» weiter als offenen Posten, `PFLICHTEN.md`:613-624 verlangt den Vertrag.
**Beide Buchungen stehen nebeneinander und meinen Verschiedenes.** Der Widerspruch ist
auflösbar und die Auflösung ist eine Zahl: A2 sprach über **Trait-Objekte** (10 `dyn SchedOps`,
je eine Implementierung → statische Auflösung, das Objekt verschwindet). Die **11 echten
`fn(…)`-Typen** in caprock sind davon nicht berührt — sie sind keine Trait-Objekte, sondern
C-Funktionszeiger, und für sie gilt A2s Argument nicht.

*Die Buchung schönt nicht, sie veraltet: A2 hat die eine Hälfte gemessen und die andere nicht
genannt.*

---

## Was NICHT gelungen ist

1. **Ein Grundwert in einem PRÄDIKAT hat keinen Leser.** `ensures result == HolFehler::Leer`
   gibt **0 Fehler** — die Stellungsregel läuft über Anweisungen, `Pred` ist ein eigener Baum.
   Der Vertrag ist Unsinn (`result` ist der Erfolgstyp) und niemand sagt es.
   `ssh ki-pc-fisch-101 'cd gabbro-f && ./target/debug/gabbro pruefe ~/proben/p8-alle-stellungen.gab'`
   — sechs der sieben Stellungen fallen, diese eine nicht.
2. **Wie ein Grund die Syscall-ABI überquert, ist nicht entschieden.** `FRAGMENTE.md`:657
   schreibt `set_reg(f, SYSNO_RESULT, IpcResult::ErrQuiescing);` — ein Grund als Argument, und
   `M124` sagt es ab. *Die Absage ist richtig und der Bedarf ist echt:* dort reist die Zahl,
   und das ist die ABI und nicht der Fehlerkanal. Gebucht als `BENANNT`-Eintrag, dieselbe Lage
   wie `S006`.
3. **`let … else` über einem PLACE trägt weiterhin keinen Grund** («B14b»): dort ist der
   Fehlschlag `None`, und `None` sagt nicht woran. Unverändert, der Erzeuger weigert sich mit
   seiner eigenen Begründung.
4. **Der volle Mutationslauf über alle 250 ist nicht gelaufen** — er baut je Mutation neu.
   Gelaufen sind `--anker` über alle 250 (ALL PASS) und die zehn neuen einzeln
   (`fahre-stufe7.py`, 10 von 10). *Die 240 alten sind unberührt geblieben; keine ihrer
   Ankerstellen ist durch diesen Bau verschwunden — eine wurde MEHRDEUTIG und ist repariert,
   indem der neue Code eine andere Zeilenform bekam.*
5. **`fnptr`** — siehe oben. Nicht gebaut, mit Zahl und Grund.

## Drei Buchungen, die der Lauf als veraltet gemessen hat

| Buchung | behauptet | gemessen 2026-08-21 | Befehl |
|---|---|---|---|
| Diagnosekennungen | 194 | **191** (jetzt 198) | `python3 pruefe-kennungen.py` bei `HEAD` |
| Mutationen | 254 | **240** (jetzt 250) | `python3 mutiere-pruefer.py --anker` |
| Giftproben | „232 bis 245 sind frei" | **222 vorhanden**, höchste Nummer 226 | `ls beispiele/gift/ \| wc -l` |

*Alle drei in derselben Richtung: die Buchführung nennt mehr, als dasteht.*
