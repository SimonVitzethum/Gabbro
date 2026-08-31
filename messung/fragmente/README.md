# Der vervollständigte Fragmentkorpus

**Dies sind dieselben zehn Fragmente wie in [`dokumente/FRAGMENTE.md`](../../dokumente/FRAGMENTE.md) — byteidentisch, plus genau die Zeilen, die sie zu Programmen machen.**

## Warum es diesen Ordner gibt

K100s Absenkungspflicht lautet: *„das erzeugte C rechnet, was das Fragment sagt"* — **an der Ausführung gemessen.** Sieben der zehn erfüllten sie nicht, und am 2026-08-20 wurde nachgezählt, woran das liegt:

```
41 Stellen nennen 20 Namen, die niemand deklariert
   (MAX_POLL · EP_BADGE · SYSNO_RESULT · Fehler · NTFN · IpcResult · …)
 9 `let … else` rufen Rümpfe, die diese Einheit nicht kennt
 6 Bitlagen sind unbenannt
 1 Tabelle nennt kein `tree`, 1 Gerufener kein `or <reason>`
```

**Jedes der sieben trug mindestens einen korpusseitigen Riegel.** F4 — das reinste — brauchte genau eine Zeile: `MAX_POLL`. Ohne sie nennt die `bounded`-Klausel nichts.

Damit fiel die Absenkungsspalte **um keinen Punkt**, solange `FRAGMENTE.md` unangetastet bleibt — und die Datei trägt ihren Einfriersatz: *„ein Bericht vom 2026-08-14, und er bleibt unangetastet."*

> **Ein Ausschnitt lässt sich nicht ausführen.** Die sieben zu schließen hieße, eine eingefrorene Datei zu ändern — das ist nicht das Schließen einer Pflicht, sondern das Verschieben des Maßstabs.

## Die Regel dieses Ordners

**Je Datei steht im Kopf, was ergänzt wurde — und was nicht.** Es ist derselbe Zug wie bei «K2»: *nachgebildet, nicht übersetzt, und ausdrücklich gesagt.* Wer die Zahl liest, sieht daneben, welcher Teil gemessen und welcher geschrieben ist.

Ergänzt werden **nur** Deklarationen, die der Ausschnitt ruft und nicht nennt. Nichts wird umgeschrieben, nichts weggelassen, keine Absage wegdefiniert. **Wo ein Fehler nach der Vervollständigung stehen bleibt, gehört er Gabbro** — und genau das ist der Ertrag.

## Der Stand

```
$ ./instrumente/zaehle-fragmente.py
6 von 10 prüfen sauber        (über den Ausschnitten: 5; am 2026-08-20 kurz 7;
                               ~~7~~ **6 seit dem 2026-08-31: `N041` nimmt `F05` heraus**,
                               und die 7 war ein falsches Grün — die Datei prüfte sauber,
                               emittierte 199 Zeilen C und wurde von `cc` zurückgewiesen)
6 von 10 senken ab            (über den Ausschnitten: 3)
6 von 10 sind DURCHGESTOCHEN  — F02, F04, F06, F07, F08, F10   (F6 am 2026-08-31)
```

**Die vierte Zahl kam am 2026-08-25 dazu, und sie ist die, auf der K100s erstes Tor steht.**
Der Absatz unten sagte seit jeher *„eine, die absenkt, ist nicht ausgeführt"* — und zählte die
Ausgeführten dann nicht. Die Absenkungspflicht lautet aber wörtlich *„das erzeugte C rechnet,
was das Fragment sagt"*, **an der Ausführung gemessen**; wer bei `senkt ab` aufhört, hört
genau vor der Aussage auf.

> **F02 ist das erste der sieben, das gefallen ist** — ohne eine Zeile Konstrukt, ohne eine
> neue Schablone. Es fehlten fünf `reserved`-Felder; danach emittiert es 157 Zeilen C,
> übersetzt unter `-Werror` bei `-O0` und `-O2`, läuft unter UBSan und liefert
> `4096 153 7 3 256 1 6 2 1 1 0 9`. **Die Vervollständigung wird dabei selbst geprüft:**
> `pruefe-emission.sh` schneidet den eingefrorenen Block und weist die Datei ab, wenn ihr
> auch nur eine Zeile des Ausschnitts fehlt. *Ergänzen ist erlaubt, weglassen nicht* — sonst
> wäre die Vervollständigung ein Verschieben des Maßstabs.

| | ergänzt | was danach noch fällt |
|---|---|---|
| **F1** | `reason Fehler`, `or Fehler` an `delete_leaf` | **`N029`** — `revoke` ruft `delete_leaf` und fängt das Scheitern nicht. *(2026-08-31, P-d: die Form GIBT es und ist gemessen — mit `let … else` + `or Fehler` am Rufer bleibt genau **eine** Absage übrig, `K001` mit **+80 256 ops** = einer op je Durchgang. Es sind damit **ZWEI** eingefrorene Zeilen, :337 und die `costs`-Zeile :328 — also ein Umschreiben. Und der Grund liegt tiefer: im Original ist `delete_leaf` gar nicht fehlbar; fehlbar macht sie «B29» bei :268. Beide Hälften stehen im selben Bericht. Siehe [`../DREI-FRAGMENTABSAGEN.md`](../DREI-FRAGMENTABSAGEN.md).)* |
| **F2** | fünf `reserved`-Felder | — *prüft sauber, senkt ab, übersetzt — und ist seit 2026-08-25 **durchgestochen***|
| **F3** | vier Konstanten, `or EpVoll` an `enqueue`, `lock SCHEDS` *(2026-08-25)* | 3× `M124`, `M101` Optionssonderwert, `H011` `locks SCHEDS` nie genommen, **5× `N035`** — der Vertrag am `fn(…)`-Typ, seit 2026-08-21 Pflicht. *(2026-08-31, P-c: die drei `M124` sind eine **richtige Absage**. Die Vorlage in `caprock-messbasis` führt an dieser Stelle `pub const ERR_… : u64`, keinen Aufzählungstyp — **null Projektionen im ganzen Baum** — und die zwei Zahlenräume weichen heute schon ab: `ErrBadCap = 2` gegen `ERR_BADCAP = 1`. Was fehlt, sind vier `const`-Zeilen, und die stünden in Ausschnittzeilen.)* |
| **F4** | `MAX_POLL`, `assume`, `on_exceeded`-Ziel | — *prüft sauber*; Absenkung an der `dma`-Barriere. **Nachgeprüft 2026-08-25 und GEBUCHT, nicht gebaut:** die drei `C001` sind `device Virtq(…) at dma` (:79) und zwei `let` in `publish` — und die beiden `let` stehen HINTER der ersten Absage, das Gerät senkt gar nicht erst ab. *Die `at dma`-Absage ist die Axiomschicht selbst* (welche Barriere ein DMA-Zugriff verlangt, ist eine Aussage über das Speichermodell; M3 baut sie ausdrücklich nicht). **Sie zu verengen hieße raten**, und ein Erzeuger, der rät, hebt jeden Pass vor sich auf |
| **F5** | neun Konstanten, fünf `extern fn` mit Kanal, ein `assume` | — *prüft sauber (nachgemessen 2026-08-31: 26 Items, 0 Fehler).* ~~3× `M124` — ein Grundwert steht als ARGUMENT~~ **geschlossen von der VIERTEN TÜR** (2026-08-25): ein Argument darf ein Grund sein, wenn der Parameter genau diesen `reason` deklariert. *Diese Zeile stand sechs Tage länger, als sie wahr war.* **2026-08-31 ausgemessen: F5 wäre EINE Ergänzung von der Absenkung entfernt** — fünf `extern fn`, alle vom Dienstrumpf gerufen und nirgends genannt, geben 31 Items, 0 Fehler, 0 Hinweise und 199 Zeilen C. *Sie steht nicht da:* `cc -Werror` fällt an drei Stellen, und die erste ist `exit`, ein Name, den C vergeben hat und den der EINGEFRORENE Ausschnitt ruft (`ABSAGEFORMEN.md` U10, `TODO.md`). **BERICHTIGT am 2026-08-31: F5 prüft NICHT mehr sauber, und das ist die erste ehrliche Ablesung.** `N041` weist `extern fn exit()` ab — 558 Namen, die C vergeben hat, in drei gemessenen Klassen ([`../C-NAMEN.md`](../C-NAMEN.md)). *Die Datei prüfte sauber, emittierte 199 Zeilen C und wurde vom fremden Übersetzer zurückgewiesen; jetzt fällt sie an der Zeile, die es verursacht.* **Und sie ist unerreichbar, nicht bloß offen:** `exit` steht neunmal im eingefrorenen Block, die Umbenennung wäre neunmal ein Weglassen, und C führt `void exit(int)` gegen ein `exit()` ohne Argument ([`../F05-UNERREICHBAR.md`](../F05-UNERREICHBAR.md)) |
| **F6** | zwei Konstanten, `IrqMarke`+`static irq`, zwei Kanäle, ein Tor | — *prüft sauber*; ~~Absenkung an «B12» `elems of`~~ *(«B12» ist seit 2026-08-20 entschieden)*. **2026-08-25: 4 × `C001` auf 2.** Was bleibt: drei Namen im `check`-Rumpf, die niemand deklariert — **korpusseitig**, und kein Pass sagt es (Befund 7) — und `lenof` außerhalb eines `format`, dessen einziger Korpusort genau dahinter liegt (Regel A). **2026-08-31 DURCHGESTOCHEN** — `lauf "fragment6"`, achtzehn Zahlen, `-O0`/`-O2`/UBSan; `H` fällt von 5 auf 4 |
| **F7 F8 F10** | nichts | — *waren schon Programme* |
| **F9** | zwei `reserved`-Felder | **`K001`** — die Zusage `costs <= 4096 ops` ist seit Stufe 3 nachrechenbar **falsch** (137 438 953 472). Siehe Kopf der Datei. *(2026-08-31, P-a: die Zahl ist nachgerechnet und **scharf**, `Rumpf × Knotenlänge^Ebenen`; und `F9` ist nicht vom PRÜFER blockiert, sondern **dreimal vom Erzeuger** — keine der drei `C001` hängt an `K001`. [`../K001-DOMAENENSCHRANKE.md`](../K001-DOMAENENSCHRANKE.md).)* |

## Der Ertrag: drei Befunde, die der eingefrorene Korpus nicht zeigen konnte

**1. `A::B` parst und wird nie aufgelöst.** `path = ident { "::" ident }` steht in der Grammatik; der Namenspass liest die **erste Silbe** und schlägt sie als Wert nach. `IpcResult::Ok` fällt als `M119`, gleichgültig ob `IpcResult` ein `module`, ein `reason` oder ein Variantentyp ist — alle drei geprüft.

**2. ~~Ein `reason`-Wert hat keinen Erzeuger.~~ — ÜBERHOLT am 2026-08-21, nachgemessen am 2026-08-25.** Seit Stufe 7 steht `return R::F;` als eine von drei erlaubten Stellungen fest; der Erzeuger ist gebaut. Was an den sechs Stellen in F1/F3/F5 heute fällt, ist **`M124`** — die STELLUNG, nicht die Produktion: ein Grundwert darf nur als `return`, als Gegenstand eines `match` und in `==`/`!=` stehen, und alle sechs sind Argumente. *Der offene Rest ist damit kleiner und genauer benannt: einem `reason` fehlt die ZAHLPROJEKTION, obwohl er seine Zahlen deklariert.* Der ursprüngliche Wortlaut bleibt daneben stehen — er ist der Befund vom 2026-08-20:

> **2. (2026-08-20) Ein `reason`-Wert hat keinen Erzeuger.** `primary` (`SYNTAX.md`:405) kennt keine Produktion dafür. **Jede `-> T or R`-Signatur im Korpus steht an einem `extern fn`** — an einem Rumpf, den Gabbro nie sieht. *Keine einzige Gabbro-Funktion erzeugt je einen Grund.*

> **Dieselbe Gestalt wie «B9» bei `fnptr`:** eine Form, die man deklarieren und nicht herstellen kann. Erst der Erzeuger, dann der Vertrag.

**6. Nachgetragen am 2026-08-25: «B9» ist ebenfalls überholt — ~~und es steht noch als offene Lücke in `PFLICHTEN.md`~~ *(am selben Tag berichtigt; die Zeile trägt jetzt `N035`/`N036`/`N037`, und `H` fiel von 11 auf 10)*.**

<!-- widerruf:aus -->
Der Kommentar in F3 sagt, `fnptr` trage „kein `requires`, kein `ensures`, kein `effects`“. *Der Satz steht hier ZITIERT — deshalb der `widerruf:aus`-Block: `WB3` in [`../../instrumente/pruefe-widerruf.py`](../../instrumente/pruefe-widerruf.py) sucht seit dem 2026-08-25 genau diesen Wortlaut.*
<!-- widerruf:an -->

Seit dem 2026-08-21 trägt er `effects` **und** `costs`, und zwar als PFLICHT: `N035` weist einen `fn(…)`-Typ ohne beides ab, `N036` sagt, welche Wirkungswörter durch einen indirekten Ruf tragen, und `beispiele/49-dispatch-tabelle.gab` schreibt alle vier Hälften in einem Programm auf (`messung/FNPTR.md` führt die Messung). `requires`/`ensures` sind **mit einer gemessenen Begründung abgewiesen** (`N037`) — nicht vergessen. Nachgerechnet am 2026-08-25:

```
$ printf 'type T = { f : fn(u8), };' > /tmp/b9.gab && gabbro pruefe /tmp/b9.gab
Fehler: [N035] /tmp/b9.gab:1:16: `fn(#1)` declares no `effects` and no `costs`
```

> **Und es ist eine BERICHTIGUNG, kein Dekrement per Buchung.** Die Arbeit ist vom 2026-08-21; was heute fiel, ist ein Eintrag, der seit vier Tagen falsch war. *Eine Zahl per Umformulierung zu senken wäre Umtopfen — einen falschen Eintrag zu korrigieren ist das Gegenteil davon.*

> *Der Ertrag ist hier zweischneidig:* dieselbe Regel macht **fünf neue Fehler** in F3, weil die fünf `fn(…)`-Zeilen des Ausschnitts vom 2026-08-14 einen Vertrag tragen müssten, den es damals nicht gab. **Ein eingefrorener Korpus kann unter einer neuen Absage veralten** — und das ist keine Regression, sondern der Preis dafür, dass der Maßstab nicht mitwandert.

**5. Nachgetragen am 2026-08-20 (Stufe 3): die entschiedene Lesart hat ein Fragment
GEKOSTET, und das ist der Ertrag.** `mappings of` heißt seither die **Blattmenge**, und F9s
Zeile `costs <= 4096 ops` — begründet im Ausschnitt mit *„`levels` mal `node`-Länge"* — ist
damit nachrechenbar falsch: der Rumpf kostet **137 438 953 472**.

> **Der Fehler stand seit dem Schnitt in der Datei und war unsichtbar, solange der Pass
> dieselbe falsche Lesart trug wie der Mensch, der die Zeile schrieb.** Zwei Register über
> derselben Sache, und beide falsch (W7). *Eine Zahl fällt von 7 auf 6 — und was fällt, ist
> eine Zusage, die niemand hält.*

**4. Nachgetragen am 2026-08-20 (Stufe 2): «B11» ist veraltet, und die Korrektur steht im
Kopf von F5.** `forever` hat sehr wohl einen Ausgang — `leave <marke>` steht in der Grammatik
(`SYNTAX.md`:658), prüft mit 0 Fehlern und senkt zu `goto marke_ende;` ab. Was fehlt, ist ein
Ausgang, der einen **Grund** trägt; `leaves` heißt in Gabbro etwas anderes (die linearen Werte,
die den Bereich verlassen). *«B11» schrumpft von „die Dienstschleife ist nicht schreibbar" auf
„ihr Austritt ist unbenannt".*

> **Der Wortlaut des Ausschnitts bleibt trotzdem stehen**, und die Korrektur steht daneben mit
> Datum. Ein Ausschnitt vom 2026-08-14 ist ein Bericht von diesem Tag — ihn zu überschreiben
> hieße, den Maßstab zu verschieben statt die Pflicht zu schließen.

**3. ~~Und eine Zeile, die ich selbst ergänzt habe, senkt nicht ab:~~ — GESCHLOSSEN am 2026-08-25.** `static irq : IrqMarke = IrqMarke(…)` in F6 — ein `static` eines Verbunds mit gewöhnlichem Anfangswert. *Das stand hier, statt die Zeile wegzulassen; heute senkt sie ab.*

> **Nachgemessen 2026-08-25: die Absage ist WEITER als ihr Grund.** `emit.rs`:1275-1281 weigert sich bei jedem `static`, dessen Typ ein `tagged` oder ein Verbund ist — der Text nennt aber den Fall „mit einer gewöhnlichen Zahl initialisiert“ (`= 0`) und begründet ihn damit, dass die Deklaration nicht sagt, **welche Variante die Null ist**. Hier sagt sie es: `IrqMarke(tiefe_max: 0, n: 1)` ist der markierte Ruf, also genau die Form, für die es die Schablone `S19 verbund.konstruktor` (**bewiesen**) gibt. *Eine Regel, deren Umfang und deren Begründung auseinanderfallen* — dieselbe Gestalt, die dieser Ordner schon viermal gefunden hat.

> **Verengt am selben Tag, und `L` bewegt sich dabei nicht.** Der markierte Ruf wird im
> `static` zu einem geklammerten Anfangswert mit benannten Bestimmern —
> `static IrqMarke irq = { .tiefe_max = 0, .n = 1 };` — und nicht zu dem
> zusammengesetzten Literal, das `emit::ruf` an einer Ausdrucksstelle schreibt: ein
> `(P){…}` hat statische Speicherdauer, ist aber **kein konstanter Ausdruck**, und
> C11 6.7.9p4 verlangt an dieser Stelle einen. *Zwei Stellungen, eine Schablone, zwei
> C-Formen* — die Unterscheidung steht in `verbundmarken` und nicht im Kopf.
>
> **Was NICHT dazugehört:** ein `tagged` behält seine Absage. Welche Variante die Null ist,
> sagt die Deklaration weiterhin nicht, und ein markierter Ruf kann keine nennen. *Der Grund
> ist unverändert richtig; nur sein Umfang war es nicht.*

**Und was danach an F6 noch fällt — drei Absagen wurden zwei, und die zweite ist Regel A:**

| Zeile | vorher | heute |
|---|---|---|
| `:54` `static mut irq` | `C001` | **senkt ab** (oben) |
| `:134` `art : Stackart` | `C001 parameter type` | **senkt ab** — ein `reason` IST ein C-Typ, `ItemArt::Reason` schreibt sein `typedef enum` seit jeher; `ctyp` kannte den Namen nur nicht |
| `:142` `let benutzt = s.len - frei` | `C001 let without a resolvable type` | **senkt ab** — `frei` kommt aus `unberuehrt(s) -> u64`, und der Typ stand in der Signatur |
| `:155` `let f = eichfeld()` | `C001` | **offen, korpusseitig**: `eichfeld`, `muster_schreiben` und `beruehre` deklariert niemand — siehe Befund 7 |
| `:160` `lenof(f.worte)` | `C001` | **offen, Regel A**: die Absage begründet sich mit `sizeof(T)` und der Schichtung; `lenof` eines deklarierten `[u64; N]` ist die deklarierte ZAHL und hat mit der Schichtung nichts zu tun. *Dieselbe Gestalt wie oben — aber der EINZIGE Korpusort dafür ist diese Zeile, und sie ist hinter dem Riegel darüber verschlossen. Kein Konstrukt ohne ein Programm, das es gebraucht hat.*

**7. Nachgetragen am 2026-08-25: ein `check … can_fail` wird von den Namens-, Wirkungs- und Kostenpässen NICHT betreten — und F6 prüft teilweise deshalb sauber.**

Gemessen an einer eigens gebauten Probe, beide Hälften:

```
$ gabbro pruefe <check-Block mit `let x = gibtesnicht();`>
… 4 Items, 0 Fehler, 0 Hinweise

$ gabbro pruefe <derselbe Ruf in einem `impl fn`>
Hinweis: [E009] … the call effects of `t` are undecidable: `gibtesnicht` is unknown to the graph
Fehler:  [K003] … `t` promises costs, but `gibtesnicht` is not declared here
```

> **Derselbe Ruf, zwei Antworten** — und die stillere steht in dem Block, dessen ganzer Zweck
> das Messen ist. In F6 sind es drei Namen (`eichfeld`, `muster_schreiben`, `beruehre`), und
> **der einzige Pass, der sie überhaupt bemerkt, ist der Erzeuger** (`C001`). *Die Zeile „6 von
> 10 prüfen sauber" trägt damit an dieser Stelle weniger, als sie liest.* Nicht gebaut: ein
> Pass, der den `can_fail`-Rumpf betritt, kostet seine Absagekennung, seinen Satz und seine
> Giftprobe — und er würde eine Zahl senken, die niemand darum gebeten hat.
