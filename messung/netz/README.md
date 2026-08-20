# Der Netzwerkstack — Stufe 4, und die Vorlage kommt von außen

**Gegenstand: Ethernet → ARP → IPv4 → UDP, ein Echodienst.** Geschrieben gegen **RFC 791**,
**RFC 826**, **RFC 768** und **RFC 1071** — und geprüft gegen **veröffentlichte Testvektoren**,
nicht gegen eigene Pakete.

```
$ ./instrumente/zaehle-netz.py
ok   ohne   Gabbro b861  Gegenrechnung b861   IPv4-Kopf, Feld genullt (RFC 791)
ok   mit    Gabbro 0000  Gegenrechnung 0000   derselbe Kopf MIT der Summe — muss 0 sein
ok   summe  Gabbro ddf2  Gegenrechnung ddf2   RFC 1071, Abschnitt 3: die Summe
3 von 3 Proben grün
```

## Warum die Vektoren von außen kommen müssen

**Regel A: kein neues Konstrukt ohne ein Programm, das es gebraucht hat.** *Regel B, und ohne
sie hält Regel A nicht:* ein Stack, den derselbe Autor gegen seine eigenen Testpakete schreibt,
misst wieder, **wie gut Gabbro zu Gabbro passt**.

Deshalb dreierlei Trennung:

| | |
|---|---|
| **die Vorlage** | die RFCs — niemand hat sie für Gabbro ausgesucht |
| **die Vektoren** | der klassische IPv4-Kopf und RFC 1071 §3; sie standen vorher da |
| **die Gegenrechnung** | eine **zweite Implementierung**, in Python, absichtlich anders geschrieben (dort faltet jeder Schritt, in Gabbro faltet erst das Ende zweimal) |

> *Ein Vergleich gegen die eigene Zahl ist kein Vergleich* (W7). Wären beide Seiten aus
> derselben Feder, ginge derselbe Denkfehler zweimal durch.

**Die dritte Probe trägt am meisten:** die Summe über einem Kopf, in dem die Prüfsumme schon
steht, muss **0** sein. Das ist die Eigenschaft, auf der der ganze Empfangsweg ruht — und die
einzige der drei, die eine falsche Faltung nicht überlebt.

## Der Ertrag: vier Löcher, die 45 Beispiele nicht gezeigt haben

**1. `!` hatte keine Absenkung — und das ganze saubere Korpus hat null Fundstellen.**

```
if !kopf_gueltig(k, w) { return 0; }     -- die gewöhnlichste Zeile eines Empfangswegs
gabbro pruefe → 0 Fehler · gabbro emit → C001 „expression form"
```

*Der Korpus ist **je Konstrukt** geschrieben — eine Datei für `table`, eine für `device`. Ein
`!` ist kein Konstrukt; es ist das, was man tut, wenn man ein Programm schreibt.* Gebaut, mit
Gegenprobe in [`beispiele/46-verneinung.gab`](../../beispiele/46-verneinung.gab). **Das unäre
Minus wurde ausdrücklich *nicht* mitgebaut** ([`gift/219`](../../beispiele/gift/219-unaeres-minus.gab)):
in C bleibt `-x` auf einem vorzeichenlosen Operanden vorzeichenlos, während M1
`i32 in -4294967295 .. 0` sagt — und kein Programm hat es gebraucht.

**2. Der Fehlerkanal `-> T or R` senkte FALSCH ab, und zwar auf zwei Arten zugleich.**

```
f(0)  →  der Ruf meldet MISSERFOLG, obwohl 0 ein gültiger Wert ist
f(7)  →  der Ruf meldet Erfolg, und *_wert bleibt UNBERÜHRT
```

Der Erzeuger schrieb `return <wert>;` in eine Funktion, deren C-Signatur `bool` zurückgibt —
und setzte obendrein `__attribute__((const))` darauf, worauf GCC den Speicherschritt wegließ.
**`gabbro pruefe`: 0 Fehler, 0 Hinweise. `gabbro emit`: Rücklaufwert 0. `cc` ohne `-Werror`:
übersetzt.**

> *Der ganze Korpus führt `or R` ausschließlich an `extern fn`* — also an Rümpfen, die dieser
> Erzeuger nie sieht. **Der erste eigene Rumpf mit Fehlerkanal war dieser Stack.**

**3. Ein `reason`-Wert hat keinen Erzeuger — und jetzt steht es im erzeugten C.** `*_grund`
bleibt ungeschrieben, weil `primary` keine Produktion dafür kennt. Ohne eine Zeile scheitert
die Übersetzung unter `-Werror=unused-parameter`; der Erzeuger schreibt sie **mit dem Befund
darin** statt sie zu verschweigen.

**4. „Lies dieselben Bytes als big-endian 16-Bit-Worte" ist nicht schreibbar.** Ein `format`
erklärt die Byteordnung *für seine Felder*; ein Feldtyp `[u16; 10]` in einem `format` wird
zweimal abgesagt — der Feldtyp selbst, und der Zugriff darauf (*„ein Leser liefert einen WERT,
und ein Wert hat keine Stelle in den Bytes"*, und das ist richtig).

> **Die Folge steht im Prüfstand:** das Zusammensetzen der Worte aus den Bytes passiert in C,
> nicht in Gabbro. *Die Prüfsumme rechnet Gabbro; die Sicht auf dieselben Bytes kommt von
> außen* — und damit liegt genau der Schritt außerhalb der Sprache, den eine Sprache für
> Netzcode können müsste.

### Und die Kante steht fest, BEVOR gebaut wird *(2026-08-21)*

**Die Bytesicht darf keine Aliasfrage öffnen. Eine Sicht schreibend, alle anderen lesend, und
der Wechsel ist ein EREIGNIS** — das ist die Gestalt von `state`/`transition`, auf Sichten
statt auf Zustände angewandt. Die Langfassung steht in
[`dokumente/SYNTAX.md`](../../dokumente/SYNTAX.md) §3; hier steht, warum dieser Ordner der
Anlass ist.

**Diese Datei enthält den Fall schon.** `echo_beantworten` nimmt zwei Zeiger:

```gabbro
impl fn echo_beantworten(e : ptr<normal, r>  EthKopf,
                         k : ptr<normal, rw> IpKopf,      -- schreibend
                         w : ptr<normal, r>  Kopfworte,   -- DIESELBEN Bytes, lesend
                         meine_ip : u32) -> u32 or Verwurf
    effects { reads e, reads w, writes k }
```

`w` ist `kopfworte_von(k)` — dieselben zwanzig Bytes, einmal als Felder und einmal als zehn
16-Bit-Worte. Der Rumpf prüft die Prüfsumme über `w`, und danach schreibt er `k.ttl = 64`.
**Von dieser Zeile an ist die über `w` gelesene Antwort veraltet**; RFC 791 verlangt die
Prüfsumme neu gerechnet, und `effects` behauptet, beide Zugriffe seien erklärt.

Gemessen am 2026-08-21 mit einer Handprobe derselben Gestalt: **0 Fehler, 0 Hinweise.**
Ebenso schweigt `gabbro pruefe` bei `zwei(r, r)` an zwei `ptr<normal, rw>`-Parametern. Nur der
syntaktisch gleiche Ort an zwei `own`-Parametern fällt (`R004`), und dessen eigene Notiz sagt
den Rest: *„two DIFFERENT names pointing at the same object stay indistinguishable (M3's open
alias question)."*

> **Die Rechtehälfte ist hier schon richtig** — `w` liest, `k` schreibt. **Was fehlt, ist die
> Ereignishälfte:** nichts entwertet `w` an der Schreibstelle, nichts verbietet die Benutzung
> danach. *Eine Bytesicht, die nur die Rechtehälfte übernimmt, erbt dieses Loch und gibt ihm
> ein Konstrukt, hinter dem es sich verstecken kann* — dann kauft der Posten seine
> Vollständigkeit mit einer stillen Alias-Ausnahme.

## Was hier NICHT steht

Kein TCP, keine Fragmentierung, keine variable Kopflänge (`ihl > 5` wird geprüft und nicht
behandelt), kein Zeitgeber, keine Neuübertragung. **Der Stack ist an drei Vektoren gemessen,
nicht an einem Netz** — was er kann, steht oben; was Gabbro dabei nicht konnte, daneben, und
das ist der eigentliche Ertrag.
