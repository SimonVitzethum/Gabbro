# Gabbro — die Syntax

**Die Quelle fuer die Oberflaeche.** [`SPRACHE.md`](SPRACHE.md) sagt, welche Mechanismen es gibt
und warum; [`BEWEIS.md`](BEWEIS.md), wozu sie da sind; hier steht, wie man sie hinschreibt.
Was hier nicht steht, ist nicht schreibbar.

Stand 2026-08-13, zweite Fassung. **Kein Uebersetzer liest das.**

> **Was jede Regel dieser Grammatik zu leisten hat:** eine **Klempnerei**-Pflicht durch Konstruktion
> erledigen — Index, Ueberlauf, Alias, Rahmen, Sperre, Rennen, Verfeinerung. Bleibt eine davon beim
> Programmierer haengen, ist das an dieser Stelle **eine Widerlegung**, kein Schoenheitsfehler.
> **Logik** schreibt der Programmierer ohnehin, in jeder Sprache.

---

## Stand — gemessen

| | erste Fassung | **diese** |
|---|---|---|
| definierte EBNF-Regeln | 40 | **104** |
| benutzt, aber nie definiert | 21 (17 tragend) | **0** |
| offene Entwurfsfragen | 7 | **9, benannt am Ende** |
| **Wächter** | — | `pruefe-syntax.sh` prüft **Geschlossenheit der Regeln UND Deckung der Terminale durch den Wortschatz**, je mit Sprechprobe |

> **DRITTE blinde Stelle, dieselbe Familie — und sie kostete drei Grammatikfehler, die die Sprache
> unbrauchbar machten.** Der Wächter prüfte, dass jede **benutzte** Regel definiert ist, **nicht ob
> jede definierte Regel erreichbar ist**. Gefunden von einem Fragmentprüfer, nachgerüstet als
> Erreichbarkeitslauf von `program` aus. Er fand sofort:
> **`atomicdecl`, `lockdecl`, `lockstmt` waren definiert und von `program` aus nie erreichbar** —
> also **kein Atomic, keine Sperre, kein kritischer Abschnitt** in der ganzen Sprache, während
> alle sechs Fragmente sie benutzen. Und eine **doppelte `item`-Produktion**, bei der die zweite
> die erste verdeckte.
>
> Dazu zwei Fehler, die kein Wächter sah, weil sie *innerhalb* gültiger Grammatik lagen:
> **`old(x)` hing unter `atompred` statt unter `primary`** — es konnte als Prädikat für sich
> stehen, aber in **keinem Ausdruck** vorkommen, also nie neben `==`. **Die Differenzaussage, die
> dieses Projekt als Kernlehre führt, war nicht schreibbar** — und das eigene `delete_leaf`-Beispiel
> gab eine an. Und **`fndecl` liess nur `block | ";"`**, womit **keine einzige `spec fn`
> schreibbar** war.

> **Der Wächter hatte eine zweite blinde Stelle, und sie war dieselbe wie die erste.** Er prüfte
> die **Nichtterminale** auf Geschlossenheit und behauptete daneben einen „geschlossenen
> Wortschatz", **ohne die Terminale je anzusehen** — 39 Schlüsselwörter standen in der Grammatik
> und nicht in der Tabelle, vier Tabellenwörter (`loop`, `never`, `offset_into`, `old`) in **keiner
> Produktion**. Zwei davon trugen Argumente: **ohne `offset_into` ist ELF nicht schreibbar, ohne
> `old` nicht die Differenzaussage.** Und sein erster eigener Fund war er selbst: er las „elf" aus
> „Self", weil ihm die Wortgrenzen fehlten.

Die tragenden Luecken der ersten Fassung — `expr`, `pred`, `block`, `place`, `ifstmt`, `matchstmt`,
`params`, `variants` — sind geschlossen. **`pred` ist dabei die wichtigste**: eine Beweissprache
*ist* ihre Praedikatsprache, und erst mit ihr laesst sich sagen, wo die Linie liegt.

---

## Fuenf Entscheidungen, die alles andere festlegen

| | Entscheidung | Grund |
|---|---|---|
| **E1** | **Englische Schluesselwoerter, deutscher Fliesstext, freie Bezeichner** | Caprocks eigene Praxis. Der Wortschatz ist eine **geschlossene Tabelle**; ein Tausch kostet den Lexer |
| **E2** | **Anweisungsorientiert, Zuweisung ist KEIN Ausdruck** | `if (x = y)` ist nicht schreibbar; die Auswertungsreihenfolge bleibt sichtbar |
| **E3** | **Nichts ist implizit** — keine Umwandlung, keine Kopie eines linearen Werts, kein Auffangzweig, kein Standardwert | jede der vier Klassen hat eine bezahlte Falle |
| **E4** | **Vertraege stehen VOR dem Rumpf, in fester Reihenfolge** | ein Werkzeug, das sortieren muss, kann nicht sagen „hier fehlt `effects`" |
| **E5** | **Jede Deklaration ist an genau einer Stelle vollstaendig** | kein Praeprozessor, keine Vorwaertsdeklaration |

> **`obligation` ist KEIN Quellwort.** Die Festlegung zaehlt es unter ihren dreizehn neuen
> Woertern; es steht aber im **Pflichtenmanifest**, also im **Erzeugnis**. Der Wortschatz hier ist
> der der **Quelle** — das Manifest hat sein eigenes Format, und beides zu vermischen waere
> derselbe Riss wie zwei Schluesselwortsprachen. **Zwoelf neue Quellwoerter, nicht dreizehn.**

> **Schreibregel fuer diese Dateien:** `Backticks` bezeichnen **heutige Gabbro-Syntax**. Ein
> abgeschaffter Name steht *kursiv in Anfuehrungszeichen* — er **ist** keine Syntax mehr.

---

## Wortschatz — geschlossen

```
  Struktur   module pub use type opaque linear ghost tagged const static fn
             spec impl raw divergent prim extern section arch when
  Vertraege  requires ensures maintains breaking effects costs where in
             exhaustive old narrow to induction
  Wirkungen  reads writes locks masks allocs consumes publishes diverges pure
  Ablauf     if else match traverse over by touches retry forever until
             bounded progress on_exceeded per_pass return let mut
             unvisited consuming decreasing leave leaves next ops result
             exchange update returns
  Zeiger     ptr normal mmio dma code boot r w rw x own
  Bibliothek format table slot invariant reason state transition device reg
             class fields bank at stride count mirrors from
             assume falsifier unfalsifiable axiom lock protects rank
             check claim measures gates can_fail floor counterprobe expects
             endian little big reserved cost runs online offline
             offset_into index into option chain wrapping
             atomic acquire release seq relaxed nothing accumulates merge
             max min add or and held protects rank shared
             embeds scale walk levels node down leaf mappings
             entry vector regs out preserves clobbers stack dispatch
             per cpu ist nested masked awaits port step via
  Domaenen   slots of chain descendants queue elems fields threads reaches via
  Typen      u8 u16 u32 u64 i8 i16 i32 i64 bool never w1c rc
  Eingebaut  sizeof lenof aligned forall exists true false Self Some None
  Sonderform O @version    (KEINE Wortschatzwoerter -- s. Fussnote G6)
```

**Alles andere ist ein Bezeichner.** Ein neues Wort ist eine Sprachaenderung und braucht einen
Eintrag hier.

---

## Lexik

```ebnf
ident      = ( letter | "_" ) { letter | digit | "_" } ;
letter     = "a" … "z" | "A" … "Z" | "ä" | "ö" | "ü" | "Ä" | "Ö" | "Ü" | "ß" ;
digit      = "0" … "9" ;
hexdigit   = digit | "a" … "f" | "A" … "F" ;
int        = dec | hex | bin ;
dec        = digit { digit | "_" } ;
hex        = "0x" hexdigit { hexdigit | "_" } ;
bin        = "0b" ( "0" | "1" ) { "0" | "1" | "_" } ;
string     = quote { char } quote ;
char       = ? jedes Zeichen ausser quote und newline ? ;
quote      = ? das Zeichen U+0022 ? ;
newline    = ? Zeilenende ? ;
comment    = "--" { char } newline ;
path       = pathseg { "::" pathseg } ;                        (* G5 *)
pathseg    = ident | "u8" | "u16" | "u32" | "u64" | "i8" | "i16" | "i32" | "i64" ;
             (* `u64::max` -- beide Segmente sind Wortschatzwoerter. `primtype` als
                Pfadsegment zuzulassen ist die kleinere Aenderung; die Alternative waere,
                die Grenzwerte umzubenennen. *)
identlist  = ident { "," ident } ;
regbind    = ident ":" ident ;                                 (* G4 *)
```

> **Die Zeile `Sonderform` und warum sie keine Ausnahme ist (G6).** `O` (in `costexpr`) und
> `@version` (in `format`) sind **Terminale der Grammatik, aber keine Woerter des
> Wortschatzes**: `O` steht als Bezeichner in fester Stellung (so auch im Parser,
> `parse.rs:costexpr`), `@version` ist ein zusammengesetztes Zeichen, kein Schluesselwort.
> **Der Befund war nie die Ausnahme, sondern dass der Waechter sie nie angesehen hat** — er
> behauptete einen geschlossenen Wortschatz ueber einer Menge, aus der zwei Terminale
> stillschweigend herausfielen (Grossbuchstabe, fuehrendes `@`). Jetzt zaehlt er sie, nennt
> sie beim Namen und fuehrt sie in einer eigenen Klasse. *Eine benannte Ausnahme ist eine
> Zusage; eine unsichtbare ist ein Loch.*

**Kein Gleitkomma im Kern.** Zeichenketten nur in `claim`, `reason`, `assume` und `section`.

---

## 1. Programm, Module, Konstanten

```ebnf
program    = { item } ;
item       = [ "when" constexpr ]
             ( moduledecl | usedecl | typedecl | constdecl | staticdecl | fndecl
             | format | table | reason | state | device | assume | axiom | check
             | atomicdecl | lockdecl | accdecl | walkdecl | entrydecl | bootdecl ) ;
bootdecl   = "boot" ident "arch" ident "{"
               { bootstep }
               "dispatch" path ";"
             "}" ;
bootstep   = "step" ( call | ident "=" constexpr ) ";" ;
entrydecl  = "entry" ident [ "vector" constexpr ] [ "via" ident ] "arch" ident "{"
               "regs" "in"  "{" [ regbind { "," regbind } [ "," ] ] "}"
               "regs" "out" "{" [ regbind { "," regbind } [ "," ] ] "}"   (* G4 *)
               (* regbind steht unten bei den Hilfsregeln *)
               "preserves" "{" [ identlist ] "}"
               "clobbers"  "{" [ identlist ] "}"                (* G7: leer erlaubt *)
               entryextra
               "dispatch" path ";"
             "}" ;
entryextra = "stack" ident [ "per" "cpu" ] [ "ist" constexpr ]
             [ "nested" ( "never" | "masked" | "bounded" constexpr ) ] ;
accdecl    = "accumulates" ident ":" typeexpr
             "merge" ( "max" | "min" | "add" | "or" | "and" ) ";" ;
             (* Verbundwerte: typeexpr darf structty sein, merge gilt fuer das erste Feld und
                traegt die uebrigen mit -- P0 Teil 4c, sync:572-592 wird damit konsistent *)
moduledecl = [ "pub" ] "module" path "{" { item } "}" ;
usedecl    = [ "pub" ] "use" path ";" ;
constdecl  = [ "pub" ] "const" ident ":" typeexpr "=" constexpr ";" ;
constexpr  = expr ;                    (* zur Uebersetzungszeit auswertbar; kein Aufruf einer
                                          Funktion mit effects, kein place auf mut *)
staticdecl = [ "pub" ] "static" [ "mut" ] ident ":" typeexpr "=" expr
             [ "section" string ] ";" ;
```

**`when`** steht an jedem `item` (oben in der Produktion) und ersetzt die bedingte Uebersetzung
(335 `cfg`-Stellen in Caprock).

Es senkt sich auf `#if` ab und ist **konstant auswertbar** — kein Praeprozessor, keine Textersetzung.

---

## 2. Typen — M1, D1, D2

```ebnf
typedecl   = [ "pub" ] [ "opaque" ] [ "linear" [ "ghost" ] ] [ "tagged" ]
             "type" ident [ "(" typelist ")" ] [ "=" typeexpr ] ";" ;
typeexpr   = intty | boolty | nevertype | path | array | ptrty | structty | fnptr | variants
           | indexty ;
indexty    = [ "option" ] "index" "into" ident ;
             (* Der ERZEUGTE Indextyp einer Tabelle: `0 ..< count`. Er steht als `typeexpr`,
                weil er sonst in keiner Signatur genannt werden kann -- und dann bliebe die
                Schranke doch wieder ein von Hand geschriebener Typ neben der Tabelle. *)
nevertype  = "never" ;                             (* Rueckgabetyp von prim/divergent *)
intty      = ( "u8"|"u16"|"u32"|"u64"|"i8"|"i16"|"i32"|"i64" ) [ "in" range ] ;
boolty     = "bool" ;
range      = expr ".." expr | expr "..<" expr ;
array      = "[" typeexpr ";" constexpr "]" ;
structty   = "{" { field } "}" ;
field      = ident ":" fieldty [ "@" bitpos ] [ "offset_into" ( ident | "Self" ) ]
             (* «B36», 2026-08-15: `Self` stand in der Wortschatztabelle und in KEINER
                Produktion -- ein totes Wort, das der Waechter nie sah, weil seine
                Terminalregex nur Kleinbuchstaben las. `offset_into Self` steht in
                SYNTAX.md:524 und im ELF-Fragment; die Grammatik schrieb es nirgends.
                Dritter Fund derselben Klasse an einem Tag: eine Zusage ueber eine Menge,
                aus der die grossgeschriebenen Woerter stillschweigend herausfielen. *)
             [ "where" pred ] [ "reserved" ] "," ;
fieldty    = typeexpr
           | typeexpr "embeds" "[" int ":" int "]" [ "scale" constexpr ] ;
bitpos     = int | "[" int ":" int "]" ;
variants   = "{" ident [ "(" typeexpr ")" ] { "," ident [ "(" typeexpr ")" ] } "}" ;
fnptr      = "fn" "(" [ typelist ] ")" [ "->" typeexpr ] ;
typelist   = typeexpr { "," typeexpr } ;
params     = ident ":" typeexpr { "," ident ":" typeexpr } ;
```

```gabbro
opaque type Pa   = u64;
opaque type Iova = u64;
type SlotIdx  = u32 in 0 ..< NSLOTS;
type Refcount = u32 in 0 .. 0xFFFF_FFFF;
type Cycles   = u64 in 1 .. u64::max;

tagged type ObjectKind = { Untyped(Region), Endpoint(EpId), Frame(Pa), Cnode(SlotIdx) };

linear type Parked;
linear type Uninstalled(ObjectId);
linear ghost type Held(Lock);
linear ghost type BootPhase;
linear ghost type MayWrite(ThreadId, Pa);
linear ghost type Duty(check);
```

**`tagged`** ist der Summentyp (13 `ObjectKind`-Varianten in Caprock) und senkt sich auf eine
C-Union mit Marke ab. **`bitpos` als Bereich** deckt die 13 Mehrbitfelder in `vtd.rs` (F5).

---

## 3. Zeiger und Adressraeume — M3

```ebnf
ptrty  = "ptr" "<" space "," rights ">" typeexpr ;
space  = "normal" | "mmio" | "dma" | "code" | "boot" | "port" | ident ;
rights = right { "+" right } ;
right  = "r" | "w" | "rw" | "x" | "own" [ "@" ident ] ;
```

`own` ist das Eigentumsrecht: wer es haelt, darf freigeben — damit ist `Finalized` ohne
Lebenszeiten ausdrueckbar. Die Barriere folgt aus dem **Raum**, nicht aus der Architektur.

---

## 4. Ausdruecke — `expr`

```ebnf
expr       = orexpr ;
orexpr     = andexpr { "||" andexpr } ;
andexpr    = cmpexpr { "&&" cmpexpr } ;
cmpexpr    = bitexpr [ ( "==" | "!=" | "<" | "<=" | ">" | ">=" ) bitexpr ] ;
bitexpr    = addexpr { ( "&" | "|" | "^" | "<<" | ">>" ) addexpr } ;
addexpr    = mulexpr { ( "+" | "-" ) mulexpr } ;
mulexpr    = unary { ( "*" | "/" | "%" ) unary } ;
unary      = [ "!" | "-" ] primary ;
primary    = int | "true" | "false" | place | call | paren | builtin | optionexpr
                                                                (* G9: kein `cast` *)
           | oldexpr | "result" ;
optionexpr = "Some" "(" expr ")" | "None" ;
             (* «B35», 2026-08-15: `option index into T` hatte KEINEN Konstruktor. Der
                Bestand schreibt `Some(x)` seit jeher -- in `match`-Mustern (beispiele/01,
                dreimal), in Ausdruecken (FRAGMENTE.md IPC) und in SPRACHE.md:381 selbst.
                Die Grammatik kannte es an keiner der drei Stellen; `Some` parste als
                gewoehnlicher Aufruf, und der Kostenpass verlangte dafuer eine
                `costs`-Zeile. Nachgezogen nach R9: die EBNF folgt dem Bestand. *)
paren      = "(" expr ")" ;
call       = path "(" [ arglist ] ")" ;
arglist    = expr { "," expr } ;
(* G9: `cast` war eine echte Teilmenge von `call` und aus der Grammatik nie eindeutig
   ableitbar. Die Produktion entfaellt: ein `call`, dessen `path` einen Typ nennt, IST die
   Umwandlung. Die Unterscheidung ist eine Namensaufloesung, keine Syntaxfrage -- und ein
   Erreichbarkeitswaechter auf Nichtterminalebene konnte sie nie sehen. *)
builtin    = ( "sizeof" | "lenof" ) "(" ( typeexpr | place ) ")"
           | "aligned" "(" expr "," constexpr ")" ;
oldexpr    = "old" "(" place ")" ;                 (* AUSDRUCK, nicht Praedikat; nur in ensures *)
place      = ident { placesuffix } ;
placesuffix= "." ident | "[" expr "]" | "->" ident ;
placelist  = place { "," place } ;
```

**M1 wirkt hier und nirgends sonst:** jede Operation muss im Bereich ihres Ergebnistyps bleiben.
`a + b` mit `a, b : u32 in 0..1000` hat den Typ `u32 in 0..2000`; passt der nicht in das Ziel, ist
es ein **Uebersetzungsfehler**, keine Laufzeitpruefung.

**Division und Rest verlangen einen Nenner, dessen Bereich die Null ausschliesst.**
`%` und `/` durch `u32 in 0..n` sind nicht schreibbar; durch `u32 in 1..n` schon.

> **Die Grenze von M1 ist benannt und seit dem 2026-08-14 GEMESSEN.** `31 - x.leading_zeros()`
> braucht eine **flusssensitive** Folgerung. **Aber nur eine Regel, nicht allgemeine Inferenz:**
> *eine geprüfte Bedingung verengt den Bereich der geprüften Groesse im Zweig danach.* Vier
> Fundstellen im ganzen Baum, alle dieselbe Redewendung. Wo er nicht durchkommt, verlangt Gabbro eine
> **Einengung** statt eines Beweises: `narrow x to 1..u32::max else { … }` — eine Anweisung mit
> benanntem Ausgang, keine Beweiszeile. **Sie zaehlt als Klempnerei und muss klein bleiben; wenn
> sie das nicht tut, ist das eine Widerlegung** (s. offene Punkte).

---

## 5. Praedikate — `pred`. **Hier liegt die Linie**

```ebnf
pred       = orpred ;
orpred     = andpred { "||" andpred } ;
andpred    = notpred { "&&" notpred } ;
notpred    = [ "!" ] atompred [ "=>" pred ] ;
atompred   = cmpexpr | quant | member | reach | "(" pred ")" ;
quant      = ( "forall" | "exists" ) ident "in" domain ":" pred ;
domain     = "slots" "of" place                  (* die Slots einer Tabelle *)
           | "chain" "(" ident "," ident ")" "in" place
           | "descendants" "of" place
           | "queue" place
           | "fields" "of" path
           | "elems" "of" place
           | "threads"
           | "mappings" "of" place ;             (* erzeugt aus einer walk-Deklaration;
                das Element traegt va, level und index[level] -- P0 Teil 4b: der echte W^X-Audit
                schliesst die geteilten Kernel-Tabellen ueber index[2] >= FINE_BLOCKS aus *)
member     = expr "in" domain ;
reach      = place "reaches" place "via" ident ;
predlist   = pred { "," pred } ;
```

**Acht Domaenen, geschlossen. Schachtelung hoechstens zwei.** `old(place)` ist in `ensures`
erlaubt und sonst nicht.

> **Das ist die Linie, und sie ist hier zum ersten Mal aufschreibbar.** Es gibt **keine
> benutzerdefinierten Quantorendomaenen, keine Rekursion in `spec fn`, keine handgeschriebenen
> Lemmata**. Wer mehr braucht, braucht Verus oder F\*.
>
> **Die eine Ausnahme, und sie ist KEIN Lemma: `by induction over <domain>`.** Sie **nennt** das
> Induktionsschema, das der Uebersetzer aus der `table`-Deklaration **erzeugt** hat — kein
> Beweisschritt, kein Beweiskoerper, keine rekursive `spec fn`. **Der Grund, warum sie genannt und
> nicht geraten wird, ist Vorhersagbarkeit:** ein Uebersetzer, der das Schema waehlt, macht
> „uebersetzt es" von Loeserglueck abhaengig — und M1 bis M4 sind Typen, keine Loeser.
> Ganz in [`SPRACHE.md`](SPRACHE.md).
>
> **Der Preis ist unbeziffert und vermutlich der groesste des ganzen Entwurfs:** es gibt keinen
> Notausgang. Faellt eine Kernel-Eigenschaft aus den sieben Domaenen heraus, ist sie **nicht
> formulierbar** — nicht „teuer", sondern **gar nicht**.

---

## 6. Funktionen und Vertraege — E4

```ebnf
fndecl   = [ "pub" ] [ "spec" | "impl" | "raw" | "divergent" | "prim" | "extern" ]
           "fn" ident "(" [ params ] ")" [ "->" typeexpr ]
           [ "requires"  predlist ]
           [ "ensures"   predlist ]
           [ "maintains" identlist ]
           [ "effects"   "{" efflist "}" ]
           [ "costs"     "<=" expr "ops" ]
           [ "by"        inductlist ]
           [ "section" string ] [ "arch" ident ] [ "when" constexpr ]
           ( block | "=" pred ";" | ";" ) ;      (* "=" pred: nur fuer spec fn *)
inductlist = induct { "," induct } ;
induct     = "induction" "over" domain ;      (* nennt das SCHEMA -- kein Lemma, kein Beweisschritt *)
efflist  = eff { "," eff } ;
eff      = "reads" place | "writes" place | "locks" [ "shared" ] place | "masks" ident
         | "allocs" ident | "consumes" place | "publishes" place | "diverges"
         | "pure" ;
```

> **`effects` ist NICHT fail-open.** Eine Funktion **ohne** `effects` ist ein Uebersetzungsfehler;
> wer nichts anfasst, schreibt `effects { pure }`. Die frueher moegliche Auslassung war zugleich
> **die staerkste Zusage und die kuerzeste Spezifikation** — der Anreiz stand gegen die
> Vollstaendigkeit.

```gabbro
spec fn cdt_wellformed(c: CapSpace) -> bool =
    forall s in slots of c: c.parent_chain(s) reaches Root via parent;

impl fn revoke(c: ptr<normal, rw> CapSpace, s: SlotIdx) -> Result
    ensures   !exists k in descendants of s: k.used
    maintains cdt_wellformed
    effects   { writes c.slots, locks CAPS }
    by        induction over descendants of s
{ … }

impl fn delete_leaf(c: ptr<normal, rw> CapSpace, s: SlotIdx) -> Result
    requires  Held(CAPS), c.slots[s].used, !exists k in slots of c: k.parent == s
    ensures   !c.slots[s].used, old(c.objects[o].refcount) == c.objects[o].refcount + 1
    maintains cdt_wellformed, refcount_matches
    effects   { writes c.slots, writes c.objects, locks CAPS }
    costs     <= 200 ops
{ … }
```

**`breaking`** benennt den Bereich, in dem eine Invariante ruht — drei Fundstellen in Caprock:

```ebnf
breakstmt = "breaking" identlist block ;
```

Sie muss am Ende des Blocks wiederhergestellt sein; der Bereich ist **sichtbar statt versteckt**.

---

## 7. Anweisungen

```ebnf
block      = "{" { stmt } "}" ;
stmt       = letstmt | assign | ifstmt | matchstmt | loopform | breakstmt
           | narrowstmt | lockstmt | leavestmt | nextstmt | publishstmt
           | awaitload | exchstmt | "return" [ expr ] ";" | exprstmt ;
leavestmt  = "leave" ident ";" ;
nextstmt   = "next" ident ";" ;
awaitload  = "let" ident "=" place "awaits" "{" placelist "}" ";" ;
exchstmt   = "let" ident "=" place "exchange" xform
             [ "publishes" ( placelist | "nothing" ) ]
             [ "awaits" "{" placelist "}" ] ";" ;
xform      = "update" "(" ident ")" block
           | expr "when" pred "returns" ident ;
letstmt    = "let" [ "mut" ] ident [ ":" typeexpr ] "=" expr ";"
           | "let" ident "=" call "else" "(" ident ")" block ;
assign     = place ( "=" | "+=" | "-=" | "&=" | "|=" ) expr ";" ;
exprstmt   = call ";" ;
ifstmt     = "if" expr block { "else" "if" expr block } [ "else" block ] ;
matchstmt  = "match" expr "{" { ident [ "(" ident ")" ] "=>" block } "}" ;
narrowstmt = "narrow" place "to" range "else" block ;
```

**`match` ist erschoepfend** — es gibt keinen Auffangzweig; eine neue Variante bricht die
Uebersetzung. **Fehlerfortpflanzung** ist `let … else (e) { … }`: kein verborgener Kontrollfluss,
der `else`-Zweig muss divergieren oder zurueckkehren.

---

## 8. Schleifen — **drei Formen, und unendlich ist eine davon**

**Die Regel ist nicht „jede Schleife endet", sondern: was eine Schleife tun darf, steht dabei.**

```ebnf
loopform   = traverse | retry | forever ;

traverse   = "traverse" ident [ "of" expr ]
             "over"  domain
             "by"    ( "unvisited" | "consuming" | "decreasing" expr )
             [ "touches" efflist ]
             block ;

retry      = "retry" [ ident ] [ "until" pred ]
             "bounded"     expr "ops"
             [ "progress"  ident ]
             "on_exceeded" ident
             [ "effects" "{" efflist "}" ]
             block ;

forever    = "forever" [ ident ]
             "per_pass"  "bounded" expr "ops"
             "on_exceeded" ident
             "effects"   "{" efflist "}"
             [ "progress" ident ]
             [ "leaves"   identlist ]
             block ;
```

| Form | endet? | was die Klempnerei erledigt |
|---|---|---|
| **`traverse`** | ja, durch die Menge | Bereich **und** Terminierung; `by consuming` zusaetzlich die Blattheit ueber die Ordnung der Domaene |
| **`retry`** | ja, durch `bounded` | Terminierung als **Zahl**; der Ueberlauf ist **benannt** (`on_exceeded`), nicht gedeutet |
| **`forever`** | **nein — und das ist erlaubt** | jeder **Durchgang** ist begrenzt, der **Rahmen** steht in `effects` |

```gabbro
forever
    per_pass bounded 4096 ops
    on_exceeded watchdog_schlug_an
    effects  { reads READY, writes CURRENT, locks SCHEDS }
    progress timer_tick_arrives
{ … }
```

> **Das ist der enge Rahmen.** Eine Leerlaufschleife, die Hauptschleife eines Servers, ein
> Spinlock — sie sollen ewig laufen. Was **nicht** erlaubt ist: ein Durchgang, der selbst
> unbegrenzt ist, oder eine Schleife, die anfasst, was nicht in ihrem Rahmen steht.
> **`per_pass` und `effects` sind Pflicht; `forever` ohne sie uebersetzt nicht.**
>
> **`progress` nennt, WER sie beendet** — eine Annahme ueber die Umgebung, mit Falsifikator. Der
> Watchdog **ist** der Falsifikator. Damit ist eine Warteschleife nicht „unbeweisbar", sondern
> **beweisbar unter einer benannten, falsifizierbaren Annahme**.

---

## 9. Tabellen, Traversierungen, Formate

```ebnf
table      = "table" ident [ "count" constexpr ] "{"
               { constdecl | slotdecl | invariant | opdecl } "}" ;
opdecl     = "ops" identlist ";" ;
walkdecl   = "walk" ident "levels" constexpr "{"
               "node" ":" array ","
               "down" ":" ident "when" pred ","
               "leaf" ":" pred ","
               { invariant }
             "}" ;
slotdecl   = "slot" "{" { ident ":" slottype "," } "}" ;
slottype   = typeexpr | intty "wrapping" ;
             (* `index into T` ERBT die Schranke aus `T`s `count` -- der Indextyp wird
                erzeugt, nicht geschrieben. Ohne `count` bleibt er unbeschraenkt, und das
                ist dann eine Aussage der Deklaration statt eine Konvention. *)
invariant  = "invariant" ident "cost" costexpr "runs" ( "online" | "offline" )
             [ "by" inductlist ] ":" pred ";" ;
costexpr   = "O" "(" expr ")" ;

format     = "format" ident [ "@version" int ] [ "endian" ( "little" | "big" ) ]
             "{" { field } "}" ;
```

**Variable Laengen und Versaetze** — damit ist ELF ein `format`:

```gabbro
format Elf64 endian little {
    e_phoff     : u64 offset_into Self where e_phoff + e_phentsize * e_phnum <= lenof(Self),
    e_phentsize : u16 in 56 .. 56,
    e_phnum     : u16 in 0 .. 65535,
}
```

`offset_into Self` bindet den Versatz an die Pufferlaenge; die `where`-Klausel ist die **einzige**
Zusatzangabe und senkt sich auf eine Bereichspruefung ab.

**`reason`** ist Regel 3 in Schreibweise, **`state`** nennt die erlaubten Uebergaenge eines Wertes:

```ebnf
reason  = "reason" ident "{" { ident "=" int string } [ "exhaustive" ] "}" ;
state   = "state" ident "{" { transition } "}" ;
```

`state` und `device`s `transition` sind **dasselbe Konstrukt auf zwei Ebenen**: einmal ueber
Feldern, einmal ueber Registerbits. `resume` (`iretq`/`eret`) ist der Uebergang auf der dritten —
ueber dem Maschinenzustand.

---

## 10. Geraete — und Falle 4

```ebnf
device  = "device" ident [ "(" params ")" ] "at" space
          "{" [ mirrors ] { regdecl | bank | transition } "}" ;
mirrors = "mirrors" place "from" place ";" ;       (* EINMAL je Geraet, nicht je Uebergang *)
bank    = "bank" ident "at" expr "stride" expr "count" expr "{" { regdecl } "}" ;
regdecl = "reg" ident ":" intty "@" expr
          "class" ( "r" | "w" | "rw" | "w1c" | "rc" )
          [ "fields" "{" { ident "@" bitpos "," } "}" ]
          [ "requires" pred ] ;
transition = "transition" ident "{" transset "}"
             [ "requires" pred ] [ "effects" "{" efflist "}" ] ;
transset   = placeshift { "," placeshift } ;      (* MEHRERE Orte in EINEM Zug -- s. Grenze *)
placeshift = shiftplace ":" expr "->" expr ;                   (* G3 *)
shiftplace = ident { "." ident | "[" expr "]" } ;
             (* KEIN "->"-Suffix: in `ST: ACK -> ACK` waere `ACK -> ACK` sonst zugleich
                placesuffix und Uebergangspfeil. Die Entscheidung steht hier, nicht im
                Parser -- ein Zeigerzugriff links eines Uebergangs ist damit nicht
                schreibbar, und das ist die gewollte Seite: ein `transition` beschreibt
                Registerfelder, keine Zeigerketten. *)
```

```gabbro
device Vtd(base: Pa) at mmio {
    reg GCMD : u32 @0x18 class w fields { TE @31, SRTP @30, IRE @25 }
    reg GSTS : u32 @0x1c class r  fields { TES @31, RTPS @30 }
    reg CAP  : u64 @0x08 class r  fields { FRO @[33:24], ND @[2:0] }

    bank FRR at CAP.FRO * 16 stride 16 count 256 { reg FR : u64 @0x8 class rw }

    mirrors GCMD from GSTS;          -- EINMAL: alle Zustandsbits kommen aus GSTS

    transition arm_te { GCMD.TE: 0 -> 1 }
        requires GSTS.RTPS == 1
        effects  { writes GCMD }
}
```

> **`keeping` toetet Falle 4, und `class w` allein tat es nicht.** Die Falle ist nicht „GCMD lesen",
> sondern **„beim Schreiben die Zustandsbits nicht mitschreiben"**. `keeping` nennt die Bits, die
> das geschriebene Wort **mitfuehren** muss; ihre Quelle ist ein lesbares Register. Ein `store`,
> der sie fallenlaesst, ist damit **nicht schreibbar** — und ein Lesen von `GCMD` bleibt weiterhin
> untypisierbar.
>
> **`bank`** deckt Register an laufzeitberechneter Basis (F6): `FRR` bei `CAP.FRO*16`. Der Index
> ist M1-beschraenkt durch `count`.

---

## 11. Nebenlaeufigkeit

```ebnf
atomicdecl  = [ "pub" ] "atomic" ident ":" typeexpr
              [ "publishes" nutzlast ]                          (* G1 *)
              [ "acquire" | "release" | "seq" | "relaxed" ] ";" ;
              (* Reihenfolge nach dem BESTAND, nicht nach dem Entwurf: SYNTAX.md:603 und
                 FRAGMENTE.md F6 (4x) schreiben `publishes` VOR der Ordnung. *)
publishstmt = place "=" expr "publishes" nutzlast ";" ;
nutzlast   = "{" placelist "}" | "nothing" ;
             (* Nach dem BESTAND entschieden (2026-08-15): 22-mal `nothing`, 11-mal die
                Klammerform, 2-mal klammerlos. Die Grammatik folgt den 33 und nicht den 2 --
                die beiden Ausnahmen in beispiele/05 sind nachgezogen. Klammern trennen die
                Nutzlast sichtbar von dem, was folgt (`release`, `;`). *)
lockdecl   = "lock" ident "protects" "{" placelist "}"
             "rank" constexpr [ "held" "<=" constexpr "ops" ]
             [ "shared" "held" "<=" constexpr "ops" ] [ "masks" ident ] ";" ;
lockstmt   = "locks" [ "shared" ] place block ;
```

```gabbro
lock CAPS protects { slots, cdt } rank 2 masks irqs;
atomic COLOR_DONE : bool publishes { color_report } release;
```

**`publishes` ist Pflicht an jedem Atomic** — die Nutzlast ist Teil des Modells, nicht des
Kommentars. **`rank`** gibt die Sperrordnung; Nehmen verlangt echt kleineren Rang. Ein `locks`-Block
gibt am Ende frei; wer kopieren-und-freigeben will, tut es **innerhalb** und nimmt danach neu.

---

## 12. Hardwareannahmen und Axiome — **tragend, nicht Beiwerk**

```ebnf
assume = "assume" ident string
         ( "falsifier" ident | "unfalsifiable" string ) ";" ;
axiom  = "axiom" ident "(" [ params ] ")" [ "->" typeexpr ]
         [ "requires" pred ]                                    (* G2 *)
         "effects" "{" efflist "}"
         ( "falsifier" ident | "unfalsifiable" string ) ";" ;
```

```gabbro
assume vtd_te_effective
    "GCMD.TE schaltet die Uebersetzung scharf; DMA ohne Kontexteintrag faultet."
    falsifier probe_vtd_te;

assume x2apic_two_step
    "EN und EXTD in einem Schreibvorgang ist ein verbotener Uebergang."
    unfalsifiable "qemu64 hat kein x2APIC";

axiom write_cr3(p: Pa) effects { writes tlb, writes active_table } falsifier probe_cr3;
```

**Drei Klassen, und die dritte gibt es syntaktisch nicht:** *falsifiziert* (Sonde lief und hielt),
*nicht falsifizierbar* (**mit Grund als Zeichenkette**), *nicht gefahren* — das ist die
**Abwesenheit beider Angaben** und ein **Uebersetzungsfehler**. Eine nicht gefahrene Annahme darf
nie wie eine falsifizierte aussehen.

**Die Annahmenmenge wird ins Erzeugnis emittiert** („bewiesen unter A1…An"), als **Menge von Namen
mit Klasse**, nicht als Zahl — eine Ratsche ueber einer Kardinalzahl greift nicht gegen Austausch.

> **Damit ist die Zusage relativ, und das steht im Artefakt statt in einer Fussnote:**
> *speichersicher unter A1…An.* Ein Beweis, dessen Annahmenmenge der Verbraucher nicht kennt, hat
> keine Reichweite. **Die Axiomschicht ist die groesste unbewiesene Flaeche der Sprache** — groesser
> als der Uebersetzer — und deshalb zaehlbar und ratschenfaehig.

---

## 13. `check` — die lineare Pruefpflicht

```ebnf
check = "check" ident "{"
          "claim"        string
          "measures"     placelist
          "gates"        identlist
          "can_fail"     block
          [ "floor"      predlist ]
          [ "counterprobe" string "expects" ident ]
        "}" ;
```

Der Uebersetzer erzeugt ein `linear ghost Duty(ident)`. **Vier Uebersetzungsfehler fallen aus
M1/M2/M3, nicht aus Sonderregeln:** `gates` fehlt → die Pflicht wird nie verbraucht;
`can_fail` fehlt → dito; eine Groesse unter `measures`, die der **gemessene Pfad** schreibt →
Schreibrecht; einseitige Schwelle ohne `floor` → die Groesse hat keinen Bereich.

**Die `measures`-Liste IST die Berichtszeile** — daraus entsteht die Formatierung, ohne dass
Formatierung im Sprachkern existiert.

---

## 14. Bootphase, Maschinenzustand, Assembler

```gabbro
raw fn phys_write(p: Pa, w: u64) requires BootPhase effects { writes phys };
fn boot_end(t: BootPhase) effects { consumes t, writes code_map };

prim fn switch_to(from: ptr<normal,rw> Context, to: ptr<normal,r> Context) -> never;
prim fn resume(k: ptr<normal,r> Context) -> never;
divergent fn idle() effects { diverges };
```

`boot_end` verbraucht die **lineare** Marke **und** bildet `code<boot>` ab — ein Ereignis. Eine
Sonde dorthin muss danach faulten; das ist der Falsifikator.

---

## Was es absichtlich nicht gibt

`while` · `for` · `goto` · `union` als Umdeutung · Praeprozessor · implizite Umwandlung · `void*` ·
Zeigerarithmetik ohne Grundlage · Auffangzweig · Ausnahmen · Vererbung · Reflexion · GC ·
Gleitkomma im Kern · Zuweisung als Ausdruck · Vorwaertsdeklaration · Selbst-Hosting ·
benutzerdefinierte Quantorendomaenen · Rekursion in `spec fn` · handgeschriebene Lemmata.

---

## Offene Punkte — Stand 2026-08-14, nach der Festlegung

**Die neun Entwurfsfragen sind in [`SPRACHE.md`](SPRACHE.md) §18 entschieden (F1–F9).**
Was hier steht, ist, was danach **noch offen** ist — und das sind Messungen, keine Entwuerfe.

### Die eine Messung, an der die Festlegung haengt

- [ ] **Die 74-Pflichten-Messung gegen diese Fassung wiederholen: haengende Klempnerei 19 → 0.**
      Das ist die **Abnahme** der Festlegung, nicht ihre Zustimmung. Bleibt eine haengen, ist sie
      an dieser Stelle widerlegt — mit Klasse und Fundstelle.

### Vier Messlatten, alle vorab gesetzt

- [ ] **`narrow`-Zaehlung am Baum: ≤ 24 Fundstellen.** Wachsen sie darueber, ist die Regelmenge
      V1–V3 zu klein — **und *das* ist die Widerlegung, nicht ein weiteres Regelwachstum in Stille.**
- [ ] **Wieviele der 17 gemessenen Logik-Pflichten brauchen `by induction over`**, wieviele kommen
      ohne aus, **wieviele braeuchten rekursive `spec fn` oder Lemmata**? Ein einziger Fall in der
      letzten Spalte setzt die Decke tiefer.
- [ ] **Kostenwahrheit je uebersetztem Modul** (Festlegung §14.2): erzeugtes C gegen
      handgeschriebenes im Differenz-Benchmark.
- [ ] **Die zehn Fragmente auf diese Syntax ziehen**, Waechter gruen. Sechs liegen in
      [`FRAGMENTE.md`](FRAGMENTE.md) und sind gegen die **zweite** Fassung geschrieben.

### Was auch nach der Festlegung nicht gedeckt ist — benannt, nicht vergessen

- [ ] **Die Naht CPU ↔ Geraet** hat kein mechanisiertes Vorbild ([`BEWEIS.md`](BEWEIS.md)).
- [ ] **Der `iasm`-Eintrittspfad hat keinen nachgelagerten Beweiser** — das Vertrauen schrumpft von
      161 Fundstellen auf eine Stelle, es verschwindet nicht.
- [ ] **Lebendigkeit und Fortschritt** faellt unter keinen Mechanismus.
- [ ] **Die Geistertheorie-Schablonen sind die vertrauenskritischste Flaeche** und gehoeren einmal
      nach Isabelle ([`BEWEIS.md`](BEWEIS.md), Stufe 1).
