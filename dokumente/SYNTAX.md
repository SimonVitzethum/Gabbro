# Gabbro — the syntax

**The source for the surface.** [`SPRACHE.md`](SPRACHE.md) says which mechanisms there are
and why; [`BEWEIS.md`](BEWEIS.md), what they are there for; here stands how one writes them down.
What does not stand here is not writable.

As of 2026-08-13, second version. **The compiler reads this** — since 2026-08-16 the corpus test
`die_beispiele_der_grammatik_gehen_selbst_durch` runs the ```gabbro blocks below through the
checker, `wortschatz.rs` holds the lexer against the vocabulary table, and
`pruefe-wortschatz.py` holds the table against the terminals of the EBNF. *(Until 2026-08-17 the
line here read "No compiler reads this." That was true on 2026-08-13 and has been false since the
compiler existed — a grammar document whose examples nobody translates is the most expensive kind
of prose: it looks like evidence.)*

> **What every rule of this grammar has to achieve:** discharge one **plumbing** obligation by
> construction — index, overflow, alias, frame, lock, race, refinement. If one of them stays hanging
> on the programmer, that is **a refutation** at that point, not a blemish.
> **Logic** the programmer writes anyway, in every language.

---

## State — measured

| | first version | **this one** |
|---|---|---|
| defined EBNF rules | 40 | **132** |
| used but never defined | 21 (17 load-bearing) | **0** |
| open design questions | 7 | **9, named at the end** |
| **Guardian** | — | `pruefe-syntax.sh` checks **closure of the rules AND coverage of the terminals by the vocabulary**, each with a speech test |

> **THIRD blind spot, the same family — and it cost three grammar errors that made the language
> unusable.** The guardian checked that every **used** rule is defined, **not whether
> every defined rule is reachable**. Found by a fragment checker, retrofitted as a
> reachability run from `program`. It found immediately:
> **`atomicdecl`, `lockdecl`, `lockstmt` were defined and never reachable from `program`** —
> so **no atomic, no lock, no critical section** in the whole language, while
> all six fragments use them. And a **duplicate `item` production** in which the second
> hid the first.
>
> Plus two errors no guardian saw, because they lay *inside* valid grammar:
> **`old(x)` hung under `atompred` instead of under `primary`** — it could stand as a predicate on
> its own, but could occur in **no expression**, hence never next to `==`. **The difference
> statement this project carries as a core lesson was not writable** — and our own `delete_leaf`
> example gave one. And **`fndecl` allowed only `block | ";"`**, with which **not a single `spec fn`
> was writable**.

> **The guardian had a second blind spot, and it was the same as the first.** It checked
> the **nonterminals** for closure and claimed alongside a "closed
> vocabulary", **without ever looking at the terminals** — 39 keywords stood in the grammar
> and not in the table, four table words (`loop`, `never`, `offset_into`, `old`) in **no
> production**. Two of them carried arguments: **without `offset_into` ELF is not writable, without
> `old` the difference statement is not.** And its first find of its own was itself: it read "elf" out
> of "Self", because it lacked the word boundaries.

The load-bearing gaps of the first version — `expr`, `pred`, `block`, `place`, `ifstmt`, `matchstmt`,
`params`, `variants` — are closed. **`pred` is the most important of them**: a proof language
*is* its predicate language, and only with it can one say where the line lies.

---

## Five decisions that fix everything else

| | Decision | Reason |
|---|---|---|
| **E1** | **English keywords, German running text, free identifiers** | Caprock's own practice. The vocabulary is a **closed table**; a swap costs the lexer |
| **E2** | **Statement-oriented, assignment is NOT an expression** | `if (x = y)` is not writable; the evaluation order stays visible |
| **E3** | **Nothing is implicit** — no conversion, no copy of a linear value, no catch-all branch, no default value | each of the four classes has a paid-for trap |
| **E4** | **Contracts stand BEFORE the body, in a fixed order** | a tool that has to sort cannot say "`effects` is missing here" |
| **E5** | **Every declaration is complete at exactly one place** | no preprocessor, no forward declaration |

> **`obligation` is NOT a source word.** The definition counts it among its thirteen new
> words; but it stands in the **obligation manifest**, i.e. in the **artefact**. The vocabulary here is
> that of the **source** — the manifest has a format of its own, and mixing the two would be
> the same crack as two keyword languages. **Twelve new source words, not thirteen.**

> **Writing rule for these files:** `Backticks` denote **today's Gabbro syntax**. An
> abolished name stands *in italics in quotation marks* — it **is** no longer syntax.

---

## Vocabulary — closed

```
  Struktur   module pub use type opaque linear ghost tagged const static fn
             spec impl raw divergent prim extern section arch when
  Vertraege  requires ensures maintains breaking effects costs where in
             exhaustive old narrow to induction order advances
  Wirkungen  reads writes locks masks allocs consumes publishes diverges pure
  Ablauf     if else match traverse over by touches retry forever until
             bounded progress on_exceeded per_pass return let mut
             unvisited consuming decreasing leave leaves next ops result
             exchange update returns insert remove relabel
  Zeiger     ptr normal mmio dma code boot r w rw x own
  Bibliothek format table slot invariant reason state transition device reg
             class fields bank at stride count backed mirrors from
             assume falsifier unfalsifiable axiom lock protects rank group rcu observes reclaims
             check claim measures gates can_fail floor counterprobe expects
             endian little big reserved cost runs online offline
             offset_into index into option chain wrapping
             atomic acquire release seq relaxed nothing accumulates merge
             max min add or and held protects rank shared
             embeds scale walk levels node down leaf mappings
             entry entrust vector regs out preserves clobbers stack dispatch
             per cpu ist nested masked awaits port step via
  Domaenen   slots of chain descendants ancestors queue elems fields threads
             reaches via
  Typen      u8 u16 u32 u64 i8 i16 i32 i64 f32 f64 rounded finite bool never w1c rc
  Eingebaut  sizeof lenof aligned forall exists true false Self Some None
  Sonderform O @version Held    (KEINE Wortschatzwoerter -- s. Fussnote G6)
```

**Everything else is an identifier.** A new word is a language change and needs an
entry here.

---

## Lexis

```ebnf
ident      = ( letter | "_" ) { letter | digit | "_" } ;
letter     = "a" … "z" | "A" … "Z" | "ä" | "ö" | "ü" | "Ä" | "Ö" | "Ü" | "ß" ;
digit      = "0" … "9" ;
hexdigit   = digit | "a" … "f" | "A" … "F" ;
int        = dec | hex | bin ;
dec        = digit { digit | "_" } ;
hex        = "0x" hexdigit { hexdigit | "_" } ;
bin        = "0b" ( "0" | "1" ) { "0" | "1" | "_" } ;
float      = dec "." dec [ "e" [ "+" | "-" ] dec ] ;           (* «F», 2026-08-18 *)
(* Der Punkt ist mehrdeutig, und zwar GEMESSEN: `0..100` ist heute gueltiger Bereich. Die
   Regel ist maximal munch -- `..` frisst zuerst, also ist `1..5` ein Bereich und `1.5` eine
   Gleitkommazahl. Ein Punkt ohne Ziffer dahinter (`1.`) wird abgelehnt.

   NUR KLEINES `e` im Exponenten. Der Leser lehnt `0X`/`0B` seit jeher ab (`L004`) -- eine
   Schreibweise, nicht zwei, und die Regel stand schon da. *)
string     = quote { char } quote { quote { char } quote } ;   (* «B22» *)
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

> **One comma rule for all lists (2026-08-16).** `entrydecl`, `slotdecl` and
> `reg … fields` wrote three different rules for the same thing — twice a
> compulsory trailing comma, once none, and the parser held none of them. **Now one:
> separating comma between the entries, trailing comma optional.** *The existing code writes it
> everywhere; nothing breaks, and the grammar has one rule instead of three.*

> **The `Sonderform` line and why it is not an exception (G6).** `O` (in `costexpr`),
> `@version` (in `format`) and `Held` (in `heldpred`) are **terminals of the grammar but
> not words of the vocabulary**: `O` stands as an identifier in a fixed position (so too in the parser,
> `parse.rs:costexpr`), `@version` is a composite character, not a keyword.
> **The finding was never the exception, but that the guardian never looked at it** — it
> claimed a closed vocabulary over a set out of which two terminals
> silently fell (capital letter, leading `@`). Now it counts them, names
> them and carries them in a class of their own. *A named exception is a
> promise; an invisible one is a hole.*


> ## The surface of Gabbro is English — decided 2026-08-19
>
> **Keywords were English from the start**, for the reason written down in `TODO.md`: *that is
> what the existing code is.* What was never decided is everything **else a user of Gabbro
> reads** — and it had drifted.
>
> **Measured on the day of the decision: 41 of 100 refusal messages were German**, and the
> mixture ran through single sentences (`M101`: *„die Rueckgabe requires `u32 in 0 .. 100`, the
> value has `u32`"*).
>
> | | |
> |---|---|
> | **English** | keywords · refusal messages and their notes · the reports of `gabbro paesse`, `schablonen`, `pflichten`, `zeugnis` · the vocabulary table |
> | **German stays** | the working documents of this folder (`PLAN.md`, `MESSUNGEN.md`, `TODO.md`), source comments, and every identifier a *user* chooses |
>
> **The line is: what Gabbro says is English; what the folder says about Gabbro is not.** *An
> identifier is the user's word, not the language's* — `beispiele/01` may keep calling a slot
> `Kappenraum`.
>
> **And a rule of this kind needs a guardian, or it drifts back** — `pruefe-englisch.py` holds
> the refusal texts against a German word list, in both directions.

~~**No floating point in the core.**~~ **Revoked 2026-08-18 by «F».** `f32` and `f64` are
core types: a declared range, a NaN bit and an infinity bit, arithmetic rounded outward,
round-to-nearest-even pinned. *The sentence stood for as long as the need was measured at
zero; the folder decided otherwise, and «F0» names the substitute for the missing need
instead of inventing one.*

Strings only in `claim`, `reason`, `assume` and `section`.

---

## 1. Program, modules, constants

```ebnf
program    = { item } ;
item       = [ "when" constexpr ]
             ( moduledecl | usedecl | typedecl | constdecl | staticdecl | fndecl
             | format | table | reason | state | device | assume | axiom | check
             | atomicdecl | lockdecl | rcudecl | gruppedecl | accdecl | walkdecl | entrydecl | entrustdecl
             | bootdecl ) ;
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
entrustdecl = "entrust" ident "at" ident "arch" ident "{"
                "regs" "in" "{" [ regbind { "," regbind } [ "," ] ] "}"
                "stack"  ident
                "assume" ident ";"
              "}" ;
(* «entrust» -- der Raum, dessen INHALT Gabbro nicht kennt (2026-08-18).

   Gabbro sagt ueber den Gast NICHTS: keine Kosten, keine Wirkungen, keine Terminierung.
   Was es sagt, ist der VERTRAG AM EINTRITT -- welche Register der Gast bekommt, auf welchem
   Stapel er laeuft, und in welchem `code`-Raum er liegt.

   `at` nimmt einen NAMEN, keinen Ausdruck. Der Raum ist ein deklariertes Ding; ein `entrust`
   auf einen gerechneten Wert waere ein Sprung an eine ausgerechnete Adresse -- genau das,
   was nicht nennbar sein soll. Der Namenspass haelt ihn (`N006`).

   `assume` ist PFLICHT und nicht schmueckend: dass der Gast seinen Vertrag haelt, ist eine
   Aussage ueber die Umgebung. Sie muss erklaert und FALSIFIZIERBAR sein -- dieselbe Regel
   wie bei `progress` (`S003`/`S004`), hier `N004`/`N005`.

   *Kein neuer Pass, kein `effects`, kein `costs`: Isolation statt Beweis. Das ist keine
   Luecke, sondern der Zweck eines Mikrokernels.* *)
entryextra = "stack" ident [ "per" "cpu" ] [ "ist" constexpr ]
             [ "nested" ( "never" | "masked" | "bounded" constexpr ) ] ;
accdecl    = "accumulates" ident ":" typeexpr
             "merge" ( "max" | "min" | "add" | "or" | "and" )
             [ "per" "cpu" constexpr ] ";" ;
(* `per cpu N` -- die ZELLENZAHL, 2026-08-18. SPRACHE.md 11.4 sagte seit jeher "one cell
   per core, merged over the NCORES-bounded loop" und nannte die Zahl NIRGENDS; der
   Erzeuger haette `NCORES` raten muessen. Optional in der Grammatik, PFLICHT fuer die
   Absenkung -- ohne sie weigert er sich benannt.

   **Der aktuelle Kern ist KEIN Ausdruck der Sprache.** Er ist eine Maschinenfrage, also
   ein fremder Rumpf (`gabbro_kern()`), und das Zeugnis fuehrt ihn in Abschnitt E mit
   seinem Vertrag -- genauso wie den Rumpf einer Sperre. *Ihn in die Sprache zu heben
   hiesse, eine Maschinenfrage als Ausdruck zu tarnen.* *)
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

**`when`** stands at every `item` (above in the production) and replaces conditional compilation
(335 `cfg` sites in Caprock).

It lowers to `#if` and is **constant-evaluable** — no preprocessor, no text substitution.

---

## 2. Types — M1, D1, D2

```ebnf
typedecl   = [ "pub" ] [ "opaque" ] [ "linear" [ "ghost" ] ] [ "tagged" ]
             "type" ident [ "(" typelist ")" ] [ markorder ] [ "=" typeexpr ] ";" ;
markorder  = "order" "{" identlist "}" ;
(* «B37», 2026-08-17. Der Befund stand im Bootfragment selbst: „die Marke traegt die
   Reihenfolge, aber sie traegt sie als LINEARITAET, nicht als ORDNUNG." Ein linearer Wert
   erzwingt eine KETTE, aber nicht WELCHE -- bei sechs Bootschritten typprueften alle 720
   Reihenfolgen, weil M2 nur sieht, dass jede Marke genau einmal weiterwandert.

   Das Fragment nannte beide Auswege: je Schritt eine eigene Marke (dann waechst der
   Wortschatz mit jedem Bootschritt) oder eine Ordnung auf Marken. **Gewaehlt ist die
   zweite** -- die Stufen sind Bezeichner in EINER Deklaration, der Wortschatz waechst um
   zwei Woerter, einmal.

   `order` steht VOR dem `=`, weil es kein Rumpf ist: eine Ordnung sagt nichts darueber,
   woraus der Wert besteht, sondern welche Schritte auf ihm zulaessig sind. Ein
   `linear ghost type` hat ohnehin keinen Rumpf. *)
typeexpr   = intty | floatty | boolty | nevertype | path | array | ptrty | structty | fnptr | variants
           | indexty ;
indexty    = [ "option" ] "index" "into" ident ;
             (* Der ERZEUGTE Indextyp einer Tabelle: `0 ..< count`. Er steht als `typeexpr`,
                weil er sonst in keiner Signatur genannt werden kann -- und dann bliebe die
                Schranke doch wieder ein von Hand geschriebener Typ neben der Tabelle. *)
nevertype  = "never" ;                             (* Rueckgabetyp von prim/divergent *)
intty      = ( "u8"|"u16"|"u32"|"u64"|"i8"|"i16"|"i32"|"i64" ) [ "in" range ] ;
floatty    = ( "f32" | "f64" ) [ "in" frange ] ;                    (* «F», 2026-08-18 *)
frange     = fexpr ( ".." | "..=" | "..<" ) fexpr ;
fexpr      = float [ "rounded" ] | ident | int ;
(* «F» -- f32 und f64.

   `rounded` ist PFLICHT an einem Literal, das nicht exakt darstellbar ist, und dort auch
   die einzige Form. Gemessen an 340 Literalen eines echten Renderers waeren ohne es 53
   abgelehnt worden, darunter ln 2 und 2 pi (FRAGMENTE.md, «F0»). Verboten ist nicht das
   Inexakte, sondern das STILLSCHWEIGEND Inexakte -- genau der Satz, den `wrapping` ueber
   den Ueberlauf sagt.

   `finite` steht nur hinter `narrow … to` und stellt Nicht-NaN-Sein her. Ohne diese
   Tatsache liefert die Negation eines Gleitkommavergleichs NICHTS -- mit ihr rechnet man
   gewoehnlich weiter. *)
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
linear ghost type Duty(farbtest);   -- der Parameter ist der NAME einer `check`-
                                    -- Deklaration, nicht das Wort `check` (:697)
```

**`tagged`** is the sum type (13 `ObjectKind` variants in Caprock) and lowers to a
C union with a tag. **`bitpos` as a range** covers the 13 multi-bit fields in `vtd.rs` (F5).

---

## 3. Pointers and address spaces — M3

```ebnf
ptrty  = "ptr" "<" space "," rights ">" typeexpr ;
space  = "normal" | "mmio" | "dma" | "code" | "boot" | "port" | ident ;
rights = right { "+" right } ;
right  = "r" | "w" | "rw" | "x" | "own" [ "@" ident ] ;
```

**`own` is the ownership right — and what it does TODAY is less than that sentence used to
promise.** Measured 2026-08-19, prompted by a review from outside:

| | |
|---|---|
| what the checker reads | **read + write**, in three `matches!` arms next to `rw` (`m3.rs`, `emit.rs`) |
| `own @ident` — the origin | **no reader anywhere**; parsed, stored, never asked |
| occurrences in the corpus | **one** (`beispiele/15`, a file that exists so the rights check gives no false red) |
| the release it was justified by | **does not exist in the grammar** |

> The old sentence here read *"whoever holds it may release — with that `Finalized` is
> expressible without lifetimes."* **The release is not writable in Gabbro**, so the sentence
> described a language that was planned and not one that is.

**The exclusivity the word stands for is not decidable at any single site without alias
analysis** — `m3.rs` says so itself (*"no alias analysis: two `ptr<normal, rw>` to the same
object stay indistinguishable"*). Two `own` parameters of the same carrier are **not** an
error: `own` asserts they are different objects, which is exactly the case that must stay
writable. *A rule that only looked like a check would be worse than none.*

**What `own` is good for as it stands:** it says in the signature what a `rw` does not — that
this handle is the owner — and it is the one right a future release rule can attach to. The
barrier follows from the **space**, not from the architecture.

---

## 4. Expressions — `expr`

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
arglist    = arg { "," arg } ;
(* «B7»: `arg` traegt eine MARKE, und damit ist `call` zugleich der Verbundkonstruktor:
   `P(a: 1, b: true)` stellt einen `type P = { a : u32, b : bool }` her.

   **Ein geschweiftes Verbundliteral gibt es nicht, und das ist eine Entscheidung.**
   `P { a: 1 }` waere die erste Ausdrucksform, die mit `{` weitergeht; an 76 Korpusstellen
   folgt ein `{` direkt auf einen Ausdruck (`if x {`, `match a {`, `traverse i over d {`,
   `retry … until p {`, `locks S {`). Rust loest das mit einem Kontextschalter -- und wer
   den falsch setzt, verliest die 76 Stellen, ohne dass ein Tor es meldet: sie parsen
   weiter, nur anders. **Ein stiller Verleser ist teurer als eine fehlende Form.**

   Der Preis der gewaehlten Form ist eine Klammer statt einer geschweiften; der Gewinn ist
   eine Grammatik, die ohne Kontext eindeutig bleibt. Die Marke ist ihrerseits eindeutig:
   ein Ausdruck kann nie mit `ident ":"` anfangen (Pfade trennen mit `::`, Orte mit `.`).

   M1 haelt die Marken gegen die Felderliste (`M106`) und verlangt sie am Verbund
   vollstaendig (`M107`) -- `deckt fs zs ⟷ map fst zs = fs`, bewiesen in
   `beweise/Verbund_Konstruktor.thy`. Entweder ALLE Argumente sind markiert oder keines
   (`P036`). *)
arg        = [ ident ":" ] expr ;
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

**M1 acts here and nowhere else:** every operation must stay within the range of its result type.
`a + b` with `a, b : u32 in 0..1000` has the type `u32 in 0..2000`; if that does not fit into the
target, it is a **compile error**, not a runtime check.

**Division and remainder demand a denominator whose range excludes zero.**
`%` and `/` by `u32 in 0..n` are not writable; by `u32 in 1..n` they are.

> **The limit of M1 is named and has been MEASURED since 2026-08-14.** `31 - x.leading_zeros()`
> needs a **flow-sensitive** inference. **But only one rule, not general inference:**
> *a checked condition narrows the range of the checked quantity in the branch after it.* Four
> sites in the whole tree, all the same turn of phrase. Where it does not get through, Gabbro demands a
> **narrowing** instead of a proof: `narrow x to 1..u32::max else { … }` — a statement with a
> named exit, not a proof line. **It counts as plumbing and must stay small; if
> it does not, that is a refutation** (see open items).

---

## 5. Predicates — `pred`. **Here lies the line**

```ebnf
pred       = orpred ;
orpred     = andpred { "||" andpred } ;
andpred    = notpred { "&&" notpred } ;
notpred    = [ "!" ] atompred [ "=>" pred ] ;
atompred   = cmpexpr | quant | member | reach | heldpred | "(" pred ")" ;
heldpred   = "Held" "(" ident [ "," "shared" ] ")" ;
             (* Der Sperrzeuge, mit seiner STAERKE. Bis 2026-08-15 war `Held(L)` ein
                gewoehnlicher Aufruf im Praedikat und trug keine Staerke -- damit war
                `requires Held-shared` nicht schreibbar, und die Zwischenregel `H005`
                musste JEDEN Zeugen sperren. Eine eigene Regel statt einer Aufweichung
                des Ausdrucks: `shared` ist ein Wort des Wortschatzes und soll es
                bleiben. *)
quant      = ( "forall" | "exists" ) ident "in" domain ":" pred ;
domain     = "slots" "of" place                  (* die Slots einer Tabelle *)
           | "chain" "(" ident "," ident ")" "in" place
           | "descendants" "of" place
           | "ancestors" "of" place        (* «B41»: dieselbe Kante, andere Richtung *)
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

**Eight domains, closed. Nesting at most two.** `old(place)` is permitted in `ensures`
and nowhere else.

> **That is the line, and here it is writable down for the first time.** There are **no
> user-defined quantifier domains, no recursion in `spec fn`, no hand-written
> lemmas**. Whoever needs more needs Verus or F\*.
>
> **The one exception, and it is NOT a lemma: `by induction over <domain>`.** It **names** the
> induction scheme that the compiler **generated** from the `table` declaration — no
> proof step, no proof body, no recursive `spec fn`. **The reason it is named and
> not guessed is predictability:** a compiler that chooses the scheme makes
> "it compiles" depend on solver luck — and M1 to M4 are types, not solvers.
> In full in [`SPRACHE.md`](SPRACHE.md).
>
> **The price is unquantified and probably the largest of the whole design:** there is no
> emergency exit. If a kernel property falls outside the seven domains, it is **not
> formulable** — not "expensive" but **not at all**.

---

## 6. Functions and contracts — E4

```ebnf
fndecl   = [ "pub" ] [ "spec" | "const" | "impl" | "raw" | "divergent" | "prim" | "extern" ]
           "fn" ident "(" [ params ] ")" [ "->" typeexpr ]
           [ "requires"  predlist ]
           [ "ensures"   predlist ]
           [ "maintains" identlist ]
           [ "advances"  ident "->" ident ]
           [ "effects"   "{" efflist "}" ]
           [ "costs"     "<=" expr "ops" ]
           [ "by"        inductlist ]
           [ "section" string ] [ "arch" ident ] [ "when" constexpr ]
           ( block | "=" pred ";" | ";" ) ;      (* "=" pred: nur fuer spec fn *)
(* `const fn` -- comptime, das WERTE rechnet, 2026-08-17. Die Linie, an der es haengt:

     comptime, das WERTE rechnet   ->  kostet keine Schablone
     comptime, das CODE  erzeugt   ->  kostet eine, und die will bewiesen werden

   Ein `const fn` erzeugt keinen Code; es liefert eine Zahl, und die steht dann in `count`,
   in `costs` oder in einer Bereichsgrenze:

     const fn zellen(kerne : u32 in 0 .. 256) -> u32 effects { pure } costs <= 4 ops
     { return kerne * 4; }
     table W count zellen(NKERNE) { … }

   **Der Rumpf ist EIN Ausdruck** -- `{ return <expr>; }`. Das ist keine Vorstufe, sondern
   die Entscheidung: ein `const fn` mit Verzweigung waere ein Auswerter im Pruefer, und ein
   Auswerter ist ein Erzeuger. Rekursion liefert `None` statt zu haengen -- dieselbe
   Schranke, die die Sprache ihren Schleifen auferlegt.

   `const` faengt damit zweierlei an; ein Blick auf das naechste Wort trennt sie
   (`const N : u32 = 4;` gegen `const fn f(…)`), und das ist KEIN Kontextschalter. *)

(* «B37»: `advances roh -> mmu` sagt, WELCHEN Schritt diese Funktion auf einer Marke mit
   `order` tut. Sie steht an der DEKLARATION, nicht am Rufer -- wer den Schritt macht, weiss,
   welcher es ist; wer ruft, soll es nicht wiederholen muessen. Zwischen `maintains` und
   `effects`, weil sie zu den ZUSAGEN gehoert: was der Schritt anfasst, sagt `effects`.

   Geprueft wird in drei Stufen: die Stufen gibt es und der Schritt geht VORWAERTS
   (`O001`/`O002` -- ohne die zweite Haelfte waere `order` eine Liste), die Marke steht beim
   Ruf auf der Ausgangsstufe (`O003`), und der Rumpf setzt sich zu seiner eigenen Zusage
   zusammen (`O004`), und alle Zweige erreichen dieselbe Stufe (`O006`, K11.1) -- ein Zweig,
   der mit `return` endet, schliesst sich nicht an; ein Schritt in einer Schleife wird
   abgelehnt. *)
inductlist = induct { "," induct } ;
induct     = "induction" "over" domain ;      (* nennt das SCHEMA -- kein Lemma, kein Beweisschritt *)
efflist  = eff { "," eff } ;
eff      = "reads" place | "writes" place | "locks" [ "shared" ] place | "masks" ident
         | "allocs" ident | "consumes" place | "publishes" place | "diverges"
         | "pure" ;
```

> **`effects` is NOT fail-open.** A function **without** `effects` is a compile error;
> whoever touches nothing writes `effects { pure }`. The omission that was formerly possible was at once
> **the strongest promise and the shortest specification** — the incentive stood against
> completeness.

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

**`breaking`** names the region in which an invariant rests — three sites in Caprock:

```ebnf
breakstmt = "breaking" identlist block ;
```

It must be restored at the end of the block; the region is **visible instead of hidden**.

---

## 7. Statements

```ebnf
block      = "{" { stmt } "}" ;
stmt       = letstmt | assign | ifstmt | matchstmt | loopform | breakstmt
           | narrowstmt | lockstmt | observestmt | leavestmt | nextstmt | publishstmt
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
           | "let" ident "=" ( call | place ) "else" "(" ident ")" block ;   (* «B14b» *)
assign     = place ( "=" | "+=" | "-=" | "&=" | "|=" ) expr ";" ;
exprstmt   = call ";" ;
ifstmt     = "if" expr block { "else" "if" expr block } [ "else" block ] ;
matchstmt  = "match" expr "{" { ident [ "(" ident ")" ] "=>" block } "}" ;
narrowstmt = "narrow" place "to" ( range | "finite" ) "else" block ;
(* «F»: `finite` stellt NICHT-NaN-SEIN her, und es ist die einzige Form dafuer.

   Ohne diese Tatsache liefert die Negation eines Gleitkommavergleichs nichts: ist ein
   Operand NaN, sind alle Vergleiche falsch, und aus `!(x < y)` folgt `x >= y` nicht. Mit
   ihr rechnet man gewoehnlich weiter -- die Verengungsmaschinerie ist damit BEDINGT statt
   abgeschaltet.

   Der Korpus zeigt dieselbe Bewegung von Hand (FRAGMENTE.md, «F0»/FF1): dort steht
   `isnan(de.x) || isinf(de.x) || …` neben dem Vergleich, weil der Vergleich allein den Fall
   nicht abdeckt. *)
```

**`match` is exhaustive** — there is no catch-all branch; a new variant breaks the
compilation. **Error propagation** is `let … else (e) { … }`: no hidden control flow,
the `else` branch must diverge or return.

---

## 8. Loops — **three forms, and infinite is one of them**

**The rule is not "every loop ends" but: what a loop may do stands beside it.**

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

| Form | ends? | what discharges the plumbing |
|---|---|---|
| **`traverse`** | yes, through the set | range **and** termination; `by consuming` additionally the leafness via the ordering of the domain |
| **`retry`** | yes, through `bounded` | termination as a **number**; the overrun is **named** (`on_exceeded`), not interpreted |
| **`forever`** | **no — and that is permitted** | every **pass** is bounded, the **frame** stands in `effects` |

```gabbro
forever
    per_pass bounded 4096 ops
    on_exceeded watchdog_schlug_an
    effects  { reads READY, writes CURRENT, locks SCHEDS }
    progress timer_tick_arrives
{ … }
```

> **That is the narrow frame.** An idle loop, the main loop of a server, a
> spinlock — they are meant to run forever. What is **not** permitted: a pass that is itself
> unbounded, or a loop that touches what does not stand in its frame.
> **`per_pass` and `effects` are compulsory; `forever` without them does not compile.**
>
> **`progress` names WHO ends it** — an assumption about the environment, with a falsifier. The
> watchdog **is** the falsifier. With that a wait loop is not "unprovable" but
> **provable under a named, falsifiable assumption**.

---

## 9. Tables, traversals, formats

```ebnf
table      = "table" ident [ "count" constexpr ] [ "backed" ident ] "{"
               { constdecl | slotdecl | invariant | opdecl } "}" ;
(* `count` ist der ADRESSRAUM, `backed` der SPEICHER (Punkt 1, 2026-08-18).

   `count N` sagt, wie viele Plaetze der Typ kennt; `backed k` nennt den WERT, bis zu dem
   sie hinterlegt sind. Ohne die Trennung fiel beides zusammen -- und dann ist "30 GiB
   deklarieren, 100 MiB hinterlegen" keine Aussage der Sprache, sondern eine Hoffnung an den
   Seitenfehlerpfad.

   **Das Tor ist keine neue Pruefung, sondern dieselbe gegen die richtige Zahl:** `M103`
   haelt jeden Index gegen die deklarierte Schranke, und mit `backed` ist das `k` statt `N`.
   Die Tatsache `i < k` kommt aus `narrow i to 0 ..< k` -- ein Vergleich zweier STELLEN, und
   den fuehrt M1 als `Fakt::Beziehung` seit jeher.

   Ein Schreiben auf `k` loescht jede Tatsache, die auf ihm ruht -- damit ist ein
   SCHRUMPFEN sicher, ohne dass eine Monotonieregel noetig waere. *Die Gefahr war nie das
   Wachsen.* *)
opdecl     = "ops" opname { "," opname } ";" ;
opname     = "insert" | "remove" | "relabel" ;
             (* «NL.1», decided 2026-08-19: the operation set is CLOSED, and the words are
                English like every other keyword.

                Until then `opdecl` took arbitrary identifiers, and that made
                `table.ops.erhaltung` unprovable in the only sense that matters: **from a name
                no effect follows.** A generator cannot emit `insert` if nothing says what
                `insert` does.

                MEASURED BEFORE DECIDED (second corpus, `kernel/` + `mm/`, 659 files):

                    remove     479 sites in 151 files
                    insert     448 in 161
                    (init)     408 in 132   -- construction, not mutation: `count N` does it
                    relabel    127 in  43
                    replace     11 in   7   -- marginal, folded into `relabel`

                Insert and remove carry 63 % of the sites. **`relabel` is the uncomfortable
                one:** it is re-parenting, and `Table_Ops_Erhaltung.thy` proves the
                COUNTEREXAMPLE for it (`umhaengen_faellt` — hang one node under the other and
                *neither* reaches a root any more). Leaving it out would leave 127 measured
                sites as hand work; taking it in means the generator owes a condition the
                other two do not.

                **It is taken in, and the condition comes with it** — that is the decision:
                a language that only covers the easy operations moves the work, it does not
                remove it. *`init` is deliberately NOT a word: `table … count N` constructs,
                and `table.absenkung` proves it.* *)
walkdecl   = "walk" ident "levels" constexpr "{"
               "node" ":" array ","
               "down" ":" ident "when" pred ","
               "leaf" ":" pred ","
               { invariant }
             "}" ;
slotdecl   = "slot" "{" [ slotfeld { "," slotfeld } [ "," ] ] "}" ;
slotfeld   = ident ":" slottype [ "by" "ops" ] ;
             (* `by ops`: dieses Feld schreiben NUR die erzeugten Operationen der Tabelle.
                Zwei vorhandene Woerter, null Wortschatzzuwachs. Damit wird die K-Bedingung
                des Messprotokolls -- *„gilt nur, wenn ALLE Mutationen des Traegers erzeugte
                Operationen sind"* -- von einer PRUEFVORSCHRIFT zu einer
                GRAMMATIKEIGENSCHAFT, und `refcount -= 1` von Hand ist schlicht nicht
                schreibbar. *)
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

**Variable lengths and offsets** — with them ELF is a `format`:

```gabbro
format Elf64 endian little {
    e_phoff     : u64 offset_into Self where e_phoff + e_phentsize * e_phnum <= lenof(Self),
    e_phentsize : u16 in 56 .. 56,
    e_phnum     : u16 in 0 .. 65535,
}
```

`offset_into Self` binds the offset to the buffer length; the `where` clause is the **only**
additional statement and lowers to a range check.

**`reason`** is rule 3 in notation, **`state`** names the permitted transitions of a value:

```ebnf
reason  = "reason" ident "{" { ident "=" int string } [ "exhaustive" ] "}" ;
state   = "state" ident "{" { transition } "}" ;
```

`state` and `device`'s `transition` are **the same construct on two levels**: once over
fields, once over register bits. `resume` (`iretq`/`eret`) is the transition on the third —
over the machine state.

---

## 10. Devices — and trap 4

```ebnf
device  = "device" ident [ "(" params ")" ] "at" space
          "{" [ mirrors ] { regdecl | bank | transition } "}" ;
mirrors = "mirrors" place "from" place ";" ;       (* EINMAL je Geraet, nicht je Uebergang *)
bank    = "bank" ident "at" expr "stride" expr "count" expr "{" { regdecl } "}" ;
regdecl = "reg" ident ":" intty [ "wrapping" ] "@" expr
          (* «B32», 2026-08-15: `slottype = intty "wrapping"` konnte den gewollten Umlauf
             aussprechen, `regdecl` nicht -- und der HAEUFIGSTE Fall eines Treibers ist ein
             Hardwarezaehler, der per Entwurf umlaeuft (virtios `AVAIL_IDX` zaehlt modulo
             2^16 und nimmt den Rest gegen `q.n`). Ohne das Wort stand die Absicht nirgends,
             und die Zaehlerregel faellt zu Recht -- am falschen Programm. Gemessen am
             Fragmentkorpus, nicht entworfen. *)
          "class" ( "r" | "w" | "rw" | "w1c" | "rc" )
          [ "fields" "{" [ regfeld { "," regfeld } [ "," ] ] "}" ]
regfeld = ident "@" bitpos ;
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

> **`mirrors` kills trap 4, and `class w` alone did not.** The trap is not "reading GCMD"
> but **"not carrying the state bits along when writing"**. `mirrors` names the bits that
> the written word must **carry along**; their source is a readable register. A `store`
> that drops them is thereby **not writable** — and a read of `GCMD` remains
> untypeable.
>
> *(Until 2026-08-17 this paragraph said `keeping` three times. The word was renamed to
> `mirrors`; the production above has carried the new name for a while, the prose carried the old
> one — and the file's own writing rule says that backticks denote **today's** syntax. A name in
> backticks that no grammar knows is the same false green as a table word in no production.)*
>
> **`bank`** covers registers at a run-time-computed base (F6): `FRR` at `CAP.FRO*16`. The index
> is M1-bounded by `count`.

---

## 11. Concurrency

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
rcudecl    = "rcu" ident "protects" "{" placelist "}" [ "reclaims" place ] ";" ;
observestmt = "observes" ident block ;
(* RCU, und es ist KEINE Sperre (2026-08-18, aus «K2»).

   Die Leseseite nimmt gar nichts: `observes D { … }` ist ein BEREICH, in dem ein gelesener
   Zeiger gueltig bleibt -- kein Ausschluss. Die Schreibseite braucht ihre eigene
   Wechselseitigkeit, denn RCU serialisiert Leser gegen die Rueckgewinnung und nicht
   Schreiber gegeneinander.

   Daraus zwei Regeln, und beide spiegeln `protects`/`H007`:

     H009  ein LESEN einer rcu-geschuetzten Stelle steht in `observes`
     H010  ein SCHREIBEN steht zusaetzlich unter einer echten Sperre

   `reclaims` nennt den Ort, an dem ein Platz zurueckgegeben wird -- den Kopf der Freiliste.
   Daran haengen zwei weitere Regeln:

     H011  eine Rueckgabe steht NICHT in `observes` -- wer zurueckgibt, ist nicht Leser
     H012  eine Rueckgabe steht unter der Schreibersperre

   Und die GNADENFRIST selbst ist keine Pruefung, sondern eine ANNAHME: dass kein Leser das
   alte Objekt mehr sehen kann, ist eine Aussage ueber die Umgebung -- kein statischer Pass
   stellt sie her. Sie gehoert damit dorthin, wo `progress` steht: in die Annahmenschicht,
   mit Falsifikator. *`progress` nennt, wer eine Schleife beendet; die Gnadenfrist nennt, wer
   garantiert, dass kein Leser mehr drin ist.* *)
gruppedecl = "group" ident "over" "{" ident { "," ident } [ "," ] "}"
             ( "{" { invariant } "}" | ";" ) ;
```

```gabbro
lock CAPS protects { plaetze, cdt } rank 2 masks irqs;
atomic COLOR_DONE : bool publishes { color_report } release;
group Zustellung over { Endpunkte, Faeden } {
    invariant wartende_haben_grund cost O(n) runs offline :
        forall e in slots of Endpunkte :
            Faeden.slots[Endpunkte.slots[e].wartet].gruende > 0;
}
```

**`group` carries the invariant that lives between two carriers** — *"the counter in A
corresponds to the number of references in B"*. No `table … invariant` can say that; it
quantifies only over its own carrier.

**The lock order does NOT stand at the group.** Every carrier lies under a
`lock … rank N`, and the ranks give the order — a second declaration would be a
second truth about the same thing. What the checker makes of it: `U003` demands that
a function that writes **two** carriers of a group holds **all** their locks, and
`U005` falls if two locks of a group carry the same rank — then there is no
order, and the group operation could take them in two directions. `U006` falls if
a path leaves the body **between** the first and the last write access
(`return`, `leave`, `let … else`) — there the invariant does not hold.

**The body is optional, the invariant is not meaningless.** Without a body the lock imprint
and the move bite; only with it does the connection statement itself stand there. **`U007` falls
if a group invariant names fewer than two carriers of the group** — then it belongs
at the `table … invariant`, and the group would be merely the more convenient notation. *A
construct that is only more convenient has no evidence (W3).*

*The measured need stands in `MESSUNGEN.md`, SWEEP der Verbindungs-Invarianten: four in the
existing code, three under one lock, one (V4) over two crates with two lock classes.*

**`publishes` is compulsory at every atomic** — the payload is part of the model, not of the
comment. **`rank`** gives the lock order; acquiring demands a strictly smaller rank. A `locks` block
releases at the end; whoever wants copy-and-release does it **inside** and acquires afresh afterwards.

---

## 12. Hardware assumptions and axioms — **load-bearing, not trimming**

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

**Three classes, and the third does not exist syntactically:** *falsified* (probe ran and held),
*not falsifiable* (**with a reason as a string**), *not run* — that is the
**absence of both statements** and a **compile error**. An assumption that has not been run must
never look like a falsified one.

**The assumption set is emitted into the artefact** ("proved under A1…An"), as a **set of names
with a class**, not as a number — a ratchet over a cardinal number does not bite against exchange.

> **With that the promise is relative, and that stands in the artefact instead of in a footnote:**
> *memory-safe under A1…An.* A proof whose assumption set the consumer does not know has
> no reach. **The axiom layer is the largest unproved surface of the language** — larger
> than the compiler — and therefore countable and ratchetable.

---

## 13. `check` — the linear checking obligation

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

The compiler generates a `linear ghost Duty(ident)`. **Four compile errors fall out of
M1/M2/M3, not out of special rules:** `gates` missing → the obligation is never consumed;
`can_fail` missing → likewise; a quantity under `measures` that the **measured path** writes →
write right; a one-sided threshold without `floor` → the quantity has no range.

**The `measures` list IS the report line** — the formatting arises out of it, without
formatting existing in the language core.

---

## 14. Boot phase, machine state, assembler

```gabbro
raw fn phys_write(p: Pa, w: u64) requires BootPhase effects { writes phys };
fn boot_end(t: BootPhase) effects { consumes t, writes code_map };

prim fn switch_to(von: ptr<normal,rw> Context, zu: ptr<normal,r> Context) -> never
    effects { writes kontext };
prim fn resume(k: ptr<normal,r> Context) -> never effects { reads k };
divergent fn idle() effects { diverges };
```

`boot_end` consumes the **linear** token **and** unmaps `code<boot>` — an event. A
probe there must fault afterwards; that is the falsifier.

---

## What deliberately does not exist

`while` · `for` · `goto` · `union` as reinterpretation · preprocessor · implicit conversion · `void*` ·
pointer arithmetic without a basis · catch-all branch · exceptions · inheritance · reflection · GC ·
floating point in the core · assignment as an expression · forward declaration · self-hosting ·
user-defined quantifier domains · recursion in `spec fn` · hand-written lemmas ·
**the braced compound literal**.

### The last one is the youngest, and it is the one with a price — «B7», 2026-08-17

`P { a: 1, b: true }` does not exist. A record value is made by a **labelled call**:
`P(a: 1, b: true)`.

> **It would have been the first expression form in Gabbro that continues with `{`.** At
> **76** sites of the corpus a `{` follows an expression directly — `if x {`, `match a {`,
> `traverse i over d {`, `retry … until p {`, `locks S {`. Until now that was unambiguous
> for exactly one reason: no expression ever went on with a brace.

Rust resolves this with a context flag (*"no struct literal here"*). Gabbro has none, and
whoever sets one wrongly **misreads all 76 sites without a single gate firing** — they keep
parsing, only differently. *A silent misparse is dearer than a missing form.*

What is given up: one character. What is kept: a grammar that stays unambiguous **without
knowing where it stands**. And the mechanism was already there — the parameter list of a
`device` declaration is its constructor (`Vtd(basis)`); the field list of a `type` is the
same thing, said about fields.

**Labels are mandatory at a record and forbidden elsewhere** (`M107`), and they must be the
field list in declaration order (`M106`). That is not politeness: two same-typed fields in a
positional list are swappable **without any type objecting**, and the name is the only thing
that tells them apart. The rule is `deckt fs zs ⟷ map fst zs = fs`, machine-checked in
[`beweise/Verbund_Konstruktor.thy`](../beweise/Verbund_Konstruktor.thy).

Writing the braced form is refused by name (`P037`), not by a follow-on error — the refusal
carries the reason, because *a form that deliberately does not exist deserves its ground and
not the silence of one nobody thought about.*

---

## Open items — as of 2026-08-14, after the definition

**The nine design questions are decided in [`SPRACHE.md`](SPRACHE.md) §18 (F1–F9).**
What stands here is what is **still open** after that — and those are measurements, not designs.

### The one measurement the definition hangs on

- [ ] **Repeat the 74-obligation measurement against this version: hanging plumbing 19 → 0.**
      That is the **acceptance** of the definition, not agreement with it. If one stays hanging, it is
      refuted at that point — with a class and a source reference.

### Four marks, all set in advance

- [ ] **`narrow` count on the tree: ≤ 24 sites.** If they grow beyond that, the rule set
      V1–V3 is too small — **and *that* is the refutation, not a further growth of rules in silence.**
- [ ] **How many of the 17 measured logic obligations need `by induction over`**, how many manage
      without, **how many would need a recursive `spec fn` or lemmas**? A single case in the
      last column sets the ceiling lower.
- [ ] **Cost truth per compiled module** (definition §14.2): generated C against
      hand-written in the differential benchmark.
- [ ] **Pull the ten fragments onto this syntax**, guardians green. All ten now lie in
      [`FRAGMENTE.md`](FRAGMENTE.md) (F1–F10, gate P2 at 10 of 10 since 2026-08-16); the first six
      are written against the **second** version. *(Until 2026-08-17 this line said "six lie in
      FRAGMENTE.md" — F7–F10 were written on 2026-08-16 and the line was not pulled up.)*

### What is not covered even after the definition — named, not forgotten

- [ ] **The seam CPU ↔ device** has no mechanised model to follow ([`BEWEIS.md`](BEWEIS.md)).
- [ ] **The `iasm` entry path has no downstream prover** — the trust shrinks from
      161 sites to one site, it does not disappear.
- [ ] **Liveness and progress** falls under no mechanism.
- [ ] **The ghost-theory templates are the most trust-critical surface** and belong in
      Isabelle once ([`BEWEIS.md`](BEWEIS.md), level 1).
