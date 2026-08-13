# Gabbro — die Syntax

**Diese Datei ist die Quelle für die Oberfläche.** [`SPRACHE.md`](SPRACHE.md) sagt, *welche
Mechanismen* es gibt und warum; hier steht, *wie man sie hinschreibt*. Was hier nicht steht, ist
nicht schreibbar.

Stand 2026-08-13. **Kein Übersetzer liest das.** Die Grammatik ist ein Entwurf, und die offenen
Punkte stehen am Ende benannt statt weggelassen.

---

## Fünf Entscheidungen, die alles andere festlegen

| | Entscheidung | Grund |
|---|---|---|
| **E1** | **Englische Schlüsselwörter, deutscher Fliesstext, freie Bezeichner** | genau Caprocks eigene Praxis. Vorher standen beide Sprachen gemischt in den Beispielen — *„wirkung“* neben `touches`. Der Wortschatz ist eine **geschlossene Tabelle** (unten), ein Tausch kostet den Lexer und sonst nichts |
| **E2** | **Anweisungsorientiert, geschweifte Klammern, Zuweisung ist KEIN Ausdruck** | `if (x = y)` ist nicht schreibbar. Vorhersagbare Absenkung nach C verlangt, dass Auswertungsreihenfolge sichtbar ist |
| **E3** | **Nichts ist implizit** — keine Umwandlung, keine Kopie eines linearen Werts, kein Auffangzweig, kein Standardwert | jede der vier Klassen hat eine bezahlte Falle in `fallen-klassifikation.tsv` |
| **E4** | **Verträge stehen VOR dem Rumpf, in fester Reihenfolge**: `requires` · `ensures` · `maintains` · `effects` · `costs` | eine feste Reihenfolge macht Fehlen sichtbar. Ein Werkzeug, das sortieren muss, kann nicht sagen „hier fehlt `effects`" |
| **E5** | **Jede Deklaration ist an genau einer Stelle vollständig.** Keine Vorwärtsdeklaration, kein Präprozessor, kein `include` | „zwei Zahlen aus derselben Hand sind keine zwei Quellen" |

---

## Wortschatz — die geschlossene Tabelle

**Alles andere ist ein Bezeichner.** Ein neues Schlüsselwort ist eine Sprachänderung und braucht
einen Eintrag hier.

```
  Struktur   module pub use type opaque linear ghost const fn spec impl raw
             divergent prim section arch
  Verträge   requires ensures maintains effects costs where in exhaustive
  Wirkungen  reads writes locks masks allocs diverges
  Ablauf     if else match loop variant traverse over by touches return
  Werte      let mut true false
  Zeiger     ptr normal mmio dma code boot r w rw x
  Bibliothek format table slot invariant reason state transition device reg
             class fields assume falsifier axiom check claim measures gates
             can_fail floor counterprobe endian reserved cost runs
             index into option chain wrapping unfalsifiable
  Eingebaut  sizeof forall exists never bool Self
```

---

> **Schreibregel fuer diese Dateien, und sie ist keine Kosmetik:** `Backticks` bezeichnen
> **heutige Gabbro-Syntax**. Ein abgeschaffter Name steht *kursiv in Anfuehrungszeichen* -- er **ist**
> keine Syntax mehr. Der Waechter prueft genau das; ohne die Regel braeuchte er eine Ausnahmeliste,
> und die waechst still.

---

## Lexik

```ebnf
ident     = (letter | "_") { letter | digit | "_" } ;      (* Umlaute erlaubt *)
letter    = "a".."z" | "A".."Z" | "ä" | "ö" | "ü" | "Ä" | "Ö" | "Ü" | "ß" ;
int       = dec | hex | bin ;
dec       = digit { digit | "_" } ;
hex       = "0x" hexdigit { hexdigit | "_" } ;
bin       = "0b" ("0"|"1") { "0" | "1" | "_" } ;
string    = '"' { char } '"' ;                              (* nur in Verträgen und Absagen *)
comment   = "--" { char } newline ;                         (* nur Zeilenkommentar *)
```

**Kein Gleitkomma im Kern**, keine Zeichenketten-Arithmetik, keine Formatierung im Sprachkern —
Berichtstexte sind `string`-Literale in `check` und `reason`, sonst nirgends.

---

> **Ein Wort ist beim Aufschreiben WEGGEFALLEN.** Der Entwurf führte `decrement x requires x > 0`
> als eigenes Konstrukt für die Arithmetik-Vorbedingung. Mit M1 ist es überflüssig: `Refcount` hat
> einen Bereich, `-= 1` unter 0 verlässt ihn und ist **nicht typisierbar**. Ein Schlüsselwort für
> etwas, das der Typ schon kann, ist Ballast — **das ist der Ertrag davon, eine Grammatik
> hinzuschreiben statt Konstrukte aufzuzählen.**

---

## 1. Typen — M1 und D1

```ebnf
typedecl  = [ "pub" ] [ "opaque" ] [ "linear" [ "ghost" ] ] "type" ident
            [ "(" ident ")" ]                  (* Parameter, z. B. Held(CAPS) *)
            [ "=" typeexpr ] ";" ;

typeexpr  = intty | ident | array | ptrty | structty | fnptr ;
intty     = ("u8"|"u16"|"u32"|"u64"|"i8"|"i16"|"i32"|"i64") [ "in" range ] ;
range     = expr ".." expr | expr "..<" expr ;
array     = "[" typeexpr ";" expr "]" ;
structty  = "{" { ident ":" typeexpr [ "@" expr ] "," } "}" ;   (* @ = Bitlage/Versatz *)
fnptr     = "fn" "(" [ typelist ] ")" [ "->" typeexpr ] ;
```

```gabbro
opaque type Pa   = u64;            -- D1: keine implizite Umwandlung nach Iova
opaque type Iova = u64;
opaque type Colors = u16;          -- MASK_BITS ist KEINE Farbanzahl

type SlotIdx  = u32 in 0 ..< NSLOTS;      -- M1: jede Operation bleibt im Bereich
type Refcount = u32 in 0 .. 0xFFFF_FFFF;
type Cycles   = u64 in 1 .. u64::max;     -- Null ist ein Befund, kein Messwert

linear type Parked;                        -- muss verbraucht werden
linear ghost type Held(CAPS);              -- Sperrbeleg, kostenlos
linear ghost type BootPhase;               -- genau eine Instanz
linear ghost type Duty(check);             -- eine unerfuellte Pruefzusage
```

> **`opaque` ohne `=` ist ein Typ ohne Darstellung** — nur als Wert weiterreichbar. Das ist die
> Form für `Parked`: kein öffentlicher Weg an die `ThreadId`.

---

## 2. Zeiger — M3

```ebnf
ptrty  = "ptr" "<" space "," rights ">" typeexpr ;
space  = "normal" | "mmio" | "dma" | "code" | "boot" | ident ;
rights = "r" | "w" | "rw" | "x" | rights "@" ident ;     (* @ring3 usw. *)
```

```gabbro
let gcmd : ptr<mmio, w>  u32   = ...;    -- Lesen ist NICHT typisierbar (Falle 4)
let buf  : ptr<dma,  rw> [u8; 4096] = ...;
fn probe() section ".user_text" arch x86_64 { ... }   -- Falle 72
```

**Barrieren gehören zum Raum, nicht zur Architektur:** ein Schreibzugriff auf `mmio` zieht die
Barriere des Raums; `normal` zieht die schwächere. `dmb ish` gegen `dsb sy` ist damit keine
Stilfrage mehr (Falle 8).

---

## 3. Funktionen und Verträge — E4

```ebnf
fndecl   = [ "pub" ] [ "spec" | "impl" | "raw" | "divergent" | "prim" ]
           "fn" ident "(" [ params ] ")" [ "->" typeexpr ]
           [ "requires"  predlist ]
           [ "ensures"   predlist ]
           [ "maintains" identlist ]        (* Invarianten, die erhalten bleiben *)
           [ "effects"   "{" efflist "}" ]
           [ "costs"     "<=" expr unit ]
           [ "section" string ] [ "arch" ident ]
           ( block | ";" ) ;

efflist  = eff { "," eff } ;
eff      = "reads" path | "writes" path | "locks" ident | "masks" ident
         | "allocs" ident | "diverges" ;
```

```gabbro
fn delete_leaf(c: ptr<normal, rw> CapSpace, s: SlotIdx) -> Result
    requires  held(CAPS), c.slots[s].used
    ensures   !c.slots[s].used
    maintains cdt_wellformed, refcount_matches
    effects   { writes c.slots, writes c.objects, locks CAPS }
    costs     <= 200 cycles
{ ... }
```

**`effects` ist Pflicht, wenn eine Funktion irgendetwas anfasst.** Voreinstellung ist die leere
Menge — eine Funktion ohne `effects` ist rein.

### `spec` und `impl` — der Gold-Mechanismus

```gabbro
spec fn cdt_wellformed(c: CapSpace) -> bool =
    forall s in c.slots: c.parent_chain(s) ends_at Root;

impl fn delete_leaf(...) maintains cdt_wellformed { ... }
```

`spec fn` ist **nicht ausführbar**, hat keine `effects`, keine Kosten und keine Bereichsgrenzen —
sie ist Mathematik. `impl fn` trägt die **erzeugte** Verfeinerungspflicht gegen sie.

---

## 4. Ablauf — M4

```ebnf
stmt      = letstmt | assign | ifstmt | matchstmt | traverse | loopstmt
          | "return" [ expr ] ";" | exprstmt ;
letstmt   = "let" [ "mut" ] ident [ ":" typeexpr ] "=" expr ";" ;
assign    = place "=" expr ";" ;                  (* E2: kein Ausdruck *)
traverse  = "traverse" ident [ "of" expr ]
            "over"  setexpr
            "by"    measure
            [ "touches" efflist ]
            block ;
setexpr   = ident | "chain" "(" ident "," ident ")" "in" ident | range ;
measure   = "unvisited" | "decreasing" expr ;
loopstmt  = "loop" block "variant" expr ;         (* die BENANNTE Ausnahme *)
```

```gabbro
traverse siblings of p
    over    chain(first_child, next_sibling) in slots
    by      unvisited                 -- toetet Zyklen, nicht nur Nichtterminierung
    touches reads slots
{
    if it == s { return Found; }
}
```

**`it` ist das Laufelement und ein Element von `over`** — keine Zahl. Ein Index ausserhalb der
Menge ist damit nicht formulierbar (S1a). **Es gibt kein `while`, kein `for`, kein `goto`.**

---

## 5. Die Bibliotheksschicht

```ebnf
format  = "format" ident [ "@version" int ] [ "endian" ("little"|"big") ] "{" field* "}" ;
field   = ident ":" typeexpr [ "where" pred ] [ "in" "{" variants "}" ] [ "reserved" ] ;

table   = "table" ident "{" { constdecl | slotdecl | invariant } "}" ;
invariant = "invariant" ident "cost" bigO "runs" ("online"|"offline") ":" pred ;

reason  = "reason" ident "{" { ident "=" int string } [ "exhaustive" ] "}" ;

state   = "state" ident "{" { transition } "}" ;
transition = "transition" ident "{" place ":" expr "->" expr "}"
             [ "requires" pred ] [ "effects" "{" efflist "}" ] ;

device  = "device" ident "at" space "{" { regdecl | transition } "}" ;
regdecl = "reg" ident ":" intty "@" expr
          "class" ("r"|"w"|"rw"|"w1c"|"rc")
          [ "fields" "{" { ident "@" int "," } "}" ]
          [ "requires" pred ] ;
```

```gabbro
device Vtd at mmio {
    reg GCMD : u32 @0x18 class w  fields { TE @31, SRTP @30, IRE @25 }
    reg GSTS : u32 @0x1c class r
    transition arm_te { GCMD.TE: 0 -> 1 } requires GSTS.RTPS == 1
}
device Smmu at mmio {
    reg STE_S1STALLD : u32 @0x00 class rw requires IDR0.STALL_MODEL == 0b10
}
```

---

## 6. Annahmen und Axiome

```ebnf
assume = "assume" ident string [ "falsifier" ident | "unfalsifiable" string ] ";" ;
axiom  = "axiom" ident "(" [ params ] ")" "effects" "{" efflist "}"
         [ "falsifier" ident | "unfalsifiable" string ] ";" ;
```

```gabbro
assume vtd_te_effective
    "GCMD.TE schaltet die Uebersetzung scharf; DMA ohne Kontexteintrag faultet."
    falsifier probe_vtd_te;

axiom write_cr3(p: Pa) effects { writes tlb, writes active_table } falsifier probe_cr3;
```

**`unfalsifiable` verlangt einen Grund als Zeichenkette** — die dritte Klasse („nicht gefahren")
gibt es syntaktisch nicht: sie ist die **Abwesenheit** beider Angaben und ein Übersetzungsfehler.

---

## 7. `check` — die lineare Prüfpflicht

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

```gabbro
check epfull {
    claim        "ein Ueberlauf der Endpoint-Warteschlange ist BENANNT"
    measures     ep.rejected_send, ep.rejected_recv
    gates        acceptance
    can_fail     { five_probes_against_four_slots(); }
    floor        ep.rejected_send >= 1
    counterprobe "TidQueue::enqueue ignoriert die Kapazitaet"
                 expects exactly_one_conjunct_open
}
```

Der Übersetzer erzeugt daraus ein `linear ghost Duty(epfull)`. **Vier Übersetzungsfehler fallen
daraus, nicht aus Sonderregeln:**

| Fehler | Grund |
|---|---|
| `gates` fehlt oder nennt keine erreichte Liste | die `Duty` wird nie verbraucht — M2 |
| `can_fail` fehlt | dito, zweite Pflicht |
| eine Grösse unter `measures` wird vom **gemessenen Pfad** geschrieben | Schreibrecht — M3 |
| einseitige Schwelle ohne `floor` | die gemessene Grösse hat keinen Bereich — M1 |

---

## 8. Bootphase, Maschinenzustand, Module

```gabbro
raw fn phys_write(p: Pa, w: u64) requires &BootPhase effects { writes phys };
fn boot_end(t: BootPhase) effects { drops code<boot> };

prim fn switch_to(from: ptr<normal,rw> Context, to: ptr<normal,r> Context) -> never;
prim fn resume(k: ptr<normal,r> Context) -> never;   -- iretq / eret
divergent fn idle_loop() effects { diverges };

module kernel::caps {
    pub use crate::addr::Pa;
    pub fn resolve(...) -> ... { }
}
```

**`raw`** ist das einzige Wort, hinter dem M1/M3/M4 nicht gelten — und es ist **nur** mit einem
geliehenen `BootPhase` aufrufbar.

---

## Was es ABSICHTLICH nicht gibt

`while` · `for` · `goto` · `union` als Umdeutung (das kann `ptr<space>`) · Präprozessor · implizite
Umwandlung · `void*` · Zeigerarithmetik ohne Grundlage · Auffangzweig (`_ =>`) · Ausnahmen ·
Vererbung · Reflexion · GC · Gleitkomma im Kern · Zuweisung als Ausdruck · Vorwärtsdeklaration ·
Selbst-Hosting.

---

## Der Wächter — `./pruefe-syntax.sh`

Er hält **alle** Beispiele in `SPRACHE.md`, `SYNTAX.md`, `PLAN.md` und `README.md` gegen zwei Listen:
die absichtlich fehlenden Formen und die **alte deutsche Schlüsselwortsprache**. Zwei Oberflächen
sind ein Riss, und der entsteht beim nächsten Beispiel von selbst.

**Sprechprobe in beide Richtungen:** vier Gifte müssen fallen, ein sauberer Block muss durchkommen.

> **Beim ersten Lauf hat er zwei echte Fehler gefunden** — ein *„erhaelt“* aus der Zeit vor E1, das
> das Gegenlesen übersehen hatte, und ein Sprachprimitiv, das `switch` hiess, also **wie ein
> ausdrücklich verbotenes Wort**. Dazu einen Fehlalarm auf einem Kommentar, der die verbotene Form
> erklärt; seither streicht der Wächter Kommentare, bevor er prüft.

---

## Offene Syntaxfragen — benannt, nicht weggelassen

- [ ] **Variable Längen in `format`.** Die harten 20 % jedes Parser-Erzeugers; die Totalitätsregel
      deckt sie im Prinzip (eine vorher gelesene, geprüfte Länge), **eine Schreibweise gibt es
      nicht**.
- [ ] **Versionsevolution.** `@version 3` — liest der Leser auch v2? **Absage oder Migration?**
- [ ] **Generizität.** Ohne sie braucht jede Tabelle ihren eigenen `traverse`. Mit ihr:
      monomorphisieren, aber wie werden Verträge parametrisiert?
- [ ] **Die Schreibweise der Sperrordnung.** `locks CAPS` nennt die Sperre, nicht die **Stufe** —
      die Ordnung ist im Entwurf ein Bereichstyp, in der Syntax fehlt sie.
- [ ] **`spec fn`-Sprache.** `forall … in … :` ist hier gesetzt, aber der Vorrat an Quantoren und
      mathematischen Funktionen ist unentschieden — **und genau dort wandert die Linie**, wenn man
      nicht aufpasst.
- [ ] **Fehlerfortpflanzung.** `Result` steht in den Beispielen, ein `?`-Operator ist nicht
      entschieden. Ohne ihn wird jeder Aufruf drei Zeilen; mit ihm gibt es verborgenen Kontrollfluss.
- [ ] **Schlüsselwortsprache.** E1 setzt Englisch, weil das der Bestand ist (`traverse`, `over`,
      `by`, `touches`, `format`, `table`, `state`, `check`, `assume`). Der Preis ist der Bruch mit
      dem deutschen Fliesstext. **Reversibel: eine Tabelle im Lexer.**
