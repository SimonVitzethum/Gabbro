# FESTLEGUNG — Gabbro, vollständig

**Dritte Fassung der Oberfläche, erste vollständige Festlegung.** Dieses Dokument legt Syntax und
die tragenden Teile dahinter (Typregeln, Beweisarchitektur, C-Absenkung) so fest, dass ein Kernel,
Treiber und Programme — namentlich Caprock — **vollständig** in Gabbro schreibbar sind. Es
**entscheidet** die neun offenen Entwurfsfragen aus `SYNTAX.md` und nimmt die **19 hängenden
Klempnerei-Pflichten in 11 Klassen** aus `LOGIK-KLEMPNEREI.md` je mit einem Konstrukt ab.

> **EINGETRAGEN 2026-08-14.** Die Grammatik in [`SYNTAX.md`](SYNTAX.md) ist auf diese Festlegung
> nachgezogen — **112 Regeln, 0 offen, jede von `program` aus erreichbar, 170 Terminale gegen 170
> Wortschatzwörter**, Wächter grün. **Eine Korrektur beim Eintragen:** `obligation` war als
> dreizehntes Wort gezählt, ist aber **kein Quellwort** — es steht im Manifest, also im Erzeugnis.
> Zwölf.

Stand 2026-08-14. **Kein Übersetzer liest das.** Abnahme dieses Dokuments ist nicht Zustimmung,
sondern die **Wiederholung der 74-Pflichten-Messung** gegen diese Fassung: hängende Klempnerei
muss von 19 auf 0 fallen, sonst ist die Festlegung an den verbleibenden Stellen widerlegt.

---

## 0. Die Zusage — und die Nichtzusage

**Gabbro beweist alles außer Logik.**

| | wer | wie |
|---|---|---|
| **Klempnerei** — Index, Überlauf, Alias, Rahmen, Sperre, Rennen, Terminierung, Phase, Blattheit, Publikation | **Gabbro selbst** | Typregeln M1–M4 und erzeugte Schemata. **Kein SMT, kein Löser, keine Heuristik** — „übersetzt es" ist eine Funktion der Quelle, nicht des Löserglücks |
| **Logik** — *diese* Funktion tut *das Richtige* (`ensures` jenseits der Konstruktion) | **der Programmierer**, in jeder Sprache | Gabbro **emittiert** jede offene Logik-Pflicht in ein maschinenlesbares **Pflichtenmanifest** (§15). Nichts geht stillschweigend verloren |
| **Klempnerei, getragen von Logik** (dritte Klasse, §8.3) | gemischt | fällt durch Konstruktion, **wird aber als Logik gebucht**, weil ihre Grundlage eine Logik-Invariante ist |

Die Zusage ist **relativ**: *speichersicher unter A1…An* — die Annahmenmenge (Axiomschicht §12)
steht **im Erzeugnis**, nicht in einer Fußnote. Der Prüfer ist **unverifiziert**; das Vertrauen
sitzt an drei benannten Stellen: Prüfer, syntaxgesteuerte Absenkung, eine `iasm`-Emissionsstelle.

---

## 1. Grundsatz

Gabbro ist **C ohne seine Löcher, plus zwei Dinge**: Bereichstypen (M1) und lineare Werte, auch
geisterhafte (M2). Dazu Adressräume und Rechte am Zeiger (M3), kein ungeprüftes Indizieren und
keine unbeschriebene Schleife (M4), undurchsichtige Neutypen ohne implizite Umwandlung (D1),
vollständige Layouts ohne Auffangzweig (D2). Alles Weitere ist **Einschränkung** von C, nicht
Erweiterung.

Die fünf Entscheidungen **E1–E5** gelten unverändert: englische Schlüsselwörter bei deutschem
Fließtext; anweisungsorientiert, Zuweisung ist kein Ausdruck; nichts ist implizit; Verträge vor dem
Rumpf in fester Reihenfolge; jede Deklaration an genau einer Stelle vollständig.

---

## 2. Lexik und Wortschatz

Lexik unverändert (Bezeichner, Zahlen mit `_`, `--`-Kommentare, kein Gleitkomma im Kern,
Zeichenketten nur in `claim`, `reason`, `assume`, `section`, `unfalsifiable`).

**Der Wortschatz ist geschlossen. Diese Festlegung fügt genau zwölf Quellwörter hinzu** — jedes an
einer Pflicht aus der Messung, keines aus Vorrat:

```
  embeds scale aligned          -- §5.3: PTE ist Zeiger UND Bitfeld (Wurzelproblem)
  walk levels leaf mappings     -- §5.4/§6: Seitentabellen und die achte Domäne
  held                          -- §11.2: Sperrhaltezeit als Zahl (repariert per_pass)
  next                          -- §8: continue; leave gab es schon
  accumulates merge             -- §11.4: Sammelwerte ohne CAS-Schleife
  -- obligation                 -- §15: KEIN Quellwort, es steht im MANIFEST (Erzeugnis)
  extern                        -- §14.4: C-Randfunktionen mit Vertrag
```

Gestrichen wird **nichts**; jedes Wort der zweiten Fassung behält seine Bedeutung, drei bekommen
schärfere Pflichten (`forever`, `publishes`, `breaking`).

---

## 3. Typen und Bereiche — M1, jetzt mit drei Flussregeln

### 3.1 Deklarationen (unverändert)

```ebnf
typedecl = [ "pub" ] [ "opaque" ] [ "linear" [ "ghost" ] ] [ "tagged" ]
           "type" ident [ "(" typelist ")" ] [ "=" typeexpr ] ";" ;
intty    = ( "u8"|"u16"|"u32"|"u64"|"i8"|"i16"|"i32"|"i64" ) [ "in" range ] ;
range    = expr ".." expr | expr "..<" expr ;
```

Jede Operation muss im Bereich ihres Ergebnistyps bleiben; passt `a + b` nicht ins Ziel, ist das
ein **Übersetzungsfehler, keine Laufzeitprüfung**. Division und Rest verlangen einen Nenner, dessen
Bereich die Null ausschließt.

### 3.2 Die drei Flussregeln — geschlossen, lokal, vorhersagbar

Die Gegenmessung (`NARROW-GEMESSEN.md` überholt: **255 Subtraktionen, 102 flusssensitiv**) hat
gezeigt, dass *eine* Regel nicht reicht und `narrow` allein zum Ritual würde. Es gibt jetzt **genau
drei** Regeln. Sie sind **syntaxgesteuert, ohne Fixpunkt, ohne Löser**: der Prüfer führt je Block
eine **Faktenmenge**, die nur an den drei benannten Stellen wächst und bei **jedem Schreiben auf
eine beteiligte Stelle stirbt**. Schleifen tragen keine Fakten hinein (die Invariante der
Traversierung tut das, §9).

| | Regel | Beispiel |
|---|---|---|
| **V1** | eine geprüfte **Bereichsbedingung** verengt den Bereich der geprüften Stelle im Zweig danach | `if x >= 1 { … }` → `x : u32 in 1..max` |
| **V2** | eine geprüfte **Beziehung zweier Stellen** wird zum Zweigfakt; unter dem Fakt `a >= b` hat `a - b` den Typ `0 .. a.max − b.min`, unter `a > b` den Typ `1 .. a.max − b.min`. Ausschließlich Vergleichsfakten, ausschließlich direkt geprüfte Stellen | `if a >= b { let d = a - b; }` — die **102 Fundstellen** fallen sämtlich unter diese Form |
| **V3** | ein `match` auf einen `tagged`-Typ verengt im Zweig auf die Variante samt Nutzlast | erschöpfend, kein Auffangzweig |

Was **nicht** unter V1–V3 fällt, braucht `narrow place to range else { … }` — eine Anweisung mit
benanntem Ausgang, keine Beweiszeile. **Messlatte bleibt:** wächst `narrow` über die Restmenge der
Gegenmessung hinaus (**≤ 24 Fundstellen** im heutigen Baum), ist die Regelmenge zu klein gewählt
und *das* die Widerlegung — nicht ein weiteres Regelwachstum in Stille.

### 3.3 Neutypen und Summen (unverändert)

`opaque` verbietet die Umwandlung in beide Richtungen; `tagged` ist der Summentyp und senkt sich
auf C-Union mit Marke ab; `match` darüber ist erschöpfend.

---

## 4. Lineare und geisterhafte Werte — M2

```gabbro
linear type Parked;                      -- echte Ressource: Bytes im Erzeugnis
linear ghost type Held(Lock);            -- Beleg: vor der Codeerzeugung gelöscht
linear ghost type BootPhase;
linear ghost type MayWrite(ThreadId, Pa);
linear ghost type Duty(check);
linear ghost type Member(domain);        -- Zugehörigkeitszeuge, nur erzeugt (§9.2)
```

**Linear heißt linear, nicht affin:** ein linearer Wert wird genau einmal verbraucht. Fallenlassen
ist ein Übersetzungsfehler; `leave`/`return` aus einem Bereich, der lineare Werte hält, verlangt
deren Nennung (`leaves`). Kopieren gibt es nicht (E3). Geisterwerte haben **keine Absenkung**:
kein Byte, keine Halde, kein Zyklus.

**Wer Zeugen erzeugen darf, ist geschlossen:** `Held` nur der `locks`-Block, `Member` nur die
Domänenaufzählung des Übersetzers, `MayWrite` nur die erzeugte Cap-Auflösung, `Duty` nur `check`,
`BootPhase` nur der Eintrittspfad. Ein von Hand gebauter Beleg ist damit ein **Typfehler** — das
ist das an Verus gemessene Ergebnis („selbstgebauter Beleg: Typfehler"), als Sprachregel.

---

## 5. Zeiger, Adressräume, eingebettete Zeiger — M3

### 5.1 Räume und Rechte (unverändert)

```ebnf
ptrty  = "ptr" "<" space "," rights ">" typeexpr ;
space  = "normal" | "mmio" | "dma" | "code" | "boot" | ident ;
rights = right { "+" right } ;
right  = "r" | "w" | "rw" | "x" | "own" [ "@" ident ] ;
```

Die Barriere folgt aus dem **Raum**: ein Store nach `dma` emittiert die Publikationsbarriere der
Zielarchitektur, ein `mmio`-Zugriff ist volatil und nicht umsortierbar. `own` ist das
Eigentumsrecht (Freigabe), damit ist `Finalized` ohne Lebenszeiten ausdrückbar.

### 5.2 Zeigerarithmetik hat genau eine Form

`place[expr]` mit M1-beschränktem Index und `offset_into` in Formaten. Sonst keine.

### 5.3 `embeds` — **das Wurzelproblem: ein PTE ist zugleich Zeiger und Bitfeld**

```ebnf
field    = ident ":" fieldty [ "@" bitpos ] [ "offset_into" ident ]
           [ "where" pred ] [ "reserved" ] "," ;
fieldty  = typeexpr
         | typeexpr "embeds" "[" int ":" int "]" [ "scale" constexpr ] ;
```

Ein `embeds`-Feld **trägt einen typisierten Wert in einem Bitbereich**, skaliert:

```gabbro
format Pte endian little {
    present  : bool @0,
    writable : bool @1,
    user     : bool @2,
    nx       : bool @63,
    pfn      : Pa embeds [51:12] scale 4096 where aligned(it, 4096),
}
```

Lesen von `pfn` liefert `Pa` (Bits `[51:12] << 12`); Schreiben verlangt die `where`-Bedingung —
`aligned(it, 4096)` ist ein eingebautes Prädikat über M1 (die unteren Bits des Bereichs sind
null), **kein Löser**. Die Absenkung ist Maske-und-Schiebung, zur Übersetzungszeit ausgerechnet.
Damit ist die 13-Mehrbitfelder-Klasse aus `vtd.rs` **und** die PTE-Klasse **ein** Konstrukt.

### 5.4 `walk` — selbstbeschreibende, mehrstufige Tabellen

```ebnf
walkdecl = "walk" ident "levels" constexpr "{"
             "node" ":" array ","
             "down" ":" ident "when" pred ","
             "leaf" ":" pred ","
             { invariant }
           "}" ;
```

```gabbro
walk PageTable levels 4 {
    node : [Pte; 512],
    down : pfn when it.present && !leaf(it),
    leaf : it.present && (level == 0 || it.large),

    invariant wx_disjoint cost O(n) runs online :
        forall m in mappings of Self: !(m.writable && !m.nx);
}
```

`down` nennt das **eingebettete** Feld, über das abgestiegen wird; `levels` ist eine Konstante,
also ist die Tiefe M1-beschränkt und **die Terminierung des Abstiegs fällt durch Konstruktion** —
kein Variant, kein Lemma. Der Übersetzer erzeugt aus der Deklaration die Aufzählung, die
Traversierung, das Induktionsschema (§6) — und die Mutationsoperationen im Zuschnitt (c) (§10.2).

---

## 6. Prädikate — die Linie, mit der achten Domäne

```ebnf
quant  = ( "forall" | "exists" ) ident "in" domain ":" pred ;
domain = "slots" "of" place | "chain" "(" ident "," ident ")" "in" place
       | "descendants" "of" place | "queue" place | "fields" "of" path
       | "elems" "of" place | "threads"
       | "mappings" "of" place ;              (* NEU — erzeugt aus einer walk-Deklaration *)
```

**Acht Domänen, geschlossen. Schachtelung höchstens zwei. `old(place)` nur in `ensures`.**

`mappings of` quantifiziert über alle erreichbaren Blatt-Einträge einer `walk`-Struktur, samt
virtueller Adresse und Ebene — damit ist **W^X über die zweistufige Seitentabelle**
(`mmu.rs:1283`, die eine unformulierbare Pflicht der Messung) formulierbar. Die Domäne ist
**erzeugt aus der Deklaration**, nicht benutzerdefiniert: die Linie steht.

Unverändert: keine benutzerdefinierten Quantorendomänen, keine Rekursion in `spec fn`, keine
handgeschriebenen Lemmata. Die eine Ausnahme bleibt `by induction over <domain>` — sie **nennt**
das erzeugte Schema (Vorhersagbarkeit), sie beweist nicht. Fällt eine Eigenschaft aus den acht
Domänen heraus, ist sie **nicht formulierbar** — sie wandert als benannte `obligation` ins
Manifest (§15), nicht in einen Kommentar.

---

## 7. Funktionen, Verträge, Kosten — E4

```ebnf
fndecl = [ "pub" ] [ "spec" | "impl" | "raw" | "divergent" | "prim" | "extern" ]
         "fn" ident "(" [ params ] ")" [ "->" typeexpr ]
         [ "requires"  predlist ]
         [ "ensures"   predlist ]
         [ "maintains" identlist ]
         [ "effects"   "{" efflist "}" ]        (* PFLICHT ausser bei spec fn *)
         [ "costs"     "<=" expr "ops" ]
         [ "by"        inductlist ]
         [ "section" string ] [ "arch" ident ] [ "when" constexpr ]
         ( block | "=" pred ";" | ";" ) ;
```

**`effects` ist Pflicht und nicht fail-open**; wer nichts anfasst, schreibt `effects { pure }`,
und das wird geprüft.

**`costs` zählt Operationen, und die Einheit ist definiert:** 1 op = eine Gabbro-Primitive
(Zuweisung, arithmetische Operation, Laden, Speichern; ein Aufruf zählt die deklarierten `costs`
des Gerufenen; eine Traversierung zählt Rumpfkosten × Domänenschranke; Zweige zählen das Maximum).
Das ist eine **Eigenschaft des Programms** (D10), statisch ausgerechnet, keine Zeitmessung — und
sie ist die Größe, in der `per_pass`, `held` und `bounded` sprechen. Zyklen gibt es in der Sprache
nicht.

---

## 8. Anweisungen

### 8.1 Bestand

`let` (mit `else (e) { … }` als einziger Fehlerfortpflanzung: der Zweig divergiert oder kehrt
zurück), Zuweisung (kein Ausdruck), `if`, erschöpfendes `match`, `narrow … else`, `locks`-Block,
`return`.

### 8.2 `leave` und `next`

```ebnf
leavestmt = "leave" ident ";" ;
nextstmt  = "next"  ident ";" ;
```

Beide zielen auf eine **benannte** Schleifenform. `leave` aus `forever` ist erlaubt und ist die
geordnete Abschaltung: die `leaves`-Klausel nennt die linearen Werte, die den Ausgang verlassen.
`break`/`continue` ohne Namen gibt es nicht — bei geschachtelten Schleifen ist das Ziel sonst
Konvention statt Syntax.

### 8.3 `breaking` — mit Buchungsregel

```ebnf
breakstmt = "breaking" identlist block ;
```

Im Block ist die Invariante **als Prämisse nicht verfügbar**: Funktionen mit `requires I` oder
`maintains I` sind nicht aufrufbar (Effekt-geprüft). Am Blockende ist I wiederherzustellen —
**durch Konstruktion nur, wenn der Block mit einer erzeugten Operation der Struktur schließt**;
sonst ist die Wiederherstellung eine **`obligation`** im Manifest. Das ist die dritte Klasse
„Klempnerei, getragen von Logik", als Regel: *fällt eine Klempnerei-Pflicht nur über eine
Logik-Invariante, wird sie als Logik gebucht.* Ohne diese Regel wird „fällt durch Konstruktion"
zur bequemen Buchung — der `depleted_count`-Streitfall ist damit entschieden.

---

## 9. Schleifen — drei Formen, alle repariert

### 9.1 Grammatik

```ebnf
loopform = traverse | retry | forever ;

traverse = "traverse" ident [ "of" expr ]
           "over" domain
           "by" ( "unvisited" | "consuming" | "decreasing" expr )
           [ "touches" efflist ]
           block ;

retry    = "retry" [ ident ] [ "until" pred ]
           "bounded" expr "ops"
           [ "progress" ident ]
           "on_exceeded" ident
           [ "effects" "{" efflist "}" ]
           block ;

forever  = "forever" [ ident ]
           "per_pass" "bounded" expr "ops"
           "on_exceeded" ident                   (* JETZT PFLICHT — D11 *)
           "effects" "{" efflist "}"
           [ "progress" ident ]
           [ "leaves" identlist ]
           block ;
```

### 9.2 `by consuming` — mit der Zeugenordnung, die der vierte Papierversuch verlangt hat

Die Laufvariable ist ein `linear ghost Member(domain)`, den der Rumpf verbrauchen **muss** (M2).
**Die Ordnung ist Teil der Domäne, nicht des Aufrufs:** eine Domäne, die `by consuming` anbietet,
liefert ihre Zeugen in der **von der Struktur erzeugten wohlfundierten Ordnung** — für
`descendants of` ist das *tiefenfallend* (Kinder vor Eltern), für `chain` die Kettenfolge, für
`mappings of` blattaufwärts. Der Zeuge trägt dadurch nicht nur Zugehörigkeit, sondern die Zusage
*„alle Nachfolger in der Ordnung sind bereits verbraucht"* — und **genau das ist Blattheit zum
Verbrauchszeitpunkt**. `delete_leaf(it)` verlangt diese Zusage als `requires`; sie kommt aus der
Ordnung, nicht aus einer Laufzeitprüfung.

**Buchung, ehrlich:** die Entsprechung „Zeugenmenge leer ⇒ Menge leer" und die Ordnungserhaltung
unter der erzeugten Mutation fallen **einmal je Konstrukt in der Schablone des Erzeugers** an —
amortisiert, nicht beseitigt. Die Schablone gehört zur vertrauenskritischen Fläche (§0) und steht
im Pflichtenmanifest als geschlossener Posten mit Fundstelle.

### 9.3 `forever` — Sperrwartezeit, entschieden

**Sperrwartezeit zählt nicht in `per_pass` — und darf trotzdem nicht unbeschränkt sein.** Die
Auflösung ist kompositional statt im Schleifenkonstrukt:

1. Jede Sperre deklariert `held <= K ops` (§11.2). Ein `locks`-Block, dessen Rumpfkosten K
   übersteigen, ist ein Übersetzungsfehler.
2. In `forever`/`retry` ist nur eine Sperre **mit** `held`-Angabe nehmbar. Der Ticket-Spinlock
   ohne Schranke (`caprock-sync:821`) ist damit in einer Dienstschleife **nicht schreibbar** — das
   Konstrukt nimmt die Pflicht ab, statt sie zu behaupten.
3. `per_pass bounded` zählt die eigenen ops des Durchgangs; die Schranke **darf von
   Durchgangs-Eingaben abhängen** (`per_pass bounded 64 + 12 * lenof(msg) ops`) — damit ist
   Ed25519 über ein Manifest ehrlich beschreibbar statt falsch beschränkt.
4. Die Latenzaussage je Wartestelle ist damit ableitbar (Ranghöhere halten ≤ ihrer `held`-Summe)
   und wird als Zahl ins Erzeugnis emittiert — eine **abgeleitete** Größe, die niemand parallel
   zur Wahrheit führt.

`progress` bleibt: es nennt, **wer** die Schleife beendet — eine Annahme mit Falsifikator; der
Watchdog ist der Falsifikator.

---

## 10. `format`, `table`, `walk` — die Bibliotheksschicht mit erzeugten Mutationen

### 10.1 `format` (Bestand, plus `embeds`)

Fester Satz: Felder mit Bereichen, `where`-Bedingungen, `offset_into` gegen `lenof(Self)`,
`endian`, Versionen mit **Absage statt Migration** (gemessen: 0 von 11 Formatwechseln waren
Migrationen). Der Leser prüft **einmal am Eintritt** die Pufferlänge; alles Weitere sind bewiesene
Zugriffe ohne Laufzeitprüfung. Der Schreiber ist die Umkehrung; `lesen(schreiben(x)) == x` ist
Pflicht im Differenztest.

### 10.2 `table` — Zuschnitt (c) ist festgelegt

```ebnf
table    = "table" ident "{" { constdecl | slotdecl | invariant | opdecl } "}" ;
opdecl   = "ops" identlist ";" ;
```

`ops insert, remove, relabel, delete_leaf;` nennt die **erzeugten Mutationen**. Der Erzeuger zeigt
je Operation **einmal über der Deklaration**, dass jede `online`-Invariante erhalten bleibt —
nicht je Aufrufstelle. Handgeschriebene Mutation an einer `table` mit `ops` ist ein
Übersetzungsfehler; eine `table` **ohne** `ops` ist reine Beschreibung mit erzeugtem Prüfer
(Zuschnitt (a)) — beides ist dieselbe Syntax, der Unterschied ist eine Zeile und damit **sichtbar
gewählt** statt schleichend.

Invarianten tragen `cost O(…)` und `runs online | offline` (Bestand): `online` läuft im erzeugten
Mutationspfad und muss in dessen `costs` passen; `offline` ist Diagnostik und läuft im
Prüfgerüst.

### 10.3 `device` (Bestand)

`class r|w|rw|w1c|rc`, `fields` mit Bitbereichen, `bank … at expr stride … count …` (M1-beschränkt),
`mirrors … from …` einmal je Gerät, `transition` über dem **ganzen geschriebenen Wort** samt
`keeping` — RMW auf `w`-Registern bleibt unformulierbar. Neu: `transition … publishes { place }`
(§11.3) für die Gerätepublikation.

---

## 11. Nebenläufigkeit — vier Reparaturen

### 11.1 `atomic` — Deklaration schlank, Nutzlast am Store

```ebnf
atomicdecl = [ "pub" ] "atomic" ident ":" typeexpr
             [ "acquire" | "release" | "seq" | "relaxed" ] ";" ;
```

### 11.2 `lock` — mit Haltezeit

```ebnf
lockdecl = "lock" ident "protects" "{" placelist "}"
           "rank" constexpr [ "held" "<=" constexpr "ops" ] [ "masks" ident ] ";" ;
```

`rank`: Nehmen verlangt echt kleineren Rang (Bestand). `held` ist die deklarierte Haltezeit in
ops; jeder `locks`-Block wird dagegen geprüft. Ohne `held` ist die Sperre in Dienstschleifen
nicht nehmbar (§9.3).

### 11.3 `publish` — die Publikation steht am Store

```ebnf
publishstmt = place "=" expr "publishes" ( placelist | "nothing" ) ";" ;
```

**Jeder Store an ein `atomic` und jeder Store in einen `dma`-Raum ist ein `publishstmt`** — die
Nutzlast wird dort genannt, wo sie entsteht, mit den dort sichtbaren Indizes
(`FP_OWNER[core] = tid publishes { FP_STATES[tid] };` — der selbstbezügliche Fall ist schreibbar).
Eine **Aussage** als Nutzlast wird als `ghost static` reifiziert und veröffentlicht wie ein Platz
(`STALE_STEP = 2 publishes { ghost dead_in_senders };`). Reine Zähler schreiben
`publishes nothing`, und das ist ein Wort, kein leeres Listenloch. Die Gerätepublikation
(virtio-`avail`) steht an der `transition` des Geräts — die sicherheitskritischste
Veröffentlichung im Baum ist damit erstmals im Modell.

Die Deklaration darf zusätzlich eine **Obermenge** nennen; dann prüft der Übersetzer jede
Store-Nutzlast dagegen. Sie muss es nicht — die Pflicht sitzt am Store.

### 11.4 `accumulates` — ohne die verbotene Schleife

```ebnf
accdecl = "accumulates" ident ":" typeexpr "merge" ( "max"|"min"|"add"|"or"|"and" ) ";" ;
```

Absenkung: **je Kern eine Zelle** (`relaxed`), Zusammenführung beim Lesen über die
NCORES-beschränkte Schleife. **Kein CAS, keine unbegrenzte Schleife** — der Widerspruch
„der Übersetzer emittiert, was die Sprache verbietet" ist damit aufgelöst, und die Absenkung ist
schneller als die, die sie ersetzt. Die Merge-Menge ist geschlossen (kommutative Monoide).

---

## 12. Boot, Maschine, Axiome (Bestand, präzisiert)

`linear ghost BootPhase`; `raw fn` verlangt sie geliehen; `boot_end` verbraucht sie **und** bildet
`code<boot>` ab — ein Ereignis, die Sonde auf eine `.boot`-Adresse ist der Falsifikator.
`prim fn … -> never` für `switch_to`/`resume` (Kontextwechsel als Primitiv, Stapelwechsel ist in
keiner strukturierten Sprache ausdrückbar); `divergent fn` für ausgesprochene Nichtterminierung.

`assume`/`axiom` mit den drei Klassen (falsifiziert / mit Grund nicht falsifizierbar / **nicht
gefahren = Übersetzungsfehler**). Die Axiomschicht ist die größte unbewiesene Fläche der Sprache
und **ratschenfähig**: wächst sie, um ein Sprachdefizit zu decken, greift Abbruchbedingung 5.

**`iasm`** hat genau eine Emissionsstelle im Übersetzer. Der Eintrittspfad (Registerabdruck,
`iretq`/`eret` als Übergang über dem Maschinenzustand) hat **keinen nachgelagerten Beweiser** —
das Vertrauen schrumpft von 161 Fundstellen auf eine Stelle, es verschwindet nicht. So steht es
im Manifest.

---

## 13. `check` (Bestand)

Unverändert: `claim`, `measures` (die Liste **ist** die Berichtszeile), `gates`, `can_fail`,
`floor`, `counterprobe … expects`. Der Übersetzer erzeugt `linear ghost Duty(check)`; die vier
Übersetzungsfehler fallen aus M1/M2/M3. `check`-Rümpfe und `offline`-Invarianten übersetzen nur
unter `when TESTBUILD` — im Auslieferungs-C existieren sie nicht.

---

## 14. Absenkung nach C — hochperformant, weil beweisend statt prüfend

### 14.1 Der Grundsatz

**Syntaxgesteuert, nicht optimierend.** Jede Konstruktion hat genau eine C-Form; Optimierung ist
Sache des C-Übersetzers, dem die Absenkung dafür das Beste mitgibt, was sie weiß: `restrict` aus
`effects`, `_Noreturn` aus `never`, konstante Masken aus `embeds`/`fields`, `switch` aus `match`.

### 14.2 Die Kostenwahrheit, prüfbar

**Was bewiesen ist, wird nicht geprüft.** Bereiche, Indizes, Blattheit, Phasen, Beleg­e — alles
M1/M2-Material ist im C **abwesend**, nicht abgeschaltet. Laufzeitprüfungen existieren an genau
zwei Stellen: am `format`-Eintritt (eine Längenprüfung je Puffer) und in `narrow` (ein Zweig).
Geisterwerte, `progress`, `costs`, Verträge: **null Bytes**.

| Konstrukt | C-Form | Mehrkosten gegen Handschrift |
|---|---|---|
| `intty in range` | nackter C-Typ | **0** — der Bereich ist Beweis, nicht Prüfung |
| `narrow … else` | ein `if` | 0 gegen den `if`, den Handschrift auch braucht |
| `tagged` + `match` | Union+Tag, `switch` | 0 |
| `traverse` | `for` ohne Bound-Checks | 0; `by consuming` erzeugt **keinen** Besucht-Speicher — die Ordnung ist statisch |
| `format`-Leser | Zugriffe nach einer Längenprüfung | 0 gegen korrekte Handschrift |
| `device`/`transition` | ein volatiler Store, Maske konstant | 0 |
| `walk`-Abstieg | Schleife über `levels` (konstant, entrollbar) | 0 |
| `accumulates` | Zelle je Kern, relaxed | **negativ** gegen die CAS-Fassung |
| `lock`/`locks` | die vorhandene Sperrprimitive | 0 |
| Geister, Verträge, `check` (Auslieferung) | — | **0 Bytes** |

**Prüfbar als Abnahme:** je Modul erzeugtes C gegen handgeschriebenes C im Differenz-Benchmark;
Auslösung, wenn erzeugt langsamer als Handschrift + Messrauschen. Das ist die Phase-1-Schwelle,
jetzt als Absenkungseigenschaft formuliert.

### 14.3 Ausgabeform

Ein Ziel: **C11 (freestanding) + `iasm`**, `-ffreestanding`-tauglich, keine libc-Abhängigkeit im
Kern. Deterministisch: gleiche Quelle, gleiches C, byteweise. Namen stabil aus `path`, damit das
Erzeugnis diffbar ist.

### 14.4 Der Rand: `extern fn`

```gabbro
extern fn memcpy_fast(dst: ptr<normal, w> u8, src: ptr<normal, r> u8, n: usize)
    effects { writes dst, reads src }
    requires n <= lenof(dst), n <= lenof(src);
```

Ein `extern fn` ist eine C-Randfunktion: ihr Vertrag ist ein **`assume` je Deklaration** und zählt
in die Axiomschicht — der Rand ist damit sichtbar und ratschenfähig statt still.

---

## 15. Das Pflichtenmanifest — Logik geht nicht verloren

Der Übersetzer emittiert je Übersetzungseinheit ein Manifest:

```
obligation revoke.functional      "ensures !exists k in descendants of s: k.used"   offen
obligation breaking.cdt_repair    "Wiederherstellung nach breaking in move_cap"      offen
assumption vtd_te_effective       falsifiziert(probe_vtd_te)
assumption x2apic_two_step        unfalsifizierbar("qemu64 hat kein x2APIC")
closed     consuming.schablone    "Ordnungserhaltung descendants, Erzeuger-Schablone" Fundstelle
```

**Drei Klassen:** offene Logik-Pflichten (der Programmierer oder ein externes Werkzeug), die
Annahmenmenge (Namen mit Klasse, keine Kardinalzahl), geschlossene amortisierte Posten mit
Fundstelle. „Speichersicher unter A1…An, funktional offen an O1…Ok" ist damit ein **Satz im
Erzeugnis**. Die Ratsche läuft über Namen; Austausch ist sichtbar.

---

## 16. Caprock-Vollständigkeit — die Landkarte

| Bereich | trägt | über |
|---|---|---|
| Formate (part, fat, ELF, DTB, ABI, ACPI-dmar, virtio-Deskriptoren) | `format` + `embeds` + `offset_into` + `chain` | §10.1 |
| CapSpace/CDT samt revoke | `table … ops` + `by consuming` + `by induction over` | §10.2, §9.2 |
| Seitentabellen, W^X, IOMMU-Wurzeln | `walk` + `mappings of` + `embeds` | §5.4, §6 |
| Gerätetreiber (VT-d, SMMUv3, virtio, x2APIC) | `device` + `transition publishes` + `bank` | §10.3, §11.3 |
| Scheduler/SMP (Sperren, Phasen, FP-Besitz) | `lock rank held` + `linear ghost` (Held, Parked→admit, MayWrite) + V2 | §11.2, §4, §3.2 |
| Dienstschleifen (virtio-blk, Server) | `forever` mit `on_exceeded`, eingabeabhängigem `per_pass`, `held`-Pflicht | §9.3 |
| Boot, Eintritt, Kontextwechsel | `BootPhase`, `prim`, `iasm`, Axiomschicht | §12 |
| Prüfgerüst (15,7 %) | `check` unter `when TESTBUILD` | §13 |
| Rand (memcpy, Krypto-Kerne) | `extern fn` mit Vertrag als Annahme | §14.4 |
| Bedingte Übersetzung (335 `cfg`) | `when` | Bestand |

**Was bleibt, ist Logik** — `ensures` der algorithmischen Rümpfe (IPC-Fastpath, Scheduler-Wahl,
revoke-Funktionalität), sichtbar im Manifest. Das ist die Zusage aus §0, wörtlich.

---

## 17. Was es absichtlich nicht gibt (ergänzt)

Bestand (`while`, `for`, `goto`, Präprozessor, implizite Umwandlung, `void*`, Auffangzweig,
Ausnahmen, Vererbung, Reflexion, GC, Gleitkomma im Kern, Zuweisung als Ausdruck,
Vorwärtsdeklaration, Selbst-Hosting, benutzerdefinierte Quantorendomänen, Rekursion in `spec fn`,
handgeschriebene Lemmata) — **plus, jetzt genannt statt vergessen:** `break`/`continue` ohne Ziel
(ersetzt durch `leave`/`next` mit Namen), unbenannte Sperrhaltezeit in Dienstschleifen,
CAS-Schleifen als Absenkungsdetail, Migration in Formatversionen, Zyklen als Zeiteinheit.

---

## 18. Die neun Entscheidungen, nummeriert

| # | Frage | Entscheidung |
|---|---|---|
| F1 | 102 relationale Vorbedingungen | **V2**, geschlossene Flussregel; `narrow`-Messlatte ≤ 24 |
| F2 | PTE = Zeiger UND Bitfeld | **`embeds [hi:lo] scale`**; Wurzel gelöst, nicht die Domäne |
| F3 | achte Domäne (W^X) | **`mappings of`**, erzeugt aus `walk` |
| F4 | `per_pass`-Ritual | ops statt Zyklen, `on_exceeded` Pflicht, Wartezeit über **`held`** kompositional, eingabeabhängige Schranke |
| F5 | `publishes` an der falschen Stelle | **Store-Pflicht** (`publishstmt`), Deklaration optional als Obermenge; Geräte über `transition publishes`; Aussagen als `ghost static` |
| F6 | `accumulates`-Widerspruch | **Zelle je Kern + merge**, kein CAS |
| F7 | `break`/`continue` | **`leave`/`next`** mit Zielname; in der Verbotsliste genannt |
| F8 | `breaking` | Invariante als Prämisse gesperrt; Wiederherstellung durch erzeugte Op **oder** `obligation` — Buchungsregel „getragen von Logik" |
| F9 | `depleted_count`-Streitfall | dritte Klasse, Buchung als Logik (§8.3) |

---

## 19. Abnahme dieser Festlegung

1. **Die 74-Pflichten-Messung wiederholen** gegen diese Fassung: hängende Klempnerei 19 → 0,
   sonst Widerlegung an den Reststellen (mit Klasse und Fundstelle).
2. **Die zehn Fragmente** aus dem Scratchpad in den Ordner, auf diese Syntax gezogen, Wächter
   grün (Erreichbarkeit, Terminaldeckung, Sprechprobe in beide Richtungen).
3. **`narrow`-Zählung** am Baum: ≤ 24, sonst ist V1–V3 zu klein.
4. **Kostenwahrheit** (§14.2) je übersetztem Modul im Differenz-Benchmark.
5. Die Zählregel bleibt: Spezifikation ist, **was in der Quelle steht** und vor der Codeerzeugung
   gelöscht wird; Erzeugtes ist Ausgabe. Ziel 0,5:1 für Kernelcode, 1:1 nie überschritten für
   `format`; Abbruch > 3:1 unverändert.
