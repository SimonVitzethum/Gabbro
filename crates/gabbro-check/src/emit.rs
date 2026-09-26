//! **The C emitter -- the first line of the largest undamageable surface.**
//!
//! Until 2026-08-17 this surface did not exist. `mutiere-pruefer.py` reported it with **0
//! mutations**, and *what has 0 mutations is not covered, it is undamageable*. Three things
//! hung on it: the plumbing class *refinement*, the templates `table.absenkung` and
//! `table.ops.erhaltung`, and the licence notice that `LIZENZ-ZUSATZ.md` demands in generated
//! C while nothing wrote it.
//!
//! ## What this emitter is, and what it deliberately is not
//!
//! **It is two translation units, not ten.** It covers exactly the forms that
//! `beispiele/16-by-ops-am-feld.gab` and `FRAGMENTE.md` F7 use: a `table` with `count`, range
//! types, `bool`, `index into T`, pointer parameters, field and index access, assignment,
//! `return`, calls, prototypes for bodiless declarations, and **the erasure of a
//! `linear ghost type`**. Anything else it **refuses by name** (`C001`) instead of emitting
//! something plausible.
//!
//! ## The erasure is the one thing here that is not a lowering
//!
//! A ghost value **does not exist at run time**. It has to vanish from the signature, from the
//! call site and from the `let` binding — three places at once, and two of the three failure
//! forms are silent. *The third is the dangerous one:* drop the whole `let` statement instead
//! of only its binding and the C compiles while the boot step **does not happen**. The
//! counter-probe of 2026-08-17 produced `6` where `123456` was expected — five of six steps
//! gone without a warning.
//!
//! > **A generator that emits something for a form it does not know is worse than one that
//! > stops.** The whole value of this crate is that its output is trustworthy; a silent
//! > approximation in the emitter would undo every pass in front of it.
//!
//! ## W6 holds here, and this is where it bites
//!
//! *The omission of a runtime check is justified by M1 alone, never by an invariant.* This
//! emitter omits **no** check, because it emits none yet -- but the rule is why `index into T`
//! becomes a plain `uint32_t` and not a range-checked accessor: the bound comes from `count N`
//! and is an M1 fact. The moment a check is left out here, the reason has to be an M1 fact and
//! stand in this file.

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};
use std::collections::{BTreeSet, HashMap};

/// What the emitter must resolve: table names (a path naming one IS the struct), named
/// types (they lower to their carrier), **ghost types (they lower to NOTHING)** and the
/// signatures it needs in order to erase a ghost at a call site.
#[derive(Default, Clone)]
struct Namen {
    tabellen: Vec<String>,
    /// Die `format`-Namen. Ein Pfad, der eines nennt, IST der Zugriffsverbund.
    formate: BTreeSet<String>,
    /// **Format name -> the fields that GET A READER** (`D1`, 2026-09-03).
    ///
    /// `format_` writes one `{Format}_{field}` accessor per field and writes NONE for a
    /// field marked `reserved` -- that is what the word is for. Nothing else in this file
    /// knew it. A `walk`'s descent lowers `down : rest when …` into a call on exactly that
    /// accessor, so `beispiele/gift/641` reached `cc` as an implicit declaration of
    /// `Pte_rest` while the checker said `0 errors`.
    ///
    /// > *The set says READER, not FIELD, and the difference is the whole point.* A
    /// > `reserved` field is declared and has no reader; a misspelt one is neither. Both
    /// > lower to the same missing call, so both belong on the same side of this map, and
    /// > the refusal at the `walk` distinguishes them in its text.
    formatfelder: HashMap<String, BTreeSet<String>>,
    /// Je Geraet: der Raum und seine Register. **Ein Registerzugriff ist KEIN Feldzugriff**
    /// -- siehe `geraet`.
    /// **The assumption names this unit DECLARES** (2026-08-26).
    ///
    /// The emitter already prints them into the C header; until now nothing READ them.
    /// `at dma` does: which barrier a DMA access needs is a statement about the memory
    /// model, and rather than guessing it the generator DEMANDS that the unit name it.
    /// *A wall becomes a door: the refusal says which assumption is missing.*
    annahmen: BTreeSet<String>,
    /// **The machines this unit NAMES** (2026-09-02) -- every `arch` word that stands
    /// anywhere in it: at an `entry`, an `entrust`, a `boot`, a function, an `assume`.
    ///
    /// `at port` reads it. A port access lowers to an `in`/`out` instruction, and those exist
    /// on x86 and nowhere else -- so a unit that emits one must SAY it is x86. Same move as
    /// `ANNAHME_DMA` a few hundred lines down: not guessed, demanded by name.
    ///
    /// > *Wider than `namen.rs::annahme_arch`'s own set, and deliberately.* That pass asks
    /// > "can this assumption ever be in force here", and an `assume … arch` is the thing it
    /// > judges, so it may not count itself. **The question here is the other one** -- does
    /// > this unit say which machine it is for -- and an `assume … arch x86_64` says it.
    architekturen: BTreeSet<String>,
    geraete: HashMap<String, Geraet>,
    /// Name -> Geraetetyp, **global und konservativ**: wird derselbe Name irgendwo mit einem
    /// anderen Typ erklaert, faellt er heraus. Dieselbe Bauart wie `vorzeichenlos` -- Unwissen
    /// faellt nach lautstark, dann weigert sich der Registerzugriff.
    geraetezeiger: HashMap<String, String>,
    /// Name -> Tabelle, fuer Zeigerparameter. Konservativ wie `geraetezeiger`.
    tabellenzeiger: HashMap<String, String>,
    /// **Lane E5: the accepted library calls of this unit, by call span.**
    /// Each entry is `(function short name, payload table short name, payload
    /// C name)`: the payload `static const` tables are emitted file-scope
    /// beside the tables, and the two lowering arms read this map. Keyed by
    /// the call's span, which is unique per call. Bare short names, last
    /// wins -- the same module caveat as every other map on this struct.
    nutzlast_einsaetze: HashMap<(u32, u32), (String, String, String)>,
    /// (Tabelle, Slotfeld) -> der erklaerte Typ des Slotfeldes. **Er ist die einzige
    /// Quelle, aus der ein `let obj = c.slots[s].objekt` seinen Typ bekommt** -- und der
    /// Erzeuger raet ihn nicht, er liest ihn ab.
    slotfeld: HashMap<(String, String), TypExpr>,
    /// **(Tabelle, Slotfeld) -> der erklaerte Umlauf.** `SlotTyp::Wrapping` landete bis zum
    /// 2026-08-20 NIRGENDS in dieser Tabelle -- der Erzeuger wusste an der Rechnung nicht,
    /// dass der Slot umlaeuft, und schrieb `a * a` ohne Cast. *Ein Deklarationszeichen, das
    /// die Sprache traegt und die Absenkung nicht kennt.*
    umlaeufer: HashMap<(String, String), IntTy>,
    /// Die `static`-Namen mit ihrem erklaerten Typ. Ein `static mut frei : option index
    /// into Halde` ist ein Ort wie ein Slotfeld -- **ohne den Typ wuesste `frei = Some(i)`
    /// nicht, gegen welchen Sonderwert es schreibt.**
    statiken: HashMap<String, TypExpr>,
    /// Je Tabelle ihr aufgeloester `count`-Wert. **Der Sonderwert haengt daran** -- siehe
    /// `beweise/Option_Sonderwert.thy`, M-1.
    kapazitaet: HashMap<String, i128>,
    /// **«E4»: each arena maps to its `hi` expression and element type.** The bound
    /// stays an expression (a literal or a `const` name, like `count`),
    /// because the C array length spells it the same way; the element
    /// type sizes the buffer. Keyed by bare name, last wins -- the same
    /// module caveat as every other map on this struct.
    arenen: HashMap<String, (Expr, TypExpr)>,
    /// **«E4»: the arenas this unit really touches.** An arena whose name
    /// no body names gets no storage -- an unused file-scope `static`
    /// is a `-Wunused-variable` finding about the generator, not the user
    /// (the same reason `tabelle()` asks `tabellenglobal`).
    arenen_global: BTreeSet<String>,
    /// **The `let` bindings this body never reads back** (2026-08-31).
    ///
    /// The emitter already writes `(void)k;` for an unread PARAMETER, and the comment at
    /// that site gives the reason: *`cc -Wextra` finds it, no pass of this compiler does,
    /// and the user did not write the generated line.* **A `let` is the same C problem and
    /// the same answer** -- `uint64_t r2 = spuelen(a);` with no reader is
    /// `-Werror=unused-variable`, and `messung/fragmente/F05.gab`:184 writes exactly that,
    /// in a FROZEN line.
    ///
    /// > **And it is deliberately not a refusal.** Measured 2026-08-31 over the 418 files:
    /// > a rule that refused an unread binding fell in **17** of them -- thirteen poison
    /// > probes, four `fnptr` probes and one measurement file -- *and not one was a defect.*
    /// > **Binding a value and not reading it back is a thing this corpus writes.** Rule A
    /// > cuts the other way here, and the whole weighing stands in
    /// > `messung/ZWEI-BLINDSTELLEN.md` §3.
    ungelesene_lets: BTreeSet<String>,
    typen: HashMap<String, TypExpr>,
    /// **Die Verbundtypen: Name -> Felderliste in Deklarationsreihenfolge** («B7»).
    /// Sie werden zu einem C-`typedef struct`, und ihr Konstruktor zu einem
    /// zusammengesetzten Literal. *`fs` aus `beweise/Verbund_Konstruktor.thy`.*
    verbunde: BTreeSet<String>,
    /// **Die `tagged type`-Namen mit ihren Varianten** («C2»). Sie werden `struct { marke;
    /// union { … } }` -- und die Marke ist ein `enum`, damit `-Wswitch` ein **zweiter
    /// Leser von `D005`** wird.
    markierte: HashMap<String, Vec<Variante>>,
    /// **The `reason` names -- a TYPE, and the emitter already writes it** (2026-08-25).
    ///
    /// `ItemArt::Reason` emits `typedef enum { … } R;` some hundred lines below, so `R` is a C
    /// type name of this unit's own making. `ctyp` did not know it, and the collection branch
    /// below listed `reason` among the items that *"declare no name a lowering would look
    /// up"* -- **a sentence that its own emitter refutes.**
    ///
    /// *Found by `messung/fragmente/F06.gab`:* `impl fn messen_benutzt(…, art : Stackart)`
    /// checks with zero errors and fell at `C001 parameter type`. The catch-all branch is
    /// exactly the shape the comment beside it warns about -- **a map that is not missing
    /// loudly, but silently.**
    gruende: BTreeSet<String>,
    /// Name -> markierter Typ, fuer Parameter und `let`. Konservativ wie `tabellenzeiger`:
    /// wer irgendwo anders erklaert ist, faellt heraus. **Ohne das weiss ein `match m`
    /// nicht, WELCHE Variantenmenge erschoepfend sein muss.**
    markenwerte: HashMap<String, String>,
    /// **Name -> `reason`, fuer das `e` eines `let … else`** (Stufe 7, 2026-08-21).
    ///
    /// Anders als `markenwerte` ist diese Karte NICHT ueber die Einheit gesammelt, sondern
    /// wird an genau einer Stelle gesetzt: beim Absenken des `let … else`, fuer die Dauer
    /// seines `else`-Zweiges. *`e` lebt nur dort, und eine Karte, die laenger lebt als ihr
    /// Name, ist der Fehler, den `eigene_sicht` weiter unten beschreibt.*
    gruendewerte: HashMap<String, String>,
    /// **Name -> C expression, for the span of ONE condition** («B26», 2026-08-28).
    ///
    /// The `requires` at a register names the register by its bare name
    /// (`QUEUE_SIZE <= QMAX`). Lowering that name back into a volatile access would read the
    /// device a SECOND time -- and two reads of a volatile register are two values. *That is
    /// «B33» exactly:* the check would then not be about the value that was bound. So the
    /// name is bound to the local that holds the ONE read, and only while that condition is
    /// being lowered. Like `gruendewerte`, and for the same reason: a map that outlives its
    /// name is the mistake `eigene_sicht` describes.
    ersetzungen: HashMap<String, String>,
    /// Die `accumulates`-Namen. **Ein Lesen wird ein Ruf, ein Schreiben auch** -- sonst
    /// stuende im C ein Zugriff auf eine Zelle, die es nicht gibt.
    akkus: BTreeSet<String>,
    /// **The generated operations of this unit, as a caller writes them** (`Verzeichnis::insert`).
    ///
    /// A path call is lowered by its LAST segment everywhere else in this emitter; a
    /// generated operation is the one callee whose C name is built from two of them
    /// (`Verzeichnis_insert`). *The relation stands in the `table` declaration, not in the
    /// call -- so the emitter establishes it instead of copying the name and letting `cc`
    /// find an implicit declaration.* Same move as the `transition` twenty lines further on.
    opsnamen: BTreeSet<String>,
    /// Which of them this unit actually calls -- the one thing `__attribute__((unused))`
    /// hangs on (`crate::opsruf::gerufene`).
    opsgerufen: BTreeSet<String>,
    /// Atomicname -> (C-Typ, `memory_order`-Wort). **K11.2.3** -- ohne den Typ hat ein
    /// `let x = A awaits { … }` keinen, und ohne die Ordnung stuende im C das Vorgabemodell
    /// von `_Atomic` statt dessen, was die Quelle sagte.
    /// **Zwei Ordnungen, nicht eine.** Die Deklaration nennt die SPEICHERseite; ein Laden
    /// mit `memory_order_release` gibt es in C11 nicht (`atomic_load_explicit` nimmt
    /// relaxed, consume, acquire oder seq_cst). *Gefunden beim Lesen des erzeugten C fuer
    /// `beispiele/14` -- der C-Uebersetzer haette es auch gesagt, aber sich darauf zu
    /// verlassen hiesse, die Absage zu delegieren, wo die Antwort hier steht.*
    atomics: HashMap<String, (String, &'static str, &'static str)>,
    /// **The atomics whose declared type is an ARRAY, with their length** --
    /// `atomic REGEL : [u32; 256] relaxed;` lowers to `_Atomic uint32_t REGEL[256];`
    /// (C11 6.7.2.4: `_Atomic` qualifies the ELEMENT type, so every element is an
    /// atomic object of its own and `&REGEL[i]` is a valid first argument to every
    /// `atomic_*_explicit` call).
    ///
    /// **It is a SECOND map beside `atomics` and not a field inside it**, because the
    /// two answer different questions and only one of them has a second reader: the C
    /// type of ONE element is what every access needs (and `atomics` carries exactly
    /// that -- the element type, not the array type), while the length is needed at the
    /// declaration alone. *A name in here is in `atomics` too; the membership is what
    /// says "indexed access is a form here".*
    ///
    /// **And the carrier stays ONE carrier.** In the goal theorem's race component
    /// (`Zielsatz/Akzeptiert.lean`, `atomarB`) the exemption from `RennfreiBis` is one
    /// Bool per `D.Glob` -- a table (`.inl`) is never exempt. An atomic array is the
    /// global `REGEL`, named once in `effects`, in the footprint and under `atomare`;
    /// it does not become a table anywhere, and nothing here widens that exemption.
    atom_arrays: HashMap<String, u128>,
    /// **Atomic name -> its DECLARED element type (lane 221).** `atomics` above
    /// carries the C word, and a C word has forgotten what the declaration
    /// said: `uint32_t` no longer knows whether the source promised the whole
    /// word or `0 .. 65535`. The fetch-add gate (`holwrap_form`) needs the
    /// declaration, not its C image -- *a fetch-add bought by guessing a
    /// modulus is not an improvement* (`OPUS-BERICHT-FETCHADD.md` §2.3). For
    /// an array atomic this is the ELEMENT type, the same choice `atomics`
    /// makes, for the same reason. A name in here is in `atomics` too.
    atomic_elem_typs: HashMap<String, TypExpr>,
    /// Namen, die einen Verbund als **Wert** tragen (Parameter oder `let`). Ihr Feldzugriff
    /// ist `.`, nicht `->` -- siehe `ort`.
    werte: BTreeSet<String>,
    /// **Every name this function binds as a VALUE (lane 167): parameters, `let`s,
    /// `let … else` names and error names, `match` binders, `traverse` variables,
    /// `alloc` indices, `awaits` and `exchange` bindings.**
    ///
    /// A bare `tagged` case (`Leer`) lowers to a compound literal -- unless the name
    /// means something else here. The unit-wide maps cannot answer that: a `let`
    /// shadows only inside its own function, and a `match` binder only inside its
    /// own arm. So the shadowing question is asked against this per-function set,
    /// filled in `eigene_sicht`, and not against the unit. The residual -- a name
    /// bound in one arm and read bare as a case in another -- stays loud: the
    /// checker types it as the case, this set withholds the literal, and `cc`
    /// names the undeclared identifier. It is booked, not closed (same class as
    /// the lane-152 `match`-binder atomic note).
    schatten: BTreeSet<String>,
    /// **The names an enclosing `traverse` bound** -- see `laufsicht` (2026-08-31).
    ///
    /// Every lowered loop variable is an index word: `uint32_t i` or `uint64_t i`. It names
    /// no table, carries no fields and is not a pointer -- so a DOMAIN over it can be
    /// lowered to nothing, and `ort` would write `i->slots` about an `unsigned int`.
    laufvariablen: BTreeSet<String>,
    /// **Enclosing `traverse` binders a `count` may close over («SG-24»): name and
    /// C type, innermost last.** One push per loop form at its `laufsicht` call,
    /// with the loop header's own C type (`traversebinder_ctyp` -- one table, read
    /// here and at the collection walk, so the two cannot drift): the counter a
    /// `count` lowers to takes them as parameters, and this stack resolves them --
    /// the same names C resolves by scope. Every other binder (`match` arms,
    /// `exchange`, `awaits`, `let … else`) is NOT threaded: closing over one
    /// refuses by name, and hoisting it into a `let` first is one line.
    zaehlbinder: Vec<(String, String)>,
    /// **Die Tabellen, die ueber ihren eigenen NAMEN adressiert werden** -- `beispiele/09`:
    /// *„die Tabelle ist der Speicher, ihr Name der Ort."* Sie bekommen ein Objekt
    /// (`T_speicher`); die anderen nicht, denn *eine ungenutzte Groesse im erzeugten C ist
    /// ein Befund ueber den Erzeuger.*
    tabellenglobal: BTreeSet<String>,
    /// `linear ghost type BootPhase;` — a value that **does not exist at run time**.
    geister: Vec<String>,
    /// **`linear type Angemeldet;` ohne Rumpf -- eine MARKE** (2026-08-20).
    ///
    /// `SPRACHE.md`:721 zieht die Linie selbst: *`linear type Parked;` -- echte Ressource:
    /// Bytes im Erzeugnis*, gegen *`linear ghost type Held(Lock);` -- Beleg: vor der
    /// Codeerzeugung geloescht*. Der Geist wird **geloescht**, die Marke nicht. Wer beide
    /// gleich absenkte, machte `ghost` zur Verzierung.
    ///
    /// **Und hier wird nichts geraten.** Der Erzeuger weigert sich, wo mehrere Antworten
    /// plausibel sind; eine Marke ohne Felder hat keine mehrere -- sie hat keine Felder.
    /// Dass in C ein Wert eine Adresse und eine Groesse braucht, ist eine Aussage ueber C.
    /// *Ein Byte ist nicht die kleinste plausible Wahl, sondern die einzige.*
    marken: BTreeSet<String>,
    /// **«B41b»: je Tabelle ihre Baumkanten** -- (parent, child, sibling), jede fuer sich
    /// vorhanden oder nicht. Sie stehen an der `table` und nicht am Durchlauf; `D006`-`D008`
    /// haben sie dort schon gegen den Slot gehalten, also liest der Erzeuger hier ab.
    baeume: HashMap<String, (Option<String>, Option<String>, Option<String>)>,
    /// **Ein Geraetegriff, der aus einem `let` kommt und nicht aus einem Parameter**
    /// (2026-08-20). `beispiele/09` schreibt `let v = Vtd(basis);` -- *„die Parameterliste
    /// der Deklaration IST der Konstruktor"* -- und `v` ist danach ein WERT, kein Zeiger.
    /// Ohne diese Karte wurde `v.RTA` zu `v->RTA`, und `geraetezeiger` half nicht: die Karte
    /// kennt nur Parameter.
    geraetewerte: HashMap<String, String>,
    /// **Name -> `format`, fuer Parameter.** Ein Feld darauf ist ein RUF (`Elf64Kopf_e_eintritt`),
    /// kein `->`. Funktionslokal wie alles andere in `eigene_sicht`.
    formatwerte: HashMap<String, String>,
    /// **Uebergangsname -> sein Geraet.** Ein `transition` heisst im C `Vtd_wurzel_setzen`
    /// und nimmt einen Zeiger; in Gabbro steht `wurzel_setzen(v)`. *Der Erzeuger stellt den
    /// Bezug her, statt den Namen so hinzuschreiben, wie er dasteht.*
    uebergaenge: HashMap<String, String>,
    funktionen: HashMap<String, Signatur>,
    /// Namen, die diese Einheit **nicht deklariert** und die nur hinter einem Zeiger
    /// vorkommen. Sie werden als unvollstaendiger C-Typ vorwaerts deklariert.
    fremde: BTreeSet<String>,
    /// Je `retry` (an seinem Spannenanfang): die **Zahl der Durchgaenge**, die sein
    /// Operationsbudget hergibt. Siehe `retry_schranken`.
    retry_schranke: HashMap<u32, i128>,
    /// Die `const`-Namen -- in einer `where`-Klausel ist ein blanker Name sonst ein FELD.
    konstanten: BTreeSet<String>,
    /// Je `const` sein ausgerechneter Wert -- **von `umgebung.rs` und nicht hier**.
    /// `u64::max` ist dort seit jeher eine Zahl; der Erzeuger hatte daneben seinen eigenen,
    /// schwaecheren Auswerter (`konst_zahl`) und weigerte sich. *Zwei Register ueber
    /// derselben Sache, und das schwaechere hat entschieden* (W7).
    konstwert: HashMap<String, i128>,
    /// **Lane 197: what the checked world names.** `welt_und_konstanten` beside
    /// the emitter, so `wirkungsattribut` reads an omitted clause from the
    /// deeds — the same two lists the checker passes beside the same walker.
    /// Read once per unit in `emittiere_mit`; `eigene_sicht` clones them along.
    welt_konstanten: Vec<String>,
    welt_namen: Vec<String>,
    /// Name -> erklaerter Parametertyp, konservativ ueber alle Funktionen. **Nur damit
    /// bekommt ein `let d = a - b;` seinen Typ**, ohne dass ihn jemand raet.
    ///
    /// Unit-wide by construction -- and therefore NEVER read as-is for a name in a
    /// body. `eigene_sicht` clears the inherited entries and inserts only the
    /// current function's parameters, so every per-function view answers from
    /// its own scope. A reader holding the collected map (a static initializer,
    /// a prototype) answers a different question and says so at its own site.
    parametertyp: HashMap<String, TypExpr>,
    /// **`let`-bound local -> its C type, read from a declaration and not guessed**
    /// (2026-08-25).
    ///
    /// `parametertyp` above answers for anything a SIGNATURE names. A local bound by `let`
    /// had no answer at all: `let frei = unberuehrt(s); let benutzt = s.len - frei;` refused
    /// at `C001 let without a resolvable type` -- **and the type stood in the callee's
    /// declaration the whole time**, exactly as the comment above says about parameters.
    ///
    /// *The chain is why this is a map and not a lookup:* `benutzt` needs `frei`, and `frei`
    /// needs the signature of `unberuehrt`. `lokale_lets` therefore runs to a FIXPOINT, and a
    /// name bound twice in one body is dropped rather than decided -- **unknown falls loud**,
    /// the same rule `geraetezeiger` follows.
    lokaltyp: HashMap<String, String>,
    /// **`let`-bound local -> its DECLARED type expression** (2026-08-26).
    ///
    /// `lokaltyp` above answers with a C type, and a C type has forgotten what the
    /// declaration said: `uint64_t *` no longer knows it points at a `Stack`. `ort_typ`
    /// needs the declaration, not its C image -- *`lenof(f.worte)` asks for the length of an
    /// array field, and that length stands in `[u64; STACK_WORTE]`, nowhere else.*
    lokaltypexpr: HashMap<String, TypExpr>,
    /// **`let`-bound local whose value IS a ghost** (2026-08-30).
    ///
    /// `parametertyp` above answers the same question for anything a SIGNATURE names, and
    /// `geist_wert` asked it alone. A ghost bound by `let` therefore went unrecognised at
    /// every LATER mention of the name: the binding was erased, the mention was kept, and
    /// the C named a variable the emitter had just deleted.
    ///
    /// *This map exists because the other two cannot hold the answer.* `lokaltyp` and
    /// `lokaltypexpr` skip a ghost `let` on purpose -- an entry there would claim a C type
    /// for a name the product never spells. The question "was this name a ghost?" survives
    /// that skip, so it needs a register of its own.
    geistlokal: BTreeSet<String>,
    /// Function name -> its DECLARED result type expression. The one source from which a
    /// `let f = eichfeld();` can learn what `f` is without anyone guessing.
    ergebnistyp: HashMap<String, TypExpr>,
    /// (Verbund, Feld) -> erklaerter Feldtyp. Dieselbe Rolle wie `slotfeld`, eine Ebene
    /// daneben: **ohne ihn weiss der Erzeuger von `s.len` nur, dass es ein Feld ist.**
    verbundfeld: HashMap<(String, String), TypExpr>,
    /// Namen, deren Typ der Erzeuger als VORZEICHENLOS kennt. Nur fuer sie darf die untere
    /// Schranke eines `narrow` bei null wegfallen -- Unwissen faellt nach lautstark.
    vorzeichenlos: BTreeSet<String>,
    /// **Lane 260: the `start` sites with their root counts** -- (statement
    /// span-lo, roots). The file-scope thread stacks are emitted from this
    /// list beside the tables (one 64 KiB region per root); the `Start` arm
    /// reads the same spans to name them. Walked once in `emittiere_mit` over
    /// every function body -- a second register beside the arm would drift
    /// (W7). The walk descends through `crate::unterbloecke`, like every
    /// collector that must not return a subset looking like a set.
    start_orte: Vec<(u32, usize)>,
    /// **Lane 260: functions with a lowered body.** Only a `Block` rumpf has
    /// an address in this unit that a thread could start in; an `extern` or
    /// otherwise bodiless declaration has none, and starting one would link
    /// nowhere. The `Start` arm refuses those by name instead of emitting a
    /// call into a body that does not exist.
    impl_funktionen: BTreeSet<String>,
}

/// Die lokal gebundenen Verbundwerte eines Rumpfes -- **auch in verschachtelten Bloecken**.
///
/// *Ein Sammler, der nur die oberste Ebene sieht, liefert eine Teilmenge und sieht aus wie
/// eine Menge* -- dieselbe Bauart wie eine gefuellte Karte, die niemand vollstaendig geprueft
/// hat (`umgebung.rs`, `Traegerart`).
fn verbundlokale(b: &Block, u: &Namen, aus: &mut Vec<String>) {
    let ist_verbund = |t: &TypExpr| {
        matches!(t, TypExpr::Pfad(p)
            if p.teile.last().is_some_and(|n| u.verbunde.contains(&n.text)))
    };
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Let(l) => {
                // **Steht keine Annotation da, wird der Typ ABGELESEN** -- genau wie in
                // `wert_ctyp`, und bis zum 2026-08-20 tat das nur der eine der beiden
                // Sammler. Die Folge war eine STILLE Absenkung: `let c = fertig(k, 7);`
                // wurde richtig zu `Completion c = fertig(k, 7);`, und der Feldzugriff
                // darauf zu `c->len` -- weil dieser Sammler `c` nicht als Verbund kannte.
                // **`gabbro emit` gab 0 zurueck, `cc` lehnte ab.**
                //
                // > *Gefunden am 2026-08-20 von der Zeremoniefrage:* die Annotation stand
                // > im TODO als ableitbare Zeremonie, und der Versuch, sie wegzulassen,
                // > deckte auf, dass sie zwei Leser hat und nur einer sie ablas.
                let ist = match &l.typ {
                    Some(t) => ist_verbund(t),
                    None => verbundwert(&l.wert, u),
                };
                if ist {
                    aus.push(l.name.text.clone())
                }
            }
            // **`D22`, corrected 2026-09-03: `let x = call else (e) { … }` binds a RECORD
            // too, and this collector's old answer ("decided at the lowering of the
            // statement, not here") did not match what that lowering actually does.**
            //
            // `StmtArt::LetSonst` below always writes a plain `{T} {name};` declaration --
            // never a pointer -- whatever `T` is, so whether `x` ends up a value was already
            // decided, uniformly, and this collector simply had not read it. A name this
            // collector does not register defaults to `zeiger = true` in `ort` (`werte` is
            // the only source `!u.werte.contains(...)` reads), so a record-valued binding
            // lowered its own field access as `c->len` on a plain `Completion c;`:
            //
            //     pruefe: 0 errors, 0 hints    emit: exit 0, `return c->len;`
            //     cc: error: invalid type argument of '->' (have 'Completion')
            //
            // The repair reads the same declaration `wert_ctyp` already reads at the
            // lowering site (the callee's `-> T or R` signature) rather than inventing a
            // second source -- W7. See `messung/ERZEUGERREST.md` D22.
            StmtArt::LetSonst(l) => {
                if let Some(r) = l.als_ruf() {
                    let ist = r
                        .path()
                        .and_then(|p| p.teile.last())
                        .and_then(|n| u.funktionen.get(&n.text))
                        .and_then(|sig| sig.rueck.as_ref())
                        .is_some_and(ist_verbund);
                    if ist {
                        aus.push(l.name.text.clone());
                    }
                }
            }
            // `let x = place awaits { … }` unwraps an ATOMIC. An atomic carries a scalar
            // payload -- never a record -- so there is nothing to register.
            StmtArt::AwaitLoad(_) => {}
            // `let x = place exchange …` likewise yields the atomic's scalar payload.
            StmtArt::Exchange(_) => {}
            // The forms that bind no name at all. **Written out one by one** so that a new
            // `StmtArt` is a compile error here rather than a silent "binds nothing".
            // **Lane E1:** a library call in statement position binds nothing.
            // **«E4»:** an arena index is a `uint32_t`, never a record; `reset`
            // binds nothing at all.
            StmtArt::Zuweisung(_)
            | StmtArt::Wenn(_)
            | StmtArt::Match(_)
            | StmtArt::Schleife(_)
            | StmtArt::Bricht(_)
            | StmtArt::Narrow(_)
            // **Lane O-1:** `child` binds no name itself; locals of the
            // path are collected through `unterbloecke` below.
            | StmtArt::Child(_)
            // **Lane 253:** `start` binds no name itself and carries no
            // block for `unterbloecke` below.
            | StmtArt::Start(_)
            | StmtArt::Alloc(_)
            | StmtArt::ResetArena(_)
            // **Lane 257:** `grow` binds no name; the amount is a count,
            // never a record.
            | StmtArt::Grow(_)
            | StmtArt::Sperrt(_)
            | StmtArt::Observiert(_)
            | StmtArt::Leave(_)
            | StmtArt::Next(_)
            | StmtArt::Publish(_)
            | StmtArt::Return(_)
            | StmtArt::Ruf(_)
            | StmtArt::LibraryCall(_) => {}
        }
        // **The descent is not spelled out a second time.** It used to be -- nine arms of
        // its own -- and the copy had drifted: `observes { … }` and the `update` body of an
        // `exchange` carry blocks, and neither was visited, so a record local declared in
        // one of them was lowered with `->` instead of `.`. *Two registers over the same
        // thing run apart* (W7); `crate::unterbloecke` is the one register, and it matches
        // over `StmtArt` without a catch-all arm.
        for k in crate::unterbloecke(s) {
            verbundlokale(k, u, aus);
        }
    }
}

/// **Liefert dieser Ausdruck einen VERBUNDWERT?** -- abgelesen aus der Deklaration des
/// Gerufenen, nicht geraten.
///
/// Dieselbe Quelle wie `wert_ctyp`: der erklaerte Rueckgabetyp. *Zwei Register ueber
/// derselben Sache laufen auseinander* (W7) -- und genau das war der Fehler, den diese
/// Funktion schliesst.
fn verbundwert(e: &Expr, u: &Namen) -> bool {
    match &e.art {
        ExprArt::Klammer(x) => verbundwert(x, u),
        ExprArt::Ruf(r) => {
            let Some(n) = r.path().and_then(|p| p.teile.last()) else { return false };
            // **Ein Verbundkonstruktor ist kein Ruf** («B7»): `Completion(id: …)` nennt den
            // Typ selbst.
            if u.verbunde.contains(&n.text) {
                return true;
            }
            match u.funktionen.get(&n.text).and_then(|s| s.rueck.as_ref()) {
                Some(TypExpr::Pfad(p)) => p
                    .teile
                    .last()
                    .is_some_and(|x| u.verbunde.contains(&x.text)),
                _ => false,
            }
        }
        _ => false,
    }
}

/// **The brace initialiser of a LABELLED CALL, for a `static` of that record** (2026-08-25).
///
/// `Some("{ .a = 1, .b = 2 }")` exactly when `e` is the labelled call of the record `verbund`
/// itself. Everything else is `None` -- **including a call that returns such a record**: a
/// function call is not a constant expression, and C11 6.7.9p4 requires one at file scope.
/// *The distinction is the same one `verbundwert` draws, and it is drawn here again because
/// the answer differs: an expression position takes the call, an initialiser does not.*
///
/// The template is `S19 verbund.konstruktor` (proved 2026-08-17) -- the same one `emit::ruf`
/// already rests on. **No new register entry, and `L` does not move.**
fn verbundmarken(e: &Expr, verbund: &str, u: &Namen, absagen: &mut Absagen) -> Option<String> {
    match &e.art {
        ExprArt::Klammer(x) => verbundmarken(x, verbund, u, absagen),
        ExprArt::Ruf(r) if r.ist_verbundwert() => {
            // The record it constructs must be the record that was declared. `static mut x : A
            // = B(f: 1)` is not a lowering question -- it is a type error, and M1 owns it.
            if r.path().and_then(|p| p.teile.last()).map(|n| n.text.as_str()) != Some(verbund) {
                return None;
            }
            let felder: Vec<String> = r
                .marken
                .iter()
                .zip(r.argumente.iter())
                .map(|(m, a)| feldsetzer(verbund, m, a, u, absagen))
                .collect();
            Some(format!("{{ {} }}", felder.join(", ")))
        }
        _ => None,
    }
}

/// **A `section` name goes into C between quotes, and Gabbro escapes nothing** (`D6`,
/// 2026-09-03).
///
/// The lexer's `string` rule is *quote { char } quote* with *char = any character except
/// quote and newline* (`L006`), so a backslash inside one is an ordinary character and means
/// nothing. **In C it means the opposite.** A name ending in a backslash, copied through
/// unchanged, became
///
/// ```text
/// static uint64_t x __attribute__((section("a\"))) __attribute__((unused)) = 0;
/// ```
///
/// -- the backslash escapes the closing quote, the string runs on, and `cc` says *missing
/// terminating quote character*. That is `beispiele/gift/646`, and the note beside
/// `kommentartext` a few hundred lines down had said in so many words that this channel was
/// never open, because a Gabbro string cannot hold a quote. **It was open by one character
/// nobody had thought of.**
///
/// ESCAPING WAS THE SMALLER CHANGE AND IT IS NOT THE ANSWER
/// -------------------------------------------------------
/// Doubling the backslash makes the C legal and hands the ASSEMBLER a section whose name
/// ends in one. GCC emits that name into a `.section` directive **unquoted**, so a
/// backslash, a comma, a quote or a space in it breaks that line instead -- measured on the
/// same day as three further shapes of this one slot: an empty name and a blank one reach
/// the assembler, which answers *missing name*; Gabbro's own doubling form for an embedded
/// quote lands as *junk at end of line*; a NUL draws *null characters preserved in
/// literal*. **Escaping moves the failure one tool further out, to the tool fewer
/// instruments look at** -- `tests/beispiele.rs` stops at `-fsyntax-only` and would never
/// see it again.
///
/// So the name is held to what a section name can BE: at least one character, and each of
/// them a letter, a digit, or one of `. _ - $`. That is the set the linker's own sections
/// live in (`.text`, `.data.rel.ro`, `.init_array.65535`, `.gnu.linkonce.t.foo`), and it is
/// the set the corpus uses -- **two `section` declarations in 612 files, both `.rodata`**.
///
/// > *A wider set could be argued for and none of it is asked for.* Rule A: the narrow one
/// > is what has a witness, and the refusal says exactly which character it stopped at, so
/// > widening it later is a one-line change with a reason attached.
fn abschnitt_attribut(st: &StatischDecl, absagen: &mut Absagen) -> String {
    let Some(t) = &st.section else { return String::new() };
    let schlecht = t
        .text
        .chars()
        .find(|c| !(c.is_ascii_alphanumeric() || matches!(c, '.' | '_' | '-' | '$')));
    match schlecht {
        None if !t.text.is_empty() => format!(" __attribute__((section(\"{}\")))", t.text),
        _ => {
            weigere(
                absagen,
                t.span,
                &format!(
                    "a `section` name that cannot be one -- {}. The name is copied into a C \
                     string literal and from there into an unquoted assembler directive; \
                     letters, digits and `. _ - $` are what survives both",
                    match schlecht {
                        Some(c) => format!("`{}` is not a name character", c.escape_debug()),
                        None => "it is empty".to_string(),
                    }
                ),
            );
            String::new()
        }
    }
}

/// The `const` prefix and the `section` attribute of a `static` -- **the record case only**,
/// where the C type can never end in `*` and the pointer/target distinction below does not
/// arise.
fn statischer_kopf(st: &StatischDecl, absagen: &mut Absagen) -> (&'static str, String) {
    let konst = if st.veraenderlich { "" } else { "const " };
    let abschnitt = abschnitt_attribut(st, absagen);
    (konst, abschnitt)
}

/// Ist `t` ein Zeiger auf einen Pfad, den diese Einheit nicht aufloest? Dann traegt sie
/// seinen Namen, aber nicht sein Layout -- und C hat dafuer bereits eine Form.
fn fremdes_ziel(t: &TypExpr, u: &Namen) -> Option<String> {
    let TypExpr::Zeiger(z) = t else { return None };
    if ctyp(&z.ziel, u).is_some() {
        return None;
    }
    match &z.ziel {
        TypExpr::Pfad(p) => Some(p.teile.last()?.text.clone()),
        _ => None,
    }
}

/// What must be known about a callee in order to erase a ghost **at the call site**.
#[derive(Clone)]
struct Signatur {
    /// Per parameter: is it a ghost? A ghost argument is dropped from the C call.
    geist_param: Vec<bool>,
    /// Does it return a ghost? Then `let x = f(…)` loses its binding, **not its call**.
    geist_rueck: bool,
    /// Returns `option index into T`? Then the table name, for the sentinel comparison.
    option_rueck: Option<String>,
    /// `-> never`. Ein `on_exceeded` darf nur auf so eine Funktion zeigen.
    nie_rueck: bool,
    /// **Der erklaerte Rueckgabetyp.** `wert_ctyp` las bis zum 2026-08-20 jeden Ort und jede
    /// Rechnung ab und **einen Ruf nicht** -- der Typ steht in der Deklaration des Gerufenen
    /// und war die einzige der drei Quellen, die niemand fragte.
    rueck: Option<TypExpr>,
    /// **`-> T or R`: der Name des `reason`.** Wer einen Fehlerkanal hat, hat eine ANDERE
    /// C-Signatur -- `bool f(T *_wert, R *_grund)` -- und ein Ruf ausserhalb eines
    /// `let … else` waere derselbe Name mit der falschen Stelligkeit.
    fehler: Option<String>,
}

/// Ein Geraet, so wie der Erzeuger es braucht.
#[derive(Clone)]
struct Geraet {
    /// Registername -> (Versatz, C-Wortbreite).
    reg: HashMap<String, (i128, String)>,
    /// **The declared space -- and until 2026-09-02 it stood here NOT, with a reason that
    /// has since expired.**
    ///
    /// The line that stood above `reg` said: *"the space is not here -- `geraet` reads it
    /// straight from the tree, and a second field beside it would be the second register
    /// over one thing (W7)."* That was true while every space this emitter lowered used the
    /// SAME access form: a `volatile` load at `basis + offset`. Then only the item walk
    /// needed the word, and the item walk holds the `Device` node.
    ///
    /// **`at port` breaks that.** The access form now differs by space, and the sites that
    /// decide it -- `ort`, the assignment branch, `uebergang` -- are handed a NAME and this
    /// map, never the node. Reading the tree again from there would mean resolving the
    /// device declaration a second time at every access site.
    ///
    /// > *It is still one register, not two.* The map is filled from `Device::raum` in
    /// > `sammle` and from nowhere else; `geraet` keeps reading the node because it has it.
    /// > W7 is about two SOURCES for one fact, and there is one.
    raum: Raum,
    /// **Registername -> der erklaerte Umlauf** («B32»). Ein `reg X : u16 wrapping` traegt
    /// dieselbe Aussage wie ein umlaufender Slot, und dieselbe Falle: `X = X * X` hebt beide
    /// Seiten auf `int` und laeuft dort UNDEFINIERT ueber.
    umlaeufer: HashMap<String, IntTy>,
    /// Registername -> Feldname -> (hoechstes Bit, niedrigstes Bit, Registerbreite in Bit).
    felder: HashMap<String, HashMap<String, (u32, u32, u32)>>,
    /// Registername -> die erklaerte Zugriffsklasse. **Sie entscheidet, ob ein Bitfeld
    /// ueberhaupt geschrieben werden DARF:** ein Lese-Aendere-Schreibe braucht eine Lesung,
    /// und ein `class w` gibt keine her -- das ist Falle 4, und ihre Antwort heisst
    /// `transition` mit `mirrors`.
    klassen: HashMap<String, RegKlasse>,
    /// **Register name -> the FALSIFIER of its `requires`** («B26», 2026-08-28).
    ///
    /// `(condition, reason type, reason value)`. Present exactly when the declaration carries
    /// `requires <pred> else <R>::<case>` -- and then the READ of that register is fallible
    /// and lowers through `fehlbare_lesung`. Absent means the clause is a counted obligation
    /// and nothing else, which is the state «B26» stood in until today.
    fehlbar: HashMap<String, (Pred, String, String)>,
    /// **The declared parameters BEYOND the base address -- name and C type** (2026-08-25).
    ///
    /// `Device::parameter` was parsed (`ast.rs`:1488) and read by `emit.rs` NOWHERE. So
    /// `device Virtq(base : Iova, n : u16 in 1 .. QMAX) at dma` handed the generator a `n`
    /// it never saw, and `let platz = q.AVAIL_IDX % q.n;` refused with *`let` without a
    /// resolvable type* -- a refusal whose stated reason (`let`) was not the real one
    /// (`q.n`).
    ///
    /// > *A clause that parses and is dropped* -- the same shape as `RegDecl::requires`
    /// > before 2026-08-24, and as `OrtSchritt::von`, which no line reads to this day.
    ///
    /// The FIRST parameter is the address and becomes `basis`; it is not in this list.
    parameter: Vec<(String, String)>,
    /// **Bank name -> its register names** (2026-08-26).
    ///
    /// A bank lowers to ACCESSOR FUNCTIONS, because its base may only be known at run time
    /// (`bank FRR at CAP.FRO * 16`). They were emitted and **nothing generated ever called
    /// them**: `q.USED_RING[s].id` lowered to `q->USED_RING[s].id`, a struct field that does
    /// not exist. *`pruefe` 0 errors, `emit` 0 refusals, and `cc` finds it.*
    ///
    /// > No differential test caught this, and the reason is exact: the only pierced unit
    /// > with a bank (`F02`) reads it from the **C driver**, which calls the accessors. **A
    /// > generated interface that only a hand-written caller uses is not measured by its
    /// > own corpus.**
    baenke: HashMap<String, BTreeSet<String>>,
    /// **Bank name -> register name -> field name -> (highest bit, lowest bit, register
    /// width in bits)** -- `D19`, found 2026-09-03 by the SAME shape as the comment above,
    /// one suffix longer.
    ///
    /// `felder` above is filled from `d.register` only -- a bank's OWN `RegDecl` list
    /// (`Bank::register`) was never walked for its bit ranges, so `d.F[i].X.A` had nowhere
    /// to look up `A`. `ort` fell through past the `suffixe.len() == 3` branch (one suffix
    /// too many) to the generic struct-field lowering, and wrote `d->F[i].X.A` -- a field
    /// access into a `typedef struct { volatile uint8_t *basis; } D;`, which has neither
    /// `F`, `X` nor `A`. **`pruefe` 0 errors, `emit` 0 refusals, `cc` says `'D' has no
    /// member named 'F'`.** *The exact fault line `baenke`'s own comment already named, one
    /// level down.*
    bankfelder: HashMap<String, HashMap<String, HashMap<String, (u32, u32, u32)>>>,
}

/// **Is this type a ghost — i.e. does it vanish in the C?**
///
/// This is the one question that separates an erasure from a lowering, and getting it wrong is
/// silent in both directions: erase too much and the C computes something else; erase too
/// little and it does not compile.
fn ist_geist(t: &TypExpr, u: &Namen) -> bool {
    match t {
        TypExpr::Pfad(p) => p
            .teile
            .last()
            .is_some_and(|i| u.geister.iter().any(|g| *g == i.text)),
        _ => false,
    }
}

/// **The licence notice, and it is not decoration.**
///
/// `LIZENZ-ZUSATZ.md` grants an additional permission under AGPL §7 -- *what you write in
/// Gabbro is not a derived work* -- and ties it to one condition: generated C carries this
/// header. **The compiler writes it itself**, because a condition that depends on the user
/// remembering it is not a condition.
pub const KOPF: &str = "\
/* Generated by Gabbro -- https://github.com/SimonVitzethum/Gabbro
 *
 * This file was generated. Edit the .gab source, not this file.
 *
 * Gabbro is AGPL-3.0 with an additional permission: this generated file and the program it
 * belongs to are NOT a derived work of Gabbro. You may remove this notice -- keeping it is a
 * condition only where the result is presented as formally verified or secure, because a proof
 * claim whose origin cannot be looked up is a claim nobody can check. See LIZENZ-ZUSATZ.md.
 */
#include <stdint.h>
#include <stdbool.h>
#include <stdatomic.h>
#include <math.h>
/* The shift and conversion this generator relies on are implementation-defined in C11 --
 * so the prelude pins them (PLAN-BITS.md section 5b), on EVERY unit, float or not.
 * Two's complement itself is the language's own rule and needs no probe. */
_Static_assert((-1 >> 1) == -1, \"arithmetic right shift\");
_Static_assert((int)0xFFFFFFFFu == -1, \"modular conversion\");
";

/// **«F»: der Zusatz, wenn eine Einheit mit Gleitkomma rechnet.**
///
/// Er steht im erzeugten C und nicht bloss in einem Memo, weil er den Uebersetzer betrifft
/// und nicht den Leser. *Ein `-ffast-math` macht jede Aussage dieses Prueferlaufs ungueltig:
/// es erlaubt Umsortierungen, und Gleitkommaaddition ist nicht assoziativ.*
pub const KOPF_GLEITKOMMA: &str = "\
/* This unit computes in floating point.
 *
 *   -ffast-math is FORBIDDEN. It permits reassociation, and addition is not associative --
 *   every bound the checker computed falls with it. Build with `-ffp-contract=off`.
 *
 *   On x86, SSE2 is presupposed (the x87 registers compute at 80 bits and round twice).
 *   That stands in the certificate as an assumption, with its falsifier.
 *
 *   The rounding mode is round-to-nearest-even. It is global state (MXCSR/FPCR); that it
 *   holds is an assumption, never a promise of this generator.
 */
#include <float.h>
/* No `#pragma STDC FP_CONTRACT OFF`: `#pragma` is on the C-form census's NEVER list
 * (`instrumente/zaehle-c-formen.py`), GCC does not implement it, and it carries nothing
 * the build does not already carry -- `-ffp-contract=off` is binding in the manifest for
 * every compiler, and the probe `instrumente/sonde-fma.c` PROVES it at build time
 * (PLAN-BITS.md section 5). */
/* No excess precision anywhere, x86_64 included: `__FLT_EVAL_METHOD__` is 0 by default
 * and 2 under `-mfpmath=387` or `-m32` -- flags somebody may set for unrelated reasons.
 * `== 0` also excludes `-1` (indeterminable). This replaces the prose SSE2 assumption. */
_Static_assert(FLT_EVAL_METHOD == 0, \"FLT_EVAL_METHOD == 0 (no excess precision)\");
";

/// **«F»: benutzt diese Uebersetzungseinheit ueberhaupt Gleitkomma?**
///
/// Syntaktisch beantwortet, ueber die Typausdruecke -- *eine Frage an den Baum, keine an den
/// Pruefer.* Sie muss auch dann stimmen, wenn M1 geschwiegen hat.
fn rechnet_mit_gleitkomma(baum: &Programm) -> bool {
    fn im_typ(t: &TypExpr) -> bool {
        match t {
            TypExpr::Float(_) => true,
            TypExpr::Feld(a) => im_typ(&a.element),
            TypExpr::Zeiger(z) => im_typ(&z.ziel),
            TypExpr::Verbund(fs, _) => fs.iter().any(|f| im_typ(&f.typ.typ)),
            _ => false,
        }
    }
    let mut ja = false;
    crate::fuer_jedes_item(baum, &mut |item| match &item.art {
        ItemArt::Konst(k) => ja |= im_typ(&k.typ),
        ItemArt::Statisch(st) => ja |= im_typ(&st.typ),
        ItemArt::Typ(t) => {
            if let Some(r) = &t.rumpf {
                ja |= im_typ(r);
            }
        }
        ItemArt::Funktion(f) => {
            ja |= f.parameter.iter().any(|p| im_typ(&p.typ));
            ja |= f.ergebnis.as_ref().is_some_and(im_typ);
        }
        // **A `syscall` declares parameter and result types like an `fn`.**
        ItemArt::Syscall(s) => {
            ja |= s.parameter.iter().any(|p| im_typ(&p.typ));
            ja |= s.ergebnis.as_ref().is_some_and(im_typ);
        }
        ItemArt::Accumulates(a) => ja |= im_typ(&a.typ),
        // **Zwei Traeger, die der Sammelzweig verschwiegen hat** (2026-08-21): ein
        // `table T { slot { g : f64, } }` und ein `format F { x : f32, }` rechnen mit
        // Gleitkomma, und die Ansage stand nicht im Erzeugnis. *Die Ansage ist keine
        // Verzierung* -- sie sagt dem Uebersetzer `-ffast-math ist verboten` und dem
        // Kerneleser, dass diese Einheit FPU-Zustand anfasst. **Eine Aussage, die fehlt,
        // ist keine schwaechere Aussage, sondern gar keine.**
        ItemArt::Tabelle(t) => {
            if let Some(slot) = &t.slot {
                for f in &slot.felder {
                    if let SlotTyp::Typ(x) = &f.typ {
                        ja |= im_typ(x);
                    }
                }
            }
            ja |= t.konstanten.iter().any(|k| im_typ(&k.typ));
        }
        // **«E4»:** the element type decides whether this unit touches the
        // FPU -- like a slot field above, and for the same `-ffast-math`
        // reason.
        ItemArt::Arena(a) => {
            ja |= im_typ(&a.element);
        }
        ItemArt::Format(f) => ja |= f.felder.iter().any(|x| im_typ(&x.typ.typ)),
        // **Und die Traeger, die KEINEN Gleitkommatyp fuehren koennen -- einzeln, mit dem
        // Grund.** Ein Register ist ein Wort fester Breite (`intty`), eine `reason` eine
        // Aufzaehlung, ein `atomic` traegt eine Ganzzahl, und die uebrigen erklaeren
        // ueberhaupt keinen Typ, sondern eine Beziehung, eine Annahme oder eine Naht.
        //
        // *Der Sammelzweig hatte fuer diese dieselbe Antwort und keinen Grund* -- und darum
        // fielen die zwei darueber genauso durch wie sie.
        ItemArt::Modul(_)
        | ItemArt::Use(_)
        | ItemArt::Device(_)
        | ItemArt::Reason(_)
        | ItemArt::State(_)
        | ItemArt::Assume(_)
        | ItemArt::Axiom(_)
        | ItemArt::Check(_)
        | ItemArt::Atomic(_)
        | ItemArt::Lock(_)
        | ItemArt::Rcu(_)
        | ItemArt::Gruppe(_)
        | ItemArt::Walk(_)
        | ItemArt::Entry(_)
        | ItemArt::Entrust(_)
        | ItemArt::Boot(_)
        // **«E6»: a profile block carries modes and references, never a
        // float type.** Keys and `assume` names, like the assumptions above.
        | ItemArt::Profil(_)
        | ItemArt::ProfilBedarf(_)
        | ItemArt::Concurrent(_) => {}
    });
    ja
}

/// **The two tree-only maps the syscall stub lowering reads.**
///
/// Collected once per emission in `emittiere_mit`, before any lowering runs:
/// source order is free, so a `reason` may stand after the `syscall` that
/// decodes into it. Both maps are keyed by BARE name, exactly like
/// `Namen::funktionen` -- and a collision answers the same way: last wins
/// for the module, loud refusal for two different case lists.
#[derive(Default)]
struct SyscallTabellen {
    /// Bare syscall name -> the module it stands in (for `konst_wert`).
    module: HashMap<String, String>,
    /// Bare reason name -> its cases with declared numbers (for decoding).
    gruende: HashMap<String, Vec<(String, u128)>>,
    /// Bare reason names declared twice with DIFFERENT case lists.
    strittig: BTreeSet<String>,
}

/// Emits C for a tree, or refuses by name.
/// **The shipping build.** A `when TESTBUILD` item produces no line of C.
///
/// This is the signature every caller had before the gate existed, and it keeps the SAFE
/// value: whoever forgets the build loses check code out of a check build, which is loud.
/// The other default would ship it, which is silent.
pub fn emittiere(baum: &Programm, absagen: &mut Absagen) -> String {
    emittiere_mit(baum, absagen, crate::gatter::Bau::Auslieferung)
}

/// **The generator, with the build named.**
///
/// The gate is a FILTER IN FRONT of the emitter, not a branch inside it: `ohne_gatter`
/// hands over a tree the gated items are not in, and the twenty walks below cannot forget
/// them one at a time. *Same reason the ghost erasure lives in `ist_geist` and not at the
/// three sites that would each have had to remember it.*
///
/// **And it means a gated item is never held against `C001`.** It produces no C, so whether
/// the emitter could lower it is not a question about the artefact. In the CHECK build it
/// is one again, and there the refusal comes.
pub fn emittiere_mit(
    baum: &Programm,
    absagen: &mut Absagen,
    bau: crate::gatter::Bau,
) -> String {
    let gefiltert;
    let baum = match bau {
        crate::gatter::Bau::Auslieferung => {
            gefiltert = crate::gatter::ohne_gatter(baum);
            &gefiltert
        }
        crate::gatter::Bau::Pruefbau => baum,
    };
    let mut namen = Namen::default();
    namen.opsgerufen = crate::opsruf::gerufene(baum);
    // **Lane 197, beside the emitter:** the two lists the deeds walker reads
    // (`welt_und_konstanten`, the same call the checker makes), so an omitted
    // `effects` over a call-free body earns the attribute its deeds earn.
    let (welt_konstanten, welt_namen) = crate::wirkungen::welt_und_konstanten(baum);
    namen.welt_konstanten = welt_konstanten;
    namen.welt_namen = welt_namen;
    // **The syscall stub tables (lane S6).** Two tree-only maps the stub
    // lowering reads: which module each `syscall` stands in (for folding
    // `number` and result bounds through `Umgebung::konst_wert`), and the
    // `reason` case numbers the errno decoding compares against. Both stand
    // on the PARSED tree and never consult the passes, like every refusal
    // in this file -- a second `syscall` with the same bare name in another
    // module is last-wins here, exactly as in `Namen::funktionen` below.
    let mut syscall_tabellen = SyscallTabellen::default();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        if let ItemArt::Syscall(s) = &item.art {
            syscall_tabellen
                .module
                .insert(s.name.text.clone(), modul.to_string());
        }
    });
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Reason(r) = &item.art {
            let faelle: Vec<(String, u128)> = r
                .faelle
                .iter()
                .map(|f| (f.name.text.clone(), f.wert))
                .collect();
            match syscall_tabellen.gruende.get(&r.name.text) {
                // **One name, one case list -- the same rule `funktion` keeps
                // for prototypes.** Two same-named `reason` declarations with
                // the same cases share one C `enum` anyway; with different
                // ones the decoding could not pick a number, so the name is
                // marked and the stub refuses it loudly at its own site.
                None => {
                    syscall_tabellen.gruende.insert(r.name.text.clone(), faelle);
                }
                Some(vorher) if *vorher == faelle => {}
                _ => {
                    syscall_tabellen.strittig.insert(r.name.text.clone());
                }
            }
        }
    });
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Tabelle(t) = &item.art {
            for k in crate::opsruf::koepfe(t) {
                namen.opsnamen.insert(k.pfad());
            }
        }
    });
    // **Lane E5: the accepted library calls, collected before any body
    // lowers.** The lowering arms read `nutzlast_einsaetze`, and bodies
    // lower in the item gang far below -- filling the map beside the
    // tables would be too late. The payload C name is a pure function of
    // the call site (function name plus call span, unique per call), so
    // the statics gang below recomputes the same names deterministically.
    for e in crate::uebersetzung::einsaetze(baum) {
        let pl = format!("{}__nutzlast_{}_{}", e.funktion, e.von, e.bis);
        namen.nutzlast_einsaetze.insert(
            (e.von, e.bis),
            (e.funktion.clone(), e.tabelle.clone(), pl),
        );
    }
    crate::fuer_jedes_item(baum, &mut |item| match &item.art {
        ItemArt::Konst(k) => {
            namen.konstanten.insert(k.name.text.clone());
        }        ItemArt::Format(f) => {
            namen.formate.insert(f.name.text.clone());
            // **The reader set, and it is built by the SAME condition `format_` lowers by.**
            // One rule, read twice: a field gets `{Format}_{field}` exactly when it is not
            // `reserved`. Any other spelling here would be a second opinion about the
            // emitter's own output.
            namen.formatfelder.insert(
                f.name.text.clone(),
                f.felder
                    .iter()
                    .filter(|g| !g.reserviert)
                    .map(|g| g.name.text.clone())
                    .collect(),
            );
        }
        ItemArt::Device(d) => {
            // **Collected by the BARE name, with no module qualifier anywhere in this
            // struct** (2026-09-03, `zaehle-karten.py`). Two `device` declarations that
            // share a short name in two different `module` blocks check CLEAN --
            // `Umgebung::geraete` keys them apart, `q(&d.name.text)` -- but this map does
            // not, and the second one collected silently overwrote the first's entry.
            //
            // *Measured, not guessed:* two modules, each a `device Foo(basis: u16) at
            // port { reg R: u8 @… }` at a DIFFERENT offset, checked with `0 errors` and
            // then emitted `Foo_R_in`/`Foo_R_out` TWICE, both copies at the SECOND
            // device's offset -- the first device's own accessor read and wrote the
            // WRONG port, silently, with the checker having said nothing was wrong.
            //
            // A full fix threads a module path through every reader of this struct, not
            // only `geraete`; short of that rewrite, a named refusal is the one thing
            // this file never trades away for a guess (see `weigere`, above).
            if namen.geraete.contains_key(&d.name.text) {
                weigere(
                    absagen,
                    d.name.span,
                    &format!(
                        "two `device` declarations named `{}` in this unit -- the C name \
                         `{}` has room for one, and the emitter's device table is keyed by \
                         this bare name with no module qualifier. Picking one silently would \
                         make every register and port access against the OTHER a silent \
                         misread instead of the compile error two same-named devices need",
                        d.name.text, d.name.text
                    ),
                );
            }
            namen.geraete.insert(
                d.name.text.clone(),
                Geraet {
                            reg: HashMap::new(),
                            raum: d.raum.clone(),
                            felder: HashMap::new(),
                            umlaeufer: HashMap::new(),
                            klassen: HashMap::new(),
                            fehlbar: d
                                .register
                                .iter()
                                .chain(d.baenke.iter().flat_map(|b| b.register.iter()))
                                .filter_map(|r| {
                                    let pred = r.requires.clone()?;
                                    let (g, f) = r.requires_grund.clone()?;
                                    Some((
                                        r.name.text.clone(),
                                        (
                                            pred,
                                            g.text.clone(),
                                            format!("{}_{}", g.text, f.text),
                                        ),
                                    ))
                                })
                                .collect(),
                            // The first parameter is the base address -- `skip(1)`. A
                            // parameter whose type this unit cannot lower is DROPPED here
                            // and the constructor refuses by name below, rather than
                            // emitting a struct field of a type nobody wrote.
                            baenke: d
                                .baenke
                                .iter()
                                .map(|b| {
                                    (
                                        b.name.text.clone(),
                                        b.register.iter().map(|r| r.name.text.clone()).collect(),
                                    )
                                })
                                .collect(),
                            // **`D19`.** The same walk as `felder` below, over `Bank::register`
                            // instead of `Device::register` -- a register this unit cannot
                            // lower (`breite_von` fails) is skipped, the same silence the
                            // top-level walk already keeps, and `ort`'s new branch below
                            // refuses by name when a lookup here comes back empty.
                            bankfelder: d
                                .baenke
                                .iter()
                                .map(|b| {
                                    (
                                        b.name.text.clone(),
                                        b.register
                                            .iter()
                                            .filter_map(|r| {
                                                let breite = breite_von(&r.typ)? * 8;
                                                let mut f = HashMap::new();
                                                // `u32::try_from` and not `as` -- a bit
                                                // position past `u32::MAX` saturates to
                                                // `u32::MAX` here rather than wrapping
                                                // silently, and `D15`'s `u128` mask
                                                // arithmetic downstream is already fenced
                                                // against exactly that value.
                                                for (name, lage, _) in &r.felder {
                                                    let tou32 =
                                                        |v: &u128| u32::try_from(*v).unwrap_or(u32::MAX);
                                                    let (hi, lo) = match lage {
                                                        BitPos::Bit(bp) => (tou32(bp), tou32(bp)),
                                                        BitPos::Bereich(h, l) => (tou32(h), tou32(l)),
                                                    };
                                                    f.insert(name.text.clone(), (hi, lo, breite));
                                                }
                                                Some((r.name.text.clone(), f))
                                            })
                                            .collect(),
                                    )
                                })
                                .collect(),
                            parameter: d
                                .parameter
                                .iter()
                                .skip(1)
                                .filter_map(|pa| {
                                    Some((pa.name.text.clone(), ctyp(&pa.typ, &namen)?))
                                })
                                .collect(),
                        },
            );
            for x in &d.uebergaenge {
                namen.uebergaenge.insert(x.name.text.clone(), d.name.text.clone());
            }
        }
        ItemArt::Tabelle(t) => {
            namen.tabellen.push(t.name.text.clone());
            if let Some(b) = &t.baum {
                namen.baeume.insert(
                    t.name.text.clone(),
                    (
                        b.elter.as_ref().map(|i| i.text.clone()),
                        b.kind.as_ref().map(|i| i.text.clone()),
                        b.geschwister.as_ref().map(|i| i.text.clone()),
                    ),
                );
            }
        }
        ItemArt::Accumulates(ac) => {
            namen.akkus.insert(ac.name.text.clone());
        }
        // **«E4»:** the arena declares a name every lowering looks up --
        // the storage (`A_arena_speicher`), the buffer, the bound. The
        // `hi` expression and the element type travel with it, so the
        // declaration arm and the statement arms read one map.
        ItemArt::Arena(a) => {
            namen
                .arenen
                .insert(a.name.text.clone(), (a.hi.clone(), a.element.clone()));
        }
        ItemArt::Atomic(a) => {
            // (Speichern, Laden) -- die Deklaration nennt die Speicherseite.
            // **Written out, because the catch-all here decided a MEMORY MODEL by
            // default.** `_ => relaxed` covered the declared `relaxed` and the missing
            // clause -- both right today -- and would have covered a fifth ordering as well,
            // silently and with the weakest of them all. *A wrong memory order is the one
            // defect that does not show up in a test run; it shows up on another machine.*
            let (sp, ld) = match a.ordnung {
                Some(Ordnung::Release) => ("memory_order_release", "memory_order_acquire"),
                Some(Ordnung::Acquire) => ("memory_order_release", "memory_order_acquire"),
                Some(Ordnung::Seq) => ("memory_order_seq_cst", "memory_order_seq_cst"),
                // `atomic x : u32 publishes nothing relaxed;` -- the load-free counter.
                Some(Ordnung::Relaxed) => ("memory_order_relaxed", "memory_order_relaxed"),
                // **No clause at all is `relaxed`, and that is a decision, not an absence.**
                // The declaration promises nothing about visibility, so the emitter must
                // not promise anything either -- anything stronger would be a guarantee the
                // checker never gave.
                None => ("memory_order_relaxed", "memory_order_relaxed"),
            };
            namen.atomics.insert(a.name.text.clone(), (String::new(), sp, ld));
        }
        ItemArt::Typ(t) => {
            // **A ghost type has no body and no C.** `linear ghost type BootPhase;` declares a
            // value the checker threads and the machine never sees.
            if t.ghost {
                namen.geister.push(t.name.text.clone());
            } else if t.linear && t.rumpf.is_none() && t.parameter.is_none() {
                // **Eine Marke.** Siehe `Namen::marken`.
                namen.marken.insert(t.name.text.clone());
            } else if let Some(unter) = &t.rumpf {
                if matches!(unter, TypExpr::Verbund(f, _) if !f.is_empty()) && !t.opaque {
                    namen.verbunde.insert(t.name.text.clone());
                }
                // **«C2»: ein `tagged type` ist ein WERT und kein Bereichstyp.** Er steht
                // hier VOR `typen`, weil `ctyp` dort in den Rumpf absteigen und an
                // `TypExpr::Varianten` scheitern wuerde -- also eine Weigerung fuer einen
                // Typ, den diese Einheit gerade selbst erklaert.
                if let TypExpr::Varianten(v, _) = unter {
                    if t.tagged && !v.is_empty() {
                        namen.markierte.insert(t.name.text.clone(), v.clone());
                    }
                }
                if let TypExpr::Verbund(felder, _) = unter {
                    for f in felder {
                        namen.verbundfeld.insert(
                            (t.name.text.clone(), f.name.text.clone()),
                            f.typ.typ.clone(),
                        );
                    }
                }
                namen.typen.insert(t.name.text.clone(), unter.clone());
            }
        }
        // **Der Namensindex ist die Karte, auf der jede spaetere Absenkung nachschlaegt --
        // und ein Sammelzweig darin heisst „dieses Konstrukt steht auf keiner Karte".**
        //
        // Genau diese Klasse steht drei Bildschirme weiter unten schon aufgeschrieben: ein
        // `device` als WERTPARAMETER stand bis 2026-08-20 in keiner der beiden Karten, der
        // Erzeuger nahm den gewoehnlichen Ortspfad, und `d.ST.IDX` wurde `d->ST.IDX` -- ein
        // Feldzugriff auf etwas, das keine Felder hat. **`cc` brach ab, `C001` schwieg.**
        //
        // *Die Karte fehlt nicht laut, sie fehlt still.* Darum stehen die Traeger, die
        // NICHTS eintragen, hier einzeln: `lock`, `rcu` und `walk` tragen ihren Namen selbst
        // und werden ueber ihn gefunden; `use`, `module`, `assume`, `axiom`, `check`,
        // `group`, `reason`, `state`, `entry`, `entrust` und `boot` erklaeren keinen Namen,
        // den eine Absenkung nachschlagen muesste.
        //
        // > **Und `static` steht hier, weil `rustc` beim Ausschreiben danach gefragt hat.**
        // > Ein `static x : Verbund` traegt keinen Eintrag in `namen.werte` -- der Zugriff
        // > darauf laeuft ueber den gewoehnlichen Ortspfad. *Ob das reicht, hat vor dem
        // > Ausschreiben nie jemand gefragt, weil der Sammelzweig die Frage gar nicht
        // > stellte.* Das Verhalten bleibt; die Frage steht jetzt da.
        //
        // > **And on 2026-08-25 `reason` LEFT this list, because the sentence above was wrong
        // > about it.** It does declare a name a lowering looks up: `ItemArt::Reason` writes
        // > `typedef enum { … } R;`, and a parameter of type `R` is a parameter of a C type
        // > this unit itself defines. *The catch-all had the same answer for it as for `use`
        // > and `module` -- and gave no reason, which is precisely what this comment stands
        // > against.* Found at `F06`:134, `impl fn messen_benutzt(…, art : Stackart)`.
        ItemArt::Reason(r) => {
            namen.gruende.insert(r.name.text.clone());
        }
        ItemArt::Modul(_)
        | ItemArt::Use(_)
        | ItemArt::Funktion(_)
        | ItemArt::Statisch(_)
        | ItemArt::State(_)
        | ItemArt::Assume(_)
        | ItemArt::Axiom(_)
        | ItemArt::Check(_)
        | ItemArt::Lock(_)
        | ItemArt::Rcu(_)
        | ItemArt::Gruppe(_)
        | ItemArt::Walk(_)
        | ItemArt::Entry(_)
        | ItemArt::Entrust(_)
        | ItemArt::Boot(_)
        // **A `syscall` declares no name a lowering looks up.** Its parameter and
        // result types travel through `Umgebung`, and its own lowering
        // (`syscall_stumpf`) reads the register map straight from the tree.
        | ItemArt::Syscall(_)
        // **«E6»: a profile block declares modes and references, no name a
        // lowering looks up.** Keyed entries and `assume` references travel
        // into the manifest (`manifest::profil_und_bedarf`), never into C.
        | ItemArt::Profil(_)
        | ItemArt::ProfilBedarf(_)
        | ItemArt::Concurrent(_) => {}
    });
    // **Second pass, and it needs the first**: whether a parameter is a ghost can only be
    // decided once the ghost names are known.
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Funktion(f) = &item.art {
            // **Lane 260: which functions have a body in this unit.** Only
            // those are thread roots a `start` can name -- see `Namen`.
            if matches!(&f.rumpf, FnRumpf::Block(_)) {
                namen.impl_funktionen.insert(f.name.text.clone());
            }
            let sig = Signatur {
                geist_param: f.parameter.iter().map(|p| ist_geist(&p.typ, &namen)).collect(),
                geist_rueck: f.ergebnis.as_ref().is_some_and(|t| ist_geist(t, &namen)),
                nie_rueck: matches!(f.ergebnis, Some(TypExpr::Never(_))),
                fehler: f.fehler.as_ref().map(|i| i.text.clone()),
                rueck: f.ergebnis.clone(),
                option_rueck: match &f.ergebnis {
                    Some(TypExpr::Index { tabelle, optional: true, .. }) => {
                        Some(tabelle.text.clone())
                    }
                    _ => None,
                },
            };
            if let Some(e) = &f.ergebnis {
                namen.ergebnistyp.insert(f.name.text.clone(), e.clone());
            }
            namen.funktionen.insert(f.name.text.clone(), sig);
        }
        // **A `syscall` lowers its call sites exactly like an `extern fn`.** The
        // signature carries the same fields -- ghost flags, the `or R` channel,
        // the result -- so a `let … else` over a syscall call takes the same
        // arm as over a foreign body. The declaration itself lowers to the
        // stub (`syscall_stumpf`); this entry keeps the call lowering from
        // inventing a second refusal for the same declaration.
        if let ItemArt::Syscall(s) = &item.art {
            let sig = Signatur {
                geist_param: s.parameter.iter().map(|p| ist_geist(&p.typ, &namen)).collect(),
                geist_rueck: s.ergebnis.as_ref().is_some_and(|t| ist_geist(t, &namen)),
                nie_rueck: matches!(s.ergebnis, Some(TypExpr::Never(_))),
                fehler: s.fehler.as_ref().map(|i| i.text.clone()),
                rueck: s.ergebnis.clone(),
                option_rueck: match &s.ergebnis {
                    Some(TypExpr::Index { tabelle, optional: true, .. }) => {
                        Some(tabelle.text.clone())
                    }
                    _ => None,
                },
            };
            if let Some(e) = &s.ergebnis {
                namen.ergebnistyp.insert(s.name.text.clone(), e.clone());
            }
            namen.funktionen.insert(s.name.text.clone(), sig);
        }
    });
    // **Dritter Sammelgang: die fremden Zeigerziele.** C verlangt den Tag VOR der
    // Parameterliste -- sonst hat er nur Prototyp-Reichweite, und `-Wall` sagt das zu Recht.
    let mut fremde = BTreeSet::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Funktion(f) = &item.art {
            for p in &f.parameter {
                fremde.extend(fremdes_ziel(&p.typ, &namen));
            }
            if let Some(r) = &f.ergebnis {
                fremde.extend(fremdes_ziel(r, &namen));
            }
        }
        if let ItemArt::Tabelle(tb) = &item.art {
            if let Some(slot) = &tb.slot {
                for f in &slot.felder {
                    if let SlotTyp::Typ(ty) = &f.typ {
                        fremde.extend(fremdes_ziel(ty, &namen));
                    }
                }
            }
        }
    });
    namen.fremde = fremde;

    // **Welche Namen sind nachweislich vorzeichenlos?** Konservativ ueber alle Funktionen:
    // wer irgendwo vorzeichenbehaftet erklaert ist, faellt heraus. *Unwissen faellt nach
    // lautstark -- dann bleibt die untere Pruefung stehen und `-Wextra` meldet sich.*
    let mut ohne: BTreeSet<String> = BTreeSet::new();
    let mut mit: BTreeSet<String> = BTreeSet::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        let ItemArt::Funktion(f) = &item.art else { return };
        let mut erklaert: Vec<(&str, Option<&TypExpr>)> =
            f.parameter.iter().map(|p| (p.name.text.as_str(), Some(&p.typ))).collect();
        if let FnRumpf::Block(b) = &f.rumpf {
            // **The collector descends -- a `let` inside `traverse`/`match`/`if` counts.**
            // Measured 2026-09-03 on the IPC fastpath: `let w : u32` in a `traverse` body
            // fell out of the map, and `narrow w` then wrote `>= 0` over a `u32`, which
            // `-Werror=type-limits` rejects. Outside any loop the same line came out right
            // (`w < 1024`). *A collector that sees only the top level returns a SUBSET and
            // looks like a set* -- the same build as `sammle_lets` beside it.
            fn sammle<'a>(b: &'a Block, aus: &mut Vec<(&'a str, Option<&'a TypExpr>)>) {
                for s in &b.anweisungen {
                    if let StmtArt::Let(l) = &s.art {
                        aus.push((l.name.text.as_str(), l.typ.as_ref()));
                    }
                    for k in crate::unterbloecke(s) {
                        sammle(k, aus);
                    }
                }
            }
            sammle(b, &mut erklaert);
        }
        for (name, ty) in erklaert {
            match ty.and_then(|x| vorzeichen(x, &namen)) {
                Some(true) => ohne.insert(name.to_string()),
                _ => mit.insert(name.to_string()),
            };
        }
    });
    namen.vorzeichenlos = ohne.difference(&mit).cloned().collect();

    {
        let umg = crate::umgebung::Umgebung::sammle(baum);
        crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
            if let ItemArt::Tabelle(tb) = &item.art {
                if let Some(k) = &tb.kapazitaet {
                    if let Some(n) = umg.konst_wert(modul, k) {
                        namen.kapazitaet.insert(tb.name.text.clone(), n);
                    }
                }
            }
            // **Der Wert eines `const` kommt aus `umgebung.rs`, nicht aus einem zweiten
            // Auswerter hier.** `u64::max` war dort seit jeher eine Zahl; der Erzeuger
            // weigerte sich trotzdem, weil `konst_zahl` nur Literale kennt. *Das schwaechere
            // von zwei Registern ueber derselben Sache hat entschieden* (W7).
            if let ItemArt::Konst(k) = &item.art {
                if let Some(n) = umg.konst_wert(modul, &k.wert) {
                    namen.konstwert.insert(k.name.text.clone(), n);
                }
            }
        });
    }
    // Die Parametertypen, konservativ: wer irgendwo anders erklaert ist, faellt heraus.
    {
        let mut eindeutig: HashMap<String, TypExpr> = HashMap::new();
        let mut strittig: BTreeSet<String> = BTreeSet::new();
        crate::fuer_jedes_item(baum, &mut |item| {
            let ItemArt::Funktion(f) = &item.art else { return };
            for p in &f.parameter {
                match eindeutig.get(&p.name.text) {
                    Some(vorher) if typtext(vorher) != typtext(&p.typ) => {
                        strittig.insert(p.name.text.clone());
                    }
                    _ => {
                        eindeutig.insert(p.name.text.clone(), p.typ.clone());
                    }
                }
            }
        });
        for s in &strittig {
            eindeutig.remove(s);
        }
        namen.parametertyp = eindeutig;
    }

    {
        let umg = crate::umgebung::Umgebung::sammle(baum);
        crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
            if let ItemArt::Device(d) = &item.art {
                let mut reg = HashMap::new();
                let mut felder: HashMap<String, HashMap<String, (u32, u32, u32)>> =
                    HashMap::new();
                let mut umlaeufer = HashMap::new();
                let mut klassen = HashMap::new();
                for r in &d.register {
                    // **A register word this emitter cannot lower is not collected**, and
                    // `geraet` refuses it by name a few hundred lines further down. Skipping
                    // here records NOTHING -- it does not put a plausible width into the map,
                    // which is the whole difference to the `_ => 8` that stood in
                    // `breite_von`.
                    let (Some(c), Some(breite)) = (intty(&r.typ), breite_von(&r.typ)) else {
                        continue;
                    };
                    if let Some(v) = umg.konst_wert(modul, &r.versatz) {
                        reg.insert(r.name.text.clone(), (v, c));
                    }
                    if r.umlaufend {
                        umlaeufer.insert(r.name.text.clone(), r.typ.clone());
                    }
                    let breite = breite * 8;
                    let mut f = HashMap::new();
                    for (name, lage, _) in &r.felder {
                        let (hi, lo) = match lage {
                            BitPos::Bit(b) => (*b as u32, *b as u32),
                            BitPos::Bereich(h, l) => (*h as u32, *l as u32),
                        };
                        f.insert(name.text.clone(), (hi, lo, breite));
                    }
                    felder.insert(r.name.text.clone(), f);
                    klassen.insert(r.name.text.clone(), r.klasse);
                }
                if let Some(g) = namen.geraete.get_mut(&d.name.text) {
                    g.reg = reg;
                    g.felder = felder;
                    g.umlaeufer = umlaeufer;
                    g.klassen = klassen;
                }
            }
        });
        // Welcher Name traegt welches Geraet? Konservativ ueber alle Funktionen.
        let mut eindeutig: HashMap<String, String> = HashMap::new();
        let mut strittig: BTreeSet<String> = BTreeSet::new();
        crate::fuer_jedes_item(baum, &mut |item| {
            let ItemArt::Funktion(f) = &item.art else { return };
            for p in &f.parameter {
                let TypExpr::Zeiger(z) = &p.typ else { continue };
                let TypExpr::Pfad(pf) = &z.ziel else { continue };
                let Some(n) = pf.teile.last() else { continue };
                if !namen.geraete.contains_key(&n.text) {
                    continue;
                }
                match eindeutig.get(&p.name.text) {
                    Some(vorher) if *vorher != n.text => {
                        strittig.insert(p.name.text.clone());
                    }
                    _ => {
                        eindeutig.insert(p.name.text.clone(), n.text.clone());
                    }
                }
            }
        });
        for s in &strittig {
            eindeutig.remove(s);
        }
        namen.geraetezeiger = eindeutig;
    }

    // **Die Namen, die WERTE sind und keine Zeiger** («B7»).
    //
    // Die Absenkung eines Ortes nahm bis heute an, dass die Basis eines `place` ein
    // Zeigerparameter ist -- was sie war, solange jeder zusammengesetzte Wert von aussen kam.
    // **Ein `let c : Completion` ist der erste, der es nicht ist**, und `c->len` waere dafuer
    // schlicht falsch.
    //
    // *Der Fehler faellt bei `cc` und nicht still* -- `->` auf einem Wert ist dort ein
    // Uebersetzungsfehler, `.` auf einem Zeiger ebenso. Es ist dieselbe delegierte Weigerung
    // wie beim unvollstaendigen Zeigerziel. Trotzdem gehoert sie hier entschieden und nicht
    // dem C-Uebersetzer ueberlassen: **eine Weigerung, auf die man baut, ist eine Zusage.**
    crate::fuer_jedes_item(baum, &mut |item| {
        let ItemArt::Funktion(f) = &item.art else { return };
        let ist_verbund = |t: &TypExpr, u: &Namen| {
            matches!(t, TypExpr::Pfad(p)
                if p.teile.last().is_some_and(|n| u.verbunde.contains(&n.text)))
        };
        for p in &f.parameter {
            if ist_verbund(&p.typ, &namen) {
                namen.werte.insert(p.name.text.clone());
            }
        }
        let FnRumpf::Block(rumpf) = &f.rumpf else { return };
        let mut gefunden = Vec::new();
        verbundlokale(rumpf, &namen, &mut gefunden);
        namen.werte.extend(gefunden);
    });

    // **«C2»: welcher Name traegt welchen `tagged type`?** Konservativ ueber alle
    // Funktionen, dieselbe Bauart wie `geraetezeiger` -- *Unwissen faellt nach lautstark,*
    // und dann weigert sich das `match` statt eine Variantenmenge zu raten.
    {
        let mut eindeutig: HashMap<String, String> = HashMap::new();
        let mut strittig: BTreeSet<String> = BTreeSet::new();
        let mut merke = |name: &str, typ: &TypExpr, markierte: &HashMap<String, Vec<Variante>>| {
            let TypExpr::Pfad(p) = typ else { return };
            let Some(n) = p.teile.last() else { return };
            if !markierte.contains_key(&n.text) {
                return;
            }
            match eindeutig.get(name) {
                Some(vorher) if *vorher != n.text => {
                    strittig.insert(name.to_string());
                }
                _ => {
                    eindeutig.insert(name.to_string(), n.text.clone());
                }
            }
        };
        crate::fuer_jedes_item(baum, &mut |item| {
            let ItemArt::Funktion(f) = &item.art else { return };
            for p in &f.parameter {
                merke(&p.name.text, &p.typ, &namen.markierte);
            }
            if let FnRumpf::Block(b) = &f.rumpf {
                for s in &b.anweisungen {
                    if let StmtArt::Let(l) = &s.art {
                        if let Some(t) = &l.typ {
                            merke(&l.name.text, t, &namen.markierte);
                        }
                    }
                }
            }
        });
        for s in &strittig {
            eindeutig.remove(s);
        }
        // Ein markierter Wert ist ein WERT: sein Feldzugriff ist `.`, nicht `->`.
        namen.werte.extend(eindeutig.keys().cloned());
        namen.markenwerte = eindeutig;
    }

    {
        let mut typen: Vec<(String, String)> = Vec::new();
        let mut laengen: Vec<(String, u128)> = Vec::new();
        let mut elemtypen: Vec<(String, TypExpr)> = Vec::new();
        crate::fuer_jedes_item(baum, &mut |item| {
            if let ItemArt::Atomic(a) = &item.art {
                // **An atomic ARRAY carries its ELEMENT type in `atomics`**, because
                // that is what every access to it yields: `atomic_load_explicit(&R[i],
                // …)` has the element's type, and so has the CAS operand. The array
                // type itself appears in exactly one place, the declaration, and the
                // length below carries it there. *Storing the array type here would
                // give four arms a type none of them can use.*
                //
                // Both halves must resolve or neither is entered: a length the emitter
                // cannot fold is a size it would have to guess, and the declaration arm
                // then refuses by name (`C001`) instead of writing `[]`.
                if matches!(&a.typ, TypExpr::Feld(_)) {
                    let TypExpr::Feld(f) = &a.typ else { unreachable!() };
                    if let (Some(c), Some(n)) =
                        (ctyp(&f.element, &namen), feldlaenge_von(&a.typ, &namen))
                    {
                        typen.push((a.name.text.clone(), c));
                        laengen.push((a.name.text.clone(), n));
                        elemtypen.push((a.name.text.clone(), f.element.clone()));
                    }
                } else if let Some(c) = ctyp(&a.typ, &namen) {
                    typen.push((a.name.text.clone(), c));
                    elemtypen.push((a.name.text.clone(), a.typ.clone()));
                }
            }
        });
        for (n, c) in typen {
            if let Some(e) = namen.atomics.get_mut(&n) {
                e.0 = c;
            }
        }
        for (n, l) in laengen {
            namen.atom_arrays.insert(n, l);
        }
        // **The declared element type travels beside the C word.** Both halves
        // must resolve or neither is entered -- the same joint rule as above:
        // a declaration the emitter cannot spell in C has no exactness to read
        // either, and the fetch gate then stays silent (`None`, the loop).
        for (n, t) in elemtypen {
            namen.atomic_elem_typs.insert(n, t);
        }
    }

    // Optionfelder, Slotfeldtypen, `static`-Typen und Tabellenzeiger -- fuer `x = None`
    // und fuer jeden Ort, dessen Typ ein `option index into T` ist.
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Statisch(st) = &item.art {
            namen.statiken.insert(st.name.text.clone(), st.typ.clone());
        }
        if let ItemArt::Tabelle(tb) = &item.art {
            if let Some(slot) = &tb.slot {
                for f in &slot.felder {
                    match &f.typ {
                        SlotTyp::Typ(t) => {
                            namen
                                .slotfeld
                                .insert((tb.name.text.clone(), f.name.text.clone()), t.clone());
                        }
                        SlotTyp::Wrapping(i) => {
                            namen
                                .umlaeufer
                                .insert((tb.name.text.clone(), f.name.text.clone()), i.clone());
                        }
                    }
                }
            }
        }
    });
    {
        let mut eindeutig: HashMap<String, String> = HashMap::new();
        let mut strittig: BTreeSet<String> = BTreeSet::new();
        crate::fuer_jedes_item(baum, &mut |item| {
            let ItemArt::Funktion(f) = &item.art else { return };
            for p in &f.parameter {
                let TypExpr::Zeiger(z) = &p.typ else { continue };
                let TypExpr::Pfad(pf) = &z.ziel else { continue };
                let Some(n) = pf.teile.last() else { continue };
                if !namen.tabellen.iter().any(|x| *x == n.text) {
                    continue;
                }
                match eindeutig.get(&p.name.text) {
                    Some(v) if *v != n.text => {
                        strittig.insert(p.name.text.clone());
                    }
                    _ => {
                        eindeutig.insert(p.name.text.clone(), n.text.clone());
                    }
                }
            }
        });
        for s in &strittig {
            eindeutig.remove(s);
        }
        namen.tabellenzeiger = eindeutig;
    }

    // **Welche Tabelle wird ueber ihren eigenen NAMEN adressiert?**
    //
    // Bis zum 2026-08-19 senkte `Kappenraum.slots[s]` zu `Kappenraum->slots[s]` ab -- ein
    // Pfeil auf einen Typnamen. **Das war nicht still, sondern an `cc` delegiert**, und
    // folgenlos, solange jede solche Datei aus einem anderen Grund `C001` sagte. Mit «C3c»
    // sagt `beispiele/17` keinen mehr, und die Zeile stuende im Erzeugnis.
    //
    // *Es ist keine Sprachentscheidung:* `beispiele/09` sagt den Satz selbst -- die Tabelle
    // IST der Speicher, ihr Name der Ort. Der Erzeuger gibt ihm einen C-Namen, und der ist
    // in Gabbro unaussprechlich; entschieden wird nichts.
    {
        let mut benutzt: BTreeSet<String> = BTreeSet::new();
        crate::fuer_jedes_item(baum, &mut |item| match &item.art {
            ItemArt::Funktion(f) => {
                if let FnRumpf::Block(b) = &f.rumpf {
                    benutzte_namen(b, &mut benutzt);
                }
            }
            ItemArt::Check(c) => benutzte_namen(&c.can_fail, &mut benutzt),
            // **Die Traeger OHNE Rumpf -- einzeln, und der Grund ist bei allen derselbe:
            // nur ein `Block` kann eine Tabelle beim Namen nennen.** `unterbloecke` und
            // `benutzte_namen` laufen ueber Anweisungen; wo keine stehen, gibt es nichts zu
            // finden.
            //
            // *Zwei davon sind knapp daran vorbei:* ein `device` senkt seine `transition`
            // ab, aber ueber `d->basis` und nie ueber eine Tabelle; und ein `boot` senkt
            // `set x = <expr>` als `static const uint64_t` ab, was C zu einem
            // Konstantenausdruck zwingt -- **ein Tabellenzugriff waere dort schon kein
            // gueltiges C.** Beide sind damit ausgeschlossen und nicht bloss unbeobachtet.
            ItemArt::Modul(_)
            | ItemArt::Use(_)
            | ItemArt::Typ(_)
            | ItemArt::Konst(_)
            | ItemArt::Statisch(_)
            | ItemArt::Tabelle(_)
            // **«E4»:** the declaration names no body -- its USES do, and
            // they arrive through `benutzte_namen` above.
            | ItemArt::Arena(_)
            | ItemArt::Format(_)
            | ItemArt::Device(_)
            | ItemArt::Reason(_)
            | ItemArt::State(_)
            | ItemArt::Assume(_)
            | ItemArt::Axiom(_)
            | ItemArt::Atomic(_)
            | ItemArt::Lock(_)
            | ItemArt::Rcu(_)
            | ItemArt::Gruppe(_)
            | ItemArt::Accumulates(_)
            | ItemArt::Walk(_)
            | ItemArt::Entry(_)
            | ItemArt::Entrust(_)
            | ItemArt::Boot(_)
            // **A `syscall` names no table through a block.** Its body is the
            // machine -- the stub template (`syscall_stumpf`) reads the
            // register map, not carrier names.
            | ItemArt::Syscall(_)
            // **«E6»: a profile block names no table.** Modes and references
            // are manifest entries, not carriers.
            | ItemArt::Profil(_)
            | ItemArt::ProfilBedarf(_)
            | ItemArt::Concurrent(_) => {}
        });
        // **«B41b»: ein Baumdurchlauf ueber einem blanken Index adressiert seine Tabelle
        // ebenfalls beim Namen** (2026-08-20).
        //
        // `traverse v of g over ancestors of g` nennt `Topologie` in keiner Zeile des
        // Rumpfes -- nur im TYP von `g` und in der Wirkungsliste. `benutzte_namen` sah
        // deshalb nichts, der Speicher wurde nicht angelegt, und das Erzeugnis las
        // `Topologie_speicher`, das es nicht gab. *Ein Durchlauf ist ein Zugriff; er steht
        // nur nicht als einer da.*
        crate::fuer_jedes_item(baum, &mut |item| {
            let ItemArt::Funktion(f) = &item.art else { return };
            let FnRumpf::Block(b) = &f.rumpf else { return };
            fn im_block(b: &Block, p: &[Parameter], benutzt: &mut BTreeSet<String>) {
                for s in &b.anweisungen {
                    if let StmtArt::Schleife(sch) = &s.art {
                        if let Schleife::Traverse(t) = sch.as_ref() {
                            let o = match &t.domaene {
                                Domaene::NachfahrenVon(o) | Domaene::VorfahrenVon(o) => Some(o),
                                _ => None,
                            };
                            if let Some(o) = o {
                                if o.suffixe.is_empty() {
                                    if let Some(TypExpr::Index { tabelle, .. }) = p
                                        .iter()
                                        .find(|x| x.name.text == o.basis.text)
                                        .map(|x| &x.typ)
                                    {
                                        benutzt.insert(tabelle.text.clone());
                                    }
                                }
                            }
                        }
                    }
                    for k in crate::unterbloecke(s) {
                        im_block(k, p, benutzt);
                    }
                }
            }
            im_block(b, &f.parameter, &mut benutzt);
        });
        namen.tabellenglobal = namen
            .tabellen
            .iter()
            .filter(|t| benutzt.contains(*t) && !namen.tabellenzeiger.contains_key(*t))
            .cloned()
            .collect();
        // **«E4»:** an arena whose name no body names gets no storage --
        // the same reason as above, one map over. The names arrive through
        // `benutzte_namen` (reads name the basis, `alloc`/`reset` name the
        // arena itself), so a declaration nobody touches emits its type
        // and no object.
        namen.arenen_global = namen
            .arenen
            .keys()
            .filter(|t| benutzt.contains(*t))
            .cloned()
            .collect();
    }

    namen.retry_schranke = retry_schranken(baum);

    // **Die Wortleser werden MITERZEUGT, nicht vorausgesetzt** -- ein Erzeugnis, das eine
    // Bibliothek braucht, ist kein Erzeugnis. Und nur die gebrauchten: eine ungenutzte
    // Funktion im erzeugten C ist ein Befund ueber den Erzeuger.
    let mut leser: BTreeSet<&'static str> = BTreeSet::new();
    let mut schreiber: BTreeSet<&'static str> = BTreeSet::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Format(f) = &item.art {
            let gross = matches!(f.endian, Some(Endian::Gross));
            for feld in &f.felder {
                if let TypExpr::Int(i) = &feld.typ.typ {
                    // A word without a width collects no reader here -- `format_`
                    // refuses it by name a moment later. *Collecting nothing is not the
                    // same as collecting the next best thing.*
                    let Some(b) = breite_von(i) else { continue };
                    let (Some(l), Some(s)) = (lesewort(b, gross), schreibwort(b, gross)) else {
                        continue;
                    };
                    leser.insert(l);
                    // **Ein Achtbyteleser ist aus ZWEI Vierbytelesern gebaut**, und der
                    // Sammler kannte nur den, den ein Feld nennt. Ein `format`, dessen
                    // einziges Ganzzahlfeld `u64` ist, definiert `gabbro_le64` und ruft darin
                    // `gabbro_le32`, das nirgends steht. *Eine Abhaengigkeit zwischen zwei
                    // ERZEUGTEN Ruempfen -- der Sammler zaehlte die genannten, nicht die
                    // gebrauchten.*
                    if b == 8 {
                        leser.extend(lesewort(4, gross));
                    }
                    schreiber.insert(s);
                    if b == 8 {
                        schreiber.extend(schreibwort(4, gross));
                    }
                }
            }
        }
    });

    let mut aus = String::from(KOPF);
    // **Die Einheit sagt selbst an, dass sie mit Gleitkomma rechnet.** Der Uebersetzer muss
    // es wissen (`-ffast-math`, SSE2), und fuer einen Kernel ist es eine Aussage ueber
    // Preemption und Kontextgroesse -- nicht ueber Zahlen.
    if rechnet_mit_gleitkomma(baum) {
        aus.push_str(KOPF_GLEITKOMMA);
    }
    // **PLAN-BITS section 4 (lane 88): the saturating helpers, on demand.**
    // `needs_saturation` is a syntactic presence scan -- it cannot see signs,
    // so both helpers are emitted on `true` (the unused one silenced, like every
    // unused generated reader). Every form in them is already in the C-form
    // census; the scan is what keeps a unit that never saturates free of them.
    if needs_saturation(baum) {
        aus.push_str(SATURATION_PRELUDE);
    }
    let annahmen = crate::manifest::sammle(baum);
    namen.annahmen = annahmen.iter().map(|a| a.name.clone()).collect();
    // **Every `arch` word this unit carries, from every clause that can carry one.**
    // `at port` demands `x86_64` among them -- see `geraet`.
    crate::fuer_jedes_item(baum, &mut |item| match &item.art {
        ItemArt::Entry(e) => {
            namen.architekturen.insert(e.arch.text.clone());
        }
        ItemArt::Entrust(e) => {
            namen.architekturen.insert(e.arch.text.clone());
        }
        ItemArt::Boot(b) => {
            namen.architekturen.insert(b.arch.text.clone());
        }
        ItemArt::Funktion(f) => {
            if let Some(a) = &f.arch {
                namen.architekturen.insert(a.text.clone());
            }
        }
        ItemArt::Assume(a) => {
            if let Some(x) = &a.arch {
                namen.architekturen.insert(x.text.clone());
            }
        }
        _ => {}
    });
    if !annahmen.is_empty() {
        let (menge, _) = crate::manifest::vereinige(annahmen);
        aus.push_str("\n/* Proved under the following assumptions (SYNTAX.md 12).\n");
        aus.push_str(" * Each is a statement about the MACHINE that this program takes on\n");
        aus.push_str(" * trust. A falsifier names the probe that could refute it.\n");
        for a in &menge {
            let wie = match &a.klasse {
                crate::manifest::Klasse::Falsifizierbar { sonde } => {
                    format!("falsifier {sonde}")
                }
                crate::manifest::Klasse::NichtFalsifizierbar { grund } => {
                    format!("UNFALSIFIABLE -- {grund}")
                }
            };
            aus.push_str(&format!(
            " *   {} ({}): {}\n",
            kommentartext(&a.name),
            a.art,
            kommentartext(&wie)
        ));
            // **The side condition of an `axiom` -- the COUNT, because this channel has no
            // source** (2026-09-02). `emittiere_mit` is handed a tree and nothing else, so
            // `voraussetzung_text` is `None` here by construction and `manifest.rs` keeps
            // the two fields apart for exactly this caller: *a missing wording must not
            // read as a missing clause.*
            //
            // Printing the number is the honest half. `A1` was `rdtscp` UNDER a machine
            // feature and the header said `rdtscp` -- **and this header is what a C reader
            // gets**, the outermost surface the promise travels on. The wording stands one
            // command over, in `gabbro certificate`, which does have the source.
            if a.voraussetzungen > 0 {
                aus.push_str(&format!(
                    " *     under {} side condition(s) -- `gabbro certificate` prints them\n",
                    a.voraussetzungen
                ));
            }
        }
        aus.push_str(" */\n");
    }
    // **Alle Prototypen vor allen Rümpfen.** In C ist ein Ruf vor der Erklärung eine
    // implizite Deklaration, und `-Werror` haelt dort an. Die Quellreihenfolge einer
    // Gabbro-Datei ist aber frei: `FRAGMENTE.md` F10 erklaert `baum_unlesbar` NACH dem
    // Rufer. *Der Erzeuger sortiert, statt die Quelle zu einer C-Reihenfolge zu zwingen.*
    let mut rumpf = String::new();
    if !leser.is_empty() {
        aus.push_str(
            "\n/* Word readers for the declared byte order. Generated, not assumed. */\n",
        );
        for l in &leser {
            aus.push_str(LESER_C.iter().find(|(n, _)| n == l).map(|(_, c)| *c).unwrap_or(""));
        }
        // **Und die Schreiber daneben** -- `SPRACHE.md`:355 sagt beide zu, und bis zum
        // 2026-08-20 stand nur die eine Haelfte da.
        for w in &schreiber {
            aus.push_str(
                SCHREIBER_C.iter().find(|(n, _)| n == w).map(|(_, c)| *c).unwrap_or(""),
            );
        }
    }
    if !namen.fremde.is_empty() {
        aus.push_str(
            "\n/* Types this unit names but does not declare. Incomplete on purpose: C\n\
             \x20* refuses every use that needs the layout, which is the refusal this emitter\n\
             \x20* would otherwise have to invent. */\n",
        );
        for f in &namen.fremde {
            aus.push_str(&format!("struct {f};\n"));
        }
    }

    // **Which names does this unit DEFINE itself, and what does the definition lower to?**
    // Read before the emitting pass, because a Gabbro file's order is free -- see the
    // refusal in `funktion`.
    let eigene = eigene_ruempfe(baum, &namen);

    // **Welche Namen haben im Erzeugnis einen Prototyp?** Genau die Funktionen, die keine
    // `spec fn` sind -- `funktion` schreibt fuer die anderen nichts. *Ohne diese Liste waere
    // eine gepruefte Bezugnahme auf eine Spezifikationsfunktion ein Uebersetzungsfehler im
    // erzeugten C, und der Anwender hat die Zeile nicht geschrieben.*
    let mut ruempfe: BTreeSet<String> = BTreeSet::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Funktion(f) = &item.art {
            if !matches!(f.klasse, Some(FnKlasse::Spec)) {
                ruempfe.insert(f.name.text.clone());
            }
        }
    });

    // **CForm typOfErw (lane 142): every non-`spec` function lowers its prototype
    // core once, here -- the same `prototyp_kern` the definition is written from
    // (`funktion`, same `u`), so a checked reference spells the signature from
    // the SAME lowering and never a second one (W7). Bodies are not required:
    // `extern` declarations lower through the same helper, which is exactly the
    // half `eigene_ruempfe` above does not cover.**
    let mut bezugskerne: std::collections::BTreeMap<String, (String, String)> =
        std::collections::BTreeMap::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Funktion(f) = &item.art {
            if matches!(f.klasse, Some(FnKlasse::Spec)) {
                return;
            }
            if let Ok(k) = prototyp_kern(f, &namen) {
                bezugskerne.insert(f.name.text.clone(), k);
            }
        }
    });

    // **`gabbro_kern()` ist ein FREMDER Rumpf, und ein fremder Rumpf braucht seinen
    // Prototypen** (2026-08-20).
    //
    // Der Kommentar an `accumulates` sagt es seit jeher -- *„Der aktuelle Kern ist ein
    // FREMDER Rumpf … so steht er da, wo er hingehoert: im Zeugnis, Abschnitt E, mit seinem
    // Vertrag"* -- und im C stand er nirgends. `_melde` rief ihn, und C11 machte daraus eine
    // implizite Deklaration. *Es fiel nicht auf, weil die einzige Datei mit `accumulates`
    // aus einem anderen Grund `C001` sagte.*
    if baum_hat_accumulates(baum) {
        aus.push_str(
            "\n/* The current core. A FOREIGN body: which core is running is a question about\n\
             \x20* the MACHINE, and lifting it into the language would be an expression for\n\
             \x20* something the language cannot check. It stands in the certificate,\n\
             \x20* section E, with its contract: it returns a core number below the `per cpu`\n\
             \x20* count, and nothing here proves that. */\nuint32_t gabbro_kern(void);\n",
        );
    }
    // **Lane 260: the `start` sites, walked once for the whole unit.**
    //
    // Every `start { f, g };` owns one 64 KiB stack region per root, at file
    // scope beside the tables: the threads the statement starts run on these
    // regions, handed in as tops (`+ 65536u`, 16-aligned by the attribute --
    // what the SysV ABI wants before a call). The walk descends through
    // `crate::unterbloecke`, and the list it fills is the same one the
    // `Start` arm names -- one register, not two (W7).
    {
        fn sammle_start(b: &Block, aus: &mut Vec<(u32, usize)>) {
            for s in &b.anweisungen {
                if let StmtArt::Start(st) = &s.art {
                    aus.push((s.span.von, st.roots.len()));
                }
                for k in crate::unterbloecke(s) {
                    sammle_start(k, aus);
                }
            }
        }
        crate::fuer_jedes_item(baum, &mut |item| {
            if let ItemArt::Funktion(f) = &item.art {
                if let FnRumpf::Block(b) = &f.rumpf {
                    sammle_start(b, &mut namen.start_orte);
                }
            }
        });
    }
    if !namen.start_orte.is_empty() {
        aus.push_str(
            "\n/* Runtime thread starts (`start { f, g };`, lane 260). The runtime owns\n\
             \x20* creation and joining (`laufzeit/faden.c`: our own raw `clone`, no libc\n\
             \x20* threading on these paths); the unit owns the stacks below, one 64 KiB\n\
             \x20* region per root, and these two declarations are the contract between\n\
             \x20* them. A misspelt name is an undefined reference, not a silent default.\n\
             \x20* Linked with `laufzeit/faden.c`; stage 9 (`cc -c`) needs only the names. */\n\
             int gabbro_faden_start(void (*fn)(void), void *spitze, uint32_t *wort);\n\
             void gabbro_faden_warte(uint32_t *wort);\n",
        );
        for (lo, n) in namen.start_orte.clone() {
            for i in 0..n {
                aus.push_str(&format!(
                    "static unsigned char gabbro_stapel_{lo}_{i}[65536] \
                     __attribute__((aligned(16)));\n\
                     static uint32_t gabbro_wort_{lo}_{i};\n"
                ));
            }
        }
    }
    // **Die Marken stehen HIER und nicht an ihrem Item** -- aus demselben Grund, aus dem
    // alle Prototypen vor allen Ruempfen stehen. `beispiele/04` erklaert `linear type
    // Angemeldet;` **nach** der Funktion, die den Typ in ihrer Signatur fuehrt; an seinem
    // Platz erzeugt waere er in C erst nach seinem ersten Gebrauch bekannt. *Die
    // Quellreihenfolge einer Gabbro-Datei ist frei, und der Erzeuger sortiert.*
    if !namen.marken.is_empty() {
        aus.push_str(
            "\n/* `linear type T;` without a body -- a TOKEN: it carries a right, not data.\n\
             \x20* The one byte exists so that C can pass and address the value; nothing ever\n\
             \x20* reads it. That the value is used exactly once is M2's statement, and M2\n\
             \x20* has already made it. A `linear ghost type` is ERASED instead -- that is the\n\
             \x20* whole difference between the two words. */\n",
        );
        for m in &namen.marken {
            aus.push_str(&format!("typedef struct {{ uint8_t nichts; }} {m};\n"));
        }
    }
    // **Alle Typen vor allem anderen -- aus demselben Grund wie alle Prototypen vor allen
    // Ruempfen** (2026-08-20).
    //
    // `beispiele/05` erklaert `type Zelle = { wert : Zaehlerwert, };` als **letztes Item** und
    // fuehrt `ptr<normal, rw> Zelle` in einer Signatur zwanzig Zeilen davor. An seinem Platz
    // erzeugt stuende der `typedef` hinter seinem ersten Gebrauch, und `cc` saehe einen
    // unbekannten Typnamen. *Die Quellreihenfolge einer Gabbro-Datei ist frei; der Erzeuger
    // sortiert, statt sie zu einer C-Reihenfolge zu zwingen.*
    //
    // > Es fiel bis heute nicht auf, weil die Dateien, die einen Verbund spaet erklaeren, aus
    // > einem anderen Grund `C001` sagten -- **dieselbe Bauart wie beim `format`-Feldzugriff
    // > und beim fehlenden `gabbro_kern`, am selben Tag, aus demselben Grund.**
    // **Und die `#define`s stehen vor den Typen.** `beispiele/32` fuehrt `[u8; KAP]` in
    // einem Verbund, und ein `typedef` vor seinem `#define` ist eine unbekannte Laenge.
    // *Beim ersten Anlauf stand genau das da: die Hochziehung hat einen Fehler geheilt und
    // beim Nachbarn einen aufgemacht -- und `cc` hat ihn in derselben Minute gemeldet.*
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| match &item.art {
        ItemArt::Konst(k) => {
            // **Lane 111:** a const table lowers to one `static const` C array,
            // element-wise from the same folder the checker reads (`umgebung.rs`
            // computes it for `table … count N` anyway -- a second evaluator
            // beside it would be the second register over the same fact, W7).
            // Anything the folder does not fold is `C001`, never guessed.
            if let ExprArt::ArrayLit(elements) = &k.wert.art {
                match const_table(k, elements, modul, baum) {
                    Some(zeile) => aus.push_str(&zeile),
                    None => weigere(
                        absagen,
                        k.name.span,
                        "const table without a lowering: the element type needs a C \
                         word and every element a translation-time value",
                    ),
                };
            } else if let Some(w) = konst_zahl(&k.wert) {
                aus.push_str(&format!("\n#define {} {}u\n", k.name.text, w));
            // **«F»: eine Gleitkommakonstante ist ein `#define` ohne `u`.**
            //
            // *Das `u` waere hier nicht bloss ueberfluessig, sondern falsch* -- es macht aus
            // dem Literal eine vorzeichenlose Ganzzahl, und der Uebersetzer wuerde es
            // wortlos annehmen.
            } else if let ExprArt::Gleitkomma { bits, .. } = &k.wert.art {
                aus.push_str(&format!(
                    "\n#define {} {}\n",
                    k.name.text,
                    gleitkommatext(*bits, false)
                ));
            // **«G5»: `u64::max` IST eine Konstante -- sie steht nur nicht als Ziffernfolge
            // da.** Die Grenzen einer Breite sind Wortschatzwoerter, und sie hier abzulehnen
            // hiesse, dem Anwender die Grenzwerte zu verbieten, die die Grammatik ihm seit
            // dem 2026-08-15 ausdruecklich gibt. *Das Vorzeichen entscheidet ueber das `u`:
            // ein `#define X -5u` waere nicht bloss haesslich, sondern eine andere Zahl.*
            //
            // Der Wert kommt aus `namen.konstwert` und wird hier NICHT noch einmal gerechnet
            // -- `umgebung.rs` rechnet ihn ohnehin fuer `table … count N`, und ein zweiter
            // Rechner daneben waere das zweite Register ueber derselben Sache (W7).
            } else if let Some(w) = namen.konstwert.get(&k.name.text).copied() {
                let suffix = if w < 0 { "" } else { "u" };
                aus.push_str(&format!("\n#define {} {w}{suffix}\n", k.name.text));
            // **`~` inside a `const` gets its OWN refusal, because the one beside it would
            // be false.** `const H : u32 = ~G;` IS a constant expression -- it is merely not
            // one `umgebung.rs` can fold: that folder computes in `i128`, and the complement
            // is `2^n - 1 - x` with an `n` it does not have. *A refusal that says
            // "non-constant" sends the reader the wrong way* -- looking for a variable and
            // finding a missing folder.
            //
            // The folding is not built (Rule A: zero corpus sites); the form for the
            // all-ones constant stands beside it and is called `u32::max`.
            } else if enthaelt_bitnicht(&k.wert) {
                weigere(
                    absagen,
                    k.name.span,
                    "`~` inside a `const` -- the value IS constant, and the folder in \
                     `umgebung.rs` computes in `i128` without a width. The all-ones constant \
                     of a width has its own form: `u32::max`",
                );
            } else {
                weigere(absagen, k.name.span, "const with a non-constant value");
            }
        }
        // **Dieser Gang schreibt NUR `#define`s, und nur ein `const` erklaert einen.**
        // Alles andere hat seinen eigenen Gang -- die Typen den davor, die Ruempfe den
        // danach --, und dass die Reihenfolge zwischen ihnen entschieden ist und nicht der
        // Quellreihenfolge folgt, steht oben. *Ein Sammelzweig hier las sich wie „das
        // uebrige kommt spaeter"; er sagte aber nur „hier nicht".*
        ItemArt::Modul(_)
        | ItemArt::Use(_)
        | ItemArt::Typ(_)
        | ItemArt::Statisch(_)
        | ItemArt::Funktion(_)
        | ItemArt::Tabelle(_)
        | ItemArt::Format(_)
        | ItemArt::Device(_)
        | ItemArt::Reason(_)
        | ItemArt::State(_)
        | ItemArt::Assume(_)
        | ItemArt::Axiom(_)
        | ItemArt::Check(_)
        | ItemArt::Atomic(_)
        | ItemArt::Lock(_)
        | ItemArt::Rcu(_)
        | ItemArt::Gruppe(_)
        | ItemArt::Accumulates(_)
        | ItemArt::Walk(_)
        | ItemArt::Entry(_)
        | ItemArt::Entrust(_)
        | ItemArt::Boot(_)
        // **A `syscall` hoists no constant.** Its `number` may name one, but the
        // number is read by the stub (lane S6), not emitted as a `#define`.
        | ItemArt::Syscall(_)
        // **«E6»: a profile block hoists no constant.** Values are mode
        // names, not numbers.
        | ItemArt::Profil(_)
        | ItemArt::ProfilBedarf(_)
        // **«E4»:** an arena hoists no constant either. Its bounds may name
        // `const`s, but they are read where they are spelled (`zahltext`
        // in `arena()`), not hoisted.
        | ItemArt::Arena(_)
        | ItemArt::Concurrent(_) => {}
    });
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Typ(t) = &item.art {
            if namen.verbunde.contains(&t.name.text) {
                verbund(t, &mut aus, &namen, absagen);
            }
            if namen.markierte.contains_key(&t.name.text) {
                markiert(t, &mut aus, &namen, absagen);
            }
        }
    });

    crate::fuer_jedes_item(baum, &mut |item| match &item.art {
        // **Die Konstanten stehen VOR den Typen** -- siehe dort.
        ItemArt::Konst(_) => {}
        // Die Typen stehen VOR der Schleife -- siehe dort.
        ItemArt::Typ(_) => {}
        ItemArt::Tabelle(t) => tabelle(t, &mut aus, &namen, absagen),
        // **«E4»:** the buffer type and, when used, its storage -- beside
        // the table, in the same gang.
        ItemArt::Arena(a) => arena(a, &mut aus, &namen, absagen),
        ItemArt::Format(f) => format_(f, &mut aus, &namen, absagen),
        ItemArt::Device(d) => geraet(d, &mut aus, &namen, absagen),
        // **`atomic x : u32 publishes nothing relaxed;`** -- der lastfreie Zaehler, und nur
        // er. Er traegt KEINE Nutzlast, also gibt es keine Paarung und keine Sichtbarkeit zu
        // begruenden: `_Atomic` mit `relaxed` ist genau das, was dasteht.
        //
        // > **`release`/`acquire` werden abgelehnt.** Dass ein `release`-Speichern die
        // > Sichtbarkeit HERSTELLT, die die Paarung behauptet, ist eine Aussage ueber das
        // > Speichermodell -- die Klempnerei-Klasse *Rennen* haengt seit dem 2026-08-16 genau
        // > daran, und der Pruefer baut sie nicht. *Der Erzeuger entscheidet nicht, was der
        // > Pruefer offenlaesst.*
        // **K11.3.1: `static` senkt ab.** Bis heute weigerte sich der Erzeuger, und das hat
        // `beispiele/05` und `/22` am C gehindert -- beides Dateien, deren Gegenstand
        // (Paarung, Bootstrecke) gar nicht am `static` haengt.
        //
        // **Ohne `mut` ist es `const`, und das ist keine Kosmetik:** ein Schreiben darauf ist
        // in C ein Uebersetzungsfehler, und damit traegt das Erzeugnis die
        // Unveraenderlichkeit selbst statt sie dem Pruefer allein zu ueberlassen.
        //
        // `section ".rodata"` wird ein Attribut. *Es ist eine Aussage ueber die PLATZIERUNG,
        // und die gehoert in das Erzeugnis -- ein Kommentar daneben waere genau die Bauart,
        // gegen die `mirrors` gebaut wurde.*
        ItemArt::Statisch(st) => {
            // **Ein `static` ueber einem FELD -- und der Grund, warum es hier steht und
            // nicht in `ctyp`** (2026-08-20).
            //
            // In C steht die Laenge **hinter dem Namen**: `uint32_t kernlast[64]`, nicht
            // `uint32_t[64] kernlast`. Ein Typ, den man als Zeichenkette vor den Namen
            // setzen kann, gibt es dafuer nicht -- `ctyp` liefert genau so eine Zeichenkette,
            // und darum kann die Feldform dort gar nicht sitzen. *Die C-Deklaratorsyntax ist
            // keine Eigenheit, die man wegabstrahiert; sie ist der Grund fuer die Fallform.*
            // Lane 170 spells the whole spine there: `[[u32; 4]; 3]` becomes
            // `uint32_t M[3][4]` out of `feld_deklarator`, one `[n]` per dimension.
            if matches!(&st.typ, TypExpr::Feld(_)) {
                feldstatisch(st, &mut aus, &namen, absagen);
                return;
            }
            // **Ein `tagged` oder ein Verbund faengt nicht mit einer ZAHL an** (2026-08-20).
            //
            // `static mut letzte : Vergabe = 0;` ergab `static Vergabe letzte = 0;` -- eine
            // ungueltige Initialisierung, bei null Fehlern im Pruefer. *Wieder eine Form, die
            // aussah wie eine Absenkung und keine war.*
            //
            // Der Erzeuger weigert sich benannt, statt `{0}` zu schreiben und es die
            // Leervariante zu nennen: **welche Variante die Null ist, sagt die Deklaration
            // nicht** -- `enum` beginnt bei der ersten, aber dass die erste die gemeinte ist,
            // steht nirgends. Gefunden beim Abarbeiten der Blindstellen.
            //
            // **NARROWED on 2026-08-25, and the reason is that the refusal was WIDER than its
            // own grounds.** The text above argues one case -- *initialised with a plain
            // number* -- and the code refused **every** `static` whose type is a `tagged` or a
            // record, including the one form for which the question it asks is already
            // answered in the source: the LABELLED CALL. `static mut irq : IrqMarke =
            // IrqMarke(tiefe_max: 0, n: 1);` does not leave open which field carries what; it
            // says so, field by field, and in the checker `M106`/`M107` have already held the
            // label list against the field list (`m1.rs::marken_pruefen`).
            //
            // *That is the shape `messung/fragmente/` has now found five times:* a rule whose
            // extent and whose justification have drifted apart. **The justification was
            // right; the extent was not.**
            //
            // > **No new template.** The lowering is `S19 verbund.konstruktor`, PROVED on
            // > 2026-08-17 (`beweise/Verbund_Konstruktor.thy`) and already carried by
            // > `emit::ruf` for the expression position. This branch reaches the same
            // > designators at file scope -- `L` does not move, and that is the whole point of
            // > K100's second gate.
            //
            // A `tagged` keeps its refusal: which variant the zero is, the declaration still
            // does not say, and a labelled call cannot name one.
            if let TypExpr::Pfad(p) = &st.typ {
                if let Some(n) = p.teile.last() {
                    if namen.markierte.contains_key(&n.text) || namen.verbunde.contains(&n.text) {
                        // **Lane 167: `static N : Nachricht = Kurz(5);` -- the brace form.**
                        //
                        // A compound literal is no constant expression, so the file-scope
                        // initializer spells the same designators `ruf` writes in braces.
                        // The payload must be translation-time constant -- the same gate
                        // the number path below holds; anything else falls through to the
                        // `C001` beside it, which then names the constantness, not the case.
                        if namen.markierte.contains_key(&n.text) {
                            if let Some(init) = varianten_statisch(&st.wert, &n.text, &namen, absagen) {
                                let (konst, abschnitt) = statischer_kopf(st, absagen);
                                aus.push_str(&format!(
                                    "\nstatic {konst}{} {}{abschnitt} __attribute__((unused)) = {init};\n",
                                    n.text, st.name.text
                                ));
                                return;
                            }
                        }
                        // **A brace initialiser, not a compound literal.** `ruf` writes
                        // `(P){ .a = 1 }` -- an lvalue with static storage duration, which C11
                        // 6.7.9p4 does not admit as an initialiser for a static object. At file
                        // scope the same designators go in braces, and `cc -Werror` is the
                        // second reader of the completeness (`-Wmissing-field-initializers`).
                        if let Some(felder) = verbundmarken(&st.wert, &n.text, &namen, absagen) {
                            let (konst, abschnitt) = statischer_kopf(st, absagen);
                            aus.push_str(&format!(
                                "\nstatic {konst}{} {}{abschnitt} __attribute__((unused)) = {felder};\n",
                                n.text, st.name.text
                            ));
                            return;
                        }
                        weigere(
                            absagen,
                            st.name.span,
                            "`static` of a `tagged` type or a record initialised with a plain number \
                             -- which variant the zero is, the declaration does not say, and a \
                             record has no scalar value. **A record initialised by its LABELLED CALL \
                             lowers since 2026-08-25** -- write `T(f: …, g: …)`, which says field by \
                             field what the number does not",
                        );
                        return;
                    }
                }
            }
            let Some(c) = ctyp(&st.typ, &namen) else {
                weigere(absagen, st.name.span, "`static` of an unresolvable type");
                return;
            };
            // **Ein `static mut frei : option index into Halde = None;`** -- der
            // Anfangswert ist der Sonderwert, und der steht als `#define` ueber der
            // Tabelle. *Ohne diesen Zweig war die Freiliste nicht absenkbar, obwohl der
            // Beweis dafuer seit dem 2026-08-17 dalag.*
            let anfang = match &st.typ {
                TypExpr::Index { tabelle, optional: true, .. } => {
                    option_wert(&st.wert, &tabelle.text, &namen, absagen)
                }
                _ => None,
            };
            let w = match anfang {
                Some(x) => x,
                // **Ein `static`, dessen Anfangswert eine KONSTANTE ist** (2026-08-20).
                //
                // `static GERAETEBASIS : Pa = BASIS;` fiel an *„`static` with a non-constant
                // initialiser"* -- und `BASIS` ist so konstant, wie eine Zahl es sein kann.
                // `konst_zahl` liest eine Ziffernfolge; ein `const`-Name ist keine.
                //
                // > *Gefunden beim Abarbeiten der Blindstellen*, an der ersten Datei, die
                // > einen undurchsichtigen Typ als `static` fuehrt. Der Wert kommt aus
                // > `namen.konstwert` und wird hier NICHT noch einmal gerechnet (W7).
                None => match konst_zahl(&st.wert).or_else(|| match &st.wert.art {
                    ExprArt::Ort(o) if o.suffixe.is_empty() => {
                        namen.konstwert.get(&o.basis.text).copied()
                    }
                    _ => None,
                }) {
                    // **`D14`: this sink was one of the nine `D3` named, and `D3` did not
                    // reach it** (2026-09-03).
                    //
                    // `czahl` grew on 2026-09-03 so that a literal past `2^63 - 1` carries
                    // the `u` C needs. It sits in the EXPRESSION path, and a `static`
                    // initialiser does not travel that path: the value arrives here as an
                    // `i128` out of `konst_zahl` or out of `namen.konstwert`, and was
                    // written with `to_string()`.
                    //
                    //     static mut x : u64 = 18446744073709551615;
                    //     ->  static uint64_t x __attribute__((unused)) = 18446744073709551615;
                    //     cc: integer constant is so large that it is unsigned [-Werror]
                    //
                    // **The `#define` of a `const` two branches up already writes a suffix**,
                    // and has since it was built. *Two spellings for one thing, and the
                    // weaker one decided here* -- `W7`, the same shape `konst_wert` had.
                    //
                    // > It takes `czahl`'s boundary and not the `#define`'s. That branch
                    // > suffixes every non-negative value; `czahl` suffixes only above
                    // > `2^63 - 1`, and its own note says why -- `-Wconversion` and
                    // > `-Wsign-conversion` read these same literals, so a suffix added where
                    // > C does not need one trades this error for a different one.
                    //
                    // A negative value keeps `to_string()`: `-5u` is not a smaller spelling
                    // of `-5`, it is another number. The same sentence stands at the
                    // `#define`.
                    Some(n) => match u128::try_from(n) {
                        Ok(u) => czahl_oder_absage(u, st.name.span, absagen),
                        Err(_) => n.to_string(),
                    },
                    None => {
                        weigere(
                            absagen,
                            st.name.span,
                            "`static` with a non-constant initialiser",
                        );
                        return;
                    }
                },
            };
            // **Ein `const` gehoert an den ZEIGER, nicht an sein Ziel** (2026-08-20).
            //
            // `static tz : ptr<normal, rw> T` ergab `static const T * tz` -- ein Zeiger auf
            // *konstantes* `T`. Gemeint ist ein *konstanter* Zeiger auf schreibbares `T`.
            // Die Folge war eine abgewiesene Uebersetzungseinheit fuer ein Programm, das
            // Gabbro **richtig** findet:
            //
            //     tz.slots[i].a = 5;
            //     -> error: Zuweisung von Element »a« in schreibgeschuetztem Objekt
            //
            // *Das fehlende `mut` sagt etwas ueber den ZEIGER -- dass er nicht umgehaengt
            // wird -- und nichts ueber das, worauf er zeigt.* Das steht in `ptr<…, rw>` und
            // steht dort schon.
            let (konst, konst_nach) = match (st.veraenderlich, c.trim_end().ends_with('*')) {
                (true, _) => ("", ""),
                (false, false) => ("const ", ""),
                (false, true) => ("", "const "),
            };
            let abschnitt = abschnitt_attribut(st, absagen);
            // **`unused` -- und das ist derselbe Befund wie beim `(void)k;` oben**
            // (2026-08-20).
            //
            // `beispiele/36-asm.gab` hat `static mut GERAET` und schreibt es in einem
            // `asm`-Block: auf Gabbro-Ebene steht `effects { writes GERAET }`, im C steht
            // kein einziger Zugriff, denn den Befehl liest Gabbro nicht. `cc -Wunused`
            // meldet daraufhin einen Platz, der sehr wohl benutzt wird.
            //
            // > *Die Warnung gilt dem ERZEUGNIS, nicht dem Anwender.* Er hat die Zeile nicht
            // > geschrieben, und ob ein Weltzustand tot ist, ist eine Gabbro-Frage.
            //
            // **Und dafuer gibt es heute keinen Pass** -- ein `static`, den niemand nennt,
            // faellt nirgends auf. In `TODO.md` gebucht; hier stillgelegt, nicht
            // verschwiegen.
            // **A POINTER OUT OF A NUMBER GOES THROUGH `(uintptr_t)`, and that is the whole
            // difference between undefined and implementation-defined** (2026-09-02).
            //
            // `static tz : ptr<normal, rw> Platz = 0;` produced
            //
            //     static Platz * const tz __attribute__((unused)) = 0;
            //
            // and that `0` is a **null pointer constant** under C11 6.3.2.3p3. The body
            // below it writes `tz->slots[i].a = 5;`, so the emitted C dereferences a null
            // pointer -- **undefined behaviour, C11 6.5.3.2p4.** Found by `clang --analyze`
            // (`core.NullDereference`) over `beispiele/38`, the only site in the corpus with
            // this shape, in the audit of 2026-09-02.
            //
            // > `dokumente/BEWEIS.md` carries the class *null pointer* as *"Gabbro has no
            // > `null`"* with residual risk **only at the `extern` boundary**. This file is
            // > not at the `extern` boundary. *The row was right about the LANGUAGE and
            // > wrong about the PRODUCT.*
            //
            // **The cure was already in this same emitter.** The MMIO path has always
            // written `(volatile uint8_t *)(uintptr_t)GERAETEBASIS`: converting an INTEGER
            // to a pointer is *implementation-defined* (6.3.2.3p5) rather than undefined,
            // and that is exactly what a place naming a fixed address on bare metal needs.
            // Address 0 there is a vector slot and not a mistake; **what was wrong is the
            // spelling, not the intent.** Two spellings for one thing were `W7`; now there
            // is one.
            let zeigertyp = c.trim_end().ends_with('*');
            let wert = if zeigertyp { format!("({}) (uintptr_t){w}", c.trim_end()) } else { w };
            aus.push_str(&format!(
                "\nstatic {konst}{c} {konst_nach}{}{abschnitt} __attribute__((unused)) = {wert};\n",
                st.name.text
            ));
        }
        // **`accumulates` -- eine Zelle je Kern, gefaltet beim Lesen.** Kein CAS, keine
        // unbeschraenkte Schleife: der Widerspruch *„der Uebersetzer erzeugt, was die Sprache
        // verbietet"* faellt damit weg.
        //
        // **Die Schablone war VOR dem Konstrukt bewiesen** (`beweise/Accumulates_Monoid.thy`,
        // 2026-08-17) -- so verlangt es das zweite Tor. Und sie hat die Falle ausgespuelt,
        // die hier drinsteckt: **`min` hat als Neutrales das MAXIMUM des Typs, nicht die
        // Null.** Ein Erzeuger, der mit `0` anfaengt, zieht jedes `min` auf null.
        //
        // *Der aktuelle Kern ist ein FREMDER Rumpf* -- `gabbro_kern()`. Ihn in die Sprache zu
        // heben waere ein Ausdruck fuer eine Maschinenfrage; so steht er da, wo er hingehoert:
        // im Zeugnis, Abschnitt E, mit seinem Vertrag.
        ItemArt::Accumulates(ac) => {
            let Some(c) = ctyp(&ac.typ, &namen) else {
                weigere(absagen, ac.name.span, "`accumulates` of an unresolvable type");
                return;
            };
            let Some(zahl) = &ac.pro_kern else {
                weigere(
                    absagen,
                    ac.name.span,
                    "`accumulates` without `per cpu <constexpr>` -- the lowering is one cell \
                     per core, and how many cores there are is not in the declaration",
                );
                return;
            };
            // **Wie bei `count`: eine Zahl ODER ein `const`-Name.** Ein `#define` steht schon
            // im Kopf des Erzeugnisses, also traegt der Name sich selbst.
            let n = zahltext(zahl, absagen);
            // **Die Zellen fangen bei NULL an, und C laesst sich das nicht abgewoehnen.**
            //
            // Fuer `max`, `add` und `or` ist null das Neutrale -- die unberuehrten Zellen
            // stoeren nicht. **Fuer `min` und `and` ist es das Vollbild des Typs**
            // (`min_ist_monoid_mit_top`), und eine statische Belegung damit gibt es in
            // Standard-C nicht: `= { [0 ... N-1] = ~0 }` ist eine GCC-Erweiterung, und die
            // Liste auszuschreiben geht nicht, wenn `per cpu` einen `const`-NAMEN nennt.
            //
            // > **Der erste Lauf zeigte es sofort:** drei Kerne melden 7, 3, 11 -- und
            // > `min` lieferte **0**, weil 61 unberuehrte Zellen mitgezaehlt wurden. *Der
            // > Beweis hatte den Satz; die Absenkung hatte ihn nicht.*
            //
            // **Die Loesung ist die Darstellung, nicht die Belegung:** `min` und `and`
            // speichern das KOMPLEMENT und falten mit `max` bzw. `or`. Die Komplementbildung
            // kehrt die Ordnung um, also ist `~(max ~v) = min v` -- und eine unberuehrte
            // Zelle traegt `~0`-komplementiert, also das Neutrale. *Zero-init trifft damit
            // genau das, was der Satz verlangt.*
            let (falte, kehrt) = match ac.merge {
                MergeOp::Max => ("z = (z > v) ? z : v;", false),
                MergeOp::Min => ("z = (z > v) ? z : v;", true),
                MergeOp::Add => ("z += v;", false),
                MergeOp::Or => ("z |= v;", false),
                MergeOp::And => ("z |= v;", true),
            };
            let (auf, ab) = if kehrt {
                (format!("({c})~"), format!("({c})~"))
            } else {
                (String::new(), String::new())
            };
            let neutral = "0";
            let op = match ac.merge {
                MergeOp::Max => "max", MergeOp::Min => "min", MergeOp::Add => "add",
                MergeOp::Or => "or", MergeOp::And => "and",
            };
            let nm = &ac.name.text;
            // **CForm schrittStmt (lane 142): the merge loop steps with `+= 1`.**
            // (`z += v` below is the admitted merge itself, untouched.)
            aus.push_str(&format!(
                "\n/* accumulates {nm} merge {op} per cpu {n} -- one cell per core.\n\
                 \x20* The merge set is a commutative monoid, so the fold is order-independent\n\
                 \x20* (beweise/Accumulates_Monoid.thy). AT A QUIESCENT POINT this equals an\n\
                 \x20* atomic RMW chain -- read while others write, it does not, and that is\n\
                 \x20* the price of the lowering, not an inaccuracy. */\n \
                 static _Atomic {c} {nm}_zellen[{n}];\n\
                 \n \
                 static {c} {nm}_lies(void) __attribute__((unused));\n\
                 static {c} {nm}_lies(void) {{\n\
                 \x20   {c} z = ({c}){neutral};\n\
                 \x20   for (uint32_t k = 0; k < (uint32_t)({n}); k += 1) {{\n\
                 \x20       {c} v = atomic_load_explicit(&{nm}_zellen[k], memory_order_relaxed);\n\
                 \x20       {falte}\n\
                 \x20   }}\n\
                 \x20   return {ab}z;\n\
                 }}\n\
                 \n \
                 static void {nm}_melde({c} roh) __attribute__((unused));\n\
                 static void {nm}_melde({c} roh) {{\n\
                 \x20   {c} v = {auf}roh;\n\
                 \x20   uint32_t k = gabbro_kern();\n\
                 \x20   {c} z = atomic_load_explicit(&{nm}_zellen[k], memory_order_relaxed);\n\
                 \x20   {falte}\n\
                 \x20   atomic_store_explicit(&{nm}_zellen[k], z, memory_order_relaxed);\n\
                 }}\n"
            ));
        }
        ItemArt::Atomic(a) => {
            match a.ordnung {
                // `publishes nothing` IST die lastfreie Form -- sie steht als Nutzlast da,
                // und genau darum ist sie harmlos: es gibt nichts zu paaren.
                Some(Ordnung::Relaxed) | None
                    if matches!(a.obermenge, None | Some(Nutzlast::Nichts(_))) =>
                {
                    match atom_declarator(a, &namen) {
                        Some(d) => aus.push_str(&format!("\n_Atomic {d};\n")),
                        None => weigere(absagen, a.span, atom_refusal(a, &namen)),
                    }
                }
                // **K11.2.3 (2026-08-17): `release`/`acquire`/`seq` senken ab.**
                //
                // Bis heute stand hier eine Weigerung mit diesem Grund: *„dass ein
                // release-Speichern die Sichtbarkeit HERSTELLT, die die Paarung behauptet,
                // ist eine Aussage ueber das Speichermodell, und der Pruefer baut sie nicht."*
                // **Der Grund stimmt weiter -- er ist nur kein Grund fuer eine Weigerung.**
                //
                // Die Aussage steht seit K100.2 als **A10** in der Axiomschicht
                // (`release_stellt_sichtbarkeit_her`), gebucht als **nicht falsifizierbar**:
                // *das Speichermodell ist nicht durch Ausfuehrung widerlegbar -- eine
                // erfolgreiche Probe zeigt nur, dass die Umordnung diesmal ausblieb.*
                //
                // > **Eine Annahme, die benannt und gebucht ist, traegt.** Sich weiter zu
                // > weigern hiesse, dieselbe Aussage zweimal zu verlangen: einmal als Axiom
                // > und einmal als Beweis.
                //
                // Die Ordnung wandert in einen Kommentar neben die Deklaration und in die
                // Zugriffe (`atomic_store_explicit`/`atomic_load_explicit`) -- **im C steht
                // dann, was die Quelle sagte, und nicht das Vorgabemodell von `_Atomic`.**
                // *Das ist die strukturelle Zusage; mehr kann eine Uebersetzung hier nicht
                // geben, und ein Differenztest koennte die Abwesenheit eines Rennens ohnehin
                // nicht zeigen.*
                Some(o) => match atom_declarator(a, &namen) {
                    Some(c) => {
                        let (wort, notiz) = match o {
                            Ordnung::Release => ("memory_order_release", "publishes"),
                            Ordnung::Acquire => ("memory_order_acquire", "awaits"),
                            Ordnung::Seq => ("memory_order_seq_cst", "total order"),
                            Ordnung::Relaxed => ("memory_order_relaxed", "no payload"),
                        };
                        // **Three cases, and two of them say the same word for different
                        // reasons** (the `_` here was struck 2026-08-31; measured 21 hits,
                        // every one of them `None`). `publishes nothing` is the source
                        // SAYING there is no payload; no clause at all is the source saying
                        // nothing. The C comment reads the same either way -- what changes
                        // is that a third `Nutzlast` is now a translation error instead of
                        // the word `nothing`.
                        let last: String = match &a.obermenge {
                            Some(Nutzlast::Orte(l)) => l
                                .iter()
                                .map(|x| x.text())
                                .collect::<Vec<_>>()
                                .join(", "),
                            Some(Nutzlast::Nichts(_)) => "nothing".into(),
                            None => "nothing".into(),
                        };
                        aus.push_str(&format!(
                            "\n/* {} under A10 (release_stellt_sichtbarkeit_her, UNFALSIFIABLE):\n\
                             \x20* the ordering below is the one the source declared, not C's default.\n\
                             \x20* payload: {last} */\n_Atomic {c};\n#define {}_ORDER {wort}\n",
                            notiz, a.name.text
                        ));
                    }
                    None => weigere(absagen, a.span, atom_refusal(a, &namen)),
                },
                None => weigere(
                    absagen,
                    a.span,
                    "`atomic` with a payload but no ordering -- a payload without an ordering \
                     is a publication nobody can pair",
                ),
            }
        }
        // **`check` -- der Pruefkoerper wird eine Funktion, der Rest faehrt als Kommentar mit.**
        //
        // `claim`, `measures`, `gates`, `floor` und `counterprobe` sind Buchfuehrung ueber die
        // MESSUNG, nicht Rechnung: sie sagen, was die Probe behauptet, woran sie haengt und
        // wie sie rot werden koennte. *Sie zu unterschlagen hiesse, eine Probe auszuliefern,
        // deren Behauptung nirgends steht.*
        ItemArt::Check(c) => pruefkoerper(c, &mut aus, &mut rumpf, &namen, absagen),
        // **Eine Sperre erzeugt zwei Prototypen und keine Zeile Rumpf.**
        //
        // Rang und Haltezeit stehen im C NIRGENDS: `H006` rechnet die Ordnung zur
        // Uebersetzungszeit nach, `K002`/`K004` die Haltezeiten -- und **was der Pruefer
        // entschieden hat, darf die Maschine nicht noch einmal pruefen** (W6, und hier ist
        // die Begruendung eine M1-artige: die Ordnung ist eine Eigenschaft des Programms,
        // keine des Laufs).
        //
        // Was bleibt, ist das Primitiv selbst, und **das ist Vertrauensbasis, nicht
        // Erzeugnis** -- es gehoert in die Axiomschicht wie `write_cr3`. Der Erzeuger nennt
        // es und definiert es nicht.
        ItemArt::Lock(l) => {
            aus.push_str(&format!(
                "\nvoid {n}_nimm(void);\nvoid {n}_gib(void);\n",
                n = l.name.text
            ));
            if l.geteilte_haltezeit.is_some() {
                aus.push_str(&format!(
                    "void {n}_nimm_geteilt(void);\nvoid {n}_gib_geteilt(void);\n",
                    n = l.name.text
                ));
            }
        }
        ItemArt::Funktion(f) => funktion(f, &mut aus, &mut rumpf, &namen, &eigene, absagen),
        // **`assume` und `axiom` erzeugen keinen Code -- aber sie erzeugen die ZUSAGE.**
        //
        // `SYNTAX.md` §12: *„Die Annahmenmenge wird ins Erzeugnis emittiert (‚bewiesen unter
        // A1…An‘), als Menge von Namen mit Klasse, nicht als Zahl."* Bis zum 2026-08-17 hat
        // das nichts getan: `gabbro annahmen` druckt sie auf die Konsole, und das Erzeugnis
        // wusste nichts davon.
        //
        // > *Eine Zusage, die nur in einem Werkzeugaufruf steht, faehrt nicht mit dem Code
        // > mit.* Sie steht jetzt im Kopf der erzeugten Datei -- dort, wo auch der
        // > Lizenzhinweis steht, und aus demselben Grund.
        // **«C3a»: ein `reason` ist eine benannte Zahlenmenge, und die Zahlen STEHEN DA.**
        //
        // `KeinSlot = 1 "kein freier Slot mehr"` nennt den Wert selbst -- der Erzeuger
        // waehlt keinen. Damit ist die Absenkung ein `enum` mit ausgeschriebenen Werten,
        // und der Text wandert als Kommentar mit: *er ist die Erklaerung, die ein Leser des
        // Erzeugnisses sonst nirgends findet.*
        //
        // > **Was hier NICHT entschieden wird: wie ein Fehler ZURUECKKOMMT.** Ein
        // > `let x = f() else (e) { … }` braeuchte eine Fehlerrueckgabe-Konvention, und die
        // > steht in keiner Zeile der Grammatik -- `f() -> u32` hat keinen Fehlerkanal.
        // > *Die Grammatik ist fuer den Menschen da, der Gabbro schreibt; wo sie und der
        // > Erzeuger auseinandergehen, gewinnt der Mensch und der Erzeuger sagt `C001`.*
        // > Dieselbe Absage steht seit jeher am `on_exceeded` eines `retry`.
        ItemArt::Reason(r) => {
            // **`D13`: an enumerator is the one C object whose width the emitter does not
            // choose** (2026-09-03).
            //
            // The lowering above is an `enum`, and C11 6.7.2.2p2 is a CONSTRAINT on it:
            // *"the expression that defines the value of an enumeration constant shall be an
            // integer constant expression that has a value representable as an `int`"*. A
            // value past `INT_MAX` therefore makes this translation unit ill-formed, and the
            // emitter was writing one.
            //
            // **Three complaints over one cause, and the sweep saw all three:**
            //
            //     A = 2147483648            cc -Wpedantic: ISO C restricts enumerator values
            //                               to range of `int`          (13 cases, net 5)
            //     A = 18446744073709551615  cc -Werror: integer constant is so large that it
            //                               is unsigned                 (6 cases, shape 2)
            //     A = 2^127                 cc -Werror: integer constant is too large for
            //                               its type                   (10 cases, shape 2)
            //
            // *One fence closes all three*, because the first one is the real rule and the
            // other two are what is left when a value sails past it.
            //
            // **A suffix would have been the smaller change and it is the wrong one.**
            // `A = 18446744073709551615u` silences `-Werror` and leaves the constraint
            // violation exactly where it was -- the failure moves to `-Wpedantic`, which is a
            // gate fewer readers run. *That is `D6`'s argument, one file over: a repair that
            // moves the complaint to a quieter tool is not a repair.*
            //
            // > **`int` is taken as 32 bits, and that is an assumption, so it is written
            // > down.** C promises only 16, and a narrower `int` would make this fence
            // > UNDER-refuse. Every target this back end writes has a 32-bit `int`, and the
            // > number in the refusal is GCC's own -- read off the message above rather than
            // > assumed. The safe direction is the one taken: what slips through, `cc` still
            // > catches.
            for f in &r.faelle {
                if f.wert > C_ENUM_MAX {
                    weigere(
                        absagen,
                        f.span,
                        &format!(
                            "a `reason` case whose value is {} -- a `reason` lowers to a C \
                             `enum`, and C11 6.7.2.2 requires every enumerator to be \
                             representable as an `int`. The largest one is {C_ENUM_MAX}, and \
                             there is no wider enumerator to write",
                            f.wert
                        ),
                    );
                    return;
                }
            }
            aus.push_str(&format!("\n/* reason {} */\ntypedef enum {{\n", r.name.text));
            for f in &r.faelle {
                aus.push_str(&format!(
                    "    {}_{} = {}, /* {} */\n",
                    r.name.text,
                    f.name.text,
                    f.wert,
                    kommentartext(&f.text.text)
                ));
            }
            aus.push_str(&format!("}} {};\n", r.name.text));
        }
        // **«C3c»: eine `group` erzeugt NICHTS, und sie darf nichts erzeugen.**
        //
        // Sie ist die Verbindungsaussage ueber zwei Traegern -- eine Invariante, die keine
        // `table` sagen kann, weil eine Tabelle nur ueber ihrem eigenen Traeger
        // quantifiziert (`U007`). **Was sie zur Laufzeit kostet, ist null.**
        //
        // *Der Sperrabdruck, den sie verlangt (`U001`-`U006`), ist eine Aussage ueber das
        // PROGRAMM und wird zur Uebersetzungszeit nachgerechnet* -- W6: was der Pruefer
        // entschieden hat, prueft die Maschine nicht noch einmal.
        ItemArt::Gruppe(_) => {}
        // **Lane C: a `concurrent` set declares which bodies may run together -- like a
        // `group` it is a statement about the program, checked at translation time
        // (`nebeneinander.rs`), and costs null at run time: it emits NOTHING.**
        ItemArt::Concurrent(_) => {}
        // **«C3b»: `rcu` erzeugt zwei Prototypen und keine Zeile Rumpf** -- genau wie eine
        // Sperre, und aus genau demselben Grund.
        //
        // Was RCU von einer Sperre unterscheidet, steht im Erzeugnis dann als das, was
        // FEHLT: es gibt kein `_nimm`, das jemanden aufhaelt. Der Lesebereich wird betreten
        // und verlassen; **ausgeschlossen wird niemand.** *Das ist die ganze Substanz des
        // Konstrukts, und die Absenkung macht sie sichtbar.*
        //
        // > **Die Gnadenfrist ist eine ANNAHME und keine Prüfung.** Dass nach der Ruecknahme
        // > des Zeigers kein Leser mehr in einem `observes` steht, stellt kein statischer
        // > Pass her -- `beispiele/31` sagt es selbst und schreibt `assume
        // > gnadenfrist_ist_abgelaufen` daneben. Der Erzeuger nennt das Primitiv und
        // > definiert es nicht.
        //
        // `reclaims` erzeugt nichts: **wo zurueckgegeben werden darf, rechnen `H011` und
        // `H012` zur Uebersetzungszeit nach** (W6). Der Ort steht als Kommentar daneben,
        // damit ein Leser des C ihn findet.
        ItemArt::Rcu(r) => {
            let n = &r.name.text;
            if let Some(o) = &r.gibt_zurueck {
                aus.push_str(&format!(
                    "\n/* rcu {n} reclaims {} -- WHERE a slot may be given back is checked at\n\
                     \x20* compile time (H011, H012); nothing of it is left for the run. */\n",
                    kommentartext(&o.text())
                ));
            } else {
                aus.push_str(&format!("\n/* rcu {n} */\n"));
            }
            aus.push_str(&format!(
                "void {n}_lese_start(void);\nvoid {n}_lese_ende(void);\n"
            ));
        }
        ItemArt::Assume(_) | ItemArt::Axiom(_) => {}
        ItemArt::Modul(_) | ItemArt::Use(_) => {}
        // **Die vier Formen der Maschinennaht** -- siehe die Funktionen am Ende dieser Datei.
        //
        // Sie schreiben **hinter** die Prototypen und nicht zwischen sie, weil sie auf
        // Erklaerungen ZUGREIFEN statt welche zu machen: eine gepruefte Bezugnahme auf
        // `dispatch` braucht dessen Prototyp, und die Quellreihenfolge einer Gabbro-Datei ist
        // frei -- `beispiele/11` erklaert `behandler` NACH dem `entry`, der ihn nennt.
        // *Dieselbe Sortierung, aus demselben Grund wie oben bei den Ruempfen.*
        ItemArt::Walk(w) => walk_(w, &mut rumpf, &namen, absagen),
        ItemArt::Entry(e) => eintritt(e, &mut rumpf, &ruempfe, &bezugskerne, absagen),
        ItemArt::Entrust(t) => anvertrauen(t, &mut rumpf, &namen, absagen),
        ItemArt::Boot(b) => bootstrecke(b, &mut rumpf, &namen, &ruempfe, &bezugskerne, absagen),
        // -- und die vier, die weiter abgelehnt werden, jetzt aber MIT GRUND -----------
        //
        // **Der Sammelzweig ist weg, und das ist der eigentliche Ertrag.** Ein `_`-Arm ist
        // die Stelle, an der ein neues Konstrukt still durchfaellt: wer morgen eine
        // `ItemArt` hinzufuegt, bekommt hier einen Uebersetzungsfehler statt einer Absage,
        // die nach einem Bauposten klingt.
        //
        // > **Und der Sammelzweig hat beim Verschwinden gleich etwas ueber sich gesagt.**
        // > Beim Ausschreiben standen zuerst vier Weigerungen hier -- fuer `reason`, `state`,
        // > `rcu` und `group`. **Drei davon senken laengst ab**, ein paar Dutzend Zeilen
        // > weiter oben, und `rustc` hat es sofort gemeldet: *unreachable pattern*. Ein
        // > `_`-Arm laesst nicht nur Neues durchfallen; **er laesst auch vergessen, was schon
        // > da ist.** Uebrig bleibt die eine, die wirklich offen ist.
        ItemArt::State(s) => weigere(
            absagen,
            s.span,
            "`state` -- the transitions are a proof device over a carrier that is declared \
             ELSEWHERE; which C object holds the state, and whether a transition is a check \
             or an assignment, the declaration does not say",
        ),
        // **A `syscall` lowers to its stub** -- prototype into `aus`,
        // definition into `rumpf`, exactly like `funktion` above. The stub
        // template is `syscall_stumpf` at the end of this file.
        ItemArt::Syscall(s) => {
            syscall_stumpf(
                s,
                &mut aus,
                &mut rumpf,
                &namen,
                &syscall_tabellen,
                baum,
                absagen,
            );
        }
        // **`assume` and `axiom` emit no code -- but they emit the PROMISE**
        // (see the header above): the profile blocks beside them emit
        // nothing at all. Their entries already stand in the emitted
        // header through `manifest::sammle` -- a second emission here
        // would print every mode twice.
        ItemArt::Profil(_) | ItemArt::ProfilBedarf(_) => {}
    });
    // **Lane E5: one `static const` table per accepted library call.**
    //
    // The translation stage ran at check time (`uebersetzung::einsaetze`,
    // recomputed here over the same tree -- W6: the emitter trusts the
    // checker and re-derives nothing beyond this list). Each payload stands
    // file-scope beside the tables it is typed as, before the bodies that
    // pass it: after the table storage above, before the counters and the
    // bodies below, so source order stays free. The walk is the same
    // deterministic tree order the collection above read, so two runs over
    // one tree emit the same C byte for byte; the C names match the map
    // entries by construction (same pure function of the call site). A call
    // the checker refused is not in the list, and the lowering arms keep
    // their refusal for it.
    {
        for e in crate::uebersetzung::einsaetze(baum) {
            let pl = format!("{}__nutzlast_{}_{}", e.funktion, e.von, e.bis);
            let mut glieder = String::new();
            for (i, w) in e.werte.iter().enumerate() {
                if i > 0 {
                    glieder.push_str(", ");
                }
                // The literal rule of the const tables (`const_table`): a
                // non-negative value in an unsigned word carries the `u` C
                // needs, anything else stands bare.
                let lit = if *w < 0 {
                    format!("{w}")
                } else {
                    format!("{w}u")
                };
                glieder.push_str(&format!("{{{lit}}}"));
            }
            aus.push_str(&format!(
                "\n/* Payload for `{}` (lane E5): the region, translated at compile time \
                 into {} value(s) -- the call below passes `&{pl}`. */\n\
                 static const {} {} = {{{{{glieder}}}}};\n",
                e.funktion,
                e.werte.len(),
                e.tabelle,
                pl
            ));
        }
    }
    // **«SG-24»: every counter of the unit, defined.** Between the declarations and
    // the bodies: after the table storage they read (`tabelle()` wrote it into `aus`
    // above), before the bodies that call them (`rumpf` joins below). Per-item
    // emission cannot carry them -- source order is free, so a counter emitted at
    // its function could precede its table -- and the bodies cannot either, being
    // what the counters are called from. *The same reason all prototypes precede
    // all bodies, one construct over.*
    {
        let mut zaehler = String::new();
        crate::fuer_jedes_item(baum, &mut |item| {
            if let ItemArt::Funktion(f) = &item.art {
                // `spec fn` emits nothing, and neither do its counters.
                if matches!(f.klasse, Some(FnKlasse::Spec)) {
                    return;
                }
                let eigen = eigene_sicht(f, &namen);
                zaehler_funktion(f, &eigen, &mut zaehler, absagen);
            }
        });
        aus.push_str(&zaehler);
    }
    // **Rotation helpers are GENERATED, not assumed -- and only the used ones.**
    // The same principle the word readers above answer to: an unused function in
    // the emitted C is a finding about the generator. Collection is a scan of
    // the lowered BODIES just before they join the unit: what is collected is
    // the helper NAME as `ruf` emits the call (`gabbro_rotl32(`), so the two
    // can never disagree the way a width read twice could -- the call site
    // reads types from the per-function view that exists only while a body is
    // lowered, and no pre-pass walk can see it. A user comment naming a helper
    // would over-collect; the over-collected body is `static inline`, which
    // neither compiler warns about when unused.
    {
        let mut dreh: BTreeSet<&'static str> = BTreeSet::new();
        for (n, _) in DREH_C {
            if rumpf.contains(&format!("{n}(")) {
                dreh.insert(*n);
            }
        }
        if !dreh.is_empty() {
            aus.push_str(
                "\n/* Bit rotation (PLAN-BITS §3). Generated, not assumed: C has no rotate. */\n",
            );
            for d in &dreh {
                aus.push_str(DREH_C.iter().find(|(n, _)| n == d).map(|(_, c)| *c).unwrap_or(""));
            }
        }
    }
    aus.push_str(&rumpf);
    aus
}

/// **P20 — the correspondence call site: item-level certificate rows beside the C.**
///
/// One row per lowered item whose top-level C shape is one of the 19 named forms
/// ([`corrcert::CForm`]), in lowering order, returned beside the C string. The C
/// itself goes through the unchanged `emittiere_mit` on the unchanged tree, so the
/// artefact is byte-identical with the uncertified run — pinned by
/// `c_ist_mit_und_ohne_zertifikat_gleich` below. *A sidecar that rewrites the
/// artefact would be a second emitter wearing a certificate's clothes* (the same
/// rule `kostenledger` keeps).
///
/// The obligation convention is the row index: `gabbro_site == c_site ==` position
/// among the rowed items, so the recomputer's list is `0 .. rows`. Statement- and
/// expression-level shapes (`zuweisung`, the if-form, `ruf`, …) are not item
/// shapes;
/// their rows need the builder threaded through the body walks and stay booked —
/// see `korr_form` and `messung/CORRCERT-ANBINDUNG.md`.
pub fn emittiere_mit_corr(
    baum: &Programm,
    absagen: &mut Absagen,
    bau: crate::gatter::Bau,
) -> (String, crate::corrcert::CorrCert) {
    // The same gate the generator itself reads: rows cover what the C covers —
    // a gated item owes no C and no row.
    let gefiltert;
    let baum = match bau {
        crate::gatter::Bau::Auslieferung => {
            gefiltert = crate::gatter::ohne_gatter(baum);
            &gefiltert
        }
        crate::gatter::Bau::Pruefbau => baum,
    };
    let c = emittiere_mit(baum, absagen, crate::gatter::Bau::Pruefbau);
    let mut sammler = crate::corrcert::CorrCertBuilder::neu();
    let mut zeile: u32 = 0;
    crate::fuer_jedes_item(baum, &mut |item| {
        if let Some(form) = korr_form(&item.art) {
            sammler.aufzeichnen(zeile, zeile, form);
            zeile += 1;
        }
    });
    (c, sammler.zertifikat())
}

/// **P20 — the item-to-form table: which lowered item earns a correspondence row.**
///
/// Total over `ItemArt`: every variant stands here exactly once, either with the
/// form its emitting arm demonstrably writes or with the reason it earns no row.
/// An item that lowers to no C site (scaffolding, ghost, refusal) owes no row —
/// exactly like a gated item owes no C. A row without a C site would BE the extra
/// effect `ohne_extra` refuses.
fn korr_form(art: &ItemArt) -> Option<crate::corrcert::CForm> {
    use crate::corrcert::CForm::*;
    match art {
        // `#define N lit` — the arm writes the literal value, or refuses.
        // **Lane 111:** a const TABLE writes `static const` storage instead --
        // the `Statisch` row, like every other static array the emitter lays down.
        ItemArt::Konst(k) => match &k.wert.art {
            ExprArt::ArrayLit(_) => Some(Statisch),
            _ => Some(Literal),
        },
        // Static storage, with or without initializer; `tabelle()` writes the same
        // kind of storage for tables, `accumulates` one cell per core.
        // **«E4»:** `arena()` writes the buffer plus its counter -- the same
        // kind of storage, one construct over.
        ItemArt::Statisch(_) | ItemArt::Tabelle(_) | ItemArt::Arena(_) | ItemArt::Accumulates(_) => {
            Some(Statisch)
        }
        // `_Atomic T name;` — the atomic shape, not plain storage.
        ItemArt::Atomic(_) => Some(Atomar),
        // Prototypes and nothing else: the lock pair, the `rcu` pair, and a
        // bodyless foreign function (its prototype always stands above).
        ItemArt::Lock(_) | ItemArt::Rcu(_) => Some(Extern),
        ItemArt::Funktion(f) => korr_form_funktion(f),
        // Definitions and declarations whose shape is not among the 19: struct and
        // reader declarations, device descriptions, the `reason` enumeration,
        // check bodies, dispatch and startup. Booked against the open ruling
        // table (§19.4), not guessed here.
        ItemArt::Typ(_)
        | ItemArt::Format(_)
        | ItemArt::Device(_)
        | ItemArt::Reason(_)
        | ItemArt::Check(_)
        | ItemArt::Walk(_)
        | ItemArt::Entry(_)
        | ItemArt::Entrust(_)
        | ItemArt::Boot(_) => None,
        // Scaffolding, ghost, or refusal: no C site, no row. A `syscall`
        // stands here too: its stub body is generated statements around one
        // `__asm__`, and statement-level rows belong to the body-walk
        // follow-up -- exactly like a defined block function above, which
        // earns no row here either.
        ItemArt::Modul(_)
        | ItemArt::Use(_)
        | ItemArt::Assume(_)
        | ItemArt::Axiom(_)
        | ItemArt::Gruppe(_)
        | ItemArt::Concurrent(_)
        | ItemArt::State(_)
        // **«E6»: a profile block earns no correspondence row.** It lowers
        // to no C -- its entries are manifest lines, not forms.
        | ItemArt::Profil(_)
        | ItemArt::ProfilBedarf(_)
        | ItemArt::Syscall(_) => None,
    }
}

/// The function arm of the table: only the item shapes the prototype and body arms
/// demonstrably write. A defined block body is statements — booked for the
/// body-walk follow-up, not rowed here.
fn korr_form_funktion(f: &FnDecl) -> Option<crate::corrcert::CForm> {
    use crate::corrcert::CForm::*;
    // A `spec fn` emits nothing at all — the early return beside `funktion`.
    if matches!(f.klasse, Some(FnKlasse::Spec)) {
        return None;
    }
    // An `asm` body is one `__asm__ __volatile__` block («OPT3»).
    if matches!(f.rumpf, FnRumpf::Asm(_)) {
        return Some(AsmEins);
    }
    // `-> never` is `_Noreturn` on the prototype, defined or not.
    if matches!(&f.ergebnis, Some(TypExpr::Never(_))) {
        return Some(Noreturn);
    }
    // A bodyless foreign function is a prototype and nothing else.
    if !matches!(f.rumpf, FnRumpf::Block(_) | FnRumpf::Asm(_)) {
        return Some(Extern);
    }
    None
}

/// **P20 — the derivation call site for `certemit`: one certificate per folded const.**
///
/// For every `const` whose value the emitter folds itself ([`konst_zahl`]: a `Zahl`
/// literal — the only shape the emitter folds, nothing else), the certificate that
/// `certemit::emit` prints over `CertExpr::Lit`: the exact value with the exact
/// range, beside the `#define` the Konst arm writes. Float consts, `u64::max`
/// words and `konstwert`-folded names are NOT covered: their source spelling is
/// not a literal, and a `Lit` certificate over them would certify the emitter's
/// reading instead of the checked expression. The boundary is the folder's.
pub fn konst_zertifikate(
    baum: &Programm,
) -> Vec<(String, crate::certemit::Certificate)> {
    let empty_ctx = crate::certemit::Ctx::new(vec![]);
    let empty_world = crate::certemit::World::default();
    let mut aus = Vec::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Konst(k) = &item.art {
            if let Some(n) = konst_zahl(&k.wert) {
                let z = crate::certemit::emit(
                    &crate::certemit::CertExpr::Lit(n),
                    &empty_ctx,
                    &empty_world,
                );
                aus.push((k.name.text.clone(), z));
            }
        }
    });
    aus
}

#[cfg(test)]
mod korr_anbindung {
    use super::*;

    fn baum_fuer(quelle: &str) -> (Programm, Absagen) {
        gabbro_syntax::lies("anbindung", quelle)
    }

    fn mikro() -> &'static str {
        "const K : u32 = 3;\n\
         static mut Z : u32 = 0;\n\
         lock RIEGEL protects { Z } rank 0 held <= 8 ops;\n\
         impl fn f() -> u32 effects { pure } costs <= 1 ops {\n\
         \x20   return K;\n\
         }\n"
    }

    #[test]
    fn c_ist_mit_und_ohne_zertifikat_gleich() {
        // The sidecar must not move the artefact: same tree, same build, same C.
        let (baum, mut absagen) = baum_fuer(mikro());
        let (certified, _) = emittiere_mit_corr(
            &baum,
            &mut absagen,
            crate::gatter::Bau::Auslieferung,
        );
        let (baum2, mut absagen2) = baum_fuer(mikro());
        let plain = emittiere_mit(&baum2, &mut absagen2, crate::gatter::Bau::Auslieferung);
        assert_eq!(certified, plain);
    }

    #[test]
    fn zeilen_tragen_form_und_ordnung() {
        let (baum, mut absagen) = baum_fuer(mikro());
        let (_, cert) = emittiere_mit_corr(
            &baum,
            &mut absagen,
            crate::gatter::Bau::Auslieferung,
        );
        // const, static, lock — in lowering order; the plain function body is
        // statements and earns no item row.
        assert_eq!(
            cert.to_json(),
            concat!(
                "{\"sites\":[{\"gabbroSite\":0,\"cSite\":0,\"form\":\"literal\"},",
                "{\"gabbroSite\":1,\"cSite\":1,\"form\":\"statisch\"},",
                "{\"gabbroSite\":2,\"cSite\":2,\"form\":\"extern\"}]}"
            )
        );
        let obliegen: Vec<u32> = (0..3).collect();
        assert!(cert.pruefe_gegen(&obliegen).gueltig());
    }

    #[test]
    fn reine_typen_einheit_hat_leeres_gueltiges_zertifikat() {
        // Nothing among the 19 is lowered: no rows, no obligation, valid.
        let (baum, mut absagen) = baum_fuer("type Z = u32 in 0 .. 10;\n");
        let (c, cert) = emittiere_mit_corr(
            &baum,
            &mut absagen,
            crate::gatter::Bau::Auslieferung,
        );
        let plain = emittiere_mit(
            &baum_fuer("type Z = u32 in 0 .. 10;\n").0,
            &mut gabbro_syntax::lies("x", "").1,
            crate::gatter::Bau::Auslieferung,
        );
        assert_eq!(c, plain);
        assert!(cert.zeilen().is_empty());
        assert!(cert.pruefe_gegen(&[]).gueltig());
        assert!(!cert.pruefe_gegen(&[0]).gueltig());
    }

    #[test]
    fn asm_und_noreturn_tragen_ihre_form() {
        let quelle = "extern fn abbruch() -> never effects { diverges } costs <= 1 ops;\n\
             extern fn hol() -> u32 effects { pure } costs <= 1 ops;\n\
             impl fn schranke()\n\
             \x20   effects { pure }\n\
             \x20   costs <= 1 ops\n\
             \x20   arch x86_64\n\
             \x20   = asm {\n\
             \x20       \"sfence\"\n\
             \x20       in { }\n\
             \x20       clobbers { memory }\n\
             \x20   };\n";
        let (baum, mut absagen) = baum_fuer(quelle);
        let (_, cert) = emittiere_mit_corr(
            &baum,
            &mut absagen,
            crate::gatter::Bau::Auslieferung,
        );
        // A foreign never-function carries `_Noreturn` on its prototype —
        // `noreturn`; a bodyless foreign function without one is a bare
        // prototype — `extern`. The `asm` body: one `__asm__` — `asmEins`.
        assert_eq!(
            cert.to_json(),
            concat!(
                "{\"sites\":[{\"gabbroSite\":0,\"cSite\":0,\"form\":\"noreturn\"},",
                "{\"gabbroSite\":1,\"cSite\":1,\"form\":\"extern\"},",
                "{\"gabbroSite\":2,\"cSite\":2,\"form\":\"asmEins\"}]}"
            )
        );
    }

    #[test]
    fn konst_zertifikate_tragen_exakte_bereiche() {
        let (baum, _) = baum_fuer(mikro());
        let zs = konst_zertifikate(&baum);
        assert_eq!(zs.len(), 1);
        assert_eq!(zs[0].0, "K");
        assert_eq!(zs[0].1.term, "(.lit 3)");
        assert_eq!(
            zs[0].1.claimed,
            Some(crate::certemit::Range::new(3, 3))
        );
        assert_eq!(
            zs[0].1.to_json(),
            concat!(
                "{\"term\":\"(.lit 3)\",\"claimed\":[3,3],",
                "\"sides\":[\"lit 3: exact (3, 3) -- HOLDS\"]}"
            )
        );
    }

    #[test]
    fn beispiel_67_traegt_asm_zeilen() {
        // End to end over a shipped sample: the certificate is emitted on the run,
        // beside C the uncertified path writes byte-identically.
        let quelle = include_str!("../../../beispiele/67-befehlsebene.gab");
        let (baum, mut absagen) = baum_fuer(quelle);
        let (certified, cert) = emittiere_mit_corr(
            &baum,
            &mut absagen,
            crate::gatter::Bau::Auslieferung,
        );
        let (baum2, mut absagen2) = baum_fuer(quelle);
        let plain = emittiere_mit(&baum2, &mut absagen2, crate::gatter::Bau::Auslieferung);
        assert_eq!(certified, plain);
        assert!(
            cert.zeilen()
                .iter()
                .any(|z| z.form == crate::corrcert::CForm::AsmEins),
            "67 lowers asm bodies, so the run must carry asmEins rows"
        );
        let obliegen: Vec<u32> = (0..cert.zeilen().len() as u32).collect();
        assert!(cert.pruefe_gegen(&obliegen).gueltig());
    }
}

/// **`bounded N ops` ist ein OPERATIONSBUDGET, kein Schleifenzaehler — und das ist die
/// Entscheidung, die diese Funktion traegt.**
///
/// `SPRACHE.md` ist eindeutig: die Einheit ist `ops`, und Zeitmasse sind an D10 gestorben
/// (*"eine Iterationszahl ist eine Eigenschaft des Programms, eine Zeitmessung nicht"*). Wer
/// die Zusage zur Laufzeit durchsetzen will, teilt also durch die Kosten EINES Durchgangs:
///
/// ```text
///     Durchgaenge  =  floor( N / Kosten-je-Durchgang )
/// ```
///
/// **Die Kosten rechnet der Kostenpass, nicht der Erzeuger** — ein zweiter Kostenrechner waere
/// genau das zweite Register, gegen das W7 steht. Steht die Zahl nicht fest, weigert sich der
/// Erzeuger (`C001`), statt eine zu raten.
///
/// > **Und der Vergleich mit `traverse` ist der eigentliche Ertrag der Absenkung:** eine
/// > Traversierung braucht **keinen** Laufzeitzaehler, weil ihre Domaene durch Konstruktion
/// > endlich ist. Ein `retry` braucht einen, weil seine Bedingung von der WELT abhaengt — und
/// > genau darum verlangt die Grammatik dort ein `on_exceeded` und hier keines. *Die
/// > Absenkung macht sichtbar, was die beiden Formen unterscheidet.*
fn retry_schranken(baum: &Programm) -> HashMap<u32, i128> {
    let mut aus = HashMap::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let ItemArt::Funktion(f) = &item.art else { return };
        let FnRumpf::Block(b) = &f.rumpf else { return };
        sammle_retry(baum, modul, f, b, &mut aus);
    });
    aus
}

fn sammle_retry(baum: &Programm, modul: &str, f: &FnDecl, b: &Block, aus: &mut HashMap<u32, i128>) {
    for s in &b.anweisungen {
        // **The one decision this collector makes: does this statement OPEN a `retry`?**
        if let StmtArt::Schleife(sch) = &s.art {
            if let Schleife::Retry(r) = sch.as_ref() {
                let budget = crate::umgebung::Umgebung::sammle(baum)
                    .konst_wert(modul, &r.schranke);
                let je_gang = crate::kosten::durchgangskosten(baum, modul, f, r, HashMap::new());
                if let (Some(n), Some(c)) = (budget, je_gang) {
                    if c > 0 && n / c > 0 {
                        aus.insert(r.span.von, n / c);
                    }
                }
            }
        }
        // **What the catch-all promised here was false.** The four arms it stood behind
        // reached `locks`, `match`, `narrow` and the body of a `retry` -- and nothing else.
        // A `retry` inside an `if`, inside a `breaking`, inside an `observes`, inside the
        // `else` of a `let … else`, inside the `update` body of an `exchange` or inside a
        // `forever`/`traverse` therefore had **no entry in the bound map at all**, and the
        // lowering answered that with `C001`: *"`bounded … ops` -- the per-pass cost is not
        // fixed"*. **The cost was fixed; the collector never got there.** A refusal that
        // names the wrong reason is the failure this file is built against, one step short
        // of a silent one.
        for k in crate::unterbloecke(s) {
            sammle_retry(baum, modul, f, k, aus);
        }
    }
}

/// **Das Gegenteil von `weigere` -- und es steht hier NUR, damit eine Mutation es einsetzen
/// kann.** Ein Erzeuger, der eine Form still uebergeht, ist der eine Fehler, gegen den dieses
/// Modul gebaut ist; `mutiere-pruefer.py` setzt diese Funktion an die Stelle einer Absage und
/// prueft, dass etwas faellt.
#[allow(dead_code)]
fn nichts_tun(_a: &mut Absagen, _s: gabbro_syntax::span::Span, _w: &str) {}

/// **C001 -- the emitter refuses instead of guessing.**
/// **`.bytes = 0` is not C, and until today both designator sites wrote it** (2026-09-02).
///
/// Measured over an unchanged tree:
///
/// ```gabbro
/// pub type Text = { bytes : [u8; KAP], len : u32 in 0 .. KAP, };
/// pub static mut T : Text = Text(bytes: 0, len: 0);
/// ```
///
/// `gabbro pruefe` said `5 items, 0 errors, 0 hints`, `gabbro emit` wrote
/// `static Text T = { .bytes = 0, .len = 0 };`, and `cc -std=c11 -O0 -Wall -Wextra -Werror`
/// answered **`error: missing braces around initializer [-Werror=missing-braces]`**. The
/// compound-literal site had it too: `return (Text){ .bytes = 0, .len = 0 };`. *The checker
/// reported clean over C that does not build* -- the one thing this emitter promises not to
/// do, and it is not a refusal it was missing but a pair of braces.
///
/// **The zero is the whole set of values an array field can carry here.** `= 0` is the
/// aggregate zero-initialiser; C has no assignment of one array to another, so any other
/// value at this position has no lowering. It is REFUSED by name rather than braced and
/// hoped for -- *a generator that guesses undoes every pass in front of it.*
fn feldsetzer(
    verbund: &str,
    marke: &gabbro_syntax::ast::Ident,
    a: &Expr,
    u: &Namen,
    absagen: &mut Absagen,
) -> String {
    let feldtyp = u.verbundfeld.get(&(verbund.to_string(), marke.text.clone()));
    if matches!(feldtyp, Some(TypExpr::Feld(_))) {
        if konst_zahl(a) != Some(0) {
            weigere(
                absagen,
                a.span,
                "an array field initialised with anything but `0` -- C has no assignment \
                 of one array to another, and `{0}` is the whole set this form carries",
            );
        }
        return format!(".{} = {{0}}", marke.text);
    }
    format!(".{} = {}", marke.text, ausdruck(a, u, absagen))
}

fn weigere(absagen: &mut Absagen, span: gabbro_syntax::span::Span, was: &str) {
    absagen.schiebe(
        Absage::fehler("C001", span, format!("no lowering: {was}")).mit_notiz(
            "the emitter refuses by name instead of emitting something plausible -- a \
             generator that guesses undoes every pass in front of it",
        ),
    );
}

/// **The atomic OBJECT a place names: its C designator, the C type of one element, and
/// the declaration's two memory orders.**
///
/// The four arms that touch an atomic (`publishes`, `awaits`, `exchange`, and the bare
/// read in `ort`) each asked `u.atomics.get(&place.text())` for themselves. That answers
/// the scalar and nothing else -- `REGEL[r]` is not a key of that map and never will be,
/// so all four refused an indexed atomic by the same accident. **One reader now, and it
/// answers the two shapes an atomic can have:**
///
/// * `GESAMT` -> `("GESAMT", "uint32_t", …)` -- byte for byte what the four arms built
///   before, because `Ort::text()` of a suffix-free place IS the name;
/// * `REGEL[r]` over `atomic REGEL : [u32; 256]` -> `("REGEL[r]", "uint32_t", …)`.
///
/// **Exactly ONE index suffix, and nothing else.** A field suffix on an atomic names
/// nothing (`N271` in the checker -- an atomic carries a scalar or an array of scalars,
/// never a record), and two indices would need a nested array, which no declaration can
/// write. *The refusal for everything else stays where it was: the caller sees `None`
/// and says `C001` in its own words.*
///
/// **The index is an ordinary expression and is lowered as one** -- so the bound is the
/// bound M1 proved (`M103`, and `N380` where it could not be proved at all), and nothing
/// is re-checked at run time that the checker decided (W6). *A place whose index the
/// checker could not bound never reaches this function: `gabbro emit` writes no C for a
/// unit with errors.*
fn atom_target(
    o: &Ort,
    u: &Namen,
    absagen: &mut Absagen,
) -> Option<(String, String, &'static str, &'static str)> {
    if let Some((typ, sp, ld)) = u.atomics.get(&o.text()) {
        return Some((o.text(), typ.clone(), sp, ld));
    }
    if o.suffixe.len() != 1 || !u.atom_arrays.contains_key(&o.basis.text) {
        return None;
    }
    let OrtSuffix::Index(idx) = &o.suffixe[0] else {
        return None;
    };
    let (typ, sp, ld) = u.atomics.get(&o.basis.text)?;
    Some((
        format!("{}[{}]", o.basis.text, ausdruck(idx, u, absagen)),
        typ.clone(),
        sp,
        ld,
    ))
}

/// **CForm zeigerArithmetik: a `*` at the end of the RESOLVED C type is a
/// pointer, and nothing else in this emitter's type vocabulary ends with one.**
/// Integers, `bool`, `float`/`double`, struct names and the `void` of an empty
/// parameter list never match; a pointer (`const Text *`, `uint8_t *`) always
/// does. The check reads the type, not the spelling -- and the map behind the
/// resolution is function-scoped (`eigene_sicht`), so a same-named integer in
/// another scope never matches. Withdrawn 2026-09-11 on the unscoped map,
/// re-added on the scoped one.
fn ist_zeigerwort(t: &Option<String>) -> bool {
    t.as_deref().is_some_and(|c| c.trim_end().ends_with('*'))
}

/// **CForm doubleTyp (lane 142): exactly the mixed pair.** Both sides carrying
/// the same width is a pure computation of that width; a literal carries no
/// width until its neighbour decides it (`None`); an integer beside a float is
/// the checker's `F005`, not this arm.
fn ist_gemischt_float_double(x: &Option<String>, y: &Option<String>) -> bool {
    matches!(
        (x.as_deref(), y.as_deref()),
        (Some("float"), Some("double")) | (Some("double"), Some("float"))
    )
}

/// **`try_from` and NOT `as`, and that is the same defect as `registerlagen()` had.**
///
/// Gabbro's literals are `u128`; this returns `i128`. `*n as i128` is silent where the two
/// disagree, and `u128::MAX as i128` is `-1`. Until 2026-09-02 that number went straight
/// into the generated file:
///
/// ```text
/// entry e vector 340282366920938463463374607431768211455 arch x86_64 { … }
///   ->  3 items, 0 errors, 0 hints
///   ->  /* entry e -- arch x86_64
///        * vector -1
/// ```
///
/// **The emitter did not fail. It wrote a different number**, and the vector is what the
/// hardware indexes its table with. `static mut A : [u64; u128::MAX]` came out the other
/// way: the length arrived as `-1` and the refusal read *"array of length zero -- C has no
/// such object"*, a diagnostic that is wrong about the very number it is quoting. *A rule
/// that is right because two errors cancel is not a rule that holds* -- written on
/// 2026-09-01 about `N047`, and true here one file over.
///
/// Sixteen sites read this: bank stride and count, register offsets, array lengths, `walk`
/// levels and node width, the entry vector, the nesting bound, `const` and `static` values.
/// **They all already have a `None` branch** -- "not a constant this unit can read" -- and
/// that is where a number the emitter cannot represent belongs. *The fence, and not the
/// widening: `i128` is not too narrow for any address this back end writes; the cast was
/// simply lying about which numbers fit.*
///
/// Found by `instrumente/fuzze-grenzen.py`, by reading the C it emitted for the rungs the
/// checker waved through.
fn konst_zahl(e: &Expr) -> Option<i128> {
    match &e.art {
        ExprArt::Zahl(n) => i128::try_from(*n).ok(),
        _ => None,
    }
}

/// **Lane 111:** lower a const table to one `static const` C array.
///
/// The element C word comes from `ctyp_primitiv` (primitives only -- a named
/// element type has no C spelling here, and the callers turn the `None` into
/// `C001` by name); every value comes from the checker's own folder
/// (`Umgebung::konst_wert`, W7). The bound is the literal's element count:
/// on a checked tree it equals the declared count (`K191` holds that), and
/// on an unchecked one the literal is the honest number. `None` anywhere is
/// `C001` at the caller, never a guess.
///
/// **Lane 170:** a nested table lowers to one multi-dimensional `static
/// const` array (`[[1, 2], [3, 4]]` over `[[u32; 2]; 2]` becomes
/// `static const uint32_t T[2][2] = {{1u, 2u}, {3u, 4u}};`). The word is
/// read at the INNERMOST element (primitives only, the same rule the flat
/// table follows); every dimension's bound is the literal's own count down
/// the first column -- on a checked tree every row holds the declared count
/// (`N286` holds that), and on an unchecked one the literal is the honest
/// number, the same rule the flat table follows. A row where the spine
/// still declares an array, or a value where it does not, is `None`
/// (`N285` holds that on a checked tree).
fn const_table(
    k: &KonstDecl,
    elements: &[Expr],
    module: &str,
    tree: &Programm,
) -> Option<String> {
    let TypExpr::Feld(_) = &k.typ else {
        return None;
    };
    // The spine, outermost first: each `Feld` peels one dimension.
    let mut tiefen: Vec<&ArrayTy> = Vec::new();
    let mut rest = &k.typ;
    while let TypExpr::Feld(a) = rest {
        tiefen.push(a.as_ref());
        rest = &a.element;
    }
    let word = ctyp_primitiv(rest)?;
    let env = crate::umgebung::Umgebung::sammle(tree);
    let unsigned = word.starts_with('u');
    // The declaration's dimensions down the first column.
    let mut dekl = String::new();
    let mut erste: &[Expr] = elements;
    for _ in &tiefen {
        dekl.push_str(&format!("[{}]", erste.len()));
        let Some(vorderste) = erste.first() else { break };
        let ExprArt::ArrayLit(zeile) = &vorderste.art else { break };
        erste = zeile;
    }
    let literal = const_wert_zeile(elements, 0, &tiefen, &env, module, unsigned)?;
    Some(format!(
        "\nstatic const {word} {}{dekl} __attribute__((unused)) = {literal};\n",
        k.name.text,
    ))
}

/// One row of a (possibly nested) const-table literal as C: `{1u, 2u}`, rows
/// nested inside rows. Every scalar comes from the checker's own folder;
/// `None` anywhere is `C001` at the caller, never a guess.
fn const_wert_zeile(
    eintraege: &[Expr],
    tiefe: usize,
    tiefen: &[&ArrayTy],
    env: &crate::umgebung::Umgebung,
    modul: &str,
    vorzeichenlos: bool,
) -> Option<String> {
    let mut teile = Vec::with_capacity(eintraege.len());
    if tiefe + 1 == tiefen.len() {
        for e in eintraege {
            let w = env.konst_wert(modul, e)?;
            if w < 0 || !vorzeichenlos {
                teile.push(w.to_string());
            } else {
                teile.push(format!("{w}u"));
            }
        }
    } else {
        for e in eintraege {
            let ExprArt::ArrayLit(zeile) = &e.art else {
                return None;
            };
            teile.push(const_wert_zeile(zeile, tiefe + 1, tiefen, env, modul, vorzeichenlos)?);
        }
    }
    Some(format!("{{{}}}", teile.join(", ")))
}

/// **A literal as C writes it -- with the `u` where C needs one, and `None` where C has no
/// type at all** (`D3`/`D4`, 2026-09-03).
///
/// A bare decimal constant in C takes the first of `int`, `long`, `long long` that holds it.
/// Past `2^63 - 1` none of them does, so GCC gives it `unsigned long` and says so:
/// *integer constant is so large that it is unsigned*. The value is legal Gabbro -- `u64`
/// reaches exactly that far -- and legal C **with the suffix**. Without one the tree's own
/// compile gate refuses the unit, which is what `beispiele/gift/643` measured.
///
/// **The suffix is added exactly where it is NEEDED and nowhere else**, and that boundary was
/// chosen against a named risk rather than for tidiness. The probe's own header names it:
/// `-Wconversion` and `-Wsign-conversion` read these same literals -- `zaehle-c-formen.py`
/// runs both over the whole corpus -- so *a suffix added everywhere would trade this error
/// for a different one*. Below `2^63` the emitted text is unchanged, byte for byte, and the
/// corpus was measured to confirm it: the C of all 612 versioned `.gab` before and after.
///
/// **Past `2^64 - 1` there is no C integer type**, and then the honest answer is not a
/// spelling but a refusal. `unsigned long long` is at least 64 bits and C promises no more;
/// `2^64` itself draws *integer constant is too large for its type* however it is written.
/// That is `beispiele/gift/644`, one door further in.
///
/// > *`i128` is not the fence here, and that is the lesson `konst_zahl` learned one door
/// > up.* Its `try_from` stopped the emitter writing `-1` for `2^128 - 1`; it did not stop
/// > `2^64`, which fits `i128` perfectly well. **A repair at the reader is not a repair at
/// > the writer** -- so the fence stands where the C types end.
/// **C's largest object, in bytes** -- `PTRDIFF_MAX` on every target this back end writes.
///
/// C requires the difference of two pointers into one object to be representable as a
/// `ptrdiff_t`, so an object wider than `PTRDIFF_MAX` bytes cannot exist. GCC names exactly
/// this number in its own refusal (*size of array `A` exceeds maximum object size
/// 9223372036854775807*), which is where the value is read from rather than assumed.
const C_OBJEKT_MAX: u128 = i64::MAX as u128;

/// **The largest value C lets an ENUMERATOR carry** -- and a `reason` lowers to an `enum`
/// (`D13`, 2026-09-03).
///
/// C11 6.7.2.2p2 is a constraint and not a recommendation: an enumeration constant *"shall
/// be an integer constant expression that has a value representable as an `int`"*. GCC takes
/// a wider one as an extension under `-Wall -Wextra -Werror` and names the rule the moment
/// `-Wpedantic` is added, which is where this number was read off rather than assumed.
///
/// **`int` is taken as 32 bits.** C promises only 16, so on a narrower target this fence
/// under-refuses -- the same safe direction `cbreite` takes, and for the same reason: what
/// slips through, `cc` still refuses. Every target this back end writes has a 32-bit `int`.
const C_ENUM_MAX: u128 = i32::MAX as u128;

/// **The bytes this emitter will write into ONE initialiser** -- and the number is its own,
/// because C has none to lend (`D12`, 2026-09-03).
///
/// `C_OBJEKT_MAX` above is read off the standard and off GCC's own message. There is no such
/// number here: ISO C sets no limit on how many elements an initialiser may hold, and
/// C11 5.2.4.1's translation limits speak of nesting and of identifiers, not of this. **The
/// bound in practice is patience and memory**, so a number that fences it is a statement
/// about this back end and belongs beside the back end with its cost written out.
///
/// One mebibyte, and the reasoning is at the single site that reads it -- including the
/// corpus measurement that says what headroom it leaves.
const C_INITIALISIERER_MAX: u128 = 1 << 20;

/// The width in bytes of an emitted C type name -- `None` where this emitter cannot say.
///
/// **Only the fixed-width names get an answer, and that is the whole of the claim.**
/// `uint32_t` is four bytes wherever it exists; a `struct` from this unit is not something
/// a name lookup can size. Callers treat `None` as one byte, which is the smallest any C
/// object has -- an under-estimate, and therefore a refusal that fires too seldom rather
/// than too often.
fn cbreite(c: &str) -> Option<u128> {
    Some(match c {
        "uint8_t" | "int8_t" | "bool" | "char" => 1,
        "uint16_t" | "int16_t" => 2,
        "uint32_t" | "int32_t" | "float" => 4,
        "uint64_t" | "int64_t" | "double" => 8,
        _ => return None,
    })
}

fn czahl(n: u128) -> Option<String> {
    if n <= i64::MAX as u128 {
        Some(n.to_string())
    } else if n <= u64::MAX as u128 {
        Some(format!("{n}u"))
    } else {
        None
    }
}

/// `czahl` with the refusal already written -- for the sinks that have a span to hang it on.
fn czahl_oder_absage(n: u128, span: gabbro_syntax::span::Span, absagen: &mut Absagen) -> String {
    match czahl(n) {
        Some(t) => t,
        None => {
            weigere(
                absagen,
                span,
                "an integer literal past `2^64 - 1` -- no C integer type holds it, with or \
                 without a suffix, and `cc` says `integer constant is too large for its \
                 type`. There is no spelling to write here",
            );
            String::new()
        }
    }
}

/// Ein Typausdruck als Text -- **nur zum VERGLEICHEN zweier Deklarationen**, nicht zum
/// Absenken. `TypExpr` traegt Spannen und ist darum nicht vergleichbar.
///
/// **A word with no C name gets its OWN SOURCE TEXT as the key here**, never another word's.
/// That is not a lowering, it is a comparison key: two different unknown words have to stay
/// different, or this comparison would hold two unequal declarations to be equal.
fn typtext(t: &TypExpr) -> String {
    match t {
        TypExpr::Int(i) => intty(i).unwrap_or_else(|| i.wort.to_string()),
        TypExpr::Bool(_) => "bool".into(),
        TypExpr::Pfad(p) => p.teile.iter().map(|i| i.text.clone()).collect::<Vec<_>>().join("::"),
        TypExpr::Index { tabelle, optional, .. } => {
            format!("{}index into {}", if *optional { "option " } else { "" }, tabelle.text)
        }
        TypExpr::Zeiger(z) => format!("ptr {}", typtext(&z.ziel)),
        TypExpr::Feld(a) => format!("[{}]", typtext(&a.element)),
        andere => format!("?{:?}", std::mem::discriminant(andere)),
    }
}

/// **Ein `type P = { a : u32, b : bool }` wird ein C-Verbund -- und HIER ist es einer.**
///
/// Bei `format` steht die entgegengesetzte Entscheidung, mit ihrem Grund: *ein Format ist
/// eine Zusage ueber BYTES*, und ein C-Verbund haette dort eine Layoutbehauptung eingefuehrt,
/// die die Deklaration nicht macht. **Ein `type` macht sie.** Es sagt nichts ueber Bytes,
/// Versaetze oder Reihenfolge im Speicher -- es sagt „diese Felder gehoeren zusammen", und
/// genau das ist ein C-`struct`.
///
/// > *Derselbe Satz, zweimal verschieden beantwortet, weil zweimal etwas anderes dasteht.*
///
/// Was der Erzeuger **nicht** tut: `packed`, `aligned` oder eine Reihenfolgezusage. Wer ein
/// Verbund ueber eine Schnittstelle schickt, will ein `format`; wer ihn im Programm herumreicht,
/// will diesen hier. Die C-Freiheit beim Auffuellen ist damit kein Verlust, sondern die
/// Abwesenheit einer Zusage, die niemand gegeben hat.
fn verbund(t: &TypDecl, aus: &mut String, u: &Namen, absagen: &mut Absagen) {
    let Some(TypExpr::Verbund(felder, _)) = &t.rumpf else {
        return;
    };
    aus.push_str("\ntypedef struct {\n");
    for f in felder {
        // **Ein Bitfeld in einem `type` wird abgelehnt, nicht weggelassen.** `@ hi:lo` ist
        // eine Aussage ueber die Lage in einem Wort; sie gehoert in ein `format` oder an ein
        // Register. Sie hier stillschweigend fallen zu lassen hiesse, ein Programm zu
        // erzeugen, das die Deklaration nicht mehr erfuellt.
        if f.bitpos.is_some() || f.offset_into.is_some() {
            weigere(
                absagen,
                f.name.span,
                "a `type` record carries no bit position and no `offset_into` -- \
                 those are statements about a layout, and a `format` makes them",
            );
            continue;
        }
        // **Ein Feldtyp, der ein FELD ist** -- `bytes : [u8; KAP]`. In C steht die Laenge
        // hinter dem Namen und nicht beim Typ, also gibt es dafuer keinen `ctyp`.
        // *Die Laenge kommt aus der Deklaration, wie bei `count N` -- geraten wird sie
        // nicht.*
        // Lane 170 spells the whole spine the same way: `m : [[u32; 4]; 3]`
        // becomes `uint32_t m[3][4]` out of `feld_deklarator` -- at one dimension
        // the line below is byte-identical to the one it replaces.
        if matches!(&f.typ.typ, TypExpr::Feld(_)) {
            let Some((el, suffix)) = feld_deklarator(&f.typ.typ, u) else {
                weigere(absagen, f.name.span, "array field type -- element or length");
                continue;
            };
            aus.push_str(&format!("    {el} {}{};\n", f.name.text, suffix));
            continue;
        }
        // **A function pointer field, like an array, puts its name INSIDE the type**
        // («B8», 2026-08-21) -- `bool (*bereit)(void);`, C11 §6.7.6.3.
        //
        // *That is why it cannot go through `ctyp`:* `ctyp` answers with a type that a name
        // is appended to, and a C function pointer declarator has no such form. The same
        // reason the array branch above exists, and the same shape of answer.
        if let TypExpr::FnZeiger(z) = &f.typ.typ {
            match fnzeiger_deklarator(z, &f.name.text, u) {
                Some(d) => aus.push_str(&format!("    {d};\n")),
                None => weigere(absagen, f.name.span, "function pointer field type"),
            }
            continue;
        }
        match ctyp(&f.typ.typ, u) {
            Some(c) => aus.push_str(&format!("    {c} {};\n", f.name.text)),
            None => weigere(absagen, f.name.span, "field type"),
        }
    }
    aus.push_str(&format!("}} {};\n", t.name.text));
}

/// Die Laenge eines Feldtyps: eine Zahl oder ein `const`-Name (der als `#define` schon im
/// Kopf des Erzeugnisses steht). **Alles andere ist keine Laenge, die dieser Erzeuger kennt.**
fn feldlaenge(e: &Expr, u: &Namen) -> Option<String> {
    match &e.art {
        ExprArt::Zahl(n) => czahl(*n),
        ExprArt::Ort(o) if o.suffixe.is_empty() && u.konstanten.contains(&o.basis.text) => {
            Some(o.basis.text.clone())
        }
        _ => None,
    }
}

/// **«C2»: ein `tagged type` wird `struct { marke; union { … } }` -- und die Marke ist ein
/// `enum`.**
///
/// ```c
/// typedef enum { ObjektArt_Speicher, ObjektArt_Endpunkt } ObjektArt_marke;
/// typedef struct { ObjektArt_marke marke; union { uint64_t Speicher; uint32_t Endpunkt; } last; } ObjektArt;
/// ```
///
/// ## Warum ein `enum` und nicht das schmalste Wort
///
/// Die Breite der Marke ist Handwerk; **welcher Typ sie traegt, ist es nicht.** Mit einem
/// `enum` wird `switch` ohne `default` unter `-Wswitch` zu einem **zweiten Leser von
/// `D005`**: der Pruefer verlangt das erschoepfende `match` ohne Sammelzweig, und der
/// C-Uebersetzer prueft dieselbe Zusage noch einmal. *Zwei unabhaengige Leser derselben
/// Zusage -- dieselbe Bauart wie `-Wmissing-field-initializers` beim Verbundkonstruktor.*
///
/// Und die Breite kostet nichts: die Vereinigung richtet ohnehin auf ihr breitestes Glied
/// aus. **Ein `uint8_t` haette dieselbe Verbundgroesse und keinen zweiten Leser.**
///
/// ## Was das Typrecht angeht -- und warum es hier NICHT entschieden wird
///
/// Eine C-`union` ist wohldefiniert, solange nur das ZULETZT GESCHRIEBENE Glied gelesen
/// wird. Genau das erzwingt `D005` eine Ebene hoeher: das `match` liest das Glied, das die
/// Marke nennt. *Der Erzeuger darf sich darauf berufen, weil ein Pass es haelt* -- er
/// entscheidet die Frage nicht selbst.
fn markiert(t: &TypDecl, aus: &mut String, u: &Namen, absagen: &mut Absagen) {
    let Some(varianten) = u.markierte.get(&t.name.text) else {
        return;
    };
    let n = &t.name.text;
    aus.push_str(&format!("\ntypedef enum {{\n"));
    for v in varianten {
        aus.push_str(&format!("    {n}_{},\n", v.name.text));
    }
    aus.push_str(&format!("}} {n}_marke;\n\ntypedef struct {{\n    {n}_marke marke;\n"));
    // **Eine Vereinigung nur, wenn es etwas zu vereinigen gibt.** Ein `tagged type`, dessen
    // Varianten alle ohne Nutzlast sind, ist eine reine Fallunterscheidung -- und eine
    // leere `union` gibt es in C nicht.
    let mit_last: Vec<&Variante> = varianten.iter().filter(|v| v.nutzlast.is_some()).collect();
    if !mit_last.is_empty() {
        aus.push_str("    union {\n");
        for v in mit_last {
            let Some(nl) = &v.nutzlast else { continue };
            match ctyp(nl, u) {
                Some(c) => aus.push_str(&format!("        {c} {};\n", v.name.text)),
                None => {
                    weigere(absagen, v.name.span, "`tagged` variant payload type");
                    return;
                }
            }
        }
        aus.push_str("    } last;\n");
    }
    aus.push_str(&format!("}} {n};\n"));
}

/// A table becomes a slot struct plus a carrier struct with a fixed-size array.
///
/// **`count N` is the whole reason the array is fixed.** Without it `index into T` has no
/// upper bound from the declaration, and this lowering would have to be a pointer plus a
/// length -- i.e. exactly the shape Gabbro exists to avoid.
fn tabelle(t: &Tabelle, aus: &mut String, u: &Namen, absagen: &mut Absagen) {
    let Some(n) = &t.kapazitaet else {
        weigere(absagen, t.span, "table without `count` -- the array would have no size");
        return;
    };
    // **`count 0` -- and this arm exists because every SIBLING zero already had one.**
    //
    // The emitter refuses a `static` array of length zero, a slot field of length zero, a
    // `walk` node array of length zero and `walk levels 0`. It wrote `T_slot slots[0];` for a
    // table, which ISO C forbids and GCC takes as an extension -- so `cc -Wall -Wextra
    // -Werror` said nothing and `-Wpedantic` said *ISO C forbids zero-size array*.
    //
    // > *The table was the one zero-length array with no arm, not the one with a reason.*
    //
    // Measured 2026-09-02 by `instrumente/fuzze-erzeuger.py`; the poison probe is
    // `beispiele/gift/647`. **The other half of the same zero is in `umgebung.rs`**, where a
    // `count 0` was FILTERED OUT of the capacity map -- so `M103` had no bound to read and
    // `T.slots[0]` on an empty table gave `0 errors`. *A zero dropped is a zero unchecked.*
    if konst_zahl(n) == Some(0)
        || matches!(&n.art, ExprArt::Ort(o) if u.konstwert.get(&o.text()) == Some(&0))
    {
        weigere(
            absagen,
            t.name.span,
            "`table` with `count 0` -- C has no zero-size array, and every statement over an \
             empty table holds vacuously",
        );
        return;
    }
    aus.push_str(&format!("\ntypedef struct {{\n"));
    if let Some(slot) = &t.slot {
        for f in &slot.felder {
            let c = match &f.typ {
                SlotTyp::Typ(t) => ctyp(t, u),
                // `intty wrapping` -- the wraparound is DECLARED («B32»), so the C type is
                // the plain unsigned word whose wrap C already defines.
                SlotTyp::Wrapping(i) => intty(i),
            };
            match c {
                Some(c) => aus.push_str(&format!("    {c} {};\n", f.name.text)),
                None => weigere(absagen, f.name.span, "field type"),
            }
        }
    }
    aus.push_str(&format!("}} {}_slot;\n\ntypedef struct {{\n", t.name.text));
    let laenge = zahltext(n, absagen);
    aus.push_str(&format!(
        "    {}_slot slots[{}];\n}} {};\n",
        t.name.text, laenge, t.name.text
    ));
    // **Und wo die Quelle die Tabelle bei ihrem NAMEN nennt, bekommt sie ihren Speicher.**
    // *Nur dort*: eine ungenutzte Groesse im erzeugten C waere ein Befund ueber den
    // Erzeuger, nicht ueber den Anwender.
    if u.tabellenglobal.contains(&t.name.text) {
        aus.push_str(&format!(
            "/* `{n}` is addressed by NAME: the table IS the storage (beispiele/09). */\n\
             static {n} {n}_speicher;\n",
            n = t.name.text
        ));
    }
    // **Der Sonderwert fuer `option index into T`, und er hat eine PRAEMISSE.**
    //
    // Er ist die Laenge selbst -- der eine Wert, den ein gueltiger Index nach `count N` und
    // M1 nie annimmt. **Aber nur, solange `N` ins Maschinenwort passt.** Der Index senkt zu
    // `uint32_t` ab; ist `N = 2^32`, faellt der Sonderwert mit dem ERSTEN Slot zusammen, und
    // `None` ist von `Some 0` nicht mehr zu unterscheiden.
    //
    // > **Diese Praemisse stand nirgends** -- nicht im Registereintrag, nicht in `SPRACHE.md`,
    // > nicht hier. Sie kam am 2026-08-17 aus der Formalisierung
    // > (`beweise/Option_Sonderwert.thy`, `sonderwert_kollidiert_bei_vollem_wort` und
    // > `kodiere_wort_injektiv`). *In der Praxis war sie erfuellt -- `count 80256` gegen
    // > `2^32` -- aber erfuellt und geprueft sind zwei Zustaende.*
    const WORTGRENZE: i128 = 1 << 32;
    match u.kapazitaet.get(&t.name.text) {
        Some(&n) if n < WORTGRENZE => {
            aus.push_str(&format!("#define {}_NONE ({})\n", t.name.text, laenge));
        }
        Some(&n) => weigere(
            absagen,
            t.span,
            &format!(
                "`count {n}` fills the index word: the `option` sentinel would be `2^32`, \
                 which collides with slot 0 -- see beweise/Option_Sonderwert.thy, M-1"
            ),
        ),
        None => weigere(
            absagen,
            t.span,
            "`count` does not resolve to a number, so the `option` sentinel cannot be \
             checked against the index word",
        ),
    }
    ops(t, aus, u, absagen);
}

/// **`arena A capacity lo .. hi of T;` («E4»).**
///
/// A static array of `hi` elements beside a `used` counter -- no heap
/// allocation in the C, ever. The reservation `lo` emits nothing: it is a
/// checker fact (which `alloc` owes its `else`), not a second object.
/// `reset` stores zero into the counter; `alloc` bumps it. The storage is
/// conditional on use (`arenen_global`), like a table's: an untouched
/// declaration emits its type and no object.
fn arena(a: &ArenaDecl, aus: &mut String, u: &Namen, absagen: &mut Absagen) {
    let Some((hi_expr, element)) = u.arenen.get(&a.name.text) else {
        weigere(
            absagen,
            a.span,
            "arena without a collected bound -- the array would have no size",
        );
        return;
    };
    let Some(c) = ctyp(element, u) else {
        weigere(
            absagen,
            a.span,
            "arena element type -- the buffer holds values of one C type, \
             and this one has no lowering",
        );
        return;
    };
    let hi = zahltext(hi_expr, absagen);
    if hi.is_empty() {
        return;
    }
    aus.push_str(&format!(
        "\ntypedef struct {{\n    {c} buf[{hi}];\n    uint32_t used;\n}} {n}_arena;\n",
        n = a.name.text
    ));
    // **Where the source names the arena, it gets its storage.** *Only there*:
    // like the table, unused bulk in the generated C is a finding about the
    // generator, not the user.
    if u.arenen_global.contains(&a.name.text) {
        aus.push_str(&format!(
            "static {n}_arena {n}_arena_speicher;\n",
            n = a.name.text
        ));
    }
}

/// **Cut (c): the generated mutations -- and the PROOF writes them, not I.**
///
/// `beweise/Table_Ops_Erhaltung.thy` has three parts, and the third decides what comes out
/// here:
///
/// | Theorem | word | what it says |
/// |---|---|---|
/// | `einfuegen_erhaelt` | `insert` | preserves, under *fresh* and *parent reachable* |
/// | `blatt_loeschen_erhaelt` | `remove` | preserves, under *`s` is a leaf* |
/// | `umhaengen_erhaelt` | `relabel` | preserves, under *new parent reachable* and *`s` not on its chain* |
///
/// > **`relabel` was refused until 2026-08-28, evening, and the refusal was not wrong -- it
/// > was incomplete.** It said the re-hanging breaks `wohlgeformt` (`umhaengen_faellt`), and
/// > never what it breaks ON. What stood there was the third word of a CLOSED vocabulary
/// > that emitted nothing and nobody could call -- *a clause with no redeemer*, at 127
/// > measured corpus sites.
/// >
/// > **The theorem came first, as K100's second gate demands** (`verbund.konstruktor` is the
/// > booked precedent). `umhaengen_erhaelt` (U-3) names the condition; `umhaengen_faellt`
/// > stays, and `G-1`/`G-2` show the old counterexample fails at THAT premise and no other.
/// > *`messung/OPS-RELABEL.md` weighs the three forms the condition could take.*
///
/// **And `remove` resets the WHOLE slot, not just the flag.** `sigma(s := None)` is a slot
/// that carries no value any more -- `beispiele/47` shows why that is not zeal: its invariant
/// `marke_null_wenn_frei` breaks if `marke` survives the removal. *That is the item a hand
/// mutation forgets and a generator cannot forget.*
/// **The carrier of a named type -- ONE reader for all three callers.**
///
/// `vorzeichen`, `ctyp` and `ruecksetzwert` each need the same thing: `type Zaehler = u32 in
/// 0 .. 65535` behind the name `Zaehler`. Until 2026-08-31 all three looked into the map
/// themselves, which is four direct looks at one card (`zaehle-karten.py` counts them, and
/// its reason is `M103` in `m1.rs`: a look that only hits a fully qualified name goes silent
/// inside a `module` block).
///
/// **One reader is one place to fix that**, and four are four places to forget it.
fn traegertyp<'a>(name: &str, u: &'a Namen) -> Option<&'a TypExpr> {
    u.typen.get(name)
}

/// **Does a `~` stand anywhere inside this expression?** -- the one question the `const`
/// refusal above needs, and it is asked over the whole tree rather than at the top node:
/// `const H : u32 = (~G) & 255;` is unfoldable for the same reason as `~G` itself, and a
/// look at the root alone would have sent it to the wrong sentence.
fn enthaelt_bitnicht(e: &Expr) -> bool {
    match &e.art {
        ExprArt::Unaer(UnOp::BitNicht, _) => true,
        ExprArt::Unaer(_, x) | ExprArt::Klammer(x) => enthaelt_bitnicht(x),
        ExprArt::Binaer(_, a, b) => enthaelt_bitnicht(a) || enthaelt_bitnicht(b),
        ExprArt::Ruf(r) => r.argumente.iter().any(enthaelt_bitnicht),
        // **Lane E1:** a `~` in the arguments unfolds nothing either; the
        // region is raw tokens, not Gabbro code, and is never scanned.
        ExprArt::LibraryCall(r) => r.args.iter().any(enthaelt_bitnicht),
        // **«SG-24»** -- a `~` inside the counted predicate unfolds nothing either.
        ExprArt::Zaehle { rumpf, .. } => crate::ausdruecke_im_praedikat(rumpf)
            .into_iter()
            .any(enthaelt_bitnicht),
        // **Lane 111:** a `~` inside a table element unfolds nothing either --
        // the elements are ordinary expressions and read here like any other.
        ExprArt::ArrayLit(es) => es.iter().any(enthaelt_bitnicht),
        ExprArt::Zahl(_)
        | ExprArt::Gleitkomma { .. }
        | ExprArt::Wahr
        | ExprArt::Falsch
        | ExprArt::Ort(_)
        | ExprArt::FnWert(_)
        | ExprArt::Eingebaut(_)
        | ExprArt::Alt(_)
        | ExprArt::Ergebnis
        | ExprArt::Grund { .. } => false,
    }
}

/// A range BOUND as a number -- like `konst_zahl`, but the minus sign counts.
///
/// **`konst_zahl` deliberately does not read one**: its other callers are a table length and
/// a register offset, and a negative one of those is nonsense. `i32 in -4 .. 4` is not, and
/// reading its lower bound as "unreadable" would refuse a field whose reset value is plainly
/// derivable.
fn grenzzahl(e: &Expr) -> Option<i128> {
    match &e.art {
        ExprArt::Unaer(UnOp::Negativ, i) => Some(-konst_zahl(i)?),
        _ => konst_zahl(e),
    }
}

/// **The reset value of ONE slot field -- derived, and `None` where it cannot be.**
///
/// `T_remove` clears a slot: the theorem it carries (`beweise/Table_Ops_Erhaltung.thy`,
/// `blatt_loeschen_erhaelt`) says the slot carries NO value any more, so EVERY field is
/// reset. Until 2026-08-31 that read *`T_NONE` for an optional index, `0` for everything
/// else*, and the `0` was a `_` arm. Measured over 499 corpus files: 29 hits.
///
/// **`messung/proben/probe-wildcard-ruecksetzung.gab` is what the `_` cost.** It checks with
/// `0 errors` and the emitter wrote two wrong values into one function:
///
/// ```text
/// t->slots[s].stufe   = 0;   `u32 in 1 .. 9`   -- OUTSIDE the field's own range
/// t->slots[s].nachbar = 0;   `index into Verz` -- a VALID index, i.e. a claimed edge
/// ```
///
/// Two different defects out of one line. The first has the emitter break the type the
/// checker had just enforced -- *a generator that violates the pass in front of it undoes
/// it.* The second writes a lie: a non-optional index has no `None`, and `0` is not neutral,
/// it is the first slot.
///
/// So the value is DERIVED now: `T_NONE` for the optional edge, `0` for a truth value and
/// for a range that contains the zero, and otherwise nothing -- the caller refuses by name.
///
/// `tiefe` bounds the walk through named types; a cyclic `type` declaration must not turn a
/// refusal into a stack overflow.
fn ruecksetzwert(t: &SlotTyp, tn: &str, u: &Namen, tiefe: u32) -> Option<String> {
    if tiefe > 16 {
        return None;
    }
    let x = match t {
        // `u32 wrapping`: the wraparound is DECLARED («B32»), the range is the whole word,
        // and the zero lies in it.
        SlotTyp::Wrapping(_) => return Some("0".to_string()),
        SlotTyp::Typ(x) => x,
    };
    match x {
        // The sentinel is `count` itself -- `beweise/Option_Sonderwert.thy`.
        TypExpr::Index { optional: true, .. } => Some(format!("{tn}_NONE")),
        // And the non-optional one has no sentinel at all. **That is the refusal**, not an
        // oversight: the type says every value of it names a slot.
        TypExpr::Index { optional: false, .. } => None,
        TypExpr::Bool(_) => Some("0".to_string()),
        TypExpr::Int(i) => match &i.bereich {
            None => Some("0".to_string()),
            Some(b) => {
                let (Some(von), Some(bis)) = (grenzzahl(&b.von), grenzzahl(&b.bis)) else {
                    // A bound this emitter cannot read is not a bound it may ignore.
                    return None;
                };
                let bis = if b.exklusiv { bis - 1 } else { bis };
                (von <= 0 && 0 <= bis).then(|| "0".to_string())
            }
        },
        // A named type is its underlying one -- read off, not guessed.
        TypExpr::Pfad(p) => {
            let n = &p.teile.last()?.text;
            ruecksetzwert(&SlotTyp::Typ(traegertyp(n, u)?.clone()), tn, u, tiefe + 1)
        }
        // Pointer, float, array, record, function pointer, `never`, a tagged type: **no
        // reset value is derived here.** Each of them would need its own statement about
        // what "empty" means, and this emitter refuses by name rather than writing a
        // plausible zero.
        //
        // Lane 256: a bounded string joins that list -- nothing about `string max N`
        // says what "empty" lowers to, so there is no reset value either. (This arm
        // is forced by exhaustiveness over `TypExpr`; it changes no existing
        // behaviour -- the variant cannot arise from any pre-string source.)
        TypExpr::Zeiger(_)
        | TypExpr::Float(_)
        | TypExpr::Feld(_)
        | TypExpr::Verbund(..)
        | TypExpr::FnZeiger(_)
        | TypExpr::Never(_)
        | TypExpr::Zeichenkette { .. }
        | TypExpr::Varianten(..) => None,
    }
}

fn ops(t: &Tabelle, aus: &mut String, u: &Namen, absagen: &mut Absagen) {
    if t.ops.is_empty() {
        return;
    }
    // `D011` holds this in the checker; it stands here because a generator without that map
    // would silently zero a different field -- and a generator that guesses cancels every
    // pass in front of it.
    let Some(belegt) = &t.belegt else { return };
    let tn = &t.name.text;
    let elter = t.baum.as_ref().and_then(|b| b.elter.as_ref());
    // **`__attribute__((unused))` is a MEASUREMENT from today on, not a habit** (2026-08-28).
    //
    // Until this morning every generated operation carried it, because nothing in this
    // language could call one -- *a prohibition (`D001`) with a replacement nobody could
    // reach.* The call form exists since `messung/OPS-RUFFORM.md`; the attribute therefore
    // has to say whether THIS unit calls THIS operation, and where it does, it must go. An
    // attribute claiming a function is unused while a line below calls it is a false
    // statement about the unit, and `pruefe-emission.sh` would never see it fall.
    let koepfe = crate::opsruf::koepfe(t);
    let leise = |wort: &str| {
        if u.opsgerufen.contains(&format!("{tn}::{wort}")) {
            String::new()
        } else {
            " __attribute__((unused))".to_string()
        }
    };
    // The premises, with the parameter names of the emitted head. **They are the same
    // objects `D012` holds against the call site** -- one producer, so the C states what the
    // checker demands instead of paraphrasing it.
    let pflicht = |wort: &str| -> String {
        let zeilen: Vec<String> = koepfe
            .iter()
            .filter(|k| k.wort == wort)
            .flat_map(|k| k.kopfform())
            .map(|z| format!("\x20     requires {z}\n"))
            .collect();
        if zeilen.is_empty() {
            "\x20  This table has no `parent` edge, so no slot can name another as parent:\n\
             \x20  `blatt sigma s` holds of every `s`, and the caller owes NOTHING here.\n"
                .to_string()
        } else {
            format!(
                "\x20  What the caller owes, held against the call site by `D012`:\n{}",
                zeilen.concat()
            )
        }
    };
    for w in &t.ops {
        match w.text.as_str() {
            "insert" => {
                aus.push_str(&format!(
                    "\n/* `ops insert` -- beweise/Table_Ops_Erhaltung.thy, `einfuegen_erhaelt`.\n\
                     \x20  The premises are the theorem's: the slot is FRESH (`sigma n = None`)\n\
                     \x20  and the parent is REACHABLE (`erreicht sigma p`). What this function\n\
                     \x20  buys is Teil I: the proof falls ONCE per operation, not per call site.\n\
                     {} */\n",
                    pflicht("insert")
                ));
                match elter {
                    Some(e) => aus.push_str(&format!(
                        "static void {tn}_insert({tn} *t, uint32_t n, uint32_t p){};\n\
                         static void {tn}_insert({tn} *t, uint32_t n, uint32_t p) {{\n\
                         \x20   t->slots[n].{} = p;\n\
                         \x20   t->slots[n].{} = 1;\n}}\n",
                        leise("insert"),
                        e.text,
                        belegt.text
                    )),
                    None => aus.push_str(&format!(
                        "static void {tn}_insert({tn} *t, uint32_t n){};\n\
                         static void {tn}_insert({tn} *t, uint32_t n) {{\n\
                         \x20   t->slots[n].{} = 1;\n}}\n",
                        leise("insert"),
                        belegt.text
                    )),
                }
            }
            "remove" => {
                aus.push_str(&format!(
                    "\n/* `ops remove` -- beweise/Table_Ops_Erhaltung.thy, `blatt_loeschen_erhaelt`.\n\
                     \x20  Premise the theorem charges: `blatt sigma s` -- nobody names `s` as\n\
                     \x20  parent. `sigma(s := None)` is a slot that carries NO value any more, so\n\
                     \x20  EVERY field is reset. beispiele/47 shows why that is not zeal: its\n\
                     \x20  invariant `marke_null_wenn_frei` breaks if a field survives removal.\n\
                     {} */\n\
                     static void {tn}_remove({tn} *t, uint32_t s){};\n\
                     static void {tn}_remove({tn} *t, uint32_t s) {{\n",
                    pflicht("remove"),
                    leise("remove")
                ));
                // **Every field is asked, and the refusal does not stop at the first.** A
                // table with two underivable fields would otherwise be reported as having
                // one, and the second would surface only after the first was fixed --
                // *a measurement that stops at the first hit answers a different question.*
                let mut fehlt = false;
                for f in t.slot.iter().flat_map(|sd| sd.felder.iter()) {
                    match ruecksetzwert(&f.typ, tn, u, 0) {
                        Some(wert) => {
                            aus.push_str(&format!("    t->slots[s].{} = {wert};\n", f.name.text))
                        }
                        None => {
                            fehlt = true;
                            weigere(
                                absagen,
                                f.name.span,
                                &format!(
                                    "`ops remove` on `{}`: this emitter has no reset value \
                                     for that field type. A cleared slot carries NO value \
                                     any more, so every field is reset -- and `0` is a value \
                                     like any other: outside a declared range it breaks the \
                                     type the checker just enforced, and in a non-optional \
                                     `index into T` it is the FIRST slot, not the absence \
                                     of one",
                                    f.name.text
                                ),
                            );
                        }
                    }
                }
                if fehlt {
                    return;
                }
                aus.push_str("}\n");
            }
            // **And ONLY the parent edge is written -- that is the whole body, and the
            // reason it may be the whole body is a proof and not an intuition.**
            //
            // The model's `umhaengen` replaces the slot; on a slot with further fields the C
            // here keeps them. Where that differs is a FREE `s`: the model makes it
            // occupied, the C leaves it free. **The C state then has FEWER occupied slots
            // than the model state, and `wohlgeformt` is a `forall` over the occupied ones**
            // -- an all-statement over a smaller set does not fall. *That is why no
            // occupancy premise is charged: `umhaengen_erhaelt` does not ask for one, and an
            // invented duty would have looked stricter and meant less.*
            "relabel" => match elter {
                Some(e) => aus.push_str(&format!(
                    "\n/* `ops relabel` -- beweise/Table_Ops_Erhaltung.thy, `umhaengen_erhaelt` (U-3).\n\
                     \x20  The premises are the theorem's: the NEW parent is REACHABLE\n\
                     \x20  (`erreicht sigma p`) and the re-hung slot does NOT lie on that\n\
                     \x20  parent's chain, that parent itself included -- U-3's second. That\n\
                     \x20  one is why this operation was refused until 2026-08-28: the folder\n\
                     \x20  had the counterexample (`umhaengen_faellt`) and not the condition.\n\
                     \x20  `G-1`/`G-2` show that counterexample fails at THIS premise and no\n\
                     \x20  other -- it is a witness that the condition is needed, not a bar.\n\
                     {} */\n\
                     static void {tn}_relabel({tn} *t, uint32_t s, uint32_t p){};\n\
                     static void {tn}_relabel({tn} *t, uint32_t s, uint32_t p) {{\n\
                     \x20   t->slots[s].{} = p;\n}}\n",
                    pflicht("relabel"),
                    leise("relabel"),
                    e.text
                )),
                // **«B41b», word for word: a missing edge is an ANSWER, not a gap.** A table
                // whose `tree` names no `parent` has no field to re-hang, and the emitter
                // does not guess one -- the same move `ancestors of` makes one file over.
                None => weigere(
                    absagen,
                    w.span,
                    "`ops relabel` on a table whose `tree` names no `parent` edge -- there is \
                     no field to re-hang. `umhaengen_erhaelt` is a statement about the parent \
                     chain, and without that chain the operation has no subject",
                ),
            },
            other => weigere(
                absagen,
                w.span,
                &format!("`ops {other}` -- no generated meaning for this word"),
            ),
        }
    }
}

/// **Ein Geraeteregister wird ein volatiler Zugriff an `basis + Versatz` -- und KEIN Feld.**
///
/// Ein C-Verbund haette dieselbe Schwaeche wie beim `format`: die Versaetze stehen in der
/// Deklaration, die Fuellung eines `struct` bestimmt der Uebersetzer. Hier kommt hinzu, dass
/// ein Registerzugriff **nicht wegoptimiert werden darf** -- dafuer steht `volatile`, und es
/// ist die eine Stelle, an der die Absenkung dem C-Uebersetzer etwas VERBIETEN muss.
///
/// ```c
/// typedef struct { volatile uint8_t *basis; } Ring;
/// /* r.AVAIL_IDX  ->  (*(volatile uint16_t *)((r)->basis + 0x102)) */
/// ```
///
/// **Der Zugriff wird als ORT abgesenkt, nicht als Funktionspaar.** Damit traegt `+=` sich
/// von selbst, und die Rechteregel bleibt beim Pruefer: `R002`/`R003` weisen ein Schreiben
/// auf `class r` ab, und **was der Pruefer entschieden hat, prueft die Maschine nicht noch
/// einmal** (W6).
///
/// **Nur `at mmio` wird abgesenkt.** `at dma` verlangt Barrieren, und *welche* Barriere ein
/// `dma`-Zugriff braucht, ist eine Aussage ueber das Speichermodell -- dieselbe Axiomschicht
/// wie bei der Paarung, und der Pruefer baut sie ausdruecklich nicht (M3, `SPRACHE.md`).
/// `at normal` waere gar kein Geraetezugriff.
/// **The one name `at dma` demands.** It stands here and nowhere else: a magic string in two
/// places is two registers over one thing (W7).
///
/// *It is deliberately not a new grammar word.* Regel A does not carry one: the corpus has a
/// single `at dma` site, and `assume … falsifier …` already exists and already travels into
/// the certificate. **A fixed name costs no notation; a clause would.**
const ANNAHME_DMA: &str = "dma_kohaerent";

fn geraet(d: &Device, aus: &mut String, u: &Namen, absagen: &mut Absagen) {
    // **`at dma` lowers under a NAMED assumption since 2026-08-26 -- and refuses without it.**
    //
    // Which barrier a DMA access needs is a statement about the memory model, and the
    // generator does not build it. *But refusing outright made the obligation unpayable:*
    // `H = 0` over the fragment corpus was unreachable for F4, and not because of missing
    // work -- because of a decision.
    //
    // The move is the one K100.2 made for «B19»/«B38»/«B39»: **not discharge it, but carry
    // it by NAME with a probe.** The unit must declare
    //
    //     assume dma_kohaerent "…" falsifier <probe>;
    //
    // and then the access lowers exactly like `at mmio` -- a `volatile` access at
    // `basis + offset`. What the assumption buys is written out in `SPRACHE.md` and printed
    // into the C header by `manifest::sammle`, so the reader of the C sees what it rests on.
    //
    // > **`at normal` stays refused, and NOT for the same reason.** A `normal` access needs
    // > no barrier at all -- there the refusal is about whether it is a device access in the
    // > first place. *Two refusals under one text was the older mistake; they are two now.*
    if matches!(d.raum, Raum::Normal) {
        weigere(
            absagen,
            d.span,
            "`device … at normal` -- an access into the ordinary space is not a device \
             access, and what a `device` block would mean there is not decided",
        );
        return;
    }
    // **`at port` LOWERS since 2026-09-02, and the refusal that stood here is withdrawn.**
    //
    // From 2026-08-31 to today this was the third refusal in this function and the third for
    // a reason of its own: `at normal` above asks whether it is a device access at all, `at
    // dma` below asks which barrier, and this one asked nothing -- **it took back a wrong
    // lowering.** `device SerialCom1 at port { reg LSR : u8 @0x3FD … }` checked with 0 errors
    // and emitted `(((*(volatile uint8_t *)(d->basis + 1021)) >> 5) & 1u)`; `1021` is
    // `0x3FD`, the PORT NUMBER, handed out as an offset onto a memory pointer.
    //
    // The refusal named Rule A as its reason and put a number on it: *"zero `device … at
    // port` in 426 files"*. **`messung/proben/probe-port-nachfrage.gab` is the one that
    // number was waiting for** -- a 16550 at COM1, the very device the paragraph above names
    // as its example, checking with 0 errors and 0 hints.
    //
    // > *Rule A has two halves and the second is quoted less often:* no construct without
    // > measured demand -- **and no refusal without a measured defect.** Once the demand is
    // > written, "nobody asks" is no longer a reason.
    //
    // WHAT `in`/`out` DEMANDS THAT A VOLATILE LOAD DOES NOT
    // -----------------------------------------------------
    // Five things, and each one is a refusal below or a line in `portzugriff`:
    //
    // 1. **A port NUMBER, not an address.** `in`/`out` take a 16-bit unsigned port number,
    //    in `dx` or as an 8-bit immediate -- the constraint `"Nd"` is exactly that pair. So
    //    the handle carries a `uint16_t`, not a `volatile uint8_t *`, and the constructor
    //    casts to the number and not to a pointer.
    // 2. **The width picks the INSTRUCTION.** `inb`/`inw`/`inl` and `outb`/`outw`/`outl`, and
    //    that list ends at 32 bits. **There is no 64-bit port access on x86** -- a `reg X :
    //    u64` at a port device is refused by name below, where `at mmio` lowers it.
    // 3. **The access is not an lvalue.** The paragraph over this function states the mmio
    //    decision: *"the access lowers as a PLACE and not as a function pair. That way `+=`
    //    carries itself."* `in` and `out` ARE a function pair with no place between them, so
    //    every form that needed the place twice needs the pair written out -- and a compound
    //    assignment, which had carried itself, is refused by name.
    // 4. **The number must FIT.** The port space is 16 bits wide and ends there; a register
    //    offset past `0xffff` and a base parameter wider than `u16` are both refused, because
    //    the alternative is a silent truncation into a port that answers.
    // 5. **The instruction is x86 and nothing else.** Hence the `arch` demand right below.
    //
    // **The way out already existed and this is a wiring job.** `beispiele/36-asm.gab`:18
    // writes `outb` today through an `asm` body with `effects`, `costs`, `clobbers` and
    // `arch x86_64`, and this emitter lowers it to `__asm__ __volatile__` with operand lists.
    // Both constructs stood in the tree, both correct, and *that one could lower to the other
    // belonged to neither* -- `OA4` in pure form.
    if matches!(d.raum, Raum::Port) {
        // **`arch x86_64` at a port device -- the second half of the same promise**, and it
        // did not stand either. `SPRACHE.md` § *the sixth address space*: a `port` device is
        // *"declarable only under `arch x86_64`"*, and the probe carried none and was taken.
        //
        // The demand is `ANNAHME_DMA`'s move one item over: the emitter does not guess which
        // machine this is, it **demands that the unit say so**. Any clause that carries an
        // `arch` word answers -- an `entry`, an `entrust`, a `boot`, a function, an `assume`.
        //
        // > *Why the demand sits at the DEVICE and not at the function that reads it.* The
        // > `in` instruction lives in exactly one place per register: the accessor this
        // > block emits. A body that calls `Com1_LSR_in(c)` contains portable C and nothing
        // > else, so an `arch` word there would guard a line that needs no guarding. **The
        // > accessor is emitted whether or not any function calls it**, which is the other
        // > half of the same argument.
        if !u.architekturen.contains("x86_64") {
            let genannt: Vec<&str> = u.architekturen.iter().map(|s| s.as_str()).collect();
            let wo = if genannt.is_empty() {
                "this unit names no architecture at all".to_string()
            } else {
                format!("this unit names only `{}`", genannt.join("`, `"))
            };
            weigere(
                absagen,
                d.span,
                &format!(
                    "`device … at port` in a unit that does not declare `arch x86_64` -- \
                     {wo}. A port access lowers to an `in`/`out` instruction, and that \
                     instruction exists on x86 and nowhere else; SPRACHE.md makes a port \
                     device declarable only under `arch x86_64`. Say the machine at an \
                     `entry`, a `boot`, an `entrust`, a function or an `assume` -- the \
                     emitter demands the word, it does not guess it"
                ),
            );
            return;
        }
        // **A bank in the port space is refused, and it is a refusal BY FORM.**
        //
        // `bank FRR at CAP.FRO * 16 stride 16 count 256` puts its base in a register the
        // driver reads at run time. In the memory space that is address arithmetic and the
        // accessor carries it. In the port space the sum `base + i * stride + offset` must
        // land inside 16 bits, and **no clause in the declaration bounds it there** -- `count`
        // bounds the index, nothing bounds the base. Emitting the `in` anyway would truncate
        // into a port that answers.
        //
        // *Rule A points the same way:* zero banks at a port device in the corpus, and the
        // hardware the space is made of (`0x3f8`, `0xcf8`/`0xcfc`, PIC, PIT) is fixed ports,
        // not a strided array.
        if !d.baenke.is_empty() {
            weigere(
                absagen,
                d.baenke[0].span,
                "`bank` in a `device … at port` -- a bank base is a value read at run time, \
                 and the port space is 16 bits wide with no clause in the declaration that \
                 bounds `base + i * stride + offset` inside it. In the memory space that sum \
                 is address arithmetic; here it would be a silent truncation into a port \
                 that answers",
            );
            return;
        }
        // **The base is a port number and must fit in one.** `device Com1(basis : u64)`
        // would hand `(uint16_t)basis` to the instruction and drop everything above bit 15
        // without a word -- the same class of defect as the offset that stood here before,
        // one level up.
        if let Some(p) = d.parameter.first() {
            match ctyp(&p.typ, u).as_deref() {
                Some("uint8_t") | Some("uint16_t") => {}
                Some(c) => {
                    weigere(
                        absagen,
                        p.name.span,
                        &format!(
                            "the base of a `device … at port` is declared `{c}`, and a port \
                             number is 16 bits -- the handle would truncate it silently. \
                             Declare the base at `u8` or `u16`, or at a named type over one"
                        ),
                    );
                    return;
                }
                None => {
                    weigere(
                        absagen,
                        p.name.span,
                        "the base of a `device … at port` has a type this emitter cannot \
                         lower, and a port number is 16 bits -- the width is the question",
                    );
                    return;
                }
            }
        }
        for r in &d.register {
            // **32 bits is where `in`/`out` stop.** `inb`/`inw`/`inl` is the whole list, and
            // there is no `inq`: the port space was never widened past a doubleword. `at
            // mmio` lowers a `u64` register to one `volatile` access; here the instruction
            // does not exist, and two halves at two ports would be a device this declaration
            // did not describe.
            let breite = breite_oder_absage(&r.typ, absagen) * 8;
            if breite > 32 {
                weigere(
                    absagen,
                    r.name.span,
                    &format!(
                        "a {breite}-bit register at a `device … at port` -- `in`/`out` come \
                         in `b`, `w` and `l` and stop at 32 bits; there is no 64-bit port \
                         access on x86. Splitting it over two ports would be a device this \
                         declaration does not describe"
                    ),
                );
                return;
            }
            // The port number is `basis + offset` and the whole space is 16 bits, so an
            // offset past `0xffff` cannot name a port on its own account.
            //
            // *Read from the collected map and not from the tree*, because the map is what
            // `portzugriff` writes into the instruction -- checking one number and emitting
            // another is the shape this whole refusal was written against.
            if let Some((v, _)) = u.geraete.get(&d.name.text).and_then(|g| g.reg.get(&r.name.text)) {
                if !(0..=0xffff).contains(v) {
                    weigere(
                        absagen,
                        r.name.span,
                        &format!(
                            "port number {v} at a `device … at port` -- the port space runs \
                             from 0 to 0xffff, and a number outside it names no port"
                        ),
                    );
                    return;
                }
            }
        }
    }
    if matches!(d.raum, Raum::Dma) && !u.annahmen.contains(ANNAHME_DMA) {
        weigere(
            absagen,
            d.span,
            &format!(
                "`device … at dma` without `assume {ANNAHME_DMA}` -- which barrier a DMA \
                 access needs is a statement about the MEMORY MODEL, and this generator \
                 does not build it. It carries it by name instead: declare the assumption \
                 with a falsifier, and the access lowers like an `mmio` one"
            ),
        );
        return;
    }
    // **«B24» an seiner eigenen Stelle:** eine Bitlage muss INNERHALB der erklaerten
    // Registerbreite liegen. Der Befund des Ordners redet ueber Lagen jenseits von 64 in
    // einem `format`; hier ist die Breite erklaert, also ist die Frage entscheidbar -- und
    // eine Lage, die herausragt, ist ein Fehler, kein offener Punkt.
    // **`D16`/`D17`: a register offset the emitter cannot WRITE, and a register offset it
    // cannot READ, and until today neither said a word** (2026-09-03).
    //
    // The offset becomes C text in `geraetelesung`: `(*(volatile uint64_t *)(d->basis +
    // <offset>))`. Two things could go wrong there and both did.
    //
    // **`D16` -- it could not be written.** The number went in through `{versatz}` with no
    // spelling rule at all, so `@0x8000000000000000` emitted `d->basis + 9223372036854775808`
    // and `cc` answered *integer constant is so large that it is unsigned*. **This is the
    // NINTH sink of `D3`** -- the eight others are named in
    // `messung/proben/probe-literal-past-the-signed-end.gab`, and this one is not among them
    // because nothing had ever emitted it: the shared sweep template declares a register that
    // nothing reads, and a register nobody reads gets no accessor.
    //
    // **`D17` -- it could not be read, and the register VANISHED.** `Namen`'s builder records
    // a register only `if let Some(v) = umg.konst_wert(...)`. An offset that is not a
    // constant this unit can fold drops the whole entry, `ort` then finds no register of that
    // name, and the access falls through to the generic suffix walk:
    //
    //     device D(basis : Pa) at mmio {{ reg X : u64 @_1 class rw }}   ->   return d->X;
    //     gabbro pruefe   4 items, 0 errors, 0 hints
    //     cc              error: `D` has no member named `X`
    //
    // *A filter that turns a KNOWN fact into a MISSING one* -- word for word the class
    // `messung/ERZEUGERSWEEP.md` §9 named for `table count 0`, one construct over. **A rule
    // with no value does not refuse; it says nothing**, and what it says nothing about here
    // is a struct member that was never declared.
    //
    // > **Both are refused HERE and not at the four reading sites.** `geraetelesung` has no
    // > span to hang a refusal on and is called from four places; the declaration has one
    // > span, one refusal per register, and it points at the line the author wrote. *The
    // > comment beside the width filter in `Namen` already promised this shape of answer --
    // > "`geraet` refuses it by name a few hundred lines further down" -- and the offset was
    // > the half of that sentence nobody had written.*
    //
    // **ONE lookup for both questions in this function**, hoisted rather than repeated --
    // the same sentence `ort` carries over its own three: *asking it three times in one
    // block is three chances to ask it differently.* The parameter list a hundred lines down
    // reads the same entry.
    let hier = u
        .geraete
        .get(&d.name.text);
    for r in &d.register {
        if intty(&r.typ).is_some() && breite_von(&r.typ).is_some() {
            match hier.and_then(|g| g.reg.get(&r.name.text)) {
                None => {
                    weigere(
                        absagen,
                        r.name.span,
                        "a `reg` whose `@` offset is not a constant this unit can fold -- \
                         the offset is the whole of the access (`basis + offset`), and \
                         without it there is no accessor to write. The access would fall \
                         through to a plain struct member that no declaration ever made",
                    );
                    return;
                }
                Some((v, _)) => {
                    if u128::try_from(*v).ok().and_then(czahl).is_none() {
                        weigere(
                            absagen,
                            r.name.span,
                            &format!(
                                "a `reg` at offset {v} -- the offset goes into the C as a \
                                 literal (`basis + {v}`), and no C integer type holds it. A \
                                 negative offset has no reading here at all: the base is the \
                                 device, and there is nothing below it"
                            ),
                        );
                        return;
                    }
                }
            }
        }
        let breite = breite_oder_absage(&r.typ, absagen) * 8;
        for (name, lage, _) in &r.felder {
            let hi = match lage {
                BitPos::Bit(b) => *b as u32,
                BitPos::Bereich(h, _) => *h as u32,
            };
            if hi >= breite {
                weigere(
                    absagen,
                    name.span,
                    &format!("bit {hi} lies outside the declared register width of {breite}"),
                );
                return;
            }
        }
    }

    // **The declared parameters travel IN the handle** (2026-08-25). `device Virtq(base :
    // Iova, n : u16 in 1 .. QMAX)` says the ring carries its length; without it `q.n` had no
    // lowering and no type. *The declaration named it, the emitter dropped it.*
    let felder: String = hier
        .map(|g| {
            g.parameter
                .iter()
                .map(|(n, c)| format!(" {c} {n};"))
                .collect::<String>()
        })
        .unwrap_or_default();
    // **A port handle carries a NUMBER, and a memory handle carries a pointer.** That is the
    // first of the five demands over this function: `in`/`out` take a 16-bit port number, and
    // `basis + offset` on a `volatile uint8_t *` is arithmetic on an address. *The handle is
    // where the difference has to start, because everything below reads it.*
    let basisfeld = if matches!(d.raum, Raum::Port) {
        "uint16_t basis;"
    } else {
        "volatile uint8_t *basis;"
    };
    aus.push_str(&format!(
        "\ntypedef struct {{ {basisfeld}{felder} }} {};\n",
        d.name.text
    ));
    if matches!(d.raum, Raum::Port) {
        for r in &d.register {
            portzugriff(d, r, aus, u);
        }
    }
    for b in &d.baenke {
        bank(d, b, aus, u, absagen);
    }
    for u2 in &d.uebergaenge {
        uebergang(d, u2, aus, u, absagen);
    }
}

/// **The instruction letter and the operand letter for a port access of `bits` width.**
///
/// `inb`/`inw`/`inl` is the whole list, and the operand modifier that names the matching
/// half of the accumulator is `b`/`w`/`k`. **Both come from the same width and they are not
/// the same letter** -- 32 bits is `l` in the mnemonic and `k` in the operand -- so they are
/// returned together and never spelled apart.
///
/// *There is no fourth row.* A wider register is refused in `geraet`, by name and with the
/// reason: the port space stops at a doubleword.
fn portbuchstaben(bits: u32) -> (&'static str, &'static str) {
    match bits {
        8 => ("b", "b"),
        16 => ("w", "w"),
        _ => ("l", "k"),
    }
}

/// **`reg LSR : u8 @0x3fd` at a port device -- one reader, one writer, and the INSTRUCTION
/// inside them** (2026-09-02).
///
/// ```c
/// static inline __attribute__((unused)) uint8_t Com1_LSR_in(const Com1 *d) {
///     uint8_t _w;
///     __asm__ __volatile__("inb %w[tor], %b[wert]\n"
///         : [wert] "=a" (_w)
///         : [tor] "Nd" ((uint16_t)(d->basis + 1021u))
///         : "memory");
///     return _w;
/// }
/// ```
///
/// **Why a function pair and not a place.** The paragraph over `geraet` states the mmio
/// decision and its reason: *the access lowers as a PLACE, so `+=` carries itself.* `in` and
/// `out` are two instructions with nothing between them that a C lvalue could be, so the
/// pair is the only shape -- and the forms that leaned on the place are refused by name at
/// the assignment branch.
///
/// **Why the operands are constrained the way they are, and not more loosely.**
///
/// | operand | constraint | what it says |
/// |---|---|---|
/// | the port | `"Nd"` | an 8-bit unsigned immediate **or** `dx` -- and that pair IS the addressing mode `in`/`out` have. `0x3f8` does not fit the immediate, so the compiler picks `dx`; `0x21` fits and becomes `in $0x21, %al` |
/// | the datum | `"a"` / `"=a"` | `in` and `out` read and write the accumulator and no other register. The constraint does not prefer it, it is the instruction |
///
/// **`memory` in the clobber list is the default and not the exception** (`N026`, and
/// `beispiele/36-asm.gab` says the sentence). A port write is how a driver orders a device
/// about; the compiler may not float a memory access across it, and `__volatile__` alone
/// only says the block may not be deleted.
///
/// > **Both are emitted for every register, whatever its `class`.** `R002`/`R003` refuse a
/// > write to a `class r` register and a read of a `class w` one, and *what the checker
/// > decided the machine does not decide again* (W6) -- the sentence stands over `geraet`
/// > for the mmio place and it holds here word for word. An accessor nobody calls costs an
/// > `__attribute__((unused))` and no line of object code.
fn portzugriff(d: &Device, r: &RegDecl, aus: &mut String, u: &Namen) {
    let Some(g) = u.geraete.get(&d.name.text) else {
        return;
    };
    let Some((versatz, breite)) = g.reg.get(&r.name.text) else {
        return;
    };
    // **The fourth row does not exist, and it is REFUSED and not defaulted.** `geraet` returns
    // before this function is reached for any register wider than 32 bits, by name and with
    // the reason -- so the arm below covers `uint32_t` and nothing else. *A catch-all that
    // quietly picks a width would be the shape this whole refusal was written against.*
    let bits: u32 = match breite.as_str() {
        "uint8_t" => 8,
        "uint16_t" => 16,
        "uint32_t" => 32,
        _ => return,
    };
    let (befehl, op) = portbuchstaben(bits);
    let (dev, reg) = (&d.name.text, &r.name.text);
    let tor = format!("(uint16_t)(d->basis + {versatz}u)");
    aus.push_str(&format!(
        "\nstatic inline __attribute__((unused)) {breite} {dev}_{reg}_in(const {dev} *d) {{\n\
         \x20   {breite} _w;\n\
         \x20   __asm__ __volatile__(\n\
         \x20       \"in{befehl} %w[tor], %{op}[wert]\\n\"\n\
         \x20       : [wert] \"=a\" (_w)\n\
         \x20       : [tor] \"Nd\" ({tor})\n\
         \x20       : \"memory\");\n\
         \x20   return _w;\n}}\n"
    ));
    aus.push_str(&format!(
        "\nstatic inline __attribute__((unused)) void {dev}_{reg}_out({dev} *d, {breite} _w) {{\n\
         \x20   __asm__ __volatile__(\n\
         \x20       \"out{befehl} %{op}[wert], %w[tor]\\n\"\n\
         \x20       :\n\
         \x20       : [wert] \"a\" (_w), [tor] \"Nd\" ({tor})\n\
         \x20       : \"memory\");\n}}\n"
    ));
}

/// **The reading half of a device register access -- a place for `mmio`, a CALL for `port`.**
///
/// One function, because the two sites that need it (`ort` for an access in an expression,
/// `uebergang` for the mirror read) would otherwise each decide the space for themselves,
/// and a `transition` that reads through a load while `ort` reads through `in` is exactly the
/// mixture `C001` exists to prevent.
///
/// `name` is the handle's C name and `pfeil` is `->` for a pointer or `.` for a value -- the
/// same pair `ort` already carries, and the same one the bank accessor turns into an address.
fn geraetelesung(
    g: &Geraet,
    name: &str,
    pfeil: &str,
    versatz: i128,
    breite: &str,
    dev: &str,
    reg: &str,
) -> String {
    if matches!(g.raum, Raum::Port) {
        format!("{dev}_{reg}_in({})", handgriff(name, pfeil))
    } else {
        // **`D16`: the offset is a LITERAL in the emitted C, so it obeys `czahl`** -- the
        // same boundary every other literal sink took on 2026-09-03, and the ninth of the
        // nine `D3` named. Below `2^63` the text is unchanged, byte for byte.
        //
        // *The refusal lives at the declaration and not here*, because this function has no
        // span and four callers; `geraet` refuses a `reg` whose offset has no C spelling
        // before any of them runs. The fallback below is therefore unreachable, and it is
        // spelt out rather than unwrapped: a back end that panics on its own invariant has
        // replaced a wrong number with a worse answer.
        let stelle = u128::try_from(versatz)
            .ok()
            .and_then(czahl)
            .unwrap_or_else(|| versatz.to_string());
        format!("(*(volatile {breite} *)({name}{pfeil}basis + {stelle}))")
    }
}

/// **Does this pointer target name a `device … at port` of this unit?**
///
/// The one question the narrowed `ptr<port, …>` refusal asks. A path is taken by its LAST
/// segment, the way every other lookup in this emitter takes one.
fn ist_portgeraet(ziel: &TypExpr, u: &Namen) -> bool {
    let TypExpr::Pfad(p) = ziel else { return false };
    p.teile
        .last()
        .and_then(|i| u.geraete.get(&i.text))
        .is_some_and(|g| matches!(g.raum, Raum::Port))
}

/// The handle as a POINTER, whichever way the name holds it. `q` stays `q`, `v` becomes `&v`.
fn handgriff(name: &str, pfeil: &str) -> String {
    if pfeil == "->" {
        name.to_string()
    } else {
        format!("&{name}")
    }
}

/// **`bank FRR at CAP.FRO * 16 stride 16 count 256` -- ein Registersatz an BERECHNETER Lage.**
///
/// Die Lage kommt aus einem GELESENEN Feld: `CAP.FRO` sagt, wo die Fehlerregister liegen, und
/// der Bestand rechnet dieselbe Adresse von Hand aus (`vtd.rs:442`, `frr_off`). **Der Index
/// ist ueber `count` M1-beschraenkt** -- die Schranke steht in der Deklaration, nicht in einer
/// Pruefung im Rumpf.
///
/// Abgesenkt als Zugriffsfunktion mit Index, weil die Lage erst zur Laufzeit feststeht:
///
/// ```c
/// static inline __attribute__((unused)) uint64_t Vtd_FRR_FR_LO(const Vtd *d, uint32_t i) {
///     return *(volatile uint64_t *)(d->basis + <lage> + i * 16 + 0);
/// }
/// ```
fn bank(d: &Device, b: &Bank, aus: &mut String, u: &Namen, absagen: &mut Absagen) {
    let (Some(schritt), Some(anzahl)) = (konst_zahl(&b.schritt), konst_zahl(&b.anzahl)) else {
        weigere(absagen, b.span, "`bank` with a non-constant `stride` or `count`");
        return;
    };
    // Die BASIS darf berechnet sein -- das ist der Sinn der Form. Sie muss aber aus Feldern
    // dieses Geraets kommen, sonst kennt der Erzeuger ihren Wert nicht.
    let Some(lage) = ausdruck_geraet(&b.basis, d, u, absagen) else {
        // Der GRUND steht schon in `ausdruck_geraet`, an der Stelle, die ihn kennt. Hier
        // bleibt nur der Abbruch -- **eine zweite Absage waere ein zweites Register ueber
        // derselben Sache** (W7), und der Leser bekaeme zwei Zeilen fuer einen Befund.
        return;
    };
    for r in &b.register {
        let Some(off) = konst_zahl(&r.versatz) else {
            weigere(absagen, r.name.span, "`bank` register at a non-constant offset");
            return;
        };
        let Some(breite) = intty(&r.typ) else {
            weigere(absagen, r.name.span, "`bank` register word -- no such integer word");
            return;
        };
        aus.push_str(&format!(
            "\nstatic inline __attribute__((unused)) {breite} {}_{}_{}(const {} *d, uint32_t i) {{\n\
             \x20   /* count {anzahl}: the index bound falls out of the declaration */\n\
             \x20   return *(volatile {breite} *)(d->basis + ({lage}) + i * {schritt}u + {off}u);\n}}\n",
            d.name.text, b.name.text, r.name.text, d.name.text
        ));
        // **The SETTER, and until 2026-08-26 there was none** -- so a bank could be read
        // from C and written from nowhere. *Half a lowering looks like a whole one until
        // somebody writes.*
        //
        // The class rule stays with the checker (`R002`/`R003`, issued in `m3.rs`), as
        // everywhere: what the pass decided, the machine does not check a second time (W6).
        aus.push_str(&format!(
            "\nstatic inline __attribute__((unused)) void {}_{}_setz_{}({} *d, uint32_t i, {breite} x) {{\n\
             \x20   *(volatile {breite} *)(d->basis + ({lage}) + i * {schritt}u + {off}u) = x;\n}}\n",
            d.name.text, b.name.text, r.name.text, d.name.text
        ));
    }
}

/// Ein Ausdruck ueber Feldern DIESES Geraets -- fuer die berechnete Banklage.
///
/// **Die leere Zeichenkette war das Fehlerzeichen, und sie ueberlebte die Zusammensetzung
/// nicht** (aufgeraeumt 2026-08-21). `bank` prueft `lage.is_empty()`, und in einem BLATT
/// stimmte das auch. Sobald das unbekannte Blatt aber in einem `Binaer` oder einer `Klammer`
/// steckte, kam `" * 16"` oder `"()"` heraus -- **nicht leer**, also durch die Wache. Was
/// dann in `bank` geschrieben wurde, war `(d->basis + ( * 16) + …)`.
///
/// > *Der Fehler faellt bei `cc` und nicht still* -- aber genau darum geht es in diesem
/// > Modul nicht: **eine Weigerung, auf die man baut, ist eine Zusage.** Der Erzeuger
/// > entscheidet hier und delegiert nicht an den C-Uebersetzer, dessen Meldung ueber eine
/// > Zeile spricht, die der Anwender nie geschrieben hat.
///
/// `Option` traegt das Scheitern jetzt durch `?` -- und der Sammelzweig ist ausgeschrieben,
/// damit eine neue Ausdrucksform nicht dieselbe Reise noch einmal macht.
fn ausdruck_geraet(e: &Expr, d: &Device, u: &Namen, absagen: &mut Absagen) -> Option<String> {
    Some(match &e.art {
        ExprArt::Zahl(n) => czahl(*n)?,
        ExprArt::Klammer(x) => format!("({})", ausdruck_geraet(x, d, u, absagen)?),
        ExprArt::Binaer(op, a, b) => format!(
            "{} {} {}",
            geklammert(op, a, ausdruck_geraet(a, d, u, absagen)?),
            op_text(op),
            geklammert(op, b, ausdruck_geraet(b, d, u, absagen)?)
        ),
        // `CAP.FRO` -- ein Feld dieses Geraets, gelesen ueber `d`.
        ExprArt::Ort(o) if o.suffixe.len() == 1 => {
            let (Some(g), OrtSuffix::Feld(f)) = (u.geraete.get(&d.name.text), &o.suffixe[0])
            else {
                weigere(
                    absagen,
                    o.span,
                    "`bank` base over a place that is not `REGISTER.field` of this device",
                );
                return None;
            };
            let Some((versatz, breite)) = g.reg.get(&o.basis.text) else {
                weigere(absagen, o.basis.span, "`bank` base over a register this device does not declare");
                return None;
            };
            let Some((hi, lo, _)) = g.felder.get(&o.basis.text).and_then(|m| m.get(&f.text))
            else {
                weigere(absagen, f.span, "`bank` base over a field this register does not declare");
                return None;
            };
            let maske: u128 = (1u128 << (hi - lo + 1)) - 1;
            format!("(((*(volatile {breite} *)(d->basis + {versatz})) >> {lo}) & {maske}u)")
        }
        // A bare name, a `->`, an index, a chain of more than one suffix: none of them names
        // a field of THIS device, and the emitter knows no other source for the address.
        ExprArt::Ort(o) => {
            weigere(
                absagen,
                o.span,
                "`bank` base over a place that is not `REGISTER.field` of this device -- the \
                 address has to be computable from this device's own register block",
            );
            return None;
        }
        // Everything else: a bank address is an ADDRESS. A boolean, a float, a call, a
        // `sizeof`, an `old(…)`, a `result` -- none of them is one, and none of them is
        // readable from the register block at the moment the accessor is generated.
        ExprArt::Wahr
        | ExprArt::Falsch
        | ExprArt::Gleitkomma { .. }
        | ExprArt::Ruf(_)
        | ExprArt::Eingebaut(_)
        | ExprArt::Alt(_)
        | ExprArt::Ergebnis
        // **`FnWert` and `Grund` arrived on 2026-08-21, and the compiler asked HERE.**
        // Before this catch-all was written out, both would have been swallowed in silence:
        // a function pointer or a reason value inside a `device` expression would have
        // lowered to whatever the fallthrough produced. *That is the point of resolving the
        // branch -- a new variant asks instead of passing.*
        | ExprArt::FnWert(_)
        | ExprArt::Grund { .. }
        // **«SG-24»** -- a count is a run-time number, not an address: a bank base
        // over one names no register field of this device.
        // **Lane E1** -- a library call is no address either.
        // **Lane 111** -- a table literal is no address either: it stands only
        // as a `const` initializer and never reaches a bank base.
        | ExprArt::Zaehle { .. }
        | ExprArt::LibraryCall(_)
        | ExprArt::ArrayLit(_)
        | ExprArt::Unaer(_, _) => {
            weigere(
                absagen,
                e.span,
                "`bank` base expression form -- only a number, a parenthesis, a binary \
                 operation and `REGISTER.field` of this device lower to an address",
            );
            return None;
        }
    })
}

/// **`check` -- die Probe wird eine Funktion, ihre Behauptung ein Kommentar.**
/// **Quelltext, der in einen C-Kommentar geht — an EINER Stelle entschärft.**
///
/// Gefunden am 2026-08-19 von aussen, nachgestellt bis ins Objekt: ein `claim` mit der Folge
/// `*/` schliesst den Kommentar und schreibt danach C. `nm` fand
/// `0000000000000000 D EINGESCHLEUST` — **eine Zeichenkette aus der Quelle wurde ein
/// Datensymbol im Objekt.**
///
/// *Der Grund, warum ausgerechnet diese Folge trägt:* der Lexer kennt **keine Escapes**
/// (`L006`), eine Zeichenkette kann also kein `"` enthalten — damit war der `section`-Kanal
/// nie offen. `*/` braucht keins.
///
/// **Warum entschärfen und nicht weigern:** der Kommentar ist Prosa für einen Leser, und
/// eine Prosa mit `*/` darin ist keine Zusage, die falsch würde. Die Folge wird sichtbar
/// getrennt (`* /`), nicht entfernt — *wer sie geschrieben hat, findet sie wieder.*
fn kommentartext(t: &str) -> String {
    t.replace("*/", "* /").replace("/*", "/ *")
}

fn pruefkoerper(
    c: &Check,
    aus: &mut String,
    rumpf_aus: &mut String,
    u: &Namen,
    absagen: &mut Absagen,
) {
    aus.push_str(&format!("\nbool pruefe_{}(void);\n", c.name.text));
    rumpf_aus.push_str(&format!(
        "\n/* check {}\n * claim: {}\n",
        kommentartext(&c.name.text),
        kommentartext(&c.claim.text)
    ));
    for g in &c.gates {
        rumpf_aus.push_str(&format!(" * gates: {}\n", kommentartext(&g.text)));
    }
    if let Some((was, erwartet)) = &c.counterprobe {
        // **Die Gegenprobe ist die Zeile, die die Probe erst zu einer macht** -- sie sagt,
        // wie die Probe ROT werden koennte. Eine Probe ohne sie ist eine Zusage.
        rumpf_aus.push_str(&format!(
            " * counterprobe: \"{}\" expects {}\n",
            kommentartext(&was.text),
            kommentartext(&erwartet.text)
        ));
    }
    rumpf_aus.push_str(" */\n");
    rumpf_aus.push_str(&format!("bool pruefe_{}(void) {{\n", c.name.text));
    // **A probe body gets its own view, exactly as a function body does** (2026-08-26).
    //
    // Until today `pruefkoerper` handed the GLOBAL `u` straight to `anweisung`, so every
    // name a probe bound with `let` had no type at all. Measured at
    // `messung/fragmente/F06.gab`: `let f = eichfeld(); … lenof(f.worte)` refused, while the
    // byte-identical code in a function body lowers to `8u`.
    //
    // > *A rule that works in one body and not in another is not a rule about the language,
    // > it is a gap in one caller* -- and this one had no name, because the refusal it
    // > produced spoke about `lenof` instead of about the missing view.
    let mut sicht = u.clone();
    lokale_lets(&c.can_fail, &mut sicht);
    for s in &c.can_fail.anweisungen {
        anweisung(s, rumpf_aus, &sicht, absagen, 1, &Austritt::default());
    }
    rumpf_aus.push_str("}\n");
}

/// **`transition` -- und `mirrors` ist die Antwort auf Falle 4.**
///
/// Ein Uebergang schreibt das GANZE Wort. Das ist keine Bequemlichkeit, sondern die Sache
/// selbst: `GCMD` ist **kein** Lese-Aendere-Schreib-Register, und ein nicht mitgeschriebenes
/// Zustandsbit wird geloescht. Woher die mitzuschreibenden Bits kommen, sagt `mirrors`:
///
/// ```text
///     mirrors GCMD from GSTS;      ->   write(GCMD, (read(GSTS) & ~geaendert) | neu)
/// ```
///
/// **Eine Zeile je Geraet, und sie ersetzt `GCMD_STATE_MASK` samt der Kommentarwand**
/// (`FRAGMENTE.md` F2, `vtd.rs:42-52`). *Das Konstrukt war die Falle, gegen die es gebaut
/// wurde -- jetzt steht sie im erzeugten C statt in einem Kommentar.*
///
/// ## Das `requires` wird KEINE Laufzeitpruefung, und das ist die Entscheidung
///
/// `requires GSTS.RTPS == 1` ist dieselbe Art Klausel wie `requires Held(CAPS)` an einer
/// Funktion: eine **Pflicht des Rufers**, kein erzeugter Zusicherungsaufruf. Der Erzeuger
/// gibt fuer ein Funktions-`requires` auch keine Pruefung aus.
///
/// > **Die Alternative waere die stille Ausnahme:** hier pruefen und dort nicht. *Genau das
/// > ist die Bewegung, gegen die dieser Ordner an jeder anderen Stelle steht.* Die Klausel
/// > steht darum als Kommentar im C -- sichtbar, aber nicht ausgefuehrt.
fn uebergang(d: &Device, x: &Uebergang, aus: &mut String, u: &Namen, absagen: &mut Absagen) {
    // **`transset` -- mehrere Orte in EINEM Zug.** Am Register ist das entscheidbar: die Bits
    // werden veroderrt und in einem Schreibzug gesetzt. *Genau die Form, an der F3 zerbricht
    // («B17») -- dort geht es um zwei SLOTFELDER, und dafuer gibt es keinen Schreibzug, der
    // beide zugleich trifft.* Am Wort eines Registers gibt es ihn.
    if x.schritte.is_empty() {
        weigere(absagen, x.span, "`transition` without a step");
        return;
    }
    let reg = x.schritte[0].ort.basis.text.clone();
    if x.schritte.iter().any(|s| s.ort.basis.text != reg) {
        weigere(
            absagen,
            x.span,
            "`transset` across two different registers -- there is no single write that hits \
             both, and that is «B17» one level up",
        );
        return;
    }
    let s = &x.schritte[0];
    let Some(g) = u.geraete.get(&d.name.text) else { return };
    let Some((versatz, breite)) = g.reg.get(&reg) else {
        weigere(absagen, x.span, "`transition` on something that is not a register");
        return;
    };
    let leer = HashMap::new();
    let felder = g.felder.get(&reg).unwrap_or(&leer);
    // **The word width in BITS** -- it decides what a whole-word step SAYS. See
    // `schrittbits`: until 2026-08-25 it said "these bits" instead of "the whole word", and
    // at `-> 0` those were none.
    //
    // **All eight lowered words stand one by one, and none falls into a ninth.** The
    // strings come from the same `ganzzahlwort` table as every other width in this
    // emitter, signed ones included -- a `reg R : i16` checks clean and lowers through
    // this very match. A ninth string is `C001`, not 64: *a default width here would be
    // `breite_von`'s `_ => 8`, one level down.*
    let wortbits: u32 = match breite.as_str() {
        "uint8_t" | "int8_t" => 8,
        "uint16_t" | "int16_t" => 16,
        "uint32_t" | "int32_t" => 32,
        "uint64_t" | "int64_t" => 64,
        _ => {
            weigere(
                absagen,
                x.span,
                "a `transition` on a register word outside the eight lowered words -- \
                 the whole-word mask has no width to stand on",
            );
            return;
        }
    };

    // Welche Bits aendert dieser Zug, und auf welchen Wert? Ueber ALLE Schritte veroderrt.
    let mut geaendert: u128 = 0;
    let mut neu: u128 = 0;
    for s in &x.schritte {
        let (g2, n2) = match schrittbits(s, felder, wortbits, absagen) {
            Some(v) => v,
            None => return,
        };
        geaendert |= g2;
        neu |= n2;
    }
    let _ = s;

    // **A `transition` in the port space writes through `out`, and reads its mirror through
    // `in`.** The transition itself is unchanged -- it is still "these bits to these values,
    // in ONE move" -- and only its two ends move. *`geraetelesung` is the one line that
    // decides the read end, here and in `ort`, because a `transition` that read through a
    // load while `ort` read through `in` would be exactly the mixture `C001` exists against.*
    let ist_port = matches!(g.raum, Raum::Port);
    let wort = geraetelesung(g, "d", "->", *versatz, breite, &d.name.text, &reg);
    let schreib = |w: String| {
        if ist_port {
            format!("    {}_{reg}_out(d, {w});\n", d.name.text)
        } else {
            format!("    {wort} = {w};\n")
        }
    };
    aus.push_str(&format!("\n/* transition {} */\n", x.name.text));
    if let Some(p) = &x.requires {
        // **The clause is READ here and its content thrown away**, and that is measured, not
        // suspected (2026-09-02): `requires GSTS.RTPS == 1` and `requires 1 == 2` produce
        // BYTE-IDENTICAL C. *A comment that does not say WHAT is owed tells its reader
        // nothing he can act on* -- and the `reg` half of the same construct has carried its
        // predicate into the artefact since «B26» (`fehlbare_lesung` writes `if (!(t <= 8))`).
        //
        // **It stays a comment and not an assertion, and that half is right**: the register
        // is volatile and a hostile device may report what it likes («B33»), so a generated
        // check would be a fact where an assumption belongs.
        //
        // > **Saying the clause was TRIED here and taken out again.** `pred_c` renders
        // > `GSTS.RTPS == 1` as `GSTS->RTPS == 1` -- and `GSTS` is no name this artefact
        // > has; the register is `(*(volatile uint32_t *)(d->basis + 28))`. *A comment that
        // > points at a name the file does not carry is worse than one that points at
        // > nothing.* Saying it in GABBRO notation needs a `Pred` -> source-text renderer
        // > that does not exist -- every other caller slices the SOURCE, and the emitter is
        // > handed a tree and nothing else. Booked in `TODO.md`, not bodged here.
        let _ = p;
        aus.push_str("/* requires: a caller obligation, not a generated assertion */\n");
    }
    aus.push_str(&format!(
        "static inline __attribute__((unused)) void {}_{}({} *d) {{\n",
        d.name.text, x.name.text, d.name.text
    ));
    match &d.mirrors {
        Some(m) if m.ziel.basis.text == reg => {
            let quelle = m.quelle.basis.text.clone();
            let Some((qv, qb)) = g.reg.get(&quelle) else {
                weigere(absagen, m.span, "`mirrors` from a register this device does not declare");
                return;
            };
            let spiegel = geraetelesung(g, "d", "->", *qv, qb, &d.name.text, &quelle);
            aus.push_str(&format!("    {breite} _s = {spiegel};\n"));
            aus.push_str(&schreib(format!(
                "({breite})((_s & ({breite})~({breite}){geaendert}u) | ({breite}){neu}u)"
            )));
        }
        _ => aus.push_str(&schreib(format!("({breite}){neu}u"))),
    }
    aus.push_str("}\n");
}

/// Die geaenderten und die neuen Bits EINES Schritts.
fn schrittbits(
    s: &OrtSchritt,
    felder: &HashMap<String, (u32, u32, u32)>,
    wortbits: u32,
    absagen: &mut Absagen,
) -> Option<(u128, u128)> {
    match s.ort.suffixe.first() {
        // `GCMD.SRTP: 0 -> 1` -- genau ein Bit.
        Some(OrtSuffix::Feld(f)) => {
            let Some((hi, lo, _)) = felder.get(&f.text) else {
                weigere(absagen, f.span, "`transition` on an unknown register field");
                return None;
            };
            if hi != lo {
                weigere(absagen, f.span, "`transition` on a multi-bit field");
                return None;
            }
            let maske = 1u128 << lo;
            // **A field step says one bit, and only a digit says which value (lane-140).**
            //
            // Until today this read `matches!(&s.nach.art, ExprArt::Zahl(n) if *n != 0)`:
            // every other form counted as "clear". `GCMD.TE: 0 -> (1)` checked clean and
            // lowered to a bit-CLEAR with exit 0, though the value is 1 -- and `-> true`
            // cleared too, for the same silent reason. The corpus writes digits at this
            // spot, so there is nothing to fold here, only something to name: a step
            // target that is not a number refuses, by name.
            let ExprArt::Zahl(n) = &s.nach.art else {
                weigere(
                    absagen,
                    s.nach.span,
                    "`transition` field step whose target is not a number -- the step sets \
                     or clears ONE bit, and anything but a digit (`(1)`, `true`, a call) \
                     has no bit value this lowering may read",
                );
                return None;
            };
            let an = *n != 0;
            Some((maske, if an { maske } else { 0 }))
        }
        // `DEVICE_STATUS: ACK -> ACK | DRIVER` -- eine Veroderung von Feldnamen.
        //
        // **A whole-word step says the WHOLE WORD, not the bits it sets** (2026-08-25).
        // Until today this read `Some((n, n))`: "changed" was the new value itself -- and so
        // at `-> 0` it was **empty**. On a `mirrors` device that produced
        //
        //     (_s & ~0) | 0     ==     _s
        //
        // *a "reset" that writes the mirror back and resets nothing* -- 0 errors, 0
        // refusals, a certificate that says nothing. **A silent wrong lowering is worse than
        // a refusal**, because it looks like a result.
        //
        // The defect does NOT hang on a placeholder for the pre-state: `{ GCMD: 0 -> 0 }`
        // produced byte-identically the same. It is unreachable today because no corpus
        // program writes a whole-word step on a `mirrors` device -- *and that is exactly why
        // it belongs corrected BEFORE a notation makes it reachable.*
        //
        // With the full mask `mirrors` is consistently without effect for a whole-word
        // step: whoever names the whole word carries nothing over from the mirror.
        None => match bitwort(&s.nach, felder) {
            Some(n) => {
                let vollmaske: u128 = if wortbits >= 128 {
                    u128::MAX
                } else {
                    (1u128 << wortbits) - 1
                };
                Some((vollmaske, n))
            }
            None => {
                weigere(absagen, s.span, "`transition` target that is not a set of field names");
                None
            }
        },
        // **Der Sammelzweig sagte etwas Falsches, und das war sein eigentlicher Schaden.**
        // Er stand fuer ZWEI Suffixformen und nannte nur eine: ein `GCMD->SRTP: 0 -> 1`
        // bekam *"`transition` on an indexed place"* zu lesen -- eine Absage, deren Grund
        // nicht stimmt. *Eine Weigerung, auf die man baut, ist eine Zusage* (siehe oben);
        // eine Weigerung mit dem falschen Grund ist eine falsche Zusage.
        Some(OrtSuffix::Index(_)) => {
            weigere(
                absagen,
                s.span,
                "`transition` on an indexed place -- a step names ONE bit of ONE register, \
                 and which register an index picks is a run time question",
            );
            None
        }
        // **Und dieser Arm ist der Gegenfall: er ist ausgeschrieben und trotzdem
        // UNERREICHBAR -- nicht aus Versehen, sondern durch die Grammatik.**
        //
        // `parse::transition` setzt `pfeil_ist_suffix = false`, solange es den Ort links vom
        // `:` liest (G3): in `ST: ACK -> ACK` waere `->` sonst zugleich Zeigerzugriff und
        // Uebergangspfeil. Ein `R->A:` faellt damit schon im Parser an `P001`, und diese
        // Zeile bekommt es nie zu sehen.
        //
        // *Sie steht hier, weil der `match` erschoepfend sein muss, und sie sagt, WORAUF sie
        // sich verlaesst.* Eine Zusicherung ueber die Kistengrenze ist keine, die der
        // Uebersetzer haelt -- **darum eine Absage und kein `unreachable!()`**: faellt die
        // Parserregel, faellt hier eine benannte Weigerung und kein Absturz.
        Some(OrtSuffix::Ueber(_)) => {
            weigere(
                absagen,
                s.span,
                "`transition` through a pointer (`->`) -- a step names a field of THIS \
                 device's register block, and the block is reached through `d->basis`, not \
                 through a place the author dereferences",
            );
            None
        }
    }
}

/// Eine Veroderung von Feldnamen als Bitwort -- `ACK | DRIVER` wird `0b11`.
fn bitwort(e: &Expr, felder: &HashMap<String, (u32, u32, u32)>) -> Option<u128> {
    match &e.art {
        ExprArt::Zahl(n) => Some(*n as u128),
        ExprArt::Ort(o) if o.suffixe.is_empty() => {
            let (hi, lo, _) = felder.get(&o.basis.text)?;
            if hi != lo {
                return None;
            }
            Some(1u128 << lo)
        }
        ExprArt::Klammer(x) => bitwort(x, felder),
        ExprArt::Binaer(BinOp::BitOder, a, b) => Some(bitwort(a, felder)? | bitwort(b, felder)?),
        _ => None,
    }
}

/// **Ein `format` wird KEIN C-Verbund, und das ist die Entscheidung.**
///
/// Fuellung, Bitreihenfolge und Wortbreite eines `struct` sind in C implementierungsoffen —
/// ein Format ist aber genau eine Zusage ueber BYTES. Ein Verbund waere also die eine
/// Absenkung, die genau das verliert, wofuer es das Konstrukt gibt.
///
/// **Die gewaehlte Form sind Zugriffsfunktionen ueber einem Bytezeiger** — und sie ist nicht
/// erfunden: der gemessene Bestand schreibt sie schon von Hand. *`be32(data, n)?` ist bereits
/// „pruefen, sonst absagen"* (`BEWEIS.md`, «B40»: 145 Zeilen ohne Fehler, ohne Sprache und
/// ohne Werkzeug).
///
/// ```c
/// typedef struct { const uint8_t *bytes; uint32_t len; } DtbKopf;
/// static uint32_t DtbKopf_magie(const DtbKopf *f) { … }
/// static bool     DtbKopf_gueltig(const DtbKopf *f) { … }   /* jede `where`-Klausel */
/// ```
///
/// **Heute abgesenkt wird der byteweise Fall**: ganzzahlige Felder in Deklarationsreihenfolge,
/// mit der erklaerten Bytereihenfolge. **Bitlagen (`@[63:12]`) werden beim Namen abgelehnt** —
/// dort steht mit «B24» ein offener Befund des Ordners selbst: `bitpos` sagt nicht, worauf
/// sich eine Lage jenseits von 64 bezieht und wie sie mit `endian` zusammenwirkt. *Eine
/// Absenkung zu bauen, waehrend die Bedeutung offen ist, hiesse die Frage still zu
/// beantworten.*
fn format_(f: &Format, aus: &mut String, u: &Namen, absagen: &mut Absagen) {
    let gross = matches!(f.endian, Some(Endian::Gross));
    if f.endian.is_none() {
        weigere(absagen, f.span, "`format` without `endian` -- the byte order is the point");
        return;
    }
    let n = &f.name.text;
    aus.push_str(&format!(
        // **`bytes` ist NICHT `const`, seit es Schreiber gibt** (2026-08-20). Ein Treiber,
        // der einen Rahmen stellt, schreibt durch dieselbe Sicht, durch die er liest.
        //
        // *Das C verliert damit eine Zusage, die es ohnehin nie gehalten hat:* `const` am
        // Zeiger im Verbund haette nur gesagt, dass `bytes` nicht umgehaengt wird, und ein
        // `const {n} *` propagiert in C nicht nach innen. **Wer hier schreiben darf,
        // entscheidet `ptr<…, r>` gegen `ptr<…, rw>`, und das haelt M3** -- W6: was der
        // Pruefer entschieden hat, prueft die Maschine nicht noch einmal.
        "\ntypedef struct {{ uint8_t *bytes; uint32_t len; }} {n};\n"
    ));
    let mut versatz: u32 = 0;
    let mut pruefungen: Vec<String> = Vec::new();
    // **«B24» entschieden 2026-08-18: die Bitlage liegt IM EIGENEN WORT des Feldes.**
    //
    // Der Befund fragte zweierlei, und beides wird hier beantwortet statt umgangen:
    //
    // 1. *„Worauf bezieht sich eine Position jenseits der Wortbreite?"* -- **auf nichts.**
    //    `hi >= breite(typ)` ist eine Absage, keine Bedeutung. Das ist die engere Antwort,
    //    und sie erfindet nichts.
    // 2. *„Wie wirkt sie mit `endian` zusammen?"* -- **das Wort wird zuerst in der erklaerten
    //    Bytereihenfolge gelesen, dann werden die Bits aus dem WERT gezogen.** Bitnummern
    //    zaehlen ueber den Wert, nicht ueber die Bytes. *Anders komponiert es nicht: ein
    //    16-Bit-Feld hat in beiden Reihenfolgen dasselbe Bit 15.*
    //
    // **Und die Belegung eines Wortes muss es GENAU KACHELN** -- keine Luecke, keine
    // Ueberlappung. Eine Luecke heisst `reserved`, und das Wort gibt es schon.
    //
    // > *Damit gibt es keine implizite Buchhaltung.* Ein Format sagt, welche Bits existieren;
    // > der Erzeuger zaehlt nicht mit, wann ein Wort „voll" ist.
    //
    // Das ist genau die Mechanik, die `device`-Register seit dem 2026-08-14 tragen -- eine
    // Vereinheitlichung zweier vorhandener Formen, kein neues Konstrukt.
    let mut i_feld = 0usize;
    while i_feld < f.felder.len() {
        let feld = &f.felder[i_feld];
        // **Ein Bitfeld ist eines mit LAGE -- und `embeds` ist eine Lage** (2026-08-20).
        //
        // Bis heute stand hier *„`embeds` in a `format` -- that is a pointer form"*, und das
        // war zweimal daneben: `embeds [51:12] scale 4096` nennt eine Bitlage und einen
        // Faktor, und **was der Rohwert bedeutet, ist keine Frage an den Erzeuger.** Er
        // liefert die Bits mal dem Faktor; ob daraus eine Adresse wird, entscheidet der
        // Leser. *Eine Weigerung, die den Gegenstand falsch benennt, hindert ein Programm,
        // fuer das der Grund nie galt.*
        if feld.bitpos.is_none() && feld.typ.embeds.is_none() {
            let TypExpr::Int(i) = &feld.typ.typ else {
                weigere(absagen, feld.span, "`format` field type");
                return;
            };
            let breite = breite_oder_absage(i, absagen);
            let c = intty_oder_absage(i, absagen);
            let (leser, sw) = wortpaar_oder_absage(breite, gross, feld.span, absagen);
            if !feld.reserviert {
                aus.push_str(&format!(
                    "static inline __attribute__((unused)) {c} {n}_{f2}(const {n} *v) {{ return ({c}){leser}(v->bytes + {versatz}); }}\n",
                    f2 = feld.name.text
                ));
                // **Der SCHREIBER, und er heisst `_setz_`** -- `SPRACHE.md`:355 sagt ihn
                // seit jeher zu. Ohne ihn ist ein `format` nur halb abgesenkt, und ein
                // Treiber, der einen Rahmen STELLT, faellt auf eine Zuweisung an einen
                // Funktionsaufruf.
                aus.push_str(&format!(
                    "static inline __attribute__((unused)) void {n}_setz_{f2}({n} *v, {c} x) {{ {sw}(v->bytes + {versatz}, x); }}\n",
                    f2 = feld.name.text
                ));
            }
            // **The pinning of a byte-wise field.** *A `reserved` one has no reader, so
            // there is nothing to hold the bound against* -- refusing beats emitting a check
            // over a function that does not exist.
            if i.bereich.is_some() {
                if feld.reserviert {
                    weigere(
                        absagen,
                        feld.span,
                        "`in a .. b` at a `reserved` field -- a reserved field has no reader, \
                         so there is no place at which the bound could be established",
                    );
                    return;
                }
                let vz = matches!(
                    i.wort,
                    gabbro_syntax::kw::Kw::U8
                        | gabbro_syntax::kw::Kw::U16
                        | gabbro_syntax::kw::Kw::U32
                        | gabbro_syntax::kw::Kw::U64
                );
                pruefungen.extend(bereichspruefung(
                    i,
                    n,
                    &feld.name.text,
                    breite * 8,
                    vz,
                    u,
                    absagen,
                ));
            }
            if let Some(b) = &feld.bedingung {
                match pred_c_format(b, n, u, absagen) {
                    Some(x) => pruefungen.push(x),
                    None => {
                        weigere(absagen, feld.span, "`where` clause form in a `format`");
                        return;
                    }
                }
            }
            versatz += breite;
            i_feld += 1;
            continue;
        }

        // **Die Wortbreite einer Bitgruppe kommt aus IHREN Ganzzahlfeldern, nicht aus dem
        // ersten Feld** (2026-08-20).
        //
        // `format Pte` faengt mit vier `bool @N` an. Ein `bool` sagt ueber die Wortbreite
        // nichts -- und die alte Fassung las die Breite aus dem ERSTEN Feld der Gruppe und
        // waere hier auf ein Byte gekommen, wo ein Achtbytewort steht. **Also sagt es das
        // Feld, das es sagen kann:** `rahmen : u64 embeds [51:12]`.
        //
        // > *Und wo keines es sagt, wird geweigert statt geraten.* Acht `bool` in Folge
        // > koennten ein Byte sein oder die untersten acht Bits von vier -- der Erzeuger hat
        // > keinen Grund, das eine zu waehlen.
        let mut breite: Option<u32> = None;
        let mut ctyp_wort: Option<String> = None;
        {
            let mut j = i_feld;
            while j < f.felder.len() {
                let g = &f.felder[j];
                if g.bitpos.is_none() && g.typ.embeds.is_none() {
                    break;
                }
                if let TypExpr::Int(gi) = &g.typ.typ {
                    match &ctyp_wort {
                        // Ein anderes Ganzzahlwort faengt ein neues Wort an -- dieselbe
                        // Regel wie bisher, nur ohne die `bool` mitzuzaehlen.
                        Some(vorher) if Some(vorher.as_str()) != intty(gi).as_deref() => break,
                        Some(_) => {}
                        None => {
                            // **A word without a width opens no group, it refuses.**
                            // Until 2026-08-31 a `breite_von` stood here that made every
                            // unknown word eight bytes wide -- and a bit group over the
                            // wrong word width is exactly the error «B24» prevents from
                            // the other side.
                            let (Some(b), Some(c)) = (breite_von(gi), intty(gi)) else {
                                weigere(
                                    absagen,
                                    g.span,
                                    "integer width -- no such word in the width table",
                                );
                                return;
                            };
                            breite = Some(b);
                            ctyp_wort = Some(c);
                        }
                    }
                }
                j += 1;
            }
        }
        let (Some(breite), Some(c)) = (breite, ctyp_wort) else {
            weigere(
                absagen,
                feld.span,
                "a bit word of a `format` takes its width from an integer field, and this \
                 group names none -- a `bool @N` says which BIT, never which WORD",
            );
            return;
        };
        let (leser, sw) = wortpaar_oder_absage(breite, gross, feld.span, absagen);
        let bits = breite * 8;
        let mut belegt: u64 = 0;
        let mut gruppe = Vec::new();
        while i_feld < f.felder.len() {
            let g = &f.felder[i_feld];
            // `@N`, `@[hi:lo]` -- oder `embeds [hi:lo]`, was dieselbe Lage ist.
            let (hi, lo) = match (&g.bitpos, &g.typ.embeds) {
                (Some(BitPos::Bit(b)), _) => (*b, *b),
                (Some(BitPos::Bereich(h, l)), _) => (*h, *l),
                (None, Some((h, l))) => (*h, *l),
                (None, None) => break,
            };
            match &g.typ.typ {
                TypExpr::Bool(_) => {
                    if hi != lo {
                        weigere(
                            absagen,
                            g.span,
                            "a `bool` over more than one bit -- a truth value has one bit, and \
                             which of several it would be is not a question with an answer",
                        );
                        return;
                    }
                }
                TypExpr::Int(gi) if intty(gi).as_deref() == Some(c.as_str()) => {}
                TypExpr::Int(_) => break,
                _ => {
                    weigere(absagen, g.span, "`format` bit field type");
                    return;
                }
            }
            if hi < lo || hi >= bits as u128 {
                weigere(
                    absagen,
                    g.span,
                    "bit position beyond the word width -- «B24» is decided: a position lies \
                     inside the field's OWN word, and beyond it there is nothing to mean",
                );
                return;
            }
            let maske: u64 = if hi - lo + 1 >= 64 {
                u64::MAX
            } else {
                (((1u128 << (hi - lo + 1)) - 1) << lo) as u64
            };
            if belegt & maske != 0 {
                weigere(
                    absagen,
                    g.span,
                    "two bit positions overlap -- a word says which bits exist, and twice is \
                     not an answer",
                );
                return;
            }
            belegt |= maske;
            gruppe.push((g, hi, lo));
            i_feld += 1;
            // **Ein Wort endet, wenn seine Bits vollstaendig sind** -- und genau das macht
            // die Gruppenbildung deterministisch, ohne vorauszuzaehlen.
            //
            // *Der erste Anlauf las alle aufeinanderfolgenden Bitfelder gleicher Breite als
            // EIN Wort und meldete an `dscp @[7:2]` eine Ueberlappung mit `version @[7:4]`
            // -- zwei Bytes des IP-Kopfs, als eines gelesen.* Die Kachelung ist damit nicht
            // nur eine Pruefung, sondern die Wortgrenze selbst.
            let voll_hier: u64 = if bits >= 64 { u64::MAX } else { (1u64 << bits) - 1 };
            if belegt == voll_hier {
                break;
            }
        }
        // **Die Kachelung ist die Zusage.** Ohne sie waere die Wortgrenze geraten.
        let voll: u64 = if bits >= 64 { u64::MAX } else { (1u64 << bits) - 1 };
        if belegt != voll {
            weigere(
                absagen,
                feld.span,
                "the bit positions of this word leave a gap -- name it `reserved`; a format \
                 says which bits EXIST, and the emitter does not count along",
            );
            return;
        }
        for (g, hi, lo) in gruppe {
            if g.reserviert {
                if matches!(&g.typ.typ, TypExpr::Int(gi) if gi.bereich.is_some()) {
                    weigere(
                        absagen,
                        g.span,
                        "`in a .. b` at a `reserved` field -- a reserved field has no reader, \
                         so there is no place at which the bound could be established",
                    );
                    return;
                }
                continue;
            }
            let maske: u128 = if hi - lo + 1 >= 64 {
                u64::MAX as u128
            } else {
                (1u128 << (hi - lo + 1)) - 1
            };
            // **Ein `bool @N` liest sich als `bool` und nicht als Wortbreite.** Der Typ steht
            // in der Deklaration; ihn im Erzeugnis zu verbreitern hiesse, den Leser ein Bit
            // mit einer Zahl verwechseln zu lassen.
            let ergebnis = if matches!(&g.typ.typ, TypExpr::Bool(_)) { "bool" } else { &c };
            // **`scale K` gehoert IN den Leser.** Der Rohwert ist um `K` verkuerzt gespeichert
            // -- ihn ungeskaliert herauszugeben waere eine Zahl, die aussieht wie die richtige.
            let mal = match &g.typ.scale {
                Some(e) => match konst_zahl(e).or_else(|| match &e.art {
                    ExprArt::Ort(o) => u.konstwert.get(&o.text()).copied(),
                    _ => None,
                }) {
                    // **`D4`: the scale reaches C as a literal, and `2^64` is not one.**
                    // `konst_zahl` hands over anything that fits `i128`, and the next 64
                    // bits of the journey had no owner: `beispiele/gift/644` emitted
                    // `* 18446744073709551616u` and `cc` answered *integer constant is too
                    // large for its type*. `u64::try_from` is the fence at the place where
                    // the number becomes C, which is where it belongs.
                    Some(k) => match u64::try_from(k).ok().map(|v| format!(" * {v}u")) {
                        Some(t) => t,
                        None => {
                            weigere(
                                absagen,
                                g.span,
                                "`scale` past `2^64 - 1` -- the reader multiplies the raw \
                                 bits by this number and the multiplier goes into the C as a \
                                 literal. No C integer type holds it, so there is no reader \
                                 to write",
                            );
                            return;
                        }
                    },
                    None => {
                        weigere(absagen, g.span, "`scale` that is not a constant");
                        return;
                    }
                },
                None => String::new(),
            };
            aus.push_str(&format!(
                "static inline __attribute__((unused)) {ergebnis} {n}_{f2}(const {n} *v) {{ \
                 return ({ergebnis})(((({c}){leser}(v->bytes + {versatz}) >> {lo}) & {maske}u){mal}); }}\n",
                f2 = g.name.text
            ));
            // **Ein Bitfeld zu schreiben ist ein Lese-Aendere-Schreib-Zug auf dem GANZEN
            // Wort**, und deshalb steht die Maske hier zweimal: einmal zum Loeschen der
            // alten Bits, einmal zum Beschneiden der neuen. *Ein Setzer, der die Nachbarbits
            // mitnimmt, ist die Registerfalle 4 eine Ebene tiefer.*
            //
            // Mit `scale K` gibt es KEINEN Setzer: der Rueckweg waere eine Division, und ob
            // ein Wert ohne Rest durch `K` teilbar ist, sagt die Deklaration nicht. *Eine
            // Absenkung, die stillschweigend abrundet, ist genau die, gegen die dieses
            // Modul steht.*
            if g.typ.scale.is_none() {
                aus.push_str(&format!(
                    "static inline __attribute__((unused)) void {n}_setz_{f2}({n} *v, {ergebnis} x) {{ \
                     {c} w = ({c}){leser}(v->bytes + {versatz}); \
                     w = ({c})((w & ({c})~(({c}){maske}u << {lo})) | ((({c})x & {maske}u) << {lo})); \
                     {sw}(v->bytes + {versatz}, w); }}\n",
                    f2 = g.name.text
                ));
            }
            // **The pinning of a BIT field, and its width is the group's, not the carrier's.**
            // `grund : u64 @[39:32] in 1 .. 12` hands out eight bits; against `u64` the bound
            // would look like a real constraint everywhere and the tautology test would never
            // bite.
            if let TypExpr::Int(gi) = &g.typ.typ {
                if gi.bereich.is_some() {
                    // **`scale K` plus `in` is refused, not guessed.** The reader hands out
                    // `raw * K`; whether the declared bound means the raw value or the scaled
                    // one is not written anywhere, and *a generator that guesses undoes every
                    // pass in front of it*. Zero corpus sites ask for it.
                    if g.typ.scale.is_some() {
                        weigere(
                            absagen,
                            g.span,
                            "`in a .. b` together with `scale` -- the reader hands out the \
                             SCALED value, and which of the two the bound speaks about is \
                             not said",
                        );
                        return;
                    }
                    let vz = matches!(
                        gi.wort,
                        gabbro_syntax::kw::Kw::U8
                            | gabbro_syntax::kw::Kw::U16
                            | gabbro_syntax::kw::Kw::U32
                            | gabbro_syntax::kw::Kw::U64
                    );
                    pruefungen.extend(bereichspruefung(
                        gi,
                        n,
                        &g.name.text,
                        (hi - lo + 1) as u32,
                        vz,
                        u,
                        absagen,
                    ));
                }
            }
            if let Some(b) = &g.bedingung {
                match pred_c_format(b, n, u, absagen) {
                    Some(x) => pruefungen.push(x),
                    None => {
                        weigere(absagen, g.span, "`where` clause form in a `format`");
                        return;
                    }
                }
            }
        }
        versatz += breite;
    }
    // **Die `where`-Klauseln sind der Grund, warum danach kein Zugriff mehr eine
    // Laengenpruefung braucht** (`PFLICHTEN.md` F10). Sie stehen als EINE Funktion da, damit
    // der Rufer sie einmal stellt statt an jedem Feld.
    aus.push_str(&format!(
        "static inline __attribute__((unused)) bool {n}_gueltig(const {n} *v) {{\n    if (v->len < {versatz}u) return false;\n"
    ));
    for p in &pruefungen {
        aus.push_str(&format!("    if (!({p})) return false;\n"));
    }
    aus.push_str("    return true;\n}\n");
}

/// Der Leser fuer eine Breite und eine Bytereihenfolge. **Er wird MITERZEUGT**, nicht
/// vorausgesetzt: ein Erzeugnis, das eine Bibliothek braucht, ist kein Erzeugnis.
/// `Some(true)` = nachweislich vorzeichenlos, `Some(false)` = nachweislich mit Vorzeichen,
/// `None` = der Erzeuger weiss es nicht. **Die dritte Antwort wird wie die zweite behandelt.**
fn vorzeichen(t: &TypExpr, u: &Namen) -> Option<bool> {
    match t {
        TypExpr::Int(i) => Some(matches!(
            i.wort,
            gabbro_syntax::kw::Kw::U8
                | gabbro_syntax::kw::Kw::U16
                | gabbro_syntax::kw::Kw::U32
                | gabbro_syntax::kw::Kw::U64
        )),
        // `index into T` ist ein erzeugter, vorzeichenloser Index.
        TypExpr::Index { .. } => Some(true),
        TypExpr::Pfad(p) => {
            let n = &p.teile.last()?.text;
            match n.as_str() {
                "u8" | "u16" | "u32" | "u64" => Some(true),
                "i8" | "i16" | "i32" | "i64" => Some(false),
                _ => vorzeichen(traegertyp(n, u)?, u),
            }
        }
        _ => None,
    }
}

/// **The eight integer words, their C name and their width in bytes -- and NOTHING else.**
///
/// This one table is what all four hardware points stand on. It used to be two matches with
/// a `_` arm each: `intty` named seven words and let the eighth fall into `int64_t`,
/// `breite_von` named six and let the rest fall into `8`. *A new integer word would have
/// been lowered as a signed eight-byte one by both, silently* -- `gabbro pruefe` clean,
/// `cc -Werror` clean, and a device register accessed at the wrong width.
///
/// **A word that is not in this table has no width here, and the emitter says so.** The
/// callers turn the `None` into `C001` by name; none of them substitutes a plausible value.
/// The refusal is unreachable today and the test below says why: every word `ist_intty`
/// admits stands in this table, and the table admits no other. *The point is not that it
/// fires -- the point is that adding a ninth word is a translation error instead of a silent
/// byte.*
fn ganzzahlwort(k: gabbro_syntax::kw::Kw) -> Option<(&'static str, u32)> {
    use gabbro_syntax::kw::Kw;
    Some(match k {
        Kw::U8 => ("uint8_t", 1),
        Kw::U16 => ("uint16_t", 2),
        Kw::U32 => ("uint32_t", 4),
        Kw::U64 => ("uint64_t", 8),
        Kw::I8 => ("int8_t", 1),
        Kw::I16 => ("int16_t", 2),
        Kw::I32 => ("int32_t", 4),
        Kw::I64 => ("int64_t", 8),
        _ => return None,
    })
}

/// The width in BYTES of an integer type, or `None` for a word this emitter cannot lower.
fn breite_von(i: &IntTy) -> Option<u32> {
    ganzzahlwort(i.wort).map(|(_, b)| b)
}

/// The width, or a `C001` at the type's own span. **Zero comes back with the refusal**, and
/// that is safe because an emission with an error writes no C at all (`command_emit`); it is
/// the same shape `zahltext` uses for a table length it cannot read.
fn breite_oder_absage(i: &IntTy, absagen: &mut Absagen) -> u32 {
    match breite_von(i) {
        Some(b) => b,
        None => {
            weigere(absagen, i.span, "integer width -- no such word in the width table");
            0
        }
    }
}

/// Die Leser selbst. **Byteweise zusammengesetzt, nicht gecastet** -- ein `*(uint32_t*)p`
/// waere unausgerichtet und haette die Bytereihenfolge der Maschine statt der erklaerten.
/// **Die SCHREIBER, und sie standen bis zum 2026-08-20 nicht da** -- obwohl `SPRACHE.md`:355
/// sie seit jeher zusagt (*„Generates: reader, writer, C struct with fixed widths"*).
///
/// Gefunden beim ersten Treiber, der nicht aus dem Entwurf kam: ein virtio-net muss einen
/// ARP-Rahmen **stellen**, nicht bloss lesen. Der Erzeuger machte daraus
/// `EthArp_ethertyp(r) = 2054;` -- **eine Zuweisung an einen Funktionsaufruf**, und der
/// Pruefer meldete null Fehler.
///
/// > *Das ist die eine Fehlerklasse, gegen die dieses Modul gebaut ist:* es sieht aus wie
/// > eine Absenkung und ist keine. Dass `cc` es faengt, ist Glueck und keine Zusage -- ein
/// > `format` ohne Schreiber war eine halbe Absenkung mit einem ganzen Anschein.
const SCHREIBER_C: &[(&str, &str)] = &[
    ("gabbro_setz_u8", "static inline void gabbro_setz_u8(uint8_t *p, uint8_t v) { p[0] = v; }\n"),
    ("gabbro_setz_be16", "static inline void gabbro_setz_be16(uint8_t *p, uint16_t v) { p[0] = (uint8_t)(v >> 8); p[1] = (uint8_t)v; }\n"),
    ("gabbro_setz_le16", "static inline void gabbro_setz_le16(uint8_t *p, uint16_t v) { p[1] = (uint8_t)(v >> 8); p[0] = (uint8_t)v; }\n"),
    ("gabbro_setz_be32", "static inline void gabbro_setz_be32(uint8_t *p, uint32_t v) { p[0] = (uint8_t)(v >> 24); p[1] = (uint8_t)(v >> 16); p[2] = (uint8_t)(v >> 8); p[3] = (uint8_t)v; }\n"),
    ("gabbro_setz_le32", "static inline void gabbro_setz_le32(uint8_t *p, uint32_t v) { p[3] = (uint8_t)(v >> 24); p[2] = (uint8_t)(v >> 16); p[1] = (uint8_t)(v >> 8); p[0] = (uint8_t)v; }\n"),
    ("gabbro_setz_be64", "static inline void gabbro_setz_be64(uint8_t *p, uint64_t v) { gabbro_setz_be32(p, (uint32_t)(v >> 32)); gabbro_setz_be32(p + 4, (uint32_t)v); }\n"),
    ("gabbro_setz_le64", "static inline void gabbro_setz_le64(uint8_t *p, uint64_t v) { gabbro_setz_le32(p + 4, (uint32_t)(v >> 32)); gabbro_setz_le32(p, (uint32_t)v); }\n"),
];

/// Das Schreibwort zu einer Breite und Byteordnung -- Spiegel von `lesewort`.
///
/// **The four widths stand one by one, and none falls into a fifth.** Until 2026-08-31
/// `_ => "gabbro_setz_le64"` caught everything that was not `(8, true)`: measured 148 hits,
/// every one of them `(8, false)` -- answered correctly, but a width of 16 would have got
/// the same answer. *The arm was load-bearing and written as `_` instead of named.*
fn schreibwort(breite: u32, gross: bool) -> Option<&'static str> {
    Some(match (breite, gross) {
        (1, _) => "gabbro_setz_u8",
        (2, true) => "gabbro_setz_be16",
        (2, false) => "gabbro_setz_le16",
        (4, true) => "gabbro_setz_be32",
        (4, false) => "gabbro_setz_le32",
        (8, true) => "gabbro_setz_be64",
        (8, false) => "gabbro_setz_le64",
        _ => return None,
    })
}

const LESER_C: &[(&str, &str)] = &[
    ("gabbro_u8", "static inline uint8_t gabbro_u8(const uint8_t *p) { return p[0]; }\n"),
    ("gabbro_be16", "static inline uint16_t gabbro_be16(const uint8_t *p) { return (uint16_t)((uint16_t)p[0] << 8 | p[1]); }\n"),
    ("gabbro_le16", "static inline uint16_t gabbro_le16(const uint8_t *p) { return (uint16_t)((uint16_t)p[1] << 8 | p[0]); }\n"),
    ("gabbro_be32", "static inline uint32_t gabbro_be32(const uint8_t *p) { return (uint32_t)p[0] << 24 | (uint32_t)p[1] << 16 | (uint32_t)p[2] << 8 | p[3]; }\n"),
    ("gabbro_le32", "static inline uint32_t gabbro_le32(const uint8_t *p) { return (uint32_t)p[3] << 24 | (uint32_t)p[2] << 16 | (uint32_t)p[1] << 8 | p[0]; }\n"),
    ("gabbro_be64", "static inline uint64_t gabbro_be64(const uint8_t *p) { return (uint64_t)gabbro_be32(p) << 32 | gabbro_be32(p + 4); }\n"),
    ("gabbro_le64", "static inline uint64_t gabbro_le64(const uint8_t *p) { return (uint64_t)gabbro_le32(p + 4) << 32 | gabbro_le32(p); }\n"),
];

/// The reader word -- the same enumeration as `schreibwort`; the struck `_` was measured at
/// 107 hits, all of them `(8, false)`.
fn lesewort(breite: u32, gross: bool) -> Option<&'static str> {
    Some(match (breite, gross) {
        (1, _) => "gabbro_u8",
        (2, true) => "gabbro_be16",
        (2, false) => "gabbro_le16",
        (4, true) => "gabbro_be32",
        (4, false) => "gabbro_le32",
        (8, true) => "gabbro_be64",
        (8, false) => "gabbro_le64",
        _ => return None,
    })
}

/// **Rotation helpers (PLAN-BITS §3): the portable shift-or pattern, once per width.**
///
/// C has no rotate, and the pattern needs the amount TWICE (`x << s` and
/// `x >> (w - s)`). Emitting it inline would evaluate an effectful amount twice
/// -- a duplicated call is a duplicated effect, not a rotation. So the pattern
/// lives in a helper and the call site passes each argument ONCE, the way C
/// passes every argument once. The amount is masked inside (`s &= w-1`), which
/// is the masking PLAN-BITS §3 asks for, and which also keeps the `w - s` shift
/// below the width when `s` is 0 (a plain `x >> (w - s)` is undefined there).
///
/// Sub-32-bit rotations compute in `unsigned int` and cast back: a `uint16_t`
/// promotes to SIGNED `int` in C, and `x << 15` on the promoted value would
/// leave the signed range. The final cast keeps the low `w` bits, which are
/// exactly the rotated word; the conversion to an unsigned type is defined as
/// the value modulo `2^w`.
const DREH_C: &[(&str, &str)] = &[
    ("gabbro_rotl8", "static inline uint8_t gabbro_rotl8(uint8_t x, uint8_t s) { s &= 7; return (uint8_t)(((unsigned)x << s) | ((unsigned)x >> ((8 - s) & 7))); }\n"),
    ("gabbro_rotr8", "static inline uint8_t gabbro_rotr8(uint8_t x, uint8_t s) { s &= 7; return (uint8_t)(((unsigned)x >> s) | ((unsigned)x << ((8 - s) & 7))); }\n"),
    ("gabbro_rotl16", "static inline uint16_t gabbro_rotl16(uint16_t x, uint16_t s) { s &= 15; return (uint16_t)(((unsigned)x << s) | ((unsigned)x >> ((16 - s) & 15))); }\n"),
    ("gabbro_rotr16", "static inline uint16_t gabbro_rotr16(uint16_t x, uint16_t s) { s &= 15; return (uint16_t)(((unsigned)x >> s) | ((unsigned)x << ((16 - s) & 15))); }\n"),
    ("gabbro_rotl32", "static inline uint32_t gabbro_rotl32(uint32_t x, uint32_t s) { s &= 31; return (x << s) | (x >> ((32 - s) & 31)); }\n"),
    ("gabbro_rotr32", "static inline uint32_t gabbro_rotr32(uint32_t x, uint32_t s) { s &= 31; return (x >> s) | (x << ((32 - s) & 31)); }\n"),
    ("gabbro_rotl64", "static inline uint64_t gabbro_rotl64(uint64_t x, uint64_t s) { s &= 63; return (x << s) | (x >> ((64 - s) & 63)); }\n"),
    ("gabbro_rotr64", "static inline uint64_t gabbro_rotr64(uint64_t x, uint64_t s) { s &= 63; return (x >> s) | (x << ((64 - s) & 63)); }\n"),
];

/// Reader and writer word for a width, or a refusal by name. **A word this emitter does not
/// have is not replaced by the next best one.**
fn wortpaar_oder_absage(
    breite: u32,
    gross: bool,
    span: gabbro_syntax::span::Span,
    absagen: &mut Absagen,
) -> (&'static str, &'static str) {
    match (lesewort(breite, gross), schreibwort(breite, gross)) {
        (Some(l), Some(s)) => (l, s),
        _ => {
            weigere(absagen, span, &format!("a {breite}-byte word -- no reader/writer for it"));
            ("", "")
        }
    }
}

/// Eine `where`-Klausel im `format`. Feldnamen darin sind Zugriffe auf DAS Format, und
/// `lenof(Self)` ist seine Laenge.
fn pred_c_format(p: &Pred, fmt: &str, u: &Namen, absagen: &mut Absagen) -> Option<String> {
    Some(match &p.art {
        PredArt::Vergleich(e) => ausdruck_format(e, fmt, u, absagen),
        PredArt::Klammer(x) => format!("({})", pred_c_format(x, fmt, u, absagen)?),
        PredArt::Nicht(x) => format!("!({})", pred_c_format(x, fmt, u, absagen)?),
        PredArt::Und(a, b) => format!(
            "{} && {}",
            pred_c_format(a, fmt, u, absagen)?,
            pred_c_format(b, fmt, u, absagen)?
        ),
        // **The disjunction -- «B22-near», 2026-08-25.** A format says "absence" and
        // "unreadable" with ONE function, `X_gueltig`; without `||` it cannot say that a
        // constraint holds only of a record that CARRIES something:
        //
        //     grund : u64 @[39:32] where f_bit == 0 || (grund >= 1 && grund <= 12),
        //
        // The form was writable all along -- `pred = orpred` (SYNTAX.md:614) -- and parsed,
        // and name-checked by `N032` (issued in `namen.rs`). **Only this arm was missing**, so
        // the emitter refused with `C001` and the two answers stayed one.
        //
        // **The parentheses are load-bearing, and NOT for looks.** In C `&&` binds tighter
        // than `||`, so an `Und` may sit unparenthesised above (its operands cannot be
        // reassociated wrongly) -- a bare `||` may NOT: `where (a || b) && c` would lower to
        // `a || b && c`, which is `a || (b && c)`. *A precedence slip here is a check that
        // silently passes a record it should refuse.*
        PredArt::Oder(a, b) => format!(
            "({} || {})",
            pred_c_format(a, fmt, u, absagen)?,
            pred_c_format(b, fmt, u, absagen)?
        ),
        _ => return None,
    })
}

/// **The pinning `in a .. b` at a format field -- and until 2026-08-25 it fell SILENTLY.**
///
/// `format_` read exactly two things out of a field type, `breite_von` and `intty`;
/// `IntTy::bereich` was read nowhere in this function. **Sixteen declarations of the corpus
/// therefore lowered to nothing** -- `EthArp` pins six fields and `EthArp_gueltig` checked
/// only the length, so any 42 bytes were a valid ARP record; `Elf64Kopf` pins the magic and
/// 46 arbitrary bytes were a valid ELF header.
///
/// **And the expensive half is not the missing check, it is that M1 BELIEVES the pinning.**
/// `umgebung.rs::typexpr` hands a format field its declared range like any other type, so
/// `M103` (issued in `m1.rs`) waives the index bound on `let i : index into T = k.nr;` when `nr` says
/// `u32 in 0 .. 7`. Nobody established it. Measured under the same sanitizer
/// `pruefe-emission.sh` runs: `runtime error: load of address … with insufficient space`.
///
/// > *That is «B33» one storey up.* At a `device` register the answer was to REFUSE the
/// > fact, because the hardware may set the word freely. At a format field the fact is
/// > DECLARED, and `X_gueltig` is exactly the place it belongs -- every reader passes it.
///
/// Returns the comparisons, 0 to 2 of them. **A bound that coincides with the carrier's own
/// range yields none**, and that is not tidiness: `e_phnum : u16 in 0 .. 65535` would lower
/// to a tautology, and `pruefe-emission.sh` compiles with `-Werror=type-limits`.
fn bereichspruefung(
    i: &IntTy,
    fmt: &str,
    feld: &str,
    bits: u32,
    vorzeichenlos: bool,
    u: &Namen,
    absagen: &mut Absagen,
) -> Vec<String> {
    let Some(b) = &i.bereich else {
        return Vec::new();
    };
    let zugriff = format!("{fmt}_{feld}(v)");
    // A bound may be a literal or a named constant; `scale` resolves them the same way.
    let wert = |e: &Expr| -> Option<i128> {
        konst_zahl(e).or_else(|| match &e.art {
            ExprArt::Ort(o) => u.konstwert.get(&o.text()).copied(),
            _ => None,
        })
    };
    // **The range the READER can hand out** -- for a byte-wise field the carrier's width,
    // for a bit field the width of its OWN bit group. *A `u64 @[39:32]` yields 0 .. 255, so
    // `in 1 .. 12` is a real constraint there and `in 0 .. 255` is not.*
    let (min, max): (i128, i128) = if vorzeichenlos {
        (0, (1i128 << bits) - 1)
    } else {
        (-(1i128 << (bits - 1)), (1i128 << (bits - 1)) - 1)
    };
    // The `u` suffix keeps `-Wsign-compare` quiet: the reader hands out an unsigned type,
    // and a bare decimal literal is `int`.
    let zahl = |v: i128| if vorzeichenlos { format!("{v}u") } else { format!("{v}") };
    let mut aus = Vec::new();
    match wert(&b.von) {
        Some(v) if v <= min => {}
        Some(v) => aus.push(format!("{zugriff} >= {}", zahl(v))),
        None => aus.push(format!("{zugriff} >= {}", ausdruck_format(&b.von, fmt, u, absagen))),
    }
    let op = if b.exklusiv { "<" } else { "<=" };
    match wert(&b.bis) {
        // `..<` excludes the top: only `bis > max` is vacuous, `bis == max` still bites.
        Some(v) if (b.exklusiv && v > max) || (!b.exklusiv && v >= max) => {}
        Some(v) => aus.push(format!("{zugriff} {op} {}", zahl(v))),
        None => aus.push(format!("{zugriff} {op} {}", ausdruck_format(&b.bis, fmt, u, absagen))),
    }
    aus
}

/// Wie `ausdruck`, aber ein blanker Name ist ein FELD dieses Formats.
fn ausdruck_format(e: &Expr, fmt: &str, u: &Namen, absagen: &mut Absagen) -> String {
    match &e.art {
        ExprArt::Ort(o) if o.suffixe.is_empty() && !u.konstanten.contains(&o.basis.text) => {
            format!("{fmt}_{}(v)", o.basis.text)
        }
        ExprArt::Klammer(x) => format!("({})", ausdruck_format(x, fmt, u, absagen)),
        ExprArt::Binaer(op, a, b) => format!(
            "{} {} {}",
            geklammert(op, a, ausdruck_format(a, fmt, u, absagen)),
            op_text(op),
            geklammert(op, b, ausdruck_format(b, fmt, u, absagen))
        ),
        // `lenof(Self)` ist die Laenge des Puffers -- die Groesse, an der jede
        // `where`-Klausel dieses Formats haengt.
        ExprArt::Eingebaut(b) if matches!(b.as_ref(), Eingebaut::Lenof(_)) => "v->len".into(),
        // **Die Verneinung muss durch DIESEN Leser zurueck, nicht durch den gewoehnlichen**
        // (2026-08-21). Der Sammelzweig schickte sie an `ausdruck`, und der senkt einen
        // blanken Namen als ORT ab statt als Feldzugriff: aus `!gueltig` waere `!(gueltig)`
        // geworden, wo `!(Elf_gueltig(v))` gemeint ist -- **ein Bezeichner, den die erzeugte
        // Datei nirgends erklaert.** *Der Fehler faellt bei `cc`; entschieden gehoert er
        // hier.*
        ExprArt::Unaer(UnOp::Nicht, x) => format!("!({})", ausdruck_format(x, fmt, u, absagen)),
        // **`~` in a `where` clause is refused by name, and the reason is the width.** A
        // field reader is called `Elf_gueltig(v)` here; which C width it returns stands in
        // the `format` declaration and not in this reader. *Without the width the emitted
        // `~` would be an `int` complement* -- exactly the defect this operator is built
        // against. Zero corpus sites ask for it (Rule A).
        ExprArt::Unaer(UnOp::BitNicht, _) => {
            weigere(
                absagen,
                e.span,
                "`~` inside a `where` clause of a `format` -- the complement needs the WIDTH \
                 of its operand, and a field reader's width is not readable at this point",
            );
            String::new()
        }
        // **Ein Ort MIT Suffix hat in einer `where`-Klausel keinen Gegenstand.** In der
        // erzeugten Pruefkoerperfunktion steht genau ein Objekt: `v`, der Puffer. `a.b` oder
        // `a[i]` nennt etwas, das dort nicht existiert -- und `ausdruck` haette daraus
        // klaglos `a->b` gemacht.
        ExprArt::Ort(o) if !o.suffixe.is_empty() => {
            weigere(
                absagen,
                o.span,
                "a `where` clause of a `format` names FIELDS of that format -- a place with \
                 `.`, `->` or `[…]` names something the generated accessor has no object for",
            );
            String::new()
        }
        // **Und die Formen, die der gewoehnliche Leser richtig beantwortet -- einzeln, mit
        // ihrem Grund.** Ein Literal ist in jedem Zusammenhang dasselbe; ein blanker Name,
        // der eine `const` ist, steht als `#define` im Kopf des Erzeugnisses; ein Ruf ist
        // ein Ruf. Die drei ohne Absenkung (`sizeof`/`aligned`, `old`, `result`) lehnt
        // `ausdruck` beim Namen ab -- **die Absage gehoert dorthin, wo der Satz dafuer
        // steht** (W7), nicht ein zweites Mal hierher.
        ExprArt::Zahl(_)
        | ExprArt::Gleitkomma { .. }
        | ExprArt::Wahr
        | ExprArt::Falsch
        | ExprArt::Ort(_)
        | ExprArt::Ruf(_)
        | ExprArt::Eingebaut(_)
        | ExprArt::Alt(_)
        | ExprArt::Ergebnis
        // **`FnWert` and `Grund`, 2026-08-21.** Neither can stand in a `format` condition:
        // a `where` clause speaks about the FIELDS of the format, and a function pointer or
        // a reason value is not one. They go through the same fallthrough as the other
        // non-field forms -- `ausdruck` refuses them by name if they ever get here.
        | ExprArt::FnWert(_)
        | ExprArt::Grund { .. }
        // **Lane E1:** a library call in a `where` clause lowers through the
        // general reader, which refuses it by name -- like any other call form.
        // **Lane 111:** a table literal likewise -- it never stands here (the
        // parser reads `[` only as a `const` initializer), and the general
        // reader answers for it.
        | ExprArt::LibraryCall(_)
        | ExprArt::ArrayLit(_)
        | ExprArt::Unaer(UnOp::Negativ, _) => ausdruck(e, u, absagen),
        // **«SG-24»: a `count` has no object here.** The generated counter functions are
        // declared with the functions, after the format accessors -- a `where` clause
        // calling one would be an implicit declaration. *A `where` speaks about the
        // FIELDS of its format; counting table slots in one is refused, by name.*
        ExprArt::Zaehle { .. } => {
            weigere(
                absagen,
                e.span,
                "`count` in a `where` clause of a `format` -- the generated counter is \
                 declared with the functions, after the format accessors, and a `where` \
                 clause speaks about the FIELDS of its format",
            );
            String::new()
        }
    }
}

/// The C word of an integer type. **`None` for a word the table does not carry** -- the word
/// IS the width («B32»: `u32 wrapping` lowers to `uint32_t`, whose wraparound C defines, and
/// the wraparound is spoken at the declaration, not tolerated).
fn intty(i: &IntTy) -> Option<String> {
    ganzzahlwort(i.wort).map(|(c, _)| c.to_string())
}

/// The C word, or a `C001` at the type's own span -- the mirror of `breite_oder_absage`.
fn intty_oder_absage(i: &IntTy, absagen: &mut Absagen) -> String {
    match intty(i) {
        Some(c) => c,
        None => {
            weigere(absagen, i.span, "integer type -- no such word in the width table");
            String::new()
        }
    }
}

/// The array length of a `table`. **A length this emitter cannot read is refused** — the same
/// reason as above, and here it decides how much memory the struct has.
fn zahltext(e: &Expr, absagen: &mut Absagen) -> String {
    match &e.art {
        ExprArt::Zahl(n) => czahl_oder_absage(*n, e.span, absagen),
        ExprArt::Ort(o) => o.text(),
        _ => {
            weigere(absagen, e.span, "table length");
            String::new()
        }
    }
}

/// The C type for a Gabbro type. **Range types lower to their carrier** -- the range itself is
/// an M1 fact and lives in the checker, not in the C.
/// **A C function pointer declarator** -- `bool (*bereit)(void)`, `void (*senden)(uint8_t)`.
///
/// C11 §6.7.6.3: the declared name sits between the `*` and the parameter list, so the type
/// cannot be produced as a string that a name is appended to. Pass an empty `name` for the
/// abstract form (`bool (*)(void)`), which is what a parameter or a cast needs.
///
/// **`(void)` and not `()`.** An empty parameter list in C means *unspecified*, and under
/// `-Wstrict-prototypes` that is a warning; more to the point, it is a different type. *The
/// generator writes the type the declaration says, not the one that happens to compile.*
///
/// The contract is **not** emitted, and that is the division this whole item rests on: the
/// effects and the cost bound are checker facts (W6), exactly as a range type's bounds are.
/// What reaches the C is the shape.
fn fnzeiger_deklarator(z: &FnZeiger, name: &str, u: &Namen) -> Option<String> {
    let rueck = match &z.ergebnis {
        Some(e) => ctyp(e, u)?,
        None => "void".to_string(),
    };
    let params = if z.parameter.is_empty() {
        "void".to_string()
    } else {
        z.parameter
            .iter()
            .map(|p| ctyp(&p.typ, u))
            .collect::<Option<Vec<_>>>()?
            .join(", ")
    };
    Some(format!("{rueck} (*{name})({params})"))
}

/// **The C word of a type that needs NO unit context** -- the primitive rows of `ctyp`.
///
/// Split out on 2026-09-01 because a second reader appeared: `N046` compares the lowering of
/// an `extern fn` against the signature C already knows for the name, and it has no `Namen`
/// to resolve a `table` or a range type with. **What it CAN spell, it must spell exactly the
/// way `emit.rs` does** -- two spellings of one fact is the shape a false green comes in.
///
/// *`None` is not "unknown", it is "not decidable without the unit"* -- and the caller behind
/// `N046` turns that into a refusal, never into a pass.
pub(crate) fn ctyp_primitiv(t: &TypExpr) -> Option<&'static str> {
    match t {
        TypExpr::Int(i) => ganzzahlwort(i.wort).map(|(c, _)| c),
        // **«F»: `f32`/`f64` senken zu `float`/`double` ab -- und mehr sagt der Erzeuger
        // nicht.** Der Bereich ist ein M1-Faktum und lebt im Pruefer, genau wie beim
        // Ganzzahlbereich; die zwei Bits ebenso.
        //
        // **And both words stand one by one.** Until 2026-08-31 an
        // `if f32 { float } else { double }` stood here -- the same disease as
        // `_ => "int64_t"`, only written as an `else`: a third floating point word would
        // silently have become a `double`. *Now there is `None`, and `ctyp`'s callers
        // refuse by name.*
        TypExpr::Float(f) => match f.wort {
            gabbro_syntax::kw::Kw::F32 => Some("float"),
            gabbro_syntax::kw::Kw::F64 => Some("double"),
            _ => None,
        },
        TypExpr::Bool(_) => Some("bool"),
        TypExpr::Pfad(p) => primitivwort(&p.teile.last()?.text),
        _ => None,
    }
}

/// **Does this pointer let the callee WRITE?** -- the one home of the `const` decision.
///
/// Split out on 2026-09-02 because a second reader appeared: the `N046` signature comparison
/// has to decide `void *` against `const void *` for a bound `extern fn`, and it decides it
/// from the same rights list this does. *Two spellings of one fact is the register `W7` warns
/// about, and here the second would disagree at exactly `Recht::Eigen`.*
pub(crate) fn zeiger_schreibend(z: &gabbro_syntax::ast::PtrTy) -> bool {
    z.rechte.iter().any(|r| {
        matches!(
            r,
            Recht::Schreiben | Recht::LesenSchreiben | Recht::Eigen(_)
        )
    })
}

/// **The C qualifier the pointer's SPACE earns -- `volatile` for `mmio` and `dma`, nothing
/// else** (2026-09-15, lane "grammar into the emitter").
///
/// It stands here because `R008` in `m3.rs` says of itself, word for word:
///
/// > *"the address space is part of what a pointer IS -- `mmio` is volatile and
/// > device-mapped, `normal` is not, **and the emitter lowers them differently**"*
///
/// **And until today it did not.** Measured 2026-09-15 on six programs differing in nothing
/// but the space word, each dereferencing through the pointer: six byte-identical C files.
/// *A refusal that names a lowering the generator does not write is a promise nobody keeps* --
/// and it is the worse half of `W16`, because the sentence reads like a measurement.
///
/// **Two spaces earn the qualifier and four do not, and the reason is per space:**
///
/// * `mmio` -- a load IS the device access. Without `volatile` the C compiler may fold two
///   reads into one, hoist one out of a loop, or delete a store whose value is never read
///   back. Every one of those is a different program at the device, and none of them is a
///   diagnostic. The device HANDLE already carries `volatile uint8_t *basis` for exactly this
///   reason (`geraet`); a `ptr<mmio, …>` at a plain carrier had nothing.
/// * `dma` -- memory a device writes behind the CPU's back. The same three transformations
///   are the same defect; that the other writer is a bus master rather than a register file
///   changes nothing the compiler can see.
/// * `normal` is ordinary memory, `boot` is ordinary memory in a link-time section
///   (`SYNTAX.md`:1607) -- a section is a placement, not an access form. `code` is never
///   dereferenced (an incomplete type behind an `extern fn`), so there is no access to
///   qualify. `port` never reaches this function: `funktion` refuses a body carrying a
///   `ptr<port, …>` that is not a port device, and a port device is reached by `in`/`out`.
///
/// **Why `volatile` and not a second pass:** C already has the word for "this object may
/// change without this program changing it", and `cc` enforces it at every access. Inventing
/// a Gabbro-side rule beside it would be a second register over one fact (`W7`), and the
/// second one would be the one that forgets an access form.
/// * `Benannt` -- a space a program declared itself (`ptr<user, r> u8`). The generator knows
///   no access form for it and must not invent one; it lowers like `normal`, which is what it
///   did before this function existed. *A qualifier guessed for a name is the move `C001`
///   stands against.*
pub(crate) fn raumqualifizierer(raum: &Raum) -> &'static str {
    match raum {
        Raum::Mmio | Raum::Dma => "volatile ",
        Raum::Normal | Raum::Boot | Raum::Code | Raum::Port | Raum::Benannt(_) => "",
    }
}

/// The primitive type words, by their Gabbro spelling. **The one home of these eleven rows.**
pub(crate) fn primitivwort(n: &str) -> Option<&'static str> {
    Some(match n {
        "bool" => "bool",
        "u8" => "uint8_t",
        "u16" => "uint16_t",
        "u32" => "uint32_t",
        "u64" => "uint64_t",
        "i8" => "int8_t",
        "i16" => "int16_t",
        "i32" => "int32_t",
        "i64" => "int64_t",
        "f32" => "float",
        "f64" => "double",
        _ => return None,
    })
}

/// **The C declarator of an `atomic`, WITHOUT the `_Atomic` in front of it.**
///
/// `atomic GESAMT : u32` gives `uint32_t GESAMT`; `atomic REGEL : [u32; 256]` gives
/// `uint32_t REGEL[256]`. The caller writes the `_Atomic` and the `;`, so the two
/// declaration arms (ordered and payload-free) stay one line each.
///
/// **Why the array is a qualified ELEMENT type and not a qualified array type.** C11
/// 6.7.2.4p3 forbids `_Atomic` applied to an array type -- `_Atomic (uint32_t[256])` is
/// a constraint violation. `_Atomic uint32_t REGEL[256]` is the other thing: an array
/// whose ELEMENTS are atomic objects, and `&REGEL[i]` is then an `_Atomic uint32_t *`,
/// which is exactly the first parameter of every `atomic_*_explicit` generic. *One
/// atomic object per element is also what the source says -- an indexed increment
/// touches one counter, never the array.*
///
/// **The length must FOLD, and an unfoldable one is a refusal and not a guess.** `[]`
/// with no size would be an incomplete type at file scope; a guessed size would be a
/// buffer the program never asked for. `feldlaenge_von` reads the constant `umgebung.rs`
/// already folded (W7: one fold, one reader).
fn atom_declarator(a: &gabbro_syntax::ast::AtomicDecl, u: &Namen) -> Option<String> {
    match &a.typ {
        TypExpr::Feld(f) => {
            let c = ctyp(&f.element, u)?;
            let n = feldlaenge_von(&a.typ, u)?;
            Some(format!("{c} {}[{n}]", a.name.text))
        }
        t => Some(format!("{} {}", ctyp(t, u)?, a.name.text)),
    }
}

/// **The reason an `atomic` declaration has no lowering, and the two reasons are
/// different.** An unresolvable element word and an unfoldable length both end at the
/// same `None` above, and a reader who gets "unresolvable type" for `[u32; N]` with a
/// perfectly good `u32` in it goes looking in the wrong half. *The old sentence stands
/// unchanged wherever it was right.*
fn atom_refusal(a: &gabbro_syntax::ast::AtomicDecl, u: &Namen) -> &'static str {
    match &a.typ {
        TypExpr::Feld(f) if ctyp(&f.element, u).is_some() => {
            "`atomic` array whose length is not a compile-time constant -- the C \
             declaration needs a size, `[]` at file scope is an incomplete type, and a \
             guessed one is a buffer nobody asked for"
        }
        _ => "`atomic` of an unresolvable type",
    }
}

fn ctyp(t: &TypExpr, u: &Namen) -> Option<String> {
    // **The rows that need no unit** stand in `ctyp_primitiv` and are read from TWO places
    // now: here, and the signature comparison behind `N046`. *A second reader is exactly the
    // moment a table stops being allowed two homes.*
    if let Some(c) = ctyp_primitiv(t) {
        return Some(c.into());
    }
    match t {
        // The abstract declarator -- a function pointer in a position that has no name of
        // its own (a parameter, a result). See `fnzeiger_deklarator`.
        TypExpr::FnZeiger(z) => fnzeiger_deklarator(z, "", u),
        // The three primitive shapes are answered above. A word the width table does not
        // carry has no C here, and the callers turn the `None` into `C001` by name.
        TypExpr::Int(_) | TypExpr::Float(_) | TypExpr::Bool(_) => None,
        TypExpr::Pfad(p) => {
            let n = p.teile.last()?.text.clone();
            Some(match n.as_str() {
                // **A path naming a table IS the struct.** The first version lowered it to
                // `uint32_t` and called that a coarsening in the safe direction -- it was not
                // coarse, it was wrong: `ptr<normal, r> Objekte` became `const uint32_t *`,
                // and the generated C would have compiled while pointing at the wrong thing.
                // *W9 asks for the direction of a coarsening; it does not license one where
                // the exact answer is available.*
                _ if u.tabellen.iter().any(|x| *x == n) => n,
                // Ein Pfad, der ein `format` nennt, ist sein Zugriffsverbund.
                _ if u.formate.contains(&n) => n,
                // Ein Pfad, der ein `device` nennt, ist sein Griff.
                _ if u.geraete.contains_key(&n) => n,
                // **Ein Pfad, der einen Verbund nennt, IST der Verbund** («B7»). Er steht
                // VOR der Bereichstypzeile darunter: `u.typen` enthaelt ihn auch, und dort
                // wuerde `ctyp` in den Rumpf absteigen und an `TypExpr::Verbund` scheitern
                // -- also `None`, also eine Weigerung fuer einen Typ, den diese Einheit
                // gerade selbst deklariert hat.
                _ if u.verbunde.contains(&n) => n,
                // **Ein Pfad, der eine MARKE nennt, IST ihr Verbund** -- ein Byte, das
                // niemand liest. Siehe `Namen::marken`.
                _ if u.marken.contains(&n) => n,
                // **Ein Pfad, der einen `tagged type` nennt, IST der markierte Verbund**
                // («C2»). Er steht aus demselben Grund vor der Bereichstypzeile wie der
                // Verbund darueber: `u.typen` enthaelt ihn auch, und dort waere sein Rumpf
                // ein `TypExpr::Varianten`, an dem `ctyp` scheitert.
                _ if u.markierte.contains_key(&n) => n,
                // **A path naming a `reason` IS its enum** (2026-08-25). `ItemArt::Reason`
                // writes `typedef enum { R_A = 0, … } R;`, so the name carries itself -- and
                // the CONTRACT of the reason (which values exist, that it is `exhaustive`) is
                // a checker fact and stays there, exactly as a range type's bounds do (W6).
                //
                // *It stands before the range-type line below for the same reason the two
                // above do:* `u.typen` does not hold it, but a future carrier line would, and
                // an order that is right by accident is not an order.
                _ if u.gruende.contains(&n) => n,
                // **A named range type lowers to its carrier.** `type Zaehler = u32 in
                // 0 .. 65535` becomes `uint32_t`; the range itself is an M1 fact and stays in
                // the checker -- W6: what is left out of the C is left out because M1 carries
                // it, and for nothing else.
                _ if traegertyp(&n, u).is_some() => {
                    return ctyp(traegertyp(&n, u)?, u);
                }
                // A named type whose carrier is not resolved here. Refused rather than
                // guessed -- see the head of this file.
                _ => return None,
            })
        }
        // `index into T` -- the bound comes from `count N` and is an M1 fact.
        //
        // **`option index into T` carries a SENTINEL, and the sentinel is `N` itself.**
        //
        // The representation was open until 2026-08-17 and the emitter refused rather than
        // coarsen — lowering the option to a bare `uint32_t` would have erased the `None`
        // silently. The decision now taken is the cheap one, and it is *cheap because of
        // `count N`*: the index type is `0 ..< N`, so **`N` is the one value M1 guarantees no
        // real index ever takes.** No extra word, no tag.
        //
        // > *And it is what the measured code already does by hand:* Caprock walks its queues
        // > as `while i != NIL { i = t.qnext }` (`MESSUNGEN.md`, B3). The construct does not
        // > invent the sentinel — it makes it checked and names it once.
        //
        // **The obligation this buys is entered in the register** as `option.sentinel`: the
        // sentinel is outside the index domain, and no arithmetic reaches it.
        TypExpr::Index { .. } => Some("uint32_t".into()),
        TypExpr::Zeiger(z) => {
            // **A pointer to a type this unit does not declare becomes an INCOMPLETE C type.**
            // `extern fn melde_roh(text : ptr<code, r> Text)` names `Text` and nowhere declares
            // it -- the fragment is an excerpt of a larger program.
            //
            // *This is not a guess.* C already carries exactly the rule the emitter would
            // otherwise have to invent: behind a pointer an incomplete type is legal, and any
            // use that needs the layout is a compile error. **The refusal is delegated, not
            // dropped** -- and it is delegated to the one tool that can decide it.
            let ziel = match ctyp(&z.ziel, u) {
                Some(z) => z,
                None => match &z.ziel {
                    TypExpr::Pfad(p) => format!("struct {}", p.teile.last()?.text),
                    _ => return None,
                },
            };
            let konst = if zeiger_schreibend(z) { "" } else { "const " };
            // **The qualifier goes where THIS function writes the access, and nowhere else.**
            // A `device` handle and a `format` handle are both dereferenced by a GENERATED
            // ACCESSOR (`Virtq_AVAIL_RING_setz_e`, `EthArp_setz_ethertyp`), never by the
            // caller; the accessor is the one home of that access form, and it is generated
            // once per declaration, not once per space. Qualifying the HANDLE at the caller
            // would make the two disagree about a pointer neither of them dereferences
            // directly -- measured 2026-09-15: `-Werror=discarded-qualifiers` at every call
            // site of a generated setter, in `messung/treiber/virtio-net.gab` and
            // `messung/proben/probe-netz-rahmen-und-ergebnis.gab`.
            //
            // For the device half the rule is already written down. `beispiele/gift/416`, in
            // its own text: *"the space at the POINTER does not decide the access form -- the
            // `device` declaration does"*. A `ptr<mmio, r> SerialCom1` does not point at
            // device memory; it points at the HANDLE, which is ordinary memory carrying
            // `volatile uint8_t *basis`, and the register access is volatile down there
            // already.
            //
            // **What stays open, and it is named rather than papered over:** a `format` in
            // `dma` is a byte view of memory a device writes, and its accessor does NOT
            // qualify its loads and stores. The space is carried at the CALLER for every
            // target this function lowers inline -- a primitive, a record, a table, an index
            // -- and at the generated accessor for the two that have one.
            let hinter_erzeugtem_zugriff = match &z.ziel {
                TypExpr::Pfad(p) => p.teile.last().is_some_and(|t| {
                    u.geraete.contains_key(&t.text) || u.formate.contains(&t.text)
                }),
                _ => false,
            };
            let raum = if hinter_erzeugtem_zugriff {
                ""
            } else {
                raumqualifizierer(&z.raum)
            };
            Some(format!("{konst}{raum}{ziel} *"))
        }
        _ => None,
    }
}

/// **A `spec fn` is specification and has no C.** Everything else with a body becomes a
/// definition; everything else *without* one becomes a **prototype** — without it a call in
/// C11 is an implicit declaration, and `-Werror` stops there.
/// **Ruft dieser Rumpf irgendetwas?** Erschöpfend über `unterbloecke`/`eigene_ausdruecke`,
/// also ohne die Sammelzweig-Blindheit, an der `sammle_rufe` bis 2026-08-19 litt.
fn ruft_irgendwas(b: &Block) -> bool {
    // **The descent was exhaustive over STATEMENTS and hand-rolled one level below**
    // (measured 2026-09-02). `in_expr` named four forms and closed with `_ => false`, so a
    // call in INDEX position was no call:
    //
    // ```text
    // let i = fremd(); return t.slots[i].x;   ->  static uint32_t f(const T *restrict t)
    // return t.slots[fremd()].x;              ->  … __attribute__((pure))
    // ```
    //
    // Two bodies of the same meaning, and the attribute depends on where the call sits.
    // *`beispiele/gift/179` names this very consequence in its own text and expects
    // `E008`; with a `pure` callee no `E008` falls, and the attribute comes back.*
    // Compiled: `cc -O2 -fno-inline` deletes BOTH calls in the second form -- `zaehler`
    // ends at 0 -- and keeps both in the first.
    //
    // **`alle_ausdruecke` decides every form once, and the reasons stand at
    // `unterausdruecke`:** an index is evaluated, `aligned` evaluates both sides,
    // `sizeof`/`lenof` reach only the indices of their place, and `&f` names a function
    // without calling it. *There is nothing left here for a catch-all to answer
    // silently.*
    fn in_expr(e: &Expr) -> bool {
        crate::alle_ausdruecke(e)
            .into_iter()
            .any(|x| matches!(x.art, ExprArt::Ruf(_)))
    }
    b.anweisungen.iter().any(|s| {
        matches!(s.art, StmtArt::Ruf(_) | StmtArt::LetSonst(_))
            || crate::eigene_ausdruecke(s).into_iter().any(in_expr)
            // **Das `until` einer `retry`-Schleife** -- genau die Stelle, an der dieses
            // Attribut am 2026-08-19 falsch gesetzt wurde und der Uebersetzer 65 Rufe strich.
            || crate::eigene_praedikate(s)
                .into_iter()
                .flat_map(crate::ausdruecke_im_praedikat)
                .any(in_expr)
            || crate::unterbloecke(s).into_iter().any(ruft_irgendwas)
    })
}

/// **Die Wirkungsliste IST eine Optimierungsangabe** («OPT2», 2026-08-19).
///
/// `effects` steht ohnehin da, ein Pass hält sie (`E008` kompositional über die Hülle,
/// `E010` für das Lesen), und C hat für genau diese Aussage zwei Wörter. Sie nicht
/// hinzuschreiben heisst, eine geprüfte Eigenschaft zu verschenken.
///
/// **Die zwei Wörter heissen dasselbe und bedeuten Verschiedenes**, und das ist die Falle:
///
/// | | GCC | Gabbro |
/// |---|---|---|
/// | `const` | liest **gar keinen** Speicher — auch nicht über einen Parameterzeiger | — |
/// | `pure` | darf Speicher lesen, ändert nichts | `reads`/`pure` |
///
/// Ein Gabbro-`pure` darf seine Parameter lesen, auch durch einen Zeiger. **`((const))` gibt
/// es deshalb nur für eine Funktion ganz ohne Zeigerparameter** — sonst wäre die Zusage
/// stärker als die geprüfte Aussage, und der C-Übersetzer dürfte einen Ruf löschen, dessen
/// Ergebnis vom Speicher abhängt.
///
/// **Und nur für Funktionen mit Rumpf, DIE NICHTS RUFEN.**
///
/// *Der erste Anlauf verlangte nur einen Rumpf, und der Wächter hat ihn am selben Tag
/// gefangen* (`pruefe-emission.sh`, Stufe 6): Fragment 10 zählte 65 Aufrufe von
/// `naechstes_token` bei `-O0` und **null** unter `-O1` — der Übersetzer strich die Rufe, weil
/// das Attribut sie für wirkungslos erklärte.
///
/// Der Grund ist tiefer als der eine Fall: `E008` prüft die Wirkungen eines Rumpfes gegen die
/// **deklarierten** Wirkungen der Gerufenen. Bei einem `extern fn` ist diese Deklaration eine
/// **Annahme über fremden Code** — der Korpus trägt 48 solcher Rümpfe. Ein Attribut ist aber
/// keine Buchung, sondern eine **Anweisung an den Übersetzer**, und eine Annahme in eine
/// Anweisung zu verwandeln ist genau die Bewegung, gegen die das Zeugnis steht.
///
/// > **Was nicht ruft, kann keinen fremden Rumpf unter sich haben.** Das ist die einzige
/// > Schranke, die ohne Hüllenrechnung hält — und sie trifft die Gestalt, in der `pure`
/// > überhaupt etwas bringt: den kleinen Leser.
fn wirkungsattribut(f: &FnDecl, u: &Namen) -> &'static str {
    // **Eine Funktion mit Fehlerkanal SCHREIBT durch `*_wert`** -- `const` verspricht dem
    // C-Uebersetzer das Gegenteil, und `pure` fast dasselbe. *Gemessen am 2026-08-20: mit
    // `__attribute__((const))` liess GCC den Speicherschritt weg, und der Rufer sah seinen
    // alten Wert.* Dieselbe Klasse wie `pure` an einem volatilen Leser, eine Zeile tiefer.
    if f.fehler.is_some() {
        return "";
    }
    let FnRumpf::Block(b) = &f.rumpf else {
        return "";
    };
    if ruft_irgendwas(b) {
        return "";
    }
    let Some(w) = &f.effects else {
        return wirkungsattribut_abgeleitet(f, b, u);
    };
    // Eine Funktion ohne Ergebnis hat nichts, was sich zusammenfassen liesse.
    //
    // **And `-> never` is such a function, which this line did not say until 2026-09-08.**
    // The guard read the WRITTEN result and `never` is one; the C it lowers to is
    // `_Noreturn void` (`ctyp_ergebnis`, `Some(TypExpr::Never(_)) => "_Noreturn void"`), and
    // GCC refuses `const`/`pure` on a function returning `void` outright:
    //
    // ```text
    // divergent fn q() -> never effects { pure }      -> __attribute__((const)) on void
    // divergent fn q() -> never effects { reads G }   -> __attribute__((pure))  on void
    //     cc -std=c11 -Wall -Wextra -Werror
    //     error: 'const' attribute on function returning 'void' [-Werror=attributes]
    // ```
    //
    // The control in the same run: a plain `fn q() effects { pure }` -- no result clause at
    // all -- got no attribute and compiled, which is this line working as written. *The
    // fault was a guard that asked the SOURCE a question about the C.*
    //
    // **Measured separately from `S009` on purpose.** It fires whether or not the body
    // returns (measured at a body whose only statement is a `forever` with no `leave`), so
    // it is a second finding and not a symptom of the first --
    // `messung/GRAMMATIK-VOLLSTAENDIG-2026-09-08.md` §1.3 booked the two together and said
    // it had not separated them.
    if f.ergebnis.is_none() || matches!(&f.ergebnis, Some(TypExpr::Never(_))) {
        return "";
    }
    let mut nur_lesend = true;
    let mut ganz_rein = true;
    for e in &w.liste {
        match &e.art {
            WirkungArt::Rein => {}
            // **Ein VOLATILES Lesen vertraegt weder `pure` noch `const`.**
            //
            // GCC erlaubt einer `pure`-Funktion, unveraenderliche globale Objekte zu lesen --
            // *nicht* volatile. Genau darauf beruht die Optimierung: zwei Rufe mit gleichen
            // Argumenten duerfen zu einem zusammenfallen. Bei einem Statusregister ist das
            // die Schleife, die nie endet, weil sie ihr Register nur einmal liest.
            //
            // *Dieselbe Klasse wie der `extern`-Fall im Kopf dieser Funktion, und derselbe
            // Ausgang: das Attribut ist eine ANWEISUNG an den Uebersetzer, keine Buchung.*
            WirkungArt::Liest(o) if liest_geraet(&o.basis.text, u, f) => return "",
            WirkungArt::Liest(_) => ganz_rein = false,
            // Alles andere -- Schreiben, Sperren, Verbrauchen, Veröffentlichen, Divergieren,
            // Maskieren, Belegen -- ist eine Wirkung, und dann gilt keins der zwei Wörter.
            //
            // **Written out one by one, because the catch-all made a promise about a list
            // that can grow.** `__attribute__((pure))` and `((const))` are INSTRUCTIONS to
            // the C compiler, not bookkeeping: a wrong one lets the optimiser fold away
            // calls that do something. A new `WirkungArt` falling in here silently would
            // therefore not be a missing entry in a table -- it would be permission to
            // delete the call. *That is the one direction in which this file must not
            // guess.*
            WirkungArt::Schreibt(_)
            | WirkungArt::Sperrt(_)
            | WirkungArt::SperrtGeteilt(_)
            | WirkungArt::Maskiert(_)
            | WirkungArt::Belegt(_)
            | WirkungArt::Verbraucht(_)
            | WirkungArt::Veroeffentlicht(_)
            | WirkungArt::Divergiert => {
                nur_lesend = false;
                ganz_rein = false;
            }
        }
    }
    attr_ende(f, nur_lesend, ganz_rein)
}

/// The shared tail of both attribute arms: nothing but reads (and no pointer
/// parameter) is `const`, reads only is `pure`. One tail, read twice — the
/// condition is the promise to the C compiler, and two spellings of it would
/// be two promises.
fn attr_ende(f: &FnDecl, nur_lesend: bool, ganz_rein: bool) -> &'static str {
    if !nur_lesend {
        return "";
    }
    let zeigt_irgendwohin = f
        .parameter
        .iter()
        .any(|p| matches!(&p.typ, TypExpr::Zeiger(_)));
    if ganz_rein && !zeigt_irgendwohin {
        " __attribute__((const))"
    } else {
        " __attribute__((pure))"
    }
}

/// **Lane 197: the attribute over an OMITTED clause.**
///
/// Lane 191 derives an omitted `effects` from the body and checks it like a
/// written one; the emitter kept reading the written word, so `fmt
/// --explicit`/`--elide` moved the C on every pure leaf. For a body that
/// calls nothing the derived set IS the deeds — no edges, no inheritance, no
/// lower bound — said by the same walker the fixpoint runs
/// (`rumpfwirkungen_mit_ort`, wide, like the checker). Anything the loop
/// below does not recognise keeps no attribute, as before; a body with a
/// call anywhere never reaches here (the caller returns earlier).
fn wirkungsattribut_abgeleitet(f: &FnDecl, b: &Block, u: &Namen) -> &'static str {
    let taten: Vec<String> = crate::wirkungen::rumpfwirkungen_mit_ort(
        f,
        b,
        &u.welt_konstanten,
        &u.welt_namen,
        true,
    )
    .into_keys()
    .collect();
    let mut nur_lesend = true;
    let mut ganz_rein = true;
    for s in &taten {
        let (verb, ort) = crate::wirkungen::trenne(s.as_str());
        match verb {
            "pure" => {}
            "reads" => {
                let basis = ort.split(['.', '[', '-']).next().unwrap_or(ort);
                if liest_geraet(basis, u, f) {
                    return "";
                }
                ganz_rein = false;
            }
            _ => {
                nur_lesend = false;
                ganz_rein = false;
            }
        }
    }
    attr_ende(f, nur_lesend, ganz_rein)
}

/// Nennt diese `reads`-Wirkung ein Geraet -- als Typname, als Parameter oder als Griff?
fn liest_geraet(basis: &str, u: &Namen, f: &FnDecl) -> bool {
    let n = basis;
    if u.geraete.contains_key(n) || u.geraetezeiger.contains_key(n) || u.geraetewerte.contains_key(n)
    {
        return true;
    }
    // Ein Parameter traegt seinen Geraetetyp in der Signatur, auch wenn die Karte des
    // aeusseren Namensraums ihn nicht kennt.
    f.parameter.iter().any(|p| {
        &p.name.text == n
            && match &p.typ {
                TypExpr::Pfad(pf) => pf
                    .teile
                    .last()
                    .is_some_and(|t| u.geraete.contains_key(&t.text)),
                TypExpr::Zeiger(z) => match &z.ziel {
                    TypExpr::Pfad(pf) => pf
                        .teile
                        .last()
                        .is_some_and(|t| u.geraete.contains_key(&t.text)),
                    _ => false,
                },
                _ => false,
            }
    })
}

/// **Text, der in einem C-Literal landet** — Anführungszeichen und Rückstriche entschärft.
///
/// Dieselbe Klasse wie `kommentartext`: eine Zeichenkette aus der Quelle geht ins Erzeugnis,
/// und ohne diese Zeile kann sie das Literal schliessen. *Ein `claim` hat genau das am
/// 2026-08-19 schon einmal getan.*
fn ctext(t: &str) -> String {
    t.replace('\\', "\\\\").replace('"', "\\\"")
}

/// **Der Assemblertext braucht eine ZWEITE Fluchtregel, und ohne sie faellt `cc`.**
///
/// Gemessen 2026-08-20 an `beispiele/36-asm.gab`: `"mov $1, %eax"` ging woertlich in einen
/// **erweiterten** `__asm__`-Block, und GCC sagte *„ungueltiges »asm«: Operandennummer fehlt
/// hinter %-Buchstabe"*. In erweitertem Assembler ist `%` das Einleitungszeichen fuer einen
/// Operanden; ein literales Prozent muss verdoppelt werden.
///
/// Stehen bleibt allein `%[`, denn das IST die Operandenform, die Gabbro schreibt.
///
/// > **Warum das hier besonders weh tut:** bei `asm` sagt die Sprache ausdruecklich, dass sie
/// > den Inhalt nicht liest. Damit ist der C-Uebersetzer die einzige Pruefung, die es
/// > ueberhaupt gibt -- und genau der wurde nicht gefragt, weil `pruefe-emission.sh` diese
/// > Datei nicht deckte. *Ein versiegeltes Loch, dessen einziger Waechter nicht hinsah.*
fn asmtext(t: &str) -> String {
    let roh = ctext(t);
    let mut aus = String::with_capacity(roh.len());
    let mut zs = roh.chars().peekable();
    while let Some(c) = zs.next() {
        if c == '%' && zs.peek() != Some(&'[') {
            aus.push_str("%%");
        } else {
            aus.push(c);
        }
    }
    aus
}

/// **`restrict` — und die Hypothesen stehen in `beweise/Restrict_Alleinzugriff.thy`.**
///
/// Gemessen 2026-08-19, `cc -O2`: **2,85** dort, wo der C-Übersetzer die Herkunft der Zeiger
/// nicht sieht, **1,00** dort, wo er sie sieht. Das ist der grösste Hebel des Erzeugers — und
/// der einzige, der etwas **kaputt** machen kann: eine falsche Alias-Zusicherung erzeugt
/// Code, der bei `-O0` stimmt und bei `-O2` nicht.
///
/// C11 6.7.3.1 sagt, was zugesichert wird: wird das Objekt X im Block B über den
/// `restrict`-Zeiger P erreicht, muss **jeder** Zugriff auf X in B über einen aus P
/// abgeleiteten Zeiger laufen.
///
/// Der Satz `restrict_gerechtfertigt` führt das auf zwei Hypothesen zurück, und diese
/// Funktion weist genau sie nach:
///
/// | | Hypothese | wer sie hält |
/// |---|---|---|
/// | **H1** | der Rahmen ist vollständig | `E008` (seit heute über den ORT) + `E010` |
/// | **H2a** | kein zweiter Zeigerparameter desselben Trägertyps | **hier**, syntaktisch |
/// | **H2b** | kein globaler Träger desselben Typs erreichbar | **die SPRACHE**: kein `cast` (G9), kein Adressoperator — ein Zeiger auf eine globale Tabelle lässt sich in Gabbro nicht bilden |
///
/// **Und was hier NICHT behauptet wird:** dass `own` Exklusivität bedeutet. Das ist eine
/// Sprachentscheidung; sie würde H2a auch für **zwei** Zeiger desselben Typs liefern — genau
/// den Fall, in dem die 2,85 gemessen wurden. Solange sie nicht getroffen ist, gilt die
/// stärkere, entscheidungsfreie Bedingung: *höchstens ein Zeigerparameter je Trägertyp.*
///
/// > Die Aussage, die dann bleibt, ist trotzdem keine leere: **der C-Übersetzer weiss nicht,
/// > dass eine globale Tabelle in Gabbro nicht adressierbar ist.** Für ihn können
/// > `Kappenraum *c` und das globale `Kappenraum`-Objekt dasselbe sein; für Gabbro nicht.
/// > *Das ist die Angabe, die C fehlt.*
fn darf_restrict(f: &FnDecl, p: &Parameter, u: &Namen) -> bool {
    // Ohne Rumpf gibt es keinen Block, über den die C-Bedingung überhaupt spricht — und die
    // `effects` eines `extern fn` sind eine Annahme über fremden Code, keine geprüfte Aussage.
    let FnRumpf::Block(_) = &f.rumpf else {
        return false;
    };
    let TypExpr::Zeiger(z) = &p.typ else {
        return false;
    };
    let Some(traeger) = zeigerziel(&z.ziel) else {
        return false;
    };
    // **H2a**, syntaktisch: kein zweiter Zeigerparameter mit demselben Träger.
    let andere = f.parameter.iter().filter(|q| q.name.text != p.name.text);
    for q in andere {
        if let TypExpr::Zeiger(zq) = &q.typ {
            if zeigerziel(&zq.ziel).as_deref() == Some(traeger.as_str()) {
                return false;
            }
        }
    }
    // **H2b**, doppelt genäht: nennt die eigene Wirkungsliste einen globalen Träger dieses
    // Namens, wird nichts behauptet. Die Sprache schliesst den Fall schon aus (kein `cast`,
    // kein Adressoperator) — *aber eine Hypothese, die man prüfen kann, prüft man.*
    if let Some(w) = &f.effects {
        for e in &w.liste {
            let t = e.art.text();
            if let Some((_, ort)) = t.rsplit_once(' ') {
                let grund = ort.split(['.', '[']).next().unwrap_or(ort);
                if grund == traeger && u.tabellen.iter().any(|n| n == &traeger) {
                    return false;
                }
            }
        }
    }
    true
}

/// Der Name des Trägers, auf den ein Zeiger zeigt.
fn zeigerziel(t: &TypExpr) -> Option<String> {
    match t {
        TypExpr::Pfad(p) => p.teile.last().map(|i| i.text.clone()),
        _ => None,
    }
}

/// **Die Sicht DIESER Funktion auf die Namen -- und der Grund dafuer ist ein Fehler, der
/// stilles falsches C erzeugt hat** (2026-08-20).
///
/// Der Erzeuger liest Namen ueber die ganze Uebersetzungseinheit: `werte`, `markenwerte`,
/// `tabellenzeiger`, `geraetezeiger`, `parametertyp` sind alle Karten **Name -> Auskunft**,
/// ohne die Funktion, in der der Name steht. Solange jeder Name in der Einheit dasselbe
/// bedeutet, geht das gut. `beispiele/08` tut das nicht:
///
/// ```gabbro
/// impl fn v3_auswerten(m : Nachricht) -> Zaehler          -- ein WERT
/// impl fn marke_weiterdrehen(m : ptr<normal, rw> Marken)  -- ein ZEIGER
/// ```
///
/// > Beide heissen `m`, und das ist voellig normal. Der Erzeuger trug `m` als Wert ein und
/// > schrieb daraufhin in der ZWEITEN Funktion `m.slots[s].marke += 1;` -- **einen Punkt, wo
/// > ein Pfeil hingehoert.**
///
/// **Konservativ zu werden reicht hier nicht.** Die drei bestehenden Karten fallen bei
/// Uneinigkeit lautstark aus (*„Unwissen faellt nach lautstark"*), aber `werte` hat kein
/// neutrales Fehlen: draussen zu sein heisst *Zeiger*, und das ist fuer `v3_auswerten` genau
/// so falsch wie das Gegenteil fuer `marke_weiterdrehen`. **Eine Karte, deren beide Zustaende
/// eine Behauptung sind, kann nicht schweigen.**
///
/// Also faellt die Entscheidung dort, wo sie hingehoert: **ein Parameter verdeckt jede
/// globale Ablesung seines Namens** und traegt seine eigene ein. Das ist keine Heuristik,
/// sondern die Bindungsregel der Sprache -- der Erzeuger holt nur nach, was jeder Pass vor
/// ihm laengst tut.
fn eigene_sicht(f: &FnDecl, u: &Namen) -> Namen {
    let mut lokal = u.clone();
    // **Which of this body's `let`s nobody reads back** -- the same walker the
    // `(void)k;` of an unread parameter uses, so the two answers cannot drift.
    lokal.ungelesene_lets.clear();
    if let FnRumpf::Block(b) = &f.rumpf {
        let mut gelesen = BTreeSet::new();
        benutzte_namen(b, &mut gelesen);
        let (mut lets, mut allocs, mut wieoft) = (Vec::new(), Vec::new(), HashMap::new());
        sammle_lets(b, &mut lets, &mut allocs, &mut wieoft);
        for l in lets {
            // A name bound TWICE is not decided here -- the same rule the ghost
            // fixpoint above follows, and for the same reason: two bindings under
            // one name are two questions, and this map answers one.
            if wieoft.get(&l.name.text) == Some(&1) && !gelesen.contains(&l.name.text) {
                lokal.ungelesene_lets.insert(l.name.text.clone());
            }
        }
        // **«E4»:** an unread arena index is silenced the same way -- the
        // binding lowers to `uint32_t i;` unconditionally, and `-Werror`
        // asks about it just the same.
        for name in allocs {
            if wieoft.get(&name) == Some(&1) && !gelesen.contains(&name) {
                lokal.ungelesene_lets.insert(name);
            }
        }
    }
    // **The parameter map is scoped to this function before its own entries
    // go in.** The collected map is unit-wide by construction (see the
    // collection: a name bound anywhere stays unless two functions disagree on
    // its type) -- so without this line a body reads ANOTHER function's
    // parameter type for its own same-named `let`. Measured 2026-09-11:
    // `messung/netz/udp-echo.gab` binds `let a : u32` in a function whose unit
    // also declares `a : ptr ArpTabelle` elsewhere, and `wert_ctyp` answered
    // the pointer -- which fired the pointer-arithmetic refusal below on
    // integer arithmetic, reverted the same day. The per-name removals that
    // follow are not enough: they hide this function's names, while the leak
    // is every OTHER function's.
    lokal.parametertyp.clear();
    for p in &f.parameter {
        let name = &p.name.text;
        // **Erst loeschen, dann eintragen.** Was diese Funktion selbst bindet, kommt aus
        // ihrer eigenen Deklaration und aus keiner anderen.
        lokal.werte.remove(name);
        lokal.markenwerte.remove(name);
        lokal.tabellenzeiger.remove(name);
        lokal.geraetezeiger.remove(name);
        lokal.geraetewerte.remove(name);
        lokal.formatwerte.remove(name);
        lokal.parametertyp.insert(name.clone(), p.typ.clone());
        match &p.typ {
            TypExpr::Pfad(pf) => {
                if let Some(n) = pf.teile.last() {
                    if u.verbunde.contains(&n.text) {
                        lokal.werte.insert(name.clone());
                    }
                    if u.markierte.contains_key(&n.text) {
                        lokal.werte.insert(name.clone());
                        lokal.markenwerte.insert(name.clone(), n.text.clone());
                    }
                    if u.formate.contains(&n.text) {
                        lokal.formatwerte.insert(name.clone(), n.text.clone());
                    }
                    // Eine Marke ist ein WERT: ein Byte, das durch die Signatur reist.
                    if u.marken.contains(&n.text) {
                        lokal.werte.insert(name.clone());
                    }
                    // **Ein GERAET als Wertparameter -- die Form, die `beispiele/09` lokal
                    // schreibt (`let v = Vtd(basis);`) und dann weiterreicht.**
                    //
                    // Bis 2026-08-20 stand sie in KEINER der beiden Karten, und damit nahm
                    // der Erzeuger den gewoehnlichen Ortspfad: `d.ST.IDX` wurde `d->ST.IDX`
                    // -- ein Feldzugriff auf `typedef struct { volatile uint8_t *basis; }`,
                    // den es nicht gibt. **`cc` brach ab, `gabbro emit` gab 0 zurueck, und
                    // `C001` schwieg.** *Eine stille falsche Absenkung ist schlechter als
                    // eine Absage, denn eine Absage steht im Zeugnis.*
                    //
                    // `gabbro blindstellen` fuehrte `device` in Stellung `parameter` als
                    // BLIND -- die Zelle sagte es voraus, bevor sie jemand nachgerechnet hat.
                    if u.geraete.contains_key(&n.text) {
                        lokal.geraetewerte.insert(name.clone(), n.text.clone());
                        lokal.werte.insert(name.clone());
                    }
                }
            }
            TypExpr::Zeiger(z) => {
                if let TypExpr::Pfad(pf) = &z.ziel {
                    if let Some(n) = pf.teile.last() {
                        if u.tabellen.iter().any(|t| *t == n.text) {
                            lokal.tabellenzeiger.insert(name.clone(), n.text.clone());
                        }
                        if u.geraete.contains_key(&n.text) {
                            lokal.geraetezeiger.insert(name.clone(), n.text.clone());
                        }
                        if u.formate.contains(&n.text) {
                            lokal.formatwerte.insert(name.clone(), n.text.clone());
                        }
                    }
                }
            }
            // **Die Parametertypen, die keinen EINTRAG in die lokale Sicht verdienen -- und
            // der Grund je Form, weil die Karte davor schon einmal still leer war.**
            //
            // Eine Zahl, ein Gleitkommawert, ein `bool`, ein `never`, ein `index into T`
            // und ein Funktionszeiger sind SKALARE: sie tragen keinen `.`-Zugriff und keinen
            // `->`, und die Absenkung eines Ortes darueber ist der gewoehnliche Fall.
            //
            // *Zwei sind es nur beinahe:* ein `[T; N]` als Parameter und ein anonymer
            // Verbund oder eine anonyme Variantenliste in der Signatur. Sie sind keine
            // Karteneintraege, sondern **Formen ohne Absenkung** -- `ctyp` lehnt sie beim
            // Namen ab, und ein Eintrag hier wuerde einen Zugriff erlauben, dessen Typ nie
            // im Erzeugnis steht. Sie stehen darum hier und werden dort abgewiesen, nicht
            // umgekehrt.
            //
            // Lane 256: a `string max N` parameter likewise earns no local-view
            // entry -- a string carries no `.`-access and no `->`, and its
            // lowering is refused by name elsewhere. (Forced by exhaustiveness
            // over `TypExpr`; no existing behaviour changes.)
            TypExpr::Int(_)
            | TypExpr::Float(_)
            | TypExpr::Bool(_)
            | TypExpr::Never(_)
            | TypExpr::Index { .. }
            | TypExpr::Zeichenkette { .. }
            | TypExpr::FnZeiger(_)
            | TypExpr::Feld(_)
            | TypExpr::Verbund(_, _)
            | TypExpr::Varianten(_, _) => {}
        }
    }
    // **Und die `let`-gebundenen Geraetegriffe** -- `let v = Vtd(basis);`. Sie sind WERTE,
    // und der Ruf eines `transition` darauf nimmt ihre Adresse.
    //
    // > **And the name has to LEAVE `geraetezeiger`, which it did not until 2026-09-02.**
    // > That map is global and conservative by TYPE: it drops a name only when two functions
    // > declare it at two DIFFERENT device types. So a unit with
    // >
    // >     impl fn stand(c : ptr<mmio, rw> Com1) -> u8 { … }
    // >     impl fn baut()  { let c = Com1(0x3f8); c.THR = b; }
    // >
    // > left `c -> Com1` standing in `geraetezeiger`, and `ort` asks that map FIRST -- so the
    // > value `c` lowered to `c->basis` and `cc` said *`invalid type argument of '->'`*.
    // > Checker silent, emitter exit 0, and the C does not build. **Measured at `178e260` on
    // > an `at mmio` device**, so it is not new and it is not about the port space; the port
    // > lowering only makes it louder, because there the same name goes into an accessor call
    // > where `&c` was owed.
    // >
    // > *The parameter loop above already had the rule and says it in one line -- delete
    // > first, insert second -- and this loop only did the second half.* The removal is
    // > held back for a name this function also DECLARES as a parameter: two bindings under
    // > one name are two questions, and this map answers one (the sentence the ghost fixpoint
    // > above uses for the same case).
    if let FnRumpf::Block(b) = &f.rumpf {
        fn im_block(b: &Block, u: &Namen, lokal: &mut Namen, parameter: &BTreeSet<String>) {
            for s in &b.anweisungen {
                if let StmtArt::Let(l) = &s.art {
                    if let ExprArt::Ruf(r) = &l.wert.art {
                        let Some(n) = r.path().map(|p| p.text()) else { continue };
                        if u.geraete.contains_key(&n) {
                            if !parameter.contains(&l.name.text) {
                                lokal.geraetezeiger.remove(&l.name.text);
                            }
                            lokal.geraetewerte.insert(l.name.text.clone(), n);
                            lokal.werte.insert(l.name.text.clone());
                        }
                    }
                }
                for k in crate::unterbloecke(s) {
                    im_block(k, u, lokal, parameter);
                }
            }
        }
        let eigene: BTreeSet<String> =
            f.parameter.iter().map(|p| p.name.text.clone()).collect();
        let mut gefunden = lokal.clone();
        im_block(b, u, &mut gefunden, &eigene);
        lokal = gefunden;
        lokale_lets(b, &mut lokal);
        // **Lane 167: every value this function binds, for the bare-case question.**
        // Parameters first -- a parameter shadows any unit-wide reading of its name,
        // the same rule the loop above follows for the device maps.
        for p in &f.parameter {
            lokal.schatten.insert(p.name.text.clone());
        }
        gebundene_namen(b, &mut lokal.schatten);
    }
    lokal
}

/// **The C type of every `let`-bound local this body declares -- to a FIXPOINT** (2026-08-25).
///
/// `eigene_sicht` above answers for parameters, for device handles and for record values. A
/// name bound by `let` had no answer, and the emitter said `C001 let without a resolvable
/// type` at a site where the type stood in a declaration two lines up:
///
/// ```gabbro
/// let frei    = unberuehrt(s);      -- `-> u64` in the callee's signature
/// let benutzt = s.len - frei;       -- refused: `frei` was unknown
/// ```
///
/// **The fixpoint is not a flourish, it is the chain.** `benutzt` is resolvable only once
/// `frei` is, so one pass answers half the question and looks as though it answered all of it.
/// The loop is bounded by the number of `let`s: each round either adds one name or stops.
///
/// > **A name bound TWICE in one body is dropped, not decided.** Two `let`s of the same name
/// > in sibling branches may carry different types, and this map has no scopes -- *unknown
/// > falls loud*, which is the rule `geraetezeiger` and `vorzeichenlos` already follow. The
/// > cost is a refusal where an answer existed; the alternative is a wrong C type, and W9 does
/// > not license a coarsening where the exact answer is unavailable.
///
/// A ghost `let` is skipped: its binding does not reach the C at all, and an entry here would
/// claim a type for a name the product never spells. **Its NAME still goes on record**, into
/// `geistlokal` -- the skip loses the type, and the question `geist_wert` asks later survives
/// it (2026-08-30).
/// Every `let` of a body and how often each NAME is bound. **Pulled out of `lokale_lets`
/// on 2026-08-31** so `eigene_sicht` can ask the same question -- a second copy of it would
/// be the drift this file already records once.
///
/// **«E4»:** `alloc` bindings ride along in `allocs`, counted in the same
/// `wieoft` -- a name bound by both a `let` and an `alloc` is bound twice,
/// and the fixpoint drops it like any other double binding. The index type
/// needs no fixpoint (it is always `uint32_t`), so only the name travels.
fn sammle_lets<'a>(
    b: &'a Block,
    aus: &mut Vec<&'a LetStmt>,
    allocs: &mut Vec<String>,
    wieoft: &mut HashMap<String, u32>,
) {
    for s in &b.anweisungen {
        if let StmtArt::Let(l) = &s.art {
            *wieoft.entry(l.name.text.clone()).or_insert(0) += 1;
            aus.push(l);
        }
        if let StmtArt::Alloc(a) = &s.art {
            *wieoft.entry(a.name.text.clone()).or_insert(0) += 1;
            allocs.push(a.name.text.clone());
        }
        for k in crate::unterbloecke(s) {
            sammle_lets(k, aus, allocs, wieoft);
        }
    }
}

/// **Every name a block binds as a value (lane 167)** -- `let`, `let … else` (plus
/// the error name), `match` binders, `traverse` variables, `alloc` indices, `awaits`
/// and `exchange` bindings. Read through `unterbloecke`, so a binding in a nested
/// block counts: the set has no scopes, and a name bound anywhere withholds the
/// bare-case literal everywhere in the function. Where the checker still types the
/// bare name as the case (bound in one arm, read in another), the product names an
/// undeclared identifier and `cc` says so -- loud, and booked in the sentence.
/// Loop labels (`retry`/`forever` marks) bind no value and stay out: they lower to
/// `marke_weiter`-style C labels, which share nothing with a case literal.
fn gebundene_namen(b: &Block, aus: &mut BTreeSet<String>) {
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Let(l) => {
                aus.insert(l.name.text.clone());
            }
            StmtArt::LetSonst(l) => {
                aus.insert(l.name.text.clone());
                aus.insert(l.fehlername.text.clone());
            }
            StmtArt::Match(m) => {
                for z in &m.zweige {
                    if let Some(binder) = &z.binder {
                        aus.insert(binder.text.clone());
                    }
                }
            }
            StmtArt::Schleife(sch) => {
                if let Schleife::Traverse(x) = sch.as_ref() {
                    aus.insert(x.variable.text.clone());
                }
            }
            StmtArt::Alloc(a) => {
                aus.insert(a.name.text.clone());
            }
            StmtArt::AwaitLoad(a) => {
                aus.insert(a.name.text.clone());
            }
            StmtArt::Exchange(e) => {
                aus.insert(e.name.text.clone());
            }
            _ => {}
        }
        for k in crate::unterbloecke(s) {
            gebundene_namen(k, aus);
        }
    }
}

fn lokale_lets(b: &Block, lokal: &mut Namen) {
    let (mut lets, mut wieoft) = (Vec::new(), HashMap::new());
    // `alloc` names count into `wieoft` (a double-bound name is dropped),
    // but their types need no fixpoint -- always `uint32_t`.
    sammle_lets(b, &mut lets, &mut Vec::new(), &mut wieoft);
    loop {
        let mut neu: Vec<(String, String)> = Vec::new();
        let mut neu_tx: Vec<(String, TypExpr)> = Vec::new();
        let mut neu_geist: Vec<String> = Vec::new();
        for l in &lets {
            let name = &l.name.text;
            // **A ghost `let` puts its NAME on record and nothing else** (2026-08-30). Both
            // maps below skip it on purpose; the question *was this name a ghost?* outlives
            // that skip, and `geist_wert` asks it at every later mention.
            //
            // *Inside the fixpoint, so that a CHAIN resolves.* `let a = f(); let b = a;`
            // makes `b` a ghost once `a` stands here, so one round per link. The entry rule
            // matches the one below: a name bound twice in a body gets dropped, never
            // decided.
            if wieoft.get(name) == Some(&1)
                && !lokal.geistlokal.contains(name)
                && geist_wert(&l.wert, lokal)
            {
                neu_geist.push(name.clone());
            }
            if wieoft.get(name) != Some(&1)
                || lokal.parametertyp.contains_key(name)
                || (lokal.lokaltyp.contains_key(name) && lokal.lokaltypexpr.contains_key(name))
                || geist_wert(&l.wert, lokal)
            {
                continue;
            }
            // Exactly the two sources `StmtArt::Let` itself reads, and in the same order --
            // **two registers over one thing would be W7**, and the one that decides here must
            // be the one that emits there.
            let c = match l.typ.as_ref().and_then(|t| ctyp(t, lokal)) {
                Some(c) => Some(c),
                None if l.typ.is_none() => wert_ctyp(&l.wert, lokal),
                None => None,
            };
            // **The declaration alongside the C type** (2026-08-26). Two sources, and both
            // are declarations: the annotation on the `let` itself, or the declared result
            // of the callee. *Nothing is inferred from a value here* -- an unknown falls
            // out, and then `ort_typ` answers `None` and the emitter refuses by name.
            let tx = match &l.typ {
                Some(t) => Some(t.clone()),
                None => match &l.wert.art {
                    ExprArt::Ruf(r) => r
                        .path()
                        .and_then(|p| p.teile.last())
                        .and_then(|i| lokal.ergebnistyp.get(&i.text).cloned()),
                    _ => None,
                },
            };
            // **Je Karte nur, was ihr noch fehlt** -- sonst traegt der Fixpunkt denselben
            // Eintrag in jedem Durchgang nach und die Schleife endet nie. *Gemessen: sie
            // endete nicht.*
            if let Some(t) = tx {
                if !lokal.lokaltypexpr.contains_key(name) {
                    neu_tx.push((name.clone(), t));
                }
            }
            if let Some(c) = c {
                if !lokal.lokaltyp.contains_key(name) {
                    neu.push((name.clone(), c));
                }
            }
        }
        // **The third collection counts toward the end of the loop too.** Leaving it out
        // would stop the fixpoint one round early whenever a round found a ghost name alone.
        if neu.is_empty() && neu_tx.is_empty() && neu_geist.is_empty() {
            return;
        }
        for n in neu_geist {
            lokal.geistlokal.insert(n);
        }
        for (n, t) in neu_tx {
            lokal.lokaltypexpr.insert(n, t);
        }
        for (n, c) in neu {
            lokal.lokaltyp.insert(n, c);
        }
    }
}

/// **C's own declaration, with this `extern fn`'s parameter names in it.**
///
/// Reads `cnamen.rs::Signatur::absenkung` -- `int64_t(int32_t,const void *,uint64_t)` -- and
/// pairs each type with the name the writer chose. `None` when the arity does not match,
/// which cannot happen behind `N046` and is refused here rather than trusted: *a table and a
/// declaration that disagree about how many parameters there are is the one case where
/// writing the table's answer would be writing over the writer's.*
fn aus_ctafel(sig: &crate::cnamen::Signatur, f: &FnDecl) -> Option<(String, String)> {
    let i = sig.absenkung.find('(')?;
    let rueck = sig.absenkung[..i].to_string();
    let inner = sig.absenkung[i + 1..].strip_suffix(')')?;
    let typen: Vec<&str> = if inner == "void" {
        Vec::new()
    } else {
        inner.split(',').collect()
    };
    if typen.len() != f.parameter.len() {
        return None;
    }
    let liste = if typen.is_empty() {
        "void".to_string()
    } else {
        typen
            .iter()
            .zip(&f.parameter)
            .map(|(t, p)| {
                let luecke = if t.ends_with('*') { "" } else { " " };
                format!("{t}{luecke}{}", p.name.text)
            })
            .collect::<Vec<_>>()
            .join(", ")
    };
    Some((rueck, liste))
}

/// **The lowered CORE of a prototype: the return type and the parameter list.**
///
/// Split out on 2026-08-31 so that the same declaration is lowered by the same code twice --
/// once where it is written into the output, and once to answer the question *"does this
/// unit already declare that name, and does it declare the SAME thing?"* (see `funktion`).
/// *Two spellings of one lowering would be the second register W7 warns about; here the
/// second reader would silently disagree with the first at exactly the corner cases.*
///
/// `Err` carries the span and the word for the refusal instead of raising it: the pre-pass
/// asks the question without speaking, and only the emitting call reports.
fn prototyp_kern(
    f: &FnDecl,
    u: &Namen,
) -> Result<(String, String), (gabbro_syntax::span::Span, &'static str)> {
    let eigen = eigene_sicht(f, u);
    let u = &eigen;
    // **For a name C already declares, the generated unit writes C's declaration** (2026-09-02).
    //
    // The construct's whole meaning is *"this name already has a declaration over there"*, so
    // the prototype belongs to C and not to this lowering. `N046` has held the two against
    // each other since 2026-09-01 -- **for every `extern fn` that gets this far they are the
    // same string**, and the table's own counter-probe compiled all 149 of them. *This is
    // therefore a no-op for every program that compiled yesterday.*
    //
    // What it is NOT a no-op for is the one row where C is less specific than Gabbro: a
    // `void *` parameter. `extern fn write(fd : i32, p : ptr<normal, r> Text, n : u64)` says
    // `Text` and means it -- and C's declaration says `const void *`, which is what has to
    // stand in the unit or `cc` disagrees with the real `write` the moment a POSIX header is
    // in the same translation unit. *The call passes a `const Text *` into it, and that
    // conversion is C's own and implicit.*
    if f.klasse == Some(FnKlasse::Extern) {
        if let Some(sig) = crate::cnamen::signatur(&f.name.text) {
            if sig.bindbar() {
                if let Some(k) = aus_ctafel(&sig, f) {
                    return Ok(k);
                }
            }
        }
    }
    // **The ghost return becomes `void` — not a lowering but an ERASURE.** `mmu_an` hands the
    // boot token on; the token is the checker's argument and nothing the machine can hold.
    let rueck = match &f.ergebnis {
        Some(t) if ist_geist(t, u) => "void".into(),
        // **`-> never` heisst `_Noreturn void`.** Ohne das Wort sieht der C-Uebersetzer die
        // Fehlerzweige als durchfallend an -- genau der Grund, aus dem `S002` im Gabbro sechs
        // Mal ansprang, bevor `exit()` sein `-> never` bekam (`FRAGMENTE.md` F5).
        Some(TypExpr::Never(_)) => "_Noreturn void".into(),
        Some(t) => match ctyp(t, u) {
            Some(c) => c,
            None => return Err((f.name.span, "return type")),
        },
        None => "void".into(),
    };
    // Der Fehlerkanal nimmt den Rueckgabeplatz ein; das Ergebnis geht durch `_wert`.
    let rueck = if f.fehler.is_some() { "bool".to_string() } else { rueck };
    let mut params = Vec::new();
    for p in &f.parameter {
        if ist_geist(&p.typ, u) {
            continue; // erased -- see above
        }
        match ctyp(&p.typ, u) {
            Some(c) => {
                let luecke = if c.ends_with('*') { "" } else { " " };
                let r = if darf_restrict(f, p, u) { "restrict " } else { "" };
                params.push(format!("{c}{luecke}{r}{}", p.name.text))
            }
            None => return Err((p.name.span, "parameter type")),
        }
    }
    // **`-> T or R` -- der Fehlerkanal, und er aendert die C-Signatur** (2026-08-20).
    //
    // ```c
    // bool hol(uint32_t *_wert, HolFehler *_grund);
    // ```
    //
    // Drei Entscheidungen stecken darin, und alle drei sind hier begruendet und nicht bequem:
    //
    // 1. **Der Erfolg ist der Rueckgabewert, nicht der Wert.** Ein Sonderwert im Ergebnis
    //    haette den Typ verengt (`u32` haette einen Wert weniger), und `option index into T`
    //    macht genau das schon -- **zweimal dieselbe Sache auf zwei Arten ist W7.**
    // 2. **Der GRUND geht durch einen eigenen Ausgang und nicht durch den Rueckgabewert.**
    //    `reason`-Werte sind vom Menschen vergeben (`SPRACHE.md` fuehrt `Keiner = 0` als
    //    Beispiel), also gibt es kein freies Wort fuer *„kein Fehler"* -- eines zu
    //    reservieren hiesse, jede bestehende `reason`-Deklaration nachtraeglich zu
    //    beschraenken.
    // 3. **`bool` und nicht `int`.** Es gibt genau zwei Ausgaenge, und mehr sagt die
    //    Grammatik nicht.
    //
    // > *Und ein Ruf ausserhalb eines `let … else` ist damit ein Ruf mit der falschen
    // > Stelligkeit* -- `N029` faengt ihn im Pruefer, der Erzeuger noch einmal.
    if let Some(r) = &f.fehler {
        if let Some(t) = &f.ergebnis {
            match ctyp(t, u) {
                Some(c) => params.push(format!("{c} *_wert")),
                None => return Err((f.name.span, "return type")),
            }
        }
        params.push(format!("{} *_grund", r.text));
    }
    let liste = if params.is_empty() {
        "void".to_string()
    } else {
        params.join(", ")
    };
    Ok((rueck, liste))
}

/// **One name, one prototype** (2026-08-31) -- the names this unit DEFINES itself, each with
/// the core its definition lowers to.
///
/// See the refusal in `funktion`: a bodiless declaration of a name this unit defines is not
/// a foreign body, and its prototype is a second declaration of the same C function. Where
/// the two lowerings agree the second one is dropped; where they disagree the emitter
/// refuses. **The map is built BEFORE the emitting pass** because a Gabbro file's order is
/// free -- the `extern fn` may stand before the definition, and it does in
/// `beispiele/29-undurchsichtig.gab` the other way round.
fn eigene_ruempfe(
    baum: &Programm,
    u: &Namen,
) -> std::collections::BTreeMap<String, (String, String)> {
    let mut m = std::collections::BTreeMap::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Funktion(f) = &item.art {
            if matches!(f.klasse, Some(FnKlasse::Spec)) {
                return;
            }
            if !matches!(f.rumpf, FnRumpf::Block(_) | FnRumpf::Asm(_)) {
                return;
            }
            if let Ok(k) = prototyp_kern(f, u) {
                m.insert(f.name.text.clone(), k);
            }
        }
    });
    m
}

fn funktion(
    f: &FnDecl,
    aus: &mut String,
    rumpf_aus: &mut String,
    u: &Namen,
    eigene: &std::collections::BTreeMap<String, (String, String)>,
    absagen: &mut Absagen,
) {
    if matches!(f.klasse, Some(FnKlasse::Spec)) {
        return;
    }
    // **`ptr<port, …>` in a body: refused, because there is no lowering and there cannot be
    // one** (2026-08-31, `messung/ADRESSRAEUME.md`).
    //
    // `ctyp` read `z.raum` for NO space -- measured 2026-08-31: six functions differing in
    // nothing but the space word emit six byte-identical lines. For five of the six that was
    // held to be right: `normal` is ordinary memory, `boot` is ordinary memory in a link-time
    // section (`SYNTAX.md`:1607), `code` is never dereferenced (an incomplete type behind an
    // `extern fn`), and `mmio`/`dma` were said to be carried by the CHECKER (`R001`, `R008`,
    // and the W9 clause in `m3.rs`:22).
    //
    // > **TWO OF THE FIVE FELL ON 2026-09-15, and they fell on `R008`'s own sentence.** That
    // > refusal says of itself *"`mmio` is volatile and device-mapped, `normal` is not, and
    // > the emitter lowers them differently"* -- a claim the six byte-identical files above
    // > contradict. `ctyp` now reads the space through `raumqualifizierer`: `mmio` and `dma`
    // > earn `volatile`, the other four earn nothing, and each of the six carries its reason
    // > there. *The paragraph stays because the `port` half of it is untouched -- and because
    // > a measurement that later stopped holding is worth more standing next to what replaced
    // > it than deleted.*
    //
    // **`port` is the sixth, and it is wrong under a written promise.** `SPRACHE.md`:2188:
    // *"`at port` lowers accesses to `in`/`out` instead of to volatile loads/stores"*. What
    // the generator writes is a load. On x86_64 the port space is reached by `in`/`out` and
    // by nothing else, so the emitted access reads a different thing at a different address.
    //
    // **And the missing lowering is not missing work -- there is nothing to write.** `in` and
    // `out` take a PORT NUMBER; a field of a struct at an offset behind a pointer is not one.
    // *Building `in`/`out` for a `device … at port` would be a construct without a measured
    // need: the corpus holds zero `at port` devices* (34 `mmio`, 5 `dma`, and `at normal` is
    // already refused above). Rule A says no; the honest outcome is the named refusal.
    //
    // **What it costs, measured before it was built:** two sites in 426 files
    // (`messung/grammatik/geraeteworte.gab`, `messung/grammatik/raumworte.gab`), both of them
    // dereferencing a plain struct field through a port pointer -- *both the defect itself.*
    // Their repair is one word: the body moves to a foreign one, and the promise `port` makes
    // stays where it can be kept.
    //
    // **It holds at the SIGNATURE, not at the access** (W10). A body that takes a port
    // pointer and never touches it is refused too. That is coarser than the defect and it is
    // coarse in the safe direction; over the corpus the two sites both dereference, and a
    // rule that walked the body would need the pointer's space at every access site, which
    // the expression lowering does not carry.
    //
    // > **NARROWED 2026-09-02, and by exactly the sentence that set it.** The refusal named
    // > its own condition -- *"until a `device … at port` exists to lower"* -- and one now
    // > does. A port pointer AT a port device is the form that carries a port number: the
    // > device declaration says which, and `portzugriff` writes the instruction. Everything
    // > else keeps the refusal word for word, because for it nothing has changed: a plain
    // > record field at an offset behind a port pointer is still not a port number, and
    // > **there is still no lowering being withheld -- there is none.**
    if matches!(f.rumpf, FnRumpf::Block(_) | FnRumpf::Asm(_)) {
        for p in &f.parameter {
            if let TypExpr::Zeiger(z) = &p.typ {
                if z.raum == Raum::Port && !ist_portgeraet(&z.ziel, u) {
                    weigere(
                        absagen,
                        p.name.span,
                        "a body that carries a `ptr<port, …>` at something that is not a \
                         `device … at port` -- the port space is reached by `in`/`out` and \
                         not by a load, and this generator writes a load. There is no \
                         lowering to write either: `in`/`out` take a PORT NUMBER, and a \
                         struct field at an offset behind a pointer is not one. A `device … \
                         at port` names the port number and lowers; nothing else in the \
                         language does",
                    );
                    return;
                }
                // **`own@m` -- the owner MARK, and nothing in this tree reads it**
                // (2026-09-15).
                //
                // `parse::right` builds `Recht::Eigen(Some(marke))`, and that is the last
                // line in the whole repository that looks inside the `Some`. Measured:
                // `grep -rn "Eigen(Some" crates/` names the parser and nobody else; every
                // other reader -- `m3.rs` twice, `alias.rs`, `lean_g.rs` twice, this file --
                // matches `Recht::Eigen(_)` and drops the mark. `ptr<normal, own@m> u32` and
                // `ptr<normal, own> u32` emit the same C to the byte, book the same
                // obligations, and draw the same refusals: none.
                //
                // **`Ty.ptr` in `grammatik/Grammatik/Syntax.lean` carries `(t : Nat)` and
                // `(rw : Bool)` and nothing else**, so the mark has no constructor in the
                // specification either. It is a form the grammar admits and no side of the
                // compiler answers for -- a promise nobody keeps, which looks kept.
                //
                // **The refusal and not the lowering, and Rule A says why:** the mark would
                // mean *"the target is owned, and the owning mark is `m`"*, which is a
                // statement about linearity that the checker would have to hold at every
                // call. The corpus asks for it ZERO times (`grep -rn "own@" --include=*.gab`
                // is empty). Building the pass would be a construct without a measured need;
                // saying so by name costs nothing and stops the silence.
                //
                // **At the SIGNATURE, like the `port` refusal above, and for the same
                // reason** (`W10`): a body that takes the pointer and never touches it is
                // refused too. That is coarser than the defect and coarse in the safe
                // direction -- the exact rule would need the mark at every access site,
                // which the expression lowering does not carry.
                if let Some(marke) = z.rechte.iter().find_map(|r| match r {
                    Recht::Eigen(Some(m)) => Some(m),
                    _ => None,
                }) {
                    weigere(
                        absagen,
                        p.name.span,
                        &format!(
                            "`own@{}` -- the owner mark is parsed and READ BY NOTHING: every \
                             pass matches `own` and drops the mark, `ptr<…, own@{}>` emits \
                             the same C as `ptr<…, own>` to the byte, and `Ty.ptr` of the \
                             grammar carries no mark at all. Write `own` and name the owner \
                             where the language does hold it -- `effects {{ consumes {} }}`",
                            marke.text, marke.text, marke.text
                        ),
                    );
                    return;
                }
            }
        }
    }
    let (rueck, liste) = match prototyp_kern(f, u) {
        Ok(k) => k,
        Err((span, was)) => {
            weigere(absagen, span, was);
            return;
        }
    };
    let eigen = eigene_sicht(f, u);
    let u = &eigen;
    // **Without `pub` the binding is INTERNAL -- since 2026-08-25** (the ABI work).
    //
    // Until then this file knew the word `pub` nowhere: **zero occurrences in 6 976 lines.**
    // An `impl fn byte_senden` without a visibility word appeared in the C as
    // `void byte_senden(...)` -- a symbol with EXTERNAL binding, and with it the whole
    // private interior of a library lay on the linker's table.
    //
    // > *The module boundary was a statement of the checker and none of the product.*
    // > `N025`, which is caught by `namen.rs`, rejected a call from outside; whoever instead
    // > put a C program beside it and declared `byte_senden` got the function -- and no line
    // > of Gabbro knew about it.
    //
    // **`static` applies only where this unit also DEFINES.** A prototype without a body
    // points at a foreign body; giving it internal binding would send the linker to a
    // definition that is not here -- `cc` says *"used but never defined"* to that, and it
    // would be right.
    let definiert = matches!(f.rumpf, FnRumpf::Block(_) | FnRumpf::Asm(_));
    // **ONE name, ONE prototype -- and the one that stands is the DEFINITION's** (2026-08-31).
    //
    // `beispiele/29-undurchsichtig.gab` names `pa_aus_zahl` twice: as `pub impl fn … effects
    // { pure }` in the declaring module and as `extern fn … effects { pure }` in the using
    // one. **The doubling comes from the PROGRAM** -- that is the whole point of the file, a
    // module boundary drawn inside one unit. **The diverging attributes came from HERE:**
    //
    // ```c
    // uint64_t pa_aus_zahl(uint64_t z) __attribute__((const));   /* from the `impl fn`   */
    // uint64_t pa_aus_zahl(uint64_t z);                          /* from the `extern fn` */
    // ```
    //
    // *Two declarations of one C function carrying different promises to the compiler are a
    // statement that contradicts itself.* `-Wredundant-decls` names it; `-Wall -Wextra` does
    // not. The second one is dropped: the first already declares the name, with the type it
    // has and with the attribute the body earned.
    //
    // **And the attribute is NOT given to the `extern` half instead**, which would be the
    // other way to make the two agree. `wirkungsattribut` gives its reason two hundred lines
    // up: at an `extern fn` the effects clause is an ASSUMPTION about foreign code, and an
    // attribute is an INSTRUCTION to the compiler. Turning the one into the other is the
    // move the certificate stands against. *Here the body is not foreign at all -- it stands
    // in the same unit -- so the assumption has nothing left to say.*
    //
    // > **Where the two lowerings DISAGREE, nothing is dropped and the emitter refuses.**
    //   Measured on 2026-08-31: `impl fn f(z : u64) -> u64` beside `extern fn f(z : u32) ->
    //   u32` passes `gabbro pruefe` with **0 errors**, and the C is rejected by `cc`
    //   (*"conflicting types for 'f'"*). Silently dropping the second declaration would take
    //   that error away and leave a call lowered against the wrong width -- *the refusal is
    //   what makes the dropping safe, and it is not a separate feature.*
    if !definiert {
        if let Some(kern) = eigene.get(&f.name.text) {
            if *kern == (rueck.clone(), liste.clone()) {
                return;
            }
            weigere(
                absagen,
                f.name.span,
                "a bodiless declaration of a name this unit DEFINES, and the two disagree -- \
                 one C function cannot have two prototypes with different types. The body is \
                 not foreign: it stands in this same unit",
            );
            return;
        }
    }
    let intern = if !f.oeffentlich && definiert { "static " } else { "" };
    // **`unused` -- the same treatment as at the `static` of a world state and at the
    // `(void)k;` of an unread parameter, and for the same reason.**
    //
    // A `static` function nobody calls in THIS unit falls at `-Wunused-function`, and
    // `pruefe-emission.sh` compiles with `-Werror`. *The finding would be about the product
    // and not about the user:* whether a private function goes uncalled is a Gabbro
    // question, and the emitter is not the place that asks it.
    let ungenutzt = if intern.is_empty() {
        ""
    } else {
        " __attribute__((unused))"
    };
    // Der Prototyp steht IMMER oben -- auch fuer eine Funktion mit Rumpf.
    aus.push_str(&format!(
        "\n{intern}{rueck} {}({liste}){}{ungenutzt};\n",
        f.name.text,
        wirkungsattribut(f, u)
    ));
    // **Ein `asm`-Rumpf wird zu erweitertem GCC-Assembler** («OPT3», 2026-08-19).
    //
    // `__volatile__` steht IMMER da: der Block hat per Konstruktion eine Wirkung, die Gabbro
    // nicht liest, also darf der C-Uebersetzer ihn nicht wegen unbenutzten Ergebnisses
    // streichen. *Wer den Text nicht liest, darf ihn auch nicht fuer entbehrlich halten.*
    if let FnRumpf::Asm(a) = &f.rumpf {
        // **`-> never` with `out { result }` is not C** (N321, 2026-09-16).
        //
        // `prototyp_kern` lowers `-> never` to `_Noreturn void`, and the `out`
        // below lowers to `return result;` -- together a `return` in a `_Noreturn`
        // function, which `cc -Werror` refuses. The checker names it (N321); the
        // emitter refuses here too, so the contradiction is loud on both channels
        // even with the rule dropped (pinned at `gift/985` as `C001`).
        if matches!(&f.ergebnis, Some(TypExpr::Never(_))) {
            if let Some((n, _)) = a.aus.iter().find(|(n, _)| n.text == "result") {
                weigere(
                    absagen,
                    n.span,
                    "`-> never` with an `asm` body that names `out { result }` -- `_Noreturn` \
                     together with `return result` is not C; whoever reads the assembler's \
                     result declares a result type, whoever never returns writes no `out`",
                );
                return;
            }
        }
        // **Der Rueckgabewert heisst `result`, und er ist ein AUSGANGSOPERAND** (2026-08-20).
        //
        // Bis dahin weigerte sich der Erzeuger fuer jeden `asm`-Rumpf mit Ergebnis -- und
        // damit war ein Systemaufruf nur halb schreibbar: absetzen ging, die Rueckgabe lesen
        // nicht. *`result` steht als Wort laengst in der Grammatik (`primary`), also braucht
        // es kein neues.*
        //
        // **Lane 235: `-> never` has no result slot.** `f.ergebnis` is `Some` for
        // `-> never` too (it lowers to `_Noreturn void` in `prototyp_kern`), so the
        // guard below would demand an `out { result }` of a body that must never
        // answer -- exactly the accepted shape of lane 225 (pinned lowering-side
        // in `crates/gabbro-check/tests/never_lowering.rs`). `never` therefore
        // counts as "no result" here: no `result` local, no `return`.
        // The contradictory `out { result }` stays refused at the N321 arm above
        // (checker) and beside it (emitter, `gift/985`), and any OTHER `out` on a
        // `-> never` body is refused just below -- an output into a by-value
        // parameter dies with the call, so no lowering gives it meaning
        // (`gift/1066`, `-- erwartet: C001`, checker silent).
        let ist_nie = matches!(&f.ergebnis, Some(TypExpr::Never(_)));
        if ist_nie {
            if let Some((n, _)) = a.aus.first() {
                weigere(
                    absagen,
                    n.span,
                    "`-> never` with an `asm` body that names an `out` operand -- a body \
                     that never answers has no result slot, and an output into a by-value \
                     parameter dies with the call. Whoever never returns writes no `out`",
                );
                return;
            }
        }
        let hat_ergebnis = f.ergebnis.is_some() && !ist_nie;
        if hat_ergebnis && !a.aus.iter().any(|(n, _)| n.text == "result") {
            weigere(absagen, f.name.span, "`asm` body returns a value but names no `out { result : … }`");
            return;
        }
        let a2 = rumpf_aus;
        a2.push_str(&format!("\n{intern}{rueck} {}({liste}) {{\n", f.name.text));
        if hat_ergebnis {
            a2.push_str(&format!("    {rueck} result;\n"));
        }
        a2.push_str("    __asm__ __volatile__(\n");
        for z in &a.zeilen {
            a2.push_str(&format!("        \"{}\\n\"\n", asmtext(&z.text)));
        }
        let ops = |v: &Vec<(Ident, Textliteral)>| -> String {
            v.iter()
                .map(|(n, c)| format!("[{}] \"{}\" ({})", n.text, ctext(&c.text), n.text))
                .collect::<Vec<_>>()
                .join(", ")
        };
        a2.push_str(&format!("        : {}\n", ops(&a.aus)));
        a2.push_str(&format!("        : {}\n", ops(&a.ein)));
        let zer: Vec<String> = a
            .zerstoert
            .iter()
            .map(|z| format!("\"{}\"", ctext(&z.text)))
            .collect();
        a2.push_str(&format!("        : {});\n", zer.join(", ")));
        if hat_ergebnis {
            a2.push_str("    return result;\n");
        }
        // **A `-> never` `asm` body must not fall off the end of its `_Noreturn` function**
        // (review G04, 2026-09-21).
        //
        // The instruction text is unchecked, and the flagship shape `hlt` DOES return: the
        // CPU resumes after the next interrupt. Falling off a `_Noreturn` function is
        // undefined behaviour (C11 6.7.4p8), and `cc -Werror` says so at `-O0` (gcc:
        // "'noreturn' function does return") and clang even at `-fsyntax-only`
        // (`-Winvalid-noreturn`) -- measured 2026-09-21 on the lowering without this loop.
        // The model reads a returning `never` axiom as a stop that never continues
        // (`execBlock_bindAxiom_never`, NeverAsm.lean); the loop below is exactly that in
        // C, well-defined, with no decision handed to the compiler.
        if ist_nie {
            a2.push_str(
                "    /* `-> never`: the assembler text is unchecked; if it returns, the\n     \
                 * call still never continues. */\n    for (;;) {\n    }\n",
            );
        }
        a2.push_str("}\n");
        return;
    }
    let FnRumpf::Block(b) = &f.rumpf else { return };
    // **A body with no `return` in it never answers, and the declaration says it does**
    // (`D2`, 2026-09-03).
    //
    // `beispiele/gift/642` is the shape the sweep found: a `forever` loop as the whole body
    // of an `impl fn g() -> u64`. The checker is right to want no `return` after the loop --
    // control never gets there -- and the emitter wrote `for (;;) { … }` and stopped, which
    // is what a C programmer would write by hand. Then `cc -std=c11 -Wall -Wextra -Werror`
    // answers *no return statement in function returning non-void*.
    //
    // **The rule is GCC's own, deliberately**: that diagnostic is syntactic at the front
    // end -- the body holds no `return` ANYWHERE. Measured beside the generated file:
    // `static uint64_t g(void) { for (;;) { x = 1; } }` draws it, and
    // `static uint64_t g(void) { for (;;) { return 1; } }` does not. So a `forever` with a
    // `return` inside it is untouched here, and it should be: that function answers.
    //
    // **And the defect is wider than the `forever` the probe carries.** `impl fn g() -> u64
    // { erledigt = 1; }` -- no loop anywhere -- reaches `cc` with the same error, measured
    // the same day. *One rule covers both, because it is the same rule GCC applies.*
    //
    // > **`__builtin_unreachable()` after the loop was the other candidate, and it lowers a
    // > declaration that is not true.** `-> u64` says this function hands back a `u64`;
    // > nothing here ever does. `never` is already in the language, `M2` reads it, and
    // > `prototyp_kern` lowers it to `_Noreturn void` -- measured end to end on the day this
    // > was written: checker silent, emitter exit 0, `cc` silent. *The refusal points at a
    // > word the language already has, which is the one case where refusing beats lowering.*
    if rueck != "void" && rueck != "_Noreturn void" && !rumpf_antwortet(b) {
        let schleife = matches!(
            b.anweisungen.last().map(|s| &s.art),
            Some(StmtArt::Schleife(l)) if matches!(**l, Schleife::Forever(_))
        );
        weigere(
            absagen,
            f.name.span,
            &format!(
                "a body that holds no `return` at all under a declaration that promises a \
                 result -- nothing in it ever answers{}. A function that is MEANT never to \
                 answer says so in its own declaration: `-> never` lowers to `_Noreturn \
                 void`, and the callers already read it",
                if schleife {
                    ", and the `forever` loop that ends it is exactly that case"
                } else {
                    ""
                }
            ),
        );
        return;
    }
    let aus = rumpf_aus;
    aus.push_str(&format!("\n{intern}{rueck} {}({liste}) {{\n", f.name.text));
    // **`(void)k;` fuer jeden Parameter, den der Rumpf nicht liest -- und das ist ein Befund,
    // kein Kunstgriff.**
    //
    // `FRAGMENTE.md` F8 nimmt `toeten(l, t, k)` und liest `k` nie: die Funktion loest `t`
    // stattdessen neu auf. **`cc -Wextra` sagt das, und KEIN Pass dieses Uebersetzers sagt
    // es** -- der C-Uebersetzer hat hier etwas gefunden, wofuer Gabbro keine Diagnose hat.
    //
    // > *Der Befund gehoert auf die Gabbro-Ebene, nicht ins Erzeugnis.* Der Anwender hat die
    // > erzeugte Zeile nicht geschrieben; eine Warnung darin sagt nichts ueber ihn. Deshalb
    // > wird sie hier stillgelegt **und in `TODO.md` als fehlender Pass gebucht** -- nicht
    // > verschwiegen, sondern an die richtige Stelle gelegt.
    let mut gelesen = std::collections::BTreeSet::new();
    benutzte_namen(b, &mut gelesen);
    for p in &f.parameter {
        if !ist_geist(&p.typ, u) && !gelesen.contains(&p.name.text) {
            aus.push_str(&format!("    (void){};\n", p.name.text));
        }
    }
    // **`(void)fertig;` for an `awaits` binding the body never reads back.**
    //
    // The same answer the two lines above give an unread parameter, and for the
    // same reason (`Namen::ungelesene_lets` carries the weighing). An `AwaitLoad`
    // binds outside `sammle_lets` -- that walker only sees `StmtArt::Let` -- so
    // the shared set cannot carry it; this site asks the same `benutzte_namen`
    // set directly. Measured 2026-09-12: the `awaitload` row of
    // `messung/proben/absenkung/` binds `fertig` and returns past it, so the
    // emitted `bool fertig = atomic_load_explicit(…)` fell at
    // `-Werror=unused-variable` under BOTH families -- the one stage-9 finding
    // of this lane that is not a `main`.
    //
    // **Deferred past the body, not beside the binding.** The silencer must
    // stand AFTER the declaration in the C -- `funktion` collects the unread
    // `awaits` names here and hands them to the statement loop below through
    // `rahmen` (see `Austritt::stille_awaits`); the `AwaitLoad` arm emits the
    // silencer where the name is already declared.
    let mut stille_awaits: Vec<String> = Vec::new();
    for s in &b.anweisungen {
        if let StmtArt::AwaitLoad(al) = &s.art {
            if !gelesen.contains(&al.name.text) {
                stille_awaits.push(al.name.text.clone());
            }
        }
    }
    // **And an `exchange` binding is the third name that binds outside
    // `sammle_lets`** (2026-09-15, the fetch-op lane).
    //
    // The same hole, found the same way: `let alt = X exchange update(t) { … }`
    // whose result no line reads back lowers to a local that `cc -Wextra`
    // refuses -- `unused-but-set-variable` out of the CAS loop,
    // `unused-variable` out of the new single-instruction arm. Measured
    // 2026-09-15 on `probe/p3.gab`: **both** families fell, so this is not a
    // cost of the new arm, it is a gap the new arm made visible.
    //
    // **Collected RECURSIVELY, unlike the `awaits` list above** -- every
    // `exchange` in the corpus stands inside a nested block
    // (`beispiele/41-handschlag.gab` inside an `if`), so a top-level-only walk
    // would answer "nothing to silence" for exactly the shapes that occur.
    fn stille_exchanges_von(b: &Block, gelesen: &BTreeSet<String>, aus: &mut Vec<String>) {
        for s in &b.anweisungen {
            if let StmtArt::Exchange(x) = &s.art {
                if !gelesen.contains(&x.name.text) {
                    aus.push(x.name.text.clone());
                }
            }
            for k in crate::unterbloecke(s) {
                stille_exchanges_von(k, gelesen, aus);
            }
        }
    }
    let mut stille_exchanges: Vec<String> = Vec::new();
    stille_exchanges_von(b, &gelesen, &mut stille_exchanges);
    // **Der Rueckgabetyp reist mit in den Rumpf** -- ein `return None` haengt an ihm.
    //
    // **Der Grund hat seit Stufe 7 einen Erzeuger** (2026-08-21). Bis dahin stand hier
    // bedingungslos `(void)_grund;` mit dem Befund im Kommentar -- *das Loch stand im
    // erzeugten C und in keiner Absage.* Jetzt schreibt `return R::F;` die Stelle, und die
    // Ruhigstellung bleibt nur fuer den Rumpf, der es nicht tut.
    //
    // > **Und der Fall, in dem sie noch faellig ist, hat einen Namen:** `N034` weist ihn im
    // > Pruefer ab. Die Zeile ist damit die zweite Flaeche derselben Regel und kein Ersatz
    // > fuer sie -- «B24». *Steht sie noch da, ist ein Pass durchgerutscht.*
    if f.fehler.is_some() && !rumpf_scheitert(b) {
        aus.push_str(
            "    (void)_grund; /* this body never returns a reason -- N034 */\n",
        );
    }
    // **And the OTHER channel needed the same line, and had it for nobody** (2026-09-15).
    //
    // A `-> T or R` lowers to `bool f(T *_wert, R *_grund)`. The guard above covers the body
    // that never writes `_grund`; the mirror -- a body whose every exit is a REASON, so
    // `_wert` is never written -- had none. Measured:
    //
    // ```text
    // fn f() -> u32 or R effects { pure } costs <= 2 ops { return R::Leer; }
    //   ->  static bool f(uint32_t *_wert, R *_grund) { *_grund = R_Leer; return false; }
    //   cc: error: unused parameter '_wert' [-Werror=unused-parameter]
    // ```
    //
    // *Zero checker errors, `gabbro emit` returned 0, and the C did not compile at either
    // level.* The form is not exotic: a routine that only ever fails is what a stub of a
    // fallible one looks like, and `Stmt.retGrund` is a constructor of the grammar in its
    // own right (`Syntax.lean`:523).
    //
    // **`rumpf_gibt_wert` and not `!rumpf_scheitert`:** a body may do both, and the two
    // questions are independent. Asking the wrong one would silence a parameter the body
    // does write -- and `(void)x;` on a written parameter is not an error, which is exactly
    // why it has to be the right question rather than a safe-looking one.
    if f.fehler.is_some() && f.ergebnis.is_some() && !rumpf_gibt_wert(b) {
        aus.push_str(
            "    (void)_wert; /* every exit of this body is a reason -- the value channel stays unwritten */\n",
        );
    }
    let rahmen = Austritt {
        freigaben: Vec::new(),
        rueck_option: match &f.ergebnis {
            Some(TypExpr::Index { tabelle, optional: true, .. }) => Some(tabelle.text.clone()),
            _ => None,
        },
        schleifen: Vec::new(),
        fehlerkanal: f.fehler.is_some(),
        stille_awaits,
        stille_exchanges,
    };
    for s in &b.anweisungen {
        anweisung(s, aus, u, absagen, 1, &rahmen);
    }
    // **The SUCCESS return of an `or R` body, and until 2026-09-03 it was not written at
    // all.**
    //
    // A Gabbro function without a result carries no closing `return` -- C's `void` return is
    // implicit and nobody misses it. **An `or R` function is `bool` in C**, and there the
    // same body runs off the end of a non-void function: the caller reads an indeterminate
    // value out of `if (!f(...))` and takes a branch on it. *Undefined behaviour, and `cc
    // -Wall -Wextra -Werror` compiled it at `-O0` and at `-O2` -- `-Wreturn-type` does not
    // reach a `static` function nothing has called yet.*
    //
    // It survived because **nothing ever emitted such a body.** The corpus carried `or R`
    // exclusively at `extern fn` until `messung/netz/udp-echo.gab`, and that one returns a
    // VALUE on every path, so the explicit `return <x>;` arm two hundred lines up wrote the
    // `return true;` for it. A body with an error channel and no result had no lowering to
    // fall out of -- `let … else` refused every call to it, one door earlier.
    //
    // > *Two holes in one form, and the first one hid the second:* repairing the call side
    // > is what made this reachable, and the repair had to be measured at the RUN and not at
    // > `cc`, which had nothing to say.
    //
    // **The one case that is left out is the one the reader would trip over:** a body whose
    // LAST statement is already a `return`. There the success return is written by the arm
    // two hundred lines up, and a second one under it would stand in the C twice --
    // `messung/netz/udp-echo.gab` and every `-> T or R` body show that shape. *C says nothing
    // about unreachable code, so this is legibility and not correctness* -- and everything
    // that falls off the end, which is what the whole paragraph is about, still gets it.
    if f.fehler.is_some() && !matches!(b.anweisungen.last().map(|s| &s.art), Some(StmtArt::Return(_)))
    {
        aus.push_str("    return true;\n");
    }
    aus.push_str("}\n");
}

/// **A syscall refusal with its own code (`C180`-`C184`).**
///
/// The five shape rules of the stub template each carry one code, so each has
/// its own poison probe -- the same reason `N063`-`N068` stand apart in
/// `syscall.rs` instead of sharing one. Everything the stub cannot lower for
/// any OTHER reason stays the generic `C001` (`weigere`), exactly as at
/// `prototyp_kern`: a code of its own is for a rule of its own, not for a
/// second spelling of "no lowering".
fn syscall_code(
    absagen: &mut Absagen,
    code: &'static str,
    span: gabbro_syntax::span::Span,
    was: &str,
) {
    absagen.schiebe(
        Absage::fehler(code, span, format!("no lowering: {was}")).mit_notiz(
            "the emitter refuses by name instead of emitting something plausible -- a \
             generator that guesses undoes every pass in front of it",
        ),
    );
}

/// **The syscall stub (lane S6, PLAN-SYSCALL.md lane S6): one C function per
/// declared `syscall`.**
///
/// The template binds every parameter to its declared in-register, loads
/// `number` into `rax`, executes the `syscall` instruction as extended inline
/// `__asm__` -- declared clobbers plus `memory`, `rcx` and `r11`, the two the
/// instruction itself destroys -- and decodes the raw `rax` answer: a
/// negative `-4095..-1` against the `errors` map into the `or R` channel, an
/// unlisted errno or an out-of-range non-negative value into the hardware
/// outcome -- `hardware (annahme a)`, the kernel answered outside its
/// contract (SYNTAX.md 12.1).
///
/// Five shape rules guard the five places where the template would otherwise
/// emit a plausible wrong stub (`C180`-`C184`, each with its poison probe);
/// everything else unlowerable is `C001` via `weigere`.
///
/// The signature is the one the call sites already lower against
/// (`prototyp_kern` for fallible functions, `let … else` at the call):
/// `bool f(params, T *_wert, R *_grund)` with the channel, `T f(params)`
/// without one. The stub carries NO `const`/`pure` attribute whatever the
/// declared effects say -- `effects { pure }` is the checker's contract
/// fiction, while the C function executes `syscall` behind a `memory`
/// clobber, and a `const` would let GCC merge two writes into one
/// (`wirkungsattribut` states the same for fallible functions).
///
/// The pinned `register … __asm__("reg")` locals are the musl idiom for this
/// ABI: the sixteen general registers have no complete constraint-letter set
/// (`r10` has none), so letters alone cannot bind them. Under the named
/// assumption the `#if defined(__GNUC__)` handover compiles on both measured
/// families (GCC and Clang define it); anywhere else it falls through and
/// `cc` complains loudly instead of the stub deciding something on its own --
/// the same handover `match_grund` writes for `D005`.
#[allow(clippy::too_many_arguments)]
fn syscall_stumpf(
    s: &SyscallDecl,
    aus: &mut String,
    rumpf_aus: &mut String,
    u: &Namen,
    tabellen: &SyscallTabellen,
    baum: &Programm,
    absagen: &mut Absagen,
) {
    let n = &s.name.text;
    // **C182 -- the pair after `abi`/`arch` is the template's own ABI.**
    // The checker holds `arch` against the declared arches (`A005`) and
    // refuses a sealed one (`A006`), but the emitter runs on the PARSED tree
    // and never consults the passes -- a blind tree must not receive a Linux
    // stub for another machine's declaration.
    if s.abi.text != "linux" || s.arch.text != "x86_64" {
        syscall_code(
            absagen,
            "C182",
            s.name.span,
            &format!(
                "`syscall {n}` declares `abi {}` `arch {}`, and the stub template is the \
                 Linux x86_64 `syscall` ABI -- the number in `rax`, the answer in `rax`, \
                 `rcx` and `r11` destroyed. A stub for another machine would carry another \
                 instruction and is not this template",
                s.abi.text, s.arch.text
            ),
        );
        return;
    }
    // **C180 -- no in-register the stub cannot keep.** `rax` carries the call
    // number before the kernel reads anything, so a parameter bound there
    // would never arrive; a register named under `clobbers` is scratch by
    // declaration, so the kernel may destroy the parameter after reading it
    // while the C still names the stale pin. One code, like `N065`'s three
    // sub-cases under one code in `syscall.rs`.
    for (reg, param) in &s.regs_in {
        if reg.text == "rax" {
            syscall_code(
                absagen,
                "C180",
                reg.span,
                &format!(
                    "`syscall {n}` binds parameter `{}` to `rax` in `regs in` -- the stub \
                     loads the call number there, and the parameter value would never reach \
                     the kernel",
                    param.text
                ),
            );
            return;
        }
        if s.clobbers.iter().any(|c| c.text == reg.text) {
            syscall_code(
                absagen,
                "C180",
                reg.span,
                &format!(
                    "`syscall {n}` binds parameter `{}` to `{}` in `regs in`, and the same \
                     register stands under `clobbers` -- scratch by declaration, so the stub \
                     cannot keep the parameter value in it",
                    param.text, reg.text
                ),
            );
            return;
        }
    }
    // **C181 -- the answer register is `rax`, and it is not scratch.** The
    // Linux x86_64 kernel leaves the raw answer in `rax`; the stub reads it
    // there and nowhere else. An empty `regs out`, another register, or two
    // registers (which the checker lets through -- see the `vorbehalt` of
    // `syscall.erklaerung`) would make it read the wrong place.
    if s.regs_out.len() != 1 || s.regs_out[0].text != "rax" {
        let hat: Vec<&str> = s.regs_out.iter().map(|r| r.text.as_str()).collect();
        syscall_code(
            absagen,
            "C181",
            s.name.span,
            &format!(
                "`syscall {n}` names `regs out` {{{}}}, and the Linux x86_64 answer arrives \
                 in `rax` -- the stub reads the raw answer there and nowhere else",
                hat.join(", ")
            ),
        );
        return;
    }
    if s.clobbers.iter().any(|c| c.text == "rax") {
        syscall_code(
            absagen,
            "C181",
            s.name.span,
            &format!(
                "`syscall {n}` carries its answer out in `rax` and lists `rax` under \
                 `clobbers` -- what is carried out is not destroyed"
            ),
        );
        return;
    }
    let modul = tabellen.module.get(n).cloned().unwrap_or_default();
    let umg = crate::umgebung::Umgebung::sammle(baum);
    // **C184 -- the number folds.** The stub loads it as an immediate; an
    // expression nobody folds (or a number outside the 64-bit number
    // register) has no immediate to load.
    let nummer: u64 = match umg.konst_wert(&modul, &s.nummer) {
        Some(v) if 0 <= v && v <= u64::MAX as i128 => v as u64,
        _ => {
            syscall_code(
                absagen,
                "C184",
                s.nummer.span,
                &format!(
                    "`syscall {n}` numbers its call with an expression the stub cannot load \
                     -- not a translation-time constant, or outside the 64-bit number register"
                ),
            );
            return;
        }
    };
    // **A ghost parameter has no register value.** It is erased from the
    // signature, so its `regs in` binding would carry a value nobody put
    // there -- the generic refusal, since this is "no lowering" and not a
    // rule of the template's own.
    for p in &s.parameter {
        if ist_geist(&p.typ, u) {
            weigere(
                absagen,
                p.name.span,
                &format!(
                    "`syscall {n}` takes a ghost parameter `{}` -- erased from the signature, \
                     so the `regs in` binding for it would carry a value nobody put there",
                    p.name.text
                ),
            );
            return;
        }
    }
    let mut params: Vec<String> = Vec::new();
    for p in &s.parameter {
        match ctyp(&p.typ, u) {
            Some(c) => {
                let luecke = if c.ends_with('*') { "" } else { " " };
                params.push(format!("{c}{luecke}{}", p.name.text));
            }
            None => {
                weigere(
                    absagen,
                    p.name.span,
                    &format!(
                        "`syscall {n}` takes `{}` of a type with no C -- the stub binds every \
                         parameter to a register, and an unlowerable one has no register value",
                        p.name.text
                    ),
                );
                return;
            }
        }
    }
    // **The answer shape: integer with a checkable bound, or nothing.**
    // `C183` -- the decoding holds the raw answer against the declared result
    // range (`einpassen` as C, PLAN-UMSETZUNG.md 2.1); a non-integer answer
    // has no range to check. A named type is refused with it too: its carrier
    // lowers, but its range lives in a declaration the stub does not resolve
    // -- one line of honesty instead of a check against the wrong bound.
    enum Antwort {
        Leer,
        Ganz { ctyp: String, unter: Option<i128>, ober: Option<i128> },
    }
    let antwort = match &s.ergebnis {
        None => Antwort::Leer,
        Some(TypExpr::Int(i)) => {
            let Some(c) = ctyp(&s.ergebnis.clone().unwrap(), u) else {
                weigere(absagen, s.name.span, "return type");
                return;
            };
            let (mut unter, mut ober): (Option<i128>, Option<i128>) = (None, None);
            if let Some(b) = &i.bereich {
                let (Some(lo), Some(hi)) =
                    (umg.konst_wert(&modul, &b.von), umg.konst_wert(&modul, &b.bis))
                else {
                    syscall_code(
                        absagen,
                        "C184",
                        b.span,
                        &format!(
                            "`syscall {n}` bounds its answer with a range the stub cannot fold \
                             -- a bound nobody evaluates at translation time is no bound"
                        ),
                    );
                    return;
                };
                let hi = if b.exklusiv { hi - 1 } else { hi };
                if hi < lo {
                    weigere(
                        absagen,
                        b.span,
                        &format!(
                            "`syscall {n}` declares an empty answer range -- no kernel answer \
                             could satisfy it, and the decoding would be all hardware outcome"
                        ),
                    );
                    return;
                }
                unter = Some(lo);
                ober = Some(hi);
            } else {
                // **No declared range: the storage word is the range -- read
                // off the same width table every other lowering reads.**
                // A 64-bit word needs no check (every non-negative `int64_t`
                // fits); a narrower one is checked against its own bound, and
                // the check the template writes is exactly that bound.
                let Some((_, bytes)) = ganzzahlwort(i.wort) else {
                    weigere(absagen, s.name.span, "return type");
                    return;
                };
                let breite: u32 = bytes * 8;
                let vorzeichen = matches!(
                    i.wort,
                    gabbro_syntax::kw::Kw::I8
                        | gabbro_syntax::kw::Kw::I16
                        | gabbro_syntax::kw::Kw::I32
                        | gabbro_syntax::kw::Kw::I64
                );
                if breite < 64 {
                    ober = Some(if vorzeichen {
                        (1i128 << (breite - 1)) - 1
                    } else {
                        (1i128 << breite) - 1
                    });
                }
            }
            // **A check the compiler would prove vacuous is not written.**
            // `raw > hi` with `hi >= 2^63 - 1` is always false over the
            // non-negative `int64_t` leg, and `-Wtype-limits` (in `-Wextra`)
            // refuses a comparison it can decide itself. Likewise a lower
            // bound at or below zero holds by construction of the leg.
            if ober.is_some_and(|h| h >= i64::MAX as i128) {
                ober = None;
            }
            if unter.is_some_and(|l| l <= 0) {
                unter = None;
            }
            if let Some(l) = unter {
                if l > i64::MAX as i128 {
                    weigere(
                        absagen,
                        s.name.span,
                        &format!(
                            "`syscall {n}` demands an answer above {l} -- past what the raw \
                             `int64_t` answer can ever hold, so the decoding would be all \
                             hardware outcome"
                        ),
                    );
                    return;
                }
            }
            Antwort::Ganz { ctyp: c, unter, ober }
        }
        Some(_) => {
            syscall_code(
                absagen,
                "C183",
                s.name.span,
                &format!(
                    "`syscall {n}` answers a non-integer type, and the decoding holds the raw \
                     answer against the declared result range -- a non-integer answer has no \
                     range to check"
                ),
            );
            return;
        }
    };
    // **The error channel: every listed errno against its reason's declared
    // number.** The `errors` map names errnos by Linux name (`EBADF`) and
    // targets by reason case (`BadFd`); the number the kernel actually sends
    // is the case's DECLARED value (`BadFd = 9`), which is the only number
    // the unit itself writes down. An errno name the kernel numbers
    // differently than the reason declares is a declaration question the
    // checker does not ask (`N067` holds names, not numbers) -- the stub
    // reads the numbers, and says so here.
    let mut arme: Vec<(i128, String)> = Vec::new();
    if !s.errors.is_empty() {
        let Some(rname) = &s.fehler else {
            weigere(
                absagen,
                s.name.span,
                &format!(
                    "`syscall {n}` maps errnos with no `or R` channel -- the decoding has \
                     nowhere to deliver"
                ),
            );
            return;
        };
        if tabellen.strittig.contains(&rname.text) {
            weigere(
                absagen,
                rname.span,
                &format!(
                    "`reason {}` is declared twice with different cases -- the errno decoding \
                     of `syscall {n}` could not pick a number for either",
                    rname.text
                ),
            );
            return;
        }
        let Some(faelle) = tabellen.gruende.get(&rname.text) else {
            weigere(
                absagen,
                rname.span,
                &format!(
                    "`or {}` resolves to no `reason` of this unit -- the errno decoding of \
                     `syscall {n}` has no numbers to compare against",
                    rname.text
                ),
            );
            return;
        };
        for (_, ziel) in &s.errors {
            let Some((_, wert)) = faelle.iter().find(|(c, _)| c == &ziel.text) else {
                weigere(
                    absagen,
                    ziel.span,
                    &format!(
                        "`{}` is no case of `reason {}` -- the errno decoding of `syscall \
                         {n}` has no number for it (the checker refuses this shape as `N067`)",
                        ziel.text, rname.text
                    ),
                );
                return;
            };
            let Ok(wert) = i128::try_from(*wert) else {
                weigere(
                    absagen,
                    ziel.span,
                    &format!(
                        "`{}` of `reason {}` is wider than the decoding compares -- the stub \
                         holds errnos in `int64_t`",
                        ziel.text, rname.text
                    ),
                );
                return;
            };
            arme.push((wert, format!("{}_{}", rname.text, ziel.text)));
        }
    }
    // **The signature: the one the call sites lower against.** With the
    // channel the error takes the return slot and the value leaves through
    // `_wert` (`prototyp_kern`); without one it is a plain function. A
    // result-less channel has no `_wert` parameter (the `delete_leaf` shape
    // of `messung/fragmente/F01.gab`).
    let grundtyp: Option<String> = s.fehler.as_ref().map(|r| r.text.clone());
    let wert_ctyp: Option<String> = match &antwort {
        Antwort::Ganz { ctyp, .. } => Some(ctyp.clone()),
        Antwort::Leer => None,
    };
    let hat_wert = wert_ctyp.is_some();
    let rueck = if grundtyp.is_some() {
        "bool".to_string()
    } else {
        match &antwort {
            Antwort::Ganz { ctyp, .. } => ctyp.clone(),
            Antwort::Leer => "void".to_string(),
        }
    };
    let mut liste = params.clone();
    if let Some(c) = &wert_ctyp {
        liste.push(format!("{c} *_wert"));
    }
    if let Some(g) = &grundtyp {
        liste.push(format!("{g} *_grund"));
    }
    let liste = if liste.is_empty() {
        "void".to_string()
    } else {
        liste.join(", ")
    };
    // **Without `pub` the binding is INTERNAL -- like `funktion`.** The
    // declaration names no visibility, so the stub is `static`, and
    // `__attribute__((unused))` for the unit that declares and never calls.
    aus.push_str(&format!("\nstatic {rueck} {n}({liste}) __attribute__((unused));\n"));
    let b2 = rumpf_aus;
    // **The counterpart each stub answers to.** With `assume` the kernel
    // keeps its contract under the named assumption; with `kernel` the peer
    // is a Gabbro dispatch entry for the same number (the pairing check is a
    // later lane's -- the stub is the same either way, only the comment
    // knows which side it faces).
    let gegen = match &s.paarung {
        SyscallPaarung::Annahme { annahme, klasse } => {
            let art = match klasse {
                AnnahmeKlasse::Falsifizierbar(sonde) => format!("falsifier {}", sonde.text),
                AnnahmeKlasse::NichtFalsifizierbar(grund) => {
                    format!("unfalsifiable {}", grund.text)
                }
            };
            format!("the named assumption `{}` ({art})", annahme.text)
        }
        SyscallPaarung::Kernel { pfad } => {
            format!("the Gabbro kernel entry `{}`", pfad.text())
        }
    };
    let bindungen: Vec<String> = s
        .regs_in
        .iter()
        .map(|(r, p)| format!("{} in {}", p.text, r.text))
        .collect();
    b2.push_str(&format!(
        "\nstatic {rueck} {n}({liste}) {{\n\
         \x20   /* syscall {n} -- number {nummer} in rax; {}.\n\
         \x20    * The kernel behind this stub is {}: that it answers inside its\n\
         \x20    * contract is assumed, and the decoding below is generated from the\n\
         \x20    * declared `errors` map, exhaustively. */\n",
        if bindungen.is_empty() {
            "no argument registers".to_string()
        } else {
            bindungen.join(", ")
        },
        gegen
    ));
    // **The register pins.** Every parameter travels in its declared register
    // (always widened to the full word -- a `u16` in `rdi` is the same value,
    // and a half-width pin would ask GCC for a mode it does not promise);
    // the number is the `rax` pin's initial value, so the answer returns in
    // the same variable (`+a`, one name, no input/output aliasing question).
    for (reg, param) in &s.regs_in {
        // A binding without a parameter binds nothing -- the checker refuses
        // it as `N065`, and on a blind tree the C names an undeclared
        // identifier, which `cc` refuses loudly instead of the stub guessing.
        b2.push_str(&format!(
            "    register uint64_t _sys_{} __asm__(\"{}\") = (uint64_t){};\n",
            reg.text, reg.text, param.text
        ));
    }
    b2.push_str(&format!(
        "    register int64_t _sys_rax __asm__(\"rax\") = (int64_t){nummer}u;\n"
    ));
    let eingaben: Vec<String> = s
        .regs_in
        .iter()
        .map(|(r, _)| format!("\"r\" (_sys_{})", r.text))
        .collect();
    let mut zerstoert: Vec<String> = s.clobbers.iter().map(|c| format!("\"{}\"", c.text)).collect();
    for fest in ["\"rcx\"", "\"r11\"", "\"memory\""] {
        if !zerstoert.iter().any(|c| c == fest) {
            zerstoert.push(fest.to_string());
        }
    }
    b2.push_str("    __asm__ __volatile__(\n        \"syscall\\n\"\n");
    b2.push_str("        : \"+a\" (_sys_rax)\n");
    if eingaben.is_empty() {
        b2.push_str("        : /* no argument registers */\n");
    } else {
        b2.push_str(&format!("        : {}\n", eingaben.join(", ")));
    }
    b2.push_str(&format!("        : {});\n", zerstoert.join(", ")));
    // **The hardware outcome, once per depth.** An unlisted errno, an errno
    // past the Linux `-4095` bound, or a non-negative value outside the
    // declared result range all mean the same thing: the kernel answered
    // outside its contract. Under the named assumption this point is not
    // reached, and that is what the handover below tells the C compiler --
    // nothing of its own, the `D005` shape at `match_grund`. One builder for
    // both depths, so the wording cannot drift between the two sites.
    let annahme = match &s.paarung {
        SyscallPaarung::Annahme { annahme, .. } => annahme.text.clone(),
        SyscallPaarung::Kernel { pfad } => pfad.text(),
    };
    let hardware = |e: &str| {
        format!(
            "{e}/* `hardware ({annahme})` -- the kernel answered outside its contract.\n\
             {e} * Under the named assumption this point is not reached; that decision is\n\
             {e} * handed to the C compiler, which decides nothing of its own. */\n\
             {e}#if defined(__GNUC__)\n\
             {e}__builtin_unreachable();\n\
             {e}#endif\n"
        )
    };
    // **The sign leg reads the pin; the value leg checks the declared range.**
    // `-_sys_rax` is safe: the `-4095` fence stands before it, so UBSan sees
    // no negation overflow by construction, not by luck.
    let liest_roh = !arme.is_empty() || grundtyp.is_some() || hat_wert;
    if !liest_roh {
        b2.push_str("    (void)_sys_rax;\n");
    } else {
        b2.push_str("    if (_sys_rax < 0) {\n");
        b2.push_str("        if (_sys_rax < -4095) {\n");
        b2.push_str(&hardware("        "));
        b2.push_str("        }\n");
        if !arme.is_empty() {
            b2.push_str("        int64_t _sys_errno = -_sys_rax;\n");
            for (nummer, fall) in &arme {
                b2.push_str(&format!(
                    "        if (_sys_errno == {nummer}) {{\n\
                     \x20           *_grund = {fall};\n\
                     \x20           return false;\n\
                     \x20       }}\n"
                ));
            }
            b2.push_str("        /* An errno the `errors` map does not admit. */\n");
            b2.push_str(&hardware("        "));
        } else if grundtyp.is_some() {
            // **A channel with no admitted errnos.** Every negative answer is
            // unlisted by construction -- the fence above already handed the
            // past-bound ones over, this hands over the rest.
            b2.push_str("        /* No admitted errnos: every negative answer is unlisted. */\n");
            b2.push_str(&hardware("        "));
        } else {
            // **No channel at all: a negative answer has nowhere to go.**
            // The declaration promises a plain value; the kernel sent an
            // error. That is the contract's outside, not a fourth outcome.
            b2.push_str("        /* No `or R` channel: a negative answer has nowhere to go. */\n");
            b2.push_str(&hardware("        "));
        }
        b2.push_str("    }\n");
        if let Antwort::Ganz { ctyp, unter, ober } = &antwort {
            if let Some(lo) = unter {
                b2.push_str(&format!("    if (_sys_rax < {lo}) {{\n"));
                b2.push_str(&hardware("    "));
                b2.push_str("    }\n");
            }
            if let Some(hi) = ober {
                b2.push_str(&format!("    if (_sys_rax > {hi}) {{\n"));
                b2.push_str(&hardware("    "));
                b2.push_str("    }\n");
            }
            if hat_wert {
                b2.push_str(&format!("    *_wert = ({ctyp})_sys_rax;\n"));
            }
        }
        if grundtyp.is_some() {
            b2.push_str("    return true;\n");
        } else if let Some(c) = &wert_ctyp {
            b2.push_str(&format!("    return ({c})_sys_rax;\n"));
        }
    }
    b2.push_str("}\n");
}

/// Die Namen in einem Praedikat -- ein `until` liest ebenso wie ein Rumpf.
///
/// **Written out over every `PredArt`, no catch-all -- and the reason is that there is no
/// safe side to err on.** The set feeds two consumers that pull in opposite directions:
///
/// * too FEW names and a table loses its `T_speicher`, while the emitted C still names it --
///   the failure of 2026-08-20 («B41b»);
/// * too MANY names and a dead parameter loses its `(void)k;`, which `cc -Wextra -Werror`
///   turns into a rejected translation unit.
///
/// *An over-approximation is not the cautious answer here; it is the other error.* So every
/// variant gets the exact answer, and the answer is read off `pred_c`: what that function
/// refuses never reaches the C, and therefore reads nothing.
fn pred_namen(p: &Pred, aus: &mut std::collections::BTreeSet<String>) {
    match &p.art {
        PredArt::Vergleich(e) => sammle_expr_namen(e, aus),
        // `expr in domain` -- the expression side only. `pred_c` has no `Element` arm and
        // refuses the whole predicate, so the domain's place never becomes a C read.
        PredArt::Element(e, _) => sammle_expr_namen(e, aus),
        PredArt::Klammer(x) | PredArt::Nicht(x) => pred_namen(x, aus),
        PredArt::Und(a, b) | PredArt::Oder(a, b) => {
            pred_namen(a, aus);
            pred_namen(b, aus);
        }
        // **The four forms `pred_c` refuses by name -- and the refusal IS the reason they
        // read nothing.** A quantifier, a `reaches`, a `Held(L)` witness and an implication
        // are proof devices; the emitter has no lowering for any of them, so counting their
        // places as read would suppress a `(void)k;` for a parameter that the C never
        // touches. *This is a catch-all that was right, spelled out so that it stays right.*
        PredArt::Quantor(_)
        | PredArt::Erreicht { .. }
        | PredArt::Held { .. }
        | PredArt::Folgt(_, _) => {}
    }
}

/// The names a PLACE reads: its base, and every expression inside an index suffix.
///
/// **One register for two readers.** Until now `sammle_expr_namen` inserted only the base
/// while `benutzte_namen` had a second, private copy that also descended into the index --
/// two implementations of one question, and they disagreed (W7). `t.slots[i]` in an `until`
/// predicate lowers to `t_speicher.slots[i]`, so `i` is read; the predicate reader did not
/// say so.
fn ort_namen(o: &Ort, aus: &mut std::collections::BTreeSet<String>) {
    aus.insert(o.basis.text.clone());
    for s in &o.suffixe {
        match s {
            OrtSuffix::Index(x) => sammle_expr_namen(x, aus),
            // `.f` and `->f` select a FIELD of the base. A field name is never a parameter
            // and never a table, so it belongs to no read set.
            OrtSuffix::Feld(_) | OrtSuffix::Ueber(_) => {}
        }
    }
}

fn sammle_expr_namen(x: &Expr, aus: &mut std::collections::BTreeSet<String>) {
    match &x.art {
        ExprArt::Ort(o) => ort_namen(o, aus),
        ExprArt::Klammer(y) | ExprArt::Unaer(_, y) => sammle_expr_namen(y, aus),
        ExprArt::Binaer(_, a, b) => {
            sammle_expr_namen(a, aus);
            sammle_expr_namen(b, aus);
        }
        ExprArt::Ruf(r) => {
            for a in &r.argumente {
                sammle_expr_namen(a, aus);
            }
        }
        // **Lane E1:** the arguments of a library call name places like any
        // call's; the region is raw tokens and names none.
        ExprArt::LibraryCall(r) => {
            for a in &r.args {
                sammle_expr_namen(a, aus);
            }
        }
        // **Lane 111:** the elements of a table literal name places like any
        // expression's -- a `const` initializer is not name-free.
        ExprArt::ArrayLit(es) => {
            for e in es {
                sammle_expr_namen(e, aus);
            }
        }
        // **«SG-24»** -- the counted predicate runs: every name it reads is read by
        // the emitted counter call. (The binder is a loop variable of that call --
        // collecting it here is what lets the `(void)k;` decision see it as read.)
        ExprArt::Zaehle { rumpf, .. } => {
            for e in crate::ausdruecke_im_praedikat(rumpf) {
                sammle_expr_namen(e, aus);
            }
        }
        // A literal names nothing.
        ExprArt::Zahl(_) | ExprArt::Gleitkomma { .. } | ExprArt::Wahr | ExprArt::Falsch => {}
        // **The three forms `ausdruck` refuses -- see there.** `sizeof`/`lenof`/`aligned`,
        // `old(place)` and `result` have no lowering outside a `format` predicate; the unit
        // that contains one is refused as a whole, so no name of theirs is ever read by
        // emitted C.
        ExprArt::Eingebaut(_) | ExprArt::Alt(_) | ExprArt::Ergebnis => {}
        // **A reason value names no place.** `R::F` is a constant of the error channel;
        // nothing in it is a name the caller has to see.
        ExprArt::Grund { .. } => {}
        // **A function pointer value DOES name one.** `&f` names `f`, and a collector that
        // skipped it would report the emitted C as touching fewer names than it does.
        // *Added when the compiler asked, 2026-08-21.*
        //
        // **Since `&T` (2026-09-16) the short name rides along.** The emitted C
        // names the last segment only (`&f`, `&T_speicher`), while `pfad.text()`
        // carries the qualification (`&m::f`); and `tabellenglobal` -- the set
        // that buys `T_speicher` its storage -- holds short table names. Without
        // the short form a qualified `&m::T` would lower to `&T_speicher` the
        // unit never declares. Unqualified paths insert the same word twice
        // into a set, which is no change at all.
        ExprArt::FnWert(pfad) => {
            aus.insert(pfad.text());
            if let Some(letztes) = pfad.teile.last() {
                aus.insert(letztes.text.clone());
            }
        }
    }
}

/// Welche Namen liest dieser Rumpf? Nur die Formen, die der Erzeuger ueberhaupt absenkt --
/// jede andere wird ohnehin abgelehnt.
/// **The one walker that answers *which names does this body mention*.**
///
/// `pub(crate)` since 2026-08-31, because `namen.rs::let_ohne_leser` needs the same
/// answer and a second implementation of it would drift -- *the comment three lines
/// down already records that happening once inside this file.*
///
/// It is the load-bearing walker of the `(void)k;` decision, so it is measured in both
/// directions by the emission suite: too few names and a live parameter is silenced,
/// too many and a dead one keeps a warning `cc -Wextra -Werror` turns into an error.
pub(crate) fn benutzte_namen(b: &Block, aus: &mut std::collections::BTreeSet<String>) {
    // **Die zwei privaten Helfer `e` und `o_` sind weg** -- see `sammle_expr_namen` and
    // `ort_namen`. They were a second implementation of the same question and had already
    // drifted from the first.
    let e = sammle_expr_namen;
    let o_ = ort_namen;
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Return(Some(x)) => e(x, aus),
            // `return;` -- the emitted form is the lock releases and a bare `return`, and
            // neither names anything.
            StmtArt::Return(None) => {}
            StmtArt::Zuweisung(z) => {
                o_(&z.ziel, aus);
                e(&z.wert, aus);
            }
            StmtArt::Ruf(r) => {
                for a in &r.argumente {
                    e(a, aus);
                }
            }
            // **Lane E1:** same as above, at the statement form.
            StmtArt::LibraryCall(r) => {
                for a in &r.args {
                    e(a, aus);
                }
            }
            StmtArt::Let(l) => e(&l.wert, aus),
            StmtArt::Sperrt(x) => benutzte_namen(&x.rumpf, aus),
            // **Lane O-1:** names read on the child path count -- a missed
            // name here would be silenced with `(void)` while the path reads
            // it on the handed stack.
            StmtArt::Child(x) => benutzte_namen(x, aus),
            // **Fehlte bis zum 2026-08-17**, und die Folge war ein `(void)k;` fuer einen
            // Parameter, den der Schleifenrumpf sehr wohl liest -- also eine stillgelegte
            // Warnung ueber einen Namen, der gar nicht tot ist.
            StmtArt::Narrow(x) => {
                o_(&x.ort, aus);
                benutzte_namen(&x.sonst, aus);
            }
            StmtArt::Schleife(sch) => match sch.as_ref() {
                Schleife::Retry(r) => {
                    if let Some(b) = &r.bis {
                        pred_namen(b, aus);
                    }
                    benutzte_namen(&r.rumpf, aus);
                }
                Schleife::Traverse(x) => {
                    // **Der Ort der DOMAENE wird gelesen.** Ohne ihn hielt der Erzeuger den
                    // traversierten Traeger fuer tot und legte ihn mit `(void)w;` still --
                    // waehrend die Schleife ihn genau dort benutzt.
                    if let Domaene::SlotsVon(o)
                    | Domaene::NachfahrenVon(o)
                    | Domaene::VorfahrenVon(o)
                    | Domaene::Schlange(o)
                    | Domaene::ElementeVon(o)
                    | Domaene::AbbildungenVon(o) = &x.domaene
                    {
                        o_(o, aus);
                    }
                    if let Some(g) = &x.gegenstand {
                        e(g, aus);
                    }
                    benutzte_namen(&x.rumpf, aus);
                }
                Schleife::Forever(x) => benutzte_namen(&x.rumpf, aus),
            },
            StmtArt::Match(m) => {
                e(&m.gegenstand, aus);
                for z in &m.zweige {
                    benutzte_namen(&z.rumpf, aus);
                }
            }
            // **Der `if`-Zweig fehlte bis zum 2026-08-19**, und die Folge war dieselbe wie
            // beim `narrow` zwei Tage vorher: ein `(void)k;` ueber einem Namen, den der
            // Rumpf sehr wohl liest -- nur eben in einem Zweig. *Gefunden, als «C2» den
            // Binder eines `match`-Zweiges nach derselben Regel stilllegte:
            // `Kurz(k) => { if k <= 65535 { … } }` bekam ein `(void)k;` neben ein `k`.*
            StmtArt::Wenn(w) => {
                for (bed, rumpf) in &w.zweige {
                    e(bed, aus);
                    benutzte_namen(rumpf, aus);
                }
                if let Some(sonst) = &w.sonst {
                    benutzte_namen(sonst, aus);
                }
            }
            StmtArt::LetSonst(l) => {
                if let Some(r) = l.als_ruf() {
                    for a in &r.argumente {
                        e(a, aus);
                    }
                }
                benutzte_namen(&l.sonst, aus);
            }
            // **«E4»:** the stored value is read like any bound value, and the
            // full-arena continuation with it. The arena itself is named too:
            // like a table named by its body, the name decides the storage
            // (`arenen_global`) -- *a lowering and its name set are one
            // change, not two.*
            StmtArt::Alloc(a) => {
                aus.insert(a.tisch.text.clone());
                e(&a.wert, aus);
                if let Some(sonst) = &a.sonst {
                    benutzte_namen(sonst, aus);
                }
            }
            // **«E4»:** `reset` names its arena and nothing else.
            StmtArt::ResetArena(tisch) => {
                aus.insert(tisch.text.clone());
            }
            // **The value, and the INDICES of the target.** The base of a `publishes`
            // target is an ATOMIC global -- the lowering looks it up in `u.atomics` and
            // refuses anything else -- so the base is neither a parameter (no parameter is
            // an atomic) nor a table, and belongs to neither consumer of this set. The
            // `publishes { … }` payload lands in a comment; the pairing was decided at
            // compile time (V001-V004).
            //
            // **Its indices are another matter, and were wrong for exactly as long as
            // there were none.** `REGEL[r] = v publishes nothing;` over an atomic ARRAY
            // reads `r` -- the emitted `atomic_store_explicit(&REGEL[r], …)` names it --
            // and this walker did not see it. Measured 2026-09-16 at the first emitted
            // atomic array: `void setz(uint32_t r, …) { (void)r; … &REGEL[r] …}`. *`cc`
            // accepts that (a `(void)` before a use is legal), which is the bad half: the
            // line is a STATEMENT that the parameter is unread, and it was false.* Only
            // the index expressions go in, never the base -- a name too many here keeps a
            // `-Wextra` warning alive that `-Werror` turns into an error.
            StmtArt::Publish(p) => {
                e(&p.wert, aus);
                for i in crate::ausdruecke_im_ort(&p.ziel) {
                    e(i, aus);
                }
            }
            StmtArt::Observiert(o) => benutzte_namen(&o.rumpf, aus),
            StmtArt::Exchange(x) => {
                for i in crate::ausdruecke_im_ort(&x.ort) {
                    e(i, aus);
                }
                match &x.form {
                    XForm::Update { rumpf, .. } => benutzte_namen(rumpf, aus),
                    XForm::Vergleich { wert, bedingung, .. } => {
                        e(wert, aus);
                        pred_namen(bedingung, aus);
                    }
                }
            }
            // `let x = place awaits { … }` -- same as `publishes`, from the other side: the
            // source is an atomic global, and the `awaits { … }` list lands in a comment.
            // Its indices are read for the same reason as the two arms above.
            StmtArt::AwaitLoad(al) => {
                for i in crate::ausdruecke_im_ort(&al.quelle) {
                    e(i, aus);
                }
            }
            // **`breaking l { … }` LOWERS since 2026-08-31, so this arm descends.**
            //
            // What stood here was right for as long as its premise was: *"`anweisung`
            // refuses it by name, so descending would count names the C never reads."* The
            // moment the refusal fell, the arm became the OTHER error -- the emitted C names
            // what the set does not, and `beispiele/53-zwei-orte.gab` showed it in one line:
            // `(void)e;` above a body that writes `e->slots`. Harmless there, and the same
            // omission over a table loses its `T_speicher` («B41b», 2026-08-20).
            //
            // *A lowering and its name set are one change, not two.*
            StmtArt::Bricht(x) => benutzte_namen(&x.rumpf, aus),
            // **Lane 253:** `start` roots name functions, never locals of
            // this set -- and `anweisung` refuses the statement by name, so
            // descending would count names the C never reads.
            StmtArt::Start(_) => {}
            // **Lane 257:** `grow` is refused by name in `anweisung`
            // below, so descending would count names the C never reads
            // -- same shape as `start`. The arm lane adds the descent
            // with its lowering (a lowering and its name set are one
            // change, not two).
            StmtArt::Grow(_) => {}
            // `leave l;` / `next l;` lower to `goto`, `break` or `continue`. A label is not
            // a name of this set.
            StmtArt::Leave(_) | StmtArt::Next(_) => {}
        }
    }
}

/// **Die Austrittsliste -- der Grund, warum `locks` nicht nur zwei Zeilen ist.**
///
/// In einem `locks`-Block darf kein `return` die Sperre stehen lassen. Die Liste traegt die
/// Freigaben der offenen Bloecke, innerste zuletzt; vor jedem `return` werden sie **in
/// umgekehrter Reihenfolge** ausgegeben.
///
/// > *Das ist woertlich die Klasse, die C8 bezahlt hat:* ein neuer Abweispfad erbt die
/// > Aufraeumpflicht des alten nicht. Hier erbt er sie, weil nicht der Schreiber sie ausgibt.
///
/// **Und die zweite Zeile gehoert aus demselben Grund hierher**: ein `return None` weiss
/// nur an dieser Stelle, WELCHER Sonderwert gemeint ist -- er haengt am Rueckgabetyp der
/// umgebenden Funktion, nicht am Ausdruck. *Ohne ihn stuende im C ein Bezeichner `None`,
/// den niemand erklaert hat.*
#[derive(Default, Clone)]
struct Austritt {
    /// Die Freigaben der offenen `locks`-Bloecke, innerste zuletzt.
    freigaben: Vec<String>,
    /// Die Zieltabelle des `option index into T`-Rueckgabetyps dieser Funktion.
    rueck_option: Option<String>,
    /// **Je offener benannter Schleife: ihr Name und der Stand von `freigaben` bei ihrem
    /// Eintritt** (2026-08-20).
    ///
    /// `leave dienst` verlaesst die Schleife -- und damit **genau die Sperren, die INNERHALB
    /// von ihr genommen wurden**, nicht die davor. Ohne diese Zahl gaebe ein `leave` entweder
    /// zu viel frei (und der Rufer laeuft ohne seine Sperre weiter) oder zu wenig (und sie
    /// bleibt haengen). *Dieselbe Buchhaltung wie bei `return`, nur an einem naeheren Rand.*
    schleifen: Vec<(String, usize)>,
    /// **Hat diese Funktion einen Fehlerkanal (`-> T or R`)?** Dann ist der Rueckgabewert
    /// der ERFOLG, und das Ergebnis geht durch `*_wert`. Siehe `StmtArt::Return`.
    fehlerkanal: bool,
    /// **Unread `awaits` bindings of this body, collected in `funktion`.**
    ///
    /// An `AwaitLoad` binds outside `sammle_lets`, so the shared unread-`let` set
    /// cannot carry it; the arm that lowers it reads this list instead and emits
    /// the `(void)name;` silencer where the name is already declared (lane 73).
    stille_awaits: Vec<String>,
    /// **Unread `exchange` bindings of this body, collected in `funktion`.**
    ///
    /// The third name that binds outside `sammle_lets`, beside `awaits` and
    /// `alloc`. All THREE `exchange` lowerings read it -- the bounded CAS loop,
    /// the single fetch instruction and the compare-exchange -- because each
    /// declares a local that `cc -Wextra` refuses when nothing reads it back.
    stille_exchanges: Vec<String>,
}

fn einzug(n: usize) -> String {
    "    ".repeat(n)
}

fn anweisung(
    s: &Stmt,
    aus: &mut String,
    u: &Namen,
    absagen: &mut Absagen,
    tiefe: usize,
    austritt: &Austritt,
) {
    let vorzeichenlos = &u.vorzeichenlos;
    let e = einzug(tiefe);
    match &s.art {
        StmtArt::Return(w) => {
            // **Erst freigeben, dann zurueckkehren** -- und zwar fuer JEDEN offenen Block.
            for freigabe in austritt.freigaben.iter().rev() {
                aus.push_str(&format!("{e}{freigabe};\n"));
            }
            match w {
                // **Ein `return` eines GEISTES gibt nichts zurueck** (2026-08-20).
                //
                // Die Loeschung nahm bis heute den Parameter und den Rueckgabetyp und liess
                // die Anweisung stehen: `void stufe_anerkennen(Gemein *g) { … return m; }`
                // -- ein Name, den die Signatur gerade geloescht hat.
                //
                // > *Es ist nie aufgefallen, weil keine `impl fn` im Korpus einen Geist
                // > zurueckgibt.* `beispiele/22` fuehrt die ganze Bootstrecke als `extern fn`
                // > -- also Prototypen, also keine Ruempfe. **Die Loeschung war an drei von
                // > vier Stellen gebaut**, und die vierte hat kein Beispiel je ausgeloest.
                Some(x) if geist_wert(x, u) => {
                    aus.push_str(&format!("{e}return;\n"));
                }
                // **`return R::F;` ist die FEHLERrueckgabe** (Stufe 7, 2026-08-21).
                //
                // Die Gegenseite der Zeile darunter: dort geht der Erfolg durch `*_wert`
                // und `true`, hier der Grund durch `*_grund` und `false`. **Damit ist der
                // Kanal zum ersten Mal in beide Richtungen schreibbar** -- bis heute stand
                // an seiner Stelle `(void)_grund;` mit dem Befund als Kommentar, weil
                // `primary` keine Produktion fuer einen Grundwert kannte.
                //
                // *Ohne `austritt.fehlerkanal` waere das hier unerreichbar:* M1 sagt `M122`
                // an einer Funktion ohne `or R`, also kommt ein Grundwert nur hierher, wenn
                // die Signatur den Ausgang hat. **Der Erzeuger verlaesst sich trotzdem
                // nicht darauf und weigert sich** -- «B24», eine Regel, die nur auf einer
                // Flaeche steht, ist eine halbe.
                Some(x) if matches!(x.art, ExprArt::Grund { .. }) => {
                    if !austritt.fehlerkanal {
                        weigere(
                            absagen,
                            x.span,
                            "`return <reason>` in a function that declares no `or <reason>`",
                        );
                        return;
                    }
                    aus.push_str(&format!(
                        "{e}*_grund = {};\n{e}return false;\n",
                        ausdruck(x, u, absagen)
                    ));
                }
                // **`return e;` -- the reason BINDING, and it went out the wrong channel**
                // (2026-08-30).
                //
                // `fehlbare_lesung` puts `e` into `gruendewerte` for exactly the block below
                // it, so the emitter has known what `e` is since «B26». **The `return` did
                // not ask**, so a bare `e` fell through to the success branch underneath:
                //
                // ```c
                // if (!(t <= 8)) {
                //     e = Geraetelug_ZuTief;
                //     *_wert = e;             /* the reason ORDINAL, as the value */
                //     return true;            /* and the caller is told it worked */
                // }
                // ```
                //
                // > **The device lied, the check caught it, and the C reported success.**
                // > `gabbro pruefe` said nothing, `cc -Werror` compiled it: both enums lower
                // > to an integer type, so the assignment is well formed. *A silent wrong
                // > lowering is worse than a refusal -- a refusal stands in the report.*
                //
                // Found by the W24 pre-run of the M1 binding for `e`, and only because that
                // binding was built first: until then `M119` in the checker (`m1.rs`)
                // refused the program one pass earlier, and nothing ever reached the
                // emitter. **The guard was an accident, not a rule** -- and an accident that
                // holds is indistinguishable from a rule until it stops.
                Some(x)
                    if matches!(&x.art, ExprArt::Ort(o)
                        if o.suffixe.is_empty() && u.gruendewerte.contains_key(&o.basis.text)) =>
                {
                    if !austritt.fehlerkanal {
                        weigere(
                            absagen,
                            x.span,
                            "`return <reason>` in a function that declares no `or <reason>`",
                        );
                        return;
                    }
                    aus.push_str(&format!(
                        "{e}*_grund = {};\n{e}return false;\n",
                        ausdruck(x, u, absagen)
                    ));
                }
                // **`return None` / `return Some(i)`** -- der Sonderwert kommt aus dem
                // Rueckgabetyp der Funktion, nicht aus dem Ausdruck.
                Some(x) => {
                    let t = austritt
                        .rueck_option
                        .as_deref()
                        .and_then(|tab| option_wert(x, tab, u, absagen))
                        .unwrap_or_else(|| ausdruck(x, u, absagen));
                    // **`-> T or R`: der Rueckgabewert ist der ERFOLG, das Ergebnis geht
                    // durch `*_wert`** (2026-08-20, Stufe 4).
                    //
                    // Bis heute schrieb der Erzeuger `return <wert>;` in eine Funktion, deren
                    // C-Signatur `bool` zurueckgibt. **Das Ergebnis war IMMER falsch, und zwar
                    // auf zwei Arten zugleich:**
                    //
                    // ```text
                    // f(0)  ->  der Ruf meldet MISSERFOLG, obwohl 0 ein gueltiger Wert ist
                    // f(7)  ->  der Ruf meldet Erfolg und `*_wert` bleibt UNBERUEHRT
                    // ```
                    //
                    // `gabbro pruefe`: 0 Fehler, 0 Hinweise. `gabbro emit`: Ruecklaufwert 0.
                    // `cc` ohne `-Werror`: uebersetzt. **Gefunden von einem Programm** --
                    // `messung/netz/udp-echo.gab`, dem ersten mit einem Fehlerkanal an einer
                    // `impl fn`. *Der ganze Korpus fuehrt `or R` ausschliesslich an `extern
                    // fn`, also an Ruempfen, die dieser Erzeuger nie sieht.*
                    if austritt.fehlerkanal {
                        aus.push_str(&format!("{e}*_wert = {t};\n{e}return true;\n"));
                    } else {
                        aus.push_str(&format!("{e}return {t};\n"));
                    }
                }
                None if austritt.fehlerkanal => aus.push_str(&format!("{e}return true;\n")),
                None => aus.push_str(&format!("{e}return;\n")),
            }
        }
        // **Der Operator wurde bis zum 2026-08-17 IGNORIERT:** `x += 1` wurde `x = 1`. Er
        // ist in keiner der drei Waechtereinheiten vorgekommen -- und genau darum hat er
        // ueberlebt. *Dieselbe Sorte stiller Ausfall wie die Null im Ausdruckszweig.*
        StmtArt::Zuweisung(z) => {
            // **CForm zeigerArithmetik / doubleTyp: the compound forms of the
            // two Binaer refusals above.** `p += 1` on a pointer place and
            // `f += d` across the float/double boundary guess the same way the
            // binary nodes do. Integer and register places carry no `*` and take
            // the same width on both sides, so neither check fires on them --
            // the corpus scan found no pointer-typed or mixed-width `+=`/`-=`.
            // (The pointer half stood withdrawn with the Binaer one over the
            // unscoped map and returns with it on the scoped one.)
            if matches!(z.op, ZuwOp::Plus | ZuwOp::Minus) {
                let ziel = ort_typ(&z.ziel, u)
                    .and_then(|t| ctyp(&t, u))
                    .or_else(|| register_ctyp(&z.ziel, u));
                if ist_zeigerwort(&ziel) {
                    weigere(
                        absagen,
                        s.span,
                        "pointer arithmetic -- the language carries no bound for a \
                         computed address outside `place[expr]`, and an unproven \
                         bound is not emitted",
                    );
                    return;
                }
                if ist_gemischt_float_double(&ziel, &wert_ctyp(&z.wert, u)) {
                    weigere(
                        absagen,
                        s.span,
                        "mixed `float`/`double` arithmetic -- C would widen the \
                         `float` side and compute in `double`, against the checked \
                         `f32` fact, and there is no conversion form (the `F005` \
                         shape)",
                    );
                    return;
                }
            }
            // **Ein Schreiben auf ein `accumulates` MELDET, es setzt nicht.** Der Kern
            // faltet in seine eigene Zelle -- deshalb braucht es kein CAS: **niemand sonst
            // schreibt sie.** *Die Absenkung waere sonst genau die unbeschraenkte Schleife,
            // die die Sprache verbietet.*
            if z.ziel.suffixe.is_empty() && u.akkus.contains(&z.ziel.basis.text) {
                aus.push_str(&format!(
                    "{e}{}_melde({});\n",
                    z.ziel.basis.text,
                    ausdruck(&z.wert, u, absagen)
                ));
                return;
            }
            // **`x = None` braucht die ZIELTABELLE, sonst weiss der Erzeuger nicht, welcher
            // Sonderwert gemeint ist.** Bis zum 2026-08-17 weigerte er sich hier; jetzt loest
            // er das Feld auf -- und weigert sich weiterhin, wenn er es NICHT kann.
            let wert = match option_ziel(&z.ziel, u) {
                // `None` kommt als Ruf ohne Argumente an -- es IST ein Konstruktor.
                Some(tab) => option_wert(&z.wert, &tab, u, absagen)
                    .unwrap_or_else(|| ausdruck(&z.wert, u, absagen)),
                // **The declared width of the PLACE decides whether a conversion is
                // written** -- see `verenge`. `a.slots[i].kopf = i;` with an index into a
                // `count 8` table and a `u16` field narrowed silently until 2026-08-31.
                //
                // **`O9`, found while repairing D20: `ort_typ` alone never resolves a
                // register.** It answers for a table slot field, a `static`/parameter, and a
                // record field -- never for `g.REG`, so `ziel` was `None` for every register
                // WRITE and `verenge` bailed out before it ever looked at a bound. The READ
                // side already falls back to `register_ctyp` (`wert_ctyp`'s `Ort` arm); the
                // write side did not, so `g.TREIBERMERKMAL = wunsch >> 32;` carried no
                // target width to narrow AGAINST, regardless of what `verenge` could prove.
                // Mirrored here, the same way `wert_ctyp` already does it -- W7.
                None => {
                    let ziel = ort_typ(&z.ziel, u)
                        .and_then(|t| ctyp(&t, u))
                        .or_else(|| register_ctyp(&z.ziel, u));
                    // **CForm doubleTyp (lane 142): the assigned value computes
                    // in the place's width.** A `float` place suffixes its
                    // literals (`0.5f`), the way the Binaer arm does for a
                    // `float` neighbour -- without that C lifts the node to
                    // `double` and narrows late. Integer places read
                    // `schmal == false`, which is `ausdruck` itself, so their
                    // text is unchanged; mixed variables refuse above.
                    let schmal = ziel.as_deref() == Some("float");
                    verenge(
                        ausdruck_breit(&z.wert, u, absagen, schmal),
                        &z.wert,
                        ziel.as_deref(),
                        u,
                    )
                }
            };
            // **Ein `format`-Feld wird ein SETZER, kein Zuweisungsziel** (2026-08-20).
            //
            // `r.ethertyp = 2054;` ergab `EthArp_ethertyp(r) = 2054;` -- eine Zuweisung an
            // einen Funktionsaufruf, und der Pruefer meldete null Fehler. **Es sah aus wie
            // eine Absenkung und war keine**; dass `cc` es faengt, war Glueck.
            //
            // Gefunden hat es der erste Treiber, der nicht aus dem Entwurf kam: ein
            // virtio-net muss einen ARP-Rahmen STELLEN.
            if let Some(fmt) = u.formatwerte.get(&z.ziel.basis.text) {
                if let Some(OrtSuffix::Feld(f)) = z.ziel.suffixe.first() {
                    if z.ziel.suffixe.len() != 1 {
                        weigere(absagen, s.span, "a `format` field followed by more suffixes");
                        return;
                    }
                    // **`+=` auf einem Byteleser waere ein zweiter Zugriff**, und ob die
                    // beiden dasselbe sehen, sagt niemand -- bei einem Puffer, an dem ein
                    // Geraet mitschreibt, ist das die Frage selbst.
                    if !matches!(z.op, ZuwOp::Setzt) {
                        weigere(
                            absagen,
                            s.span,
                            "a compound assignment to a `format` field -- it would be a read and a \
                             write through two separate calls, and over a buffer a device also \
                             writes, whether the two see the same bytes is the question itself",
                        );
                        return;
                    }
                    aus.push_str(&format!(
                        "{e}{fmt}_setz_{}({}, {wert});\n",
                        f.text, z.ziel.basis.text
                    ));
                    return;
                }
            }
            // **Ein BITFELD eines Geraeteregisters ist kein Zuweisungsziel** (2026-08-20).
            //
            // `d.QUIT.ACK = 1;` ergab
            //
            // ```c
            // (((*(volatile uint32_t *)(d->basis + 4)) >> 0) & 1u) = 1;
            // ```
            //
            // -- der LESER auf der linken Seite einer Zuweisung. `gabbro pruefe` meldete
            // null Fehler, `gabbro emit` gab 0 zurueck, und nur `cc` sagte *„L-Wert
            // erfordert."* **Dieselbe Klasse wie der `format`-Setzer zwei Absaetze weiter
            // oben, und dieselbe Ursache: der Leser ist mechanisch, der Schreiber nicht.**
            //
            // *Warum der Korpus es nicht fand:* er schreibt Registerbits ausschliesslich
            // durch `transition`, und die hat ihren eigenen Lese-Aendere-Schreibe-Pfad.
            // Ein DIREKTER Bitschreibvorgang ging an ihm vorbei.
            //
            // **Und die Entscheidung steht schon in der Sprache:** ein Bitfeld zu schreiben
            // ist ein Lese-Aendere-Schreibe, das braucht eine Lesung, und ein `class w`
            // gibt keine her. *Das ist Falle 4.* Ihre Antwort heisst `transition` mit
            // `mirrors` -- die Bits kommen aus dem Spiegelregister, nicht aus dem
            // unlesbaren Ziel. Also: `rw` senkt ab, alles andere wird beim Namen abgesagt.
            if let Some((g, pfeil)) = u
                .geraetezeiger
                .get(&z.ziel.basis.text)
                .map(|g| (g, "->"))
                .or_else(|| u.geraetewerte.get(&z.ziel.basis.text).map(|g| (g, ".")))
            {
                // **A BANK is written through its setter** (2026-08-26). Same reason as the
                // read: the base may only be known at run time, so the address arithmetic
                // lives in the generated accessor and not at the call site.
                //
                // *A compound assignment is refused by name*, and for the same reason a
                // register bit field refuses one: it would be two accesses to a place the
                // device also writes, and which one wins is not a question with an answer.
                if z.ziel.suffixe.len() == 3 {
                    if let (Some(OrtSuffix::Feld(b)), Some(OrtSuffix::Index(i)), Some(OrtSuffix::Feld(r))) =
                        (z.ziel.suffixe.first(), z.ziel.suffixe.get(1), z.ziel.suffixe.get(2))
                    {
                        if u
                            .geraete
                            .get(g)
                            .and_then(|dev| dev.baenke.get(&b.text))
                            .is_some_and(|s| s.contains(&r.text))
                        {
                            if !matches!(z.op, ZuwOp::Setzt) {
                                weigere(
                                    absagen,
                                    s.span,
                                    "a compound assignment to a bank register -- it would be \
                                     two accesses to a place the device also writes",
                                );
                                return;
                            }
                            let adr = if pfeil == "->" {
                                z.ziel.basis.text.clone()
                            } else {
                                format!("&{}", z.ziel.basis.text)
                            };
                            aus.push_str(&format!(
                                "{e}{g}_{}_setz_{}({adr}, {}, {});\n",
                                b.text,
                                r.text,
                                ausdruck(i, u, absagen),
                                ausdruck(&z.wert, u, absagen)
                            ));
                            return;
                        }
                    }
                }
                if z.ziel.suffixe.len() == 2 {
                    if let (Some(OrtSuffix::Feld(r)), Some(OrtSuffix::Feld(f))) =
                        (z.ziel.suffixe.first(), z.ziel.suffixe.get(1))
                    {
                        let dev = u.geraete.get(g);
                        let lage = dev.and_then(|d| d.reg.get(&r.text));
                        let bits = dev.and_then(|d| d.felder.get(&r.text)).and_then(|m| m.get(&f.text));
                        let klasse = dev.and_then(|d| d.klassen.get(&r.text)).copied();
                        if let (Some(dv), Some((versatz, breite)), Some((hi, lo, _))) =
                            (dev, lage, bits)
                        {
                            if !matches!(klasse, Some(RegKlasse::LesenSchreiben)) {
                                weigere(
                                    absagen,
                                    s.span,
                                    "a bit field of a register that is not `class rw` -- \
                                     writing one bit means reading the word first, and this \
                                     register does not give a reading. That is trap 4, and \
                                     its form is `transition` with `mirrors`",
                                );
                                return;
                            }
                            if !matches!(z.op, ZuwOp::Setzt) {
                                weigere(
                                    absagen,
                                    s.span,
                                    "a compound assignment to a register bit field -- it \
                                     would be two accesses to a place the device also writes",
                                );
                                return;
                            }
                            let n = (hi - lo + 1) as u32;
                            let maske: u128 = if n >= 128 { u128::MAX } else { ((1u128 << n) - 1) << lo };
                            // **The read-modify-write is the same move in both spaces, and
                            // only its two ends differ.** `mmio` reads and writes ONE place;
                            // `port` reads through `in` and writes through `out`, and there
                            // is no place between them. *The word arithmetic in the middle
                            // does not know the difference and must not learn it.*
                            let neu = format!(
                                "({breite})((_v & ({breite})~({breite}){maske}u) \
                                 | (({breite})({wert}) << {lo}u & ({breite}){maske}u))"
                            );
                            let lesen = geraetelesung(
                                dv,
                                &z.ziel.basis.text,
                                pfeil,
                                *versatz,
                                breite,
                                g,
                                &r.text,
                            );
                            let schreiben = if matches!(dv.raum, Raum::Port) {
                                format!(
                                    "{g}_{}_out({}, {neu});",
                                    r.text,
                                    handgriff(&z.ziel.basis.text, pfeil)
                                )
                            } else {
                                format!("{lesen} = {neu};")
                            };
                            aus.push_str(&format!(
                                "{e}{{\n{e}    {breite} _v = {lesen};\n\
                                 {e}    {schreiben}\n{e}}}\n"
                            ));
                            return;
                        }
                    }
                }
                // **A WHOLE port register is written through `out`, and a compound
                // assignment to one is refused by name** (2026-09-02).
                //
                // This is demand 3 over `geraet` at the place where it costs something. The
                // `mmio` lowering falls through to the generic tail below and writes
                // `<place> op= <value>;` -- the paragraph over `geraet` says why that is
                // right there: *the access lowers as a PLACE, so `+=` carries itself.*
                //
                // **In the port space there is no place**, so the generic tail would write
                // `Com1_THR_in(c) = b;` -- a CALL on the left of an assignment, and the only
                // reader would be `cc`. *That is the same shape as the register bit field on
                // the left of an assignment above, and it was found the same way.* So the
                // simple assignment becomes the `out` call, and `+=` is refused: it would be
                // an `in` and an `out` on a register the device also writes, and which of the
                // two sees the device's own value is not a question with an answer.
                if z.ziel.suffixe.len() == 1 {
                    if let Some(OrtSuffix::Feld(r)) = z.ziel.suffixe.first() {
                        let dev = u.geraete.get(g);
                        if matches!(dev.map(|d| &d.raum), Some(Raum::Port))
                            && dev.is_some_and(|d| d.reg.contains_key(&r.text))
                        {
                            if !matches!(z.op, ZuwOp::Setzt) {
                                weigere(
                                    absagen,
                                    s.span,
                                    "a compound assignment to a port register -- `in` and \
                                     `out` are two instructions with no place between them, \
                                     so this would be a read and a write to a register the \
                                     device also writes, and which of the two sees the \
                                     device's own value is not a question with an answer",
                                );
                                return;
                            }
                            aus.push_str(&format!(
                                "{e}{g}_{}_out({}, {wert});\n",
                                r.text,
                                handgriff(&z.ziel.basis.text, pfeil)
                            ));
                            return;
                        }
                    }
                }
            }
            // **Direct byte writes take the `schreibBytes` arm (lane-141).**
            // `None` falls through to the generic tail below, exactly as before.
            if let Some(c) = schreib_bytes(z, &wert, &e, u, absagen) {
                aus.push_str(&c);
                return;
            }
            // **An `atomic` target is not read through `ort()` (lane 152).**
            //
            // The read branch in `ort()` lowers a bare atomic to
            // `atomic_load_explicit` -- an rvalue, which is exactly what a
            // store target must not be. The checker refuses the bare store
            // (`N270`), so through `gabbro emit` this line is unreachable;
            // what reaches it is the counterfactual -- `emittiere` on the
            // parsed tree, which the `-- erwartet: … allein` probes compile
            // to prove the checker is the ONLY guard on the form. For that
            // the old spelling must stand here unchanged: the plain name,
            // exactly as the generic tail wrote it before the read branch
            // existed. A name bound here shadows the atomic (the same four
            // function-scoped views as in `ort()`), and then the plain name
            // is the C local either way.
            if z.ziel.suffixe.is_empty()
                && u.atomics.contains_key(&z.ziel.basis.text)
                && !u.parametertyp.contains_key(&z.ziel.basis.text)
                && !u.lokaltyp.contains_key(&z.ziel.basis.text)
                && !u.werte.contains(&z.ziel.basis.text)
                && !u.laufvariablen.contains(&z.ziel.basis.text)
            {
                aus.push_str(&format!(
                    "{e}{} {} {};\n",
                    z.ziel.basis.text,
                    zuw_op(&z.op),
                    wert
                ));
                return;
            }
            aus.push_str(&format!(
                "{e}{} {} {};\n",
                ort(&z.ziel, u, absagen),
                zuw_op(&z.op),
                wert
            ));
        }
        // **`narrow x to a .. b else { … }` ist die einzige Laufzeitpruefung, die der
        // ANWENDER schreibt** -- und sie steht hier, weil die Sprache sie als Pruefung
        // DEFINIERT, nicht weil M1 versagt haette. *W6 gilt in die andere Richtung: was M1
        // traegt, wird weggelassen; was `narrow` heisst, bleibt stehen.* (Die Schranken an
        // direkten Bytezugriffen gibt der Erzeuger selbst aus -- `lese_bytes`/`schreib_bytes`
        // als Zweitmeinung zur getragenen Schranke; siehe dort.)
        StmtArt::Narrow(n) => {
            // **«F»: `finite` senkt zu `isfinite` ab, und die Pruefung BLEIBT.**
            //
            // Sie ist genau das, was `narrow` in dieser Sprache bedeutet -- eine Anweisung
            // mit benanntem Ausgang, deren Pruefung im C stehen bleibt (W6 gilt in die
            // andere Richtung: was M1 traegt, wird weggelassen; was `narrow` heisst, bleibt).
            //
            // `isfinite` deckt beide Bits auf einmal: NaN ist nicht endlich, und die
            // Unendlichkeiten sind es auch nicht. *Ein Makro, zwei Zusagen -- dieselbe
            // Rechnung wie im Pruefer.*
            let bereich = match &n.ziel {
                NarrowZiel::Bereich(b) => b,
                NarrowZiel::Endlich(_) => {
                    let o = ort(&n.ort, u, absagen);
                    aus.push_str(&format!("{e}if (!isfinite({o})) {{\n"));
                    for k in &n.sonst.anweisungen {
                        anweisung(k, aus, u, absagen, tiefe + 1, austritt);
                    }
                    aus.push_str(&format!("{e}}}\n"));
                    return;
                }
            };
            let o = ort(&n.ort, u, absagen);
            let von = ausdruck(&bereich.von, u, absagen);
            let bis = ausdruck(&bereich.bis, u, absagen);
            let oben = if bereich.exklusiv { "<" } else { "<=" };
            // **`x >= 0` auf einem vorzeichenlosen Wort ist immer wahr, und `-Wextra` sagt
            // das zu Recht** (`-Wtype-limits`). Die untere Pruefung faellt deshalb weg --
            // **aber nur, wenn der Erzeuger den Typ als vorzeichenlos KENNT.** Weiss er es
            // nicht, gibt er sie aus und nimmt die Warnung in Kauf: *dann wird der Waechter
            // rot, statt dass eine Pruefung still verschwindet.*
            let untere_ist_null = matches!(&bereich.von.art, ExprArt::Zahl(0));
            // **Und seit «C5» reicht der Blick bis zum FELD.** `s.len : u32 in 0 .. KAP` ist
            // nachweislich vorzeichenlos, und `s->len >= 0` waere unter `-Wtype-limits` eine
            // Warnung ueber eine Zeile, die der Anwender nicht geschrieben hat. *Der Weg
            // bleibt derselbe: Unwissen faellt nach lautstark, die Pruefung bleibt stehen.*
            let vorzeichenlos = vorzeichenlos.contains(&n.ort.basis.text)
                || ort_typ(&n.ort, u).is_some_and(|t| vorzeichen(&t, u) == Some(true));
            let bedingung = if untere_ist_null && vorzeichenlos {
                format!("{o} {oben} {bis}")
            } else {
                format!("{o} >= {von} && {o} {oben} {bis}")
            };
            aus.push_str(&format!("{e}if (!({bedingung})) {{\n"));
            for k in &n.sonst.anweisungen {
                anweisung(k, aus, u, absagen, tiefe + 1, austritt);
            }
            aus.push_str(&format!("{e}}}\n"));
        }
        StmtArt::Ruf(r) => {
            // **A call statement whose callee returns a value DISCARDS it.** C accepts that
            // for an ordinary function, but a `pure`/`const` callee (`wirkungsattribut`)
            // turns the discard into `-Wunused-value` ("statement with no effect") under
            // `-Werror` -- found 2026-09-14 on beispiele/124 (`pruefeA();`, a reading
            // callee called for its `requires`). The cast says the discard is intended.
            // Not for ghost results (the C function returns nothing) and not for the
            // `or R` channel (a call statement over it cannot stand; it is `let … else`).
            let verwirft = r
                .path()
                .and_then(|p| p.teile.last())
                .and_then(|n| u.funktionen.get(&n.text))
                .is_some_and(|s| {
                    s.rueck.as_ref().is_some_and(|t| !matches!(t, TypExpr::Never(_)))
                        && !s.geist_rueck
                        && s.fehler.is_none()
                });
            let v = if verwirft { "(void)" } else { "" };
            aus.push_str(&format!("{e}{v}{};\n", ruf(r, u, absagen)))
        }
        // **Lane E5:** an accepted library call lowers to an ordinary call
        // with the payload passed as a `static const` table argument -- the
        // `&{payload}` the stage beside the tables laid down. Anything else
        // keeps the refusal: the region has no payload the first cut could
        // translate.
        //
        // A discarded result is the normal statement form (`@lib#f` as a
        // statement, lane E1) and needs its `(void)`: the callee is often
        // `pure` (reads through a `const` pointer), and a bare pure call
        // with a discarded result is `-Werror=unused-value` about the
        // generator, not the user. A `void` callee -- none or a ghost
        // result -- takes none, since `(void)f()` on a `void` function is
        // itself ill-formed. A fallible callee has no statement form at
        // all: the error channel needs the `let … else` the call cannot
        // carry here.
        StmtArt::LibraryCall(r) => match bibliothek_ruf(r, u, absagen) {
            Some(text) => {
                let sig = u.funktionen.get(&r.function.text);
                if sig.is_some_and(|s| s.fehler.is_some()) {
                    weigere(
                        absagen,
                        r.span,
                        "`library call` with an error channel in statement position -- the \
                         reason needs a `let … else` to leave through, and a statement \
                         names none",
                    );
                } else if sig.is_some_and(|s| s.rueck.is_some() && !s.geist_rueck) {
                    aus.push_str(&format!("{e}(void){text};\n"));
                } else {
                    aus.push_str(&format!("{e}{text};\n"));
                }
            }
            None => weigere(
                absagen,
                r.span,
                "`library call` -- the region has no payload yet (lane E5: only \
                 exact-length integer regions translate)",
            ),
        },
        // **The third place the ghost erasure has to hold, and the one that is silent if it
        // does not.** `let p1 = mmu_an(p);` binds a ghost: the BINDING goes, the CALL stays.
        // Making it `void p1 = mmu_an();` does not compile; dropping the whole statement
        // compiles and **computes something else** -- the boot step would simply not happen.
        StmtArt::Let(l) if geist_wert(&l.wert, u) => {
            aus.push_str(&format!("{e}{};\n", ausdruck(&l.wert, u, absagen)))
        }
        StmtArt::Let(l) => {
            // A non-ghost `let` needs a type, and the emitter does not guess one. The first
            // version wrote `uint32_t` unconditionally -- correct for the one file it was
            // built against and wrong for every other.
            //
            // **Steht keiner da, wird er ABGELESEN und nicht geraten**: die rechte Seite ist
            // ein Ort, und der Ort hat einen erklaerten Typ (`ort_typ`). *`let obj =
            // c.slots[s].objekt` ist die Form, an der ein halbes Dutzend Weigerungen hing --
            // und der Typ stand die ganze Zeit in der Tabellendeklaration.*
            let typ = match l.typ.as_ref().and_then(|t| ctyp(t, u)) {
                Some(c) => Some(c),
                None if l.typ.is_none() => wert_ctyp(&l.wert, u),
                None => None,
            };
            match typ {
                Some(c) => {
                    // **`O9`: the same narrowing the assignment target already gets**
                    // (`verenge`, `messung/ERZEUGERREST.md` D20). `let h : u32 = w >> 32;`
                    // is the third measured form -- an initialiser whose declared type is
                    // narrower than the right-hand side's -- and until now this site called
                    // no `verenge` at all, so it wrote the bare, uncast narrowing straight
                    // into the declaration.
                    let wert = verenge(ausdruck(&l.wert, u, absagen), &l.wert, Some(c.as_str()), u);
                    aus.push_str(&format!("{e}{c} {} = {};\n", l.name.text, wert));
                    // **`(void)r2;` for a binding this body never reads back** -- the same
                    // answer the unread parameter gets, from the same walker. See
                    // `Namen::ungelesene_lets` for why it is a lowering and not a refusal.
                    if u.ungelesene_lets.contains(&l.name.text) {
                        aus.push_str(&format!("{e}(void){};\n", l.name.text));
                    }
                }
                None => weigere(absagen, s.span, "`let` without a resolvable type"),
            }
        }
        // **`locks X { … }` -- die Sperre selbst ist eine Vertrauensbasis, die DISZIPLIN
        // nicht.** Rang und Haltezeit stehen im C nirgends: `H006` und `K002` rechnen sie zur
        // Uebersetzungszeit nach, und was der Pruefer entschieden hat, muss die Maschine nicht
        // noch einmal pruefen (W6). Was bleibt, ist Nehmen und Geben -- und dass GEGEBEN wird,
        // auf jedem Pfad.
        // **K11.2.3: die Veroeffentlichung und ihre Gegenseite.**
        //
        // `A = w publishes { … };` wird `atomic_store_explicit(&A, w, A_ORDER)` --
        // **explizit, nicht ueber den Zuweisungsoperator.** Ein `A = w` auf einem `_Atomic`
        // waere in C `seq_cst`, also eine ANDERE und teurere Ordnung als die deklarierte.
        //
        // > *Ein Erzeuger, der die deklarierte Ordnung durch eine staerkere ersetzt, ist nicht
        // > auf der sicheren Seite -- er erzeugt ein Programm, das die Quelle nicht sagt.*
        //
        // Die Nutzlast steht als Kommentar daneben: sie IST die Zusage, und der Paarungspass
        // hat sie schon geprueft (`V001`-`V004`). W6 -- was der Pruefer entschieden hat, muss
        // die Maschine nicht noch einmal pruefen.
        StmtArt::Publish(pb) => {
            let Some((ziel, atyp, ordnung, _)) = atom_target(&pb.ziel, u, absagen) else {
                weigere(absagen, s.span, "`publishes` on something that is not an atomic");
                return;
            };
            let last = match &pb.nutzlast {
                Nutzlast::Orte(l) => l.iter().map(|x| x.text()).collect::<Vec<_>>().join(", "),
                Nutzlast::Nichts(_) => "nothing".into(),
            };
            // **The atomic carries its width in its own declaration** (`atomic AVAIL_IDX :
            // u16`), and it is the same silent narrowing as at a slot field -- `-Wconversion`
            // named `atomic_store_explicit(&AVAIL_IDX, i, …)` as the second of the two sites.
            let w = verenge(
                ausdruck(&pb.wert, u, absagen),
                &pb.wert,
                Some(atyp.as_str()),
                u,
            );
            aus.push_str(&format!(
                "{e}/* publishes {{ {last} }} -- paired at compile time (V001-V004) */\n\
                 {e}atomic_store_explicit(&{ziel}, {w}, {ordnung});\n"
            ));
        }
        StmtArt::AwaitLoad(al) => {
            let Some((quelle, typ, _, ordnung)) = atom_target(&al.quelle, u, absagen) else {
                weigere(absagen, s.span, "`awaits` on something that is not an atomic");
                return;
            };
            let last = al.erwartet.iter().map(|x| x.text()).collect::<Vec<_>>().join(", ");
            aus.push_str(&format!(
                "{e}/* awaits {{ {last} }} -- paired at compile time (V001-V004) */\n\
                 {e}{typ} {} = atomic_load_explicit(&{quelle}, {ordnung});\n",
                al.name.text
            ));
            // **`(void)fertig;` where the binding is never read back** -- the same
            // answer the `let` arm gives through `Namen::ungelesene_lets`, and for
            // the same reason: `cc -Wextra` finds the unread local, no pass of this
            // compiler does, and the user did not write the generated line.
            // Measured 2026-09-12: the `awaitload` row of
            // `messung/proben/absenkung/` binds and returns past its load, so the
            // emitted `bool fertig = …` fell at `-Werror=unused-variable` under
            // BOTH families -- the one stage-9 finding that is not a `main`.
            // An `AwaitLoad` binds outside `sammle_lets` (that walker only sees
            // `StmtArt::Let`), so the shared set cannot carry it; `funktion`
            // collects the unread ones into `Austritt::stille_awaits`, and the
            // silencer stands AFTER the declaration, where the name exists.
            if austritt.stille_awaits.iter().any(|n| *n == al.name.text) {
                aus.push_str(&format!("{e}(void){};\n", al.name.text));
            }
        }
        // **«C3b»: `observes D { … }` -- dieselbe Gestalt wie `locks`, und der Unterschied
        // ist genau das, was FEHLT.**
        //
        // Betreten und Verlassen, auf JEDEM Pfad -- der Austritt wird durchgereicht, sonst
        // laesst ein `return` im Rumpf den Lesebereich offen. *Was hier NICHT steht, ist
        // eine Nahme: RCU serialisiert Leser gegen die Ruckgewinnung, nicht Schreiber
        // gegeneinander.* Der Schreiber braucht seine eigene Sperre, und dass er sie hat,
        // rechnet `H010`/`H012` zur Uebersetzungszeit nach.
        StmtArt::Observiert(o) => {
            let n = &o.domaene.text;
            aus.push_str(&format!(
                "{e}/* observes {n} -- READ side: no exclusion, only a region */\n\
                 {e}{n}_lese_start();\n{e}{{\n"
            ));
            let mut innen = austritt.clone();
            innen.freigaben.push(format!("{n}_lese_ende()"));
            for k in &o.rumpf.anweisungen {
                anweisung(k, aus, u, absagen, tiefe + 1, &innen);
            }
            aus.push_str(&format!("{e}}}\n{e}{n}_lese_ende();\n"));
        }
        // **«C4»: `exchange`, und der Korpus trägt nur EINE der beiden Formen an einem
        // Atomic.**
        //
        // `compare-exchange` senkt ab: `atomic_compare_exchange_strong_explicit` mit der
        // **deklarierten** Ordnung. Genau hier hat dieser Erzeuger schon einmal geschummelt
        // -- der Mutationskatalog fuehrt `veroeffentlichung-nimmt-die-vorgabeordnung`, weil
        // ein `=` statt der Ordnung `seq_cst` bedeutet und *das erzeugte Programm dann etwas
        // anderes sagt als die Quelle.*
        //
        // ## Und `update` bleibt `C001`, mit ZWEI Gruenden statt einem
        //
        // 1. **Der Platz ist im Korpus gar kein `atomic`** (`beispiele/05`: `z.wert` ist ein
        //    Feld eines gewoehnlichen Verbundes). Ohne Deklaration gibt es keine Ordnung, und
        //    eine zu waehlen hiesse, sie zu erfinden.
        // 2. **Und selbst an einem Atomic:** `SPRACHE.md` (RMW, die dritte Form der Paarung)
        //    sagt die Absenkung ausdruecklich -- `atomic_fetch_*`, wenn der Rumpf einer
        //    Grundform entspricht (`t+1`, `t-1`, `t|m`, `t&m`), *sonst die **beschraenkte**
        //    CAS-Schleife, „emittiert als `retry bounded NCORES * K ops on_exceeded
        //    contention`"*. Der Rumpf im Korpus saettigt (`if v < GRENZE { … }`) und ist
        //    keine Grundform; die Schranke braucht `NCORES` -- **dieselbe unentschiedene
        //    Groesse wie `accumulates` ohne `per cpu N`** -- und `on_exceeded` einen Namen,
        //    den niemand nennt.
        //
        // > *Die Sprache emittiert nichts, was sie verbietet* (die `accumulates`-Lehre). Eine
        // > unbeschraenkte CAS-Schleife waere genau das.
        StmtArt::Exchange(x) => {
            let Some((mut ziel, typ, speichern, laden)) = atom_target(&x.ort, u, absagen) else {
                weigere(
                    absagen,
                    s.span,
                    "`exchange` on something that is not a declared `atomic` -- without a \
                     declaration there is no memory ordering, and choosing one would mean \
                     inventing it",
                );
                return;
            };
            // **An INDEXED exchange hoists its index, and that is not a nicety.**
            //
            // The designator stands in the lowering three times over: the initial load,
            // the `atomic_compare_exchange_weak_explicit` INSIDE the retry loop, and the
            // comment. Written straight in, `&REGEL[naechster()]` would be evaluated once
            // per lost race -- *a different element on every pass*, which is not the
            // statement the source wrote and not an atomic RMW on anything. A parameter
            // index would be harmless and a call index would be a defect, and this
            // generator does not sort its correctness by how the caller wrote the index.
            //
            // One `const` binding before the loop settles it for every index at once:
            // evaluated exactly once, in the order it stands in, and the loop reads a
            // value. *`lese_bytes` next door takes the other road (`index_ist_rein`, and
            // fall back to the plain access when the index is impure) because there the
            // second evaluation is the OPTIONAL half -- here there is nothing to fall
            // back to.*
            let mut vorlauf = String::new();
            if !x.ort.suffixe.is_empty() {
                let h = format!("_ax{tiefe}");
                vorlauf = format!(
                    "{e}/* the index, evaluated ONCE -- the loop below re-reads the value, \
                     never the expression */\n{e}uint64_t {h} = (uint64_t)({});\n",
                    match &x.ort.suffixe[0] {
                        OrtSuffix::Index(i) => ausdruck(i, u, absagen),
                        _ => String::new(),
                    }
                );
                ziel = format!("{}[{h}]", x.ort.basis.text);
            }
            // **Relaxed publish-side exchange + exchange-`erwartet` ordering (lane-149).**
            //
            // Lane 45 closed the relaxed gap for the two single-sided forms -- a
            // `publishes` payload on a `relaxed` (or orderless, which lowers to
            // `relaxed` on both sides) atomic goes to `relaxed_mit_last`, and so does
            // an `awaits` list -- but left the combined form straight through:
            // `paarung.rs` collects both exchange halves without that check, and this
            // arm lowered them without naming them at all. An exchange that stores
            // without release publishes a promise without a mechanism (the `V004`
            // question), and one that loads without acquire awaits one (the
            // `V004`/`V005` await-side question). Same questions, same answer: refuse
            // with a name. On an ORDERED atomic both halves lower, and the C names
            // them in the same words the `Publish`/`AwaitLoad` arms use -- *what the C
            // carries, the C says.*
            let entspannt = speichern == "memory_order_relaxed";
            let traege_nutzlast = match &x.nutzlast {
                Some(Nutzlast::Orte(l)) if !l.is_empty() => {
                    Some(l.iter().map(|o| o.text()).collect::<Vec<_>>().join(", "))
                }
                _ => None,
            };
            let traege_erwartung = match &x.erwartet {
                Some(l) if !l.is_empty() => {
                    Some(l.iter().map(|o| o.text()).collect::<Vec<_>>().join(", "))
                }
                _ => None,
            };
            if traege_nutzlast.is_some() && entspannt {
                weigere(
                    absagen,
                    s.span,
                    "`exchange` with a `publishes` payload on a `relaxed` atomic (or one \
                     without any ordering word, which lowers to `memory_order_relaxed` on \
                     both sides) -- a store without release publishes a promise the machine \
                     never delivers. The same broken promise `V004` refuses at the \
                     `publishes` side; the combined form is no way around it",
                );
                return;
            }
            if traege_erwartung.is_some() && entspannt {
                weigere(
                    absagen,
                    s.span,
                    "`exchange` with an `awaits` list on a `relaxed` atomic (or one without \
                     any ordering word, which lowers to `memory_order_relaxed` on both \
                     sides) -- a load without acquire awaits a promise the machine never \
                     delivers. The same broken promise `V004`/`V005` refuse at the `awaits` \
                     side; the combined form is no way around it",
                );
                return;
            }
            let wert;
            let bedingung;
            match &x.form {
                XForm::Vergleich { wert: w, bedingung: b, .. } => {
                    wert = w;
                    bedingung = b;
                }
                // **«C4b»: der `update`-Fall senkt ab, und die Schranke sagt der Schreiber**
                // (2026-08-20).
                //
                // `SPRACHE.md` hat die Absenkung immer schon gesagt -- *die beschraenkte
                // CAS-Schleife, „emittiert als `retry bounded NCORES * K ops on_exceeded
                // contention`"* -- und der Erzeuger hat sich trotzdem geweigert, mit dem
                // richtigen Grund: **`NCORES` und der Ausgang standen nirgends.**
                //
                // Sie stehen jetzt am Konstrukt, in **denselben Woertern wie beim `retry`**.
                // Das ist keine Verlegenheitsloesung, sondern die Sache: es IST ein `retry`,
                // nur mit einem CAS als Rumpf. *Wo zwei Formen dasselbe tun, sollen sie
                // gleich heissen.*
                XForm::Update { binder, schranke, bei_ueberschreitung, rumpf } => {
                    let (Some(n), Some(ausgang)) = (schranke, bei_ueberschreitung) else {
                        weigere(
                            absagen,
                            s.span,
                            "`exchange update(v) { … }` without `bounded … ops on_exceeded …` \
                             -- SPRACHE.md lowers it to a BOUNDED CAS loop, and an unbounded \
                             one is exactly what this language forbids. The two clauses are \
                             the same ones a `retry` carries, and for the same reason",
                        );
                        return;
                    };
                    if !u.funktionen.get(&ausgang.text).is_some_and(|s| s.nie_rueck) {
                        weigere(
                            absagen,
                            ausgang.span,
                            "`on_exceeded` must name a function returning `never` -- a bound \
                             whose exit returns would let the loop run on, and then the bound \
                             is a number without a consequence",
                        );
                        return;
                    }
                    // **An `update` body that can fall through leaves the CAS operand
                    // UNDEFINED, and no C compiler on this machine says so at `-O0`.**
                    //
                    // The lowering declares `_cn` and then lets the body assign it. Every
                    // path that reaches no `return` reaches the
                    // `atomic_compare_exchange_weak_explicit` with `_cn` still indeterminate
                    // -- an undefined value proposed as the new one, on a live atomic.
                    // Measured 2026-09-02 on `beispiele/gift/658`: `gabbro pruefe` reports
                    // `0 errors`, `gabbro emit` leaves with `0`, and `cc -Wall -Wextra` is
                    // silent at `-O0`, `-O1` AND `-O2`. Only `clang
                    // -Wsometimes-uninitialized` names it. **A second compiler is not the
                    // gate this generator promises to be**: `C001` is the promise that it
                    // refuses rather than guesses, and a value it never wrote is a guess.
                    //
                    // *Why the shape of the body settles this with one line:* the body
                    // admits `return <expr>` and `if <expr> { … }` with no `else`, so an
                    // `if` never closes a path -- its false side always falls through to
                    // what follows. A block therefore answers on every path exactly when one
                    // of its OWN statements is a `return`, and a nested one never repairs
                    // that. The corpus body ends in a bare `return v;` and is untouched.
                    if !rumpf.anweisungen.iter().any(|a| matches!(&a.art, StmtArt::Return(Some(_)))) {
                        weigere(
                            absagen,
                            rumpf.span,
                            "`update` body that can fall through without a `return` -- it \
                             computes old -> new, and a path that answers nothing would hand \
                             the compare-exchange a value this generator never wrote. An \
                             `if` here has no `else`, so only a `return` of its own closes \
                             the body",
                        );
                        return;
                    }
                    // **«C4c»: the primitive body lowers to ONE instruction** (2026-09-15).
                    //
                    // `SPRACHE.md` Part III §1 has promised `atomic_fetch_*` for a primitive
                    // body since it was written, and until today the emitter had only the
                    // loop. `holform` is the closed table and its head carries the boundary,
                    // measured before it was built; `holordnung` derives the one ordering an
                    // RMW can carry from the declaration's two halves.
                    //
                    // **Nothing is lifted to get here.** The `bounded … ops on_exceeded …`
                    // clauses are still demanded above, and the fall-through check still runs
                    // -- a refusal is not a price this arm pays. What the clauses lose is
                    // their CONSEQUENCE, and only because no bound can be exceeded by an
                    // instruction that never loses a race. The C says so where it stands.
                    // **The binder's declared type travels into the fetch table
                    // (lane 221).** The wrapping rows read the wrap modulus off
                    // the atomic's declaration -- the one place the range IS
                    // readable for a name that lives only inside the loop the
                    // fetch would remove. `None` (an unresolvable declaration)
                    // answers no wrapping row; the bitwise rows never look.
                    let binder_typ = atom_elem_typ(&x.ort, u);
                    if let (Some(hol), Some(ordnung)) = (
                        holform(rumpf, &binder.text, u, &typ, binder_typ.as_ref()),
                        holordnung(speichern, laden),
                    ) {
                        aus.push_str(&vorlauf);
                        aus.push_str(&format!(
                            "{e}/* {ziel} exchange update({b}) -- ONE C11 read-modify-write and no\n\
                             {e} * loop: SPRACHE.md's RMW lowering, the primitive half. `{ausgang}`\n\
                             {e} * is unreachable -- there is no pass to count, so the declared\n\
                             {e} * bound of {gaenge} passes cannot be exceeded. (What the MACHINE\n\
                             {e} * makes of it is the target's business: `lock xadd` on some,\n\
                             {e} * a cmpxchg loop on others. The C has no bound either way.)\n\
                             {e} * {ordnung} is the JOIN of the declaration's two halves\n\
                             {e} * (store {speichern}, load {laden}): one operation, one order. */\n",
                            b = binder.text,
                            ausgang = ausgang.text,
                            gaenge = ausdruck(n, u, absagen),
                        ));
                        if let Some(last) = &traege_nutzlast {
                            aus.push_str(&format!(
                                "{e}/* publishes {{ {last} }} -- paired at compile time (V001-V004) */\n"
                            ));
                        }
                        if let Some(last) = &traege_erwartung {
                            aus.push_str(&format!(
                                "{e}/* awaits {{ {last} }} -- paired at compile time (V001-V004) */\n"
                            ));
                        }
                        aus.push_str(&format!(
                            "{e}{typ} {n} = {ruf}(&{ziel}, ({typ})({arg}), {ordnung});\n",
                            n = x.name.text,
                            ruf = hol.ruf,
                            arg = ausdruck(hol.operand, u, absagen),
                        ));
                        // **`(void)alt;` for a draw whose result this body never reads** --
                        // the same answer the `awaits` arm gives through
                        // `Austritt::stille_awaits`, and for the same `-Werror` reason.
                        if austritt.stille_exchanges.iter().any(|n| *n == x.name.text) {
                            aus.push_str(&format!("{e}(void){};\n", x.name.text));
                        }
                        return;
                    }
                    // **Die Schranke geht als AUSDRUCK hinaus, nicht als Zahl.** `NKERNE * 4`
                    // steht im Erzeugnis mit `NKERNE` als `#define` daneben -- *wer die
                    // Kernzahl aendert, aendert die Schranke mit*, und niemand muss eine
                    // ausgerechnete Zahl nachziehen.
                    let gaenge = ausdruck(n, u, absagen);
                    let (h, neu_, i) =
                        (format!("_cx{tiefe}"), format!("_cn{tiefe}"), format!("_ci{tiefe}"));
                    aus.push_str(&vorlauf);
                    // **Der Rumpf rechnet alt -> neu und ist REIN** -- er wird eine
                    // `static inline`-Funktion, damit die Schleife ihn je Durchgang neu
                    // auswertet und der C-Uebersetzer ihn trotzdem einsetzen darf.
                    aus.push_str(&format!(
                        "{e}/* {ziel} exchange update({b}) -- a bounded CAS loop, and bounded is\n\
                         {e} * the point: SPRACHE.md forbids an unbounded one. The body computes\n\
                         {e} * old -> new and is pure, so re-running it on a lost race is free of\n\
                         {e} * consequence. `{ausgang}` is the exit at {gaenge} passes. */\n\
                         {e}{typ} {};\n{e}{{\n\
                         {e}    uint32_t {i} = 0;\n\
                         {e}    {typ} {h} = atomic_load_explicit(&{ziel}, {laden});\n\
                         {e}    for (;;) {{\n\
                         {e}        {typ} {neu_};\n\
                         {e}        {{\n\
                         {e}            const {typ} {b} = {h};\n",
                        x.name.text,
                        b = binder.text,
                        ausgang = ausgang.text,
                    ));
                    // **Ordered halves are named, not dropped.** `publishes nothing` and
                    // a missing clause stay byte-identical -- only a carried promise gets
                    // a line, in the words of the `Publish`/`AwaitLoad` arms.
                    if let Some(last) = &traege_nutzlast {
                        aus.push_str(&format!(
                            "{e}/* publishes {{ {last} }} -- paired at compile time (V001-V004) */\n"
                        ));
                    }
                    if let Some(last) = &traege_erwartung {
                        aus.push_str(&format!(
                            "{e}/* awaits {{ {last} }} -- paired at compile time (V001-V004) */\n"
                        ));
                    }
                    // Der Rumpf schreibt sein Ergebnis mit `return` -- hier ist das eine
                    // Zuweisung an `_cn` und ein Sprung aus dem inneren Block.
                    rumpf_als_wert(rumpf, &neu_, aus, u, absagen, tiefe + 3);
                    // **Die Marke steht beim RUFER und nicht in der Rekursion** -- sonst
                    // stuende sie einmal je verschachteltem `if`, und C haette sie doppelt.
                    aus.push_str(&format!("{e}            {neu_}_fertig: ;\n"));
                    aus.push_str(&format!(
                        "{e}        }}\n\
                         {e}        if (atomic_compare_exchange_weak_explicit(\n\
                         {e}                &{ziel}, &{h}, {neu_}, {speichern}, {laden})) break;\n\
                         {e}        if ({i} >= (uint32_t)({gaenge})) {{ {ausgang}(); }}\n\
                         {e}        {i}++;\n\
                         {e}    }}\n\
                         {e}    {} = {h};\n{e}}}\n",
                        x.name.text,
                        ausgang = ausgang.text,
                    ));
                    // **And the loop needs the silencer just as much** -- `uint32_t alt;`
                    // assigned at the end of the block and never read is
                    // `-Werror=unused-but-set-variable`. Measured on `probe/p3.gab`
                    // 2026-09-15, BEFORE the fetch arm above existed. Byte-identical over
                    // the corpus: every `exchange` in `beispiele/` reads its result.
                    if austritt.stille_exchanges.iter().any(|n| *n == x.name.text) {
                        aus.push_str(&format!("{e}(void){};\n", x.name.text));
                    }
                    return;
                }
            }
            // `old(X) == <expr>` -- die einzige Gestalt, in der der ERWARTETE Wert dasteht.
            //
            // **Zwei Entscheidungen fielen hier unter EINEM Satz**, und die leere
            // Zeichenkette war das Zeichen fuer beide: *„das ist gar kein Vergleich"* und
            // *„das ist ein Vergleich, aber nicht dieser"*. Sie sind jetzt getrennt -- wer
            // `when a && b` schreibt, hat ein anderes Problem als wer `when old(X) > 3`
            // schreibt, und das Zeugnis darf ihm nicht dieselbe Zeile geben.
            let erwartet = match &bedingung.art {
                PredArt::Vergleich(e) => match &e.art {
                    ExprArt::Binaer(BinOp::Gleich, a, b)
                        if matches!(&a.art, ExprArt::Alt(_)) =>
                    {
                        ausdruck(b, u, absagen)
                    }
                    // Ein Vergleich -- aber nicht `old(X) == …`.
                    ExprArt::Binaer(..)
                    | ExprArt::Zahl(_)
                    | ExprArt::Gleitkomma { .. }
                    | ExprArt::Wahr
                    | ExprArt::Falsch
                    | ExprArt::Ort(_)
                    | ExprArt::Ruf(_)
                    | ExprArt::Klammer(_)
                    | ExprArt::Eingebaut(_)
                    | ExprArt::Alt(_)
                    | ExprArt::Ergebnis
                    // **`FnWert` and `Grund`, 2026-08-21.** A `when` condition of a
                    // `transition` compares a place against a value; neither a function
                    // pointer nor a reason case is a value the state machine can stand on.
                    // *They join the forms that are refused BY NAME rather than swallowed.*
                    | ExprArt::FnWert(_)
                    | ExprArt::Grund { .. }
                    // **Lane E1** -- a library call is no expected value either.
                    | ExprArt::LibraryCall(_)
                    // **Lane 111** -- a table literal is no expected value either:
                    // the expected value of a compare-exchange is ONE value.
                    | ExprArt::ArrayLit(_)
                    // **«SG-24»** -- a count is a traversal, and the expected value of a
                    // compare-exchange is ONE value, not a loop.
                    | ExprArt::Zaehle { .. }
                    | ExprArt::Unaer(..) => {
                        weigere(
                            absagen,
                            s.span,
                            "`when` comparison that is not `old(X) == <expr>` -- a \
                             compare-exchange swaps on EQUALITY with one expected value; an \
                             ordering or a bit test would have to re-read and re-compare, \
                             and that is a loop, which is the `update` case",
                        );
                        return;
                    }
                },
                // Gar kein Vergleich: eine Verknuepfung, ein Quantor, ein Zeuge.
                PredArt::Quantor(_)
                | PredArt::Element(_, _)
                | PredArt::Erreicht { .. }
                | PredArt::Held { .. }
                | PredArt::Klammer(_)
                | PredArt::Nicht(_)
                | PredArt::Und(_, _)
                | PredArt::Oder(_, _)
                | PredArt::Folgt(_, _) => {
                    weigere(
                        absagen,
                        s.span,
                        "`when` condition that is not a comparison -- a compare-exchange \
                         carries ONE expected value into the instruction, and a conjunction, \
                         a quantifier or a lock witness is not one",
                    );
                    return;
                }
            };
            // **Und die dritte Moeglichkeit, die vorher mit den beiden anderen zusammenfiel:**
            // die rechte Seite steht da, `ausdruck` hat sie aber abgelehnt und die leere
            // Zeichenkette geliefert -- der Grund steht dann schon im Zeugnis, und hier
            // bleibt nur der Abbruch. *Ohne ihn stuende `({typ})()` im C.*
            if erwartet.is_empty() {
                return;
            }
            let h = format!("_cx{tiefe}");
            aus.push_str(&vorlauf);
            // **Ordered halves are named, not dropped** -- see the `update` arm above:
            // `publishes nothing` and a missing clause stay byte-identical.
            if let Some(last) = &traege_nutzlast {
                aus.push_str(&format!(
                    "{e}/* publishes {{ {last} }} -- paired at compile time (V001-V004) */\n"
                ));
            }
            if let Some(last) = &traege_erwartung {
                aus.push_str(&format!(
                    "{e}/* awaits {{ {last} }} -- paired at compile time (V001-V004) */\n"
                ));
            }
            aus.push_str(&format!(
                "{e}bool {};\n{e}{{\n{e}    {typ} {h} = ({typ})({erwartet});\n\
                 {e}    /* compare-exchange under the DECLARED ordering -- a plain `=` would \
                 be seq_cst */\n\
                 {e}    {} = atomic_compare_exchange_strong_explicit(\n\
                 {e}        &{ziel}, &{h}, ({typ})({}), {speichern}, {laden});\n{e}}}\n",
                x.name.text,
                x.name.text,
                ausdruck(wert, u, absagen)
            ));
            // **The third `exchange` lowering, the same silencer** -- see
            // `Austritt::stille_exchanges`. Byte-identical over the corpus: a
            // compare-exchange whose `won` nobody reads is not written anywhere here.
            if austritt.stille_exchanges.iter().any(|n| *n == x.name.text) {
                aus.push_str(&format!("{e}(void){};\n", x.name.text));
            }
        }
        StmtArt::Sperrt(x) => {
            let name = x.sperre.text();
            let (nimm, gib) = if x.geteilt {
                (format!("{name}_nimm_geteilt()"), format!("{name}_gib_geteilt()"))
            } else {
                (format!("{name}_nimm()"), format!("{name}_gib()"))
            };
            aus.push_str(&format!("{e}{nimm};\n{e}{{\n"));
            let mut innen = austritt.clone();
            innen.freigaben.push(gib.clone());
            for k in &x.rumpf.anweisungen {
                anweisung(k, aus, u, absagen, tiefe + 1, &innen);
            }
            aus.push_str(&format!("{e}}}\n{e}{gib};\n"));
        }
        // **`match` ueber einem `option index into T`.** Der Sonderwert macht daraus einen
        // Vergleich; die Bindung des `Some`-Zweigs ist der Wert selbst.
        StmtArt::Match(m) => match_option(m, s, aus, u, absagen, tiefe, austritt),
        // `if` -- mehrere Zweige werden eine `else if`-Kette. **Der Austritt wird
        // durchgereicht**, sonst laesst ein `return` in einem Zweig die Sperre stehen.
        StmtArt::Wenn(w) => {
            for (i, (bed, rumpf)) in w.zweige.iter().enumerate() {
                let kopf = if i == 0 { "if" } else { "} else if" };
                aus.push_str(&format!("{e}{kopf} ({}) {{\n", ausdruck(bed, u, absagen)));
                for k in &rumpf.anweisungen {
                    anweisung(k, aus, u, absagen, tiefe + 1, austritt);
                }
            }
            if let Some(sonst) = &w.sonst {
                aus.push_str(&format!("{e}}} else {{\n"));
                for k in &sonst.anweisungen {
                    anweisung(k, aus, u, absagen, tiefe + 1, austritt);
                }
            }
            aus.push_str(&format!("{e}}}\n"));
        }
        StmtArt::Schleife(sch) => match sch.as_ref() {
            Schleife::Retry(r) => retry(r, s, aus, u, absagen, tiefe, austritt),
            Schleife::Traverse(x) => traverse(x, s, aus, u, absagen, tiefe, austritt),
            Schleife::Forever(x) => forever(x, aus, u, absagen, tiefe, austritt),
        },
        // **`leave d` und `next d` -- der benannte Ausgang und der benannte Durchgang.**
        //
        // Beide werden ein `goto` und **nicht** ein `break`/`continue`: die Marke nennt eine
        // Schleife, und in C bricht ein `break` immer die INNERSTE. Steht das `leave` in
        // einem `traverse` innerhalb des `forever`, waere `break` still die falsche Schleife
        // -- genau die Klasse von Fehler, gegen die dieser Erzeuger gebaut ist.
        //
        // *Und die Sperren, die INNERHALB der Schleife genommen wurden, werden freigegeben*
        // -- siehe `Austritt::schleifen`.
        StmtArt::Leave(m) | StmtArt::Next(m) => {
            let raus = matches!(&s.art, StmtArt::Leave(_));
            let tiefe_bei_eintritt = austritt
                .schleifen
                .iter()
                .rev()
                .find(|(n, _)| *n == m.text)
                .map(|(_, d)| *d);
            let Some(d) = tiefe_bei_eintritt else {
                // `S001` hat das schon entschieden; hier kann es nur ein Auszug sein.
                weigere(absagen, s.span, "`leave`/`next` naming no enclosing loop");
                return;
            };
            for freigabe in austritt.freigaben[d..].iter().rev() {
                aus.push_str(&format!("{e}{freigabe};\n"));
            }
            let ziel = if raus { "ende" } else { "weiter" };
            aus.push_str(&format!("{e}goto {}_{ziel};\n", m.text));
        }
        // **«C3a» ist entschieden: `let x = f() else (e) { … }` senkt ab** (2026-08-20).
        //
        // Die Weigerung, die hier stand, nannte zwei Fragen und beantwortete keine: *„What
        // `e` holds and how a call reports failure would both have to be invented here."*
        // Beide sind jetzt beantwortet, und zwar **an der Deklaration des Gerufenen**, wo
        // eine Antwort ueberprueft werden kann:
        //
        // ```gabbro
        // extern fn hol() -> u32 or HolFehler effects { pure } costs <= 1 ops;
        // ```
        //
        // *„Eine Sprachentscheidung, die nur der Absenkung dient, wird nicht getroffen"* --
        // das galt und gilt. **Diese hier dient nicht der Absenkung**: sie macht sichtbar,
        // WAS eine Funktion an ihren Rufer zurueckmelden kann, und das war vorher nirgends
        // schreibbar. Die Absenkung ist die Folge, nicht der Grund.
        //
        // Die C-Gestalt steht bei `funktion`; hier ist die Rufseite:
        //
        // ```c
        // uint32_t x;
        // { HolFehler e; (void)e;
        //   if (!hol(&x, &e)) { abbruch(); } }
        // ```
        //
        // **`x` steht AUSSERHALB des Blockes** -- es lebt weiter, `e` nicht. Dass der
        // `else`-Zweig nicht durchfaellt, hat `S002` schon entschieden (`gift/47`), und
        // deshalb ist `x` danach belegt, ohne dass hier eine Zeile darauf achten muesste.
        // *W6, an einer Stelle, an der man es leicht nicht bemerkt.*
        StmtArt::LetSonst(l) => {
            // **«B26», 2026-08-28: the one PLACE source that carries a reason.**
            //
            // A register with `requires <pred> else R::C` is read ONCE into the binding, and
            // the condition is then checked ON THE BINDING. *A promise that does not lower is
            // a fact, and a fact about a volatile register is what a hostile device gets to
            // decide* -- the «B33» error, and «B26»'s own row names it.
            if let LetQuelle::Ort(o) = &l.quelle {
                if fehlbare_lesung(l, o, aus, u, absagen, tiefe, austritt) {
                    return;
                }
            }
            let Some(r) = l.als_ruf() else {
                weigere(
                    absagen,
                    s.span,
                    "`let … else` over a PLACE -- «B14b» opened the form for an option-valued \
                     place, and there the failure is `None`, which carries no reason for `e` \
                     to hold. That half is open; the call form is decided",
                );
                return;
            };
            // **An INDIRECT `let … else` is refused, by name** (2026-08-21). The `else`
            // branch binds a `reason`, and a reason comes from the callee's `-> T or R`
            // signature. A `fn(…)` type carries a contract, **but no error channel** -- so
            // there is nothing here for `e` to hold. *The refusal is the answer, not a
            // placeholder:* the emitter does not invent a channel.
            //
            // **And it is the ONLY refusal for this shape today** -- no pass says it first.
            // `N029` speaks about the reverse case (a call that CAN fail and does not stand
            // in a `let … else`), and no checker rule looks at an indirect one. *A file that
            // never reaches the emitter therefore hears nothing about it*, which is the
            // weaker half and is booked as such.
            let Some(name) = r.path().map(|p| p.text()) else {
                weigere(
                    absagen,
                    s.span,
                    "`let … else` over an INDIRECT call -- a `fn(…)` type carries a contract \
                     but no `or R` error channel, so nothing binds `e`",
                );
                return;
            };
            let Some(sig) = u.funktionen.get(&name) else {
                weigere(absagen, s.span, "`let … else` over a call this unit does not declare");
                return;
            };
            let Some(grund) = sig.fehler.clone() else {
                // `N028` hat das im Pruefer schon gesagt; hier steht es noch einmal, weil
                // ein Ausschnitt den Pruefer nicht bestanden haben muss.
                weigere(
                    absagen,
                    s.span,
                    "`let … else` over a function that declares no `or <reason>` -- the `else` \
                     branch could never run, and `e` would name nothing",
                );
                return;
            };
            let geist = sig.geist_param.clone();
            let args: Vec<String> = r
                .argumente
                .iter()
                .enumerate()
                .filter(|(i, _)| !geist.get(*i).copied().unwrap_or(false))
                .map(|(_, a)| ausdruck(a, u, absagen))
                .collect();
            let mut ruf_args = args;
            // **A callee with `or R` and NO result type binds nothing -- and until 2026-09-03
            // that made it UNCALLABLE.**
            //
            // The declaration side has always written the result out separately: `funktion`
            // gives every `or R` function `bool` and pushes a `*_wert` parameter **only when
            // `f.ergebnis` is there** -- the error channel takes the return slot, and the
            // result leaves through `_wert`. The call side did not mirror it: it pushed
            // `&{binding}` for every
            // callee that does not return a GHOST, then asked `wert_ctyp` for a type that a
            // result-less declaration does not have, and refused with *"`let … else` whose
            // call has no resolvable type"*.
            //
            // Measured on a five-item file with no fragment in it: `pruefe` says
            // `0 errors, 0 hints`, `emit` refuses. **`or R` without a result was declarable,
            // checkable, and lowered at its declaration -- and no CALL to it lowered**, while
            // `let … else` is the one form of error propagation this language has
            // (`SPRACHE.md` §8.1). *The same shape as «B9» at `fnptr`: a form one can declare
            // and not use.* `messung/fragmente/F01.gab`'s `delete_leaf` is one, and
            // `beispiele/gift/668` is the fence.
            //
            // The answer stands two fields up in `Signatur` and needed no new rule: *"Does it
            // return a ghost? Then `let x = f(…)` loses its binding, **not its call**."* A
            // missing result is the same case -- there is nothing to bind and the call is
            // unaffected. `rueck` is the declared return type, read from the same signature
            // the error channel comes from.
            let hat_wert = !sig.geist_rueck && sig.rueck.is_some();
            if hat_wert {
                ruf_args.push(format!("&{}", l.name.text));
            }
            ruf_args.push(format!("&{}", l.fehlername.text));
            if hat_wert {
                // **Der Typ steht im Gerufenen, nicht am `let`** -- `let … else` traegt
                // gar keine Typklausel. `wert_ctyp` liest ihn aus derselben Signatur ab,
                // aus der der Fehlerkanal kommt.
                let als_expr = Expr { art: ExprArt::Ruf(r.clone()), span: r.span };
                let Some(t) = wert_ctyp(&als_expr, u) else {
                    weigere(absagen, s.span, "`let … else` whose call has no resolvable type");
                    return;
                };
                aus.push_str(&format!("{e}{t} {};\n", l.name.text));
            }
            // **`(void)e;` nur, wenn der Zweig `e` nicht liest** (Stufe 7, 2026-08-21).
            //
            // Bis heute stand die Zeile immer da, und sie war immer wahr: `e` hatte keinen
            // Leser, weil kein Pass wusste, dass der Name existiert. *Jetzt hat er einen* --
            // und eine Ruhigstellung neben einem Gebrauch behauptet etwas Falsches ueber
            // den Code, der darunter steht. Dieselbe Buchung wie beim toten Parameter.
            let mut gelesen = BTreeSet::new();
            benutzte_namen(&l.sonst, &mut gelesen);
            let stillgelegt = if gelesen.contains(&l.fehlername.text) {
                String::new()
            } else {
                format!(" (void){};", l.fehlername.text)
            };
            aus.push_str(&format!(
                "{e}{{\n{e}    {grund} {};{stillgelegt}\n{e}    if (!{name}({})) {{\n",
                l.fehlername.text,
                ruf_args.join(", ")
            ));
            // **`e` traegt seinen `reason` in die Sicht des `else`-Zweiges** -- und nur
            // dorthin. Ohne diese Zeile weiss ein `match e { … }` darin nicht, welche
            // Fallmenge erschoepfend sein muss, und der Erzeuger weigert sich mit `C001`.
            let mut innen = u.clone();
            innen
                .gruendewerte
                .insert(l.fehlername.text.clone(), grund.clone());
            for k in &l.sonst.anweisungen {
                anweisung(k, aus, &innen, absagen, tiefe + 2, austritt);
            }
            aus.push_str(&format!("{e}    }}\n{e}}}\n"));
        }
        // **«E4»: `let i = alloc A (v) [else block];`.**
        //
        // The checked bump: while the counter stands below the hard bound,
        // the next slot is taken and the value stored. With an `else` the
        // bound is read at run time and the continuation runs when the
        // arena is full; without one the checker has counted the
        // reservation (`N212`), and the bump is unconditional. The bound
        // spells through `(uint32_t)` -- a bare literal beside a `uint32_t`
        // counter is `-Wsign-compare` under `-Wextra`, and the warning
        // would be about a line the user never wrote.
        StmtArt::Alloc(a) => {
            let Some((hi_expr, element)) = u.arenen.get(&a.tisch.text) else {
                weigere(
                    absagen,
                    s.span,
                    "`alloc` out of an arena this unit cannot size -- no `hi` \
                     from its declaration",
                );
                return;
            };
            let Some(c) = ctyp(element, u) else {
                weigere(absagen, s.span, "`alloc` whose element type has no lowering");
                return;
            };
            let hi = zahltext(hi_expr, absagen);
            if hi.is_empty() {
                return;
            }
            let speicher = format!("{}_arena_speicher", a.tisch.text);
            let wert = verenge(
                ausdruck(&a.wert, u, absagen),
                &a.wert,
                Some(c.as_str()),
                u,
            );
            match &a.sonst {
                Some(sonst) => {
                    aus.push_str(&format!("{e}uint32_t {};\n", a.name.text));
                    aus.push_str(&format!(
                        "{e}if ({speicher}.used < (uint32_t)({hi})) {{\n\
                         {e}    {n} = {speicher}.used;\n\
                         {e}    {speicher}.buf[{speicher}.used++] = ({wert});\n\
                         {e}}} else {{\n",
                        n = a.name.text
                    ));
                    for k in &sonst.anweisungen {
                        anweisung(k, aus, u, absagen, tiefe + 1, austritt);
                    }
                    aus.push_str(&format!("{e}}}\n"));
                }
                None => {
                    aus.push_str(&format!(
                        "{e}uint32_t {n} = {speicher}.used;\n\
                         {e}{speicher}.buf[{speicher}.used++] = ({wert});\n",
                        n = a.name.text
                    ));
                }
            }
            // **`(void)i;` for a binding this body never reads back** -- the
            // same answer the `let` arm gives through
            // `Namen::ungelesene_lets`, and for the same `-Werror` reason.
            if u.ungelesene_lets.contains(&a.name.text) {
                aus.push_str(&format!("{e}(void){};\n", a.name.text));
            }
        }
        // **«E4»: `reset A;`.** The counter goes back to zero; every index
        // bound before names another lifetime of the same slots, and the
        // checker (`N211`) says so -- the C only moves the counter.
        StmtArt::ResetArena(tisch) => {
            if !u.arenen.contains_key(&tisch.text) {
                weigere(
                    absagen,
                    s.span,
                    "`reset` of an arena this unit never declared -- no \
                     storage to empty",
                );
                return;
            }
            aus.push_str(&format!("{e}{}_arena_speicher.used = 0;\n", tisch.text));
        }
        // -- und die EINE Form, die weiter abgelehnt wird, jetzt aber MIT GRUND ----------
        //
        // **Der Sammelzweig ist weg, und beim Verschwinden hat er dasselbe gesagt wie der
        // ueber `ItemArt`:** hinter *"no lowering: statement kind"* stand nicht eine offene
        // Liste, sondern **genau eine** Anweisungsart. Sechzehn der siebzehn senken laengst
        // ab; die Absage nannte trotzdem keine von ihnen beim Namen, und ein Leser des
        // Zeugnisses konnte daraus nicht ablesen, was fehlt.
        //
        // > *Und die Absage war teurer als sie aussah:* solange sie hier stand, hielt
        // > `pruefe-abstieg.py` die ganze Datei fuer entschuldigt (*"weigert sich benannt"*),
        // > und jede fehlende Anweisungsart in jedem Sammler dieser Datei fiel damit aus der
        // > Messung. **Ein Vorbehalt an einer Stelle deckte Luecken an fuenf anderen.**
        // **`breaking I { … }` LOWERS since 2026-08-31, and the reason it did not is
        // answered rather than dropped.**
        //
        // What stood here refused with one sentence: *"emitting it would drop the region and
        // make the C look like a program whose obligation nobody carries."* The premise is
        // right and the conclusion does not follow -- **the obligation is carried, and by a
        // register that already exists.** Measured against the unchanged checker:
        //
        // ```
        // $ gabbro pflichten beispiele/53-zwei-orte.gab
        // E  Preservation (2)
        //      treffen_oeffnen :: antwortpflicht_paarig
        //      treffen_schliessen :: antwortpflicht_paarig
        // ```
        //
        // *A region whose obligation is booked is not dropped by lowering it; it is dropped
        // by lowering it SILENTLY.* So the block carries its own name into the C: which
        // invariants are suspended, and where the duty is counted. At run time the region is
        // nothing but its statements -- so a plain block is the FAITHFUL lowering, and any
        // other would be the generator inventing a run-time meaning for a proof device.
        //
        // **Regel A is satisfied by measurement, not by taste**: `beispiele/53-zwei-orte.gab`
        // is a clean corpus program -- 0 checker errors -- that produced no C. That is a
        // measured need, and it is the whole of it.
        //
        // > The alternative outcome was open and was rejected on the same measurement:
        // > refusing `breaking` in the CHECKER would make a clean example invalid, and the
        // > example exists because two places must fall together. *A language that does not
        // > have a form is complete as long as it says so -- but this one has it.*
        StmtArt::Bricht(b) => {
            let namen: Vec<&str> = b.invarianten.iter().map(|i| i.text.as_str()).collect();
            aus.push_str(&format!(
                "{e}/* breaking {} -- PROOF region: inside it the invariant is not a\n\
                 {e} * premise. At run time this is its statements and nothing else; the\n\
                 {e} * restoration is booked as a preservation obligation (`gabbro pflichten`).\n\
                 {e} */\n",
                kommentartext(&namen.join(", "))
            ));
            aus.push_str(&format!("{e}{{\n"));
            for k in &b.rumpf.anweisungen {
                anweisung(k, aus, u, absagen, tiefe + 1, austritt);
            }
            aus.push_str(&format!("{e}}}\n"));
        }
        // **Lane O-1: `child { … }` (K-1).** The handoff shape (no return
        // into the caller's frame, a never-ending tail) is the checker's
        // business (`N448`/`N449` in `clone.rs`); the lowering is refused
        // below (`C185`), and the block is written out best-effort beside
        // the refusal so the refusal changes no `cc` verdict.
        StmtArt::Child(x) => {
            // **C185 -- the child path has no lowering in this template.**
            // The stub above lowers the GATE as one C function; after a
            // stack-switching call the child resumes inside that helper on
            // the NEW stack, and the helper's `return` would pop a return
            // address off the handed stack. The sound lowering is an inline
            // trap with the child entered by jump (K-1's fork (b) is the
            // unchecked `asm` form of it; fork (a) the C driver outside the
            // language) -- until it lands, every `child` block falls here,
            // by name, never silently. The block is still written out
            // best-effort below, so the refusal changes no `cc` verdict.
            //
            // **The assumption a lowering must keep (fix lane F3, review G11
            // F4):** the checker judges the REGION only (`N451`/`N452` spill,
            // `N456`/`N457` thread, `N450` one dominating call per region).
            // The statements between the gate call and the region (155's
            // `if v == 0`) are checked as PARENT code. A lowering that lets
            // the child return from the call and run on (fork style) would
            // execute them unchecked on the handed stack -- the child must be
            // entered by jump at the region, the parent must skip it.
            // `tests/klon_faden.rs` pins this sentence to the refusal.
            syscall_code(
                absagen,
                "C185",
                s.span,
                &format!(
                    "`child` has no lowering in the `syscall` stub template -- after a \
                     stack-switching call the child resumes inside the gate's helper on \
                     the handed stack, and the helper's return would pop a return address \
                     off it. The inline trap with the child entered by jump is not built \
                     -- and the checker ASSUMES that jump: it judges the region only, so \
                     the statements between the gate call and the region never run on \
                     the child's stack (SATZKARTE §39, `klon.uebergabe`)"
                ),
            );
            aus.push_str(&format!(
                "{e}/* child -- HANDOFF region: runs on the handed stack of the\n\
                 {e} * stack-carrying gate. Never returns into the caller frame\n\
                 {e} * (`N448`/`N449`); at run time this is its statements.\n\
                 {e} */\n"
            ));
            aus.push_str(&format!("{e}{{\n"));
            for k in &x.anweisungen {
                anweisung(k, aus, u, absagen, tiefe + 1, austritt);
            }
            aus.push_str(&format!("{e}}}\n"));
        }
        // **Lane 260: `start { f, g };` (P017) lowers to the runtime's
        // raw-clone threads.** One `gabbro_faden_start` per root on the
        // file-scope stack of its own site (`gabbro_stapel_<lo>_<i>`,
        // emitted beside the tables), then one `gabbro_faden_warte` per
        // root: every spawn precedes every join, so the roots overlap, and
        // the starter proceeds only after all of them have exited. The
        // checker bills the SUM of the roots' costs (F4) -- the sum is the
        // bound that holds on any number of cores.
        //
        // A spawn this statement cannot make is refused by name, never
        // guessed: an unresolvable root, one with no body in this unit, one
        // taking parameters or answering a result, and a root twice in one
        // statement (the second spawn would overwrite the first join word
        // and leave its thread unjoined -- `N459` owns that shape in the
        // checker). What the checker owns beyond the mechanics -- one owner
        // per thread (`N460`), no held lock across the join (`N461`), pool
        // safety (`N462`) -- stays the checker's; the emitter runs on the
        // parsed tree, and lowering an unchecked shape is the counterfactual
        // the `allein` probes rely on.
        //
        // A refused spawn has no lowering beside it (nothing is started, so
        // nothing honest could stand there); a made one traps LOUDLY when
        // the kernel refuses it (`__builtin_trap` on the same line as the
        // condition, the `trap-guard` row of the C-form census). There is no
        // error channel in the statement, so running on with unstarted roots
        // would be the silent wrong answer.
        StmtArt::Start(st) => {
            let mut wurzeln: Vec<String> = Vec::new();
            let mut gesehen: BTreeSet<String> = BTreeSet::new();
            let mut unbrauchbar: Option<String> = None;
            if st.roots.is_empty() {
                unbrauchbar = Some(String::new());
            }
            for w in &st.roots {
                let kurz = w
                    .teile
                    .last()
                    .map(|i| i.text.clone())
                    .unwrap_or_default();
                let brauchbar = u.funktionen.get(&kurz).is_some_and(|sig| {
                    u.impl_funktionen.contains(&kurz)
                        && sig.geist_param.is_empty()
                        && sig.rueck.is_none()
                }) && gesehen.insert(kurz.clone());
                if brauchbar {
                    wurzeln.push(kurz);
                } else {
                    unbrauchbar = Some(kurz);
                    break;
                }
            }
            if let Some(schlecht) = unbrauchbar {
                let welche = if schlecht.is_empty() {
                    "no roots".to_string()
                } else {
                    format!("`{schlecht}`")
                };
                weigere(
                    absagen,
                    s.span,
                    &format!(
                        "`start` has no lowering for {welche} -- every root is a nullary \
                         `impl fn` of this unit with no result, named once per statement; \
                         the roots {} name no C call this unit could make",
                        st.roots
                            .iter()
                            .map(|w| format!("`{}`", w.text()))
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                );
                return;
            }
            let lo = s.span.von;
            for (i, name) in wurzeln.iter().enumerate() {
                aus.push_str(&format!(
                    "{e}/* start {name} -- a runtime thread on our own raw clone\n\
                     {e} * (`laufzeit/faden.c`); joined below before the starter proceeds. */\n\
                     {e}if (gabbro_faden_start({name}, gabbro_stapel_{lo}_{i} + 65536u, \
                     &gabbro_wort_{lo}_{i}) != 0) __builtin_trap();\n"
                ));
            }
            for i in 0..wurzeln.len() {
                aus.push_str(&format!(
                    "{e}gabbro_faden_warte(&gabbro_wort_{lo}_{i});\n"
                ));
            }
        }
        // **Lane 257: `grow A by n else { … };` has no lowering in this
        // template.** The commit call (`gabbro_arena_grow`, `laufzeit/`)
        // and the descriptor land with the arm lane (248's SPEC) -- until
        // then every `grow` falls here, by name, never silently. Emitted
        // beside the refusal is only the comment, so the refusal changes
        // no `cc` verdict.
        StmtArt::Grow(g) => {
            weigere(
                absagen,
                s.span,
                &format!(
                    "`grow` out of arena `{}` has no lowering in this template -- committing \
                     slots below the ceiling is the dynamic arm (`gabbro_arena_grow`); the \
                     commit request names no C call this unit could make",
                    g.tisch.text,
                ),
            );
            aus.push_str(&format!(
                "{e}/* grow -- HANDOFF region: commit slots of {} below its ceiling\n\
                 {e} * (`gabbro_arena_grow`); at run time this is the runtime's half.\n\
                 {e} */\n",
                g.tisch.text,
            ));
        }
    }
}

/// **`retry` -- die Schleife, deren Bedingung von der WELT abhaengt.**
///
/// Drei Teile, und jeder traegt eine Zusage der Deklaration ins C:
///
/// * `until <pred>` wird die Abbruchbedingung,
/// * `bounded N ops` wird ein **Durchgangszaehler** gegen `floor(N / Kosten-je-Durchgang)`,
/// * `on_exceeded X` wird der **benannte** Ausgang -- D11 woertlich: *wer eine Kapazitaet
///   einfuehrt, muss den Ueberlauf NENNEN.*
///
/// `X` muss `-> never` sein. Zeigt `on_exceeded` auf einen `reason`-Wert, braeuchte es eine
/// Fehlerrueckgabe-Konvention -- **und die ist nicht entschieden**, also wird abgelehnt.
fn retry(
    r: &Retry,
    s: &Stmt,
    aus: &mut String,
    u: &Namen,
    absagen: &mut Absagen,
    tiefe: usize,
    austritt: &Austritt,
) {
    let e = einzug(tiefe);
    let Some(bis) = &r.bis else {
        weigere(absagen, s.span, "`retry` without `until` -- nothing bounds the condition");
        return;
    };
    // **A quantifier is not a run time condition, and the sentence below does not say
    // so (lane-140).** `pred_c` answers `None` for a `forall`/`exists` in an `until`,
    // and the arm below reports "`until` predicate form" -- true, and silent about
    // WHICH form. A loop condition runs every pass; a quantifier would need a loop of
    // its own inside it, at a cost the `costs` pass never counted. Name it here, before
    // the generic arm erases the shape: where no quantifier stands, nothing changes --
    // `pred_c` still refuses the other four forms with the old sentence.
    if enthaelt_quantor(bis) {
        weigere(
            absagen,
            s.span,
            "`until` over a quantifier (`forall`/`exists`) -- the condition runs every \
             pass, and a quantifier would need a loop inside the condition at a cost \
             the `costs` pass never counted. A quantifier is proved, not evaluated (W6)",
        );
        return;
    }
    let Some(bedingung) = pred_c(bis, u, absagen) else {
        weigere(absagen, s.span, "`until` predicate form");
        return;
    };
    let Some(gaenge) = u.retry_schranke.get(&r.span.von) else {
        weigere(
            absagen,
            s.span,
            "`bounded … ops` -- the per-pass cost is not fixed, so the budget yields no \
             iteration count",
        );
        return;
    };
    let ausgang = &r.bei_ueberschreitung.text;
    if !u.funktionen.get(ausgang).is_some_and(|s| s.nie_rueck) {
        weigere(
            absagen,
            r.bei_ueberschreitung.span,
            "`on_exceeded` must name a function returning `never` -- a `reason` value would \
             need an error-return convention, and that is not decided",
        );
        return;
    }
    let z = format!("_r{tiefe}");
    // **`leave`/`next` at a `retry` label -- the same shape `forever` already carries, and
    // for the same reason** (`messung/ERZEUGERREST.md` D21, found 2026-09-03).
    //
    // `schleifen.rs::mit_marke` registers a `retry`'s label for `S001` right beside a
    // `forever`'s -- its own comment says *"`retry`/`forever` take one"* -- so the checker
    // accepts `leave`/`next` naming a `retry` with zero errors. Until this fix, this
    // function never pushed that label into `austritt.schleifen` and never emitted the
    // `_weiter`/`_ende` labels `forever` writes below -- so a checker-clean program fell at
    // `C001: no lowering: 'leave'/'next' naming no enclosing loop`, the emitter's own
    // internal contradiction: the checker's word and the emitter's registration disagreed
    // about a form the grammar gives both loop kinds. See
    // `messung/proben/probe-marke-an-retry-und-traverse.gab`.
    let marke = match &r.marke {
        Some(m) => m.text.clone(),
        None => format!("_r{}", r.span.von),
    };
    let (hat_leave, hat_next) = sprungziele(&r.rumpf, &marke);
    let mut innen = austritt.clone();
    innen.schleifen.push((marke.clone(), austritt.freigaben.len()));
    // **CForm schleifeStmt + schrittStmt (lane 142, re-repaired lane 73): `for` and `+= 1`.**
    // `for` is the loop the target list admits (`BEWEIS.md` §1: `for (counting
    // loop)`); `while` was lowered away on purpose and stays lowered away -- a
    // `while` wait would widen the C semantics Gabbro must one day formalise
    // (`zaehle-c-formen.py` MARKE_TABELLE/MARKE_UNERLAUBT rose 67/32 to 68/33
    // on exactly that form).
    //
    // The lane-142 `for (; !(cond); )` drew clang's `-Wfor-loop-analysis` where
    // the condition names a value no statement of the body writes (measured
    // 2026-09-12: `beispiele/66-transport-rueckgabe.gab`, parameter `bereit`;
    // clang 18.1.3 fires, gcc 13.3.0 stays silent, at `-O0` and `-O2`). That
    // warning fires exactly when NO variable of the condition is modified in
    // the body or the increment -- so the watchdog counter moves into the
    // header AND the condition: `for (; !(cond) && z < N; z += 1)`. The counter
    // IS a condition variable now, and both families are silent (measured over
    // the exact skeleton, empty and non-empty body, `-O0` and `-O2`).
    //
    // The bound arm leaves the loop and stands after it: `if (z >= N && !(cond))
    // { exit(); }`. Case by case against the old in-loop arm (`if (z >= N)`
    // inside, checked after the condition each pass): the body still runs at
    // most N times (iterations z=0..N-1); N=0 still exceeds without a body;
    // `leave` still jumps past the arm (`_ende:` stands after the block, as
    // before); `return` still leaves the function. The one deliberate
    // difference from the review sketch (`if (!(cond))` unconditional): the
    // bound-first order re-samples the condition ONLY on the bound path -- on
    // the early-exit path z<N short-circuits it, so that path evaluates the
    // condition exactly as often as the old loop did (bodies+1). The condition
    // may call (`schritt(k) == 9`) or read volatile state; sampling it once
    // more than necessary is a semantic change, not a spelling one.
    // The `exchange` CAS loop keeps its `++` -- a sibling-owned arm, out of
    // scope for this lane.
    aus.push_str(&format!(
        "{e}{{\n{e}    uint32_t {z} = 0;\n{e}    for (; !({bedingung}) && {z} < {gaenge}u; {z} += 1) {{\n"
    ));
    for k in &r.rumpf.anweisungen {
        anweisung(k, aus, u, absagen, tiefe + 2, &innen);
    }
    if hat_next {
        aus.push_str(&format!("{e}    {marke}_weiter: ;\n"));
    }
    aus.push_str(&format!("{e}    }}\n"));
    aus.push_str(&format!(
        "{e}    if ({z} >= {gaenge}u && !({bedingung})) {{ {ausgang}(); }}\n{e}}}\n"
    ));
    if hat_leave {
        aus.push_str(&format!("{e}{marke}_ende: ;\n"));
    }
}

/// **Lane 170 -- the declarator of a (possibly nested) array type, as SPELLED.**
///
/// A struct field keeps the declaration's spelling (`bytes : [u8; KAP]`
/// becomes `uint8_t bytes[KAP];`, the length the writer named). C spells the
/// lengths BEHIND the name (`uint32_t m[3][4]`), so no type-before-name word
/// (`ctyp`) can carry them -- the same reason every array site already
/// special-cases `TypExpr::Feld`. This is the one home of the nested
/// spelling: the innermost element's C word plus the `[n]` of every
/// dimension, outermost first. `None` where any dimension's length is not a
/// length this unit can spell (`feldlaenge`), or the innermost element has
/// no C word -- and the caller turns the `None` into `C001` by name, never
/// into a guess.
///
/// A `static` does NOT read here: it spells its lengths as VALUES (the
/// number `konst_oder_name` folds, not the `const` name), the way `count N`
/// and every other emitter length does -- `feldstatisch` builds that suffix
/// beside its bounds, out of the same numbers. Two conventions, and each
/// site keeps the one it always read: spelling here, value there.
fn feld_deklarator(t: &TypExpr, u: &Namen) -> Option<(String, String)> {
    let mut tiefen = Vec::new();
    let mut rest = t;
    while let TypExpr::Feld(a) = rest {
        tiefen.push(feldlaenge(&a.laenge, u)?);
        rest = &a.element;
    }
    if tiefen.is_empty() {
        return None;
    }
    let wort = ctyp(rest, u)?;
    let mut suffix = String::new();
    for n in tiefen {
        suffix.push_str(&format!("[{n}]"));
    }
    Some((wort, suffix))
}

/// One scalar fill over nested dimensions: `{{7, 7}, {7, 7}}`. The caller
/// holds the byte budget, so every depth here terminates inside it.
fn fülle(tiefe: usize, laengen: &[usize], text: &str, aus: &mut String) {
    aus.push('{');
    for i in 0..laengen[tiefe] {
        if i > 0 {
            aus.push_str(", ");
        }
        if tiefe + 1 == laengen.len() {
            aus.push_str(text);
        } else {
            fülle(tiefe + 1, laengen, text, aus);
        }
    }
    aus.push('}');
}

/// **Ein `static` ueber einem Feld: `static mut kernlast : [Zaehler; 64] = 0;`**
/// (2026-08-20). Lane 170 carries the nested spine with it: `[[u32; 4]; 3]`
/// lowers through `feld_deklarator` to `uint32_t M[3][4]`, one dimension per
/// `[n]`, outermost first.
///
/// Bis heute sagte der Erzeuger dazu *„`static` of an unresolvable type"* -- und das war eine
/// Weigerung, die den falschen Grund nannte. `[Zaehler; 64]` ist bestens aufloesbar: das
/// Element ist ein Bereichstyp ueber `u32`, die Laenge eine Konstante. **Was fehlte, war
/// nicht die Aufloesung, sondern die Deklaratorform.**
///
/// **Der Anfangswert ist der Punkt, an dem hier eine Entscheidung faellt.** `= 0` ueber einem
/// Feld heisst in Gabbro *jeder Platz null*. In C heisst `= {0}` dasselbe -- aber `= {5}`
/// heisst **nicht** *jeder Platz fuenf*, sondern *der erste fuenf, der Rest null*. Die
/// beiden Lesarten fallen genau bei der Null zusammen.
///
/// > *Also wird die Null als `{0}` geschrieben und jeder andere Wert AUSGESCHRIEBEN.* Beides
/// > ist exakt; geraten wird nichts. Ein `{5}` hinzuschreiben und es *jeder Platz fuenf* zu
/// > nennen waere die eine Sorte Fehler, gegen die dieses Modul gebaut ist -- er uebersetzt,
/// > und er rechnet etwas anderes.
fn feldstatisch(
    st: &StatischDecl,
    aus: &mut String,
    u: &Namen,
    absagen: &mut Absagen,
) {
    // The dimensions as VALUES, outermost first -- and FIRST, because the
    // refusal below names the length and the one after it the element: a
    // length no unit can read (`[u32; 2 + 2]`) is "not constant", not
    // "unresolvable", the same order the one-dimensional form always read.
    // The spellings beside them may name a `const`, and the bounds below
    // compute. Like `count`: a number OR a `const` name, with the value
    // standing in `konstwert`.
    let mut laengen: Vec<i128> = Vec::new();
    let innerste: &TypExpr;
    {
        let mut rest = &st.typ;
        while let TypExpr::Feld(x) = rest {
            let Some(n) = konst_oder_name(&x.laenge, u) else {
                weigere(absagen, st.name.span, "`static` array whose length is not constant");
                return;
            };
            if n <= 0 {
                weigere(
                    absagen,
                    st.name.span,
                    "`static` array of length zero -- C has no such object",
                );
                return;
            }
            laengen.push(n);
            rest = &x.element;
        }
        innerste = rest;
    }
    let Some(elem) = ctyp(innerste, u) else {
        weigere(absagen, st.name.span, "`static` array over an unresolvable element type");
        return;
    };
    // The declarator suffix out of the same numbers: `[[u32; 4]; 3]` becomes
    // `M[3][4]`, and at one dimension `[64]` -- the value, not the `const`
    // name that may have spelled it, exactly what this form always wrote.
    let mut suffix = String::new();
    for n in &laengen {
        suffix.push_str(&format!("[{n}]"));
    }
    // The element count of the whole object: every bound below reads it, at
    // one dimension it IS the length above. Saturating: past the object fence
    // the exact count no longer matters, only that it is past it.
    let gesamt = laengen
        .iter()
        .fold(1u128, |a, n| a.saturating_mul(*n as u128));
    // **`D5`: a length C can read exactly, in a declaration C cannot hold** (2026-09-03).
    //
    // `[u64; 2^63 - 1]` is accepted by every pass -- the length is a `u64` and fits -- and
    // the emitter wrote it out as the array bound. `cc` answered *size of array `A` exceeds
    // maximum object size 9223372036854775807*, and that number is `PTRDIFF_MAX`: C requires
    // the difference of two pointers into one object to be representable, so an object may
    // not be larger than `ptrdiff_t` can span. **The bound is on BYTES and not on elements**,
    // which is why the width is read here rather than the count compared directly.
    //
    // > *`gift/602` is the neighbour, and the pair is the point.* That one carried a length
    // > the emitter READ WRONG (`2^128 - 1` came back as `-1`); this one carries a length it
    // > reads exactly right and writes into a C declaration that cannot exist. **A lossy
    // > conversion and a missing bound, out of the same slot of the same grammar rule.**
    //
    // An unknown element width counts as ONE byte -- the smallest any C object has -- so the
    // rule under-refuses rather than over-refuses where it cannot see the size. *That is the
    // safe direction here: what it lets through, `cc` still catches.*
    //
    // Lane 170: the bound is on the WHOLE object, so a `[3]` of `[u32; 4]` counts
    // twelve elements, not three -- at one dimension `gesamt` is the length above
    // and the line below reads exactly what it always read.
    let elembreite = cbreite(&elem).unwrap_or(1);
    if gesamt.saturating_mul(elembreite) > C_OBJEKT_MAX {
        weigere(
            absagen,
            st.name.span,
            &format!(
                "`static` array of {gesamt} x {elembreite} bytes -- C's largest object spans \
                 `PTRDIFF_MAX` = {C_OBJEKT_MAX} bytes, because the difference of two pointers \
                 into one object has to be representable. There is no C declaration for this"
            ),
        );
        return;
    }
    let Some(w) = konst_zahl(&st.wert) else {
        weigere(absagen, st.name.span, "`static` array with a non-constant initialiser");
        return;
    };
    let anfang = if w == 0 {
        "{0}".to_string()
    } else {
        // **`D12`: the emitter's THIRD answer, and it was a length that halts nothing**
        // (2026-09-03). `beispiele/gift/662`.
        //
        // `[u64; 10^8] = 7` is far inside `PTRDIFF_MAX`, so `D5` above says nothing -- and
        // the line below writes a hundred million elements one at a time. **Measured on
        // this tree: 0.091 s at 10^6, 0.868 s at 10^7, 8.51 s at 10^8** -- linear, about
        // 85 ns and 190 bytes of resident memory per element. At the largest length `D5`
        // still allows for a `u64` that is about three thousand years.
        //
        // > *And the same slot has a second face.* Past
        // > `isize::MAX / size_of::<String>()` the `collect` reserves its slots up front
        // > and `raw_vec` answers *capacity overflow* -- a panic instead of a hang, two
        // > milliseconds instead of an age. **One hole, two third answers, one fence.**
        //
        // **The fence is on BYTES OF OUTPUT and not on a count, because bytes are what
        // does not halt.** The count alone cannot say it: one element of `7` costs three
        // characters and one of `-2^127` costs forty-two, a factor of fourteen at the same
        // length. The size is computed exactly here, before anything is built.
        //
        // WHY A NUMBER AT ALL, AND WHY THIS ONE
        // -------------------------------------
        // **C gives no limit to borrow.** A translation unit may hold as many initialiser
        // elements as the implementation can stand; the bound is patience and memory, and
        // neither is in the standard. So the number is this emitter's and is written here
        // with what it costs.
        //
        // **And the other two ways out were checked before this one was chosen.**
        //
        // * *A repeat form.* `{ [0 ... 9] = 7 }` is a GNU extension. Measured with the
        //   tree's own compile gate: silent under `-std=c11 -Wall -Wextra -Werror`, and
        //   under one switch more -- *ISO C forbids specifying range of elements to
        //   initialize* `[-Werror=pedantic]`. That switch is net 5 of
        //   `instrumente/fuzze-erzeuger.py`, so taking this road would trade a hang for a
        //   finding in the same tool.
        // * *A loop at run time.* A `static` initialiser has to be a constant expression;
        //   filling the array from an init function moves the work to a moment this
        //   language does not have. **That is a change to what `= 7` MEANS**, and the
        //   comment above this function was written precisely to keep the two readings of
        //   `= 5` apart.
        //
        // **The headroom, measured over the whole corpus and not estimated.** 612 versioned
        // `.gab`/`.gabi`; eleven declare an array `static`, and the lengths of every array
        // of any kind in the tree are 8, 10, 32, 64, 256 and 512. The largest array
        // `static` is `[Zaehler; 64]` (`beispiele/08`) and `[u8; KAP]` with `KAP = 64`
        // (`beispiele/64`). **Every one of them is `= 0`, so not one reaches this branch at
        // any length.**
        //
        // One mebibyte therefore leaves 349 525 elements at a one-digit value and 24 966 at
        // the widest literal Gabbro has -- **5 461 times and 390 times the largest array
        // `static` in the corpus**, and 682 times / 48 times the largest array of any kind.
        // A megabyte of initialiser text costs about 30 ms at the rate measured above.
        // *A limit a real program hits is worse than the defect; this one is not within
        // three decimal orders of any program in this tree.*
        //
        // Lane 170: a nested fill nests its braces (`{{7, 7}, {7, 7}}`), and the
        // budget counts every element of every dimension -- at one dimension the
        // shape below is byte-identical to the `{7, …}` it replaces.
        let text = w.to_string();
        // `+ 2` for the `, ` between two elements. The last element carries none, so this
        // over-counts by exactly two bytes -- the refusal fires two bytes early rather than
        // two bytes late, which is the direction with the second reader still behind it.
        // (Nested braces add two bytes per row on top; the two-byte headroom above
        // covers them wherever more than one row stands.)
        let bytes = gesamt.saturating_mul(text.len() as u128 + 2);
        if bytes > C_INITIALISIERER_MAX {
            weigere(
                absagen,
                st.name.span,
                &format!(
                    "`static` array of {gesamt} elements initialised to {w} -- C has no repeat \
                     form for an initialiser that ISO C also has, so this emitter writes \
                     one element per element and that text would be {bytes} bytes. This \
                     emitter's budget for one initialiser is {C_INITIALISIERER_MAX}. \
                     `= 0` carries no such cost at any length: it lowers to `{{0}}`"
                ),
            );
            return;
        }
        // **`try_from` and not `as`** -- the budget above bounds every dimension by
        // about a million, so the conversion cannot fail on a tree that reached
        // this line; a number that did not fit would be a truncation, and this
        // file does not truncate numbers (`konst_zahl`, `D3`/`D4`).
        let mut tiefen: Vec<usize> = Vec::with_capacity(laengen.len());
        for n in &laengen {
            let Ok(n) = usize::try_from(*n) else {
                weigere(
                    absagen,
                    st.name.span,
                    "`static` array dimension past the addressable count -- the \
                     initialiser budget above already fenced it",
                );
                return;
            };
            tiefen.push(n);
        }
        let mut gefuellt = String::new();
        fülle(0, &tiefen, &text, &mut gefuellt);
        gefuellt
    };
    let konst = if st.veraenderlich { "" } else { "const " };
    let abschnitt = abschnitt_attribut(st, absagen);
    aus.push_str(&format!(
        "\nstatic {konst}{elem} {}{suffix}{abschnitt} __attribute__((unused)) = {anfang};\n",
        st.name.text
    ));
}

/// **`forever` senkt ab, und «B11» war beim Erzeuger stehengeblieben** (2026-08-20).
///
/// Die Weigerung, die bis heute hier stand, nannte zwei Gruende. **Der zweite war nicht mehr
/// wahr:**
///
/// > *«B11»: there is no exit either.*
///
/// `leave` und `next` stehen laengst in der Grammatik -- `beispiele/04` schreibt `leave
/// dienst`, `S001` haelt die Marke gegen die umschliessenden Schleifen, und
/// `gift/10-marke-fehlt.gab` prueft genau das seit Monaten. **Eine Absage, die eine
/// geschlossene Luecke zitiert, hindert ein Programm, fuer das der Grund nicht mehr gilt** --
/// und niemand merkt es, weil die Absage aussieht wie eine Entscheidung.
///
/// **Der erste Grund gilt und wird nicht weggeraeumt, sondern eingeloest.** `per_pass bounded
/// N ops` ist eine Aussage ueber EINEN Durchgang, und die rechnet der Kostenpass zur
/// Uebersetzungszeit nach (W6). Zur Laufzeit ist da nichts zu zaehlen, also bekommt
/// `on_exceeded` **keinen Zweig**. Was es bekommt, ist mehr als der Kommentar, den die alte
/// Weigerung fuerchtete:
///
/// ```c
/// static void (*const dienst_wachhund)(void) __attribute__((unused)) = watchdog_schlug_an;
/// ```
///
/// **Der C-Uebersetzer liest die Klausel damit ein zweites Mal** -- derselbe Griff, mit dem
/// `-Wswitch` zum zweiten Leser von `D005` wurde. Der Name muss existieren und die Gestalt
/// eines Ausgangs haben; wer den Wachhund umbenennt, bricht den Bau. *Eine Klausel, die
/// still fallengelassen wird, ist ein Ritus; eine, die der Uebersetzer nachliest, ist keiner.*
fn forever(
    x: &Forever,
    aus: &mut String,
    u: &Namen,
    absagen: &mut Absagen,
    tiefe: usize,
    austritt: &Austritt,
) {
    let e = einzug(tiefe);
    // **Dieselbe Zusage wie beim `retry`, und aus demselben Grund.** Kehrte der Wachhund
    // zurueck, liefe die Schleife weiter -- die Schranke waere eine Zahl ohne Folge.
    let ausgang = &x.bei_ueberschreitung.text;
    if !u.funktionen.get(ausgang).is_some_and(|s| s.nie_rueck) {
        weigere(
            absagen,
            x.bei_ueberschreitung.span,
            "`on_exceeded` must name a function returning `never` -- a `reason` value would \
             need an error-return convention, and that is not decided",
        );
        return;
    }
    // Ohne Marke kann kein `leave` sie nennen; der Wachhund braucht trotzdem einen Namen.
    let marke = match &x.marke {
        Some(m) => m.text.clone(),
        None => format!("_f{}", x.span.von),
    };
    aus.push_str(&format!(
        "{e}/* forever {marke} -- `per_pass … ops` is a claim about ONE pass, and the cost\n\
         {e} * pass has already checked it (W6). Nothing counts here at run time, so\n\
         {e} * `on_exceeded` gets no branch -- it gets the line below instead, which makes\n\
         {e} * the C compiler read the clause a second time.\n"
    ));
    if let Some(f) = &x.fortschritt {
        aus.push_str(&format!(
            "{e} * `progress {}` is an assumption about the WORLD; nothing static\n\
             {e} * establishes it, and `{ausgang}` is its falsifier.\n",
            f.text
        ));
    }
    if !x.verlaesst.is_empty() {
        aus.push_str(&format!(
            "{e} * `leaves {}` names the LINEAR values that leave here; that they leave\n\
             {e} * exactly once is M2's statement, already made.\n",
            x.verlaesst.iter().map(|i| i.text.clone()).collect::<Vec<_>>().join(", ")
        ));
    }
    aus.push_str(&format!("{e} */\n"));
    aus.push_str(&format!(
        "{e}static void (*const {marke}_wachhund)(void) __attribute__((unused)) = {ausgang};\n"
    ));
    // **Nur die Marken, die wirklich angesprungen werden** -- `-Wunused-label` ist unter
    // `-Werror` ein Fehler, und ein Erzeugnis, das nicht uebersetzt, ist keines.
    let (hat_leave, hat_next) = sprungziele(&x.rumpf, &marke);
    let mut innen = austritt.clone();
    innen.schleifen.push((marke.clone(), austritt.freigaben.len()));
    aus.push_str(&format!("{e}for (;;) {{\n"));
    for k in &x.rumpf.anweisungen {
        anweisung(k, aus, u, absagen, tiefe + 1, &innen);
    }
    if hat_next {
        aus.push_str(&format!("{e}    {marke}_weiter: ;\n"));
    }
    aus.push_str(&format!("{e}}}\n"));
    if hat_leave {
        aus.push_str(&format!("{e}{marke}_ende: ;\n"));
    }
}

/// Wird diese Marke im Rumpf ueberhaupt angesprungen -- als `leave`, als `next`?
///
/// **Eine Marke, die niemand nennt, darf nicht im C stehen**: `-Wunused-label` faellt unter
/// `-Werror`. *Der Erzeuger schreibt nur, was gebraucht wird -- und zaehlt es, statt es zu
/// vermuten.* Eine gleichnamige Schleife weiter innen faengt die Marke ab; darum bricht der
/// Abstieg dort ab.
fn sprungziele(b: &Block, marke: &str) -> (bool, bool) {
    let (mut raus, mut weiter) = (false, false);
    fn im_block(b: &Block, marke: &str, raus: &mut bool, weiter: &mut bool) {
        for s in &b.anweisungen {
            match &s.art {
                StmtArt::Leave(m) if m.text == marke => *raus = true,
                StmtArt::Next(m) if m.text == marke => *weiter = true,
                // Ein `leave`/`next` auf eine ANDERE Marke -- es springt, aber nicht hier
                // heraus. Die Marke, auf die es zielt, fragt sich selbst.
                StmtArt::Leave(_) | StmtArt::Next(_) => {}
                // **Und die sechzehn, die ueberhaupt nicht springen -- einzeln.** Der
                // Abstieg darunter kommt von `crate::unterbloecke`, und das erzwingt fuer
                // eine neue `StmtArt` nur die Frage *„traegst du einen Block?"*. Ob sie
                // SPRINGT, fragt es nicht -- und ein neues `goto` waere hier stumm
                // durchgefallen, waehrend `-Wunused-label` dann eine Marke meldet, die sehr
                // wohl angesprungen wird. (**Fuenfzehn** bis lane E1; ein Bibliothekruf
                // springt so wenig wie ein Ruf. **Achtzehn** seit «E4»: `alloc` and
                // `reset` lower to straight-line C and never jump.)
                // **Lane O-1:** `child` itself jumps nowhere -- a `leave` /
                // `next` inside it names an outer loop, and the descent
                // below reaches it through `unterbloecke` like at every
                // other block form.
                StmtArt::Child(_)
                // **Lane 253:** `start` itself jumps nowhere and carries no
                // block for the descent below.
                | StmtArt::Start(_)
                // **Lane 257:** `grow` itself jumps nowhere; a `leave` /
                // `next` inside its `else` names an outer loop, reached
                // through `unterbloecke` like at `child` above.
                | StmtArt::Grow(_)
                | StmtArt::Let(_)
                | StmtArt::Alloc(_)
                | StmtArt::ResetArena(_)
                | StmtArt::LetSonst(_)
                | StmtArt::Zuweisung(_)
                | StmtArt::Wenn(_)
                | StmtArt::Match(_)
                | StmtArt::Schleife(_)
                | StmtArt::Bricht(_)
                | StmtArt::Narrow(_)
                | StmtArt::Sperrt(_)
                | StmtArt::Observiert(_)
                | StmtArt::Publish(_)
                | StmtArt::AwaitLoad(_)
                | StmtArt::Exchange(_)
                | StmtArt::Return(_)
                | StmtArt::Ruf(_)
                | StmtArt::LibraryCall(_) => {}
            }
            // Eine innere Schleife DERSELBEN Marke verdeckt sie -- `S001` bindet an die
            // naechste, und das Erzeugnis muss dieselbe Bindung treffen.
            if let StmtArt::Schleife(sch) = &s.art {
                let eigen = match sch.as_ref() {
                    Schleife::Forever(f) => f.marke.as_ref().map(|i| i.text.as_str()),
                    Schleife::Retry(r) => r.marke.as_ref().map(|i| i.text.as_str()),
                    Schleife::Traverse(_) => None,
                };
                if eigen == Some(marke) {
                    continue;
                }
            }
            for k in crate::unterbloecke(s) {
                im_block(k, marke, raus, weiter);
            }
        }
    }
    im_block(b, marke, &mut raus, &mut weiter);
    (raus, weiter)
}

/// **Ein Rumpf, dessen `return` ein WERT ist und kein Austritt.**
///
/// Der `update`-Rumpf eines `exchange` rechnet alt -> neu; sein `return v + 1` verlaesst
/// nicht die Funktion, sondern **liefert den neuen Wert**. Das ist die eine Stelle, an der
/// `return` in dieser Sprache etwas anderes heisst als sonst -- und darum steht die
/// Uebersetzung hier und nicht in `anweisung`, wo ein `return` Sperren freigibt und aus der
/// Funktion springt.
///
/// *Abgesenkt werden genau die Formen, die ein reiner Rechenrumpf braucht:* `return <expr>`
/// und `if <expr> { … }`. Alles andere wird abgelehnt -- **ein Rumpf mit Wirkung waere kein
/// reiner Rumpf**, und dass er rein ist, ist die Voraussetzung dafuer, ihn bei verlorenem
/// Wettlauf noch einmal zu rechnen.
fn rumpf_als_wert(
    b: &Block,
    ziel: &str,
    aus: &mut String,
    u: &Namen,
    absagen: &mut Absagen,
    tiefe: usize,
) {
    let e = einzug(tiefe);
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Return(Some(w)) => {
                aus.push_str(&format!("{e}{ziel} = {}; goto {ziel}_fertig;\n", ausdruck(w, u, absagen)));
            }
            StmtArt::Wenn(w) if w.sonst.is_none() && w.zweige.len() == 1 => {
                let (bed, rumpf) = &w.zweige[0];
                aus.push_str(&format!("{e}if ({}) {{\n", ausdruck(bed, u, absagen)));
                rumpf_als_wert(rumpf, ziel, aus, u, absagen, tiefe + 1);
                aus.push_str(&format!("{e}}}\n"));
            }
            _ => weigere(
                absagen,
                s.span,
                "statement in an `update` body -- it computes old -> new and is PURE; only \
                 `return <expr>` and `if <expr> { … }` say that",
            ),
        }
    }
}

/// **One arm of the fetch table: the C name, and the operand that rides in it.**
///
/// `ruf` is the FULL C function name and is never assembled from parts -- an
/// emitter that builds `atomic_fetch_` + a word can build a word nobody wrote.
struct Holform<'a> {
    ruf: &'static str,
    operand: &'a Expr,
}

/// **The declared element type of the atomic an `exchange` stands on (lane 221).**
///
/// A scalar atomic answers with its own declaration; an indexed one (`REGEL[r]`
/// over `atomic REGEL : [u32; 256]`) with the ELEMENT's, the same choice
/// `atom_target` and `Namen::atomics` make. `None` is the loop, never a guess.
fn atom_elem_typ(o: &Ort, u: &Namen) -> Option<TypExpr> {
    if o.suffixe.is_empty() {
        return u.atomic_elem_typs.get(&o.basis.text).cloned();
    }
    if o.suffixe.len() == 1 && matches!(o.suffixe[0], OrtSuffix::Index(_)) {
        return u.atomic_elem_typs.get(&o.basis.text).cloned();
    }
    None
}

/// **The fetch-add gate: `(bits, n)` of a `binder +% m` / `binder -% m` site
/// (lane 221).** Mirrors the checker's `M153` rule through the same three
/// helpers the general wrap lowering uses (`storage`, `intty_interval`,
/// `exact_wrap_n`), with the binder's type read off the ATOMIC's declaration
/// (`atom_elem_typ`) instead of off a static or parameter -- the one place the
/// range IS readable for a name that lives only inside the loop the fetch
/// would remove (`OPUS-BERICHT-FETCHADD.md` §2.3).
///
/// The operand answers the same question `wrap_form` asks a literal side: it
/// must be a translation-time constant in `0 .. 2^N - 1` (a runtime operand is
/// evaluated once as a fetch and once per pass as a loop -- the row-9 reason
/// `holform` keeps, so a parameter or `let` never passes here).
///
/// **`None` is the loop (or `C001` further down), never a guessed modulus.**
/// In particular `n != bits` refuses: `+%` wraps at the operands' EXACT range,
/// and where that range is narrower than the storage word (`u32 in 0 .. 65535`,
/// modulus 2^16) the general lowering masks (`wrap_c`) while `atomic_fetch_add`
/// would wrap at 2^32 -- a DIFFERENT operation, silently. The accepted cases
/// are exactly those where the general lowering would emit the UNMASKED form,
/// plain C unsigned arithmetic, which C11 6.2.5p9 defines as modulo 2^N --
/// the same operation `atomic_fetch_add` names. *The gate does not argue the
/// modulus equals the width; it checks it, and the check below is the whole
/// soundness argument.*
fn holwrap_form(binder_typ: &TypExpr, operand: &Expr, u: &Namen) -> Option<(u32, u32)> {
    let TypExpr::Int(i) = binder_typ else {
        return None;
    };
    let (bits, signed) = storage(i)?;
    if signed {
        return None;
    }
    let (lo, hi) = intty_interval(i, u)?;
    let n = crate::typen::exact_wrap_n(&crate::typen::IntBereich::genau(
        bits as u8, false, lo, hi,
    ))?;
    if n == 0 || n > bits {
        return None;
    }
    let v = constexpr_value(operand, u)?;
    if v < 0 || v > (1i128 << n) - 1 {
        return None;
    }
    if n != bits {
        return None;
    }
    Some((bits, n))
}

/// **`SPRACHE.md` Part III §1 promised `atomic_fetch_*` and the emitter had only
/// the loop -- this is the table that decides which is which** (2026-09-15).
///
/// The promise, word for word: *"`atomic_fetch_*` where the `update` body
/// corresponds to a primitive (matched against a closed pattern table: `t+1`,
/// `t-1`, `t|m`, `t&m`, `max` via `accumulates`), otherwise the **bounded** CAS
/// loop"*. Lane 201 measured what stood here instead: **every** body lowered to
/// the loop, the runtime's own ticket lock included, where `CTicket.lean`'s first
/// instruction is ONE wait-free fetch-add. This function is the missing half.
///
/// **What the table contains, and why exactly this much** (each row measured on
/// `probe/p1..p3.gab`, 2026-09-15, before a line of this was written):
///
/// * **`t | m`, `t & m`, `t ^ m` are IN.** They check clean today (`u32 | u8`
///   leaves no range), they are commutative, so which side carries the binder
///   changes nothing, and C11 7.17.7.5 defines `atomic_fetch_or/and/xor` as
///   exactly `*obj = *obj | arg` with the OLD value returned -- which is what
///   `let alt = X exchange update(t) { return t | m; }` binds.
/// * **`t + 1` and `t - 1` are OUT, and not because this table is shy.** They are
///   *unreachable*: an `update` body without a side condition must answer in the
///   atomic's own type for EVERY value the atomic can hold, and checked `±1`
///   shifts the interval by one, so `[lo+1, hi+1] ⊆ [lo, hi]` is false for every
///   non-empty interval. Measured: `atomic NEXT : u32` with `{ return t + 1; }`
///   falls at `M104` + `M101`; a ranged `u32 in 0 .. 1000` falls at `M101` the
///   same way. Nothing this emitter does can change that -- the refusal is M1's
///   and it is right.
/// * **The wrapping forms `t +% m`, `t -% m` are IN through the fetch-add
///   gate (lane 221).** They are the shapes that MATCH C11's fetch-add (which
///   wraps silently by definition), and they are what `laufzeit/sperre.gab`
///   wants -- spelled through a `folge` helper today because the direct form
///   fell at `C001`: `wrap_side`/`ort_typ` resolve a bare name only through
///   statics and parameters, never through an `exchange` binder, so the exact
///   range could not be read. The gate (`holwrap_form`) reads it off the
///   atomic's declaration instead, and accepts exactly where the wrap modulus
///   IS the storage word (`u32`, where fetch-add is exact). Where the range is
///   narrower (`u32 in 0 .. 65535`, where fetch-add would wrap at the WRONG
///   modulus and be a different operation) the refusal stays -- `None` is the
///   loop, and the loop still ends at the same `C001`, narrowed, not lifted.
///   *A fetch-add bought by guessing a modulus is not an improvement.*
///   `messung/muse/OPUS-BERICHT-FETCHADD.md` §2 carries the measurement.
/// * **A body with a side condition stays a loop** -- the whole corpus shape
///   (`if v < GRENZE { return v + 1; } return v;`). It is not one operation and
///   no single instruction computes it.
/// * **The operand must be a translation-time constant and must not be the
///   binder.** In the loop the body is re-run per pass; as a fetch operand it is
///   evaluated once. For a constant those are the same value by construction, and
///   for anything else they are only the same if the emitter reasons about purity
///   -- which it would then be doing silently. `t | t` therefore stays a loop, and
///   so does `t | (1 << i)`: the second is a real shape and a later lane's, not a
///   guess this one makes.
///
/// **A word on "wait-free", because the C comment used to say it.** C11 makes
/// `atomic_fetch_*` ONE read-modify-write operation on the abstract machine, and
/// the emitted C therefore has no loop and no bound. What the TARGET makes of it is
/// the target's business: on x86_64 `add` is `lock xadd`, while `or`/`and`/`xor`
/// with a USED old value have no single instruction and become a `cmpxchg` loop in
/// the code generator. *Removing the bound from the C is the claim this arm makes;
/// wait-freedom at the machine is not, and was not measured (`objdump` is a lane of
/// its own).*
///
/// `typ` is the atomic's C type. Only the eight integer words qualify: C11 defines
/// `atomic_fetch_*` for integer atomics, and `bool`, `float` and `double` have no
/// such instruction. The word list is the one `ganzzahlwort` writes.
/// `binder_typ` is the atomic's DECLARED element type (`atom_elem_typ`) -- the
/// wrapping rows need the declaration, the bitwise rows never look at it.
fn holform<'a>(
    rumpf: &'a Block,
    binder: &str,
    u: &Namen,
    typ: &str,
    binder_typ: Option<&TypExpr>,
) -> Option<Holform<'a>> {
    match typ {
        "uint8_t" | "uint16_t" | "uint32_t" | "uint64_t" | "int8_t" | "int16_t" | "int32_t"
        | "int64_t" => {}
        _ => return None,
    }
    // The body is EXACTLY one `return <expr>;`. A second statement, or an `if`,
    // is a body no single instruction computes -- and `rumpf_als_wert` already
    // holds those.
    let [einzige] = &rumpf.anweisungen[..] else {
        return None;
    };
    let StmtArt::Return(Some(e)) = &einzige.art else {
        return None;
    };
    let ExprArt::Binaer(op, a, b) = &ohne_klammern(e).art else {
        return None;
    };
    // **Spelled out, every one.** A `_ =>` here would silently answer for an
    // operator that does not exist yet, and the one thing this arm must never do
    // is give a body a DIFFERENT operation than the one written.
    //
    // **The binder test stands before both halves**: the bitwise rows need it
    // for the operand side, the wrapping rows need it for the side AND the
    // commutativity question.
    let ist_binder = |x: &Expr| {
        matches!(&ohne_klammern(x).art, ExprArt::Ort(o) if o.suffixe.is_empty() && o.basis.text == binder)
    };
    // **The wrapping rows (lane 221).** `t +% m` is `atomic_fetch_add` and
    // `t -% m` is `atomic_fetch_sub` -- C11 7.17.7.5 defines both as exactly
    // `*obj = *obj +/- arg` with the OLD value returned, wrapping silently,
    // which is what `+%`/`-%` say and what the `let alt = …` binds.
    if matches!(op, BinOp::PlusWrap | BinOp::MinusWrap) {
        let ruf = if matches!(op, BinOp::PlusWrap) {
            "atomic_fetch_add_explicit"
        } else {
            "atomic_fetch_sub_explicit"
        };
        // **Subtraction does not commute, and neither does this row.** `t -% m`
        // computes `X - m`, which is what `atomic_fetch_sub` computes; `m -% t`
        // computes `m - X`, which no fetch computes -- the row-7 reason, so the
        // binder on the right stays a loop. Addition commutes modulo 2^N, so
        // `m +% t` is the same instruction as `t +% m`.
        let operand = if ist_binder(a) && !ist_binder(b) {
            b.as_ref()
        } else if matches!(op, BinOp::PlusWrap) && ist_binder(b) && !ist_binder(a) {
            a.as_ref()
        } else {
            return None;
        };
        // The operand rides once, not once per pass, so it must be a
        // translation-time constant (the row-9 reason, same as the bitwise
        // rows) -- and the modulus must BE the storage width (the gate).
        holwrap_form(binder_typ?, operand, u)?;
        return Some(Holform { ruf, operand });
    }
    let ruf = match op {
        BinOp::BitOder => "atomic_fetch_or_explicit",
        BinOp::BitUnd => "atomic_fetch_and_explicit",
        BinOp::BitXor => "atomic_fetch_xor_explicit",
        // `+`/`-`: unreachable through M1, see the head of this function.
        // `+%`/`-%`: answered above, through the fetch-add gate -- the arms
        // below are unreachable, and the table stays spelled out (no `_`).
        BinOp::PlusWrap | BinOp::MinusWrap => return None,
        // The rest is not a fetch form in any C.
        BinOp::Plus
        | BinOp::Minus
        | BinOp::PlusSat
        | BinOp::Mal
        | BinOp::MalWrap
        | BinOp::Geteilt
        | BinOp::Rest
        | BinOp::SchiebLinks
        | BinOp::SchiebLinksWrap
        | BinOp::SchiebRechts
        | BinOp::Oder
        | BinOp::Und
        | BinOp::Gleich
        | BinOp::Ungleich
        | BinOp::Kleiner
        | BinOp::KleinerGleich
        | BinOp::Groesser
        | BinOp::GroesserGleich => return None,
    };
    // Exactly ONE side is the bare binder; the other is a translation-time
    // constant that is not the binder. All three operators are commutative, so
    // no row of this table depends on which side that is.
    let operand = if ist_binder(a) && !ist_binder(b) && constexpr_value(b, u).is_some() {
        b.as_ref()
    } else if ist_binder(b) && !ist_binder(a) && constexpr_value(a, u).is_some() {
        a.as_ref()
    } else {
        return None;
    };
    Some(Holform { ruf, operand })
}

/// The expression under any number of parentheses. **A shape test that stops at a
/// `(` reads the source's punctuation as its meaning.**
fn ohne_klammern(e: &Expr) -> &Expr {
    match &e.art {
        ExprArt::Klammer(x) => ohne_klammern(x),
        _ => e,
    }
}

/// **The ordering ONE read-modify-write instruction carries, derived from the
/// declaration's two halves and from nothing else.**
///
/// `Namen::atomics` holds the pair the declaration names: the STORE side, and the
/// load side derived from it (`acquire`/`release` both give release/acquire;
/// `seq` gives seq_cst/seq_cst; `relaxed` and a missing word give
/// relaxed/relaxed). A CAS loop can spend those two separately -- it has a load
/// and a store. A fetch instruction has ONE argument and must therefore carry
/// their JOIN, which is `acq_rel` exactly where the declaration asked for a
/// release store and an acquire load.
///
/// **`None` is a CAS loop, not a guess.** A pair this table does not name is a
/// declaration this function has never seen, and the catch-all that would answer
/// for it would be choosing a memory model -- the one defect that does not show up
/// in a test run (see the `Atomic` arm of `sammle_namen`, which was repaired for
/// exactly this).
fn holordnung(speichern: &str, laden: &str) -> Option<&'static str> {
    Some(match (speichern, laden) {
        ("memory_order_relaxed", "memory_order_relaxed") => "memory_order_relaxed",
        ("memory_order_release", "memory_order_acquire") => "memory_order_acq_rel",
        ("memory_order_seq_cst", "memory_order_seq_cst") => "memory_order_seq_cst",
        _ => return None,
    })
}

/// Ein Praedikat als C-Bedingung. **Nur die Formen, die ein `until` heute braucht** -- jede
/// andere wird abgelehnt, statt sie plausibel zu uebersetzen.
///
/// Does this predicate quantify anywhere inside -- at the top or nested under
/// `&&`/`||`/`!`/parentheses? Read by the `retry` lowering before `pred_c`, so that an
/// `until` over a quantifier is refused WITH the quantifier named. Spelled out arm by
/// arm, so a new `PredArt` is a compile error here rather than a silent "no" (the same
/// rule `ausdruecke_im_praedikat` in `lib.rs` holds).
fn enthaelt_quantor(p: &Pred) -> bool {
    match &p.art {
        PredArt::Quantor(_) => true,
        PredArt::Klammer(x) | PredArt::Nicht(x) => enthaelt_quantor(x),
        PredArt::Und(a, b) | PredArt::Oder(a, b) | PredArt::Folgt(a, b) => {
            enthaelt_quantor(a) || enthaelt_quantor(b)
        }
        PredArt::Vergleich(_)
        | PredArt::Element(_, _)
        | PredArt::Erreicht { .. }
        | PredArt::Held { .. } => false,
    }
}

fn pred_c(p: &Pred, u: &Namen, absagen: &mut Absagen) -> Option<String> {
    Some(match &p.art {
        PredArt::Vergleich(e) => ausdruck(e, u, absagen),
        PredArt::Klammer(x) => format!("({})", pred_c(x, u, absagen)?),
        PredArt::Nicht(x) => format!("!({})", pred_c(x, u, absagen)?),
        PredArt::Und(a, b) => format!("{} && {}", pred_c(a, u, absagen)?, pred_c(b, u, absagen)?),
        PredArt::Oder(a, b) => format!("{} || {}", pred_c(a, u, absagen)?, pred_c(b, u, absagen)?),
        // **Die fuenf, die KEINE Laufzeitbedingung sind -- einzeln, damit sie einzeln
        // gelesen werden koennen.** Der Rufer macht daraus `C001`; hier steht, was er
        // ablehnt.
        //
        // A quantifier and a `reaches` would need a loop -- and a loop inside the condition
        // of a loop is a cost the `costs` pass never counted. `x in domain` is the same
        // shape. `Held(L)` is a lock WITNESS: it is proved, not evaluated; emitting a check
        // for it would be exactly the run time check that W6 forbids. And `a => b` is
        // material implication -- writable as `!a || b`, but the emitter does not rewrite
        // what the author wrote (see the head of this file).
        PredArt::Quantor(_)
        | PredArt::Element(_, _)
        | PredArt::Erreicht { .. }
        | PredArt::Held { .. }
        | PredArt::Folgt(_, _) => return None,
    })
}

/// **`traverse` -- die Schleife, die KEINEN Laufzeitzaehler braucht.**
///
/// Ihre Domaene ist durch Konstruktion endlich; die Schranke faellt aus der Deklaration
/// (`count N`), nicht aus einer Zaehlung im Rumpf. *Genau darum verlangt die Grammatik hier
/// kein `on_exceeded` und beim `retry` eines* -- und die Absenkung macht den Unterschied
/// sichtbar: hier steht eine Laufgrenze, dort ein Wachhund.
///
/// **Abgesenkt wird heute EINE Domaene: `slots of <ort>`.** Sie bindet einen INDEX (so
/// benutzen es `beispiele/04` und `18`), und ihre Laenge rechnet C selbst aus dem Feld aus --
/// der Erzeuger muss den Tabellennamen dafuer gar nicht kennen.
///
/// **Jede andere Domaene wird beim Namen abgelehnt, mit ihrem eigenen Grund.** Sie sind
/// keine Bauarbeit, sondern Entscheidungen -- und zwei von ihnen haengen an offenen Befunden
/// **Woran ein Baumdurchlauf haengt: die Tabelle, ihr Speicher und der Wurzelindex.**
///
/// Drei Gestalten kommen im Korpus vor, und alle drei bedeuten dasselbe:
///
/// | Quelle | Tabelle | Speicher | Wurzel |
/// |---|---|---|---|
/// | `descendants of c.slots[s]` | `c`s Zeigerziel | `c->slots` | `s` |
/// | `descendants of Kappenraum.slots[s]` | `Kappenraum` | `Kappenraum_speicher.slots` | `s` |
/// | `ancestors of g` | aus `g`s Typ | `T_speicher.slots` | `g` |
///
/// *Die dritte ist die, an der es sich entscheidet:* ein blanker `index into T` nennt seine
/// Tabelle nur im TYP, und ohne den Parametertyp waere der Erzeuger hier blind.
/// **The view INSIDE a traversal -- and without it the emitter walked the wrong table.**
///
/// Measured 2026-08-31. A loop variable may carry the name of a parameter; the language
/// allows it and `gabbro pruefe` says `0 errors` about it. `baumsicht` above answers from
/// `parametertyp`, a map from NAME to declared type that knows nothing about scope -- so
/// `descendants of v` inside `traverse v of g over ancestors of g` resolved against the
/// PARAMETER `v` and lowered to a walk over the parameter's table:
///
/// ```text
/// gabbro pruefe   ->  6 items, 0 errors, 0 hints
/// cc              ->  clean
/// ./a.out         ->  0        (the right answer is 3)
/// ```
///
/// **The control in the same run is what makes it a finding**: rename the parameter, take
/// the shadow away, and the emitter REFUSES -- `C001: descendants of over a place that
/// names no table`. *The shadow was the only thing standing between a refusal and wrong
/// code.*
///
/// ## It REMEMBERS the name; it does not merely hide it -- and that is measured
///
/// `eigene_sicht` shadows a parameter by clearing seven maps, and the first version here
/// mirrored that: `parametertyp.remove(name)`, so that `baumsicht` would find nothing and
/// refuse. **It worked, and it was cut anyway**, because a second program showed it was
/// only half the question:
///
/// ```gabbro
/// impl fn f(w : ptr<normal, r> Winzig, c : ptr<normal, r> Riesen) -> u32
/// { traverse c over slots of w { traverse d of c over descendants of c.slots[0] { … } } }
/// ```
///
/// That place resolves through `tabellenzeiger`, not through `parametertyp` -- and the
/// unchanged emitter wrote three `c->slots[…]` accesses about a `uint32_t c`. **Hiding one
/// map does not answer a question the other maps also answer.** So the name is REMEMBERED,
/// once, and every domain asks `ist_laufvariable` before it asks anything else. With that
/// line in place, deleting `parametertyp.remove` killed no probe at all -- Regel A, and it
/// went.
fn laufsicht(u: &Namen, name: &str) -> Namen {
    let mut innen = u.clone();
    innen.laufvariablen.insert(name.to_string());
    innen
}

/// **Does this domain run over a name an enclosing loop bound?**
///
/// Measured 2026-08-31, and this half is the one `cc` found rather than a pass:
///
/// ```gabbro
/// impl fn f(t : ptr<normal, r> Riesig, w : ptr<normal, r> Winzig) -> u32
/// { traverse t over slots of w { traverse i over slots of t { … } } }
/// ```
///
/// ```text
/// gabbro pruefe -> 6 items, 0 errors, 0 hints
/// gabbro emit   -> for (uint32_t i = 0; i < sizeof(t->slots)/sizeof(t->slots[0]); i++)
/// cc            -> error: invalid type `uint32_t` for `->`
/// ```
///
/// `parametertyp` is not what decided this one: the arrow comes from `tabellenglobal`, and
/// the name from `ort`. **So the shadow alone does not close it** -- the emitter has to
/// know that the place IS a loop variable and refuse, the way it refuses every other domain
/// it cannot lower. *`N042` shape: the checker silent, the emitter silent, and `cc` saying
/// what both should have said.*
fn ist_laufvariable(o: &Ort, u: &Namen) -> bool {
    u.laufvariablen.contains(&o.basis.text)
}

fn baumsicht(o: &Ort, u: &Namen, absagen: &mut Absagen) -> Option<(String, String, String)> {
    // **A loop variable names no table, and NEITHER map may answer for it.** Both paths
    // below were measured: `parametertyp` carries `descendants of v`, `tabellenzeiger`
    // carries `descendants of c.slots[0]`, and the unchanged emitter walked the wrong
    // table through the first and wrote `c->slots[…]` about a `uint32_t` through the
    // second. One question in front of both.
    if ist_laufvariable(o, u) {
        return None;
    }
    // `<zeiger>.slots[i]` oder `<Tabelle>.slots[i]`
    if o.suffixe.len() == 2 {
        if let (OrtSuffix::Feld(f), OrtSuffix::Index(i)) = (&o.suffixe[0], &o.suffixe[1]) {
            if f.text == "slots" {
                let tab = u
                    .tabellenzeiger
                    .get(&o.basis.text)
                    .cloned()
                    .or_else(|| u.tabellen.iter().find(|t| **t == o.basis.text).cloned())?;
                let basis = if u.tabellenzeiger.contains_key(&o.basis.text) {
                    format!("{}->slots", o.basis.text)
                } else {
                    format!("{}_speicher.slots", o.basis.text)
                };
                return Some((tab, basis, ausdruck(i, u, absagen)));
            }
        }
    }
    // Ein blanker `index into T`.
    if o.suffixe.is_empty() {
        if let Some(TypExpr::Index { tabelle, .. }) = u.parametertyp.get(&o.basis.text) {
            return Some((
                tabelle.text.clone(),
                format!("{}_speicher.slots", tabelle.text),
                o.basis.text.clone(),
            ));
        }
    }
    None
}

/// **`ancestors of g` -- die Kette nach oben, und sie ist ein `for` mit drei Teilen.**
///
/// ```c
/// for (uint32_t v = T_speicher.slots[g].elter; v != NIL; v = T_speicher.slots[v].elter)
/// ```
///
/// **Sie faengt beim ELTER an und nicht bei `g` selbst.** *Ein Knoten ist kein Vorfahr von
/// sich* -- `beispiele/18` heisst `liegt_unter(g, wurzel)`, und dass etwas unter sich selbst
/// liegt, ist keine Aussage, die jemand haben will. Dieselbe Strenge wie bei `descendants`.
///
/// **Was diese Schleife beendet, ist eine HYPOTHESE, und das steht im Erzeugnis.** Der
/// Sonderwert `count` endet die Kette nur, wenn sie kreisfrei ist; `beispiele/18` sagt es
/// selbst -- *„Wohlfundiertheit ist HYPOTHESE, nicht Ergebnis"*. Eine erfundene Laufgrenze
/// waere hier schlimmer als keine: sie liefe still ab und liesse den Rest des Baumes aus.
///
/// `by consuming` wird abgelehnt -- **seine Vorfahren zu verbrauchen, waehrend man an ihnen
/// hochlaeuft, ist ein anderes Programm**, und welches, sagt die Grammatik nicht.
fn vorfahren(
    x: &Traverse,
    o: &Ort,
    s: &Stmt,
    aus: &mut String,
    u: &Namen,
    absagen: &mut Absagen,
    tiefe: usize,
    austritt: &Austritt,
) {
    let e = einzug(tiefe);
    if matches!(x.abstieg, Abstieg::Verbrauchend) {
        weigere(
            absagen,
            s.span,
            "`ancestors of … by consuming` -- consuming your ancestors while walking up them \
             is a different program, and the grammar does not say which",
        );
        return;
    }
    let Some((tab, basis, wurzel)) = baumsicht(o, u, absagen) else {
        weigere(absagen, s.span, "`ancestors of` over a place that names no table");
        return;
    };
    let Some((Some(elter), _, _)) = u.baeume.get(&tab).cloned() else {
        weigere(
            absagen,
            s.span,
            "`ancestors of` over a table whose `tree` names no `parent` edge -- «B41b»: the \
             edge stands at the table, and a missing one is an ANSWER, not a gap",
        );
        return;
    };
    let Some(n) = u.kapazitaet.get(&tab) else {
        weigere(absagen, s.span, "`ancestors of` over a table without `count` -- no sentinel");
        return;
    };
    let v = &x.variable.text;
    aus.push_str(&format!(
        "{e}/* ancestors of {wurzel} -- along `{elter}`, up to the sentinel {n}u. A node is\n\
         {e} * not its own ancestor, so the chain starts at the PARENT. That it ends rests on\n\
         {e} * well-foundedness, which is a HYPOTHESIS of the table, not a run-time check. */\n\
         {e}for (uint32_t {v} = {basis}[{wurzel}].{elter}; {v} != {n}u; {v} = {basis}[{v}].{elter}) {{\n"
    ));
    // The domain above was read in the OUTER scope; the BODY is not.
    let mut innen = laufsicht(u, v);
    // «SG-24»: this loop's binder is a capture a `count` may close over -- with the header's own C type (`traversebinder_ctyp`).
    innen.zaehlbinder.push((v.clone(), "uint32_t".to_string()));
    for k in &x.rumpf.anweisungen {
        anweisung(k, aus, &innen, absagen, tiefe + 1, austritt);
    }
    aus.push_str(&format!("{e}}}\n"));
}

/// **`descendants of s` -- der Abstieg OHNE Stapel, und `by consuming` bestimmt die
/// Reihenfolge.**
///
/// Ein Stapel schied aus, bevor die erste Zeile stand: er muesste so tief sein wie der Baum
/// hoch ist, also `count` Eintraege -- **16 KiB Kernstapel bei `NSLOTS = 4096`**. Mit den
/// drei Kanten braucht er keinen: `child` hinunter, `sibling` zur Seite, `parent` zurueck.
/// *Das ist der Grund, warum `tree` alle drei nennt und nicht nur die zwei, an denen es
/// abwaerts geht.*
///
/// ## `by consuming` ist hier KEIN blosses Beweismittel
///
/// Ueber `slots of` lehnt dieser Erzeuger es ab -- *„die Zeugenordnung ist ein Beweismittel;
/// was sie fuer den Lauf bedeutet, ist nicht entschieden"* -- und das bleibt richtig: ueber
/// einem Feld sagt eine Ordnung nichts, was ein linearer Durchlauf nicht schon tut.
///
/// **Ueber einem BAUM sagt sie die Richtung.** `by consuming` heisst, dass der Rumpf den
/// Knoten zerstoert, den er bekommt -- also muessen die Kinder zuerst dran sein, sonst laeuft
/// der Durchlauf an Kanten weiter, die es nicht mehr gibt. Das ist **Nachordnung**, und
/// `beispiele/01` bestaetigt es aus der anderen Richtung: sein Rumpf ruft `blatt_loeschen`,
/// und das verlangt `ist_blatt`.
///
/// `by unvisited` bekommt dieselbe Laufform und ist damit bedient: es sagt *jeder Knoten
/// einmal* und ueber die Reihenfolge nichts. **Wer die staerkere Zusage haelt, haelt die
/// schwaechere** -- und eine zweite Laufform, die der Korpus nie ausloest, waere ein
/// ungeprueftes Stueck Erzeuger.
///
/// > **Und darum wird jede Kante GELESEN, bevor der Rumpf laeuft.** Der Nachfolger steht in
/// > `_w` fest, ehe der Knoten fallen darf. Ein Erzeuger, der ihn danach liest, erzeugt C,
/// > das bei `-O0` meistens noch stimmt.
fn nachfahren(
    x: &Traverse,
    o: &Ort,
    s: &Stmt,
    aus: &mut String,
    u: &Namen,
    absagen: &mut Absagen,
    tiefe: usize,
    austritt: &Austritt,
) {
    let e = einzug(tiefe);
    match x.abstieg {
        // **Eine Laufform, und `by unvisited` ist damit BEDIENT, nicht uebergangen.**
        // `unvisited` sagt *jeder Knoten einmal* und ueber die Reihenfolge nichts; die
        // Nachordnung sagt beides. Wer die staerkere Zusage haelt, haelt die schwaechere --
        // und zwei Laufformen zu erzeugen, von denen der Korpus eine nie ausloest, waere ein
        // ungeprueftes Stueck Erzeuger. *Das ist der Unterschied zwischen einer Absenkung
        // und einer Vorratshaltung.*
        Abstieg::Verbrauchend | Abstieg::Unbesucht => {}
    }
    // **The refusal follows the witness out of `Abstieg`** (2026-09-01). It was a match arm
    // on the third run form; the third run form is gone, and the measure is now a clause
    // that either stands here or does not. *The refusal is unchanged in reach and in
    // wording: this emitter still does not know which of the two tree orders a measure
    // constrains.*
    if x.mass.is_some() {
        weigere(
            absagen,
            s.span,
            "`descendants of … decreases` -- a measure over a tree walk is not \
             decided: which of the two orders it constrains is not written anywhere",
        );
        return;
    }
    let Some((tab, basis, wurzel)) = baumsicht(o, u, absagen) else {
        weigere(absagen, s.span, "`descendants of` over a place that names no table");
        return;
    };
    let Some((elter, kind, geschwister)) = u.baeume.get(&tab).cloned() else {
        weigere(
            absagen,
            s.span,
            "`descendants of` over a table with no `tree` -- «B41b»: the edge stands at the \
             table, and this one names none",
        );
        return;
    };
    let (Some(elter), Some(kind), Some(geschwister)) = (elter, kind, geschwister) else {
        weigere(
            absagen,
            s.span,
            "`descendants of` needs all three edges -- `child` and `sibling` to walk down, \
             `parent` to come back WITHOUT a stack (one as deep as the tree is high would be \
             `count` entries of kernel stack)",
        );
        return;
    };
    let Some(n) = u.kapazitaet.get(&tab) else {
        weigere(absagen, s.span, "`descendants of` over a table without `count` -- no sentinel");
        return;
    };
    let v = &x.variable.text;
    let (k, w, h, r) = (
        format!("_k{tiefe}"),
        format!("_w{tiefe}"),
        format!("_h{tiefe}"),
        format!("_r{tiefe}"),
    );
    aus.push_str(&format!(
        "{e}/* descendants of {wurzel} -- POST-ORDER (leaves first), along `{kind}`/`{geschwister}`, back up\n\
         {e} * along `{elter}`. NO stack: one as deep as the tree is high would be {n} entries.\n\
         {e} * `{h}` says the walk arrived from BELOW, which is what keeps it from descending\n\
         {e} * into a node it has already finished. Every edge is read into `{w}` BEFORE the\n\
         {e} * body runs -- `by consuming` may destroy the node it is handed.\n\
         {e} * A node is not its own descendant: the root is walked THROUGH, never visited.\n\
         {e} * That the walk ends rests on well-foundedness, a HYPOTHESIS of the table. */\n\
         {e}{{\n\
         {e}    const uint32_t {r} = {wurzel};\n\
         {e}    uint32_t {k} = {r};\n\
         {e}    bool {h} = false;\n\
         {e}    for (;;) {{\n\
         {e}        if (!{h} && {basis}[{k}].{kind} != {n}u) {{ {k} = {basis}[{k}].{kind}; {h} = false; continue; }}\n\
         {e}        if ({k} == {r}) break;\n\
         {e}        uint32_t {w}; bool {w}_hoch;\n\
         {e}        if ({basis}[{k}].{geschwister} != {n}u) {{ {w} = {basis}[{k}].{geschwister}; {w}_hoch = false; }}\n\
         {e}        else {{ {w} = {basis}[{k}].{elter}; {w}_hoch = true; }}\n"
    ));
    // **Die Vorordnung besucht auf dem WEG hinunter, die Nachordnung auf dem Weg zurueck.**
    // Beide Male steht der Nachfolger schon fest -- der Unterschied ist allein, wo der Rumpf
    // sitzt, und genau das ist die ganze Aussage von `by consuming`.
    // The domain above was read in the OUTER scope; the BODY is not.
    let mut innen = laufsicht(u, v);
    // «SG-24»: this loop's binder is a capture a `count` may close over -- with the header's own C type (`traversebinder_ctyp`).
    innen.zaehlbinder.push((v.clone(), "uint32_t".to_string()));
    let rumpf_hin = |aus: &mut String, absagen: &mut Absagen| {
        aus.push_str(&format!("{e}        {{\n{e}            const uint32_t {v} = {k};\n"));
        aus.push_str(&format!("{e}            (void){v};\n"));
        for kk in &x.rumpf.anweisungen {
            anweisung(kk, aus, &innen, absagen, tiefe + 3, austritt);
        }
        aus.push_str(&format!("{e}        }}\n"));
    };
    rumpf_hin(aus, absagen);
    aus.push_str(&format!(
        "{e}        {k} = {w}; {h} = {w}_hoch;\n{e}    }}\n{e}}}\n"
    ));
}

/// des Ordners («B12»: bindet `elems of` ein Element oder einen Index? «B10»: `traverse`
/// liefert keinen Wert und kennt kein `break`).
///
/// **Exits pass THROUGH a `traverse` (lane 252).** The walk carries no label
/// (`SYNTAX.md` §8 gives it no slot, `schleifen.rs` registers none), so a
/// `leave`/`next` in the body can only name an enclosing `retry`/`forever`.
/// Three lines hold that together, all elsewhere: the body is lowered with
/// the incoming `austritt` unchanged (no label pushed here), the `Leave`/
/// `Next` arm emits `goto <marke>_ende|_weiter` with the locks taken inside
/// released first (never `break`/`continue` -- those would take the walk
/// itself), and `sprungziele` descends into the walk body so the outer loop
/// emits the label that is jumped to. `tests/traverse_exit.rs` pins all
/// four halves: `leave`/`next` through a `slots` walk, `leave` through the
/// stackless descendant walk, the release on the exit path, and the S001
/// refusal for an exit naming the walk binder. A windowed walk
/// (`from <start> count <len>`) never reaches this function: the reader
/// refuses it with P001 (lane 222), so there is no window arm here.
fn traverse(
    x: &Traverse,
    s: &Stmt,
    aus: &mut String,
    u: &Namen,
    absagen: &mut Absagen,
    tiefe: usize,
    austritt: &Austritt,
) {
    let e = einzug(tiefe);
    let grund = match &x.domaene {
        Domaene::SlotsVon(o) => {
            // **Die Zeugenordnung ist ein BEWEISMITTEL, kein Laufzeitding.** `by unvisited`
            // heisst: jeder Slot einmal -- das ist die Laufform selbst. `by consuming` und
            // `by decreasing` sagen etwas ueber die Erhaltung einer Ordnung und haetten hier
            // eine andere Laufform; sie werden abgelehnt.
            // **Stufe 3 hat entschieden, was der Abstieg fuer den LAUF heisst** (2026-08-20):
            //
            //   `by unvisited`   jedes Element einmal, Reihenfolge offen
            //   `by decreasing`  DASSELBE -- das Mass ist ein Terminierungszeuge und sagt
            //                    ueber den Lauf nichts, was `unvisited` nicht schon sagt
            //   `by consuming`   dasselbe PLUS die Entnahme, und die ist eine Operation
            //
            // *Bis dahin stand hier „what it means for the run is not decided" fuer beide --
            // und das war fuer `by decreasing` eine offene Frage ueber etwas, das gar keine
            // Laufwirkung hat.* Was bleibt, ist `by consuming`: die Entnahme ist erzeugter
            // Code (`ops`), und ihn zu erfinden waere ein anderes Programm.
            if matches!(x.abstieg, Abstieg::Verbrauchend) {
                weigere(
                    absagen,
                    s.span,
                    "`by consuming` -- the run form is the same walk PLUS the removal, and \
                     the removal is a generated `ops` operation this emitter does not have",
                );
                return;
            }
            // **Der Pfeil stand hart da, und eine bei NAMEN adressierte Tabelle ist kein
            // Zeiger** (2026-08-20).
            //
            // `traverse i over slots of T` ueber einer Tabelle, die ihren eigenen Namen
            // traegt, ergab
            //
            // ```c
            // for (… sizeof(T_speicher->slots) …) { T_speicher.slots[i].a = false; }
            // ```
            //
            // -- **Pfeil in der Kopfzeile, Punkt im Rumpf, in derselben Anweisung**, bei null
            // Prueferfehlern. Der Rumpf geht durch `ort()` und weiss es; die Kopfzeile hat
            // es hingeschrieben.
            //
            // > *Der Korpus traversiert `slots of` bisher ausschliesslich ueber Zeiger*
            // > (`04`, `19`); wer bei Namen adressiert (`09`, `18`, `31`), benutzt
            // > `descendants of`/`ancestors of` -- und die sind richtig. **Die Kombination
            // > gab es nicht**, und `gabbro blindstellen` hat sie als Zelle gefuehrt.
            if ist_laufvariable(o, u) {
                weigere(
                    absagen,
                    s.span,
                    "`slots of` over a name an enclosing `traverse` bound -- a loop variable \
                     is an index word, and it names no table",
                );
                return;
            }
            let feld = if u.tabellenglobal.contains(&o.basis.text) {
                format!("{}.slots", ort(o, u, absagen))
            } else {
                format!("{}->slots", ort(o, u, absagen))
            };
            let v = &x.variable.text;
            // **CForm schrittStmt (lane 142): `+= 1`, not `++`.** The bound is
            // untouched (`sizeof` stays -- text-pinned and load-bearing); only
            // the step moves into the admitted compound-assignment class.
            aus.push_str(&format!(
                "{e}for (uint32_t {v} = 0; {v} < (uint32_t)(sizeof({feld}) / sizeof({feld}[0])); {v} += 1) {{\n"
            ));
            // The domain above was read in the OUTER scope; the BODY is not.
            let mut innen = laufsicht(u, v);
            // «SG-24»: this loop's binder is a capture a `count` may close over -- with the header's own C type (`traversebinder_ctyp`).
            innen.zaehlbinder.push((v.clone(), "uint32_t".to_string()));
            for k in &x.rumpf.anweisungen {
                anweisung(k, aus, &innen, absagen, tiefe + 1, austritt);
            }
            aus.push_str(&format!("{e}}}\n"));
            return;
        }
        // **«B12» ist entschieden: `elems of` bindet einen INDEX** (Stufe 3, 2026-08-20).
        //
        // Der Korpus benutzte beide Lesarten, und zwar an tragenden Stellen: F3 schreibt
        // `forall i in elems of dst.msg : dst.msg[i] == old(src.msg[i])` (Index), F6
        // schreibt `traverse w over elems of s.worte { if w != MUSTER … }` (Element).
        //
        // Drei Gruende, und der erste entscheidet allein:
        //
        //   1. **Der Index ist echt maechtiger.** Aus dem Index bekommt man das Element
        //      (`p[i]`); aus dem Element den Index nicht. Die Aussage *„beide Felder stimmen
        //      an derselben Stelle ueberein"* -- `msg_kopiert`, die tragende Zusage des
        //      IPC-Fastpath -- ist unter der Elementlesart NICHT schreibbar.
        //   2. **Es passt zu den anderen.** `slots of`, `descendants of`, `ancestors of`
        //      binden alle eine ADRESSE. Nur `mappings of` bindet einen Verbund, und seine
        //      Deklaration sagt das -- eine Abbildung hat keine einzelne Adresse.
        //   3. **Es nimmt Zeremonie weg.** F6 fuehrt heute einen Zaehler `i` NEBEN der
        //      Traversierung mit, nur um die Stelle zu kennen. Unter der Indexlesart ist die
        //      Laufvariable diese Stelle.
        //
        // *Und der Einwand gegen den Namen ist beantwortet, nicht uebergangen:* **eine
        // Domaene heisst nach dem, WORUEBER sie laeuft, nicht nach dem, was die Variable
        // haelt.** `slots of` bindet ebenfalls einen Index; das ist ab heute eine Regel und
        // kein Zufall.
        Domaene::ElementeVon(o) => {
            if matches!(x.abstieg, Abstieg::Verbrauchend) {
                weigere(
                    absagen,
                    s.span,
                    "`elems of … by consuming` -- an array element is not removed; \
                     consumption needs a carrier with generated `ops`",
                );
                return;
            }
            // **The index of an ARRAY is not the index word of a TABLE** (2026-08-31).
            //
            // Until today this line read `uint32_t`, copied from the `slots of` arm four
            // hundred lines up. There the width is DECIDED: a table index fills an index
            // word and the `option` sentinel sits at `2^32` (`beweise/Option_Sonderwert.thy`,
            // and the refusal at `count {n} fills the index word` says so out loud). **An
            // array carries no such decision** -- its length stands in the declaration as a
            // `const … : u64`, and `sizeof(f)/sizeof(f[0])` is a `size_t`.
            //
            // The narrowing was not a matter of taste, and it was `cc` that said so:
            // `messung/fragmente/F06.gab` emitted 161 lines and fell at
            // `-Werror=type-limits` -- *"comparison is always true due to limited range"*
            // for `if (w != MUSTER)` with `MUSTER = 0xdead_beef_dead_beef`. **The same C
            // with `uint64_t w` compiles**, at `-O0` and at `-O2`; that is the whole
            // measurement, and it puts the cause in the EMITTER and not in the program.
            //
            // > *A generator that narrows what the declaration widened writes a check that
            // > checks nothing* -- and the cast in the bound truncates as well: an array of
            // > more than `2^32` entries would loop against a bound that is not its length.
            // > The warning was the cheap half of that finding.
            //
            // `slots of` keeps `uint32_t`, and that asymmetry is the point: the two indices
            // are indices into different things.
            if ist_laufvariable(o, u) {
                weigere(
                    absagen,
                    s.span,
                    "`elems of` over a name an enclosing `traverse` bound -- a loop variable \
                     is an index word, and it carries no array field",
                );
                return;
            }
            // **CForm schrittStmt (lane 142): `+= 1`, not `++`** -- same move as
            // the `slots of` header above; the `uint64_t` bound is untouched.
            // (Stands above the header: the mutation anchor below matches this
            // block literally, and a comment inside it would blind the anchor.)
            let feld = ort(o, u, absagen);
            let v = &x.variable.text;
            aus.push_str(&format!(
                "{e}for (uint64_t {v} = 0; {v} < (uint64_t)(sizeof({feld}) / sizeof({feld}[0])); {v} += 1) {{\n"
            ));
            // The domain above was read in the OUTER scope; the BODY is not.
            let mut innen = laufsicht(u, v);
            // «SG-24»: this loop's binder is a capture a `count` may close over -- with the header's own C type (`traversebinder_ctyp`).
            innen.zaehlbinder.push((v.clone(), "uint64_t".to_string()));
            for k in &x.rumpf.anweisungen {
                anweisung(k, aus, &innen, absagen, tiefe + 1, austritt);
            }
            aus.push_str(&format!("{e}}}\n"));
            return;
        }
        // **Und das ist ein BEFUND, kein Bauposten** (2026-08-17, beim Absenken gefunden).
        //
        // Die Domaene sagt nicht, AN WELCHER KANTE sie laeuft. `FRAGMENTE.md` F1 fuehrt in
        // seiner Tabelle vier Kandidaten -- `parent`, `first_child`, `next_sibling`,
        // `prev_sibling` -- und `descendants of c.slots[s]` nennt keinen.
        //
        // > **Die Grammatik weiss sehr wohl, wie man das sagt:** `chain(a, b) in <ort>`
        // > (`SYNTAX.md`:348) benennt seine beiden Felder. `descendants of` und
        // > `ancestors of` tun es nicht. *Das ist eine Unsymmetrie in der Grammatik, kein
        // > fehlender Erzeugercode* -- und sie faellt erst auf, wenn jemand die Domaene
        // > absenken will.
        // **«B41b»: die Kante steht jetzt an der TABELLE, und beide Domaenen laufen.**
        //
        // Was hier bis zum 2026-08-20 stand, war eine Weigerung mit einem Befund darin:
        // *„the domain does not name the EDGE it walks … that is an asymmetry in the
        // grammar, not missing emitter code."* **Der Befund war richtig und ist eingeloest**
        // -- nicht so, wie `chain(a, b) in` es vormacht (am Durchlauf), sondern an der
        // `table`: ein Baum wird an vielen Stellen durchlaufen, und zwei Stellen koennten
        // verschiedene Felder nennen, ohne dass jemand die beiden vergleicht.
        Domaene::NachfahrenVon(o) => {
            nachfahren(x, o, s, aus, u, absagen, tiefe, austritt);
            return;
        }
        Domaene::VorfahrenVon(o) => {
            vorfahren(x, o, s, aus, u, absagen, tiefe, austritt);
            return;
        }
        // **THE RUN FORM IS NOT THE REASON, AND UNTIL 2026-09-04 THIS LINE SAID IT WAS.**
        //
        // What stood here was *"`traverse` yields no value and knows no `break`, so `by
        // consuming` drains the WHOLE queue; that is a different program"*. Every word of
        // that is true about the IPC fastpath (`messung/fragmente/F03.gab`:185), which is a
        // SEARCH loop wanting a value and an exit. **It is not what fires this arm.** The
        // arm refuses `Domaene::Schlange` unconditionally, so a file writing `by unvisited`
        // got the identical text -- a refusal quoting a clause the file does not write.
        // Measured, both files `0 errors` at `pruefe` and both landing here at `emit`:
        //
        //     traverse j over queue r by consuming touches consumes r, reads r, writes r
        //     traverse j over queue r by unvisited touches reads r, writes r
        //
        // **What is actually missing is an ELEMENT SET**, and that stands measured at
        // `beispiele/56-auftragsring.gab`:22-27 and in `domaene.rs`:154-169. A queue here is
        // an ordinary record with exactly one array field; `arraylaenge_im_verbund` -- the
        // only machinery anywhere that reads a queue-shaped record -- takes that array's
        // LENGTH and nothing else, and head, tail and count are never identified. So
        // `queue r` denotes the whole backing buffer, dead cells included.
        //
        // *And that is why an arm would discharge nothing.* Measured 2026-09-04: `traverse j
        // over elems of r.buf by unvisited` lowers TODAY, to
        // `for (uint64_t j = 0; j < sizeof(r->buf)/sizeof(r->buf[0]); j++)`, and an arm here
        // could emit nothing else -- **a second spelling of a loop that already lowers**,
        // and the wrong loop for every program that means the live entries. Naming those
        // needs a declaration form that binds head/tail/count: a grammar question («B10»),
        // not an emitter arm.
        Domaene::Schlange(_) => {
            "`queue` -- the domain names no ELEMENT SET: a queue is an ordinary record with \
             exactly one array field, and nothing declares head, tail or count. `queue r` is \
             therefore the whole backing BUFFER, dead cells included, and an arm could emit \
             only what `elems of r.<that array>` already emits -- a second spelling, not a \
             lowering. THE RUN FORM IS NOT THE REASON: `by unvisited` reaches this line too. \
             Naming the live cells is «B10», and it is a grammar question"
        }

        // **DIE LESART IST SEIT STUFE 3 ENTSCHIEDEN, DIE ABSENKUNG NICHT** (2026-08-20).
        //
        // Bis dahin stand hier ein FEHLER IM KOSTENPASS: `SPRACHE.md`:786 sagt *„quantifies
        // over ALL reachable leaf entries"*, und `walkschranken` rechnete **Ebenen mal
        // Knotenlaenge** -- 2 048 statt 512^4 = 68 719 476 736. **Sieben Groessenordnungen**,
        // und der Pass zaehlte EINEN Abstiegspfad und nannte es die Domaene.
        //
        // *Dieselbe Klasse, die dieser Ordner zweimal bezahlt hat* -- `revoke` sagte 200 ops
        // zu und kostet 16 452 480, A4 sagte 4 096 zu und kostet 831 488. Beide Male war es
        // ein MENSCH, der den typischen Fall statt der Schranke schrieb, und der Pass hat es
        // gefangen. **Hier war es der Pass selbst.**
        //
        // **Entschieden wurde fuer die MENGE**, und der Grund ist aelter als der Pass: die
        // Domaene wurde gebaut, damit W^X ueber die ganze Tabelle formulierbar wird, und W^X
        // ist eine Aussage ueber die Menge -- ueber einen Pfad ist sie sinnlos. `umgebung.rs`
        // rechnet seither `Knotenlaenge ^ levels`.
        //
        // Was bleibt, ist ein BAUPOSTEN und keine offene Frage: eine Laufzeit-Traversierung
        // ueber die Blattmenge braucht einen **erzeugten rekursiven Abstieg** entlang `down`
        // und `leaf`. *Und sie wird danach keine Kostenzusage tragen -- das ist die Folge der
        // Entscheidung und wird ausgehalten, nicht wegdefiniert.*
        Domaene::AbbildungenVon(_) => {
            "`mappings of` -- the reading is DECIDED (the leaf SET, because W^X is a \
             statement about the set), and the cost bound now says so. What is missing is \
             the lowering: it needs a generated recursive descent along `down` and `leaf`"
        }
        Domaene::KetteIn { .. } => "`chain in` -- the sibling chain needs its own bound",
        Domaene::FelderVon(_) => "`fields of` -- a register field list is not a runtime domain",
        Domaene::Threads => "`threads` -- the thread set is not declared in a translation unit",
    };
    weigere(absagen, s.span, grund);
}

/// **«C2»: `match` ueber einem `tagged type` wird ein `switch` OHNE `default`.**
///
/// Der fehlende Sammelzweig ist die ganze Aussage: `D005` verlangt seit dem 2026-08-19 das
/// erschoepfende `match` ohne Auffangzweig, und **`-Wswitch` liest dieselbe Zusage ein
/// zweites Mal**. *Ein `default:` hier wuerde genau den Leser stilllegen, um dessentwillen
/// die Marke ein `enum` ist.*
///
/// Die Nutzlast des Zweiges kommt aus dem Glied, das die Marke nennt -- und **nur daraus**:
/// ein anderes Glied zu lesen waere der eine Fall, in dem eine C-`union` das Typrecht
/// verletzt, und der Pass davor schliesst ihn aus.
fn match_markiert(
    m: &MatchStmt,
    s: &Stmt,
    aus: &mut String,
    u: &Namen,
    absagen: &mut Absagen,
    tiefe: usize,
    austritt: &Austritt,
    typ: &str,
) {
    let e = einzug(tiefe);
    let Some(varianten) = u.markierte.get(typ).cloned() else { return };
    // **Exhaustive, no catch-all -- and the generator checks it itself.** `D005` holds it
    // one level up, in `kbedingung.rs`; here it shows up should that pass ever stop.
    // *A `switch` with missing cases otherwise falls through and does NOTHING.*
    if m.zweige.len() != varianten.len()
        || !varianten
            .iter()
            .all(|v| m.zweige.iter().any(|z| z.variante.text == v.name.text))
    {
        weigere(
            absagen,
            s.span,
            "`match` over a `tagged type` must name every variant exactly once -- there is \
             no catch-all branch, and a `switch` with a missing case falls through and does \
             NOTHING",
        );
        return;
    }
    // **A scrutinee that is not a PLACE is evaluated exactly once, and that needs a
    // temporary** (2026-08-31, with `match decode_op(m.op)`).
    //
    // The arms read `{gegenstand}.marke` and `{gegenstand}.last.{v}` -- **two mentions and
    // more**, one per arm with a payload. Written out with a call in place of the name, that
    // is one call per mention: `decode_op` would run again inside the branch it selected.
    // *A generator that duplicates a call has changed the program, not lowered it.*
    //
    // The option arm has bound `_o{tiefe}` for the same reason since it was written; this
    // is the same move under the same name scheme.
    let roh = ausdruck(&m.gegenstand, u, absagen);
    let ort_gegenstand = matches!(&m.gegenstand.art, ExprArt::Ort(_));
    let gegenstand = if ort_gegenstand { roh.clone() } else { format!("_m{tiefe}") };
    if !ort_gegenstand {
        aus.push_str(&format!("{e}{{\n{e}{typ} {gegenstand} = {roh};\n"));
    }
    aus.push_str(&format!("{e}switch ({gegenstand}.marke) {{\n"));
    for v in &varianten {
        let Some(z) = m.zweige.iter().find(|z| z.variante.text == v.name.text) else {
            continue;
        };
        aus.push_str(&format!("{e}case {typ}_{}: {{\n", v.name.text));
        if let (Some(b), Some(nl)) = (&z.binder, &v.nutzlast) {
            match ctyp(nl, u) {
                Some(c) => {
                    aus.push_str(&format!(
                        "{e}    {c} {} = {gegenstand}.last.{};\n",
                        b.text, v.name.text
                    ));
                    // **`(void)x;` fuer einen Binder, den der Zweig nicht liest** -- der
                    // Anwender hat die erzeugte Zeile nicht geschrieben, und `-Wextra`
                    // spraeche sonst ueber ihn. Dieselbe Buchung wie beim toten Parameter.
                    let mut gelesen = BTreeSet::new();
                    benutzte_namen(&z.rumpf, &mut gelesen);
                    if !gelesen.contains(&b.text) {
                        aus.push_str(&format!("{e}    (void){};\n", b.text));
                    }
                }
                None => {
                    weigere(absagen, b.span, "`tagged` variant payload type");
                    return;
                }
            }
        }
        for k in &z.rumpf.anweisungen {
            anweisung(k, aus, u, absagen, tiefe + 1, austritt);
        }
        aus.push_str(&format!("{e}}} break;\n"));
    }
    aus.push_str(&format!("{e}}}\n"));
    // **Wenn JEDER Zweig zurueckkehrt, ist die Stelle danach unerreichbar -- und C weiss es
    // nicht** (2026-08-20).
    //
    // Der `switch` hat keinen `default:`, und das ist Absicht: `-Wswitch` wird damit ein
    // zweiter Leser von `D005`. Genau deshalb sieht der C-Uebersetzer aber einen Weg um den
    // `switch` herum und meldet *„control reaches end of non-void function"* -- an einem
    // Programm, das Gabbro **richtig** findet.
    //
    // > **Die Zeile ist keine Erfindung, sondern eine Weitergabe.** `D005` hat entschieden,
    // > dass die Fallunterscheidung geschlossen ist; W6 sagt, dass die Maschine das nicht
    // > noch einmal prueft. `__builtin_unreachable()` ist die Form, in der man einem
    // > C-Uebersetzer genau diese Entscheidung mitteilt -- *und wo er sie nicht kennt, steht
    // > nichts, denn ohne die Warnung gibt es auch das Problem nicht.*
    if m.zweige.iter().all(|z| {
        z.rumpf
            .anweisungen
            .last()
            .is_some_and(|k| matches!(&k.art, StmtArt::Return(_)))
    }) {
        aus.push_str(&format!(
            "{e}/* D005: the case distinction is closed and every arm returns. The `switch`
             {e} * carries no catch-all branch on purpose -- that is what makes `-Wswitch` a second
             {e} * reader of the rule. This line hands THAT decision to the C compiler; it
             {e} * decides nothing of its own. */
             {e}#if defined(__GNUC__)
{e}__builtin_unreachable();
{e}#endif
"
        ));
    }
    if !ort_gegenstand {
        aus.push_str(&format!("{e}}}\n"));
    }
}

/// **Der `switch` ueber einem `reason`** (Stufe 7, 2026-08-21).
///
/// Kein Binder, keine Nutzlast: ein Grundfall traegt eine Zahl und einen Text, und der Text
/// steht im erzeugten C schon als Kommentar am `enum`. *Deshalb ist diese Funktion kuerzer
/// als ihre Schwester `match_markiert`* -- die Abgeschlossenheit prueft `M123`, hier wird sie
/// nur weitergereicht.
#[allow(clippy::too_many_arguments)]
fn match_grund(
    m: &MatchStmt,
    aus: &mut String,
    u: &Namen,
    absagen: &mut Absagen,
    tiefe: usize,
    austritt: &Austritt,
    name: &str,
    grund: &str,
) {
    let e = einzug(tiefe);
    aus.push_str(&format!("{e}switch ({name}) {{\n"));
    for z in &m.zweige {
        aus.push_str(&format!("{e}case {grund}_{}: {{\n", z.variante.text));
        for k in &z.rumpf.anweisungen {
            anweisung(k, aus, u, absagen, tiefe + 1, austritt);
        }
        aus.push_str(&format!("{e}}} break;\n"));
    }
    aus.push_str(&format!("{e}}}\n"));
    // Dieselbe Weitergabe wie bei `D005`: die Fallunterscheidung ist geschlossen, jeder
    // Zweig kehrt zurueck, und `-Wreturn-type` kennt die Entscheidung nicht.
    if m.zweige.iter().all(|z| {
        z.rumpf
            .anweisungen
            .last()
            .is_some_and(|k| matches!(&k.art, StmtArt::Return(_)))
    }) {
        aus.push_str(&format!(
            "{e}#if defined(__GNUC__)\n{e}__builtin_unreachable();\n{e}#endif\n"
        ));
    }
}

/// Welchen `tagged type` traegt dieser Ausdruck? **Ueber den erklaerten Typ, nicht ueber die
/// Variantennamen** -- zwei Typen duerfen gleichnamige Varianten haben.
fn marken_quelle(e: &Expr, u: &Namen) -> Option<String> {
    // **A CALL carries a declared return type, and until 2026-08-31 nobody asked it here.**
    //
    // `messung/fragmente/F05.gab` writes `match decode_op(m.op) { Info => … }` over
    // `tagged type Op`. The checker takes it -- **0 errors** -- and the emitter fell through
    // to the option arm and refused with *"`match` over something other than an `option
    // index into T`"*. The refusal named the wrong thing: the scrutinee is not an option,
    // it is a `tagged type`, and the only reason it was invisible is that this function read
    // PLACES and nothing else.
    //
    // *`wert_ctyp` learned the same lesson on 2026-08-20, in this file, four hundred lines
    // down:* **the declared return type of a callee was the one of three sources nobody
    // asked.** Here it was the third time.
    if let ExprArt::Ruf(r) = &e.art {
        let n = &r.path()?.teile.last()?.text;
        // `Op(…)` would be a constructor, not a call -- a `tagged type` variant names itself.
        if u.markierte.contains_key(n) {
            return None;
        }
        return match u.funktionen.get(n)?.rueck.as_ref()? {
            TypExpr::Pfad(p) => {
                let t = p.teile.last()?.text.clone();
                u.markierte.contains_key(&t).then_some(t)
            }
            _ => None,
        };
    }
    let ExprArt::Ort(o) = &e.art else { return None };
    if o.suffixe.is_empty() {
        if let Some(t) = u.markenwerte.get(&o.basis.text) {
            return Some(t.clone());
        }
    }
    match ort_typ(o, u)? {
        TypExpr::Pfad(p) => {
            let n = p.teile.last()?.text.clone();
            u.markierte.contains_key(&n).then_some(n)
        }
        _ => None,
    }
}

/// Nur `match` ueber einer Option und ueber einem `tagged type` wird abgesenkt.
fn match_option(
    m: &MatchStmt,
    s: &Stmt,
    aus: &mut String,
    u: &Namen,
    absagen: &mut Absagen,
    tiefe: usize,
    austritt: &Austritt,
) {
    let e = einzug(tiefe);
    if let Some(typ) = marken_quelle(&m.gegenstand, u) {
        match_markiert(m, s, aus, u, absagen, tiefe, austritt, &typ);
        return;
    }
    // **`match e { … }` ueber einem GRUND** (Stufe 7, 2026-08-21).
    //
    // Ein `reason` senkt zu einem `enum` mit ausgeschriebenen Werten ab, also ist der
    // `match` darueber ein gewoehnlicher `switch` -- **ohne `default:`, und das aus genau
    // demselben Grund wie beim `tagged type`:** ohne Sammelzweig wird `-Wswitch` ein
    // zweiter Leser der Regel, die im Pruefer `M123` heisst.
    //
    // > *Ohne diese Absenkung waere `match e` eine Form, die `gabbro pruefe` annimmt und
    // > `gabbro emit` ablehnt* -- und ich haette den Fehlerkanal an einem Ende geoeffnet
    // > und am anderen zugelassen.
    if let ExprArt::Ort(o) = &m.gegenstand.art {
        if o.suffixe.is_empty() {
            if let Some(g) = u.gruendewerte.get(&o.basis.text).cloned() {
                match_grund(m, aus, u, absagen, tiefe, austritt, &o.basis.text, &g);
                return;
            }
        }
    }
    let Some(tabelle) = option_quelle(&m.gegenstand, u) else {
        // **Two forms stood under one refusal, and its ground held for only one**
        // (2026-08-31 -- the same shape this folder has now found six times).
        //
        // `messung/fragmente/F05.gab` writes `match decode_op(m.op) { Info => … }` and got
        // *"`match` over something other than an `option index into T`"*. **The scrutinee is
        // not an option and the text says nothing true about it**: it is a call, and the
        // reason the emitter cannot see its type is that `decode_op` is declared NOWHERE in
        // that unit. `E009` says the same thing one level up, as a hint on the effect hull.
        //
        // *A refusal that names the wrong thing sends its reader to the wrong place* -- and
        // in this case to a decision («B12», the option reading) that has nothing to do with
        // it. So the two halves get one sentence each.
        if let ExprArt::Ruf(r) = &m.gegenstand.art {
            if let Some(n) = r.path().and_then(|p| p.teile.last()) {
                if !u.funktionen.contains_key(&n.text) && !u.markierte.contains_key(&n.text) {
                    weigere(
                        absagen,
                        s.span,
                        "`match` over a call this unit does not declare -- the type of the \
                         scrutinee stands in the callee's declaration, and there is none. A \
                         call whose return type IS a `tagged type` lowers",
                    );
                    return;
                }
            }
        }
        // **Lane 227: integer arms (lane 222) lower to a `switch` below.** Any integer
        // arm at all takes this road -- a MIXED match refuses there by name, and the
        // three lowerings above keep every all-variant match exactly as they read it
        // (their refusal matrix, MUSE-REPORT-222 §3, is unchanged).
        if m.zweige.iter().any(|z| z.intpat.is_some()) {
            match_int(m, s, aus, u, absagen, tiefe, austritt);
            return;
        }
        weigere(absagen, s.span, "`match` over something other than an `option index into T`");
        return;
    };
    let namen: Vec<&str> = m.zweige.iter().map(|z| z.variante.text.as_str()).collect();
    if namen.len() != 2 || !namen.contains(&"Some") || !namen.contains(&"None") {
        weigere(absagen, s.span, "`match` over an option needs exactly `Some` and `None`");
        return;
    }
    let ja = m.zweige.iter().find(|z| z.variante.text == "Some").unwrap();
    let nein = m.zweige.iter().find(|z| z.variante.text == "None").unwrap();
    let hilf = format!("_o{}", tiefe);

    aus.push_str(&format!(
        "{e}{{\n{e}    uint32_t {hilf} = {};\n{e}    if ({hilf} != {tabelle}_NONE) {{\n",
        ausdruck(&m.gegenstand, u, absagen)
    ));
    if let Some(b) = &ja.binder {
        aus.push_str(&format!("{e}        uint32_t {} = {hilf};\n", b.text));
    }
    for k in &ja.rumpf.anweisungen {
        anweisung(k, aus, u, absagen, tiefe + 2, austritt);
    }
    aus.push_str(&format!("{e}    }} else {{\n"));
    for k in &nein.rumpf.anweisungen {
        anweisung(k, aus, u, absagen, tiefe + 2, austritt);
    }
    aus.push_str(&format!("{e}    }}\n{e}}}\n"));
}

/// **At most this many `case` labels from one range arm (lane 227).**
///
/// A range arm spells an interval and a C `case` spells one value, so lowering a
/// range spells the interval OUT. Past 256 values that spelling is no longer a
/// lowering but an unfolding -- and 256 is not an arbitrary cap: the dense dispatch
/// of TODO §-1 *is* 256-way, so exactly the canonical dense arm still fits. A wider
/// interval belongs to interval guards (`if`); here it refuses with `C001`, never
/// silently unfolded. (With `N411`, fix lane F1, this cap also means a scrutinee
/// wider than a few hundred values must be narrowed before it is matched: `u16` full
/// needs 256 arms, `u32` full cannot be written.)
const INTPAT_SPANNE: u128 = 256;

/// One `case` label for one integer value, or `None` where C has no spelling.
///
/// Non-negative values go through `czahl` (the `u` suffix past `i64::MAX`, refusal
/// past `u64::MAX); negatives spell `-N`, which needs `N <= 2^63`. Anything outside
/// `-2^63 ..= 2^64 - 1` reaches no C integer type and is refused at the caller.
fn int_fall_text(w: i128) -> Option<String> {
    if w < 0 {
        let betrag = w.unsigned_abs();
        if betrag > (i64::MAX as u128) + 1 {
            return None;
        }
        // **`-2^63` has no literal spelling in C** (review G07 F5, fix lane F1): `-N` is
        // unary minus applied to `N`, and `9223372036854775808` does not fit `long long`, so
        // `cc` makes it unsigned and says so under `-Werror` (measured 2026-09-21, gcc
        // 16.2.1: "integer constant is so large that it is unsigned"). The usual spelling
        // is a constant expression, and a `case` label takes one.
        if betrag == (i64::MAX as u128) + 1 {
            return Some("(-9223372036854775807 - 1)".to_string());
        }
        Some(format!("-{betrag}"))
    } else {
        czahl(w as u128)
    }
}

/// One bound of an integer arm as an `i128`, or `None` after refusing.
///
/// The magnitude arrives as a `u128` (the lexer folds decimal, hex, binary and `_`
/// separators); `-2^127` is spelled `-` plus `2^127`, which does NOT fit `i128` as a
/// magnitude and gets its own arm instead of falling through the conversion.
fn int_grenze(
    g: &IntBound,
    span: gabbro_syntax::span::Span,
    absagen: &mut Absagen,
) -> Option<i128> {
    let w = if g.negative {
        if g.value == (1u128 << 127) {
            Some(i128::MIN)
        } else {
            i128::try_from(g.value).ok().and_then(|b| b.checked_neg())
        }
    } else {
        i128::try_from(g.value).ok()
    };
    let Some(w) = w else {
        weigere(
            absagen,
            span,
            "an integer `match` bound past `2^127 - 1` in magnitude -- no C integer type \
             holds it, and `cc` says `integer constant is too large for its type`. There is \
             no spelling to write here",
        );
        return None;
    };
    Some(w)
}

/// The case values of one integer arm pattern, or `None` after refusing.
///
/// An exact arm names one value; a range arm (`lo .. hi`, `lo ..< hi`) names every
/// value from `lo` to `hi`, bounds included or excluded as written. Three refusals,
/// all `C001`: an inverted or empty interval (no value could ever meet it), a value
/// C cannot spell (see `int_fall_text`), and an interval past `INTPAT_SPANNE`.
fn intpat_werte(
    pat: &IntPat,
    span: gabbro_syntax::span::Span,
    absagen: &mut Absagen,
) -> Option<Vec<i128>> {
    match pat {
        IntPat::Exact(g) => {
            let w = int_grenze(g, span, absagen)?;
            if int_fall_text(w).is_none() {
                weigere(
                    absagen,
                    span,
                    "an integer `match` value past `2^64 - 1` (or below `-2^63`) -- it \
                     reaches no C integer type, and `cc` says `integer constant is too \
                     large for its type`",
                );
                return None;
            }
            Some(vec![w])
        }
        IntPat::Range { lo, hi, exclusive } => {
            let a = int_grenze(lo, span, absagen)?;
            let mut b = int_grenze(hi, span, absagen)?;
            if *exclusive {
                let Some(v) = b.checked_sub(1) else {
                    weigere(
                        absagen,
                        span,
                        "an integer `match` range ending below everything -- `lo ..< \
                         -2^127` names no value, so no arm could ever run",
                    );
                    return None;
                };
                b = v;
            }
            if a > b {
                weigere(
                    absagen,
                    span,
                    "an integer `match` range whose lower bound is past its upper one -- \
                     no value could ever meet it, so no arm could ever run",
                );
                return None;
            }
            if int_fall_text(a).is_none() || int_fall_text(b).is_none() {
                weigere(
                    absagen,
                    span,
                    "an integer `match` range reaching past `2^64 - 1` (or below \
                     `-2^63`) -- its ends reach no C integer type, and `cc` says \
                     `integer constant is too large for its type`",
                );
                return None;
            }
            let anzahl = (b - a) as u128 + 1;
            if anzahl > INTPAT_SPANNE {
                weigere(
                    absagen,
                    span,
                    "`match` range wider than 256 values -- spelling it out would unfold \
                     the interval into one `case` label per value, and past the canonical \
                     dense width that unfolding is no longer a lowering. Split the interval \
                     with `if` guards",
                );
                return None;
            }
            Some((a..=b).collect())
        }
    }
}

/// **Integer `match` lowers to a C `switch` (lane 227).**
///
/// Lane 222 added the syntax (`3 =>`, `0 .. 255 =>`, `0 ..< 256 =>` over an integer
/// scrutinee); until this lane the emitter refused every such match with `C001`. The
/// lowering is a `switch` over the scrutinee expression: one `case` per exact arm,
/// one `case` per value of a range arm (stacked labels sharing one body). There is
/// no `default` and no `__builtin_unreachable`: unlike `D005`/`M123` no rule has
/// decided the distinction is closed, so handing that decision to the C compiler
/// would invent a fact. **A value no arm names skips the whole statement** -- which
/// is why the CHECKER refuses every integer `match` whose arms do not cover M1's
/// range of the scrutinee (`N411`, `crate::intmatch`, fix lane F1), and why the CLI
/// writes no C for a unit with any refusal. The `switch` below therefore meets only
/// covered matches; the flow passes still read an integer `match` as an `if` without
/// `else` (`crate::int_match_may_miss`, review G07) as a second line. The refusals
/// here (duplicates, labels outside the C type, mixed arms) mirror `N412`-`N414`
/// and stay as the emitter's own line.
///
/// A `switch` evaluates its controlling expression exactly once, so unlike the
/// `tagged` lowering above no temporary is needed for a call scrutinee: the
/// expression stands once in the header and nowhere else.
#[allow(clippy::too_many_arguments)]
fn match_int(
    m: &MatchStmt,
    s: &Stmt,
    aus: &mut String,
    u: &Namen,
    absagen: &mut Absagen,
    tiefe: usize,
    austritt: &Austritt,
) {
    let e = einzug(tiefe);
    // **Integer arms need an integer scrutinee -- read off the C type, not guessed.**
    // `wert_ctyp` answers from the declaration (parameter, `let` binding, callee
    // return); a scrutinee it cannot type has no `switch` to stand under, and a
    // non-integer one gives the arms nothing to meet.
    // **The C type's value range, which is also the range a `case` label must lie in**
    // (review G07, 2026-09-21). C converts every `case` constant to the PROMOTED type of
    // the controlling expression (C11 6.8.4.2p5): over a `uint32_t` scrutinee `case -1:`
    // becomes `case 4294967295:` and fires for `x == 4294967295`, while the arm said
    // `-1` and the model (`CFormMatch.lean`, `cases.lookup k` over `Int`) never meets it.
    // A label outside the scrutinee's type names no value the scrutinee can hold; it is
    // refused, never converted.
    let spanne: Option<(i128, i128)> = match wert_ctyp(&m.gegenstand, u).as_deref() {
        Some("uint8_t") => Some((0, u8::MAX as i128)),
        Some("uint16_t") => Some((0, u16::MAX as i128)),
        Some("uint32_t") => Some((0, u32::MAX as i128)),
        Some("uint64_t") => Some((0, u64::MAX as i128)),
        Some("int8_t") => Some((i8::MIN as i128, i8::MAX as i128)),
        Some("int16_t") => Some((i16::MIN as i128, i16::MAX as i128)),
        Some("int32_t") => Some((i32::MIN as i128, i32::MAX as i128)),
        Some("int64_t") => Some((i64::MIN as i128, i64::MAX as i128)),
        Some("bool") => Some((0, 1)),
        _ => None,
    };
    let Some((typ_min, typ_max)) = spanne else {
        weigere(
            absagen,
            s.span,
            "`match` with integer arms over a scrutinee of non-integer type -- the arms \
             name integer values, and only an integer (or `bool`) scrutinee gives them \
             something to meet",
        );
        return;
    };
    // **Expand every arm to its case values, in arm order.** A variant arm among
    // integer arms refuses here: it names a case, the others name values, and one
    // `switch` cannot meet both.
    let mut faelle: Vec<Vec<i128>> = Vec::with_capacity(m.zweige.len());
    for z in &m.zweige {
        let Some(pat) = &z.intpat else {
            weigere(
                absagen,
                z.span,
                "`match` mixing integer arms with variant arms -- every arm over an \
                 integer scrutinee names integer values, a variant arm names a case, \
                 and one `switch` cannot meet both",
            );
            return;
        };
        let Some(ws) = intpat_werte(pat, z.span, absagen) else {
            return;
        };
        if ws.iter().any(|w| *w < typ_min || *w > typ_max) {
            weigere(
                absagen,
                z.span,
                "an integer `match` arm naming a value outside its scrutinee's type -- C \
                 converts a `case` label to the scrutinee's type, so the label would fire \
                 for a DIFFERENT value than the one written",
            );
            return;
        }
        faelle.push(ws);
    }
    // **Two arms naming one value would be two `case` labels for it, and C rejects
    // the program (`duplicate case value`)** -- so the emitter refuses instead of
    // emitting what `cc` must refuse. Which arm SHOULD win is overlap and belongs to
    // the checker (`N412`, fix lane F1); two spellings of one value refuse here either way.
    {
        let mut gesehen = BTreeSet::new();
        for ws in &faelle {
            for w in ws {
                if !gesehen.insert(*w) {
                    weigere(
                        absagen,
                        s.span,
                        "`match` naming one integer value in two arms -- C allows one \
                         `case` label per value, so the second arm could never run",
                    );
                    return;
                }
            }
        }
    }
    aus.push_str(&format!(
        "{e}switch ({}) {{\n",
        ausdruck(&m.gegenstand, u, absagen)
    ));
    for (z, ws) in m.zweige.iter().zip(faelle.iter()) {
        let Some((letzt, vordere)) = ws.split_last() else {
            continue;
        };
        for w in vordere {
            let Some(t) = int_fall_text(*w) else {
                weigere(
                    absagen,
                    z.span,
                    "an integer `match` value past `2^64 - 1` (or below `-2^63`) -- it \
                     reaches no C integer type",
                );
                return;
            };
            aus.push_str(&format!("{e}case {t}:\n"));
        }
        let Some(t) = int_fall_text(*letzt) else {
            weigere(
                absagen,
                z.span,
                "an integer `match` value past `2^64 - 1` (or below `-2^63`) -- it \
                 reaches no C integer type",
            );
            return;
        };
        aus.push_str(&format!("{e}case {t}: {{\n"));
        for k in &z.rumpf.anweisungen {
            anweisung(k, aus, u, absagen, tiefe + 1, austritt);
        }
        aus.push_str(&format!("{e}}} break;\n"));
    }
    aus.push_str(&format!("{e}}}\n"));
}

/// **Der erklaerte Typ eines Ortes -- abgelesen, nicht geraten.**
///
/// Drei Wurzeln, und mehr gibt es in dieser Sprache nicht: ein Zeigerparameter auf eine
/// Tabelle, der **Name einer Tabelle selbst** (`beispiele/09`: die Tabelle IST der Speicher)
/// und ein `static`. Von dort aus traegt genau ein Weg weiter: `.slots[i].<feld>`.
///
/// > **Jede andere Gestalt liefert `None`, und dann weigert sich der Erzeuger.** Ein
/// > geratener Typ waere hier besonders teuer: an ihm haengt der Sonderwert, und ein
/// > falscher Sonderwert macht aus `None` einen gueltigen Index.
/// **The declared length of a fixed-length array type** -- or `None`.
///
/// It is a CONSTANT of the declaration, not a computed quantity: `[u64; STACK_WORTE]` says
/// it, and `umgebung.rs` has already folded `STACK_WORTE`. *A length the emitter had to work
/// out would be a second register over the same thing* (W7) -- this one reads.
fn feldlaenge_von(t: &TypExpr, u: &Namen) -> Option<u128> {
    let TypExpr::Feld(a) = t else { return None };
    // **A named constant is a length too.** `[u64; STACK_WORTE]` is the ordinary case, and
    // `konst_zahl` knows only literals -- *the same trap `scale` hit, and it is resolved the
    // same way: `umgebung.rs` has already folded the constant, and this reads its answer
    // instead of computing a second one* (W7).
    konst_oder_name(&a.laenge, u).and_then(|n| u128::try_from(n).ok())
}

fn ort_typ(o: &Ort, u: &Namen) -> Option<TypExpr> {
    let tabelle = u
        .tabellenzeiger
        .get(&o.basis.text)
        .cloned()
        .or_else(|| u.tabellen.iter().find(|t| **t == o.basis.text).cloned());
    if let Some(tab) = tabelle {
        // `h.slots[i].naechst` -- Feld, Index, Feld. Alles andere ist kein Slotfeld.
        if o.suffixe.len() != 3 {
            return None;
        }
        let (OrtSuffix::Feld(slots), OrtSuffix::Index(_), OrtSuffix::Feld(f)) =
            (&o.suffixe[0], &o.suffixe[1], &o.suffixe[2])
        else {
            return None;
        };
        if slots.text != "slots" {
            return None;
        }
        return u.slotfeld.get(&(tab, f.text.clone())).cloned();
    }
    if o.suffixe.is_empty() {
        return u
            .statiken
            .get(&o.basis.text)
            .or_else(|| u.parametertyp.get(&o.basis.text))
            .cloned();
    }
    // `s.len` -- ein Feld eines VERBUNDES, ueber einen Zeiger oder als Wert.
    if o.suffixe.len() == 1 {
        let OrtSuffix::Feld(f) = &o.suffixe[0] else { return None };
        let basis = u
            .parametertyp
            .get(&o.basis.text)
            .or_else(|| u.lokaltypexpr.get(&o.basis.text))?;
        let ziel = match basis {
            TypExpr::Zeiger(z) => &z.ziel,
            andere => andere,
        };
        let TypExpr::Pfad(p) = ziel else { return None };
        let n = &p.teile.last()?.text;
        return u.verbundfeld.get(&(n.clone(), f.text.clone())).cloned();
    }
    None
}

/// **Direct byte operations and the bound they carry (lane-141).**
///
/// A `format` field is a view: it lowers through a generated reader over
/// `v->bytes + offset` (`format_`, `lesewort`/`schreibwort`). A byte carrier
/// indexed DIRECTLY -- `PUFFER[i]`, `s.bytes[i]`, `t.bytes[i] = v` -- is not a
/// view and takes no reader: it lowers to the element itself. `byte_traeger`
/// names that path so it stops sharing the generic place lowering silently.
///
/// **The bound check comes from the run bound, and it is re-derived, not
/// trusted** (the `O9` stance: `ausdruck_obergrenze` reads the declaration
/// again rather than taking another pass's word). The carrier's declared
/// length (`feldlaenge_von`) is the bound each access is held against; the
/// checker (`M103`, plus `narrow`/`requires` at the source) has already proved
/// the access in range, so on a checked program the trap never fires -- *the
/// check is the emitter's second opinion, the proof stays the checker's.*
/// See `lese_bytes`/`schreib_bytes` for the two C shapes.
///
/// Returns the carrier (the place without its trailing index) and its length
/// in bytes, or `None` where the generic lowering stays in charge. `None` is
/// always byte-identical to today: every plain path below is the fallthrough,
/// never a re-spelling.
fn byte_traeger(o: &Ort, u: &Namen) -> Option<(Ort, u64)> {
    let idx = match o.suffixe.last() {
        Some(OrtSuffix::Index(e)) => e,
        _ => return None,
    };
    // Tables, devices, formats and accumulators are never byte carriers, even
    // where their names would resolve to something array-shaped. Each of them
    // owns its lowering further up (`ort`, the bank arms, `format_`); a byte
    // arm reaching into one would be the second register (W7).
    if u.tabellen.iter().any(|t| *t == o.basis.text)
        || u.tabellenzeiger.contains_key(&o.basis.text)
        || u.geraetezeiger.contains_key(&o.basis.text)
        || u.geraetewerte.contains_key(&o.basis.text)
        || u.formatwerte.contains_key(&o.basis.text)
        || u.akkus.contains(&o.basis.text)
    {
        return None;
    }
    let traeger = Ort {
        basis: o.basis.clone(),
        suffixe: o.suffixe[..o.suffixe.len() - 1].to_vec(),
        span: o.span,
    };
    // No arrow inside the carrier: a place reached through `->` is a device or
    // function-pointer lane, and neither is a byte run.
    if traeger
        .suffixe
        .iter()
        .any(|s| matches!(s, OrtSuffix::Ueber(_)))
    {
        return None;
    }
    let t = ort_typ(&traeger, u)?;
    let TypExpr::Feld(a) = &t else { return None };
    if ctyp(&a.element, u).as_deref() != Some("uint8_t") {
        return None;
    }
    let laenge = u64::try_from(feldlaenge_von(&t, u)?).ok()?;
    if laenge == 0 {
        return None;
    }
    // A constant index is the checker's own case: `M103` bounds every index by
    // the declared length, and a constant past it already carries the checker's
    // finding. The emitter writes the plain access, exactly as before.
    if konst_zahl(idx).is_some() {
        return None;
    }
    // A structurally re-derived bound at or under the run bound discharges the
    // same way -- but only over an UNSIGNED index type, where no negative value
    // can hide below the re-derived upper bound (`O9` again: the discharge is
    // read off the operator and the type, never off another pass's facts).
    if wert_ctyp(idx, u)
        .as_deref()
        .is_some_and(|t| c_obergrenze(t).is_some())
        && ausdruck_obergrenze(idx, u)
            .is_some_and(|h| h >= 0 && (h as u128) < u128::from(laenge))
    {
        return None;
    }
    Some((traeger, laenge))
}

/// An index the bound check may read twice (check, then use). A call would run
/// twice -- two effects for one written -- and a volatile device read would
/// sample twice, so either one falls back to the plain access, which evaluates
/// once. The checker still guards it; the emitter just states no second
/// opinion where stating one would cost an evaluation.
fn index_ist_rein(e: &Expr, u: &Namen) -> bool {
    match &e.art {
        ExprArt::Zahl(_)
        | ExprArt::Gleitkomma { .. }
        | ExprArt::Wahr
        | ExprArt::Falsch
        | ExprArt::FnWert(_)
        | ExprArt::Grund { .. } => true,
        ExprArt::Klammer(x) => index_ist_rein(x, u),
        ExprArt::Unaer(_, x) => index_ist_rein(x, u),
        ExprArt::Binaer(_, a, b) => index_ist_rein(a, u) && index_ist_rein(b, u),
        ExprArt::Ort(o) => {
            if u.geraetezeiger.contains_key(&o.basis.text)
                || u.geraetewerte.contains_key(&o.basis.text)
            {
                return false;
            }
            o.suffixe.iter().all(|s| match s {
                OrtSuffix::Feld(_) | OrtSuffix::Ueber(_) => true,
                OrtSuffix::Index(x) => index_ist_rein(x, u),
            })
        }
        _ => false,
    }
}

/// **`leseBytes`: the direct byte read with its run bound (lane-141).**
///
/// `s.bytes[i]` becomes `((uint64_t)(i) < LENu ? s->bytes[(uint64_t)(i)] :
/// (__builtin_trap(), (uint8_t)0))`. The `uint64_t` cast keeps `-Wsign-compare`
/// quiet over a signed index -- and keeps the semantics: a negative index
/// converts to a huge value, misses the bound, and traps. The trap arm needs
/// the comma value because a read is an expression; on a checked program it
/// never runs. An impure index (`None` from `index_ist_rein`) stays plain:
/// correctness of the evaluation count outranks the second opinion.
fn lese_bytes(o: &Ort, u: &Namen, absagen: &mut Absagen) -> Option<String> {
    let (traeger, laenge) = byte_traeger(o, u)?;
    let idx = match o.suffixe.last() {
        Some(OrtSuffix::Index(e)) => e,
        _ => return None,
    };
    if !index_ist_rein(idx, u) {
        return None;
    }
    let puffer = ort(&traeger, u, absagen);
    let i = ausdruck(idx, u, absagen);
    Some(format!(
        "((uint64_t)({i}) < {laenge}u ? {puffer}[(uint64_t)({i})] : (__builtin_trap(), (uint8_t)0))"
    ))
}

/// **`schreibBytes`: the direct byte write with its run bound (lane-141).**
///
/// `t.bytes[i] = v` becomes a scoped block that binds the index ONCE and traps
/// past the bound -- one evaluation whatever the index carries, so unlike the
/// read there is no purity fallback. Only `=` takes this path: a compound
/// assignment on a byte element is the checker's case (`M104` refuses the
/// `u8` overflow), and the generic tail stays in charge of it, exactly as
/// before. The block scope keeps `_gabbro_i` off every surrounding binding;
/// shadowing a user name there is legal C and changes nothing outside.
fn schreib_bytes(
    z: &Zuweisung,
    wert: &str,
    e: &str,
    u: &Namen,
    absagen: &mut Absagen,
) -> Option<String> {
    if !matches!(z.op, ZuwOp::Setzt) {
        return None;
    }
    let (traeger, laenge) = byte_traeger(&z.ziel, u)?;
    let idx = match z.ziel.suffixe.last() {
        Some(OrtSuffix::Index(x)) => x,
        _ => return None,
    };
    let puffer = ort(&traeger, u, absagen);
    let i = ausdruck(idx, u, absagen);
    Some(format!(
        "{e}{{\n{e}    uint64_t _gabbro_i = (uint64_t)({i});\n\
         {e}    if (!(_gabbro_i < {laenge}u)) __builtin_trap();\n\
         {e}    {puffer}[_gabbro_i] = {wert};\n{e}}}\n"
    ))
}

/// **Der C-Typ eines Ausdrucks -- ABGELESEN, und nur wo er eindeutig dasteht.**
///
/// Drei Quellen, und jede ist eine Deklaration: ein Ort (Slotfeld, `static`, Parameter), ein
/// Ruf (der Rueckgabetyp des Gerufenen, samt dem Geraetegriff eines `Vtd(basis)`) und eine
/// Rechnung ueber zweien davon, **die denselben Typ haben**.
///
/// > *Wo zwei Seiten verschieden erklaert sind, liefert diese Funktion nichts* -- und dann
/// > weigert sich der Erzeuger, statt eine der beiden zu waehlen.
/// **Rechnet dieser Operator?** Nur dort kann ein Umlauf entstehen; ein Vergleich oder ein
/// Bitschnitt bringt keinen Wert ueber die Breite.
fn rechnet(op: &BinOp) -> bool {
    matches!(
        op,
        BinOp::Plus
            | BinOp::Minus
            | BinOp::Mal
            | BinOp::SchiebLinks
            // PLAN-BITS section 4 (lane 88): the wrapping operators compute too
            // -- modulo 2^N on the unsigned storage type. `PlusSat` is NOT here:
            // it lowers to a saturating helper call, never to an operator.
            | BinOp::PlusWrap
            | BinOp::MinusWrap
            | BinOp::MalWrap
            | BinOp::SchiebLinksWrap
    )
}

/// **Der erklaerte Umlauf eines Ausdrucks, wenn er einen hat.** Nur ein Ort und eine Klammer
/// darum -- tiefer zu suchen hiesse raten, welcher der beiden Umlaeufe gilt.
fn umlaeufer_typ(e: &Expr, u: &Namen) -> Option<IntTy> {
    match &e.art {
        ExprArt::Klammer(x) => umlaeufer_typ(x, u),
        ExprArt::Ort(o) => {
            // **Zwei Formen laufen um, und beide muessen hier heraus.** Ein Slotfeld
            // (`t.slots[i].a`) und ein Register (`r.IDX`) -- die zweite fehlte in der ersten
            // Fassung, und `r.IDX = r.IDX * r.IDX` hatte damit dasselbe UB wie der Slot.
            if let Some(tab) = u
                .tabellenzeiger
                .get(&o.basis.text)
                .cloned()
                .or_else(|| u.tabellen.iter().find(|t| **t == o.basis.text).cloned())
            {
                if o.suffixe.len() != 3 {
                    return None;
                }
                let OrtSuffix::Feld(f) = &o.suffixe[2] else { return None };
                return u.umlaeufer.get(&(tab, f.text.clone())).cloned();
            }
            let g = u.geraetezeiger.get(&o.basis.text)?;
            if o.suffixe.len() != 1 {
                return None;
            }
            let OrtSuffix::Feld(f) = &o.suffixe[0] else { return None };
            u.geraete.get(g)?.umlaeufer.get(&f.text).cloned()
        }
        _ => None,
    }
}

/// **PLAN-BITS section 4 (lane 88): the overflow lowerings.**
///
/// Wrapping computes on the unsigned storage type and masks to `N` bits where `N`
/// is not the storage width (`(a + b) & mask`); saturating calls one of the two
/// file-scope helpers below with an explicit compare and no builtins. Every form
/// in both -- `static` functions, `if`/`else`, `return`, comparisons, casts,
/// `&` -- is already in the C-form census (`zaehle-c-formen.py`); `?:` is on its
/// NEVER list, which is why the clamp is a helper with `if`s and not a ternary.
///
/// All three range readers below are second opinions in the `O9` stance:
/// re-derived from declarations at the emission site, never trusted from the
/// checker -- and where nothing can be derived the site is refused with `C001`
/// instead of guessed.

/// Storage width in bits and signedness of a declared integer type.
fn storage(i: &IntTy) -> Option<(u32, bool)> {
    use gabbro_syntax::kw::Kw;
    let bits = match i.wort {
        Kw::U8 | Kw::I8 => 8,
        Kw::U16 | Kw::I16 => 16,
        Kw::U32 | Kw::I32 => 32,
        Kw::U64 | Kw::I64 => 64,
        _ => return None,
    };
    let signed = matches!(i.wort, Kw::I8 | Kw::I16 | Kw::I32 | Kw::I64);
    Some((bits, signed))
}

/// The C word for a storage width. `None` is not a guess -- the callers turn it
/// into `C001` by name.
fn storage_ctyp(bits: u32, signed: bool) -> Option<&'static str> {
    Some(match (bits, signed) {
        (8, false) => "uint8_t",
        (16, false) => "uint16_t",
        (32, false) => "uint32_t",
        (64, false) => "uint64_t",
        (8, true) => "int8_t",
        (16, true) => "int16_t",
        (32, true) => "int32_t",
        (64, true) => "int64_t",
        _ => return None,
    })
}

/// A translation-time integer: a literal, a parenthesised one, a negated one,
/// or a `const` name. Anything else is not known here -- and `None` says so.
fn constexpr_value(e: &Expr, u: &Namen) -> Option<i128> {
    match &e.art {
        ExprArt::Klammer(x) => constexpr_value(x, u),
        ExprArt::Zahl(n) => i128::try_from(*n).ok(),
        ExprArt::Unaer(UnOp::Negativ, x) => constexpr_value(x, u)?.checked_neg(),
        ExprArt::Ort(o) if o.suffixe.is_empty() => u.konstwert.get(&o.basis.text).copied(),
        _ => None,
    }
}

/// The promised interval of a declared integer type: the sugar's exact range,
/// a literal `lo .. hi` bound (`..<` excludes its top), or the full storage
/// word. `None` where no interval stands -- the caller refuses, never guesses.
fn intty_interval(t: &IntTy, u: &Namen) -> Option<(i128, i128)> {
    if let Some(z) = &t.zucker {
        if z.breite == 0 || z.breite > 64 {
            return None;
        }
        // Unsigned sugar promises `0 .. 2^N-1`; signed sugar promises the
        // symmetric interval around zero on the storage word.
        if !z.vorzeichen {
            return Some((0, (1i128 << z.breite) - 1));
        }
        let halb = 1i128 << (z.breite - 1);
        return Some((-halb, halb - 1));
    }
    if let Some(b) = &t.bereich {
        let lo = constexpr_value(&b.von, u)?;
        let mut hi = constexpr_value(&b.bis, u)?;
        if b.exklusiv {
            hi -= 1;
        }
        return Some((lo, hi));
    }
    let (bits, signed) = storage(t)?;
    if signed {
        let halb = 1i128 << (bits - 1);
        Some((-halb, halb - 1))
    } else {
        Some((0, (1i128 << bits) - 1))
    }
}

/// One side of a wrapping site: a declared word with its promised interval, or
/// an adopting literal point (storage `0` -- it takes the other's).
enum WrapSide {
    Word(u32, i128, i128),
    Literal(i128),
}

fn wrap_side(e: &Expr, u: &Namen) -> Option<WrapSide> {
    match &e.art {
        ExprArt::Klammer(x) => wrap_side(x, u),
        ExprArt::Zahl(n) => {
            let v = i128::try_from(*n).ok()?;
            if v < 0 {
                return None;
            }
            Some(WrapSide::Literal(v))
        }
        ExprArt::Ort(o) => {
            if o.suffixe.is_empty() {
                if let Some(w) = u.konstwert.get(&o.basis.text).copied() {
                    if w < 0 {
                        return None;
                    }
                    return Some(WrapSide::Literal(w));
                }
            }
            let TypExpr::Int(i) = ort_typ(o, u)? else {
                return None;
            };
            // Signed storage never wraps: signed overflow is undefined in C,
            // and the checker (`M153`) never lets it reach this emitter.
            let (bits, signed) = storage(&i)?;
            if signed {
                return None;
            }
            let (lo, hi) = intty_interval(&i, u)?;
            Some(WrapSide::Word(bits, lo, hi))
        }
        ExprArt::Ruf(r) => {
            let n = r.path()?.teile.last()?.text.clone();
            let TypExpr::Int(i) = u.funktionen.get(&n)?.rueck.as_ref()? else {
                return None;
            };
            let (bits, signed) = storage(i)?;
            if signed {
                return None;
            }
            let (lo, hi) = intty_interval(i, u)?;
            Some(WrapSide::Word(bits, lo, hi))
        }
        // A nested wrap is exact by construction -- its interval is its modulus.
        // A nested SHIFT resolves left-only (the amount is never exact).
        ExprArt::Binaer(op, x, y)
            if matches!(
                op,
                BinOp::PlusWrap | BinOp::MinusWrap | BinOp::MalWrap | BinOp::SchiebLinksWrap
            ) =>
        {
            let (bits, n) = if *op == BinOp::SchiebLinksWrap {
                wrap_shift_form(x, u)?
            } else {
                wrap_form(x, y, u)?
            };
            Some(WrapSide::Word(bits, 0, (1i128 << n) - 1))
        }
        // A nested clamp hands its interval up; the outer site checks exactness.
        ExprArt::Binaer(BinOp::PlusSat, x, y) => {
            let (bits, _, lo, hi) = saturation_facts(x, y, u)?;
            Some(WrapSide::Word(bits, lo, hi))
        }
        _ => None,
    }
}

/// Storage width in bits and exact bit count `N` of a wrapping site. Mirrors
/// the checker's `M153` rule joint-for-joint: unsigned storage, both sides
/// jointly exact, a literal side adopting when its point lies in the other's
/// interval. `None` is `C001` at the call site, never a guessed mask.
fn wrap_form(a: &Expr, b: &Expr, u: &Namen) -> Option<(u32, u32)> {
    let exact = |bits: u32, lo: i128, hi: i128| {
        crate::typen::exact_wrap_n(&crate::typen::IntBereich::genau(bits as u8, false, lo, hi))
    };
    let (bits, n) = match (wrap_side(a, u)?, wrap_side(b, u)?) {
        (WrapSide::Word(ba, l1, h1), WrapSide::Word(bb, l2, h2)) => {
            if ba != bb {
                return None;
            }
            let (n1, n2) = (exact(ba, l1, h1)?, exact(bb, l2, h2)?);
            if n1 != n2 {
                return None;
            }
            (ba, n1)
        }
        (WrapSide::Word(b, lo, hi), WrapSide::Literal(v))
        | (WrapSide::Literal(v), WrapSide::Word(b, lo, hi)) => {
            let n = exact(b, lo, hi)?;
            if v < 0 || v > (1i128 << n) - 1 {
                return None;
            }
            (b, n)
        }
        (WrapSide::Literal(_), WrapSide::Literal(_)) => return None,
    };
    if n == 0 || n > bits {
        return None;
    }
    Some((bits, n))
}

/// Storage width and bit count of a wrapping SHIFT site, from the VALUE side
/// alone: the amount only has to lie below `N` (the checker proved it), it is
/// never exact itself. A literal value side has no storage anywhere -- `C001`.
fn wrap_shift_form(x: &Expr, u: &Namen) -> Option<(u32, u32)> {
    let WrapSide::Word(bits, lo, hi) = wrap_side(x, u)? else {
        return None;
    };
    let n = crate::typen::exact_wrap_n(&crate::typen::IntBereich::genau(
        bits as u8,
        false,
        lo,
        hi,
    ))?;
    if n == 0 || n > bits {
        return None;
    }
    Some((bits, n))
}

/// Storage width, signedness and clamp interval of a saturating site. Mirrors
/// the checker's `M154` rule: one shared interval (a literal side adopting),
/// on any signedness and any width. `None` is `C001`, never a guessed bound.
fn saturation_facts(
    a: &Expr,
    b: &Expr,
    u: &Namen,
) -> Option<(u32, bool, i128, i128)> {
    /// Declared sides carry storage, sign and interval; a literal side only
    /// adopts the other's interval -- its own value never matters to the clamp,
    /// so the variant carries no payload (a dead field would be the finding the
    /// Baugatter names).
    enum Side {
        Word(u32, bool, i128, i128),
        Literal,
    }
    fn side(e: &Expr, u: &Namen) -> Option<Side> {
        match &e.art {
            ExprArt::Klammer(x) => side(x, u),
            ExprArt::Zahl(_) => Some(Side::Literal),
            ExprArt::Ort(o) => {
                if o.suffixe.is_empty() && u.konstwert.contains_key(&o.basis.text) {
                    return Some(Side::Literal);
                }
                let TypExpr::Int(i) = ort_typ(o, u)? else {
                    return None;
                };
                let (bits, signed) = storage(&i)?;
                let (lo, hi) = intty_interval(&i, u)?;
                Some(Side::Word(bits, signed, lo, hi))
            }
            ExprArt::Ruf(r) => {
                let n = r.path()?.teile.last()?.text.clone();
                let TypExpr::Int(i) = u.funktionen.get(&n)?.rueck.as_ref()? else {
                    return None;
                };
                let (bits, signed) = storage(i)?;
                let (lo, hi) = intty_interval(i, u)?;
                Some(Side::Word(bits, signed, lo, hi))
            }
            // A nested clamp hands its interval up; exactness is the outer
            // site's question, sharedness is answered here by construction.
            ExprArt::Binaer(BinOp::PlusSat, x, y) => {
                let (bits, signed, lo, hi) = saturation_facts(x, y, u)?;
                Some(Side::Word(bits, signed, lo, hi))
            }
            _ => None,
        }
    }
    let (bits, signed, lo, hi) = match (side(a, u)?, side(b, u)?) {
        (Side::Word(ba, sa, l1, h1), Side::Word(bb, sb, l2, h2)) => {
            if ba != bb || sa != sb || l1 != l2 || h1 != h2 {
                return None;
            }
            (ba, sa, l1, h1)
        }
        (Side::Word(b, s, lo, hi), Side::Literal)
        | (Side::Literal, Side::Word(b, s, lo, hi)) => (b, s, lo, hi),
        // Two literals: no interval anywhere -- the checker answers their exact
        // sum, and this emitter has no bound to clamp into. `C001`, honestly.
        (Side::Literal, Side::Literal) => return None,
    };
    // The clamp must sit inside the storage it is computed for; a declared
    // interval that already leaves its width never reaches this emitter (the
    // checker refuses it), but a second opinion that trusts nothing says so.
    let (slo, shi) = if signed {
        let halb = 1i128 << (bits - 1);
        (-halb, halb - 1)
    } else {
        (0, (1i128 << bits) - 1)
    };
    if lo < slo || hi > shi {
        return None;
    }
    Some((bits, signed, lo, hi))
}

/// The BASE operator of a wrapping site -- C has no `+%`, it computes `(a + b)`
/// on the unsigned storage type and the mask makes it modulo 2^N. `None` for
/// anything else; the caller turns it into `C001`.
fn wrap_op_text(op: &BinOp) -> Option<&'static str> {
    Some(match op {
        BinOp::PlusWrap => "+",
        BinOp::MinusWrap => "-",
        BinOp::MalWrap => "*",
        BinOp::SchiebLinksWrap => "<<",
        _ => return None,
    })
}

/// A wrapping site as C: on the unsigned storage type, masked to `N` bits when
/// `N` is not the storage width. The mask is a plain decimal literal (`czahl`
/// spells it, so `2^64 - 1` stays impossible the same way everywhere) --
/// no new C form either way.
fn wrap_c(
    op: &BinOp,
    a: &Expr,
    b: &Expr,
    bits: u32,
    n: u32,
    u: &Namen,
    absagen: &mut Absagen,
) -> String {
    let (Some(ct), Some(base)) = (storage_ctyp(bits, false), wrap_op_text(op)) else {
        weigere(absagen, a.span, "the unsigned storage type of a wrapping computation");
        return String::new();
    };
    let rt = if bits <= 32 { "uint32_t" } else { "uint64_t" };
    let core = format!(
        "(({rt})({}) {base} ({rt})({}))",
        ausdruck(a, u, absagen),
        ausdruck(b, u, absagen)
    );
    if n == bits {
        // Full width: C's unsigned arithmetic IS modulo 2^N (C11 6.2.5p9) --
        // the same shape the `wrapping` field attribute lowers to.
        return format!("({ct})({core})");
    }
    let Some(mask) = czahl(((1i128 << n) - 1) as u128) else {
        weigere(absagen, a.span, "the mask of a wrapping computation");
        return String::new();
    };
    format!("({ct})(({core}) & {mask})")
}

/// A saturating site as C: one of the two file-scope helpers with the clamp
/// interval as arguments. Operands ride up to 64 bits (value-preserving for
/// every storage width); the helper clamps without any wider type, so even
/// `u64`/`i64` need no `__int128` and no builtin.
fn saturation_c(
    a: &Expr,
    b: &Expr,
    bits: u32,
    signed: bool,
    lo: i128,
    hi: i128,
    u: &Namen,
    absagen: &mut Absagen,
) -> String {
    let (Some(ct), wide) = (
        storage_ctyp(bits, signed),
        if signed { "int64_t" } else { "uint64_t" },
    ) else {
        weigere(absagen, a.span, "the storage type of a saturating computation");
        return String::new();
    };
    // Bounds as 64-bit literals: `czahl` spells the wide ones with the same `u`
    // suffix every other wide literal carries; a negative bound rides on unary
    // minus, which is how the language spells it too.
    fn bound(
        v: i128,
        signed: bool,
        span: gabbro_syntax::span::Span,
        absagen: &mut Absagen,
    ) -> String {
        if signed && v < 0 {
            match czahl((-v) as u128) {
                Some(t) => format!("-{t}"),
                None => {
                    weigere(absagen, span, "a clamp bound past `2^64 - 1`");
                    String::new()
                }
            }
        } else {
            match czahl(v as u128) {
                Some(t) => t,
                None => {
                    weigere(absagen, span, "a clamp bound past `2^64 - 1`");
                    String::new()
                }
            }
        }
    }
    let (lo_t, hi_t) = (
        bound(lo, signed, a.span, absagen),
        bound(hi, signed, a.span, absagen),
    );
    if lo_t.is_empty() || hi_t.is_empty() {
        return String::new();
    }
    let helper = if signed {
        "_gabbro_sat_i"
    } else {
        "_gabbro_sat_u"
    };
    format!(
        "({ct})({helper}(({wide})({}), ({wide})({}), ({wide})({lo_t}), ({wide})({hi_t})))",
        ausdruck(a, u, absagen),
        ausdruck(b, u, absagen),
    )
}

/// The two saturating helpers, with the explicit compare and no builtins.
///
/// Both compute so that no intermediate ever leaves 64 bits: the unsigned one
/// subtracts only `b <= hi` (`hi - b >= 0`, and `a > hi - b` is `a + b > hi`
/// without ever forming the sum); the signed one guards each side by the sign
/// of `b` (`hi - b >= 0` needs `b <= hi`, `lo - b <= 0` needs `b >= lo` --
/// both hold for every value the checker lets through). `cc -Wconversion`
/// stays silent: every narrowing is a cast the generator wrote down.
const SATURATION_PRELUDE: &str = "\
/* PLAN-BITS section 4 (lane 88): saturating `+|` -- an explicit compare, no builtins. */\n\
static uint64_t _gabbro_sat_u(uint64_t a, uint64_t b, uint64_t lo, uint64_t hi) __attribute__((unused));\n\
static uint64_t _gabbro_sat_u(uint64_t a, uint64_t b, uint64_t lo, uint64_t hi) {\n\
    if (a > hi - b) {\n\
        return hi;\n\
    }\n\
    if (a + b < lo) {\n\
        return lo;\n\
    }\n\
    return a + b;\n\
}\n\
static int64_t _gabbro_sat_i(int64_t a, int64_t b, int64_t lo, int64_t hi) __attribute__((unused));\n\
static int64_t _gabbro_sat_i(int64_t a, int64_t b, int64_t lo, int64_t hi) {\n\
    if ((b > 0) && (a > hi - b)) {\n\
        return hi;\n\
    }\n\
    if ((b < 0) && (a < lo - b)) {\n\
        return lo;\n\
    }\n\
    return a + b;\n\
}\n";

/// Does this unit saturate? A syntactic pre-scan for `+|` over bodies,
/// contracts and initialisers -- no types involved, so it answers presence
/// only, and both helpers are emitted on `true` (the unused one silenced, like
/// every unused generated reader). Missing a site would be a call to a
/// function that is not there -- so the walk covers every position that
/// lowers a run-time expression, and whatever it cannot see (translation-time
/// bounds, which the checker refuses for these operators first) cannot reach
/// the C either.
fn needs_saturation(baum: &Programm) -> bool {
    fn suffixe(o: &Ort) -> bool {
        o.suffixe.iter().any(|s| match s {
            OrtSuffix::Index(x) => expr(x),
            _ => false,
        })
    }
    fn expr(e: &Expr) -> bool {
        match &e.art {
            ExprArt::Binaer(BinOp::PlusSat, _, _) => true,
            ExprArt::Binaer(_, a, b) => expr(a) || expr(b),
            ExprArt::Klammer(x) | ExprArt::Unaer(_, x) => expr(x),
            ExprArt::Ort(o) => suffixe(o),
            ExprArt::Alt(o) => suffixe(o),
            ExprArt::Ruf(r) => r.argumente.iter().any(expr),
            // **A library call carries run-time arguments like a call.** The
            // region is raw tokens, not expressions, so there is nothing to
            // walk there -- a `+|` inside it is text the checker refuses
            // (`N057`) before it could ever lower.
            ExprArt::LibraryCall(l) => l.args.iter().any(expr),
            // **Lane 111:** a `+|` inside a table element lowers like any
            // other -- the elements are ordinary expressions.
            ExprArt::ArrayLit(es) => es.iter().any(expr),
            ExprArt::Eingebaut(b) => match b.as_ref() {
                Eingebaut::Sizeof(t) | Eingebaut::Lenof(t) => match t {
                    TypOderOrt::Ort(o) => suffixe(o),
                    TypOderOrt::Typ(_) => false,
                },
                Eingebaut::Aligned(x, y) => expr(x) || expr(y),
            },
            ExprArt::Zaehle { rumpf, .. } => pred(rumpf),
            ExprArt::Zahl(_)
            | ExprArt::Gleitkomma { .. }
            | ExprArt::Wahr
            | ExprArt::Falsch
            | ExprArt::FnWert(_)
            | ExprArt::Ergebnis
            | ExprArt::Grund { .. } => false,
        }
    }
    fn domaene(d: &Domaene) -> bool {
        match d {
            Domaene::SlotsVon(o)
            | Domaene::NachfahrenVon(o)
            | Domaene::VorfahrenVon(o)
            | Domaene::Schlange(o)
            | Domaene::ElementeVon(o)
            | Domaene::AbbildungenVon(o) => suffixe(o),
            Domaene::KetteIn { ort, .. } => suffixe(ort),
            Domaene::FelderVon(_) | Domaene::Threads => false,
        }
    }
    fn pred(p: &Pred) -> bool {
        match &p.art {
            PredArt::Vergleich(e) => expr(e),
            PredArt::Klammer(x) | PredArt::Nicht(x) => pred(x),
            PredArt::Und(a, b) | PredArt::Oder(a, b) | PredArt::Folgt(a, b) => {
                pred(a) || pred(b)
            }
            PredArt::Quantor(q) => domaene(&q.domaene) || pred(&q.rumpf),
            PredArt::Element(e, d) => expr(e) || domaene(d),
            PredArt::Erreicht { von, nach, .. } => suffixe(von) || suffixe(nach),
            PredArt::Held { .. } => false,
        }
    }
    fn block(b: &Block) -> bool {
        b.anweisungen.iter().any(stmt)
    }
    fn stmt(s: &Stmt) -> bool {
        match &s.art {
            StmtArt::Let(l) => expr(&l.wert),
            StmtArt::LetSonst(l) => match &l.quelle {
                LetQuelle::Ruf(r) => r.argumente.iter().any(expr) || block(&l.sonst),
                LetQuelle::Ort(o) => suffixe(o) || block(&l.sonst),
            },
            StmtArt::Zuweisung(z) => suffixe(&z.ziel) || expr(&z.wert),
            StmtArt::Wenn(w) => {
                w.zweige.iter().any(|(c, b)| expr(c) || block(b))
                    || w.sonst.as_ref().is_some_and(block)
            }
            StmtArt::Match(m) => {
                expr(&m.gegenstand) || m.zweige.iter().any(|z| block(&z.rumpf))
            }
            StmtArt::Schleife(s) => match s.as_ref() {
                Schleife::Traverse(t) => {
                    t.gegenstand.as_ref().is_some_and(expr)
                        || domaene(&t.domaene)
                        || t.mass.as_ref().is_some_and(expr)
                        || t.touches.as_ref().is_some_and(wirkungen)
                        || block(&t.rumpf)
                }
                Schleife::Retry(r) => {
                    r.bis.as_ref().is_some_and(pred)
                        || expr(&r.schranke)
                        || r.invariante.as_ref().is_some_and(pred)
                        || block(&r.rumpf)
                }
                Schleife::Forever(f) => {
                    expr(&f.je_durchgang)
                        || f.invariante.as_ref().is_some_and(pred)
                        || block(&f.rumpf)
                }
            },
            StmtArt::Bricht(b) => block(&b.rumpf),
            // **Lane O-1:** the child path is walked like any block.
            StmtArt::Child(x) => block(x),
            StmtArt::Narrow(n) => {
                suffixe(&n.ort)
                    || match &n.ziel {
                        NarrowZiel::Bereich(b) => expr(&b.von) || expr(&b.bis),
                        NarrowZiel::Endlich(_) => false,
                    }
                    || block(&n.sonst)
            }
            StmtArt::Sperrt(s) => suffixe(&s.sperre) || block(&s.rumpf),
            StmtArt::Observiert(o) => block(&o.rumpf),
            StmtArt::Publish(p) => {
                suffixe(&p.ziel) || expr(&p.wert) || block_in_nutzlast(&p.nutzlast)
            }
            StmtArt::AwaitLoad(a) => {
                suffixe(&a.quelle) || a.erwartet.iter().any(suffixe)
            }
            StmtArt::Exchange(x) => {
                suffixe(&x.ort)
                    || match &x.form {
                        XForm::Update {
                            schranke,
                            rumpf,
                            ..
                        } => schranke.as_ref().is_some_and(expr) || block(rumpf),
                        XForm::Vergleich { wert, bedingung, .. } => {
                            expr(wert) || pred(bedingung)
                        }
                    }
                    || x.nutzlast.as_ref().is_some_and(block_in_nutzlast)
                    || x.erwartet.as_ref().is_some_and(|os| os.iter().any(suffixe))
            }
            StmtArt::Return(e) => e.as_ref().is_some_and(expr),
            StmtArt::Ruf(r) => r.argumente.iter().any(expr),
            // **Same as the expression arm above:** the arguments lower, the
            // region is raw text the checker refuses before it could lower.
            StmtArt::LibraryCall(l) => l.args.iter().any(expr),
            // **«E4»:** the stored value lowers like any bound value, and
            // the full-arena continuation with it; `reset` lowers to a
            // counter store with no expression in it.
            StmtArt::Alloc(a) => {
                expr(&a.wert) || a.sonst.as_ref().is_some_and(block)
            }
            StmtArt::ResetArena(_) => false,
            // **Lane 253:** `start` roots are paths the unit never evaluates
            // -- the driver (not this template) turns them into threads.
            StmtArt::Start(_) => false,
            // **Lane 257:** `grow` is refused by name in `anweisung`
            // below, so the template never evaluates its amount or its
            // `else` -- same shape as `start` until the arm lane lands.
            StmtArt::Grow(_) => false,
            StmtArt::Leave(_) | StmtArt::Next(_) => false,
        }
    }
    fn block_in_nutzlast(n: &Nutzlast) -> bool {
        match n {
            Nutzlast::Orte(os) => os.iter().any(suffixe),
            Nutzlast::Nichts(_) => false,
        }
    }
    // Effect lists name places; an index in one is walked, not trusted --
    // the scan over-approximates on purpose (see `needs_saturation`).
    fn wirkungen(w: &Wirkungen) -> bool {
        w.liste.iter().any(|x| match &x.art {
            WirkungArt::Liest(o)
            | WirkungArt::Schreibt(o)
            | WirkungArt::Sperrt(o)
            | WirkungArt::SperrtGeteilt(o)
            | WirkungArt::Verbraucht(o)
            | WirkungArt::Veroeffentlicht(o) => suffixe(o),
            WirkungArt::Maskiert(_)
            | WirkungArt::Belegt(_)
            | WirkungArt::Divergiert
            | WirkungArt::Rein => false,
        })
    }
    let mut ja = false;
    crate::fuer_jedes_item(baum, &mut |item| {
        if ja {
            return;
        }
        match &item.art {
            ItemArt::Funktion(f) => {
                ja |= f.requires.iter().any(pred)
                    || f.ensures.iter().any(pred)
                    || f.decreases.as_ref().is_some_and(expr)
                    || f.costs.as_ref().is_some_and(expr);
                if let FnRumpf::Block(b) = &f.rumpf {
                    ja |= block(b);
                }
            }
            ItemArt::Konst(k) => ja |= expr(&k.wert),
            ItemArt::Statisch(s) => ja |= expr(&s.wert),
            _ => {}
        }
    });
    ja
}

/// The largest value an unsigned C integer type can hold. `None` for everything else --
/// a signed type, a pointer, a struct: none of them is a narrowing this function may judge.
fn c_obergrenze(t: &str) -> Option<i128> {
    Some(match t {
        "uint8_t" => 255,
        "uint16_t" => 65535,
        "uint32_t" => 4294967295,
        "uint64_t" => i128::from(u64::MAX),
        _ => return None,
    })
}

/// **The bound the CHECKER carries for a bare `index into T`: `count N` minus one.**
///
/// `option index into T` is deliberately excluded -- its widest value is the SENTINEL `N`,
/// not `N - 1`, and an option has no business in an integer field in the first place.
fn indexschranke(e: &Expr, u: &Namen) -> Option<i128> {
    let ExprArt::Ort(o) = &e.art else { return None };
    match ort_typ(o, u) {
        Some(TypExpr::Index { tabelle, optional: false, .. }) => {
            u.kapazitaet.get(&tabelle.text).copied().map(|n| n - 1)
        }
        _ => None,
    }
}

/// **`O9`, measured 2026-09-03: a structural upper bound, re-derived independently of
/// `m1.rs`.** Same stance as `indexschranke` right above -- the checker has already refused
/// any program whose value does not fit (`M101`), so this is a second, independent opinion
/// and not a new proof obligation this emitter is taking on.
///
/// `indexschranke` only ever answers for a bare `Ort` (a place with a declared `index into
/// T`). Everything else -- a mask, a shift, a typed local read back -- fell through to
/// `_ => text` in `verenge`, and `wunsch >> 32`/`wunsch & 4294967295` on a `u64` register
/// wrote a bare, uncast narrowing assignment into a `u32` register even though `M101`
/// proves both fit: `messung/proben/probe-transport-merkmale-aushandeln.gab`,
/// `messung/ERZEUGERREST.md` D20. `zaehle-c-formen.py --uebersetzer` -- the mechanical check
/// `BEWEIS.md` §2 line 7 asks for -- reported one `-Wconversion` hit over the whole corpus
/// where the never-list promises "none, but to be checked mechanically."
///
/// The two operators covered are exactly the ones the measurement needed:
///
/// * `x & MASKE` can only turn bits off, so the result never exceeds the literal mask,
///   whatever `x` is -- `wunsch & 4294967295` is bounded by `4294967295` regardless of
///   `wunsch`'s own width.
/// * `x >> N` for a literal `N` never exceeds `x`'s own bound shifted the same amount --
///   a `u64` shifted right by 32 is bounded by `u64::MAX >> 32`, which is exactly
///   `u32::MAX`.
///
/// **This is a second opinion and not a promise borrowed from `m1.rs`.** Nothing here reads
/// M1's facts; it re-derives the bound from the operator and the literal alone, the same way
/// `indexschranke` re-derives an index bound from `count` rather than trusting the checker's
/// word for it.
fn ausdruck_obergrenze(e: &Expr, u: &Namen) -> Option<i128> {
    match &e.art {
        ExprArt::Klammer(x) => ausdruck_obergrenze(x, u),
        ExprArt::Zahl(n) => i128::try_from(*n).ok(),
        ExprArt::Ort(_) => indexschranke(e, u),
        ExprArt::Binaer(BinOp::BitUnd, a, b) => match (&a.art, &b.art) {
            (_, ExprArt::Zahl(n)) | (ExprArt::Zahl(n), _) => i128::try_from(*n).ok(),
            _ => None,
        },
        ExprArt::Binaer(BinOp::SchiebRechts, a, b) => {
            let ExprArt::Zahl(n) = &b.art else { return None };
            let basis = ausdruck_obergrenze(a, u)
                .or_else(|| wert_ctyp(a, u).as_deref().and_then(c_obergrenze))?;
            if *n >= 128 {
                Some(0)
            } else {
                Some(basis >> n)
            }
        }
        _ => None,
    }
}

/// **The width the checker knows, WRITTEN DOWN where C cannot see it** (2026-08-31).
///
/// `messung/treiber/virtio-net.gab`:236 writes `a.slots[i].kopf = i;` with
/// `i : index into Deskring`, `count QGROESSE = 8`, into a `u16` field. `index into T` lowers
/// to `uint32_t` (the representation the `option` sentinel hangs on), so the C reads
/// `a->slots[i].kopf = i;` -- **a silent narrowing.** `cc -Wconversion` names it twice,
/// `-Wall -Wextra` names neither. *The same family as `F06`, one file on: the checker knows
/// the bound -- three bits are enough -- and the producer lowered 32.*
///
/// **The cast is not a promise this function invents.** `M101` in the checker (`m1.rs`)
/// refuses the program when the value does NOT fit: measured on 2026-08-31, `k.slots[i].kopf = i` with `count 100000`
/// into a `u16` field gives
///
/// ```text
/// error: [M101] the assignment requires `u16`, the value has `u32 in 0 .. 99999`
/// ```
///
/// -- so no program that reaches this emitter carries a narrowing that loses a value. *The
/// checker already SAYS it; it says it in Gabbro, to a Gabbro reader. What was missing is
/// the sentence in C.* The bound is nevertheless read again here rather than trusted: an
/// emitter that writes a cast on another pass's word writes a promise it cannot see.
///
/// **And the other way out was NOT taken.** `index into T` could lower to the narrowest
/// width its `count` needs -- `uint8_t` for `count 8` -- and then the assignment would be a
/// WIDENING and silent by itself. That changes the representation of every index in every
/// signature, and the `option` sentinel premise (`N` must fit the index word,
/// `beweise/Option_Sonderwert.thy`) with it. *A decision about the ABI is not a side effect
/// of a warning*; `messung/GRAMMATIKTAFEL.md` §8 left it open and it stays open.
fn verenge(text: String, e: &Expr, ziel: Option<&str>, u: &Namen) -> String {
    let Some(ziel) = ziel else { return text };
    let (Some(zmax), Some(qmax)) = (
        c_obergrenze(ziel),
        wert_ctyp(e, u).as_deref().and_then(c_obergrenze),
    ) else {
        return text;
    };
    // Widening or equal: C converts without losing anything, and says nothing about it.
    if qmax <= zmax {
        return text;
    }
    // **`O9`: `indexschranke` first, `ausdruck_obergrenze` second.** The first answers for a
    // bare `index into T` place; the second re-derives a bound structurally for a mask or a
    // literal shift (`messung/ERZEUGERREST.md` D20). Neither trusts M1's own word for it --
    // both re-derive the bound from what the emitter can see on its own.
    match indexschranke(e, u).or_else(|| ausdruck_obergrenze(e, u)) {
        // It fits, and the declaration says so. Write it down.
        Some(h) if h <= zmax => format!("({ziel})({text})"),
        // It does NOT fit, or nothing here bounds it. **Then nothing is written** -- a cast
        // would be a claim, and `M101` in the checker is the pass that makes claims about
        // ranges.
        _ => text,
    }
}

fn wert_ctyp(e: &Expr, u: &Namen) -> Option<String> {
    match &e.art {
        // **«SG-24»: a count has the C type of its domain's index word.** An
        // index-word domain (`slots of`, `descendants of`, `ancestors of`) counts
        // at most `count` slots, and `count` fills the index word or the table is
        // refused -- so the counter returns `uint32_t`, exactly like the loop
        // variable below, and no narrowing cast is ever written for it. An array
        // domain (`elems of`) counts up to its length and returns `uint64_t`,
        // like its loop variable. *The emitter writes no narrowing casts
        // anywhere (`verenge` only narrows what it re-derives); picking the
        // width up front keeps the first width-crossing program from tripping
        // `-Wconversion`.* The Gabbro range (`0 ..= N`) is M1's fact and lives
        // in the checker, not in the C.
        ExprArt::Zaehle { domaene, .. } => Some(
            match domaene {
                Domaene::SlotsVon(_)
                | Domaene::NachfahrenVon(_)
                | Domaene::VorfahrenVon(_) => "uint32_t",
                _ => "uint64_t",
            }
            .to_string(),
        ),
        // **The signature first, the body second** (2026-08-25). A name a declaration knows is
        // answered from the declaration; only a `let`-bound local falls through to
        // `lokaltyp`, which `lokale_lets` filled from declarations as well. *The order is the
        // one `eigene_sicht` states: what a function binds itself comes from its own
        // declaration and from no other.*
        ExprArt::Ort(o) if o.suffixe.is_empty() => match u.parametertyp.get(&o.basis.text) {
            Some(t) => ctyp(t, u),
            // **Lane 167: a bare nullary case answers its sum for an unannotated
            // `let`.** `let m = Leer;` carries no annotation, so the C type comes
            // from the value -- through the same guard `ort` reads, and only for
            // the nullary form (a bare name over a payload case is the checker's
            // `N283`, and this arm never runs on an accepted tree for one).
            None => ort_typ(o, u)
                .and_then(|t| ctyp(&t, u))
                .or_else(|| {
                    if fall_belegt(&o.basis.text, u) {
                        return None;
                    }
                    match varianten_traeger(&o.basis.text, u) {
                        VariantenDeutung::Eine(summe, v) if v.nutzlast.is_none() => {
                            Some(summe.to_string())
                        }
                        _ => None,
                    }
                })
                .or_else(|| u.lokaltyp.get(&o.basis.text).cloned()),
        },
        ExprArt::Ort(o) => ort_typ(o, u)
            .and_then(|t| ctyp(&t, u))
            .or_else(|| register_ctyp(o, u)),
        ExprArt::Klammer(x) => wert_ctyp(x, u),
        ExprArt::Binaer(op, a, b) => {
            // Ein Vergleich ist `bool`, egal worueber; eine Rechnung traegt den Typ ihrer
            // Seiten -- und nur, wenn beide denselben nennen.
            if matches!(
                op,
                BinOp::Gleich
                    | BinOp::Ungleich
                    | BinOp::Kleiner
                    | BinOp::Groesser
                    | BinOp::KleinerGleich
                    | BinOp::GroesserGleich
                    | BinOp::Und
                    | BinOp::Oder
            ) {
                return Some("bool".into());
            }
            let (x, y) = (wert_ctyp(a, u), wert_ctyp(b, u));
            match (x, y) {
                (Some(x), Some(y)) if x == y => Some(x),
                (Some(x), None) if matches!(b.art, ExprArt::Zahl(_)) => Some(x),
                (None, Some(y)) if matches!(a.art, ExprArt::Zahl(_)) => Some(y),
                _ => None,
            }
        }
        // **`Vtd(basis)` ist der GRIFF eines Geraets, kein Ruf** -- siehe `ruf`.
        ExprArt::Ruf(r) => {
            let n = &r.path()?.teile.last()?.text;
            if u.geraete.contains_key(n) {
                return Some(n.clone());
            }
            // **Bit intrinsics (PLAN-BITS §3): the result width is the operand's
            // width.** `let y = clz(x);` without an annotation needs a C type
            // from the value, and the intrinsic's result lives in the operand's
            // own width (`0 .. w-1` still lowers to `uintN_t`). `None` falls
            // into the caller's `C001` by name -- the same honest exit an
            // unresolvable `let` value gets.
            if crate::ist_bitintrinsik(n)
                && r.path().is_some_and(|p| p.teile.len() == 1)
            {
                let a = r.argumente.first()?;
                let w = intrinsik_breite(a, u)?;
                return Some(match w {
                    8 => "uint8_t",
                    16 => "uint16_t",
                    32 => "uint32_t",
                    64 => "uint64_t",
                    _ => return None,
                }
                .to_string());
            }
            // **Und sonst: der erklaerte Rueckgabetyp des Gerufenen.** Er stand die ganze
            // Zeit da; gefragt hat ihn niemand.
            //
            // **Lane 167: a `tagged` case answers its owning sum.** `let m = Kurz(x)`
            // without an annotation needs a C type from the value, and the case is
            // not a callee -- `u.funktionen` below knows nothing of it. The guard is
            // the checker's function-wins rule without the module half (same reason
            // as in `ruf` above); several owners answer nothing, like any
            // unresolvable `let` value.
            if r.path().is_some_and(|p| p.teile.len() == 1)
                && !r.ist_verbundwert()
                && !u.funktionen.contains_key(n)
                && !u.uebergaenge.contains_key(n)
                && !u.geraete.contains_key(n)
            {
                if let VariantenDeutung::Eine(summe, _) = varianten_traeger(n, u) {
                    return Some(summe.to_string());
                }
            }
            ctyp(u.funktionen.get(n)?.rueck.as_ref()?, u)
        }
        // **Lane E5:** a library call in binding position answers its
        // declared result, like any call's -- the same declaration `ruf`
        // reads above, through the same short-name rule. The payload the
        // call carries changes the argument, not the answer.
        ExprArt::LibraryCall(r) => {
            let n = &r.function.text;
            ctyp(u.funktionen.get(n)?.rueck.as_ref()?, u)
        }
        _ => None,
    }
}

/// **Die C-Wortbreite eines Registerzugriffs -- ABGELESEN aus der `device`-Deklaration.**
///
/// `d.ST` und `d.ST.IDX` senken beide zu einem `*(volatile <breite> *)`-Zugriff ab; ein
/// Bitfeld wird daraus geschoben und maskiert, also traegt es dieselbe Breite. Die Breite
/// steht in der Deklaration, und gefragt hat sie hier bis 2026-08-20 niemand.
///
/// **Warum das gerade jetzt faellt:** seit «B33» gibt ein Vergleich auf einer Registerstelle
/// keine Tatsache mehr, und der Ausweg ist `let i = d.ST.IDX;` -- die Bindung einmal lesen
/// und SIE verengen. *Eine Regel, die eine Form erzwingt, die der Erzeuger nicht absenkt,
/// waere ein Verbot ohne Tuer gewesen.*
fn register_ctyp(o: &Ort, u: &Namen) -> Option<String> {
    let g = u
        .geraetezeiger
        .get(&o.basis.text)
        .or_else(|| u.geraetewerte.get(&o.basis.text))?;
    let OrtSuffix::Feld(r) = o.suffixe.first()? else {
        return None;
    };
    if o.suffixe.len() > 2 {
        return None;
    }
    let dev = u.geraete.get(g)?;
    if let Some((_, b)) = dev.reg.get(&r.text) {
        return Some(b.clone());
    }
    // **A declared device PARAMETER is not a register, and it has a type all the same.**
    // Without this `let platz = q.AVAIL_IDX % q.n;` had no type and the emitter refused with
    // `C001 let without a resolvable type` -- *a refusal whose named reason was the `let`,
    // while the unresolvable half was `q.n`.*
    if o.suffixe.len() == 1 {
        return dev
            .parameter
            .iter()
            .find(|(n, _)| *n == r.text)
            .map(|(_, c)| c.clone());
    }
    None
}

/// Ist dieser Ort ein `option index into T`? Dann die Zieltabelle.
///
/// **Alles andere liefert `None`, und dann weigert sich der Erzeuger** statt einen
/// Sonderwert zu raten.
fn option_ziel(o: &Ort, u: &Namen) -> Option<String> {
    match ort_typ(o, u) {
        Some(TypExpr::Index { tabelle, optional: true, .. }) => Some(tabelle.text),
        _ => None,
    }
}

/// Liefert den Tabellennamen, wenn dieser Ausdruck ein `option index into T` ist.
fn option_quelle(e: &Expr, u: &Namen) -> Option<String> {
    match &e.art {
        ExprArt::Ruf(r) => u
            .funktionen
            .get(&r.path()?.teile.last()?.text)?
            .option_rueck
            .clone(),
        ExprArt::Ort(o) => option_ziel(o, u),
        _ => None,
    }
}

/// **`None` und `Some(i)` als WERT -- und der Sonderwert kommt von der Zieltabelle.**
///
/// Die Absenkung steht in `beweise/Option_Sonderwert.thy`: `None` ist `count` selbst, der
/// erste Index, den es nicht gibt (`sonderwert_ausserhalb`), und die Kodierung ist auf dem
/// gueltigen Bereich injektiv (`kodiere_injektiv`). **Die Praemisse des dritten Satzes
/// prueft `tabelle`**, wo das `#define` entsteht -- ein volles Wort hat keinen Platz fuer
/// „keine", und das ist dort eine Absage.
///
/// Liefert `None`, wenn der Ausdruck gar kein Konstruktor ist -- dann uebersetzt der Rufer
/// ihn gewoehnlich.
fn option_wert(e: &Expr, tab: &str, u: &Namen, absagen: &mut Absagen) -> Option<String> {
    let name = match &e.art {
        ExprArt::Ruf(r) => r.path()?.teile.last()?.text.clone(),
        ExprArt::Ort(o) if o.suffixe.is_empty() => o.basis.text.clone(),
        _ => return None,
    };
    match name.as_str() {
        "None" => Some(format!("{tab}_NONE")),
        "Some" => {
            let ExprArt::Ruf(r) = &e.art else {
                weigere(absagen, e.span, "`Some` without an argument");
                return Some(String::new());
            };
            match r.argumente.first() {
                Some(a) => Some(ausdruck(a, u, absagen)),
                None => {
                    weigere(absagen, e.span, "`Some` without an argument");
                    Some(String::new())
                }
            }
        }
        _ => None,
    }
}

/// Does this expression yield a ghost? Today: a call to a function with a ghost return.
/// **Schreibt dieser Rumpf irgendwo `*_grund`?** (Stufe 7, 2026-08-21)
///
/// Genau dann, wenn ein `return R::F;` auf irgendeinem Pfad darin steht. Der Erzeuger
/// braucht die Antwort fuer eine Zeile, die er sonst zu viel schreibt -- `(void)_grund;`
/// neben einem `*_grund = …` ist kein Fehler, aber eine Behauptung, die nicht mehr stimmt.
///
/// *Dieselbe Frage stellt `N034` im Pruefer, und dort ist sie eine Absage.*
/// **Does this body hold a `return` at all?** -- the syntactic half of `D2`.
///
/// Deliberately the same question GCC's `-Wreturn-type` asks in its first, front-end form:
/// *no return statement in function returning non-void*. It is not a reachability analysis
/// and does not pretend to be one -- `return` under an `if` that never runs still counts
/// here, and still counts for GCC. **A body with none is the one case where both tools agree
/// with no analysis at all**, and that agreement is what makes the refusal safe to hold at
/// the emitter rather than at a pass.
fn rumpf_antwortet(b: &Block) -> bool {
    b.anweisungen.iter().any(|s| {
        matches!(&s.art, StmtArt::Return(_))
            || crate::unterbloecke(s).into_iter().any(rumpf_antwortet)
    })
}

fn rumpf_scheitert(b: &Block) -> bool {
    b.anweisungen.iter().any(|s| {
        if let StmtArt::Return(Some(e)) = &s.art {
            if matches!(e.art, ExprArt::Grund { .. }) {
                return true;
            }
        }
        crate::unterbloecke(s).into_iter().any(rumpf_scheitert)
    })
}

/// **Does any exit of this body carry a VALUE?** -- the mirror of [`rumpf_scheitert`], and
/// the two are independent questions over the same body (a body may do both, or neither).
///
/// It answers exactly one thing for the emitter: whether `*_wert` is ever written, so that a
/// body all of whose exits are reasons gets its `(void)_wert;` and the generated C does not
/// fall at `-Werror=unused-parameter`. A `return;` without an expression writes nothing, and
/// a `return R::F;` writes the reason channel -- neither counts.
fn rumpf_gibt_wert(b: &Block) -> bool {
    b.anweisungen.iter().any(|s| {
        if let StmtArt::Return(Some(e)) = &s.art {
            if !matches!(e.art, ExprArt::Grund { .. }) {
                return true;
            }
        }
        crate::unterbloecke(s).into_iter().any(rumpf_gibt_wert)
    })
}

fn geist_wert(e: &Expr, u: &Namen) -> bool {
    match &e.art {
        ExprArt::Ruf(r) => r
            .path()
            .and_then(|p| p.teile.last())
            .and_then(|i| u.funktionen.get(&i.text))
            .is_some_and(|s| s.geist_rueck),
        // **Und ein blanker NAME, dessen Typ ein Geist ist** (2026-08-20). Bis dahin las
        // diese Funktion nur Rufe -- `let p = mmu_an(p);` war gedeckt, `return p;` nicht.
        // *Eine Loeschung, die den Wert nur an seiner Herkunft erkennt, uebersieht ihn
        // ueberall dort, wo er schon gebunden ist.*
        // **A bare name, as a PARAMETER or as a `let` binding** (2026-08-30). The
        // parameter half landed 2026-08-20; the `let` half stayed open, and the comment
        // three lines down said the erasure was built at three sites of four.
        //
        // *The fourth site was `return`*, and no example ever reached it: `beispiele/22`
        // runs the whole boot chain as `extern fn`, so the chain has prototypes and no
        // bodies. A body that returns a `let`-bound ghost emitted `return p1;` into a
        // `void` function, `p1` already deleted -- two errors at `cc`, measured before
        // this line was written.
        ExprArt::Ort(o) if o.suffixe.is_empty() => {
            u.parametertyp
                .get(&o.basis.text)
                .is_some_and(|t| ist_geist(t, u))
                || u.geistlokal.contains(&o.basis.text)
        }
        // **Hier ist der Sammelzweig die richtige Antwort, und zwar aus einem Satz, der
        // ausserhalb dieser Datei steht: ein Geist ist LINEAR.**
        //
        // `linear ghost type` heisst, der Wert wird genau einmal weitergereicht; er hat
        // keine Felder, keine Elemente und keine Arithmetik. Damit kann keine der uebrigen
        // Formen einen liefern: ein Literal ist keiner, ein `place` MIT Suffix waere ein
        // Feld eines Geistes (den es nicht gibt), `!`/`-` und jede binaere Rechnung
        // brauchen eine Zahl, und `sizeof`/`old`/`result` haben ueberhaupt keine Absenkung.
        // Eine Klammer ist die einzige, die weiterreichen KOENNTE -- und dass sie es nicht
        // tut, ist der eine offene Punkt hier: `let p = (mmu_an(p));` wird nicht geloescht.
        //
        // > *Das steht hier, weil es vor dem Ausschreiben nirgends stand.* Der
        // > Sammelzweig gab auf zwoelf Fragen eine Antwort und begruendete keine.
        ExprArt::Zahl(_)
        | ExprArt::Gleitkomma { .. }
        | ExprArt::Wahr
        | ExprArt::Falsch
        | ExprArt::Ort(_)
        | ExprArt::Klammer(_)
        | ExprArt::Eingebaut(_)
        | ExprArt::Alt(_)
        | ExprArt::Ergebnis
        | ExprArt::Unaer(_, _)
        // **Neither is a ghost value**, and both say so rather than falling through:
        // a function pointer names a body that exists at run time, and a reason case is a
        // constant of the error channel. *`geist_wert` decides whether the emitter may drop
        // the expression entirely -- a wrong `true` here would delete real code.*
        | ExprArt::FnWert(_)
        | ExprArt::Grund { .. }
        // **«SG-24»: a count is a run-time number**, not a witness -- its predicate
        // runs over real slots. Dropping it would delete the traversal.
        // **Lane E1:** a library call is a run-time call the same way -- its
        // value is not a ghost, and dropping it would delete real code.
        // **Lane 111:** a table literal is folded numbers, not a witness --
        // its elements name no ghost a const scope could even see.
        | ExprArt::Zaehle { .. }
        | ExprArt::LibraryCall(_)
        | ExprArt::ArrayLit(_)
        | ExprArt::Binaer(_, _, _) => false,
    }
}

/// **Lane E5: a library call with its payload (the statement and the
/// binding arm share this helper).**
///
/// An accepted call -- one the translation stage took into
/// `nutzlast_einsaetze` -- lowers to an ordinary call naming the function
/// by its last segment (the same rule `ruf` keeps) with the payload passed
/// as `&{payload}`, the `static const` table beside the tables. Ghost
/// arguments drop by position exactly as in `ruf`; an unknown callee keeps
/// every argument there, while here there is no call at all -- `None`,
/// and the arms refuse by name instead of guessing a lowering.
fn bibliothek_ruf(
    r: &LibraryCall,
    u: &Namen,
    absagen: &mut Absagen,
) -> Option<String> {
    let (_, _, nutzlast) = u.nutzlast_einsaetze.get(&(r.span.von, r.span.bis))?;
    let geist = u
        .funktionen
        .get(&r.function.text)
        .map(|s| s.geist_param.clone());
    let mut args: Vec<String> = r
        .args
        .iter()
        .enumerate()
        .filter(|(i, _)| !geist.as_ref().is_some_and(|g| *g.get(*i).unwrap_or(&false)))
        .map(|(_, a)| ausdruck(a, u, absagen))
        .collect();
    args.push(format!("&{nutzlast}"));
    Some(format!("{}({})", r.function.text, args.join(", ")))
}

/// **Which `tagged` type owns this bare variant name (lane 167), if exactly one does.**
///
/// The emitter's maps are bare-keyed and unit-wide, while the checker's resolution
/// is module-aware: where the checker accepts, exactly one declaration owns the
/// name visibly -- but the unit may hold a second, invisible one. Guessing between
/// them would lower a different case list than the checker typed, so several owners
/// refuse (`C001`) instead. `None` is not a refusal: the name is no case here, and
/// the ordinary call lowering answers it (which is where `H021` shapes land -- the
/// checker has already spoken over them, and this arm never runs on an accepted tree
/// for one).
enum VariantenDeutung<'a> {
    Keine,
    Eine(&'a str, &'a Variante),
    Mehrere,
}

fn varianten_traeger<'a>(name: &str, u: &'a Namen) -> VariantenDeutung<'a> {
    let mut treffer = Vec::new();
    for (summe, varianten) in &u.markierte {
        if varianten.iter().any(|v| v.name.text == name) {
            treffer.push((summe.as_str(), varianten));
        }
    }
    match treffer.len() {
        0 => VariantenDeutung::Keine,
        1 => {
            let (summe, varianten) = treffer.pop().unwrap();
            match varianten.iter().find(|v| v.name.text == name) {
                Some(v) => VariantenDeutung::Eine(summe, v),
                None => VariantenDeutung::Keine,
            }
        }
        _ => VariantenDeutung::Mehrere,
    }
}

/// **Whether a bare name already means something in this view (lane 167).**
///
/// The checker's value-namespace rule (`m1.rs`, bare-case arm), read against the
/// emitter's maps: function-scoped bindings (`schatten`); the declared values
/// (`statiken`, folded constants, atomics, accumulators, tables, arenas);
/// declared functions; integer words and their sugar (which never name a case --
/// `return u13;` stays `M119`'s on both sides). Devices, formats and reasons are
/// NOT excluded: the checker knows none of them as a value either, so a bare
/// name over one draws `M119` there and the case here, on a refused tree in both
/// cases. Anything bound wins, and the case is unreachable behind it -- one
/// predicate, read by `ort` and by `wert_ctyp`, so a bare case never lowers in
/// one and stays a name in the other.
fn fall_belegt(name: &str, u: &Namen) -> bool {
    u.schatten.contains(name)
        || u.funktionen.contains_key(name)
        || u.statiken.contains_key(name)
        || u.konstwert.contains_key(name)
        || u.konstanten.contains(name)
        || u.atomics.contains_key(name)
        || u.akkus.contains(name)
        || u.arenen.contains_key(name)
        || u.tabellen.iter().any(|t| t == name)
        || gabbro_syntax::kw::Kw::suche(name).is_some_and(|k| k.ist_intty())
        || gabbro_syntax::zucker_speicher(name).is_some()
}

/// **A `tagged` case as a file-scope initializer (lane 167).**
///
/// `{ .marke = Nachricht_Kurz, .last.Kurz = 5 }` -- the brace spelling of what `ruf`
/// writes as a compound literal in bodies. Only constant payloads lower: a number
/// through `czahl_oder_absage` (the same suffix rule as the number path), a bare
/// `const` name through its folded value. Anything else answers `None`, and the
/// caller keeps its `C001` -- a static initializer is a constant expression, and a
/// runtime value there is not one the emitter invents.
fn varianten_statisch(wert: &Expr, summe: &str, u: &Namen, absagen: &mut Absagen) -> Option<String> {
    match &wert.art {
        ExprArt::Klammer(x) => varianten_statisch(x, summe, u, absagen),
        ExprArt::Ruf(r) => {
            let pf = r.path()?;
            if pf.teile.len() != 1 || r.ist_verbundwert() {
                return None;
            }
            let name = pf.teile[0].text.clone();
            if u.funktionen.contains_key(&name)
                || u.uebergaenge.contains_key(&name)
                || u.geraete.contains_key(&name)
            {
                return None;
            }
            let VariantenDeutung::Eine(eigen, v) = varianten_traeger(&name, u) else {
                return None;
            };
            if eigen != summe {
                return None;
            }
            match (&v.nutzlast, r.argumente.len()) {
                (None, 0) => Some(format!("{{ .marke = {summe}_{name} }}")),
                (Some(_), 1) => {
                    let c = statische_nutzlast(&r.argumente[0], u, absagen)?;
                    Some(format!("{{ .marke = {summe}_{name}, .last.{name} = {c} }}"))
                }
                _ => None,
            }
        }
        ExprArt::Ort(o) => {
            if !o.suffixe.is_empty() {
                return None;
            }
            let name = o.basis.text.clone();
            // The checker's value-namespace rule through the one predicate both
            // expression arms read (`fall_belegt`): at file scope `schatten` is
            // empty, so this is the unit's value maps alone.
            if fall_belegt(&name, u) {
                return None;
            }
            let VariantenDeutung::Eine(eigen, v) = varianten_traeger(&name, u) else {
                return None;
            };
            if eigen != summe || v.nutzlast.is_some() {
                return None;
            }
            Some(format!("{{ .marke = {summe}_{name} }}"))
        }
        _ => None,
    }
}

/// **A translation-time constant payload for a file-scope case initializer.**
fn statische_nutzlast(a: &Expr, u: &Namen, absagen: &mut Absagen) -> Option<String> {
    match &a.art {
        ExprArt::Zahl(n) => Some(czahl_oder_absage(*n, a.span, absagen)),
        ExprArt::Klammer(x) => statische_nutzlast(x, u, absagen),
        ExprArt::Ort(o) if o.suffixe.is_empty() => {
            let w = u.konstwert.get(&o.basis.text).copied()?;
            Some(match u128::try_from(w) {
                Ok(n) => czahl_oder_absage(n, a.span, absagen),
                Err(_) => w.to_string(),
            })
        }
        _ => None,
    }
}

/// **A call, with the ghost arguments dropped.** The positions come from the callee's
/// signature; an unknown callee keeps every argument, which cannot compile silently — it
/// fails at `cc`, and that is the direction to fail in.
fn ruf(r: &Ruf, u: &Namen, absagen: &mut Absagen) -> String {
    // **The indirect call lowers to itself** («B8», 2026-08-21). `t->senden(b)` is
    // `t->senden(b)` in C -- the one construct in this emitter whose C form is its Gabbro
    // form.
    //
    // *No ghost argument is dropped here, and that is not an omission:* a ghost parameter is
    // erased by position, the positions come from the callee's signature, and an indirect
    // call has no callee to ask. **A `fn(…)` type carrying a ghost parameter would be a
    // silent mismatch between the checker and the C** -- and it cannot arise, because the
    // GRAMMAR excludes it: `params` reads `ident ":" typeexpr` and knows no `ghost`
    // (`parse.rs::params`). *The guarantee is the parser's, not a rule's; if `params` ever
    // learns `ghost`, this line becomes a hole and nothing here would say so.*
    if let Some(o) = r.place() {
        let args: Vec<String> = r
            .argumente
            .iter()
            .map(|a| ausdruck(a, u, absagen))
            .collect();
        return format!("{}({})", ort(o, u, absagen), args.join(", "));
    }
    let name = r
        .path()
        .and_then(|p| p.teile.last())
        .map(|i| i.text.clone())
        .unwrap_or_default();
    // **«B35»: `Some`/`None` are CONSTRUCTORS, not calls.** The old path emitted `None()` —
    // an implicit declaration that `-Werror` happens to catch. *Happening to fail is not
    // refusing.* Their lowering waits on the same decision as `option index into T`.
    if name == "Some" || name == "None" {
        weigere(absagen, r.span, "`option` constructor -- `option` has no representation yet");
        return String::new();
    }
    // **G9, 2026-09-04 -- `u64(a)` lowers to the C cast it already reads as.** `m1.rs`'s
    // `umwandlung_ruf` is the checker half of this repair and refuses anything but exactly
    // one integer argument before this ever runs; `ganzzahlwort` is the SAME table
    // `intty`/`breite_von` use for a declared type, so a conversion's target and a
    // declaration's type can never disagree on the C spelling.
    //
    // PLAN-BITS §1: a sugared conversion lowers through its storage word.
    // `u13(a)` is `(uint16_t)(a)` -- no `_BitInt`, the next standard width.
    let name = crate::aufrufgraph::zucker_umschreiben(&name).unwrap_or(name);
    if let Some((ctyp, _)) = gabbro_syntax::kw::Kw::suche(&name)
        .filter(|k| k.ist_intty())
        .and_then(ganzzahlwort)
    {
        let Some(arg) = r.argumente.first() else {
            weigere(absagen, r.span, "an integer conversion takes exactly one argument");
            return String::new();
        };
        return format!("({ctyp})({})", ausdruck(arg, u, absagen));
    }
    // **Bit intrinsics (PLAN-BITS §3): the lowering.**
    //
    // Only the BARE name lowers: a qualified path (`m::clz`) is an ordinary
    // call, the same line `m1.rs` draws. `m1.rs::intrinsik_ruf` owns arity and
    // ranges; the emitter reads the overlap and refuses a shape it cannot lower
    // rather than indexing past the end. Every argument is rendered ONCE --
    // the rotation pattern needs its amount twice, which is why `rotl`/`rotr`
    // lower to a helper call (`DREH_C`, emitted on demand above) instead of an
    // inline shift-or.
    //
    // `__builtin_clz/ctz` count in the width of `unsigned int`; on a narrower
    // operand the count is adjusted down (`- 24` for 8 bits, `- 16` for 16).
    // The cases are unreachable for zero -- the checker excludes it (`M157`) --
    // so the builtins' undefined zero case never fires.
    if crate::ist_bitintrinsik(&name)
        && r.path().is_some_and(|p| p.teile.len() == 1)
    {
        return intrinsik_c(&name, r, u, absagen);
    }
    // **Lane 167: `Variant(payload)` lowers to the compound literal the `match`
    // reads.** `(Nachricht){ .marke = Nachricht_Kurz, .last.Kurz = (x) }` -- the
    // same designators `match_markiert` reads back (`.marke`, `.last.{case}`), so
    // construction and matching agree field for field. A nullary case takes no
    // payload arm: there is no union member for it, and an empty initializer
    // list is not writable -- the mark alone says which case it is.
    //
    // The order is the checker's (`Umgebung::ist_variantenkonstruktor` without the
    // module half, which this unit-wide map cannot ask): conversions and
    // intrinsics above cannot be cases (no keyword spelling declares one, and the
    // sugar spelling converts); a declared function, transition, device handle or
    // format head wins over a case of the same name, exactly as in `m1.rs`. What the checker
    // refused (`N281`/`N282`/`N284`, several owners) refuses here too, by name --
    // the emitter runs on the parsed tree and never consults the passes, so the
    // backstop is load-bearing for the `-- erwartet: … allein` counterfactual.
    if let Some(pf) = r.path() {
        if pf.teile.len() == 1 && !r.ist_verbundwert() {
            let name = pf.teile[0].text.clone();
            if !u.funktionen.contains_key(&name)
                && !u.uebergaenge.contains_key(&name)
                && !u.geraete.contains_key(&name)
                && !u.formate.contains(&name)
            {
                match varianten_traeger(&name, u) {
                    VariantenDeutung::Eine(summe, v) => {
                        let marke = format!("{summe}_{name}");
                        match (&v.nutzlast, r.argumente.len()) {
                            (None, 0) => {
                                return format!("({summe}){{ .marke = {marke} }}");
                            }
                            (Some(_), 1) => {
                                return format!(
                                    "({summe}){{ .marke = {marke}, .last.{name} = {} }}",
                                    ausdruck(&r.argumente[0], u, absagen)
                                );
                            }
                            _ => {
                                weigere(
                                    absagen,
                                    r.span,
                                    "`tagged` case construction with the wrong number of \
                                     arguments -- a case carries exactly its declared payload",
                                );
                                return String::new();
                            }
                        }
                    }
                    VariantenDeutung::Mehrere => {
                        weigere(
                            absagen,
                            r.span,
                            "`tagged` case construction naming a case of several `tagged` \
                             types -- the case index is read off one case list",
                        );
                        return String::new();
                    }
                    VariantenDeutung::Keine => {}
                }
            }
        }
    }
    // **«B7»: der Verbundkonstruktor wird ein ZUSAMMENGESETZTES LITERAL mit benannten
    // Bestimmern** -- `(P){ .a = 1, .b = true }`, C99 §6.5.2.5.
    //
    // *Die Marken werden nicht weggeworfen, sie werden uebersetzt.* Damit steht die bewiesene
    // Zusage im Erzeugnis selbst und nicht nur im Pruefer: `deckt fs zs ⟷ map fst zs = fs`
    // heisst in C, dass jeder Bestimmer sein Feld nennt -- und ein Feldname, den `P` nicht
    // hat, ist dort ein Uebersetzungsfehler, kein falsch belegtes Wort.
    //
    // > Ein positionelles `(P){1, true}` haette dieselben Bits erzeugt und die eine Eigenschaft
    // > verloren, um derentwillen die Marken ueberhaupt Pflicht sind.
    //
    // **Und `cc` prueft die Vollstaendigkeit ein zweites Mal:** `-Wmissing-field-initializers`
    // meldet ein ausgelassenes Feld. Zwei unabhaengige Leser derselben Zusage.
    if r.ist_verbundwert() {
        let felder: Vec<String> = r
            .marken
            .iter()
            .zip(r.argumente.iter())
            .map(|(m, a)| feldsetzer(&name, m, a, u, absagen))
            .collect();
        if !u.verbunde.contains(&name) {
            weigere(absagen, r.span, "labelled call to something this unit does not declare as a record");
            return String::new();
        }
        return format!("({name}){{ {} }}", felder.join(", "));
    }
    // **«C5»: `Vtd(basis)` ist der GRIFF eines Geraets, kein Ruf** -- `beispiele/09` sagt
    // den Satz selbst: *„die Parameterliste der Deklaration IST der Konstruktor."* Aus einer
    // physischen Adresse wird ein Griff, und mehr steht in `device Vtd(basis : Pa)` nicht.
    //
    // *Die Umwandlung nach `volatile uint8_t *` ist die eine Stelle, an der der Erzeuger
    // eine Adresse zu einem Zeiger macht* -- sie steht hier, weil die Deklaration sie sagt
    // (`at mmio`), und nicht, weil sie bequem waere.
    if u.geraete.contains_key(&name) {
        // **The handle takes EVERY declared parameter, not just the base** (2026-08-25).
        // Until then this refused anything but one argument -- and `Virtq(base, n)` has two.
        // *`beispiele/09` says the sentence: „the declaration's parameter list IS the
        // constructor"; the emitter had read only its first entry.*
        let weitere = u.geraete.get(&name).map(|g| g.parameter.clone()).unwrap_or_default();
        if r.argumente.len() != 1 + weitere.len() {
            weigere(
                absagen,
                r.span,
                "a device handle takes exactly its declared parameters -- the base and every \
                 further one the declaration names",
            );
            return String::new();
        }
        let rest: String = weitere
            .iter()
            .zip(r.argumente.iter().skip(1))
            .map(|((n, _), a)| format!(", .{n} = {}", ausdruck(a, u, absagen)))
            .collect();
        // **In the port space the base is a NUMBER and this line makes no pointer.** The
        // sentence above -- *"the one place where the emitter turns an address into a
        // pointer, and it stands here because the declaration says so (`at mmio`)"* -- is a
        // statement about `at mmio` and it reads the space to say it. `at port` says
        // something else, and the width the number must fit is refused at the declaration
        // (`geraet`), so the cast here narrows nothing the emitter has not already judged.
        if matches!(u.geraete.get(&name).map(|g| &g.raum), Some(Raum::Port)) {
            return format!(
                "({name}){{ .basis = (uint16_t)({}){rest} }}",
                ausdruck(&r.argumente[0], u, absagen)
            );
        }
        return format!(
            "({name}){{ .basis = (volatile uint8_t *)(uintptr_t){}{rest} }}",
            ausdruck(&r.argumente[0], u, absagen)
        );
    }
    // **Ein `transition` heisst im Erzeugnis anders, als er in der Quelle steht.**
    //
    // `wurzel_setzen(v)` ist in Gabbro ein Ruf auf einen Uebergang des Geraets, das `v`
    // traegt; im C ist es `Vtd_wurzel_setzen(&v)`. *Der Bezug steht in der Deklaration und
    // nicht im Ruf* -- der Erzeuger stellt ihn her, statt den Namen abzuschreiben und `cc`
    // eine implizite Deklaration finden zu lassen.
    if let Some(dev) = u.uebergaenge.get(&name) {
        if r.argumente.len() == 1 {
            if let ExprArt::Ort(o) = &r.argumente[0].art {
                if o.suffixe.is_empty() {
                    if u.geraetewerte.get(&o.basis.text) == Some(dev) {
                        return format!("{dev}_{name}(&{})", o.basis.text);
                    }
                    if u.geraetezeiger.get(&o.basis.text) == Some(dev) {
                        return format!("{dev}_{name}({})", o.basis.text);
                    }
                }
            }
        }
        weigere(
            absagen,
            r.span,
            "`transition` call whose argument is not a handle of THAT device -- the transition \
             belongs to a declaration, and which one is not a guess",
        );
        return String::new();
    }
    // **A generated operation is called by its TWO segments** (2026-08-28,
    // `messung/OPS-RUFFORM.md`). `Verzeichnis::insert(v, i)` is `Verzeichnis_insert(v, i)`
    // -- the same lowering the `transition` gets above, and for the same reason: the C name
    // is built from a relation the DECLARATION carries. Without this branch the tail below
    // would emit `insert(v, i)`, an implicit declaration that `-Werror` happens to catch.
    // *Happening to fail is not refusing.*
    if let Some(pf) = r.path() {
        if u.opsnamen.contains(&pf.text()) {
            let args: Vec<String> = r
                .argumente
                .iter()
                .map(|a| ausdruck(a, u, absagen))
                .collect();
            return format!("{}({})", pf.text().replace("::", "_"), args.join(", "));
        }
    }
    // **`old(...)` outside a contract is not the pre-state reader (lane-140).**
    //
    // `old` is a word only where a contract is read (`parse.rs::im_vertrag`); in a body
    // it is a name, and `old(x)` is a call. With no declaration behind it the call has
    // no callee -- and the tail below emitted `old(x)` straight into the C, an implicit
    // declaration `cc` happens to catch, with exit 0 and no refusal. Measured:
    // `let x : u64 = old(eintrag);` and `if old(q.slots[k].aktiv) == true` both checked
    // clean (E009 aside) and both emitted the call verbatim. *Happening to fail is not
    // refusing* -- the `Some`/`None` arm above exists for the same reason.
    //
    // The guard asks `u.funktionen`, the same bare-keyed map the tail lowers through: a
    // declared `fn old` keeps its call. Transitions, devices and ops are claimed by
    // their own arms above, so nothing declared can reach this line by accident. A bare
    // `old` that is never called -- `let old = a;` (`beispiele/70`) -- never reaches
    // `ruf` at all.
    if name == "old" && !u.funktionen.contains_key(&name) {
        weigere(
            absagen,
            r.span,
            "`old(...)` outside a contract -- `old(place)` names the value at entry and \
             only a contract (`ensures`, an invariant, an exchange `when`) reads one. \
             Here it is a call to a function nobody declared, and the emitted C would \
             name a callee that does not exist",
        );
        return String::new();
    }
    // **`result(...)` outside a contract is not the answer reader (lane-140).**
    //
    // Same shape as `old` above, one arm over: `result` is a word only where a contract
    // is read, and in a body `result(a)` is a call. Measured: `return result(a);`
    // checked clean (E009 aside) and emitted verbatim. A bare `result` that is never
    // called -- `let result = old; return result;` (`beispiele/70`) -- never reaches
    // `ruf`, and a declared `fn result` keeps its call through the same guard.
    if name == "result" && !u.funktionen.contains_key(&name) {
        weigere(
            absagen,
            r.span,
            "`result(...)` outside a contract -- `result` names the return value inside \
             an `ensures`, and a contract is checked at compile time (W6). Here it is \
             a call to a function nobody declared, and the emitted C would name a \
             callee that does not exist",
        );
        return String::new();
    }
    let geist = u.funktionen.get(&name).map(|s| s.geist_param.clone());
    let args: Vec<String> = r
        .argumente
        .iter()
        .enumerate()
        .filter(|(i, _)| !geist.as_ref().is_some_and(|g| *g.get(*i).unwrap_or(&false)))
        .map(|(_, a)| ausdruck(a, u, absagen))
        .collect();
    format!("{name}({})", args.join(", "))
}

/// **Bit intrinsics (PLAN-BITS §3): one call, one C expression.**
///
/// `w` is the operand's own width (`intrinsik_breite`), so the builtin's width
/// and the checker's `breite` are read from the same place. Widths outside the
/// four standard ones, and a `bswap` outside 16/32/64, are refused by name --
/// the checker owns those shapes (`M158`/`M159`/`M160`), and this arm is where
/// an unchecked tree would otherwise invent a lowering.
fn intrinsik_c(name: &str, r: &Ruf, u: &Namen, absagen: &mut Absagen) -> String {
    let Some(a) = r.argumente.first() else {
        weigere(
            absagen,
            r.span,
            &format!("`{name}` without an argument -- there is no value to count"),
        );
        return String::new();
    };
    let Some(w) = intrinsik_breite(a, u) else {
        weigere(
            absagen,
            r.span,
            &format!(
                "`{name}` over an operand whose C width cannot be read -- the \
                 builtin is width-specific (`__builtin_clz` counts 32 bits), and \
                 guessing the width would count the wrong word"
            ),
        );
        return String::new();
    };
    if !matches!(w, 8 | 16 | 32 | 64) {
        weigere(
            absagen,
            r.span,
            &format!("`{name}` over a {w}-bit operand -- no standard width to count in"),
        );
        return String::new();
    }
    let x = ausdruck(a, u, absagen);
    match name {
        "clz" => match w {
            64 => format!("__builtin_clzll((unsigned long long)({x}))"),
            32 => format!("__builtin_clz((unsigned)({x}))"),
            16 => format!("(__builtin_clz((unsigned)({x})) - 16)"),
            _ => format!("(__builtin_clz((unsigned)({x})) - 24)"),
        },
        "ctz" => match w {
            64 => format!("__builtin_ctzll((unsigned long long)({x}))"),
            _ => format!("__builtin_ctz((unsigned)({x}))"),
        },
        "log2_floor" => match w {
            64 => format!("(63 - __builtin_clzll((unsigned long long)({x})))"),
            32 => format!("(31 - __builtin_clz((unsigned)({x})))"),
            16 => format!("(15 - (__builtin_clz((unsigned)({x})) - 16))"),
            _ => format!("(7 - (__builtin_clz((unsigned)({x})) - 24))"),
        },
        "popcount" => match w {
            64 => format!("__builtin_popcountll((unsigned long long)({x}))"),
            _ => format!("__builtin_popcount((unsigned)({x}))"),
        },
        "rotl" | "rotr" => {
            let Some(s) = r.argumente.get(1) else {
                weigere(
                    absagen,
                    r.span,
                    &format!("`{name}` without an amount -- rotation needs both sides"),
                );
                return String::new();
            };
            let s = ausdruck(s, u, absagen);
            format!("gabbro_{name}{w}({x}, {s})")
        }
        "bswap" => match w {
            16 => format!("__builtin_bswap16((uint16_t)({x}))"),
            32 => format!("__builtin_bswap32((uint32_t)({x}))"),
            64 => format!("__builtin_bswap64((uint64_t)({x}))"),
            _ => {
                weigere(
                    absagen,
                    r.span,
                    "`bswap` needs `u16`, `u32` or `u64` -- a one-byte value has \
                     no byte order to reverse",
                );
                String::new()
            }
        },
        _ => {
            weigere(
                absagen,
                r.span,
                &format!("`{name}` -- no lowering for this intrinsic"),
            );
            String::new()
        }
    }
}

/// **The C width an intrinsic counts in: the operand's lowered type, never its range.**
///
/// A narrowed `u32 in 1 .. 5` still lowers to `uint32_t`, and the builtin must
/// count 32 bits -- reading the range here would count 3. The arms mirror what
/// the checker reads in `m1.rs`, in the order the emitter can answer: a
/// literal carries the checker's own smallest-width rule
/// (`IntBereich::konstante`), a conversion carries its target width, a named
/// limit (`u32::max`) carries `grenzwort`, and everything else goes through
/// `wert_ctyp`, which already knows parameters, locals, fields and calls.
/// `None` refuses at the caller -- guessing the width counts the wrong word.
fn intrinsik_breite(e: &Expr, u: &Namen) -> Option<u8> {
    let e = crate::ohne_klammern(e);
    match &e.art {
        ExprArt::Zahl(n) => {
            let v = *n;
            if v > u64::MAX as u128 {
                return None;
            }
            Some(if v <= 0xFF {
                8
            } else if v <= 0xFFFF {
                16
            } else if v <= 0xFFFF_FFFF {
                32
            } else {
                64
            })
        }
        ExprArt::Ruf(r) => {
            if let Some(einfach) = r.path().and_then(|p| p.einfach()) {
                if let Some(k) = gabbro_syntax::kw::Kw::suche(&einfach.text).filter(|k| k.ist_intty()) {
                    return crate::umgebung::breite_von(k).map(|(b, _)| b);
                }
                if let Some(speicher) = crate::aufrufgraph::zucker_umschreiben(&einfach.text) {
                    return gabbro_syntax::kw::Kw::suche(&speicher)
                        .filter(|k| k.ist_intty())
                        .and_then(crate::umgebung::breite_von)
                        .map(|(b, _)| b);
                }
            }
            ctyp_breite(&wert_ctyp(e, u)?)
        }
        ExprArt::Ort(o) => {
            if let Some((b, _, _)) = crate::umgebung::grenzwort(o) {
                return Some(b);
            }
            // A sugared limit (`u13::max`) carries the storage word's width --
            // the same shape `m1.rs` types it in.
            if let [OrtSuffix::Feld(f)] = &o.suffixe[..] {
                if f.text == "max" || f.text == "min" {
                    if let Some(speicher) = gabbro_syntax::zucker_speicher(&o.basis.text) {
                        return crate::umgebung::breite_von(speicher).map(|(b, _)| b);
                    }
                }
            }
            ctyp_breite(&wert_ctyp(e, u)?)
        }
        _ => ctyp_breite(&wert_ctyp(e, u)?),
    }
}

/// A lowered C integer type back to its width. Only the four unsigned words --
/// a signed width here means the checker already refused the program, and the
/// refusal below (not a guess) is what such a tree gets.
fn ctyp_breite(c: &str) -> Option<u8> {
    Some(match c {
        "uint8_t" => 8,
        "uint16_t" => 16,
        "uint32_t" => 32,
        "uint64_t" => 64,
        _ => return None,
    })
}

fn ort(o: &Ort, u: &Namen, absagen: &mut Absagen) -> String {
    // **«B26»: a name that means something else for the span of this condition.**
    // See `Namen::ersetzungen` -- it is empty everywhere except inside the condition of a
    // fallible register read, and it is the line that keeps the volatile read at ONE.
    if o.suffixe.is_empty() {
        if let Some(x) = u.ersetzungen.get(&o.basis.text) {
            return x.clone();
        }
    }
    // **`u32::max` in an EXPRESSION -- and it lowered to `u32->max`.**
    //
    // Measured 2026-09-01: `return w ^ u32::max;` checks clean and emits `w ^ u32->max`, a
    // field access through a pointer to a variable no declaration ever made. `cc` says
    // `u32 undeclared`. *The one refusal this generator must never delegate is the one it
    // does not even know it is making* -- and this was not a refusal at all, it was a place
    // lowering that happened to fit.
    //
    // > The `const` path was right the whole time and writes `#define G 4294967295u`. It is
    // > right because it asks `umgebung.rs`. **The defect was one caller that did not.**
    //
    // The suffix follows the same rule as the `#define`: `u` for a non-negative value, none
    // for `i32::min` -- an `-2147483648u` would not merely be ugly, it would be another
    // number.
    //
    // PLAN-BITS §1: a sugared limit lowers its exact bound. `u13::max` is
    // `8191u` -- the edge of the promised range, not of the storage word.
    if let Some((lo, hi)) = gabbro_syntax::zucker_bereich(&o.basis.text) {
        if o.suffixe.len() == 1 {
            if let Some(OrtSuffix::Feld(f)) = o.suffixe.first() {
                let w = match f.text.as_str() {
                    "max" => Some(hi),
                    "min" => Some(lo),
                    _ => None,
                };
                if let Some(w) = w {
                    return if w < 0 { format!("({w})") } else { format!("{w}u") };
                }
            }
        }
    }
    if let Some((_, _, w)) = crate::umgebung::grenzwort(o) {
        return if w < 0 { format!("({w})") } else { format!("{w}u") };
    }
    // **Ein blankes `None` an einer Stelle, die keine Option ist, wird ABGELEHNT.**
    //
    // Bis zum 2026-08-19 fiel es hier durch und wurde der C-Bezeichner `None` -- ein Name,
    // den niemand erklaert hat. *Er waere an `cc` gefallen, und darauf zu bauen hiesse, die
    // Weigerung zu delegieren, wo die Antwort hier steht.* Wo die Zieltabelle bekannt ist,
    // kommt dieser Ort gar nicht erst dran (`option_wert`).
    if o.suffixe.is_empty() && o.basis.text == "None" {
        weigere(
            absagen,
            o.span,
            "`None` where the emitter cannot see WHICH table's sentinel is meant -- the \
             sentinel is `count` itself (beweise/Option_Sonderwert.thy), so it needs the table",
        );
        return String::new();
    }
    // **Lane 167: a bare nullary case lowers to the compound literal with the mark
    // alone.** `Leer` is `(Nachricht){ .marke = Nachricht_Leer }` -- the same value
    // `Leer()` builds one arm up in `ruf`. The shadowing question is asked against
    // the per-function set (`schatten`: parameters, `let`s, `match` binders and
    // the rest) and the unit's value maps, mirroring the checker's value-namespace
    // rule: anything already bound wins, and the case is unreachable behind it. A
    // bare name over a case WITH payload is the checker's `N283`; here it is the
    // backstop `C001`, for the same counterfactual reason as in `ruf` above.
    if o.suffixe.is_empty() {
        let name = o.basis.text.clone();
        if !fall_belegt(&name, u) {
            match varianten_traeger(&name, u) {
                VariantenDeutung::Eine(summe, v) if v.nutzlast.is_none() => {
                    return format!("({summe}){{ .marke = {summe}_{name} }}");
                }
                VariantenDeutung::Eine(_, _) => {
                    weigere(
                        absagen,
                        o.span,
                        "`tagged` case with a payload standing as a bare name -- a bare \
                         name carries no payload",
                    );
                    return String::new();
                }
                VariantenDeutung::Mehrere => {
                    weigere(
                        absagen,
                        o.span,
                        "`tagged` case naming a case of several `tagged` types -- the case \
                         index is read off one case list",
                    );
                    return String::new();
                }
                VariantenDeutung::Keine => {}
            }
        }
    }
    // **Ein Geraeteregister ist kein Feld, sondern ein volatiler Zugriff an `basis + Versatz`.**
    // Der C-Uebersetzer darf ihn nicht wegoptimieren, und `volatile` ist die eine Stelle, an
    // der die Absenkung ihm etwas VERBIETEN muss.
    let griff = u
        .geraetezeiger
        .get(&o.basis.text)
        .map(|g| (g, "->"))
        .or_else(|| u.geraetewerte.get(&o.basis.text).map(|g| (g, ".")));
    if let (Some((g, pfeil)), Some(OrtSuffix::Feld(f))) = (griff, o.suffixe.first()) {
        // **A declared parameter is an ordinary struct field, NOT a volatile access.**
        // It travels in the handle and was fixed when the handle was built; reading it twice
        // gives the same answer, and `volatile` would say the opposite. *`q.n` is what the
        // driver KNOWS about the ring, not what the device reports.*
        // **One lookup for all three questions below.** `u.geraete` is keyed by plain name
        // here (this is the emitter's own map, not `Umgebung`'s), and asking it three times
        // in one block is three chances to ask it differently.
        let dev = u.geraete.get(g);
        if o.suffixe.len() == 1
            && dev.is_some_and(|d| {
                !d.reg.contains_key(&f.text) && d.parameter.iter().any(|(n, _)| *n == f.text)
            })
        {
            return format!("{}{pfeil}{}", o.basis.text, f.text);
        }
        // **A BANK is read through its accessor, not as a struct field** (2026-08-26).
        // `q.USED_RING[s].id` -> `Virtq_USED_RING_id(q, s)`. The address arithmetic lives in
        // the accessor because a bank base may only be known at run time.
        if o.suffixe.len() == 3 {
            if let (Some(OrtSuffix::Index(i)), Some(OrtSuffix::Feld(r))) =
                (o.suffixe.get(1), o.suffixe.get(2))
            {
                if dev
                    .and_then(|d| d.baenke.get(&f.text))
                    .is_some_and(|s| s.contains(&r.text))
                {
                    let adr = if pfeil == "->" { o.basis.text.clone() } else { format!("&{}", o.basis.text) };
                    return format!(
                        "{g}_{}_{}({adr}, {})",
                        f.text,
                        r.text,
                        ausdruck(i, u, absagen)
                    );
                }
            }
        }
        // **`D19`, found 2026-09-03: a bit field on a BANK register, one suffix past the
        // branch above.** `d.F[i].X.A` -- bank, index, register, field -- fell through this
        // whole function exactly like `d.F[i].X` did before 2026-08-26: `felder` above is
        // filled from `Device::register` only, `Bank::register`'s own bit ranges were never
        // collected (`Geraet::bankfelder` did not exist), and the generic struct-field walk
        // at the bottom of `ort` wrote `d->F[i].X.A` into a `D` that has none of the three
        // names. **`pruefe` said `0 errors`, `emit` said `0` refusals, and `cc` said `'D'
        // has no member named 'F'`.** *The exact fault line `baenke`'s own comment already
        // named, one suffix further down, and the fix is the same shape: a lookup, and a
        // named refusal where the lookup comes back empty rather than a silent fallthrough.*
        if o.suffixe.len() == 4 {
            if let (Some(OrtSuffix::Index(i)), Some(OrtSuffix::Feld(r)), Some(OrtSuffix::Feld(feld))) =
                (o.suffixe.get(1), o.suffixe.get(2), o.suffixe.get(3))
            {
                if dev
                    .and_then(|d| d.baenke.get(&f.text))
                    .is_some_and(|s| s.contains(&r.text))
                {
                    let Some((hi, lo, breite_bit)) = dev
                        .and_then(|d| d.bankfelder.get(&f.text))
                        .and_then(|m| m.get(&r.text))
                        .and_then(|m2| m2.get(&feld.text))
                    else {
                        weigere(
                            absagen,
                            feld.span,
                            "no lowering: a field on a bank register whose bit range this \
                             unit cannot resolve -- either the register's own width could \
                             not be lowered, or no field of this name is declared on it",
                        );
                        return String::new();
                    };
                    // Same overflow-safe `u128` arithmetic as the top-level field mask
                    // below (`D15`) -- a bank register's bit positions are read from the
                    // same AST shape (`RegDecl::felder`) and deserve the same fence.
                    let spanne = u128::from(*hi).saturating_sub(u128::from(*lo)).saturating_add(1);
                    let breite = u128::from(*breite_bit).clamp(1, 128);
                    let maske: u128 = if spanne >= breite {
                        u128::MAX >> (128 - breite)
                    } else {
                        (1u128 << spanne) - 1
                    };
                    let adr = if pfeil == "->" { o.basis.text.clone() } else { format!("&{}", o.basis.text) };
                    let wort = format!(
                        "{g}_{}_{}({adr}, {})",
                        f.text,
                        r.text,
                        ausdruck(i, u, absagen)
                    );
                    return format!("(({wort} >> {lo}) & {maske}u)");
                }
            }
        }
        if let (Some(dv), Some((versatz, breite))) = (dev, dev.and_then(|d| d.reg.get(&f.text))) {
            // **A `port` register reads through its `in` accessor, an `mmio` one through a
            // volatile place** -- and the ONE line that decides it is `geraetelesung`, which
            // `uebergang` reads too. The bit-field mask below is the same arithmetic either
            // way: a field is shifted out of a word, and how the word arrived is a question
            // that has already been answered by the time this line runs.
            let wort = geraetelesung(dv, &o.basis.text, pfeil, *versatz, breite, g, &f.text);
            if o.suffixe.len() == 1 {
                return wort;
            }
            // **Ein Bitfeld LESEN ist mechanisch. Es zu SCHREIBEN ist Falle 4.**
            //
            // Ein Schreiben auf ein einzelnes Bit ist ein Lese-Aendere-Schreib-Zug auf dem
            // GANZEN Register -- und bei `class w` ist das unmoeglich, weil sich das Register
            // nicht lesen laesst. Genau dafuer gibt es `mirrors` (die x86-Fassung von Falle 4,
            // `FRAGMENTE.md` F2), und `mirrors` ist nicht abgesenkt.
            //
            // *Der Erzeuger gibt darum nur den LESENDEN Ausdruck aus.* Ein Schreiben darauf
            // waere in C ein Zuweisungsziel, das es nicht gibt -- und `cc` sagt es sofort.
            if let Some(OrtSuffix::Feld(feld)) = o.suffixe.get(1) {
                if o.suffixe.len() == 2 {
                    if let Some((hi, lo, breite_bit)) =
                        dev.and_then(|d| d.felder.get(&f.text)).and_then(|m| m.get(&feld.text))
                    {
                        // **`D15`: the mask was computed in `u32`, and `u32::MAX - 0 + 1` is
                        // not a number** (2026-09-03).
                        //
                        // `hi`, `lo` and the width are all `u32` (`Geraet::felder`), so the
                        // span `hi - lo + 1` was a `u32` add that overflows at the top of
                        // the range -- and a `+ 1` that overflows is a PANIC in the debug
                        // build and a wrap in the shipped one. Measured over
                        // `reg X : u64 @0x0 fields { A @[4294967295:0] }`:
                        //
                        //     thread 'main' panicked at emit.rs:9403: attempt to add with
                        //     overflow
                        //
                        // The bit position `4294967295` is itself a truncation -- `*b as
                        // u32` up in `Namen`, the `konst_zahl` cast one construct over -- and
                        // the range refusal a few hundred lines up refuses it BY NAME. **The
                        // panic still happened**, because `command_emit` runs the whole back
                        // end before it reads the verdict, and this expression is reached
                        // from a function body while the refusal sits at the declaration.
                        //
                        // > *Found by `fuzze-erzeuger.py` net 8*, on 13 rungs of a form this
                        // > sweep owns -- `reg-bit-hi-leser`, added the same day because
                        // > the shared template declares a register nothing reads and lowers
                        // > to a struct with one field.
                        //
                        // The arithmetic is `u128` now and the width is clamped into the one
                        // range a shift is defined over. *Neither is a decision about bit
                        // positions; both are about a machine word.* The refusal that owns
                        // the decision is unchanged.
                        let spanne = u128::from(*hi)
                            .saturating_sub(u128::from(*lo))
                            .saturating_add(1);
                        let breite = u128::from(*breite_bit).clamp(1, 128);
                        let maske: u128 = if spanne >= breite {
                            u128::MAX >> (128 - breite)
                        } else {
                            (1u128 << spanne) - 1
                        };
                        return format!("(({wort} >> {lo}) & {maske}u)");
                    }
                }
            }
            weigere(absagen, f.span, "device register access form");
            return String::new();
        }
    }
    // **Ein `format`-Feld ist ein RUF, kein Feldzugriff** (2026-08-20).
    //
    // Das ist die ganze Aussage des Konstrukts, und das Zeugnis sagt sie seit jeher:
    // *„KEIN C-Verbund, sondern Byteleser -- ein Format ist eine Zusage ueber BYTES."*
    // `format_` erzeugt `Elf64Kopf_e_eintritt(v)`; der Ortsabsenker schrieb daneben
    // `v->e_eintritt` und traf damit ein Element, das der erzeugte Verbund gar nicht hat.
    //
    // > *Es fiel nicht auf, solange jede Datei mit einem `format` aus einem anderen Grund
    // > `C001` sagte.* Genau die Bauart, die dieser Ordner schon zweimal bezahlt hat: ein
    // > Fehler, den eine Weigerung davor verdeckt.
    // **And `m->a` is the SAME access as `m.a`, so it takes the same arm** (2026-09-15).
    //
    // It did not, and the consequence was the very defect the paragraph above describes --
    // one spelling later. `m : ptr<normal, r> F` with `return m->a;` passed `gabbro pruefe`
    // with zero errors and emitted `return m->a;` into a
    // `typedef struct { uint8_t *bytes; uint32_t len; } F;`. *`cc` says `'F' has no member
    // named 'a'`, `gabbro emit` returned 0, and `C001` said nothing* -- a silently wrong
    // lowering, which this file holds to be worse than a refusal because a refusal stands in
    // the certificate. The German paragraph directly above says the same thing about the DOT
    // spelling and closed only that one; this is the same finding, found again, one spelling
    // later.
    //
    // The two spellings cannot differ here: `formatwerte` is filled from a `TypExpr::Pfad`
    // AND from a `TypExpr::Zeiger` at a format (`eigene_sicht`), the generated reader takes
    // the handle by pointer either way (`F_a(const F *v)`), and the pointer-ness is already
    // in the C type. **A field of a `format` is reached by its reader, and by nothing else.**
    if let Some(fmt) = u.formatwerte.get(&o.basis.text) {
        let erste = match o.suffixe.first() {
            Some(OrtSuffix::Feld(f)) | Some(OrtSuffix::Ueber(f)) => Some(f),
            _ => None,
        };
        if let Some(f) = erste {
            if o.suffixe.len() == 1 {
                return format!("{fmt}_{}({})", f.text, o.basis.text);
            }
            weigere(
                absagen,
                f.span,
                "a `format` field followed by more suffixes -- a reader returns a VALUE, and a value \
                 has no place inside the bytes",
            );
            return String::new();
        }
    }
    // **A place over a TABLE reaches its slots and nothing else -- and until today the
    // generator wrote the nothing else out** (2026-09-15).
    //
    // A `table T count 4 { slot { wert : u32, } }` lowers to
    // `typedef struct { T_slot slots[4]; } T;` -- ONE member, named `slots`. `q->wert` on a
    // `q : ptr<normal, r> T` passed `gabbro pruefe` with zero errors and came out as
    // `return q->wert;`: a member the struct does not have. Same shape as the `format` case
    // directly above and found the same way -- by compiling what the emitter claims is
    // finished.
    //
    // **Coarse in the safe direction (`W9`):** the refusal asks only whether the FIRST
    // suffix is `slots`, which is the only member there is. A table-level `const` is not a
    // member at all (it lowers to a `#define`, `table.const`), and a name that is neither is
    // the defect itself. *The exact answer -- is this a declared slot field? -- belongs to
    // the checker, and that it does not give one is named in the report, not papered over
    // here.*
    if u.tabellenzeiger.contains_key(&o.basis.text) || u.tabellenglobal.contains(&o.basis.text) {
        let erste = match o.suffixe.first() {
            Some(OrtSuffix::Feld(f)) | Some(OrtSuffix::Ueber(f)) => Some(f),
            _ => None,
        };
        if let Some(f) = erste {
            if f.text != "slots" {
                weigere(
                    absagen,
                    f.span,
                    &format!(
                        "`{}` over a `table` -- a table handle has exactly ONE member in C, \
                         `slots`, and a slot field is reached through it (`{}.slots[i].{}`). \
                         What stood here would have named a member of the generated struct \
                         that does not exist",
                        f.text, o.basis.text, f.text
                    ),
                );
                return String::new();
            }
        }
    }
    // **Ein `accumulates` wird beim LESEN gefaltet.** Der Name steht fuer den ganzen
    // Zellenblock, nicht fuer eine Zelle -- ein blanker Zugriff waere ein Zugriff auf etwas,
    // das es im C nicht gibt.
    if o.suffixe.is_empty() && u.akkus.contains(&o.basis.text) {
        return format!("{}_lies()", o.basis.text);
    }
    // **A bare read of an `atomic` is an explicit load in its declared order**
    // (lane 152). Until now it fell to the generic walk below and came out as
    // the plain name -- over `_Atomic uint32_t AT` a plain access, which C
    // treats as `seq_cst` while the declaration said `relaxed`, and which the
    // C model (`C-SPEICHERMODELL.md` §1c) makes stuck: every atomic access
    // goes through an explicit `atomic_*_explicit` call, none is a plain
    // access to an `_Atomic` object.
    //
    // The order is the LOAD side of the declaration (`u.atomics` carries both;
    // a `release` declaration loads `acquire`, and C11 has no releasing load).
    // The STORE side is not lowered here: every store to an atomic is a
    // `publishstmt` (`SPRACHE.md` §11.3), where the payload promise stands,
    // and the checker refuses the bare store (`N270`) -- so no store reaches
    // this reader through this place. What does reach it: expression reads,
    // `retry … until` conditions (`pred_c` lowers through `ausdruck`), narrow
    // bounds, indices -- every one of them a load, and every one now explicit.
    //
    // A name bound HERE shadows the atomic, and then the plain name is right:
    // a parameter or `let` of the same name is a C local that covers the
    // global, a record value in `werte` is no atomic at all, and a traverse
    // binder in `laufvariablen` is a loop counter. All four views are
    // function-scoped (`eigene_sicht`, `laufsicht`), so a shadowing in one
    // function changes nothing in another.
    //
    // **And an INDEXED read of an atomic ARRAY is the same load on one element**
    // (`REGEL[r]` over `atomic REGEL : [u32; 256]`). It has to be: the goal theorem's
    // race component exempts an `atomic` carrier from `RennfreiBis` ENTIRELY, and that
    // exemption is only honest if every access to it is an atomic operation. A plain
    // `REGEL[r]` beside the CAS loop would be a non-atomic access to an `_Atomic`
    // object -- undefined in C11 and stuck in the C model, and this time with nothing
    // left to catch it. *The checker (`N271`) refuses the indexed read on a SCALAR
    // atomic, which is what it always did; it lets the array through to here.*
    if u.atom_arrays.contains_key(&o.basis.text)
        || (o.suffixe.is_empty() && u.atomics.contains_key(&o.basis.text))
    {
        if let Some((_, _, laden)) = u.atomics.get(&o.basis.text) {
            if !u.parametertyp.contains_key(&o.basis.text)
                && !u.lokaltyp.contains_key(&o.basis.text)
                && !u.werte.contains(&o.basis.text)
                && !u.laufvariablen.contains(&o.basis.text)
            {
                if o.suffixe.is_empty() {
                    return format!("atomic_load_explicit(&{}, {laden})", o.basis.text);
                }
                if let [OrtSuffix::Index(i)] = &o.suffixe[..] {
                    return format!(
                        "atomic_load_explicit(&{}[{}], {laden})",
                        o.basis.text,
                        ausdruck(i, u, absagen)
                    );
                }
            }
        }
    }
    // **Direct byte reads take the `leseBytes` arm, not the generic walk
    // (lane-141).** `None` falls through and the walk below runs exactly as
    // before -- every plain path is the old path, never a re-spelling.
    if let Some(c) = lese_bytes(o, u, absagen) {
        return c;
    }
    let mut t = o.basis.text.clone();
    // The base of a place in a function is a pointer parameter -- **unless it is a record
    // value bound here** («B7»). `c->len` on a `let c : Completion` is simply wrong.
    let mut zeiger = !u.werte.contains(&o.basis.text);
    // **Und ausser wenn die Basis eine TABELLE ist.** Ihr Name ist der Ort, nicht ein
    // Zeiger auf ihn -- `Kappenraum.slots[s]` greift den Speicher selbst.
    if u.tabellenglobal.contains(&o.basis.text) {
        t = format!("{}_speicher", o.basis.text);
        zeiger = false;
    }
    // **«E4»: and except when the base is an ARENA.** `A[i]` reads
    // through the buffer -- `A_arena_speicher.buf[i]`. The storage name is
    // the arena's own (see `arena()`), and the counter beside it is written
    // by `alloc` and `reset`, never read through this path. Like the table
    // above, the membership asked is the USED set, not the declared one.
    if u.arenen_global.contains(&o.basis.text) {
        t = format!("{}_arena_speicher.buf", o.basis.text);
        zeiger = false;
    }
    // **And a `static` of a RECORD is a value too** (2026-08-26). `static irq : IrqMarke`
    // lowers to `static IrqMarke irq = { … };` -- an object, not a pointer to one -- and the
    // access lowered to `irq->tiefe_max`. *`cc` says `invalid type argument of '->'`, and
    // relying on that would be delegating a refusal whose answer stands right here.*
    //
    // Found by compiling `messung/fragmente/F06.gab` for the first time. **The `static` of a
    // record was built on 2026-08-25 and nothing ever read one back** -- an emitted form
    // whose only reader is its own writer is not measured by its own corpus, the same shape
    // as the bank accessors.
    if matches!(u.statiken.get(&o.basis.text),
                Some(TypExpr::Pfad(p)) if p.teile.last().is_some_and(|i| u.verbunde.contains(&i.text)))
    {
        zeiger = false;
    }
    for suf in &o.suffixe {
        match suf {
            OrtSuffix::Feld(f) => {
                t = if zeiger {
                    zeiger = false;
                    format!("{t}->{}", f.text)
                } else {
                    format!("{t}.{}", f.text)
                };
            }
            OrtSuffix::Ueber(f) => t = format!("{t}->{}", f.text),
            OrtSuffix::Index(e) => {
                zeiger = false;
                t = format!("{t}[{}]", ausdruck(e, u, absagen));
            }
        }
    }
    t
}

/// **Every expression form this emitter does not know is REFUSED.**
///
/// Until 2026-08-17 the fallback here read `"/* NOT LOWERED */ 0"` — *it compiled, and it
/// computed zero.* A fail-open path in the one component whose whole design is "refuse rather
/// than guess", and a comment nobody reads is not a refusal.
/// **«F»: das Literal geht als KUERZESTE RUECKLESBARE Form hinaus.**
///
/// `{:?}` einer `f64` ist genau das: die kuerzeste Dezimalzahl, die auf dasselbe Bitmuster
/// zurueckliest. *Eine gekuerzte Form waere ein zweites Runden -- und zwar eines, von dem im
/// Quelltext nichts steht.*
///
/// **And `schmal` appends an `f` where the computation is an `f32` computation** (2026-08-31).
///
/// Without a suffix a C literal is a `double`. Standing next to a `float`, C lifts the
/// `float` up to it -- **the whole computation changes width** and only falls back at the
/// end. Measured over 200 000 values of the emitted unit: the old output differed from
/// `v * 0.1f` in **39 990** cases (the plain-C run of `messung/GRAMMATIKTAFEL.md` §8 said
/// 39 974 over its own sampling). *The program says `f32`, the output computed `f64` --
/// exactly the class the `wrapping` cast one level up stands against.*
///
/// **The `f` does not change the VALUE of the literal.** `{:?}` yields the shortest decimal
/// that reads back to the same `f64`; `float` has a 24 bit significand and `double` 53, so
/// `53 >= 2*24 + 2` -- under that condition double rounding is provably innocuous
/// (Figueroa 1995), and `0.1f` is bit-identical to `(float)0.1`. *The suffix picks the
/// computation width, not a different value.*
fn gleitkommatext(bits: u64, schmal: bool) -> String {
    let w = f64::from_bits(bits);
    let t = format!("{w:?}");
    let t = if t.contains('.') || t.contains('e') || t.contains("inf") || t.contains("NaN") {
        t
    } else {
        format!("{t}.0")
    };
    if schmal { format!("{t}f") } else { t }
}

/// **Does this expression compute in `float`?** -- the question the suffix hangs on.
///
/// It is answered at the LEAVES and not at the node: a literal has no type to read off, so
/// the neighbour carries it. `wert_ctyp` reads it out of the declaration -- a parameter, a
/// field, the return of a call.
fn ist_float(e: &Expr, u: &Namen) -> bool {
    wert_ctyp(e, u).as_deref() == Some("float")
}

fn ausdruck(e: &Expr, u: &Namen, absagen: &mut Absagen) -> String {
    ausdruck_breit(e, u, absagen, false)
}

/// Every counter of one function, defined («SG-24»).
///
/// The definitions stand between the declarations and the bodies (the caller in
/// `emittiere_mit` splices them there): after the table storage they read, before
/// the bodies that call them. Source order is free, so per-item emission would
/// put a counter before its table -- *the same reason all prototypes precede all
/// bodies*, one construct over.
fn zaehler_funktion(f: &FnDecl, eigen: &Namen, aus: &mut String, absagen: &mut Absagen) {
    let FnRumpf::Block(b) = &f.rumpf else {
        return;
    };
    let mut binder = Vec::new();
    let mut stellen = Vec::new();
    zaehlstellen_block(b, &mut binder, eigen, &mut stellen);
    for z in &stellen {
        zaehler_definition(z, eigen, aus, absagen);
    }
}

/// A predicate as a boolean EXPRESSION -- the condition of the synthetic `if`
/// in a generated counter («SG-24»).
///
/// The same five forms `pred_c` refuses have no expression form either: a
/// quantifier, `reaches`, a lock witness, membership and implication are proof
/// devices, not values. Refused with the same sentence shape -- what RUNS is
/// what C can evaluate, and the checker already proved the rest needs no
/// evaluation. (The grammar's SUGAR `p => q` for `!p || q` is not rewritten
/// here, for the same reason `pred_c` does not rewrite it: the emitter does
/// not rewrite what the author wrote.)
fn pred_als_expr(p: &Pred, span: gabbro_syntax::span::Span) -> Option<Expr> {
    let art = match &p.art {
        PredArt::Vergleich(e) => return Some(e.clone()),
        PredArt::Klammer(x) => ExprArt::Klammer(Box::new(pred_als_expr(x, span)?)),
        PredArt::Nicht(x) => ExprArt::Unaer(UnOp::Nicht, Box::new(pred_als_expr(x, span)?)),
        PredArt::Und(a, b) => ExprArt::Binaer(
            BinOp::Und,
            Box::new(pred_als_expr(a, span)?),
            Box::new(pred_als_expr(b, span)?),
        ),
        PredArt::Oder(a, b) => ExprArt::Binaer(
            BinOp::Oder,
            Box::new(pred_als_expr(a, span)?),
            Box::new(pred_als_expr(b, span)?),
        ),
        PredArt::Quantor(_)
        | PredArt::Element(_, _)
        | PredArt::Erreicht { .. }
        | PredArt::Held { .. }
        | PredArt::Folgt(_, _) => return None,
    };
    Some(Expr { art, span })
}

/// One counter: `static uint64_t zaehle_N(captures…)`, accumulator plus the
/// table's own traversal with a conditional increment.
///
/// The loop is not reinvented: a synthetic `Traverse` over the site's domain
/// with the body `if (<rumpf>) <acc> += 1;` goes through `traverse()` -- the
/// same arms, the same refusal texts, the same C shapes as the loop the writer
/// would have written. What is synthetic is only the plumbing around it: the
/// accumulator, the wrapper statement (a span carrier -- `traverse()` reads
/// nothing off it but the span), and the `void` exit context (the body cannot
/// leave, return or break).
fn zaehler_definition(z: &Zaehlstelle, u: &Namen, aus: &mut String, absagen: &mut Absagen) {
    // The condition runs: what C cannot evaluate is refused here, by name, with
    // the same five forms `pred_c` refuses. A counter over one is not a slower
    // program but a proof device mistaken for a value.
    let Some(bedingung) = pred_als_expr(&z.rumpf, z.span) else {
        weigere(
            absagen,
            z.span,
            "`count` over a predicate that is not a run-time condition -- a \
             quantifier, `reaches`, a lock witness, membership or an implication \
             is a proof device, and the counter would have to evaluate it",
        );
        return;
    };
    let params: Vec<String> = z.fangen.iter().map(|(_, d)| d.clone()).collect();
    let params = if params.is_empty() {
        "void".to_string()
    } else {
        params.join(", ")
    };
    let acc_ort = Ort {
        basis: Ident {
            text: z.acc.clone(),
            span: z.span,
        },
        suffixe: Vec::new(),
        span: z.span,
    };
    let eins = Expr {
        art: ExprArt::Zahl(1),
        span: z.span,
    };
    let body = Block {
        anweisungen: vec![Stmt {
            art: StmtArt::Wenn(WennStmt {
                zweige: vec![(
                    bedingung,
                    Block {
                        anweisungen: vec![Stmt {
                            art: StmtArt::Zuweisung(Zuweisung {
                                ziel: acc_ort,
                                op: ZuwOp::Plus,
                                wert: eins,
                            }),
                            span: z.span,
                        }],
                        span: z.span,
                    },
                )],
                sonst: None,
            }),
            span: z.span,
        }],
        span: z.span,
    };
    let trav = Traverse {
        variable: z.variable.clone(),
        gegenstand: None,
        domaene: z.domaene.clone(),
        abstieg: Abstieg::Unbesucht,
        mass: None,
        touches: None,
        invariante: None,
        rumpf: body,
        span: z.span,
    };
    // The wrapper statement carries the site's span into `traverse()`; its kind
    // is never read (no exit, no value -- see above).
    let huelle = Stmt {
        art: StmtArt::Next(Ident {
            text: String::new(),
            span: z.span,
        }),
        span: z.span,
    };
    let mut rumpf_c = String::new();
    traverse(
        &trav,
        &huelle,
        &mut rumpf_c,
        u,
        absagen,
        1,
        &Austritt::default(),
    );
    // The C width follows the domain's index word (see `wert_ctyp`): index-word
    // domains count into `uint32_t`, array domains into `uint64_t`. Same width
    // at the call as at the `let`, so no conversion -- explicit or implicit.
    let wort = match &z.domaene {
        Domaene::SlotsVon(_) | Domaene::NachfahrenVon(_) | Domaene::VorfahrenVon(_) => {
            "uint32_t"
        }
        _ => "uint64_t",
    };
    aus.push_str(&format!(
        "\n/* `count {} in {} : …` -- generated counter («SG-24»). The predicate is the writer's logic, the traversal the template's: it falls here once, not per site. */\n\
         static {wort} {}({}) {{\n\
         \x20   {wort} {} = 0;\n\
         {}    return {};\n\
         }}\n",
        z.variable.text,
        z.domaene.benennung(),
        z.name,
        params,
        z.acc,
        rumpf_c,
        z.acc,
    ));
}

/// **One `count` site («SG-24»): the counter name and what it closes over.**
///
/// The counter is a generated `static` C function, one per site, named after the
/// site's span (`zaehle_<von>` -- a byte offset is unique per file, and a unit is
/// one file). It closes over the names the counted predicate reads, minus the
/// binder: parameters and `let` locals travel as arguments, globals stay global.
/// A name that is neither -- a `match` binder, an `exchange` binder, an
/// `awaits` binding -- is refused by name: hoisting it into a `let` first is one
/// line, and a counter guessing at its type would be the other kind.
struct Zaehlstelle {
    name: String,
    acc: String,
    variable: Ident,
    domaene: Domaene,
    rumpf: Pred,
    span: gabbro_syntax::span::Span,
    fangen: Vec<(String, String)>,
}

/// The C type of a `traverse` binder, by domain -- the SAME words the loop
/// headers below write (`uint32_t` for an index word, `uint64_t` for an array
/// index). A second table of the same fact would drift; this one is read at the
/// collection walk and trusted at the loop both were copied from.
fn traversebinder_ctyp(d: &Domaene) -> Option<&'static str> {
    match d {
        Domaene::SlotsVon(_)
        | Domaene::NachfahrenVon(_)
        | Domaene::VorfahrenVon(_) => Some("uint32_t"),
        Domaene::ElementeVon(_) => Some("uint64_t"),
        _ => None,
    }
}

/// What one `count` site closes over: names the predicate reads, minus the
/// binder, each with its C declaration.
///
/// `Err` carries the refusal TEXT, not the refusal: the caller at the call site
/// is the one place that reports it, so one fault keeps one refusal even though
/// two passes compute this function (collection skips silently, the call
/// reports). A counter that guessed at a capture would emit a call C cannot
/// resolve, and the sentence belongs where the call stands.
fn zaehlstelle(
    e: &Expr,
    variable: &Ident,
    domaene: &Domaene,
    rumpf: &Pred,
    binder: &[(String, String)],
    u: &Namen,
) -> Result<Zaehlstelle, String> {
    let name = format!("zaehle_{}", e.span.von);
    let acc = format!("zaehle_acc_{}", e.span.von);
    let mut namen = BTreeSet::new();
    for x in crate::ausdruecke_im_praedikat(rumpf) {
        sammle_expr_namen(x, &mut namen);
    }
    let mut fangen = Vec::new();
    for n in namen.iter() {
        if n == &variable.text {
            continue;
        }
        // An enclosing `traverse` binder: a C loop variable in scope at the
        // site, passed down with the loop header's own C type.
        if let Some((_, t)) = binder.iter().find(|(b, _)| b == n) {
            fangen.push((n.clone(), format!("{t} {n}")));
            continue;
        }
        if let Some(t) = u.parametertyp.get(n) {
            if ist_geist(t, u) {
                return Err(format!(
                    "`count` over a ghost `{n}` -- a witness has no C value to \
                     pass, and the predicate runs"
                ));
            }
            let Some(c) = ctyp(t, u) else {
                return Err(format!(
                    "`count` closing over `{n}` -- its declared type has no C \
                     word here"
                ));
            };
            fangen.push((n.clone(), format!("{c} {n}")));
            continue;
        }
        if let Some(c) = u.lokaltyp.get(n) {
            if u.geistlokal.contains(n) {
                return Err(format!(
                    "`count` over a ghost `{n}` -- a witness has no C value to \
                     pass, and the predicate runs"
                ));
            }
            fangen.push((n.clone(), format!("{c} {n}")));
            continue;
        }
        // A global -- a table, a `static`, a constant, an atomic, an accumulator:
        // a C symbol in every scope, so no parameter. Anything else is a name this
        // unit cannot resolve, and the counter must not guess at it (the `let`
        // rule `C001` of 2026-08-25, one construct over).
        if !(u.tabellenglobal.contains(n)
            || u.statiken.contains_key(n)
            || u.konstanten.contains(n)
            || u.atomics.contains_key(n)
            || u.akkus.contains(n))
        {
            return Err(format!(
                "`count` closing over `{n}` -- no parameter, no `let`, no \
                 enclosing `traverse` binder and no global of this unit carries \
                 it. A `match` arm, an `exchange` or an `awaits` binding needs one \
                 line first: bind it into a `let`, and the counter takes it as an \
                 ordinary argument"
            ));
        }
    }
    fangen.sort();
    fangen.dedup();
    Ok(Zaehlstelle {
        name,
        acc,
        variable: variable.clone(),
        domaene: domaene.clone(),
        rumpf: rumpf.clone(),
        span: e.span,
        fangen,
    })
}

/// The call a `count` lowers to -- the counter name with its captures, in the
/// same order the definition takes them. Computed from the site, never stored:
/// the definition and the call cannot drift, because there is one function of
/// the site and two readers of it. This reader is the one place that REPORTS a
/// capture refusal (the collector skips silently): one fault, one refusal.
fn zaehlruf(
    e: &Expr,
    variable: &Ident,
    domaene: &Domaene,
    rumpf: &Pred,
    binder: &[(String, String)],
    u: &Namen,
    absagen: &mut Absagen,
) -> String {
    let z = match zaehlstelle(e, variable, domaene, rumpf, binder, u) {
        Ok(z) => z,
        Err(grund) => {
            weigere(absagen, e.span, &grund);
            return String::new();
        }
    };
    let args: Vec<String> = z.fangen.iter().map(|(n, _)| n.clone()).collect();
    format!("{}({})", z.name, args.join(", "))
}

/// Every `count` of a function body: collected with the binder stack in scope,
/// so a use of an enclosing loop variable resolves to a capture, not to a
/// refusal. Contracts are NOT walked here: they lower nowhere in C (the ghost
/// channel refuses them as `counted`), and the executable predicates (`until`,
/// invariants, `when`) live in the bodies walked below.
fn zaehlstellen_block(
    b: &Block,
    binder: &mut Vec<(String, String)>,
    eigen: &Namen,
    aus: &mut Vec<Zaehlstelle>,
) {
    for s in &b.anweisungen {
        // A `traverse` binder is a C loop variable in its body -- capturable, with
        // the loop header's own C type (`traversebinder_ctyp`).
        let mut gedrueckt = 0usize;
        if let StmtArt::Schleife(sch) = &s.art {
            if let Schleife::Traverse(t) = sch.as_ref() {
                if let Some(ct) = traversebinder_ctyp(&t.domaene) {
                    binder.push((t.variable.text.clone(), ct.to_string()));
                    gedrueckt += 1;
                }
            }
        }
        // A `match` binder is in scope in its arm, in NEITHER walk: the
        // collection here and the `zaehlbinder` threading below both resolve
        // `traverse` binders only, so both report the same sentence for an arm
        // binder (hoist it into a `let` first). *Two walks, one rule.* (Arms
        // are reached through `unterbloecke` below -- a second walk here would
        // be a double descent.)
        for e in crate::eigene_ausdruecke(s) {
            zaehlstellen_expr(e, binder, eigen, aus);
        }
        for p in crate::eigene_praedikate(s) {
            zaehlstellen_pred(p, binder, eigen, aus);
        }
        // Loop invariants are predicates of the body that `eigene_praedikate`
        // does not return (it covers `retry … until` only): a `count` in one
        // runs per pass and needs its counter like any other.
        if let StmtArt::Schleife(sch) = &s.art {
            let invs: Vec<&Pred> = match sch.as_ref() {
                Schleife::Traverse(t) => t.invariante.iter().collect(),
                Schleife::Retry(r) => r.invariante.iter().collect(),
                Schleife::Forever(f) => f.invariante.iter().collect(),
            };
            for p in invs {
                zaehlstellen_pred(p, binder, eigen, aus);
            }
            if let Schleife::Traverse(t) = sch.as_ref() {
                if let Some(g) = &t.gegenstand {
                    zaehlstellen_expr(g, binder, eigen, aus);
                }
            }
        }
        for k in crate::unterbloecke(s) {
            // `Match` arms were walked above, each under its own binder.
            if !matches!(s.art, StmtArt::Match(_)) {
                zaehlstellen_block(k, binder, eigen, aus);
            }
        }
        for _ in 0..gedrueckt {
            binder.pop();
        }
    }
}

fn zaehlstellen_pred(
    p: &Pred,
    binder: &mut Vec<(String, String)>,
    eigen: &Namen,
    aus: &mut Vec<Zaehlstelle>,
) {
    for e in crate::ausdruecke_im_praedikat(p) {
        zaehlstellen_expr(e, binder, eigen, aus);
    }
}

fn zaehlstellen_expr(
    e: &Expr,
    binder: &[(String, String)],
    eigen: &Namen,
    aus: &mut Vec<Zaehlstelle>,
) {
    for x in crate::alle_ausdruecke(e) {
        if let ExprArt::Zaehle {
            variable,
            domaene,
            rumpf,
        } = &x.art
        {
            // The definition is emitted from the same pure function of the site
            // as the call (`zaehlstelle`), so a site the call lowers always has
            // its counter -- and a site whose captures refuse is skipped here and
            // reported once at the call. Nested counts resolve inside out: the
            // inner counter's captures are names of the outer scopes, which the
            // outer counter takes as its own parameters (its reader descends
            // through the nested node).
            // Double collection (overlapping walks meet at one node) is deduped
            // here: two definitions of one name would be a C redefinition, not
            // a second counter.
            if let Ok(z) = zaehlstelle(x, variable, domaene, rumpf, binder, eigen) {
                if !aus.iter().any(|a| a.name == z.name) {
                    aus.push(z);
                }
            }
        }
    }
}

/// `schmal` means: this expression stands inside an `f32` computation, and a literal in it
/// gets its `f`. **Only three forms pass it on** -- the parenthesis, the binary node and the
/// literal itself. Everything else starts at `false`: a call, a place, an index carry their
/// own type, and a literal inside one has a different neighbour.
fn ausdruck_breit(e: &Expr, u: &Namen, absagen: &mut Absagen, schmal: bool) -> String {
    match &e.art {
        // **The one door nine slots share** -- `return`, `if`, `let`, `static … =`, an
        // assignment. `czahl_oder_absage` writes the `u` C needs and refuses what C cannot
        // hold; see its own note for why the boundary sits where it does.
        ExprArt::Zahl(n) => czahl_oder_absage(*n, e.span, absagen),
        ExprArt::Gleitkomma { bits, .. } => gleitkommatext(*bits, schmal),
        ExprArt::Wahr => "true".into(),
        ExprArt::Falsch => "false".into(),
        ExprArt::Ort(o) => ort(o, u, absagen),
        // **`&f` lowers to `&f`** («B8», 2026-08-21).
        //
        // C admits the bare name too (a function designator decays), and that is exactly why
        // the `&` is written: *the two spellings mean the same thing to `cc` and different
        // things to a reader*, and Gabbro's producer says which one it is at the source. The
        // ampersand survives into the C for the same reason it exists in the Gabbro.
        //
        // Only the LAST segment is emitted: a Gabbro module path is not a C name, and the
        // rest of this generator resolves callees the same way (`fn ruf`).
        //
        // **`&T` lowers to `&T_speicher`** (2026-09-16) -- the address of the table
        // storage `tabelle()` writes where the source addresses the table BY NAME.
        // The checker reads function first and table second (`m1.rs`), and this arm
        // decides in the same order: a short name that is both keeps the `&f`
        // reading. Where the checker refused (`M127`), this arm still writes the
        // bare `&f` form -- the refusal stands one pass earlier, and `cc` would
        // only repeat it.
        ExprArt::FnWert(p) => {
            let kurz = p.teile.last().map(|i| i.text.clone()).unwrap_or_default();
            if !u.funktionen.contains_key(&kurz) && u.tabellen.iter().any(|t| *t == kurz) {
                format!("&{kurz}_speicher")
            } else {
                format!(
                    "&{}",
                    p.teile.last().map(|i| i.text.clone()).unwrap_or_default()
                )
            }
        }
        // **`R::F` wird `R_F`** (Stufe 7, 2026-08-21) -- genau der Name, den
        // `ItemArt::Reason` weiter oben in sein `typedef enum` schreibt. *Die zwei Stellen
        // muessen dieselbe Regel benutzen, sonst erzeugt der Uebersetzer einen Namen, den
        // er selbst nicht deklariert hat* -- `cc` faengt das, aber erst am Ende.
        ExprArt::Grund { grund, fall } => format!("{}_{}", grund.text, fall.text),
        ExprArt::Klammer(x) => format!("({})", ausdruck_breit(x, u, absagen, schmal)),
        ExprArt::Binaer(op, a, b) => {
            // **PLAN-BITS section 4 (lane 88): the overflow lowerings go first.**
            // They answer from the operand DECLARATIONS, not from any `wrapping`
            // attribute, and neither takes the pointer-arithmetic or mixed-float
            // refusals below -- the checker typed both sides as integers.
            if matches!(
                op,
                BinOp::PlusWrap
                    | BinOp::MinusWrap
                    | BinOp::MalWrap
                    | BinOp::SchiebLinksWrap
            ) {
                // The shift resolves left-only: the amount is bounded, never exact.
                let form = if *op == BinOp::SchiebLinksWrap {
                    wrap_shift_form(a, u)
                } else {
                    wrap_form(a, b, u)
                };
                let Some((bits, n)) = form else {
                    weigere(
                        absagen,
                        e.span,
                        &format!(
                            "wrapping `{}` over operands whose exact ranges cannot \
                             be read off their declarations -- both sides need an \
                             exact unsigned range `0 .. 2^N - 1` on one storage width",
                            op_text(op)
                        ),
                    );
                    return String::new();
                };
                return wrap_c(op, a, b, bits, n, u, absagen);
            }
            if *op == BinOp::PlusSat {
                let Some((bits, signed, lo, hi)) = saturation_facts(a, b, u) else {
                    weigere(
                        absagen,
                        e.span,
                        "saturating `+|` over operands whose clamp interval cannot \
                         be read off their declarations -- both sides need one \
                         shared integer range on one width",
                    );
                    return String::new();
                };
                return saturation_c(a, b, bits, signed, lo, hi, u, absagen);
            }
            // **CForm zeigerArithmetik, re-decided 2026-09-11: no computed
            // address.** Gabbro gives pointer arithmetic exactly one form
            // (`SPRACHE.md` 5.2: `place[expr]` with an M1-bounded index); a
            // `+`/`-` with a pointer operand is none of them, so the emitter
            // refuses by name instead of writing it into the C. Comparisons
            // stay untouched (ordering two addresses computes no address), and
            // so does every integer: the `*` is read off the scope-resolved
            // type (`ist_zeigerwort`), never off a name. The same-day
            // withdrawal fired on `u32` arithmetic in
            // `messung/netz/udp-echo.gab` because that type came from another
            // function's parameter through the then-unscoped map; the map is
            // scoped since (`eigene_sicht`), and the refusal is back on it.
            if matches!(op, BinOp::Plus | BinOp::Minus)
                && (ist_zeigerwort(&wert_ctyp(a, u)) || ist_zeigerwort(&wert_ctyp(b, u)))
            {
                weigere(
                    absagen,
                    e.span,
                    "pointer arithmetic -- the language carries no bound for a \
                     computed address outside `place[expr]`, and an unproven \
                     bound is not emitted",
                );
                return String::new();
            }
            // **CForm doubleTyp (lane 142): no silent widening.** With a `double`
            // operand present, C promotes the `float` side and computes in
            // `double`, while the checker proved the `f32` fact (7400 of 200000
            // sampled cases differ). There is no conversion form, so the mixed
            // node is refused by name instead of computed in the wrong width.
            if matches!(
                op,
                BinOp::Plus | BinOp::Minus | BinOp::Mal | BinOp::Geteilt
            ) && ist_gemischt_float_double(&wert_ctyp(a, u), &wert_ctyp(b, u))
            {
                weigere(
                    absagen,
                    e.span,
                    "mixed `float`/`double` arithmetic -- C would widen the `float` \
                     side and compute in `double`, against the checked `f32` fact, \
                     and there is no conversion form (the `F005` shape)",
                );
                return String::new();
            }
            // **Ein `wrapping`-Slot rechnet UNSIGNED -- sonst sagt das C etwas anderes als
            // das Gepruefte** (Rezension 2026-08-20).
            //
            // Gabbro sagt ueber `u16 wrapping`: *der Ueberlauf ist deklariert und definiert.*
            // C sagt etwas anderes: bei `a * a` hebt die ganzzahlige Aufwertung beide
            // Operanden auf `int`, und ein `int`-Ueberlauf ist **undefiniert**. Mit UBSan
            // nachgewiesen:
            //
            // ```
            // runtime error: signed integer overflow: 50000 * 50000
            //                cannot be represented in type 'int'
            // ```
            //
            // Der Wert kam zufaellig richtig heraus (63744). *Garantiert war er nicht* -- ein
            // Optimierer darf annehmen, dass es nicht ueberlaeuft, und daraus folgt hier
            // alles.
            //
            // > **Das ist die Aussage, auf der das Projekt ruht.** Wo Gabbro `definiert` sagt
            // > und das Erzeugnis `undefiniert` meint, ist die Uebersetzung nicht mehr das
            // > Gepruefte.
            //
            // Gerechnet wird darum in `uint32_t`/`uint64_t` -- dort ist der Umlauf modulo
            // 2^n **zugesichert** (C11 6.2.5p9) -- und das Ergebnis faellt auf die erklaerte
            // Breite zurueck.
            //
            // **Warum nur bei `wrapping`:** wo Gabbro den Ueberlauf NICHT erlaubt, hat `M101`
            // bewiesen, dass das Ergebnis in den erklaerten Bereich passt; ein `u16`-Wert
            // passt in `int`, und die Aufwertung ist dann harmlos. *Die Absenkung braucht den
            // Cast genau dort, wo die Sprache den Ueberlauf zulaesst.*
            if let (true, Some(i)) = (rechnet(op), umlaeufer_typ(a, u).or(umlaeufer_typ(b, u))) {
                // Which width the modulo arithmetic runs in is not a question with a
                // default: a word without a width gets no `uint64_t` here, it gets a
                // refusal by name.
                let Some((breite, vz)) = crate::umgebung::breite_von(i.wort) else {
                    weigere(absagen, i.span, "the width of a `wrapping` computation");
                    return String::new();
                };
                let rechenwort = if breite <= 32 { "uint32_t" } else { "uint64_t" };
                let zurueck = format!("{}int{}_t", if vz { "" } else { "u" }, breite);
                return format!(
                    "({zurueck})(({rechenwort})({}) {} ({rechenwort})({}))",
                    ausdruck(a, u, absagen),
                    op_text(op),
                    ausdruck(b, u, absagen)
                );
            }
            // **And here the WIDTH of a floating point computation is decided** (2026-08-31).
            //
            // If one side is a `float`, the whole node computes in `float` -- and a literal
            // in it gets its `f`. Without that C lifted the `float` to `double`, computed
            // there and rounded back at the end: **two roundings instead of one**, and in
            // 39 990 of 200 000 measured cases a different result from what the checker said
            // about `f32`.
            //
            // *The same shape as the `wrapping` cast above:* where C changes the width by
            // itself, the producer writes it down. The only difference is where the width
            // stands -- there in the slot declaration, here in the neighbouring operand.
            //
            // **The context is INHERITED (`schmal ||`), not asked afresh.** In
            // `x * (0.5 + 0.25)` the inner node knows no `float` neighbour; without passing
            // it down the parenthesis would stay a `double` and take the expression with it.
            let schmal = schmal || ist_float(a, u) || ist_float(b, u);
            format!(
                "{} {} {}",
                geklammert(op, a, ausdruck_breit(a, u, absagen, schmal)),
                op_text(op),
                geklammert(op, b, ausdruck_breit(b, u, absagen, schmal))
            )
        }
        ExprArt::Ruf(r) => ruf(r, u, absagen),
        // **Lane E5:** same lowering as at the statement form, through the
        // shared helper -- the payload static stands file-scope, so a call
        // in binding position needs no statement around it.
        ExprArt::LibraryCall(r) => match bibliothek_ruf(r, u, absagen) {
            Some(text) => text,
            None => {
                weigere(
                    absagen,
                    r.span,
                    "`library call` -- the region has no payload yet (lane E5: only \
                     exact-length integer regions translate)",
                );
                String::new()
            }
        },
        // **«SG-24»** -- a `count` is a call to its generated counter. The counter
        // was defined from the same site (`zaehler_funktion`, spliced between the
        // declarations and the bodies), so the call always resolves; the captures
        // ride the enclosing loop binders (`u.zaehlbinder`), parameters and
        // `let` locals, and a capture none of them carries refuses -- once, here.
        ExprArt::Zaehle {
            variable,
            domaene,
            rumpf,
        } => zaehlruf(e, variable, domaene, rumpf, &u.zaehlbinder, u, absagen),
        // **Die logische Verneinung -- gebaut, WEIL ein Programm sie gebraucht hat**
        // (2026-08-20, Stufe 4, `messung/netz/udp-echo.gab`).
        //
        // `if !kopf_gueltig(k, w) { … }` -- die gewoehnlichste Zeile eines Empfangswegs.
        // **`gabbro pruefe` gab 0 Fehler, `gabbro emit` sagte `expression form` ab**, und
        // die 45 Beispiele hatten die Stelle NIE ausgeloest: kein einziges benutzt ein `!`
        // oder ein unaeres Minus in einem abgesenkten Rumpf. *Der Korpus ist je Konstrukt
        // geschrieben, und ein `!` ist kein Konstrukt -- es ist das, was man beim Schreiben
        // eines Programms tut.*
        ExprArt::Unaer(UnOp::Nicht, x) => format!("!({})", ausdruck(x, u, absagen)),
        // **`~x` lowers to `({c})~({c})(x)`, and the TWO casts are the whole item.**
        //
        // A bare `~x` in C is not a complement of the width the Gabbro states: the integer
        // promotion lifts every operand narrower than `int` up to `int`, and `~(uint16_t)240`
        // is `0xFFFFFF0F` there and not `0xFF0F`. **`-Wall -Wextra` mostly says nothing about
        // it** -- the value is well defined, it is merely a different one from the checked
        // one.
        //
        // > The inner cast binds the operand to its width, the outer one cuts the promoted
        // > result back. *Only the outer one is the effective one*; the inner stands beside
        // > it because `mirrors` and the bit-field setter have written exactly this form
        // > since day one (`emit.rs::3062`, `::3514`), and **two spellings for one thing
        // > would be the second register** (W7).
        //
        // The width comes from `wert_ctyp`, that is, from the declaration. Where it is not
        // readable the emitter refuses instead of guessing -- a `uint64_t` default here
        // would be precisely `breite_von`'s `_ => 8`, one level down.
        ExprArt::Unaer(UnOp::BitNicht, x) => {
            let Some(c) = wert_ctyp(x, u) else {
                weigere(
                    absagen,
                    e.span,
                    "`~` over an operand whose WIDTH the emitter cannot read off a \
                     declaration -- the complement is a different number in every width, and \
                     a default width here would be a guess",
                );
                return String::new();
            };
            format!("({c})~({c})({})", ausdruck(x, u, absagen))
        }
        // **Und das unaere Minus wird NICHT mitgebaut, obwohl es danebensteht** -- Regel A:
        // kein Konstrukt ohne ein Programm, das es gebraucht hat. Es hat einen zweiten
        // Grund, und der ist schaerfer:
        //
        // > In C bleibt `-x` auf einem `uint32_t` UNSIGNED -- die ueblichen arithmetischen
        // > Umwandlungen befoerdern es nicht nach `int`, weil `int` den Wertebereich nicht
        // > fasst. **Das erzeugte Programm rechnete dann etwas anderes als M1 sagt**, und M1
        // > sagt `i32 in -4294967295 .. 0`.
        //
        // *Eine Absenkung, die das stillschweigend anders rechnet, ist genau die Klasse, die
        // dieser Ordner schon dreimal bezahlt hat.*
        ExprArt::Unaer(UnOp::Negativ, _) => {
            weigere(
                absagen,
                e.span,
                "unary minus -- in C `-x` on an unsigned operand stays UNSIGNED (the usual \
                 conversions do not promote it), so the emitted program would compute \
                 something other than the checker says. No corpus site needs it",
            );
            String::new()
        }
        // -- und die drei, die weiter abgelehnt werden, jetzt aber MIT GRUND -------------
        //
        // **Hinter *"no lowering: expression form"* standen genau drei Formen, nicht eine
        // offene Liste.** Die Absage nannte keine von ihnen, und ein Leser des Zeugnisses
        // konnte daraus nicht ablesen, WAS fehlt -- bei einer Sprache, deren ganzer Wert an
        // der Nachvollziehbarkeit ihrer Weigerungen haengt.
        // **THREE forms stood under one refusal, and its reason held for only two**
        // (2026-08-26). The text speaks about `sizeof(T)`: *"it would have to agree with the
        // layout the checker computed, and that agreement is not established anywhere."*
        // True -- **and it says nothing about `lenof` over a place whose type is a
        // fixed-length array.** There the length is not computed by anyone: it stands in the
        // declaration, `[u64; STACK_WORTE]`, and `M103` already bounds every index by it.
        //
        // > *The same shape this folder has now found five times:* a refusal whose SCOPE and
        // > whose GROUND come apart -- `static` of a record, `at dma` beside `at normal`,
        // > `E008` at a probe body. **The cure is the same each time: give each half its own
        // > sentence.**
        //
        // `lenof` was never unlowerable, only unreachable outside a `format`: it lowers today
        // as a DESCENT MEASURE (`by decreasing (lenof(s.worte) - i)`), over the same
        // declaration.
        ExprArt::Eingebaut(b) => match &**b {
            Eingebaut::Lenof(TypOderOrt::Ort(o)) => {
                match ort_typ(o, u).as_ref().and_then(|t| feldlaenge_von(t, u)) {
                    Some(n) => format!("{n}u"),
                    None => {
                        weigere(
                            absagen,
                            e.span,
                            "`lenof` over a place whose type is not a fixed-length array -- \
                             the length would have to come from somewhere other than the \
                             declaration, and there is no such place",
                        );
                        String::new()
                    }
                }
            }
            _ => {
                weigere(
                    absagen,
                    e.span,
                    "`sizeof` / `aligned` outside a `format` predicate -- inside one they \
                     lower against the buffer (`v->len`), and outside one there is no object \
                     to measure: `sizeof(T)` would have to agree with the layout the checker \
                     computed, and that agreement is not established anywhere",
                );
                String::new()
            }
        },
        ExprArt::Alt(_) => {
            weigere(
                absagen,
                e.span,
                "`old(place)` outside a compare-exchange -- it names the value BEFORE the \
                 call, and nothing in the emitted C keeps it. The one place it does lower is \
                 the `when old(X) == e` of an `exchange`, where the atomic itself holds the \
                 old value",
            );
            String::new()
        }
        ExprArt::Ergebnis => {
            weigere(
                absagen,
                e.span,
                "`result` -- it names the return value of the surrounding function inside an \
                 `ensures`, and a contract is checked at compile time (W6). There is no run \
                 time object for it",
            );
            String::new()
        }
        // **Lane 111:** a table literal stands only as a `const` initializer --
        // the parser never reads `[` anywhere else, so the general reader has
        // no object for it. The `const` gang above lowers it to `static const`
        // storage; here it is refused by name.
        ExprArt::ArrayLit(_) => {
            weigere(
                absagen,
                e.span,
                "array literal outside a const-table initializer -- the parser reads \
                 `[…]` only there, and only the `const` gang lowers it",
            );
            String::new()
        }
    }
}

fn zuw_op(op: &ZuwOp) -> &'static str {
    match op {
        ZuwOp::Setzt => "=",
        ZuwOp::Plus => "+=",
        ZuwOp::Minus => "-=",
        ZuwOp::Und => "&=",
        ZuwOp::Oder => "|=",
    }
}

/// **The five operators Gabbro holds in ONE level and C grades into FOUR.**
///
/// `parse.rs::bitexpr` is a single left-associative loop over `<< >> & ^ |`. C grades them
/// `<< >>` above `&` above `^` above `|`. Printing a Gabbro tree as flat C text therefore
/// lets C REGROUP it: `a & b << c` is `(a & b) << c` here and `a & (b << c)` there.
///
/// Measured over all 25 pairs on 2026-08-31, compiled and run: **nine compute a different
/// value**, and `-Wparentheses` -- the only net -- catches three of the nine while warning
/// on three that are correct. The table is in `messung/proben/VORRANG-BITSTUFEN.md`.
fn ist_bitop(op: &BinOp) -> bool {
    matches!(
        op,
        BinOp::BitUnd
            | BinOp::BitOder
            | BinOp::BitXor
            | BinOp::SchiebLinks
            | BinOp::SchiebRechts
            // PLAN-BITS section 4 (lane 88): the wrapping operators group with
            // the bit level for parenthesisation -- their lowering is a cast-
            // and-mask shape, and a bare neighbour must not merge into it.
            // `PlusSat` stays out: its shape is a call, which binds on its own.
            | BinOp::PlusWrap
            | BinOp::MinusWrap
            | BinOp::MalWrap
            | BinOp::SchiebLinksWrap
    )
}

/// One operand of a binary node, parenthesised where flat C text would not reproduce the
/// tree the checker proved things about.
///
/// **The rule is deliberately wider than the minimum.** The minimum would be "parenthesise
/// exactly where C regroups". That leaves `a & b ^ c` bare -- C and Gabbro agree on it --
/// and `cc -Wall -Wextra -Werror` still refuses the file. `pruefe-emission.sh` stage 9
/// requires every emitting file to pass exactly that command, so the narrow rule would ship
/// C that this project's own guard rejects. Measured: three of the 25 pairs fail `-Werror`
/// today while computing the right value.
///
/// Wrapping whenever EITHER side carries a bit operator reproduces the tree and silences
/// that whole warning class. It leaves purely arithmetic and logical nodes untouched, and
/// that is safe for a reason worth writing down: **strip the bit level out of Gabbro's
/// grammar and the remaining hierarchy is C's, operator for operator** -- `||` below `&&`
/// below the comparisons below `+ -` below `* / %`. Comparisons cannot chain, so no
/// associativity question is left open there either.
fn geklammert(eltern: &BinOp, kind: &Expr, text: String) -> String {
    let ExprArt::Binaer(kind_op, _, _) = &kind.art else {
        return text;
    };
    if ist_bitop(eltern) || ist_bitop(kind_op) {
        format!("({text})")
    } else {
        text
    }
}

fn op_text(op: &BinOp) -> &'static str {
    match op {
        BinOp::Plus => "+",
        BinOp::Minus => "-",
        BinOp::Mal => "*",
        BinOp::Geteilt => "/",
        BinOp::Rest => "%",
        // PLAN-BITS section 4 (lane 88): the overflow spellings, quoted the way
        // the source wrote them. The WRAPPING lowering below prints the BASE
        // operator (`wrap_op_text`), never these -- C has no `+%`.
        BinOp::PlusWrap => "+%",
        BinOp::MinusWrap => "-%",
        BinOp::MalWrap => "*%",
        BinOp::SchiebLinksWrap => "<<%",
        BinOp::PlusSat => "+|",
        BinOp::BitUnd => "&",
        BinOp::BitOder => "|",
        BinOp::BitXor => "^",
        BinOp::SchiebLinks => "<<",
        BinOp::SchiebRechts => ">>",
        BinOp::Und => "&&",
        BinOp::Oder => "||",
        BinOp::Gleich => "==",
        BinOp::Ungleich => "!=",
        BinOp::Kleiner => "<",
        BinOp::Groesser => ">",
        BinOp::KleinerGleich => "<=",
        BinOp::GroesserGleich => ">=",
    }
}

/// Traegt dieser Baum ein `accumulates`? Dann braucht das Erzeugnis `gabbro_kern`.
fn baum_hat_accumulates(baum: &Programm) -> bool {
    let mut ja = false;
    crate::fuer_jedes_item(baum, &mut |item| {
        if matches!(item.art, ItemArt::Accumulates(_)) {
            ja = true;
        }
    });
    ja
}

// =========================================================================================
// Die Maschinennaht: `walk`, `entry`, `entrust`, `boot`
// =========================================================================================
//
// **Vier Formen, und drei davon senken KEINEN Rumpf ab.** Das ist keine Luecke, sondern die
// Einordnung, die `lock` in dieser Datei schon traegt: der Erzeuger schreibt den Prototyp und
// die Bezugnahmen, den Rumpf schreibt jemand anderes -- *und dass er tut, was die Klausel
// sagt, ist keine Aussage dieser Uebersetzung.*
//
// > **Der Unterschied zu einer Absage (`C001`) ist scharf und wird hier gehalten.** Eine
// > Absage sagt: *es gibt kein C fuer diese Form, und ich rate keines.* Eine Vertrauensbasis
// > sagt: *das C ist ein VERSPRECHEN an einen Rumpf, den diese Einheit nicht schreibt.* Wer
// > beides vermischt, liefert entweder geratenes C oder verliert eine Form, die es gibt.
//
// `beispiele/07` sagt den Grund selbst, in seiner ersten Zeile: *„Der Eintrittspfad ist in C
// nicht ausdrueckbar (`iretq`, Registerabdruck, Stapelwechsel)."* Ein `__attribute__((naked))`
// waere die naheliegende Form -- **GCC kennt es auf x86 nicht**, und die `__asm__`-Praeambel
// darunter muesste entscheiden, wohin der Stapelwechsel greift. Die Deklaration sagt
// `stack kernstapel per cpu`; **wo dieser Stapel liegt, sagt sie nicht.** Genau dort haette
// der Erzeuger raten muessen.

/// **Eine gepruefte Bezugnahme auf einen fremden Rumpf -- und darum kein Kommentar.**
///
/// Ein `dispatch`, ein `step`: die Klausel nennt einen Namen, und in der Absenkung
/// verschwaende er spurlos, weil der Rumpf woanders steht. **Ein Kommentar daneben liest
/// niemand; diese Zeile liest der C-Uebersetzer** -- ein Name, den die Uebersetzungseinheit
/// nicht kennt, ist dort ein Fehler und keine Notiz.
///
/// `__typeof__` stood here so that the signature is **not written twice**: deriving it
/// once from the declaration and spelling it here a second time would be the second
/// register over the same fact (W7) -- *and a register that can contradict itself
/// contradicts itself.*
///
/// **CForm typOfErw (lane 142) reads it from the first register instead.** `kerne`
/// carries each function lowered by the same `prototyp_kern` the definition is
/// written from, so the reference spells the signature from the SAME lowering --
/// `static void (*const m)(void) __attribute__((unused)) = f;`, the shape the
/// `forever` watchdog already ships. A name with no core falls back to the old
/// spelling; that only happens where the prototype emission refused the same
/// name through the same helper, so the unit already carries that refusal.
///
/// **The `_Noreturn` of a `-> never` core is NOT spelled here** (lane 71). `_Noreturn`
/// is a property of a FUNCTION declaration, and C11 has no pointer-to-noreturn
/// type: `static _Noreturn void (*const m)(void)` is refused by gcc
/// (`declared '_Noreturn'`) and by clang (`'_Noreturn' can only appear on
/// functions`), measured on `beispiele/07-eintritt-und-boot.gab`. The guarantee
/// stays where both compilers read it -- on the function's own prototype, which
/// this same lowering writes as `_Noreturn void rust_eintritt(void);` -- so the
/// reference binds a plain pointer to a noreturn function instead of naming a
/// type the language does not have.
fn bezugnahme(
    marke: &str,
    ziel: &str,
    kerne: &std::collections::BTreeMap<String, (String, String)>,
) -> String {
    if let Some((rueck, liste)) = kerne.get(ziel) {
        let rueck_zeiger = rueck.strip_prefix("_Noreturn ").unwrap_or(rueck);
        return format!(
            "static {rueck_zeiger} (*const {marke})({liste}) __attribute__((unused)) = {ziel};\n"
        );
    }
    format!("static __typeof__({ziel}) *const {marke} __attribute__((unused)) = {ziel};\n")
}

/// Nennt dieses Praedikat die Domaene `mappings of`? **Der Erzeuger muss es WISSEN, ohne es
/// zu entscheiden** -- siehe `traverse`, wo der Befund ueber den Kostenpass steht.
fn nennt_abbildungen(p: &Pred) -> bool {
    match &p.art {
        PredArt::Quantor(q) => {
            matches!(q.domaene, Domaene::AbbildungenVon(_)) || nennt_abbildungen(&q.rumpf)
        }
        PredArt::Element(_, d) => matches!(d, Domaene::AbbildungenVon(_)),
        PredArt::Klammer(x) | PredArt::Nicht(x) => nennt_abbildungen(x),
        PredArt::Und(a, b) | PredArt::Oder(a, b) | PredArt::Folgt(a, b) => {
            nennt_abbildungen(a) || nennt_abbildungen(b)
        }
        _ => false,
    }
}

/// Ein Praedikat ueber dem EINEN Eintrag eines `walk`-Knotens. `it.praesent` ist dort ein
/// Zugriff auf das `format` des Knotens, und `it` ist die C-Variable des Abstiegs.
fn pred_c_eintrag(p: &Pred, fmt: &str, u: &Namen, absagen: &mut Absagen) -> Option<String> {
    Some(match &p.art {
        PredArt::Vergleich(e) => ausdruck_eintrag(e, fmt, u, absagen)?,
        PredArt::Klammer(x) => format!("({})", pred_c_eintrag(x, fmt, u, absagen)?),
        PredArt::Nicht(x) => format!("!({})", pred_c_eintrag(x, fmt, u, absagen)?),
        PredArt::Und(a, b) => format!(
            "{} && {}",
            pred_c_eintrag(a, fmt, u, absagen)?,
            pred_c_eintrag(b, fmt, u, absagen)?
        ),
        PredArt::Oder(a, b) => format!(
            "{} || {}",
            pred_c_eintrag(a, fmt, u, absagen)?,
            pred_c_eintrag(b, fmt, u, absagen)?
        ),
        _ => return None,
    })
}

/// **`{Format}_{field}(it)` -- but only where that accessor EXISTS** (`D1`, 2026-09-03).
///
/// The name is built by the emitter and never looked up, which is how
/// `beispiele/gift/641` reached `cc` as *implicit declaration of function `Pte_rest`*
/// under a checker saying `3 items, 0 errors, 0 hints`. C then assumes `int` for the
/// undeclared callee, and the `int -> uint64_t` that follows is a second complaint from
/// the same one cause -- `instrumente/zaehle-c-formen.py` books it as its 67th form.
///
/// **Two spellings reach here and they get different sentences**, because they are
/// different mistakes: a `reserved` field is one the format DECLARES and deliberately
/// gives no reader, and any other name is one the format does not have at all. *A refusal
/// that says which of the two it is turns a compile error two tools away into a sentence
/// about the declaration in front of the reader.*
fn leser_oder_absage(
    fmt: &str,
    feld: &Ident,
    wie: &str,
    u: &Namen,
    absagen: &mut Absagen,
) -> Option<String> {
    match u.formatfelder.get(fmt) {
        // No entry at all means the type is not a `format` of this unit, and the caller
        // that got here already established that it is. Staying silent would be a guess.
        None => return None,
        Some(leser) if leser.contains(&feld.text) => {}
        Some(_) => {
            weigere(
                absagen,
                feld.span,
                &format!(
                    "`{wie}` over `format {fmt}`, which hands out no reader for `{f}` -- \
                     a `reserved` field is declared and deliberately has none, and a field \
                     that is not declared has nothing to read; either way this would call \
                     `{fmt}_{f}`, which no accessor of this unit defines",
                    f = feld.text
                ),
            );
            return None;
        }
    }
    Some(format!("{fmt}_{}(it)", feld.text))
}

/// `it.feld` wird `Format_feld(it)`. **Ein anderer Grundname als `it` ist keine Absenkung,
/// sondern ein Missverstaendnis** -- der Knoteneintrag ist das einzige, worueber `down when`
/// und `leaf` reden, und wer etwas anderes nennt, bekommt eine Absage statt einer Vermutung.
fn ausdruck_eintrag(e: &Expr, fmt: &str, u: &Namen, absagen: &mut Absagen) -> Option<String> {
    Some(match &e.art {
        ExprArt::Ort(o) if o.basis.text == "it" && o.suffixe.len() == 1 => {
            let OrtSuffix::Feld(f) = &o.suffixe[0] else { return None };
            leser_oder_absage(fmt, f, &format!("it.{}", f.text), u, absagen)?
        }
        ExprArt::Klammer(x) => format!("({})", ausdruck_eintrag(x, fmt, u, absagen)?),
        ExprArt::Unaer(UnOp::Nicht, x) => {
            format!("!({})", ausdruck_eintrag(x, fmt, u, absagen)?)
        }
        ExprArt::Binaer(op, a, b) => format!(
            "{} {} {}",
            geklammert(op, a, ausdruck_eintrag(a, fmt, u, absagen)?),
            op_text(op),
            geklammert(op, b, ausdruck_eintrag(b, fmt, u, absagen)?)
        ),
        ExprArt::Zahl(_) | ExprArt::Wahr | ExprArt::Falsch => ausdruck(e, u, absagen),
        _ => return None,
    })
}

/// **A `const` NAME is a constant too** -- the third site of one named defect (2026-09-03).
///
/// `konst_zahl` reads a digit string and nothing else. `umgebung.rs` folded every `const` of
/// the unit long before the emitter runs, and `Namen::konstwert` carries the answer; the
/// `static` array length and `feldlaenge_von` already read it. **`walk_` did not**, so
///
/// ```gabbro
/// const EBENEN : u32 = 4;
/// walk Seitenabstieg levels EBENEN { node : [Pte; EINTRAEGE], ... }
/// ```
///
/// drew *"`walk ... levels` that is not a number"* over a declaration that says `4`. The
/// refusal's own reason -- *the step count cannot be guessed* -- did not apply: nothing is
/// guessed when the value is READ out of the same table `count N` is read from.
///
/// *Two registers over one thing, and the weaker one decided* (W7) -- the sentence stands
/// verbatim over `Namen::konstwert` since the day that field was built.
fn konst_oder_name(e: &Expr, u: &Namen) -> Option<i128> {
    konst_zahl(e).or_else(|| match &e.art {
        ExprArt::Ort(o) => u.konstwert.get(&o.text()).copied(),
        _ => None,
    })
}

/// **`walk` -- ein Knotentyp, zwei Praedikate und EIN Abstieg, dessen Schrittzahl aus
/// `levels` kommt.**
///
/// Das ist die eine Aussage, die ein `walk` ueber den Lauf macht: *nach `levels` Schritten ist
/// Schluss.* Sie steht damit im C und nicht nur im Pruefer -- die Schleife hat ihre Grenze aus
/// der Deklaration, genau wie `traverse` sie aus `count N` hat.
///
/// **Die Invarianten werden BENANNT und nicht geprueft** (W6): `wx_getrennt` ist eine Aussage
/// ueber das Programm, keine ueber den Lauf; sie zur Laufzeit nachzurechnen hiesse, denselben
/// Satz zweimal zu verlangen. *Und sie quantifizieren ueber `mappings of` -- die Domaene, an
/// der `traverse` einen Befund ueber den KOSTENPASS stehen hat (Ebenen mal Knotenlaenge statt
/// 512^4, sieben Groessenordnungen). Der Abstieg hier laeuft EINEN Pfad und behauptet ueber
/// die Domaene nichts; er entscheidet den Befund also weder so noch so.*
///
/// ## Was hier absichtlich NICHT steht: der Weg von der virtuellen Adresse zum Index
///
/// Die naheliegende Abstiegsfunktion nimmt eine virtuelle Adresse. **Dafuer muesste der
/// Erzeuger zwei Dinge erfinden**, die in `walk` nicht stehen: welche Adressbits eine Ebene
/// auswaehlen, und wie gross das Korn unterhalb der letzten Ebene ist. Der Abstieg nimmt
/// darum den **Indexpfad** entgegen -- und prueft ihn, weil seine Werte von aussen kommen:
/// *W6 laesst eine Pruefung nur dort weg, wo M1 sie traegt, und M1 traegt nichts ueber ein
/// Feld, das der Rufer fuellt.*
///
/// Ebenso von aussen kommt die Aufloesung eines Rahmens zu einem lesbaren Knoten. Sie steht
/// als **Parameter** da und nicht als angenommener fremder Rumpf: *ein `entry` hat keine
/// Wahl, ein Abstieg schon* -- und ein Parameter ist die Fassung, in der der Rufer sieht, was
/// er schuldet.
fn walk_(w: &WalkDecl, aus: &mut String, u: &Namen, absagen: &mut Absagen) {
    let n = &w.name.text;
    let Some(ebenen) = konst_oder_name(&w.ebenen, u) else {
        weigere(
            absagen,
            w.span,
            "`walk … levels` that is neither a number nor a `const` of this unit -- the \
             descent's step count IS the declaration's one statement about the run, and it \
             cannot be guessed",
        );
        return;
    };
    let Some(weite) = konst_oder_name(&w.knoten.laenge, u) else {
        weigere(
            absagen,
            w.span,
            "`walk` whose `node` array has no constant length -- the index bound would then \
             come from nowhere",
        );
        return;
    };
    if ebenen <= 0 || weite <= 0 {
        weigere(absagen, w.span, "`walk` with a non-positive `levels` or node length");
        return;
    }
    // **Der Knoteneintrag muss ein `format` sein.** `it.praesent` ist dort ein Zugriff mit
    // erklaerter Bytereihenfolge; ueber einem C-Verbund waere dieselbe Zeile eine
    // Layoutbehauptung, die die Deklaration nicht macht. *Der Unterschied ist genau der, den
    // `verbund` und `format_` in dieser Datei schon gegeneinander stellen.*
    let TypExpr::Pfad(p) = &w.knoten.element else {
        weigere(absagen, w.span, "`walk` whose `node` element is not a named type");
        return;
    };
    let Some(elem) = p.teile.last().map(|i| i.text.clone()) else {
        weigere(absagen, w.span, "`walk` whose `node` element has no name");
        return;
    };
    if !u.formate.contains(&elem) {
        weigere(
            absagen,
            w.span,
            "`walk` whose `node` element is not a `format` -- `down`/`leaf` read FIELDS of an \
             entry, and only a `format` says which bytes they are",
        );
        return;
    }
    // **`down : rest` is a READ, and until 2026-09-03 nothing checked it was one.**
    //
    // The descent's last line is `knoten_zu({elem}_{ab}(it), &k)`, a call on the accessor
    // `format_` writes per field -- and `format_` writes NONE for a `reserved` field.
    // `beispiele/gift/641` joined the two: `down : rest` over `rest : u64 @[63:1] reserved`
    // checked clean, emitted clean, and fell at `cc`. *The emitter built a C name instead of
    // looking one up, which is the same move `opsnamen` exists to prevent at a call site.*
    if leser_oder_absage(&elem, &w.ab, &format!("down : {}", w.ab.text), u, absagen).is_none() {
        return;
    }
    // **One cause, one sentence.** `pred_c_eintrag` refuses precisely where it can; the
    // generic form refusal underneath it is for the shapes it cannot name, and printing both
    // would make one defect look like two.
    let vorher = absagen.absagen.len();
    let Some(ab_wenn) = pred_c_eintrag(&w.ab_wenn, &elem, u, absagen) else {
        if absagen.absagen.len() == vorher {
            weigere(absagen, w.span, "`walk … down … when` predicate form");
        }
        return;
    };
    let vorher = absagen.absagen.len();
    let Some(blatt) = pred_c_eintrag(&w.blatt, &elem, u, absagen) else {
        if absagen.absagen.len() == vorher {
            weigere(absagen, w.span, "`walk … leaf` predicate form");
        }
        return;
    };

    aus.push_str(&format!(
        "\n/* walk {n} levels {ebenen} -- node [{elem}; {weite}], down `{ab}`\n",
        ab = w.ab.text
    ));
    for i in &w.invarianten {
        let laeuft = match i.laeuft {
            Laeuft::Online => "online",
            Laeuft::Offline => "offline",
        };
        // **The comment said `COMPILE TIME (W6)`, and no pass decided it** (2026-08-31).
        //
        // W6 divides labour: what a pass settled, the machine does not check a second time.
        // *That sentence needs a pass.* Measured on this line: an unsatisfiable walk
        // invariant passes with `0 errors, 0 hints`, produces no template in the
        // certificate, and -- until the same day -- no obligation either.
        //
        // A refusal was weighed and dropped: `runs online` at a `table … ops` IS carried
        // (`table.ops.erhaltung`, machine-checked), and at a `table` without `ops` it becomes
        // an `E` per `maintains`. **A rule over the word `online` would hit two registers
        // that work in order to reach the one that does not.** So the gap is booked instead:
        // `gabbro pflichten` counts it as `W`, and the comment says where it stands rather
        // than claiming it is settled.
        aus.push_str(&format!(
            " * invariant {} runs {laeuft} -- NOT checked here and by no pass either;\n\
             \x20*   it stands as a `W` obligation in `gabbro pflichten`{}\n",
            kommentartext(&i.name.text),
            if nennt_abbildungen(&i.pred) {
                ".\n *   It quantifies over `mappings of`, whose bound is an open finding\n\
                 \x20*   about the COST PASS (see `traverse`). This descent walks ONE path\n\
                 \x20*   and claims nothing about the domain"
            } else {
                ""
            }
        ));
    }
    aus.push_str(" */\n");
    aus.push_str(&format!("#define {n}_EBENEN {ebenen}u\n"));
    aus.push_str(&format!("#define {n}_WEITE {weite}u\n"));
    aus.push_str(&format!(
        "\ntypedef struct {{ {elem} eintraege[{weite}]; }} {n}_knoten;\n"
    ));
    aus.push_str(&format!(
        "\nstatic inline __attribute__((unused)) bool {n}_ist_blatt(const {elem} *it) {{ return (bool)({blatt}); }}\n"
    ));
    aus.push_str(&format!(
        "static inline __attribute__((unused)) bool {n}_steigt_ab(const {elem} *it) {{ return (bool)({ab_wenn}); }}\n"
    ));
    // **Der Abstieg. `levels` ist die Schranke, und sie steht als Zahl da.**
    // **CForm schrittStmt (lane 142): `+= 1`, not `++`** -- the level counter
    // steps inside the admitted class like every other generator loop.
    aus.push_str(&format!(
        "\nstatic inline __attribute__((unused)) bool {n}_absteigen(const {n}_knoten *wurzel, const uint32_t *index,\n\
         \x20       bool (*knoten_zu)(uint64_t, const {n}_knoten **), const {elem} **blatt) {{\n\
         \x20   const {n}_knoten *k = wurzel;\n\
         \x20   for (uint32_t e = 0; e < {n}_EBENEN; e += 1) {{\n\
         \x20       /* The bound comes from `node [{elem}; {weite}]`; the VALUE comes from\n\
         \x20          the caller, and that is why the check stands here (W6). */\n\
         \x20       if (index[e] >= {n}_WEITE) return false;\n\
         \x20       const {elem} *it = &k->eintraege[index[e]];\n\
         \x20       if ({n}_ist_blatt(it)) {{ *blatt = it; return true; }}\n\
         \x20       if (!{n}_steigt_ab(it)) return false;\n\
         \x20       if (!knoten_zu({elem}_{ab}(it), &k)) return false;\n\
         \x20   }}\n\
         \x20   return false;\n\
         }}\n",
        ab = w.ab.text
    ));
}

/// **`entry` -- der Vektor, der Vertrag, und ein Prototyp fuer einen Rumpf, den C nicht
/// schreiben kann.**
///
/// `beispiele/07` sagt es in seiner ersten Zeile: *„Der Eintrittspfad ist in C nicht
/// ausdrueckbar (`iretq`, Registerabdruck, Stapelwechsel)."* **Das ist keine Absage, sondern
/// eine Einordnung** -- dieselbe, die `lock` hier schon traegt: der Erzeuger nennt das
/// Primitiv und definiert es nicht.
///
/// *Warum nicht `__attribute__((naked))` plus `__asm__`:* GCC kennt `naked` auf x86 gar nicht,
/// und die Praeambel darunter muesste entscheiden, **wohin** der Stapelwechsel greift.
/// `stack kernstapel per cpu` sagt, DASS gewechselt wird; wo dieser Stapel liegt, sagt keine
/// Klausel. Ein Erzeuger, der das erfindet, macht jeden Pass davor zunichte.
///
/// **Was er dagegen tut, ist den Vertrag pruefbar machen:** der Vektor wird eine Zahl im C
/// (die IDT-Einrichtung braucht sie), und `dispatch` wird eine **gepruefte Bezugnahme** --
/// ein Verteiler, den diese Einheit nicht kennt, ist dort ein Uebersetzungsfehler.
///
/// **Eine andere Architektur wird BENANNT abgelehnt.** Registerabdruck, Stapelwechsel und
/// Verschachtelung sind je Architektur andere; `arch` steht in der Deklaration, damit hier
/// nicht geraten wird.
fn eintritt(
    e: &EntryDecl,
    aus: &mut String,
    ruempfe: &BTreeSet<String>,
    kerne: &std::collections::BTreeMap<String, (String, String)>,
    absagen: &mut Absagen,
) {
    if e.arch.text != "x86_64" {
        weigere(
            absagen,
            e.span,
            "`entry` for an architecture other than x86_64 -- register footprint, stack \
             switch and nesting are different per architecture, and `arch` stands in the \
             declaration so that nobody has to guess which",
        );
        return;
    }
    let n = &e.name.text;
    let regs = |l: &Vec<(Ident, Ident)>| {
        if l.is_empty() {
            "(none)".to_string()
        } else {
            l.iter()
                .map(|(x, r)| format!("{}={}", x.text, r.text))
                .collect::<Vec<_>>()
                .join(" ")
        }
    };
    // **Die leere Liste ist eine AUSSAGE, kein Fehlen** («G7»). Sie wie ein fehlendes Feld zu
    // drucken hiesse, die staerkste Zusage unsichtbar zu machen.
    let liste = |l: &Vec<Ident>| {
        if l.is_empty() {
            "(none -- and that is a statement, not an omission)".to_string()
        } else {
            l.iter().map(|x| x.text.clone()).collect::<Vec<_>>().join(" ")
        }
    };
    aus.push_str(&format!(
        "\n/* entry {n} -- arch {}{}\n",
        e.arch.text,
        match &e.via {
            Some(v) => format!(", via {}", v.text),
            None => String::new(),
        }
    ));
    if let Some(v) = &e.vektor {
        match konst_zahl(v) {
            Some(k) => aus.push_str(&format!(" * vector {k}\n")),
            None => aus.push_str(" * vector: not a constant in this unit\n"),
        }
    }
    aus.push_str(&format!(" * regs in : {}\n", kommentartext(&regs(&e.regs_in))));
    aus.push_str(&format!(" * regs out: {}\n", kommentartext(&regs(&e.regs_out))));
    aus.push_str(&format!(" * preserves: {}\n", kommentartext(&liste(&e.preserves))));
    aus.push_str(&format!(" * clobbers : {}\n", kommentartext(&liste(&e.clobbers))));
    aus.push_str(&format!(
        " * stack {}{}{}\n",
        kommentartext(&e.stack.text),
        if e.pro_kern { ", per cpu" } else { "" },
        match e.ist.as_ref().and_then(konst_zahl) {
            Some(i) => format!(", ist {i}"),
            None => String::new(),
        }
    ));
    aus.push_str(&format!(
        " * nesting: {}\n",
        match &e.verschachtelt {
            Some(Verschachtelt::Nie) => "never".to_string(),
            Some(Verschachtelt::Maskiert) => "masked".to_string(),
            Some(Verschachtelt::Begrenzt(x)) => match konst_zahl(x) {
                Some(k) => format!("bounded {k}"),
                None => "bounded (not a constant here)".to_string(),
            },
            None => "not declared".to_string(),
        }
    ));
    aus.push_str(
        " *\n\
         \x20* THE STUB IS NOT A C FUNCTION. It is entered by hardware, it keeps the register\n\
         \x20* footprint above and it leaves with `iretq` -- none of which C can write. What\n\
         \x20* stands here is the PROMISE (a prototype and the vector), the same class `lock`\n\
         \x20* carries in this file: the emitter names the primitive and does not define it. */\n",
    );
    if let Some(k) = e.vektor.as_ref().and_then(konst_zahl) {
        aus.push_str(&format!("#define gabbro_eintritt_{n}_VEKTOR {k}u\n"));
    }
    aus.push_str(&format!("void gabbro_eintritt_{n}(void);\n"));
    // **`dispatch` waere sonst der eine Name, der spurlos verschwindet.**
    let ziel = e.dispatch.teile.last().map(|i| i.text.clone()).unwrap_or_default();
    if ruempfe.contains(&ziel) {
        aus.push_str(&bezugnahme(&format!("gabbro_eintritt_{n}_verteiler"), &ziel, kerne));
    } else {
        aus.push_str(&format!(
            "/* dispatch `{}`: not declared in this unit, so there is nothing here to bind it\n\
             \x20* to. `N006` holds it against the declarations; this file cannot. */\n",
            kommentartext(&e.dispatch.text())
        ));
    }
}

/// **`entrust` -- der Raum, dessen INHALT Gabbro nicht kennt.**
///
/// *Gabbro sagt ueber den Gast nichts:* keine Kosten, keine Wirkungen, keine Terminierung.
/// Was es sagt, ist der **Vertrag am Eintritt**, und den traegt das Erzeugnis: ein Prototyp
/// fuer die Uebergabe, der Raum als **gepruefte Bezugnahme** und die Annahme im Kopf der
/// Datei, wo die anderen Annahmen stehen (`SYNTAX.md` §12).
///
/// **Der Raum wird geprueft und nicht bloss genannt.** `at Gastbild` nimmt einen NAMEN -- *ein
/// `entrust` auf einen gerechneten Wert waere ein Sprung an eine ausgerechnete Adresse* -- und
/// ein `_Static_assert` ueber seiner Groesse zwingt den C-Uebersetzer, den Typ vollstaendig zu
/// kennen. Ein Raum, den diese Einheit nicht erklaert, faellt dort auf.
///
/// **Der Sprung selbst ist kein C.** Er setzt einen Registervertrag, wechselt den Stapel und
/// gibt die Kontrolle an Code ab, ueber den nichts bekannt ist. Dieselbe Naht wie bei `entry`,
/// mit demselben Ergebnis: Prototyp statt Rumpf, Vertrauensbasis statt Erzeugnis.
fn anvertrauen(t: &EntrustDecl, aus: &mut String, u: &Namen, absagen: &mut Absagen) {
    if t.arch.text != "x86_64" {
        weigere(
            absagen,
            t.span,
            "`entrust` for an architecture other than x86_64 -- the guest's entry contract is \
             a register contract, and which registers those are is what `arch` says",
        );
        return;
    }
    let n = &t.name.text;
    let raum = &t.raum.text;
    let regs = if t.regs_gast.is_empty() {
        "(none)".to_string()
    } else {
        t.regs_gast
            .iter()
            .map(|(x, r)| format!("{}={}", x.text, r.text))
            .collect::<Vec<_>>()
            .join(" ")
    };
    aus.push_str(&format!(
        "\n/* entrust {n} at {raum} -- arch {}\n\
         \x20* guest regs: {}\n\
         \x20* stack {}\n\
         \x20* under `assume {}` -- it stands in the assumption list at the head of this file,\n\
         \x20*   with the probe that could refute it. An assumption no probe can contradict is\n\
         \x20*   not isolation but a wish.\n\
         \x20*\n\
         \x20* GABBRO SAYS NOTHING ABOUT THE BODY: no cost, no effects, no termination. The\n\
         \x20* handover sets a register contract and switches stacks, and C writes neither --\n\
         \x20* so what stands here is the prototype and the contract, not a body. */\n",
        t.arch.text,
        kommentartext(&regs),
        kommentartext(&t.stapel.text),
        kommentartext(&t.annahme.text)
    ));
    // Nur ein Name, den diese Einheit als C-Typ erklaert, kann geprueft werden. Ein
    // Bereichstyp senkt zu seinem Traeger ab und hat keinen -- dort bliebe nur der Kommentar.
    if u.verbunde.contains(raum)
        || u.tabellen.iter().any(|x| x == raum)
        || u.formate.contains(raum)
        || u.geraete.contains_key(raum)
    {
        aus.push_str(&format!(
            "_Static_assert(sizeof({raum}) > 0,\n\
             \x20   \"the space an `entrust` hands over must be a declared, complete type\");\n"
        ));
    } else {
        // **emission-144 (`statikAssert`): the assert or a named refusal, no silent state.**
        // A range type lowers to its carrier and has no declared C type, and an
        // undeclared space has nothing at all -- in both cases the `_Static_assert`
        // cannot be written, and handing the space over without it would be a guess.
        weigere(
            absagen,
            t.span,
            &format!(
                "an `entrust` space with no complete C type in this unit (`{raum}` names \
                 no declared record, table, format, or device) -- the `_Static_assert` \
                 cannot be written, and without it the handover is refused, not guessed"
            ),
        );
        return;
    }
    aus.push_str(&format!("void gabbro_gast_{n}(void);\n"));
}

/// **`boot` -- die Reihenfolge ist der Gegenstand, und sie steht im PRUEFER.**
///
/// Die Mode-Leiter ist ein Tokenfluss: `write_cr0(PG)` verlangt alle drei Marken, ein
/// vertauschter Schritt ist ein fehlendes Token und kein Laufzeitfehler. **Damit ist die
/// Reihenfolge zur Uebersetzungszeit entschieden (W6), und eine zweite Durchsetzung im C waere
/// derselbe Satz zum zweiten Mal.**
///
/// Der Rumpf ist ohnehin keiner: `step stapelzeiger = boot_stapel_oben` setzt ein
/// Maschinenregister, `step bootinfo_retten(ebx)` liest eines, und die Modeschritte selbst
/// sind `axiom`e -- Formen, fuer die diese Datei ausdruecklich **kein** C erzeugt. Eine
/// C-Funktion, die sie der Reihe nach riefe, waere entweder eine implizite Deklaration oder
/// eine Erfindung.
///
/// **Was bleibt, ist pruefbar:** ein Prototyp fuer die Strecke, eine **gepruefte Bezugnahme**
/// je Schritt, dessen Ziel diese Einheit als Rumpf kennt, und eine fuer `dispatch`. *Ein
/// Schritt, der auf einen Namen zeigt, den es nicht gibt, faellt damit beim Uebersetzen auf
/// und nicht beim Booten.*
///
/// Ein `step name = wert` wird ein `static const uint64_t`: er nennt einen WERT, den der
/// Strecke jemand geben muss, und dass er 64 Bit breit ist, sagt `arch x86_64` -- fuer jede
/// andere Architektur weigert sich diese Funktion, statt eine Breite anzunehmen.
fn bootstrecke(
    b: &BootDecl,
    aus: &mut String,
    u: &Namen,
    ruempfe: &BTreeSet<String>,
    kerne: &std::collections::BTreeMap<String, (String, String)>,
    absagen: &mut Absagen,
) {
    if b.arch.text != "x86_64" {
        weigere(
            absagen,
            b.span,
            "`boot` for an architecture other than x86_64 -- a boot step sets machine \
             registers, and how wide they are is what `arch` says",
        );
        return;
    }
    let n = &b.name.text;
    aus.push_str(&format!("\n/* boot {n} -- arch {}\n", b.arch.text));
    for (i, s) in b.schritte.iter().enumerate() {
        match s {
            BootSchritt::Ruf(r) => aus.push_str(&format!(
                " * step {}: {}\n",
                i + 1,
                kommentartext(&r.target_text())
            )),
            BootSchritt::Setzt { name, .. } => aus.push_str(&format!(
                " * step {}: {} = <value>\n",
                i + 1,
                kommentartext(&name.text)
            )),
        }
    }
    aus.push_str(&format!(" * dispatch {}\n", kommentartext(&b.dispatch.text())));
    aus.push_str(
        " *\n\
         \x20* THE ORDER IS DECIDED AT COMPILE TIME (W6) and is not enforced again here: the\n\
         \x20* mode ladder is a token flow, and a swapped step is a MISSING TOKEN, not a\n\
         \x20* run-time error. The steps themselves set and read machine registers and are\n\
         \x20* `axiom`s, for which this file deliberately emits no C -- so what stands here is\n\
         \x20* a prototype for the run and one checked reference per step that has a body. */\n",
    );
    aus.push_str(&format!("void gabbro_boot_{n}(void);\n"));
    for (i, s) in b.schritte.iter().enumerate() {
        match s {
            // Ein `axiom` hat keinen Prototyp -- es steht als Annahme im Kopf der Datei, und
            // eine Bezugnahme darauf waere hier ein Uebersetzungsfehler.
            BootSchritt::Ruf(r) => {
                let ziel = r.path().and_then(|p| p.teile.last()).map(|x| x.text.clone()).unwrap_or_default();
                if ruempfe.contains(&ziel) {
                    aus.push_str(&bezugnahme(&format!("gabbro_boot_{n}_s{}", i + 1), &ziel, kerne));
                }
            }
            BootSchritt::Setzt { name, wert } => {
                aus.push_str(&format!(
                    "static const uint64_t gabbro_boot_{n}_{} __attribute__((unused)) = {};\n",
                    name.text,
                    ausdruck(wert, u, absagen)
                ));
            }
        }
    }
    let ziel = b.dispatch.teile.last().map(|x| x.text.clone()).unwrap_or_default();
    if ruempfe.contains(&ziel) {
        aus.push_str(&bezugnahme(&format!("gabbro_boot_{n}_dispatch"), &ziel, kerne));
    } else {
        aus.push_str(&format!(
            "/* dispatch `{}`: not declared in this unit, so there is nothing here to bind it\n\
             \x20* to. `N006` holds it against the declarations; this file cannot. */\n",
            kommentartext(&b.dispatch.text())
        ));
    }
}

/// **«B26» -- the fallible register access, and the LOWERING is the whole point.**
///
/// `reg QUEUE_SIZE : u16 @0x0c class r requires QUEUE_SIZE <= QMAX else Geraetelug::ZuGross`
/// makes the READ fallible. The lowering:
///
/// ```c
/// uint16_t q;
/// {
///     Geraetelug e;
///     q = (*(volatile uint16_t *)(d->basis + 0xc));   /* ONE read */
///     if (!(q <= QMAX)) { e = Geraetelug_ZuGross; <else block> }
/// }
/// ```
///
/// **The register is read exactly ONCE, and the condition is checked on the BINDING.** A
/// second volatile read would be a second value -- *`d.REG > 0` and `d.REG` are two
/// questions to a device that may answer differently*, and that is «B33» word for word.
/// `Namen::ersetzungen` is what buys it: inside the condition the register's own name means
/// the local, not the access.
///
/// Returns `false` when this place is not a fallible register -- then the caller carries on
/// with the call form and its refusals.
#[allow(clippy::too_many_arguments)]
fn fehlbare_lesung(
    l: &LetSonst,
    o: &Ort,
    aus: &mut String,
    u: &Namen,
    absagen: &mut Absagen,
    tiefe: usize,
    austritt: &Austritt,
) -> bool {
    let Some(g) = u
        .geraetezeiger
        .get(&o.basis.text)
        .or_else(|| u.geraetewerte.get(&o.basis.text))
    else {
        return false;
    };
    let Some(dev) = u.geraete.get(g) else {
        return false;
    };
    // Only the register itself, not a bit field of it: a `requires` speaks about the WORD.
    let [OrtSuffix::Feld(r)] = o.suffixe.as_slice() else {
        return false;
    };
    let Some((pred, grundtyp, grundwert)) = dev.fehlbar.get(&r.text) else {
        return false;
    };
    let e = einzug(tiefe);
    let Some(ctyp) = register_ctyp(o, u) else {
        weigere(
            absagen,
            l.name.span,
            "a fallible register read whose width the emitter cannot resolve",
        );
        return true;
    };
    // **The condition reads the BINDING, not the register.** Without this line the
    // volatile access would stand in the condition as well, and the check would be about a
    // different read than the one that was bound.
    let mut innen = u.clone();
    innen
        .ersetzungen
        .insert(r.text.clone(), l.name.text.clone());
    let Some(bedingung) = pred_c(pred, &innen, absagen) else {
        weigere(
            absagen,
            l.name.span,
            "a `requires … else` at a register whose condition is not a RUN TIME condition -- \
             a quantifier, `reaches`, `Held` or an implication is proved, not evaluated (W6)",
        );
        return true;
    };
    let zugriff = ort(o, u, absagen);
    // **`e` is DECLARED only where the branch reads it** -- unlike the call form, where it
    // travels as `&e` and is used for that reason alone. A name set here and never read is
    // `-Wunused-but-set-variable`, and the emission rule compiles with `-Werror`. *A
    // silencing next to an assignment also claims something false about the code below it.*
    let mut gelesen = BTreeSet::new();
    benutzte_namen(&l.sonst, &mut gelesen);
    let (erklaerung, zuweisung) = if gelesen.contains(&l.fehlername.text) {
        (
            format!("{e}    {grundtyp} {};\n", l.fehlername.text),
            format!("{e}        {} = {grundwert};\n", l.fehlername.text),
        )
    } else {
        (String::new(), String::new())
    };
    aus.push_str(&format!("{e}{ctyp} {};\n", l.name.text));
    aus.push_str(&format!("{e}{{\n{erklaerung}"));
    aus.push_str(&format!("{e}    {} = {zugriff};\n", l.name.text));
    aus.push_str(&format!("{e}    if (!({bedingung})) {{\n{zuweisung}"));
    // `e` carries its `reason` into the view of the `else` branch -- and nowhere else.
    let mut sicht = u.clone();
    sicht
        .gruendewerte
        .insert(l.fehlername.text.clone(), grundtyp.clone());
    for k in &l.sonst.anweisungen {
        anweisung(k, aus, &sicht, absagen, tiefe + 2, austritt);
    }
    aus.push_str(&format!("{e}    }}\n{e}}}\n"));
    true
}

/// **The width table against the word list -- the check that makes the refusals above dead.**
///
/// `ganzzahlwort` refuses a word it does not carry, and `intty`/`breite_von` hand that
/// refusal on as `C001`. That is the right answer for a word the emitter cannot lower, but
/// it is an answer nobody wants to see: it would mean the language grew an integer word and
/// the emitter did not. **This test says so at build time instead.**
///
/// It reads the SAME list the lexer reads (`kw::ALLE`) and the SAME predicate the passes read
/// (`ist_intty`). A ninth integer word is then a red test, not a silent eight-byte access on
/// a device register -- which is precisely what `_ => 8` used to be.
#[cfg(test)]
mod breitentafel {
    use super::*;

    #[test]
    fn jedes_ganzzahlwort_hat_eine_breite() {
        let mut fehlend = Vec::new();
        let mut ueberzaehlig = Vec::new();
        for k in gabbro_syntax::kw::ALLE {
            match (k.ist_intty(), ganzzahlwort(*k)) {
                (true, None) => fehlend.push(k.text()),
                (false, Some(_)) => ueberzaehlig.push(k.text()),
                _ => {}
            }
        }
        assert!(
            fehlend.is_empty(),
            "`ist_intty` admits {fehlend:?}, and the emitter has no width for them -- \
             every use lowers to `C001` instead of C"
        );
        assert!(
            ueberzaehlig.is_empty(),
            "the width table carries {ueberzaehlig:?}, which `ist_intty` does not admit"
        );
    }

    /// The other direction of the same table: **the eight words, their C name and their
    /// width, written out once more.** A test that only compared against a predicate would
    /// accept a `u16` mapped to `uint64_t` -- the predicate says nothing about widths.
    #[test]
    fn die_acht_worte_stehen_einzeln() {
        use gabbro_syntax::kw::Kw;
        let erwartet: &[(Kw, &str, u32)] = &[
            (Kw::U8, "uint8_t", 1),
            (Kw::U16, "uint16_t", 2),
            (Kw::U32, "uint32_t", 4),
            (Kw::U64, "uint64_t", 8),
            (Kw::I8, "int8_t", 1),
            (Kw::I16, "int16_t", 2),
            (Kw::I32, "int32_t", 4),
            (Kw::I64, "int64_t", 8),
        ];
        for (k, c, b) in erwartet {
            assert_eq!(ganzzahlwort(*k), Some((*c, *b)), "{}", k.text());
        }
        assert_eq!(
            erwartet.len(),
            gabbro_syntax::kw::ALLE.iter().filter(|k| k.ist_intty()).count()
        );
    }

    /// **`umgebung::breite_von` is the same table in bits, and it must not drift.** Two
    /// registers over one thing is `W7`; this test is what keeps them one.
    #[test]
    fn erzeuger_und_pruefer_sagen_dieselbe_breite() {
        for k in gabbro_syntax::kw::ALLE {
            let hier = ganzzahlwort(*k).map(|(_, b)| b * 8);
            let dort = crate::umgebung::breite_von(*k).map(|(b, _)| b as u32);
            assert_eq!(hier, dort, "{}", k.text());
        }
    }

    /// Every width the table hands out has a reader and a writer. **Without this the `C001`
    /// in `wortpaar_oder_absage` would be reachable from a legal program.**
    #[test]
    fn jede_breite_hat_ein_lese_und_ein_schreibwort() {
        for k in gabbro_syntax::kw::ALLE {
            let Some((_, b)) = ganzzahlwort(*k) else { continue };
            for gross in [true, false] {
                assert!(lesewort(b, gross).is_some(), "{} {gross}", k.text());
                assert!(schreibwort(b, gross).is_some(), "{} {gross}", k.text());
            }
        }
    }
}
