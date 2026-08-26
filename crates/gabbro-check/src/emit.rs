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
    /// Je Geraet: der Raum und seine Register. **Ein Registerzugriff ist KEIN Feldzugriff**
    /// -- siehe `geraet`.
    /// **The assumption names this unit DECLARES** (2026-08-26).
    ///
    /// The emitter already prints them into the C header; until now nothing READ them.
    /// `at dma` does: which barrier a DMA access needs is a statement about the memory
    /// model, and rather than guessing it the generator DEMANDS that the unit name it.
    /// *A wall becomes a door: the refusal says which assumption is missing.*
    annahmen: BTreeSet<String>,
    geraete: HashMap<String, Geraet>,
    /// Name -> Geraetetyp, **global und konservativ**: wird derselbe Name irgendwo mit einem
    /// anderen Typ erklaert, faellt er heraus. Dieselbe Bauart wie `vorzeichenlos` -- Unwissen
    /// faellt nach lautstark, dann weigert sich der Registerzugriff.
    geraetezeiger: HashMap<String, String>,
    /// Name -> Tabelle, fuer Zeigerparameter. Konservativ wie `geraetezeiger`.
    tabellenzeiger: HashMap<String, String>,
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
    /// Die `accumulates`-Namen. **Ein Lesen wird ein Ruf, ein Schreiben auch** -- sonst
    /// stuende im C ein Zugriff auf eine Zelle, die es nicht gibt.
    akkus: BTreeSet<String>,
    /// Atomicname -> (C-Typ, `memory_order`-Wort). **K11.2.3** -- ohne den Typ hat ein
    /// `let x = A awaits { … }` keinen, und ohne die Ordnung stuende im C das Vorgabemodell
    /// von `_Atomic` statt dessen, was die Quelle sagte.
    /// **Zwei Ordnungen, nicht eine.** Die Deklaration nennt die SPEICHERseite; ein Laden
    /// mit `memory_order_release` gibt es in C11 nicht (`atomic_load_explicit` nimmt
    /// relaxed, consume, acquire oder seq_cst). *Gefunden beim Lesen des erzeugten C fuer
    /// `beispiele/14` -- der C-Uebersetzer haette es auch gesagt, aber sich darauf zu
    /// verlassen hiesse, die Absage zu delegieren, wo die Antwort hier steht.*
    atomics: HashMap<String, (String, &'static str, &'static str)>,
    /// Namen, die einen Verbund als **Wert** tragen (Parameter oder `let`). Ihr Feldzugriff
    /// ist `.`, nicht `->` -- siehe `ort`.
    werte: BTreeSet<String>,
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
    /// Name -> erklaerter Parametertyp, konservativ ueber alle Funktionen. **Nur damit
    /// bekommt ein `let d = a - b;` seinen Typ**, ohne dass ihn jemand raet.
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
    /// Function name -> its DECLARED result type expression. The one source from which a
    /// `let f = eichfeld();` can learn what `f` is without anyone guessing.
    ergebnistyp: HashMap<String, TypExpr>,
    /// (Verbund, Feld) -> erklaerter Feldtyp. Dieselbe Rolle wie `slotfeld`, eine Ebene
    /// daneben: **ohne ihn weiss der Erzeuger von `s.len` nur, dass es ein Feld ist.**
    verbundfeld: HashMap<(String, String), TypExpr>,
    /// Namen, deren Typ der Erzeuger als VORZEICHENLOS kennt. Nur fuer sie darf die untere
    /// Schranke eines `narrow` bei null wegfallen -- Unwissen faellt nach lautstark.
    vorzeichenlos: BTreeSet<String>,
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
            // **`let x = call else (e) { … }` binds a name too, and this collector does not
            // register it.** The reason is the error channel, not an oversight: a callee
            // declared `-> T or R` returns the ERROR in C and hands `T` back through
            // `*_wert`, so whether `x` ends up a value or a pointer is decided at the
            // lowering of the statement and not here. **Left open on purpose** -- and now it
            // is written down instead of falling into a catch-all.
            StmtArt::LetSonst(_) => {}
            // `let x = place awaits { … }` unwraps an ATOMIC. An atomic carries a scalar
            // payload -- never a record -- so there is nothing to register.
            StmtArt::AwaitLoad(_) => {}
            // `let x = place exchange …` likewise yields the atomic's scalar payload.
            StmtArt::Exchange(_) => {}
            // The forms that bind no name at all. **Written out one by one** so that a new
            // `StmtArt` is a compile error here rather than a silent "binds nothing".
            StmtArt::Zuweisung(_)
            | StmtArt::Wenn(_)
            | StmtArt::Match(_)
            | StmtArt::Schleife(_)
            | StmtArt::Bricht(_)
            | StmtArt::Narrow(_)
            | StmtArt::Sperrt(_)
            | StmtArt::Observiert(_)
            | StmtArt::Leave(_)
            | StmtArt::Next(_)
            | StmtArt::Publish(_)
            | StmtArt::Return(_)
            | StmtArt::Ruf(_) => {}
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
                .map(|(m, a)| format!(".{} = {}", m.text, ausdruck(a, u, absagen)))
                .collect();
            Some(format!("{{ {} }}", felder.join(", ")))
        }
        _ => None,
    }
}

/// The `const` prefix and the `section` attribute of a `static` -- **the record case only**,
/// where the C type can never end in `*` and the pointer/target distinction below does not
/// arise.
fn statischer_kopf(st: &StatischDecl) -> (&'static str, String) {
    let konst = if st.veraenderlich { "" } else { "const " };
    let abschnitt = match &st.section {
        Some(t) => format!(" __attribute__((section(\"{}\")))", t.text),
        None => String::new(),
    };
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
    /// Registername -> (Versatz, C-Wortbreite). **Der Raum steht nicht hier** -- `geraet`
    /// liest ihn direkt aus dem Baum, und ein zweites Feld daneben waere das zweite Register
    /// ueber derselben Sache (W7).
    reg: HashMap<String, (i128, String)>,
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
 * belongs to are NOT a derived work of Gabbro. The permission is conditional on this notice
 * being preserved. See LIZENZ-ZUSATZ.md.
 */
#include <stdint.h>
#include <stdbool.h>
#include <stdatomic.h>
#include <math.h>
";

/// **«F»: der Zusatz, wenn eine Einheit mit Gleitkomma rechnet.**
///
/// Er steht im erzeugten C und nicht bloss in einem Memo, weil er den Uebersetzer betrifft
/// und nicht den Leser. *Ein `-ffast-math` macht jede Aussage dieses Prueferlaufs ungueltig:
/// es erlaubt Umsortierungen, und Gleitkommaaddition ist nicht assoziativ.*
pub const KOPF_GLEITKOMMA: &str = "\
/* Diese Einheit rechnet mit Gleitkomma.
 *
 *   -ffast-math ist VERBOTEN. Es erlaubt Umsortierungen, und die Addition ist nicht
 *   assoziativ -- jede Schranke, die der Pruefer gerechnet hat, faellt damit.
 *
 *   Auf x86 wird SSE2 vorausgesetzt (die x87-Register rechnen mit 80 Bit und runden
 *   doppelt). Das steht als Annahme mit Falsifikator im Zeugnis.
 *
 *   Der Rundungsmodus ist round-to-nearest-even. Er ist globaler Zustand (MXCSR/FPCR);
 *   dass er gilt, ist eine Annahme und keine Zusage dieses Erzeugers.
 */
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
        | ItemArt::Boot(_) => {}
    });
    ja
}

/// Emits C for a tree, or refuses by name.
pub fn emittiere(baum: &Programm, absagen: &mut Absagen) -> String {
    let mut namen = Namen::default();
    crate::fuer_jedes_item(baum, &mut |item| match &item.art {
        ItemArt::Konst(k) => {
            namen.konstanten.insert(k.name.text.clone());
        }
        ItemArt::Format(f) => {
            namen.formate.insert(f.name.text.clone());
        }
        ItemArt::Device(d) => {
            namen.geraete.insert(
                d.name.text.clone(),
                Geraet {
                            reg: HashMap::new(),
                            felder: HashMap::new(),
                            umlaeufer: HashMap::new(),
                            klassen: HashMap::new(),
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
        | ItemArt::Boot(_) => {}
    });
    // **Second pass, and it needs the first**: whether a parameter is a ghost can only be
    // decided once the ghost names are known.
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Funktion(f) = &item.art {
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
            for s in &b.anweisungen {
                if let StmtArt::Let(l) = &s.art {
                    erklaert.push((l.name.text.as_str(), l.typ.as_ref()));
                }
            }
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
                    if let Some(v) = umg.konst_wert(modul, &r.versatz) {
                        reg.insert(r.name.text.clone(), (v, intty(&r.typ)));
                    }
                    if r.umlaufend {
                        umlaeufer.insert(r.name.text.clone(), r.typ.clone());
                    }
                    let breite = breite_von(&r.typ) * 8;
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
        crate::fuer_jedes_item(baum, &mut |item| {
            if let ItemArt::Atomic(a) = &item.art {
                if let Some(c) = ctyp(&a.typ, &namen) {
                    typen.push((a.name.text.clone(), c));
                }
            }
        });
        for (n, c) in typen {
            if let Some(e) = namen.atomics.get_mut(&n) {
                e.0 = c;
            }
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
            | ItemArt::Boot(_) => {}
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
                    let b = breite_von(i);
                    leser.insert(lesewort(b, gross));
                    // **Ein Achtbyteleser ist aus ZWEI Vierbytelesern gebaut**, und der
                    // Sammler kannte nur den, den ein Feld nennt. Ein `format`, dessen
                    // einziges Ganzzahlfeld `u64` ist, definiert `gabbro_le64` und ruft darin
                    // `gabbro_le32`, das nirgends steht. *Eine Abhaengigkeit zwischen zwei
                    // ERZEUGTEN Ruempfen -- der Sammler zaehlte die genannten, nicht die
                    // gebrauchten.*
                    if b == 8 {
                        leser.insert(lesewort(4, gross));
                    }
                    schreiber.insert(schreibwort(b, gross));
                    if b == 8 {
                        schreiber.insert(schreibwort(4, gross));
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
    let annahmen = crate::manifest::sammle(baum);
    namen.annahmen = annahmen.iter().map(|a| a.name.clone()).collect();
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
    crate::fuer_jedes_item(baum, &mut |item| match &item.art {
        ItemArt::Konst(k) => {
            if let Some(w) = konst_zahl(&k.wert) {
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
                    gleitkommatext(*bits)
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
        | ItemArt::Boot(_) => {}
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
            if let TypExpr::Feld(a) = &st.typ {
                feldstatisch(st, a, &mut aus, &namen, absagen);
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
                        // **A brace initialiser, not a compound literal.** `ruf` writes
                        // `(P){ .a = 1 }` -- an lvalue with static storage duration, which C11
                        // 6.7.9p4 does not admit as an initialiser for a static object. At file
                        // scope the same designators go in braces, and `cc -Werror` is the
                        // second reader of the completeness (`-Wmissing-field-initializers`).
                        if let Some(felder) = verbundmarken(&st.wert, &n.text, &namen, absagen) {
                            let (konst, abschnitt) = statischer_kopf(st);
                            aus.push_str(&format!(
                                "\nstatic {konst}{} {}{abschnitt} __attribute__((unused)) = {felder};\n",
                                n.text, st.name.text
                            ));
                            return;
                        }
                        weigere(
                            absagen,
                            st.name.span,
                            "`static` of a `tagged` type or a record initialised with a plain                              number -- which variant the zero is, the declaration does not                              say, and a record has no scalar value. **A record initialised by                              its LABELLED CALL lowers since 2026-08-25** -- write                              `T(f: …, g: …)`, which says field by field what the number does                              not",
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
                    Some(n) => n.to_string(),
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
            let abschnitt = match &st.section {
                Some(t) => format!(" __attribute__((section(\"{}\")))", t.text),
                None => String::new(),
            };
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
            aus.push_str(&format!(
                "\nstatic {konst}{c} {konst_nach}{}{abschnitt} __attribute__((unused)) = {w};\n",
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
                 \x20   for (uint32_t k = 0; k < (uint32_t)({n}); k++) {{\n\
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
                    match ctyp(&a.typ, &namen) {
                        Some(c) => aus.push_str(&format!("\n_Atomic {c} {};\n", a.name.text)),
                        None => weigere(absagen, a.span, "`atomic` of an unresolvable type"),
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
                Some(o) => match ctyp(&a.typ, &namen) {
                    Some(c) => {
                        let (wort, notiz) = match o {
                            Ordnung::Release => ("memory_order_release", "publishes"),
                            Ordnung::Acquire => ("memory_order_acquire", "awaits"),
                            Ordnung::Seq => ("memory_order_seq_cst", "total order"),
                            Ordnung::Relaxed => ("memory_order_relaxed", "no payload"),
                        };
                        let last = match &a.obermenge {
                            Some(Nutzlast::Orte(l)) => l
                                .iter()
                                .map(|x| x.text())
                                .collect::<Vec<_>>()
                                .join(", "),
                            _ => "nothing".into(),
                        };
                        aus.push_str(&format!(
                            "\n/* {} under A10 (release_stellt_sichtbarkeit_her, UNFALSIFIABLE):\n\
                             \x20* the ordering below is the one the source declared, not C's default.\n\
                             \x20* payload: {last} */\n_Atomic {c} {};\n#define {}_ORDER {wort}\n",
                            notiz, a.name.text, a.name.text
                        ));
                    }
                    None => weigere(absagen, a.span, "`atomic` of an unresolvable type"),
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
        ItemArt::Funktion(f) => funktion(f, &mut aus, &mut rumpf, &namen, absagen),
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
        ItemArt::Entry(e) => eintritt(e, &mut rumpf, &ruempfe, absagen),
        ItemArt::Entrust(t) => anvertrauen(t, &mut rumpf, &namen, absagen),
        ItemArt::Boot(b) => bootstrecke(b, &mut rumpf, &namen, &ruempfe, absagen),
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
    });
    aus.push_str(&rumpf);
    aus
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
        sammle_retry(baum, modul, b, &mut aus);
    });
    aus
}

fn sammle_retry(baum: &Programm, modul: &str, b: &Block, aus: &mut HashMap<u32, i128>) {
    for s in &b.anweisungen {
        // **The one decision this collector makes: does this statement OPEN a `retry`?**
        if let StmtArt::Schleife(sch) = &s.art {
            if let Schleife::Retry(r) = sch.as_ref() {
                let budget = crate::umgebung::Umgebung::sammle(baum)
                    .konst_wert(modul, &r.schranke);
                let je_gang = crate::kosten::durchgangskosten(baum, modul, r, HashMap::new());
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
            sammle_retry(baum, modul, k, aus);
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
fn weigere(absagen: &mut Absagen, span: gabbro_syntax::span::Span, was: &str) {
    absagen.schiebe(
        Absage::fehler("C001", span, format!("no lowering: {was}")).mit_notiz(
            "the emitter refuses by name instead of emitting something plausible -- a \
             generator that guesses undoes every pass in front of it",
        ),
    );
}

fn konst_zahl(e: &Expr) -> Option<i128> {
    match &e.art {
        ExprArt::Zahl(n) => Some(*n as i128),
        _ => None,
    }
}

/// Ein Typausdruck als Text -- **nur zum VERGLEICHEN zweier Deklarationen**, nicht zum
/// Absenken. `TypExpr` traegt Spannen und ist darum nicht vergleichbar.
fn typtext(t: &TypExpr) -> String {
    match t {
        TypExpr::Int(i) => intty(i),
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
        if let TypExpr::Feld(a) = &f.typ.typ {
            let (Some(el), Some(n)) = (ctyp(&a.element, u), feldlaenge(&a.laenge, u)) else {
                weigere(absagen, f.name.span, "array field type -- element or length");
                continue;
            };
            aus.push_str(&format!("    {el} {}[{n}];\n", f.name.text));
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
        ExprArt::Zahl(n) => Some(n.to_string()),
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
    aus.push_str(&format!("\ntypedef struct {{\n"));
    if let Some(slot) = &t.slot {
        for f in &slot.felder {
            let c = match &f.typ {
                SlotTyp::Typ(t) => ctyp(t, u),
                // `intty wrapping` -- the wraparound is DECLARED («B32»), so the C type is
                // the plain unsigned word whose wrap C already defines.
                SlotTyp::Wrapping(i) => Some(intty(i)),
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
    for r in &d.register {
        let breite = breite_von(&r.typ) * 8;
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
    let felder: String = u
        .geraete
        .get(&d.name.text)
        .map(|g| {
            g.parameter
                .iter()
                .map(|(n, c)| format!(" {c} {n};"))
                .collect::<String>()
        })
        .unwrap_or_default();
    aus.push_str(&format!(
        "\ntypedef struct {{ volatile uint8_t *basis;{felder} }} {};\n",
        d.name.text
    ));
    for b in &d.baenke {
        bank(d, b, aus, u, absagen);
    }
    for u2 in &d.uebergaenge {
        uebergang(d, u2, aus, u, absagen);
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
/// static inline uint64_t Vtd_FRR_FR_LO(const Vtd *d, uint32_t i) {
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
        let breite = intty(&r.typ);
        aus.push_str(&format!(
            "\nstatic inline {breite} {}_{}_{}(const {} *d, uint32_t i) {{\n\
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
            "\nstatic inline void {}_{}_setz_{}({} *d, uint32_t i, {breite} x) {{\n\
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
        ExprArt::Zahl(n) => n.to_string(),
        ExprArt::Klammer(x) => format!("({})", ausdruck_geraet(x, d, u, absagen)?),
        ExprArt::Binaer(op, a, b) => format!(
            "{} {} {}",
            ausdruck_geraet(a, d, u, absagen)?,
            op_text(op),
            ausdruck_geraet(b, d, u, absagen)?
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
    let wortbits: u32 = match breite.as_str() {
        "uint8_t" => 8,
        "uint16_t" => 16,
        "uint32_t" => 32,
        _ => 64,
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

    let wort = format!("(*(volatile {breite} *)(d->basis + {versatz}))");
    aus.push_str(&format!("\n/* transition {} */\n", x.name.text));
    if let Some(p) = &x.requires {
        // Sichtbar, aber nicht ausgefuehrt -- siehe oben.
        let _ = p;
        aus.push_str("/* requires: a caller obligation, not a generated assertion */\n");
    }
    aus.push_str(&format!(
        "static inline void {}_{}({} *d) {{\n",
        d.name.text, x.name.text, d.name.text
    ));
    match &d.mirrors {
        Some(m) if m.ziel.basis.text == reg => {
            let quelle = m.quelle.basis.text.clone();
            let Some((qv, qb)) = g.reg.get(&quelle) else {
                weigere(absagen, m.span, "`mirrors` from a register this device does not declare");
                return;
            };
            aus.push_str(&format!(
                "    {breite} _s = (*(volatile {qb} *)(d->basis + {qv}));\n\
                 \x20   {wort} = ({breite})((_s & ({breite})~({breite}){geaendert}u) | ({breite}){neu}u);\n"
            ));
        }
        _ => aus.push_str(&format!("    {wort} = ({breite}){neu}u;\n")),
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
            let an = matches!(&s.nach.art, ExprArt::Zahl(n) if *n != 0);
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
            let breite = breite_von(i);
            let c = intty(i);
            let leser = lesewort(breite, gross);
            if !feld.reserviert {
                aus.push_str(&format!(
                    "static inline {c} {n}_{f2}(const {n} *v) {{ return ({c}){leser}(v->bytes + {versatz}); }}\n",
                    f2 = feld.name.text
                ));
                // **Der SCHREIBER, und er heisst `_setz_`** -- `SPRACHE.md`:355 sagt ihn
                // seit jeher zu. Ohne ihn ist ein `format` nur halb abgesenkt, und ein
                // Treiber, der einen Rahmen STELLT, faellt auf eine Zuweisung an einen
                // Funktionsaufruf.
                aus.push_str(&format!(
                    "static inline void {n}_setz_{f2}({n} *v, {c} x) {{ {sw}(v->bytes + {versatz}, x); }}\n",
                    f2 = feld.name.text,
                    sw = schreibwort(breite, gross)
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
                        Some(vorher) if *vorher != intty(gi) => break,
                        Some(_) => {}
                        None => {
                            breite = Some(breite_von(gi));
                            ctyp_wort = Some(intty(gi));
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
        let leser = lesewort(breite, gross);
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
                TypExpr::Int(gi) if intty(gi) == c => {}
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
                    Some(k) => format!(" * {k}u"),
                    None => {
                        weigere(absagen, g.span, "`scale` that is not a constant");
                        return;
                    }
                },
                None => String::new(),
            };
            aus.push_str(&format!(
                "static inline {ergebnis} {n}_{f2}(const {n} *v) {{ \
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
                    "static inline void {n}_setz_{f2}({n} *v, {ergebnis} x) {{ \
                     {c} w = ({c}){leser}(v->bytes + {versatz}); \
                     w = ({c})((w & ({c})~(({c}){maske}u << {lo})) | ((({c})x & {maske}u) << {lo})); \
                     {sw}(v->bytes + {versatz}, w); }}\n",
                    f2 = g.name.text,
                    sw = schreibwort(breite, gross)
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
        "static inline bool {n}_gueltig(const {n} *v) {{\n    if (v->len < {versatz}u) return false;\n"
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
                _ => vorzeichen(u.typen.get(n)?, u),
            }
        }
        _ => None,
    }
}

fn breite_von(i: &IntTy) -> u32 {
    match i.wort {
        gabbro_syntax::kw::Kw::U8 | gabbro_syntax::kw::Kw::I8 => 1,
        gabbro_syntax::kw::Kw::U16 | gabbro_syntax::kw::Kw::I16 => 2,
        gabbro_syntax::kw::Kw::U32 | gabbro_syntax::kw::Kw::I32 => 4,
        _ => 8,
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
fn schreibwort(breite: u32, gross: bool) -> &'static str {
    match (breite, gross) {
        (1, _) => "gabbro_setz_u8",
        (2, true) => "gabbro_setz_be16",
        (2, false) => "gabbro_setz_le16",
        (4, true) => "gabbro_setz_be32",
        (4, false) => "gabbro_setz_le32",
        (8, true) => "gabbro_setz_be64",
        _ => "gabbro_setz_le64",
    }
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

fn lesewort(breite: u32, gross: bool) -> &'static str {
    match (breite, gross) {
        (1, _) => "gabbro_u8",
        (2, true) => "gabbro_be16",
        (2, false) => "gabbro_le16",
        (4, true) => "gabbro_be32",
        (4, false) => "gabbro_le32",
        (8, true) => "gabbro_be64",
        _ => "gabbro_le64",
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
            ausdruck_format(a, fmt, u, absagen),
            op_text(op),
            ausdruck_format(b, fmt, u, absagen)
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
        | ExprArt::Unaer(UnOp::Negativ, _) => ausdruck(e, u, absagen),
    }
}

fn intty(i: &IntTy) -> String {
    // The word IS the width -- `u32 wrapping` lowers to `uint32_t`, whose wraparound C
    // defines. «B32»: the wraparound is spoken at the declaration, not tolerated.
    match i.wort {
        gabbro_syntax::kw::Kw::U8 => "uint8_t",
        gabbro_syntax::kw::Kw::U16 => "uint16_t",
        gabbro_syntax::kw::Kw::U32 => "uint32_t",
        gabbro_syntax::kw::Kw::U64 => "uint64_t",
        gabbro_syntax::kw::Kw::I8 => "int8_t",
        gabbro_syntax::kw::Kw::I16 => "int16_t",
        gabbro_syntax::kw::Kw::I32 => "int32_t",
        _ => "int64_t",
    }
    .to_string()
}

/// The array length of a `table`. **A length this emitter cannot read is refused** — the same
/// reason as above, and here it decides how much memory the struct has.
fn zahltext(e: &Expr, absagen: &mut Absagen) -> String {
    match &e.art {
        ExprArt::Zahl(n) => n.to_string(),
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

fn ctyp(t: &TypExpr, u: &Namen) -> Option<String> {
    match t {
        // The abstract declarator -- a function pointer in a position that has no name of
        // its own (a parameter, a result). See `fnzeiger_deklarator`.
        TypExpr::FnZeiger(z) => fnzeiger_deklarator(z, "", u),
        TypExpr::Int(i) => Some(intty(i)),
        // **«F»: `f32`/`f64` senken zu `float`/`double` ab -- und mehr sagt der Erzeuger
        // nicht.** Der Bereich ist ein M1-Faktum und lebt im Pruefer, genau wie beim
        // Ganzzahlbereich; die zwei Bits ebenso.
        TypExpr::Float(f) => Some(
            if f.wort == gabbro_syntax::kw::Kw::F32 {
                "float".into()
            } else {
                "double".into()
            },
        ),
        TypExpr::Bool(_) => Some("bool".into()),
        TypExpr::Pfad(p) => {
            let n = p.teile.last()?.text.clone();
            Some(match n.as_str() {
                "bool" => "bool".into(),
                "u8" => "uint8_t".into(),
                "u16" => "uint16_t".into(),
                "u32" => "uint32_t".into(),
                "u64" => "uint64_t".into(),
                "i8" => "int8_t".into(),
                "i16" => "int16_t".into(),
                "i32" => "int32_t".into(),
                "i64" => "int64_t".into(),
                "f32" => "float".into(),
                "f64" => "double".into(),
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
                _ if u.typen.contains_key(&n) => {
                    return ctyp(u.typen.get(&n)?, u);
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
            let konst = if z.rechte.iter().any(|r| {
                matches!(
                    r,
                    Recht::Schreiben | Recht::LesenSchreiben | Recht::Eigen(_)
                )
            }) {
                ""
            } else {
                "const "
            };
            Some(format!("{konst}{ziel} *"))
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
    fn in_expr(e: &Expr) -> bool {
        match &e.art {
            ExprArt::Ruf(_) => true,
            ExprArt::Klammer(x) | ExprArt::Unaer(_, x) => in_expr(x),
            ExprArt::Binaer(_, a, b) => in_expr(a) || in_expr(b),
            _ => false,
        }
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
        return "";
    };
    // Eine Funktion ohne Ergebnis hat nichts, was sich zusammenfassen liesse.
    if f.ergebnis.is_none() {
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
            WirkungArt::Liest(o) if liest_geraet(o, u, f) => return "",
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

/// Nennt diese `reads`-Wirkung ein Geraet -- als Typname, als Parameter oder als Griff?
fn liest_geraet(o: &Ort, u: &Namen, f: &FnDecl) -> bool {
    let n = &o.basis.text;
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
            TypExpr::Int(_)
            | TypExpr::Float(_)
            | TypExpr::Bool(_)
            | TypExpr::Never(_)
            | TypExpr::Index { .. }
            | TypExpr::FnZeiger(_)
            | TypExpr::Feld(_)
            | TypExpr::Verbund(_, _)
            | TypExpr::Varianten(_, _) => {}
        }
    }
    // **Und die `let`-gebundenen Geraetegriffe** -- `let v = Vtd(basis);`. Sie sind WERTE,
    // und der Ruf eines `transition` darauf nimmt ihre Adresse.
    if let FnRumpf::Block(b) = &f.rumpf {
        fn im_block(b: &Block, u: &Namen, lokal: &mut Namen) {
            for s in &b.anweisungen {
                if let StmtArt::Let(l) = &s.art {
                    if let ExprArt::Ruf(r) = &l.wert.art {
                        let Some(n) = r.path().map(|p| p.text()) else { continue };
                        if u.geraete.contains_key(&n) {
                            lokal.geraetewerte.insert(l.name.text.clone(), n);
                            lokal.werte.insert(l.name.text.clone());
                        }
                    }
                }
                for k in crate::unterbloecke(s) {
                    im_block(k, u, lokal);
                }
            }
        }
        let mut gefunden = lokal.clone();
        im_block(b, u, &mut gefunden);
        lokal = gefunden;
        lokale_lets(b, &mut lokal);
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
/// claim a type for a name the product never spells.
fn lokale_lets(b: &Block, lokal: &mut Namen) {
    fn sammle<'a>(b: &'a Block, aus: &mut Vec<&'a LetStmt>, wieoft: &mut HashMap<String, u32>) {
        for s in &b.anweisungen {
            if let StmtArt::Let(l) = &s.art {
                *wieoft.entry(l.name.text.clone()).or_insert(0) += 1;
                aus.push(l);
            }
            for k in crate::unterbloecke(s) {
                sammle(k, aus, wieoft);
            }
        }
    }
    let (mut lets, mut wieoft) = (Vec::new(), HashMap::new());
    sammle(b, &mut lets, &mut wieoft);
    loop {
        let mut neu: Vec<(String, String)> = Vec::new();
        let mut neu_tx: Vec<(String, TypExpr)> = Vec::new();
        for l in &lets {
            let name = &l.name.text;
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
        if neu.is_empty() && neu_tx.is_empty() {
            return;
        }
        for (n, t) in neu_tx {
            lokal.lokaltypexpr.insert(n, t);
        }
        for (n, c) in neu {
            lokal.lokaltyp.insert(n, c);
        }
    }
}

fn funktion(
    f: &FnDecl,
    aus: &mut String,
    rumpf_aus: &mut String,
    u: &Namen,
    absagen: &mut Absagen,
) {
    if matches!(f.klasse, Some(FnKlasse::Spec)) {
        return;
    }
    let eigen = eigene_sicht(f, u);
    let u = &eigen;
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
            None => {
                weigere(absagen, f.name.span, "return type");
                return;
            }
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
            None => {
                weigere(absagen, p.name.span, "parameter type");
                return;
            }
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
                None => {
                    weigere(absagen, f.name.span, "return type");
                    return;
                }
            }
        }
        params.push(format!("{} *_grund", r.text));
    }
    let liste = if params.is_empty() {
        "void".to_string()
    } else {
        params.join(", ")
    };
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
        // **Der Rueckgabewert heisst `result`, und er ist ein AUSGANGSOPERAND** (2026-08-20).
        //
        // Bis dahin weigerte sich der Erzeuger fuer jeden `asm`-Rumpf mit Ergebnis -- und
        // damit war ein Systemaufruf nur halb schreibbar: absetzen ging, die Rueckgabe lesen
        // nicht. *`result` steht als Wort laengst in der Grammatik (`primary`), also braucht
        // es kein neues.*
        let hat_ergebnis = f.ergebnis.is_some();
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
        a2.push_str("}\n");
        return;
    }
    let FnRumpf::Block(b) = &f.rumpf else { return };
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
    let rahmen = Austritt {
        freigaben: Vec::new(),
        rueck_option: match &f.ergebnis {
            Some(TypExpr::Index { tabelle, optional: true, .. }) => Some(tabelle.text.clone()),
            _ => None,
        },
        schleifen: Vec::new(),
        fehlerkanal: f.fehler.is_some(),
    };
    for s in &b.anweisungen {
        anweisung(s, aus, u, absagen, 1, &rahmen);
    }
    aus.push_str("}\n");
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
        ExprArt::FnWert(pfad) => {
            aus.insert(pfad.text());
        }
    }
}

/// Welche Namen liest dieser Rumpf? Nur die Formen, die der Erzeuger ueberhaupt absenkt --
/// jede andere wird ohnehin abgelehnt.
fn benutzte_namen(b: &Block, aus: &mut std::collections::BTreeSet<String>) {
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
            StmtArt::Let(l) => e(&l.wert, aus),
            StmtArt::Sperrt(x) => benutzte_namen(&x.rumpf, aus),
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
            // **Only the value.** The target of a `publishes` is an ATOMIC global -- the
            // lowering looks it up in `u.atomics` and refuses anything else -- so it is
            // neither a parameter (no parameter is an atomic) nor a table. It belongs to
            // neither consumer of this set. The `publishes { … }` payload lands in a
            // comment; the pairing was decided at compile time (V001-V004).
            StmtArt::Publish(p) => e(&p.wert, aus),
            StmtArt::Observiert(o) => benutzte_namen(&o.rumpf, aus),
            StmtArt::Exchange(x) => match &x.form {
                XForm::Update { rumpf, .. } => benutzte_namen(rumpf, aus),
                XForm::Vergleich { wert, bedingung, .. } => {
                    e(wert, aus);
                    pred_namen(bedingung, aus);
                }
            },
            // `let x = place awaits { … }` -- same as `publishes`, from the other side: the
            // source is an atomic global, and the `awaits { … }` list lands in a comment.
            StmtArt::AwaitLoad(_) => {}
            // **`breaking l { … }` has NO lowering at all** -- `anweisung` refuses it by
            // name. Descending into its block would count names that the C never reads, and
            // that is the expensive direction: a parameter read only inside a `breaking`
            // block would lose its `(void)k;` and `cc -Wextra -Werror` would reject the
            // unit. *This catch-all arm was right, and it stays -- with its reason.*
            StmtArt::Bricht(_) => {}
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
                None => ausdruck(&z.wert, u, absagen),
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
                            "a compound assignment to a `format` field -- it would be a read                              and a write through two separate calls, and over a buffer a                              device also writes, whether the two see the same bytes is the                              question itself",
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
                        if let (Some((versatz, breite)), Some((hi, lo, _))) = (lage, bits) {
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
                            let wort =
                                format!("(*(volatile {breite} *)({}{pfeil}basis + {versatz}))", z.ziel.basis.text);
                            aus.push_str(&format!(
                                "{e}{{\n{e}    {breite} _v = {wort};\n\
                                 {e}    {wort} = ({breite})((_v & ({breite})~({breite}){maske}u) \
                                 | (({breite})({wert}) << {lo}u & ({breite}){maske}u));\n{e}}}\n"
                            ));
                            return;
                        }
                    }
                }
            }
            aus.push_str(&format!(
                "{e}{} {} {};\n",
                ort(&z.ziel, u, absagen),
                zuw_op(&z.op),
                wert
            ));
        }
        // **`narrow x to a .. b else { … }` ist die einzige Laufzeitpruefung, die dieser
        // Erzeuger ausgibt** -- und sie steht hier, weil die Sprache sie als Pruefung
        // DEFINIERT, nicht weil M1 versagt haette. *W6 gilt in die andere Richtung: was M1
        // traegt, wird weggelassen; was `narrow` heisst, bleibt stehen.*
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
        StmtArt::Ruf(r) => aus.push_str(&format!("{e}{};\n", ruf(r, u, absagen))),
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
                Some(c) => aus.push_str(&format!(
                    "{e}{c} {} = {};\n",
                    l.name.text,
                    ausdruck(&l.wert, u, absagen)
                )),
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
            let ziel = pb.ziel.text();
            let Some((_, ordnung, _)) = u.atomics.get(&ziel) else {
                weigere(absagen, s.span, "`publishes` on something that is not an atomic");
                return;
            };
            let last = match &pb.nutzlast {
                Nutzlast::Orte(l) => l.iter().map(|x| x.text()).collect::<Vec<_>>().join(", "),
                Nutzlast::Nichts(_) => "nothing".into(),
            };
            aus.push_str(&format!(
                "{e}/* publishes {{ {last} }} -- paired at compile time (V001-V004) */\n\
                 {e}atomic_store_explicit(&{ziel}, {}, {ordnung});\n",
                ausdruck(&pb.wert, u, absagen)
            ));
        }
        StmtArt::AwaitLoad(al) => {
            let quelle = al.quelle.text();
            let Some((typ, _, ordnung)) = u.atomics.get(&quelle) else {
                weigere(absagen, s.span, "`awaits` on something that is not an atomic");
                return;
            };
            let last = al.erwartet.iter().map(|x| x.text()).collect::<Vec<_>>().join(", ");
            aus.push_str(&format!(
                "{e}/* awaits {{ {last} }} -- paired at compile time (V001-V004) */\n\
                 {e}{typ} {} = atomic_load_explicit(&{quelle}, {ordnung});\n",
                al.name.text
            ));
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
            let ziel = x.ort.text();
            let Some((typ, speichern, laden)) = u.atomics.get(&ziel).cloned() else {
                weigere(
                    absagen,
                    s.span,
                    "`exchange` on something that is not a declared `atomic` -- without a \
                     declaration there is no memory ordering, and choosing one would mean \
                     inventing it",
                );
                return;
            };
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
                    // **Die Schranke geht als AUSDRUCK hinaus, nicht als Zahl.** `NKERNE * 4`
                    // steht im Erzeugnis mit `NKERNE` als `#define` daneben -- *wer die
                    // Kernzahl aendert, aendert die Schranke mit*, und niemand muss eine
                    // ausgerechnete Zahl nachziehen.
                    let gaenge = ausdruck(n, u, absagen);
                    let (h, neu_, i) =
                        (format!("_cx{tiefe}"), format!("_cn{tiefe}"), format!("_ci{tiefe}"));
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
            let hat_wert = !sig.geist_rueck;
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
        StmtArt::Bricht(_) => weigere(
            absagen,
            s.span,
            "`breaking I { … }` -- the block is a PROOF region: inside it the invariant is \
             not available as a premise, and at its end it is either restored by \
             construction or booked as an obligation in the manifest. At run time it is \
             nothing but its statements, so the lowering would be a plain block -- and it is \
             not built because no program asks for it: the single corpus site is a poison \
             probe. Emitting the block and dropping the region would make the C look like a \
             program whose obligation nobody carries",
        ),
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
    aus.push_str(&format!(
        "{e}{{\n{e}    uint32_t {z} = 0;\n{e}    while (!({bedingung})) {{\n\
         {e}        if ({z} >= {gaenge}u) {{ {ausgang}(); }}\n{e}        {z}++;\n"
    ));
    for k in &r.rumpf.anweisungen {
        anweisung(k, aus, u, absagen, tiefe + 2, austritt);
    }
    aus.push_str(&format!("{e}    }}\n{e}}}\n"));
}

/// **Ein `static` ueber einem Feld: `static mut kernlast : [Zaehler; 64] = 0;`**
/// (2026-08-20).
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
    a: &ArrayTy,
    aus: &mut String,
    u: &Namen,
    absagen: &mut Absagen,
) {
    let Some(elem) = ctyp(&a.element, u) else {
        weigere(absagen, st.name.span, "`static` array over an unresolvable element type");
        return;
    };
    let Some(n) = konst_zahl(&a.laenge).or_else(|| {
        // Wie bei `count`: eine Zahl ODER ein `const`-Name, und der Wert steht in `konstwert`.
        match &a.laenge.art {
            ExprArt::Ort(o) => u.konstwert.get(&o.text()).copied(),
            _ => None,
        }
    }) else {
        weigere(absagen, st.name.span, "`static` array whose length is not constant");
        return;
    };
    if n <= 0 {
        weigere(absagen, st.name.span, "`static` array of length zero -- C has no such object");
        return;
    }
    let Some(w) = konst_zahl(&st.wert) else {
        weigere(absagen, st.name.span, "`static` array with a non-constant initialiser");
        return;
    };
    let anfang = if w == 0 {
        "{0}".to_string()
    } else {
        format!(
            "{{{}}}",
            std::iter::repeat(w.to_string()).take(n as usize).collect::<Vec<_>>().join(", ")
        )
    };
    let konst = if st.veraenderlich { "" } else { "const " };
    let abschnitt = match &st.section {
        Some(t) => format!(" __attribute__((section(\"{}\")))", t.text),
        None => String::new(),
    };
    aus.push_str(&format!(
        "\nstatic {konst}{elem} {}[{n}]{abschnitt} __attribute__((unused)) = {anfang};\n",
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
                // **Und die fuenfzehn, die ueberhaupt nicht springen -- einzeln.** Der
                // Abstieg darunter kommt von `crate::unterbloecke`, und das erzwingt fuer
                // eine neue `StmtArt` nur die Frage *„traegst du einen Block?"*. Ob sie
                // SPRINGT, fragt es nicht -- und ein neues `goto` waere hier stumm
                // durchgefallen, waehrend `-Wunused-label` dann eine Marke meldet, die sehr
                // wohl angesprungen wird.
                StmtArt::Let(_)
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
                | StmtArt::Ruf(_) => {}
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

/// Ein Praedikat als C-Bedingung. **Nur die Formen, die ein `until` heute braucht** -- jede
/// andere wird abgelehnt, statt sie plausibel zu uebersetzen.
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
fn baumsicht(o: &Ort, u: &Namen, absagen: &mut Absagen) -> Option<(String, String, String)> {
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
    for k in &x.rumpf.anweisungen {
        anweisung(k, aus, u, absagen, tiefe + 1, austritt);
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
        Abstieg::Fallend(_) => {
            weigere(
                absagen,
                s.span,
                "`descendants of … by decreasing` -- a measure over a tree walk is not \
                 decided: which of the two orders it constrains is not written anywhere",
            );
            return;
        }
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
    let rumpf_hin = |aus: &mut String, absagen: &mut Absagen| {
        aus.push_str(&format!("{e}        {{\n{e}            const uint32_t {v} = {k};\n"));
        aus.push_str(&format!("{e}            (void){v};\n"));
        for kk in &x.rumpf.anweisungen {
            anweisung(kk, aus, u, absagen, tiefe + 3, austritt);
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
            let feld = if u.tabellenglobal.contains(&o.basis.text) {
                format!("{}.slots", ort(o, u, absagen))
            } else {
                format!("{}->slots", ort(o, u, absagen))
            };
            let v = &x.variable.text;
            aus.push_str(&format!(
                "{e}for (uint32_t {v} = 0; {v} < (uint32_t)(sizeof({feld}) / sizeof({feld}[0])); {v}++) {{\n"
            ));
            for k in &x.rumpf.anweisungen {
                anweisung(k, aus, u, absagen, tiefe + 1, austritt);
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
            let feld = ort(o, u, absagen);
            let v = &x.variable.text;
            aus.push_str(&format!(
                "{e}for (uint32_t {v} = 0; {v} < (uint32_t)(sizeof({feld}) / sizeof({feld}[0])); {v}++) {{\n"
            ));
            for k in &x.rumpf.anweisungen {
                anweisung(k, aus, u, absagen, tiefe + 1, austritt);
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
        Domaene::Schlange(_) => {
            "`queue` -- «B10»: `traverse` yields no value and knows no `break`, so \
             `by consuming` drains the WHOLE queue; that is a different program"
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
    let gegenstand = ausdruck(&m.gegenstand, u, absagen);
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
    konst_zahl(&a.laenge)
        .or_else(|| match &a.laenge.art {
            ExprArt::Ort(o) => u.konstwert.get(&o.text()).copied(),
            _ => None,
        })
        .and_then(|n| u128::try_from(n).ok())
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
        BinOp::Plus | BinOp::Minus | BinOp::Mal | BinOp::SchiebLinks
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

fn wert_ctyp(e: &Expr, u: &Namen) -> Option<String> {
    match &e.art {
        // **The signature first, the body second** (2026-08-25). A name a declaration knows is
        // answered from the declaration; only a `let`-bound local falls through to
        // `lokaltyp`, which `lokale_lets` filled from declarations as well. *The order is the
        // one `eigene_sicht` states: what a function binds itself comes from its own
        // declaration and from no other.*
        ExprArt::Ort(o) if o.suffixe.is_empty() => match u.parametertyp.get(&o.basis.text) {
            Some(t) => ctyp(t, u),
            None => ort_typ(o, u)
                .and_then(|t| ctyp(&t, u))
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
            // **Und sonst: der erklaerte Rueckgabetyp des Gerufenen.** Er stand die ganze
            // Zeit da; gefragt hat ihn niemand.
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
        ExprArt::Ort(o) if o.suffixe.is_empty() => u
            .parametertyp
            .get(&o.basis.text)
            .is_some_and(|t| ist_geist(t, u)),
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
        | ExprArt::Binaer(_, _, _) => false,
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
            .map(|(m, a)| format!(".{} = {}", m.text, ausdruck(a, u, absagen)))
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
            "`transition` call whose argument is not a handle of THAT device -- the              transition belongs to a declaration, and which one is not a guess",
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

fn ort(o: &Ort, u: &Namen, absagen: &mut Absagen) -> String {
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
        if let Some((versatz, breite)) = dev.and_then(|d| d.reg.get(&f.text)) {
            let wort = format!(
                "(*(volatile {breite} *)({}{pfeil}basis + {versatz}))",
                o.basis.text
            );
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
                        let maske: u128 = if *hi - *lo + 1 >= *breite_bit {
                            u128::MAX >> (128 - breite_bit)
                        } else {
                            (1u128 << (*hi - *lo + 1)) - 1
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
    if let Some(fmt) = u.formatwerte.get(&o.basis.text) {
        if let Some(OrtSuffix::Feld(f)) = o.suffixe.first() {
            if o.suffixe.len() == 1 {
                return format!("{fmt}_{}({})", f.text, o.basis.text);
            }
            weigere(
                absagen,
                f.span,
                "a `format` field followed by more suffixes -- a reader returns a VALUE, and                  a value has no place inside the bytes",
            );
            return String::new();
        }
    }
    // **Ein `accumulates` wird beim LESEN gefaltet.** Der Name steht fuer den ganzen
    // Zellenblock, nicht fuer eine Zelle -- ein blanker Zugriff waere ein Zugriff auf etwas,
    // das es im C nicht gibt.
    if o.suffixe.is_empty() && u.akkus.contains(&o.basis.text) {
        return format!("{}_lies()", o.basis.text);
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
/// Ohne Suffix, also ein `double`-Literal. Trifft es auf ein `float`, wandelt C um.
fn gleitkommatext(bits: u64) -> String {
    let w = f64::from_bits(bits);
    let t = format!("{w:?}");
    if t.contains('.') || t.contains('e') || t.contains("inf") || t.contains("NaN") {
        t
    } else {
        format!("{t}.0")
    }
}

fn ausdruck(e: &Expr, u: &Namen, absagen: &mut Absagen) -> String {
    match &e.art {
        ExprArt::Zahl(n) => n.to_string(),
        ExprArt::Gleitkomma { bits, .. } => gleitkommatext(*bits),
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
        ExprArt::FnWert(p) => format!(
            "&{}",
            p.teile.last().map(|i| i.text.clone()).unwrap_or_default()
        ),
        // **`R::F` wird `R_F`** (Stufe 7, 2026-08-21) -- genau der Name, den
        // `ItemArt::Reason` weiter oben in sein `typedef enum` schreibt. *Die zwei Stellen
        // muessen dieselbe Regel benutzen, sonst erzeugt der Uebersetzer einen Namen, den
        // er selbst nicht deklariert hat* -- `cc` faengt das, aber erst am Ende.
        ExprArt::Grund { grund, fall } => format!("{}_{}", grund.text, fall.text),
        ExprArt::Klammer(x) => format!("({})", ausdruck(x, u, absagen)),
        ExprArt::Binaer(op, a, b) => {
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
                let (breite, vz) = crate::umgebung::breite_von(i.wort);
                let rechenwort = if breite <= 32 { "uint32_t" } else { "uint64_t" };
                let zurueck = format!("{}int{}_t", if vz { "" } else { "u" }, breite);
                return format!(
                    "({zurueck})(({rechenwort})({}) {} ({rechenwort})({}))",
                    ausdruck(a, u, absagen),
                    op_text(op),
                    ausdruck(b, u, absagen)
                );
            }
            format!("{} {} {}", ausdruck(a, u, absagen), op_text(op), ausdruck(b, u, absagen))
        }
        ExprArt::Ruf(r) => ruf(r, u, absagen),
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

fn op_text(op: &BinOp) -> &'static str {
    match op {
        BinOp::Plus => "+",
        BinOp::Minus => "-",
        BinOp::Mal => "*",
        BinOp::Geteilt => "/",
        BinOp::Rest => "%",
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
/// `__typeof__` steht da, damit die Signatur **nicht zweimal** geschrieben wird: sie einmal
/// aus der Deklaration abzuleiten und hier ein zweites Mal auszuschreiben waere das zweite
/// Register ueber derselben Sache (W7) -- *und ein Register, das sich widersprechen kann,
/// widerspricht sich.*
fn bezugnahme(marke: &str, ziel: &str) -> String {
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

/// `it.feld` wird `Format_feld(it)`. **Ein anderer Grundname als `it` ist keine Absenkung,
/// sondern ein Missverstaendnis** -- der Knoteneintrag ist das einzige, worueber `down when`
/// und `leaf` reden, und wer etwas anderes nennt, bekommt eine Absage statt einer Vermutung.
fn ausdruck_eintrag(e: &Expr, fmt: &str, u: &Namen, absagen: &mut Absagen) -> Option<String> {
    Some(match &e.art {
        ExprArt::Ort(o) if o.basis.text == "it" && o.suffixe.len() == 1 => {
            let OrtSuffix::Feld(f) = &o.suffixe[0] else { return None };
            format!("{fmt}_{}(it)", f.text)
        }
        ExprArt::Klammer(x) => format!("({})", ausdruck_eintrag(x, fmt, u, absagen)?),
        ExprArt::Unaer(UnOp::Nicht, x) => {
            format!("!({})", ausdruck_eintrag(x, fmt, u, absagen)?)
        }
        ExprArt::Binaer(op, a, b) => format!(
            "{} {} {}",
            ausdruck_eintrag(a, fmt, u, absagen)?,
            op_text(op),
            ausdruck_eintrag(b, fmt, u, absagen)?
        ),
        ExprArt::Zahl(_) | ExprArt::Wahr | ExprArt::Falsch => ausdruck(e, u, absagen),
        _ => return None,
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
    let Some(ebenen) = konst_zahl(&w.ebenen) else {
        weigere(
            absagen,
            w.span,
            "`walk … levels` that is not a number -- the descent's step count IS the \
             declaration's one statement about the run, and it cannot be guessed",
        );
        return;
    };
    let Some(weite) = konst_zahl(&w.knoten.laenge) else {
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
    let Some(ab_wenn) = pred_c_eintrag(&w.ab_wenn, &elem, u, absagen) else {
        weigere(absagen, w.span, "`walk … down … when` predicate form");
        return;
    };
    let Some(blatt) = pred_c_eintrag(&w.blatt, &elem, u, absagen) else {
        weigere(absagen, w.span, "`walk … leaf` predicate form");
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
        aus.push_str(&format!(
            " * invariant {} runs {laeuft} -- COMPILE TIME (W6), not re-checked here{}\n",
            kommentartext(&i.name.text),
            if nennt_abbildungen(&i.pred) {
                ";\n *   it quantifies over `mappings of`, whose bound is an open finding\n\
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
        "\nstatic inline bool {n}_ist_blatt(const {elem} *it) {{ return (bool)({blatt}); }}\n"
    ));
    aus.push_str(&format!(
        "static inline bool {n}_steigt_ab(const {elem} *it) {{ return (bool)({ab_wenn}); }}\n"
    ));
    // **Der Abstieg. `levels` ist die Schranke, und sie steht als Zahl da.**
    aus.push_str(&format!(
        "\nstatic inline bool {n}_absteigen(const {n}_knoten *wurzel, const uint32_t *index,\n\
         \x20       bool (*knoten_zu)(uint64_t, const {n}_knoten **), const {elem} **blatt) {{\n\
         \x20   const {n}_knoten *k = wurzel;\n\
         \x20   for (uint32_t e = 0; e < {n}_EBENEN; e++) {{\n\
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
fn eintritt(e: &EntryDecl, aus: &mut String, ruempfe: &BTreeSet<String>, absagen: &mut Absagen) {
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
        aus.push_str(&bezugnahme(&format!("gabbro_eintritt_{n}_verteiler"), &ziel));
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
                    aus.push_str(&bezugnahme(&format!("gabbro_boot_{n}_s{}", i + 1), &ziel));
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
        aus.push_str(&bezugnahme(&format!("gabbro_boot_{n}_dispatch"), &ziel));
    } else {
        aus.push_str(&format!(
            "/* dispatch `{}`: not declared in this unit, so there is nothing here to bind it\n\
             \x20* to. `N006` holds it against the declarations; this file cannot. */\n",
            kommentartext(&b.dispatch.text())
        ));
    }
}
