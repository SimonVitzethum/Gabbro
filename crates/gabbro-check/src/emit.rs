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
#[derive(Default)]
struct Namen {
    tabellen: Vec<String>,
    /// Die `format`-Namen. Ein Pfad, der eines nennt, IST der Zugriffsverbund.
    formate: BTreeSet<String>,
    /// Je Geraet: der Raum und seine Register. **Ein Registerzugriff ist KEIN Feldzugriff**
    /// -- siehe `geraet`.
    geraete: HashMap<String, Geraet>,
    /// Name -> Geraetetyp, **global und konservativ**: wird derselbe Name irgendwo mit einem
    /// anderen Typ erklaert, faellt er heraus. Dieselbe Bauart wie `vorzeichenlos` -- Unwissen
    /// faellt nach lautstark, dann weigert sich der Registerzugriff.
    geraetezeiger: HashMap<String, String>,
    /// Name -> Tabelle, fuer Zeigerparameter. Konservativ wie `geraetezeiger`.
    tabellenzeiger: HashMap<String, String>,
    /// (Tabelle, Slotfeld) -> Zieltabelle, fuer `option index into T`-Felder. **Ohne das
    /// weiss der Erzeuger bei `x = None` nicht, WELCHER Sonderwert gemeint ist.**
    optionfeld: HashMap<(String, String), String>,
    /// Je Tabelle ihr aufgeloester `count`-Wert. **Der Sonderwert haengt daran** -- siehe
    /// `beweise/Option_Sonderwert.thy`, M-1.
    kapazitaet: HashMap<String, i128>,
    typen: HashMap<String, TypExpr>,
    /// **Die Verbundtypen: Name -> Felderliste in Deklarationsreihenfolge** («B7»).
    /// Sie werden zu einem C-`typedef struct`, und ihr Konstruktor zu einem
    /// zusammengesetzten Literal. *`fs` aus `beweise/Verbund_Konstruktor.thy`.*
    verbunde: BTreeSet<String>,
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
    /// `linear ghost type BootPhase;` — a value that **does not exist at run time**.
    geister: Vec<String>,
    funktionen: HashMap<String, Signatur>,
    /// Namen, die diese Einheit **nicht deklariert** und die nur hinter einem Zeiger
    /// vorkommen. Sie werden als unvollstaendiger C-Typ vorwaerts deklariert.
    fremde: BTreeSet<String>,
    /// Je `retry` (an seinem Spannenanfang): die **Zahl der Durchgaenge**, die sein
    /// Operationsbudget hergibt. Siehe `retry_schranken`.
    retry_schranke: HashMap<u32, i128>,
    /// Die `const`-Namen -- in einer `where`-Klausel ist ein blanker Name sonst ein FELD.
    konstanten: BTreeSet<String>,
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
            StmtArt::Let(l) if l.typ.as_ref().is_some_and(|t| ist_verbund(t)) => {
                aus.push(l.name.text.clone())
            }
            StmtArt::Wenn(w) => {
                for (_, r) in &w.zweige {
                    verbundlokale(r, u, aus);
                }
                if let Some(r) = &w.sonst {
                    verbundlokale(r, u, aus);
                }
            }
            StmtArt::Match(m) => {
                for z in &m.zweige {
                    verbundlokale(&z.rumpf, u, aus);
                }
            }
            StmtArt::Bricht(x) => verbundlokale(&x.rumpf, u, aus),
            StmtArt::Sperrt(x) => verbundlokale(&x.rumpf, u, aus),
            StmtArt::Narrow(x) => verbundlokale(&x.sonst, u, aus),
            StmtArt::LetSonst(x) => verbundlokale(&x.sonst, u, aus),
            StmtArt::Schleife(sch) => match sch.as_ref() {
                Schleife::Traverse(t) => verbundlokale(&t.rumpf, u, aus),
                Schleife::Retry(r) => verbundlokale(&r.rumpf, u, aus),
                Schleife::Forever(f) => verbundlokale(&f.rumpf, u, aus),
            },
            _ => {}
        }
    }
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
struct Signatur {
    /// Per parameter: is it a ghost? A ghost argument is dropped from the C call.
    geist_param: Vec<bool>,
    /// Does it return a ghost? Then `let x = f(…)` loses its binding, **not its call**.
    geist_rueck: bool,
    /// Returns `option index into T`? Then the table name, for the sentinel comparison.
    option_rueck: Option<String>,
    /// `-> never`. Ein `on_exceeded` darf nur auf so eine Funktion zeigen.
    nie_rueck: bool,
}

/// Ein Geraet, so wie der Erzeuger es braucht.
struct Geraet {
    /// Registername -> (Versatz, C-Wortbreite). **Der Raum steht nicht hier** -- `geraet`
    /// liest ihn direkt aus dem Baum, und ein zweites Feld daneben waere das zweite Register
    /// ueber derselben Sache (W7).
    reg: HashMap<String, (i128, String)>,
    /// Registername -> Feldname -> (hoechstes Bit, niedrigstes Bit, Registerbreite in Bit).
    felder: HashMap<String, HashMap<String, (u32, u32, u32)>>,
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
";

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
                Geraet { reg: HashMap::new(), felder: HashMap::new() },
            );
        }
        ItemArt::Tabelle(t) => namen.tabellen.push(t.name.text.clone()),
        ItemArt::Accumulates(ac) => {
            namen.akkus.insert(ac.name.text.clone());
        }
        ItemArt::Atomic(a) => {
            // (Speichern, Laden) -- die Deklaration nennt die Speicherseite.
            let (sp, ld) = match a.ordnung {
                Some(Ordnung::Release) => ("memory_order_release", "memory_order_acquire"),
                Some(Ordnung::Acquire) => ("memory_order_release", "memory_order_acquire"),
                Some(Ordnung::Seq) => ("memory_order_seq_cst", "memory_order_seq_cst"),
                _ => ("memory_order_relaxed", "memory_order_relaxed"),
            };
            namen.atomics.insert(a.name.text.clone(), (String::new(), sp, ld));
        }
        ItemArt::Typ(t) => {
            // **A ghost type has no body and no C.** `linear ghost type BootPhase;` declares a
            // value the checker threads and the machine never sees.
            if t.ghost {
                namen.geister.push(t.name.text.clone());
            } else if let Some(unter) = &t.rumpf {
                if matches!(unter, TypExpr::Verbund(f, _) if !f.is_empty()) && !t.opaque {
                    namen.verbunde.insert(t.name.text.clone());
                }
                namen.typen.insert(t.name.text.clone(), unter.clone());
            }
        }
        _ => {}
    });
    // **Second pass, and it needs the first**: whether a parameter is a ghost can only be
    // decided once the ghost names are known.
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Funktion(f) = &item.art {
            let sig = Signatur {
                geist_param: f.parameter.iter().map(|p| ist_geist(&p.typ, &namen)).collect(),
                geist_rueck: f.ergebnis.as_ref().is_some_and(|t| ist_geist(t, &namen)),
                nie_rueck: matches!(f.ergebnis, Some(TypExpr::Never(_))),
                option_rueck: match &f.ergebnis {
                    Some(TypExpr::Index { tabelle, optional: true, .. }) => {
                        Some(tabelle.text.clone())
                    }
                    _ => None,
                },
            };
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
        });
    }

    {
        let umg = crate::umgebung::Umgebung::sammle(baum);
        crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
            if let ItemArt::Device(d) = &item.art {
                let mut reg = HashMap::new();
                let mut felder: HashMap<String, HashMap<String, (u32, u32, u32)>> =
                    HashMap::new();
                for r in &d.register {
                    if let Some(v) = umg.konst_wert(modul, &r.versatz) {
                        reg.insert(r.name.text.clone(), (v, intty(&r.typ)));
                    }
                    let breite = breite_von(&r.typ) * 8;
                    let mut f = HashMap::new();
                    for (name, lage) in &r.felder {
                        let (hi, lo) = match lage {
                            BitPos::Bit(b) => (*b as u32, *b as u32),
                            BitPos::Bereich(h, l) => (*h as u32, *l as u32),
                        };
                        f.insert(name.text.clone(), (hi, lo, breite));
                    }
                    felder.insert(r.name.text.clone(), f);
                }
                if let Some(g) = namen.geraete.get_mut(&d.name.text) {
                    g.reg = reg;
                    g.felder = felder;
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

    // Optionfelder und Tabellenzeiger -- fuer `x = None`.
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Tabelle(tb) = &item.art {
            if let Some(slot) = &tb.slot {
                for f in &slot.felder {
                    if let SlotTyp::Typ(TypExpr::Index { tabelle, optional: true, .. }) = &f.typ {
                        namen.optionfeld.insert(
                            (tb.name.text.clone(), f.name.text.clone()),
                            tabelle.text.clone(),
                        );
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

    namen.retry_schranke = retry_schranken(baum);

    // **Die Wortleser werden MITERZEUGT, nicht vorausgesetzt** -- ein Erzeugnis, das eine
    // Bibliothek braucht, ist kein Erzeugnis. Und nur die gebrauchten: eine ungenutzte
    // Funktion im erzeugten C ist ein Befund ueber den Erzeuger.
    let mut leser: BTreeSet<&'static str> = BTreeSet::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Format(f) = &item.art {
            let gross = matches!(f.endian, Some(Endian::Gross));
            for feld in &f.felder {
                if let TypExpr::Int(i) = &feld.typ.typ {
                    leser.insert(lesewort(breite_von(i), gross));
                }
            }
        }
    });

    let mut aus = String::from(KOPF);
    let annahmen = crate::manifest::sammle(baum);
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
            aus.push_str(&format!(" *   {} ({}): {}\n", a.name, a.art, wie));
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
    crate::fuer_jedes_item(baum, &mut |item| match &item.art {
        ItemArt::Konst(k) => {
            if let Some(w) = konst_zahl(&k.wert) {
                aus.push_str(&format!("\n#define {} {}u\n", k.name.text, w));
            } else {
                weigere(absagen, k.name.span, "const with a non-constant value");
            }
        }
        // Range types lower to their carrier (see `ctyp`); a **record** gets a C struct.
        ItemArt::Typ(t) => {
            if namen.verbunde.contains(&t.name.text) {
                verbund(t, &mut aus, &namen, absagen);
            }
        }
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
            let Some(c) = ctyp(&st.typ, &namen) else {
                weigere(absagen, st.name.span, "`static` of an unresolvable type");
                return;
            };
            let Some(w) = konst_zahl(&st.wert) else {
                weigere(absagen, st.name.span, "`static` with a non-constant initialiser");
                return;
            };
            let konst = if st.veraenderlich { "" } else { "const " };
            let abschnitt = match &st.section {
                Some(t) => format!(" __attribute__((section(\"{}\")))", t.text),
                None => String::new(),
            };
            aus.push_str(&format!(
                "\nstatic {konst}{c} {}{abschnitt} = {w};\n",
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
                 \x20* the price of the lowering, not an inaccuracy. */\n\
                 static _Atomic {c} {nm}_zellen[{n}];\n\
                 \n\
                 static {c} {nm}_lies(void) {{\n\
                 \x20   {c} z = ({c}){neutral};\n\
                 \x20   for (uint32_t k = 0; k < (uint32_t)({n}); k++) {{\n\
                 \x20       {c} v = atomic_load_explicit(&{nm}_zellen[k], memory_order_relaxed);\n\
                 \x20       {falte}\n\
                 \x20   }}\n\
                 \x20   return {ab}z;\n\
                 }}\n\
                 \n\
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
        ItemArt::Assume(_) | ItemArt::Axiom(_) => {}
        ItemArt::Modul(_) | ItemArt::Use(_) => {}
        _ => weigere(
            absagen,
            item.span,
            "this item kind has no lowering in this emitter yet",
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
        match &s.art {
            StmtArt::Schleife(sch) => {
                if let Schleife::Retry(r) = sch.as_ref() {
                    let budget = crate::umgebung::Umgebung::sammle(baum)
                        .konst_wert(modul, &r.schranke);
                    let je_gang =
                        crate::kosten::durchgangskosten(baum, modul, r, HashMap::new());
                    if let (Some(n), Some(c)) = (budget, je_gang) {
                        if c > 0 && n / c > 0 {
                            aus.insert(r.span.von, n / c);
                        }
                    }
                    sammle_retry(baum, modul, &r.rumpf, aus);
                }
            }
            StmtArt::Sperrt(x) => sammle_retry(baum, modul, &x.rumpf, aus),
            StmtArt::Match(m) => {
                for z in &m.zweige {
                    sammle_retry(baum, modul, &z.rumpf, aus);
                }
            }
            StmtArt::Narrow(n) => sammle_retry(baum, modul, &n.sonst, aus),
            _ => {}
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
        match ctyp(&f.typ.typ, u) {
            Some(c) => aus.push_str(&format!("    {c} {};\n", f.name.text)),
            None => weigere(absagen, f.name.span, "field type"),
        }
    }
    aus.push_str(&format!("}} {};\n", t.name.text));
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
fn geraet(d: &Device, aus: &mut String, u: &Namen, absagen: &mut Absagen) {
    let _ = u;
    if !matches!(d.raum, Raum::Mmio) {
        weigere(
            absagen,
            d.span,
            "`device … at dma`/`at normal` -- which barrier a `dma` access needs is a \
             statement about the memory model (the same axiom layer as pairing), and the \
             checker does not build it either",
        );
        return;
    }
    // **«B24» an seiner eigenen Stelle:** eine Bitlage muss INNERHALB der erklaerten
    // Registerbreite liegen. Der Befund des Ordners redet ueber Lagen jenseits von 64 in
    // einem `format`; hier ist die Breite erklaert, also ist die Frage entscheidbar -- und
    // eine Lage, die herausragt, ist ein Fehler, kein offener Punkt.
    for r in &d.register {
        let breite = breite_von(&r.typ) * 8;
        for (name, lage) in &r.felder {
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

    aus.push_str(&format!(
        "\ntypedef struct {{ volatile uint8_t *basis; }} {};\n",
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
    let lage = ausdruck_geraet(&b.basis, d, u, absagen);
    if lage.is_empty() {
        weigere(absagen, b.span, "`bank` base that is not computed from this device's fields");
        return;
    }
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
    }
}

/// Ein Ausdruck ueber Feldern DIESES Geraets -- fuer die berechnete Banklage.
fn ausdruck_geraet(e: &Expr, d: &Device, u: &Namen, absagen: &mut Absagen) -> String {
    match &e.art {
        ExprArt::Zahl(n) => n.to_string(),
        ExprArt::Klammer(x) => format!("({})", ausdruck_geraet(x, d, u, absagen)),
        ExprArt::Binaer(op, a, b) => format!(
            "{} {} {}",
            ausdruck_geraet(a, d, u, absagen),
            op_text(op),
            ausdruck_geraet(b, d, u, absagen)
        ),
        // `CAP.FRO` -- ein Feld dieses Geraets, gelesen ueber `d`.
        ExprArt::Ort(o) if o.suffixe.len() == 1 => {
            let Some(g) = u.geraete.get(&d.name.text) else { return String::new() };
            let Some((versatz, breite)) = g.reg.get(&o.basis.text) else { return String::new() };
            let OrtSuffix::Feld(f) = &o.suffixe[0] else { return String::new() };
            let Some((hi, lo, _)) = g.felder.get(&o.basis.text).and_then(|m| m.get(&f.text))
            else {
                return String::new();
            };
            let maske: u128 = (1u128 << (hi - lo + 1)) - 1;
            format!("(((*(volatile {breite} *)(d->basis + {versatz})) >> {lo}) & {maske}u)")
        }
        _ => {
            let _ = absagen;
            String::new()
        }
    }
}

/// **`check` -- die Probe wird eine Funktion, ihre Behauptung ein Kommentar.**
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
        c.name.text, c.claim.text
    ));
    for g in &c.gates {
        rumpf_aus.push_str(&format!(" * gates: {}\n", g.text));
    }
    if let Some((was, erwartet)) = &c.counterprobe {
        // **Die Gegenprobe ist die Zeile, die die Probe erst zu einer macht** -- sie sagt,
        // wie die Probe ROT werden koennte. Eine Probe ohne sie ist eine Zusage.
        rumpf_aus.push_str(&format!(
            " * counterprobe: \"{}\" expects {}\n",
            was.text, erwartet.text
        ));
    }
    rumpf_aus.push_str(" */\n");
    rumpf_aus.push_str(&format!("bool pruefe_{}(void) {{\n", c.name.text));
    for s in &c.can_fail.anweisungen {
        anweisung(s, rumpf_aus, u, absagen, 1, &Vec::new());
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

    // Welche Bits aendert dieser Zug, und auf welchen Wert? Ueber ALLE Schritte veroderrt.
    let mut geaendert: u128 = 0;
    let mut neu: u128 = 0;
    for s in &x.schritte {
        let (g2, n2) = match schrittbits(s, felder, absagen) {
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
        None => match bitwort(&s.nach, felder) {
            Some(n) => Some((n, n)),
            None => {
                weigere(absagen, s.span, "`transition` target that is not a set of field names");
                None
            }
        },
        _ => {
            weigere(absagen, s.span, "`transition` on an indexed place");
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
        "\ntypedef struct {{ const uint8_t *bytes; uint32_t len; }} {n};\n"
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
        if feld.typ.embeds.is_some() {
            weigere(absagen, feld.span, "`embeds` in a `format` -- that is a pointer form");
            return;
        }
        let TypExpr::Int(i) = &feld.typ.typ else {
            weigere(absagen, feld.span, "`format` field type");
            return;
        };
        let breite = match i.wort {
            gabbro_syntax::kw::Kw::U8 | gabbro_syntax::kw::Kw::I8 => 1u32,
            gabbro_syntax::kw::Kw::U16 | gabbro_syntax::kw::Kw::I16 => 2,
            gabbro_syntax::kw::Kw::U32 | gabbro_syntax::kw::Kw::I32 => 4,
            _ => 8,
        };
        let c = intty(i);
        let leser = lesewort(breite, gross);

        if feld.bitpos.is_none() {
            if !feld.reserviert {
                aus.push_str(&format!(
                    "static inline {c} {n}_{f2}(const {n} *v) {{ return ({c}){leser}(v->bytes + {versatz}); }}\n",
                    f2 = feld.name.text
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

        // **Eine Bitgruppe: alle folgenden Felder mit Lage, gleicher Breite, ein Wort.**
        let bits = breite * 8;
        let mut belegt: u64 = 0;
        let mut gruppe = Vec::new();
        while i_feld < f.felder.len() {
            let g = &f.felder[i_feld];
            let Some(bp) = &g.bitpos else { break };
            let TypExpr::Int(gi) = &g.typ.typ else { break };
            if intty(gi) != c {
                break;
            }
            let (hi, lo) = match bp {
                BitPos::Bit(b) => (*b, *b),
                BitPos::Bereich(h, l) => (*h, *l),
            };
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
                continue;
            }
            let maske: u128 = if hi - lo + 1 >= 64 {
                u64::MAX as u128
            } else {
                (1u128 << (hi - lo + 1)) - 1
            };
            aus.push_str(&format!(
                "static inline {c} {n}_{f2}(const {n} *v) {{ \
                 return ({c})((({c}){leser}(v->bytes + {versatz}) >> {lo}) & {maske}u); }}\n",
                f2 = g.name.text
            ));
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
        _ => return None,
    })
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
        _ => ausdruck(e, u, absagen),
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
fn ctyp(t: &TypExpr, u: &Namen) -> Option<String> {
    match t {
        TypExpr::Int(i) => Some(intty(i)),
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
    let mut params = Vec::new();
    for p in &f.parameter {
        if ist_geist(&p.typ, u) {
            continue; // erased -- see above
        }
        match ctyp(&p.typ, u) {
            Some(c) => {
                let luecke = if c.ends_with('*') { "" } else { " " };
                params.push(format!("{c}{luecke}{}", p.name.text))
            }
            None => {
                weigere(absagen, p.name.span, "parameter type");
                return;
            }
        }
    }
    let liste = if params.is_empty() {
        "void".to_string()
    } else {
        params.join(", ")
    };
    // Der Prototyp steht IMMER oben -- auch fuer eine Funktion mit Rumpf.
    aus.push_str(&format!("\n{rueck} {}({liste});\n", f.name.text));
    let FnRumpf::Block(b) = &f.rumpf else { return };
    let aus = rumpf_aus;
    aus.push_str(&format!("\n{rueck} {}({liste}) {{\n", f.name.text));
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
    for s in &b.anweisungen {
        anweisung(s, aus, u, absagen, 1, &Vec::new());
    }
    aus.push_str("}\n");
}

/// Die Namen in einem Praedikat -- ein `until` liest ebenso wie ein Rumpf.
fn pred_namen(p: &Pred, aus: &mut std::collections::BTreeSet<String>) {
    match &p.art {
        PredArt::Vergleich(e) | PredArt::Element(e, _) => sammle_expr_namen(e, aus),
        PredArt::Klammer(x) | PredArt::Nicht(x) => pred_namen(x, aus),
        PredArt::Und(a, b) | PredArt::Oder(a, b) => {
            pred_namen(a, aus);
            pred_namen(b, aus);
        }
        _ => {}
    }
}

fn sammle_expr_namen(x: &Expr, aus: &mut std::collections::BTreeSet<String>) {
    match &x.art {
        ExprArt::Ort(o) => {
            aus.insert(o.basis.text.clone());
        }
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
        _ => {}
    }
}

/// Welche Namen liest dieser Rumpf? Nur die Formen, die der Erzeuger ueberhaupt absenkt --
/// jede andere wird ohnehin abgelehnt.
fn benutzte_namen(b: &Block, aus: &mut std::collections::BTreeSet<String>) {
    fn e(x: &Expr, aus: &mut std::collections::BTreeSet<String>) {
        match &x.art {
            ExprArt::Ort(o) => o_(o, aus),
            ExprArt::Klammer(y) | ExprArt::Unaer(_, y) => e(y, aus),
            ExprArt::Binaer(_, a, c) => {
                e(a, aus);
                e(c, aus);
            }
            ExprArt::Ruf(r) => {
                for a in &r.argumente {
                    e(a, aus);
                }
            }
            _ => {}
        }
    }
    fn o_(o: &Ort, aus: &mut std::collections::BTreeSet<String>) {
        aus.insert(o.basis.text.clone());
        for s in &o.suffixe {
            if let OrtSuffix::Index(x) = s {
                e(x, aus);
            }
        }
    }
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Return(Some(x)) => e(x, aus),
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
            _ => {}
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
type Austritt = Vec<String>;

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
            for freigabe in austritt.iter().rev() {
                aus.push_str(&format!("{e}{freigabe};\n"));
            }
            match w {
                Some(x) => aus.push_str(&format!("{e}return {};\n", ausdruck(x, u, absagen))),
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
                Some(tab) => match &z.wert.art {
                    // `None` kommt als Ruf ohne Argumente an -- es IST ein Konstruktor.
                    ExprArt::Ruf(r) if r.pfad.teile.last().is_some_and(|i| i.text == "None") => {
                        format!("{tab}_NONE")
                    }
                    ExprArt::Ort(o) if o.suffixe.is_empty() && o.basis.text == "None" => {
                        format!("{tab}_NONE")
                    }
                    ExprArt::Ruf(r) if r.pfad.teile.last().is_some_and(|i| i.text == "Some") => {
                        match r.argumente.first() {
                            Some(a) => ausdruck(a, u, absagen),
                            None => {
                                weigere(absagen, s.span, "`Some` without an argument");
                                return;
                            }
                        }
                    }
                    _ => ausdruck(&z.wert, u, absagen),
                },
                None => ausdruck(&z.wert, u, absagen),
            };
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
            // **«F»: `narrow … to finite` senkt NICHT ab.** Der Erzeuger traegt heute keine
            // Gleitkommaform, und er weigert sich benannt, statt etwas Plausibles zu
            // schreiben -- dieselbe Haltung wie bei `entrust`.
            let NarrowZiel::Bereich(bereich) = &n.ziel else {
                weigere(absagen, n.ort.basis.span, "`narrow … to finite` (Gleitkomma)");
                return;
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
            let bedingung = if untere_ist_null && vorzeichenlos.contains(&n.ort.basis.text) {
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
            match l.typ.as_ref().and_then(|t| ctyp(t, u)) {
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
        StmtArt::Sperrt(x) => {
            let name = x.sperre.text();
            let (nimm, gib) = if x.geteilt {
                (format!("{name}_nimm_geteilt()"), format!("{name}_gib_geteilt()"))
            } else {
                (format!("{name}_nimm()"), format!("{name}_gib()"))
            };
            aus.push_str(&format!("{e}{nimm};\n{e}{{\n"));
            let mut innen = austritt.clone();
            innen.push(gib.clone());
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
            // **`forever` wird ABGELEHNT, und der Grund ist ein Befund des Ordners selbst.**
            //
            // `per_pass bounded N ops` ist eine Aussage ueber EINEN Durchgang, und die
            // rechnet der Kostenpass zur UEBERSETZUNGSZEIT nach. Zur Laufzeit gibt es
            // deshalb nichts zu zaehlen -- **und damit hat `on_exceeded` keinen Ausloeser.**
            //
            // > *`MESSUNGEN.md` nennt das seit dem 2026-08-14 einen Ritus* (**„`per_pass
            // > bounded n cycles` ist ein Ritus"**). Die Absenkung bestaetigt den Befund an
            // > der Maschine: die Klausel liesse sich nur weglassen, und **eine Klausel still
            // > fallenzulassen ist genau das, was dieser Erzeuger nicht tut.**
            //
            // Dazu «B11»: `forever` hat ueberhaupt keinen Ausgang. Beides gehoert entschieden,
            // bevor hier eine Zeile C entsteht.
            Schleife::Forever(_) => weigere(
                absagen,
                s.span,
                "`forever` -- `per_pass … ops` is a COMPILE-TIME claim, so `on_exceeded` has \
                 no runtime trigger, and dropping the clause would discard it silently \
                 (MESSUNGEN.md: \"a ritual\"); «B11»: there is no exit either",
            ),
        },
        _ => weigere(absagen, s.span, "statement kind"),
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

/// Ein Praedikat als C-Bedingung. **Nur die Formen, die ein `until` heute braucht** -- jede
/// andere wird abgelehnt, statt sie plausibel zu uebersetzen.
fn pred_c(p: &Pred, u: &Namen, absagen: &mut Absagen) -> Option<String> {
    Some(match &p.art {
        PredArt::Vergleich(e) => ausdruck(e, u, absagen),
        PredArt::Klammer(x) => format!("({})", pred_c(x, u, absagen)?),
        PredArt::Nicht(x) => format!("!({})", pred_c(x, u, absagen)?),
        PredArt::Und(a, b) => format!("{} && {}", pred_c(a, u, absagen)?, pred_c(b, u, absagen)?),
        PredArt::Oder(a, b) => format!("{} || {}", pred_c(a, u, absagen)?, pred_c(b, u, absagen)?),
        _ => return None,
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
            if !matches!(x.abstieg, Abstieg::Unbesucht) {
                weigere(
                    absagen,
                    s.span,
                    "`slots of … by consuming`/`by decreasing` -- the witness ordering is a \
                     proof device; what it means for the run is not decided",
                );
                return;
            }
            let feld = format!("{}->slots", ort(o, u, absagen));
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
        Domaene::NachfahrenVon(_) => {
            "`descendants of` -- the domain does not name the EDGE it walks. `CapSpace` \
             carries four candidates (parent, first_child, next_sibling, prev_sibling), and \
             `chain(a, b) in` shows the grammar already knows how to name one. That is an \
             asymmetry in the grammar, not missing emitter code"
        }
        Domaene::VorfahrenVon(_) => "`ancestors of` -- the same as `descendants of`: the edge is not named",
        Domaene::Schlange(_) => {
            "`queue` -- «B10»: `traverse` yields no value and knows no `break`, so \
             `by consuming` drains the WHOLE queue; that is a different program"
        }
        Domaene::ElementeVon(_) => {
            "`elems of` -- «B12» is open: whether it binds an ELEMENT or an INDEX is used \
             both ways in the specification and fixed nowhere"
        }
        // **UND HIER STEHT KEIN BAUPOSTEN, SONDERN EIN FEHLER IM KOSTENPASS** (2026-08-17).
        //
        // `SPRACHE.md`:786 sagt: *„`mappings of` quantifies over ALL reachable leaf entries
        // of a `walk` structure."* Der Kostenpass rechnet dafuer `walkschranken` =
        // **Ebenen mal Knotenlaenge** (`umgebung.rs`, `kosten.rs`:362) -- bei vier Ebenen zu
        // 512 Eintraegen also **2 048**.
        //
        // > **Die Zahl der erreichbaren Blaetter ist 512^4 = 68 719 476 736.** Sieben
        // > Groessenordnungen. *Der Pass zaehlt EINEN Abstiegspfad und nennt es die Domaene.*
        //
        // **Das ist dieselbe Klasse, die dieser Ordner zweimal bezahlt hat** -- `revoke` sagte
        // 200 ops zu und kostet 16 452 480, A4 sagte 4 096 zu und kostet 831 488. Beide Male
        // war es ein MENSCH, der den typischen Fall statt der Schranke schrieb, und der Pass
        // hat es gefangen. **Hier ist es der Pass selbst.**
        //
        // Absenken hiesse, die kleinere der beiden Lesarten still zu waehlen.
        Domaene::AbbildungenVon(_) => {
            "`mappings of` -- SPRACHE.md:786 says it quantifies over ALL reachable leaf \
             entries, but the cost pass bounds it at levels x node length (2048 for a \
             four-level table of 512), while the leaves number 512^4. **Seven orders of \
             magnitude**, and lowering it would silently pick the smaller reading"
        }
        Domaene::KetteIn { .. } => "`chain in` -- the sibling chain needs its own bound",
        Domaene::FelderVon(_) => "`fields of` -- a register field list is not a runtime domain",
        Domaene::Threads => "`threads` -- the thread set is not declared in a translation unit",
    };
    weigere(absagen, s.span, grund);
}

/// Nur `match` ueber einer Option wird abgesenkt. **Ein `match` ueber einem `tagged type` ist
/// eine eigene Entwurfsfrage** (markierter Verbund, Variantennummern, Nutzlast) und wird
/// abgelehnt statt geraten.
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

/// Ist dieser Ort ein `option index into T`-Feld? Dann die Zieltabelle.
///
/// Erkannt wird die Form `<zeiger>.slots[<i>].<feld>` -- die einzige, in der ein Slotfeld
/// ueberhaupt vorkommt. **Alles andere liefert `None`, und dann weigert sich der Erzeuger**
/// statt einen Sonderwert zu raten.
fn option_ziel(o: &Ort, u: &Namen) -> Option<String> {
    let tab = u.tabellenzeiger.get(&o.basis.text)?;
    let OrtSuffix::Feld(feld) = o.suffixe.last()? else { return None };
    u.optionfeld.get(&(tab.clone(), feld.text.clone())).cloned()
}

/// Liefert den Tabellennamen, wenn dieser Ausdruck ein `option index into T` ist.
fn option_quelle(e: &Expr, u: &Namen) -> Option<String> {
    match &e.art {
        ExprArt::Ruf(r) => u
            .funktionen
            .get(&r.pfad.teile.last()?.text)?
            .option_rueck
            .clone(),
        _ => None,
    }
}

/// Does this expression yield a ghost? Today: a call to a function with a ghost return.
fn geist_wert(e: &Expr, u: &Namen) -> bool {
    match &e.art {
        ExprArt::Ruf(r) => r
            .pfad
            .teile
            .last()
            .and_then(|i| u.funktionen.get(&i.text))
            .is_some_and(|s| s.geist_rueck),
        _ => false,
    }
}

/// **A call, with the ghost arguments dropped.** The positions come from the callee's
/// signature; an unknown callee keeps every argument, which cannot compile silently — it
/// fails at `cc`, and that is the direction to fail in.
fn ruf(r: &Ruf, u: &Namen, absagen: &mut Absagen) -> String {
    let name = r.pfad.teile.last().map(|i| i.text.clone()).unwrap_or_default();
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
    // **Ein Geraeteregister ist kein Feld, sondern ein volatiler Zugriff an `basis + Versatz`.**
    // Der C-Uebersetzer darf ihn nicht wegoptimieren, und `volatile` ist die eine Stelle, an
    // der die Absenkung ihm etwas VERBIETEN muss.
    if let (Some(g), Some(OrtSuffix::Feld(f))) =
        (u.geraetezeiger.get(&o.basis.text), o.suffixe.first())
    {
        if let Some((versatz, breite)) = u.geraete.get(g).and_then(|d| d.reg.get(&f.text)) {
            let wort = format!(
                "(*(volatile {breite} *)({}->basis + {versatz}))",
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
                        u.geraete.get(g).and_then(|d| d.felder.get(&f.text)).and_then(|m| m.get(&feld.text))
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
fn ausdruck(e: &Expr, u: &Namen, absagen: &mut Absagen) -> String {
    match &e.art {
        ExprArt::Zahl(n) => n.to_string(),
        ExprArt::Wahr => "true".into(),
        ExprArt::Falsch => "false".into(),
        ExprArt::Ort(o) => ort(o, u, absagen),
        ExprArt::Klammer(x) => format!("({})", ausdruck(x, u, absagen)),
        ExprArt::Binaer(op, a, b) => {
            format!("{} {} {}", ausdruck(a, u, absagen), op_text(op), ausdruck(b, u, absagen))
        }
        ExprArt::Ruf(r) => ruf(r, u, absagen),
        _ => {
            weigere(absagen, e.span, "expression form");
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
