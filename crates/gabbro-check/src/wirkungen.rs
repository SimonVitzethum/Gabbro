//! **Pass 8 -- `effects`, und der Grund, warum dieser Pass ueberhaupt existiert.**
//!
//! `SPRACHE.md` §7 und `SYNTAX.md` §6:
//!
//! > **`effects` ist NICHT fail-open.** Eine Funktion **ohne** `effects` ist ein
//! > Uebersetzungsfehler; wer nichts anfasst, schreibt `effects { pure }`. Die frueher
//! > moegliche Auslassung war zugleich **die staerkste Zusage und die kuerzeste
//! > Spezifikation** -- der Anreiz stand gegen die Vollstaendigkeit.
//!
//! Genau deshalb faellt die Pflicht **an der Abwesenheit**, nicht am Inhalt: der Parser laesst
//! die Klausel weg, wenn sie fehlt, und dieser Pass sieht das Loch. Ein Werkzeug, das eine
//! fehlende Klausel als „keine Wirkungen" liest, belohnt das Weglassen.

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};
use gabbro_syntax::span::Span;

pub fn pass(baum: &Programm, absagen: &mut Absagen) {
    // **Der Aufrufgraph, seit 2026-08-15.** Ohne ihn deckte eine `effects`-Liste nur die
    // ERSTE Ebene: `effects { pure }` galt fuer eine Funktion, die eine schreibende rief.
    // Damit war „nur die eingetragene Logik ist aktiv" eine halbe Aussage, und die
    // Klempnerei-Klasse *Rahmen* hing genau daran.
    let g = crate::aufrufgraph::erhebe(baum);
    // **Eine Konstante ist kein Weltzustand.** `const GRENZE: u32 = 1000000;` steht zur
    // Uebersetzungszeit fest; sie zu lesen ist kein Zugriff, sondern eine Zahl. Ohne diese
    // Ausnahme waere `pure` praktisch unerreichbar -- die erste Fassung von `E010` meldete
    // `v1_erhoehen liest GRENZE, erklaert aber pure` und hatte damit recht im Wortlaut und
    // unrecht in der Sache.
    //
    // **Und die Umkehrung derselben Einsicht, gefunden am Korpus:** `E010` spricht nur ueber
    // **bekannten Weltzustand** -- `static`, `atomic`, `table`, `device`, `state`. Der erste
    // Lauf meldete `IpcResult.Ok` (eine Variante, kein Ort) und `MAX_SECTORS` (ein Name, den
    // ein AUSSCHNITT gar nicht deklariert) als ungenannte Lesungen. Beides sind keine
    // Wirkungen, und beide Meldungen waeren Laerm gewesen, der die echten zudeckt.
    //
    // *Verloren geht dabei nichts:* in einer vollstaendigen Uebersetzungseinheit muss jeder
    // Name aufloesen -- ein unbekannter faellt bereits im Namenspass. Die Einschraenkung
    // kostet also nur im Ausschnitt, und dort ist sie richtig.
    let mut konstanten: Vec<String> = Vec::new();
    let mut weltnamen: Vec<String> = Vec::new();
    crate::fuer_jedes_item(baum, &mut |item| match &item.art {
        ItemArt::Konst(k) => konstanten.push(k.name.text.clone()),
        ItemArt::Statisch(x) => weltnamen.push(x.name.text.clone()),
        ItemArt::Atomic(x) => weltnamen.push(x.name.text.clone()),
        ItemArt::Tabelle(x) => weltnamen.push(x.name.text.clone()),
        ItemArt::Device(x) => weltnamen.push(x.name.text.clone()),
        ItemArt::State(x) => weltnamen.push(x.name.text.clone()),
        _ => {}
    });
    // **E220/E221 need the whole program before any function:** whether a carrier is
    // read-only is a statement about every function, so the writer set is computed
    // once here and handed to each function -- computed beside `konstanten`/
    // `weltnamen` for the same reason (one register, read at one place).
    let schreiber = schreiber_des_programms(baum, &weltnamen);
    // **Lane 191: the derivation every omitted clause draws on.** An omitted
    // `effects` is no longer an error where the body fixpoint settles — it is
    // the derived clause, checked exactly like a written one. Where the
    // fixpoint stays a lower bound, the omission stays a refusal (`N305`).
    let ab = crate::ableitung::leite_ab(baum, true);
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| match &item.art {
        ItemArt::Funktion(f) => {
            funktion(f, modul, &g, &konstanten, &weltnamen, &schreiber, &ab, absagen)
        }
        ItemArt::Axiom(a) => rein_allein(&a.effects, absagen),
        ItemArt::Check(c) => probenrumpf(c, modul, &g, absagen),
        _ => {}
    });
    footprint_against_guards(baum, &g, &konstanten, &weltnamen, &schreiber, absagen);
}

/// **The `can_fail` body carries an implicit contract, and it is `pure`** (2026-08-25).
///
/// This pass walked `ItemArt::Funktion` and nothing else. The same call therefore gave two
/// different answers:
///
/// ```gabbro
/// extern fn teuer() -> u32 in 0 .. 100 effects { writes zaehler } costs <= 5000 ops;
///
/// impl fn f() -> bool …  { let g = teuer(); … }         -- E008 + K001
/// check probe { … can_fail { let g = teuer(); … } … }   -- 0 errors
/// ```
///
/// `N027` already forbids the STATEMENT forms in a probe body -- assignment, `locks`,
/// `publishes`, `exchange` -- and states the principle this continues:
/// *„a body without a contract may not do what needs one."*
/// **A CALL was not covered by it**, and so the whole effect space stood open again.
///
/// > **And it closes more than the effects.** `consumes` is an effect; a call carrying it
/// > falls here. No linear value can be consumed in a probe body any more -- the
/// > `nimm(m); nimm(m);` that M2 does not see there has become unwritable. *The same
/// > construction as `N036`: a pass relying on a refusal one pass earlier.*
///
/// No new code: it is the same sentence as in an `impl fn`, only with a contract that is
/// not written down but holds. What stays allowed is exactly what the corpus does --
/// `pure` and `reads`.
fn probenrumpf(c: &Check, modul: &str, g: &crate::aufrufgraph::Graph, absagen: &mut Absagen) {
    // **What the probe body MADE ITSELF** (2026-08-26, narrowed).
    //
    // The rule as first written refused every effect that was not `reads` or `pure` -- and
    // it was **wider than its ground**. Measured at `messung/fragmente/F06.gab`: a
    // calibration probe writes a pattern into a stack it obtained inside its own body and
    // then measures how deep the touch went. *A calibration that writes nothing calibrates
    // nothing.*
    //
    // The ground of the rule is **not** „a probe may not write" but *„a probe may not change
    // what it OBSERVES"* -- that is what makes `consumes` in a probe body a double free with
    // a green tick, and it is why `N027` bars assignment and `locks` there.
    //
    // > A value bound by `let` inside the probe body is not observed by anything outside it.
    // > **Writing through it changes nothing the claim speaks about.**
    //
    // So: an effect `writes X` is tolerated when `X` is a PARAMETER NAME of the callee and
    // the argument in that position is a name the probe body bound itself. Everything else
    // -- a world name, a parameter of the enclosing unit, `consumes` in any position --
    // still falls. *The narrowing is the smallest one the measured case needs.*
    let mut eigene: std::collections::BTreeSet<String> = Default::default();
    sammle_lets_im_block(&c.can_fail, &mut eigene);
    let mut rufe: Vec<&Ruf> = Vec::new();
    sammle_rufe_im_block(&c.can_fail, &mut rufe);
    for r in rufe {
        let Some(pfad) = r.path() else { continue };
        let Some(name) = pfad.teile.last() else { continue };
        let h = g.huelle(&g.schluessel_von(modul, &name.text));
        let params = g.parameter(&g.schluessel_von(modul, &name.text));
        // Is this `writes X` about something the body made itself?
        let auf_eigenem = |w: &str| -> bool {
            let Some(ort) = w.strip_prefix("writes ") else { return false };
            let Some(i) = params.iter().position(|p| p == ort) else { return false };
            matches!(r.argumente.get(i).map(|a| &a.art),
                     Some(ExprArt::Ort(o)) if o.suffixe.is_empty() && eigene.contains(&o.basis.text))
        };
        let unrein: Vec<&str> = h
            .wirkungen
            .iter()
            .filter(|w| !w.starts_with("reads ") && w.as_str() != "pure" && !auf_eigenem(w))
            .map(|w| w.as_str())
            .collect();
        if unrein.is_empty() {
            continue;
        }
        absagen.schiebe(
            Absage::fehler(
                "E008",
                name.span,
                format!(
                    "`check {}` is `pure` by construction but calls something with `{}`",
                    c.name.text,
                    unrein.join("`, `")
                ),
            )
            .mit_notiz(
                "a `check` carries no `effects`, no `costs` and no `locks` -- so its body may read, \
                 compute, compare and return, and nothing else",
            )
            .mit_notiz(
                "`N027` says the same about statements: a body without a contract may not do what \
                 needs one",
            ),
        );
    }
}

/// **Every name the block BINDS ITSELF** -- and only those, not the parameters of the unit
/// around it. *That is the whole distinction the narrowed `E008` rests on: what a probe made
/// itself is not what a probe observes.*
fn sammle_lets_im_block(b: &Block, aus: &mut std::collections::BTreeSet<String>) {
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Let(l) => {
                aus.insert(l.name.text.clone());
            }
            StmtArt::LetSonst(l) => {
                aus.insert(l.name.text.clone());
            }
            // **«E4»:** the bound index is made here, not observed.
            StmtArt::Alloc(a) => {
                aus.insert(a.name.text.clone());
            }
            _ => {}
        }
        for k in crate::unterbloecke(s) {
            sammle_lets_im_block(k, aus);
        }
    }
}

/// Every call in the block, over the exhaustive walkers from `lib.rs` -- a call in index
/// position is a call too.
fn sammle_rufe_im_block<'a>(b: &'a Block, aus: &mut Vec<&'a Ruf>) {
    for s in &b.anweisungen {
        if let StmtArt::Ruf(r) = &s.art {
            aus.push(r);
        }
        for e in crate::eigene_ausdruecke(s) {
            for x in crate::alle_ausdruecke(e) {
                if let ExprArt::Ruf(r) = &x.art {
                    aus.push(r);
                }
            }
        }
        for k in crate::unterbloecke(s) {
            sammle_rufe_im_block(k, aus);
        }
    }
}

/// Was ein Rumpf tut -- Ort und Fundstelle je Tat.
/// Die **lokalen** Namen eines Rumpfes: alles, was `let` einfuehrt, plus die Laufvariablen
/// der Schleifen. **Ein Schreibzugriff auf einen lokalen Namen ist keine Wirkung.**
///
/// `effects` beschreibt, was eine Funktion mit der WELT tut, nicht mit ihrem eigenen Stapel.
/// Bis 2026-08-15 verlangte `E005` fuer `let mut i = 0; i += 1;` einen Eintrag in der
/// Wirkungsliste -- eine Funktion, die nur zaehlt, konnte nicht `pure` sein. Gefunden am
/// Fragmentlauf (`FRAGMENTE.md`, kstackmark), wo genau das aufschlug.
fn lokale(b: &Block, aus: &mut Vec<String>) {
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Let(l) => aus.push(l.name.text.clone()),
            StmtArt::LetSonst(l) => aus.push(l.name.text.clone()),
            // **«E4»:** an arena index lives on the stack like any `let`.
            StmtArt::Alloc(a) => aus.push(a.name.text.clone()),
            StmtArt::AwaitLoad(a) => aus.push(a.name.text.clone()),
            StmtArt::Exchange(e) => {
                aus.push(e.name.text.clone());
                // Der Binder von `update(v)` ist der ALTE Wert -- ein Name des Rumpfes,
                // keine Stelle der Welt.
                if let XForm::Update { binder, .. } = &e.form {
                    aus.push(binder.text.clone());
                }
            }
            StmtArt::Match(m) => {
                for z in &m.zweige {
                    // **Der Binder eines `match`-Zweiges ist ein lokaler Name**, und dass er
                    // hier gefehlt hat, war eine Luecke mit zwei Gesichtern: `E010` meldete
                    // ihn beim ersten Lauf als Weltzustand, und `E005` haette dasselbe fuer
                    // ein `Some(p) => { p.feld = … }` getan. **Die Lesehaelfte hat einen
                    // Fehler der SCHREIBhaelfte aufgedeckt** -- gefunden erst, weil Binder
                    // fast immer gelesen und fast nie geschrieben werden.
                    if let Some(bi) = &z.binder {
                        aus.push(bi.text.clone());
                    }
                }
            }
            StmtArt::Schleife(sch) => {
                if let Schleife::Traverse(x) = sch.as_ref() {
                    aus.push(x.variable.text.clone());
                }
            }
            _ => {}
        }
        for k in crate::unterbloecke(s) {
            lokale(k, aus);
        }
    }
}

#[derive(Default)]
struct Taten {
    schreibt: Vec<(String, Span)>,
    /// **Lesart A (2026-08-16).** Jedes Lesen eines nicht-lokalen Ortes. Die Entscheidung
    /// steht in `TODO.md`, der Preis daneben: A laesst 10 von 32 Fragmentfunktionen fallen,
    /// die gruebere Lesart C nur drei. **A ist die Lesart, deren Verletzung dieser Pass
    /// PRAEZISE melden kann** -- welche Funktion welchen Ort ungenannt liest; C koennte nur
    /// *„irgendwo ausserhalb von `mmio`/`dma`/`atomic`"* sagen. *Was man nicht genau melden
    /// kann, setzt kein Pass durch* -- dieselbe Begruendung, an der Lesart B gestorben ist.
    liest: Vec<(String, Span)>,
    /// Ort, Fundstelle, und **ob geteilt genommen** -- die Richtung ist nicht symmetrisch.
    sperrt: Vec<(String, Span, bool)>,
}

/// Der Kopf eines Ortes, so wie eine Wirkung ihn nennt: `c.slots[s].benutzt` wird von
/// `writes c.slots` gedeckt, also zaehlt jeder Praefix.
fn deckt(erklaert: &str, getan: &str) -> bool {
    getan == erklaert
        || getan.starts_with(erklaert)
            && matches!(
                getan.as_bytes().get(erklaert.len()).copied(),
                Some(b'.') | Some(b'[') | Some(b'-')
            )
}

/// Jedes Lesen eines Ortes in einem Ausdruck. **Der Index ist selbst ein Lesen** --
/// `c.slots[i]` liest `c.slots` *und* `i`; der lokale Anteil faellt spaeter am Grundnamen weg.
fn liest_expr(e: &Expr, t: &mut Taten) {
    match &e.art {
        ExprArt::Ort(o) => {
            t.liest.push((o.text(), o.span));
            for suf in &o.suffixe {
                if let OrtSuffix::Index(ix) = suf {
                    liest_expr(ix, t);
                }
            }
        }
        ExprArt::Klammer(x) | ExprArt::Unaer(_, x) => liest_expr(x, t),
        ExprArt::Binaer(_, a, b) => {
            liest_expr(a, t);
            liest_expr(b, t);
        }
        ExprArt::Ruf(r) => {
            for a in &r.argumente {
                liest_expr(a, t);
            }
        }
        // **Lane E1:** the arguments of a library call are evaluated, so
        // they read like any call's; the region is raw tokens, not
        // expressions, and reads nothing.
        ExprArt::LibraryCall(r) => {
            for a in &r.args {
                liest_expr(a, t);
            }
        }
        // **«SG-24»** -- the counted predicate runs, so it reads: same decision
        // as `geteilt.rs::orte_in`, beside the same `aligned` precedent. Missing
        // it would let a `count` over a carrier pass under `effects { pure }`.
        // The domain reads too (`domaene_liest`, same as at `traverse`): walking
        // a carrier's slots touches the carrier, even where the rumpf only
        // counts.
        ExprArt::Zaehle {
            domaene, rumpf, ..
        } => {
            domaene_liest(domaene, t);
            for e in crate::ausdruecke_im_praedikat(rumpf) {
                liest_expr(e, t);
            }
        }

        // **`aligned(p, n)` READS `p`, and until 2026-09-01 no pass saw it.** `Eingebaut` was
        // missing from the enumeration, so the whole subtree fell under the catch-all -- the
        // places inside it with everything else. Measured, both directions:
        //
        // ```text
        // if g == 4           under effects { pure }  ->  E010
        // if aligned(g, 4)    under effects { pure }  ->  0 errors
        // if wert == 4        outside its lock        ->  H007
        // if aligned(wert, 4) outside its lock        ->  0 errors
        // ```
        //
        // **Decided per form, with the reason beside it** -- not by a walker that answers the
        // question silently:
        //
        // * `aligned(a, b)` evaluates BOTH expressions at run time. Both are reads.
        // * `lenof`/`sizeof` over a place take their value from the DECLARATION, not from the
        //   content -- the emitter says so itself (`C001`: *"the length would have to come
        //   from somewhere other than the declaration, and there is no such place"*). So the
        //   place is NOT a read. **Its indices are**: `lenof(c.slots[i])` evaluates `i`.
        // * over a TYPE nothing is read at all.
        ExprArt::Eingebaut(g) => match &**g {
            gabbro_syntax::ast::Eingebaut::Aligned(a, b) => {
                liest_expr(a, t);
                liest_expr(b, t);
            }
            gabbro_syntax::ast::Eingebaut::Sizeof(x)
            | gabbro_syntax::ast::Eingebaut::Lenof(x) => {
                if let gabbro_syntax::ast::TypOderOrt::Ort(o) = x {
                    for suf in &o.suffixe {
                        if let OrtSuffix::Index(ix) = suf {
                            liest_expr(ix, t);
                        }
                    }
                }
            }
        },
        _ => {}
    }
}

/// Ein **Schreib**ziel liest seine Indizes mit: `c.slots[naechster] = x` liest `naechster`.
/// Der Ort selbst wird geschrieben, nicht gelesen.
fn ziel_indizes(o: &Ort, t: &mut Taten) {
    for suf in &o.suffixe {
        if let OrtSuffix::Index(ix) = suf {
            liest_expr(ix, t);
        }
    }
}

/// **Read sites of a body, through the E010 walk -- and nothing else.**
///
/// Lane 151 (`D267`, reads): the owner pass needs the same reads `E010` holds
/// against the `effects`, not a second, parallel walk over the body -- two
/// walks over one body drift apart (the `observes` lesson at
/// `aufrufgraph::sammle_rufe`). So this runs the very `sammle_taten` above
/// and returns its `liest` leg: every `(text, span)` the walk counts as a
/// read, with the same coverage (indices, `await`, `narrow`, exchange,
/// traverse domains) and the same blindness (whatever `liest_expr` does not
/// see, neither reader sees).
pub(crate) fn lese_orte(b: &Block) -> Vec<(String, Span)> {
    let mut t = Taten::default();
    sammle_taten(b, &mut t);
    t.liest
}

fn sammle_taten(b: &Block, t: &mut Taten) {
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Zuweisung(z) => {
                t.schreibt.push((z.ziel.text(), z.ziel.span));
                ziel_indizes(&z.ziel, t);
                liest_expr(&z.wert, t);
            }
            StmtArt::Publish(p) => {
                t.schreibt.push((p.ziel.text(), p.ziel.span));
                ziel_indizes(&p.ziel, t);
                liest_expr(&p.wert, t);
            }
            StmtArt::Let(l) => liest_expr(&l.wert, t),
            // **«E4»:** an allocation stores the value and takes a slot --
            // the arena is written, and the value is read. A reset moves
            // the used counter back to zero -- the arena is written, and
            // nothing is read. Both need `writes A` in the effects, like
            // any other store to a carrier.
            StmtArt::Alloc(a) => {
                t.schreibt.push((a.tisch.text.clone(), s.span));
                liest_expr(&a.wert, t);
            }
            StmtArt::ResetArena(tisch) => {
                t.schreibt.push((tisch.text.clone(), s.span));
            }
            StmtArt::Return(Some(x)) => liest_expr(x, t),
            StmtArt::Ruf(r) => {
                for a in &r.argumente {
                    liest_expr(a, t);
                }
            }
            // **Lane E1:** same as above, at the statement form.
            StmtArt::LibraryCall(r) => {
                for a in &r.args {
                    liest_expr(a, t);
                }
            }
            // **Ein `awaits`-Laden IST ein Lesen**, und zwar das gefaehrlichste: es liest
            // eine Nutzlast, die ein anderer Kern geschrieben hat.
            StmtArt::AwaitLoad(a) => t.liest.push((a.quelle.text(), a.quelle.span)),
            StmtArt::Exchange(e) => {
                t.schreibt.push((e.ort.text(), e.ort.span));
                t.liest.push((e.ort.text(), e.ort.span));
            }
            StmtArt::Sperrt(l) => t.sperrt.push((l.sperre.text(), l.sperre.span, l.geteilt)),
            StmtArt::Wenn(w) => {
                for (bed, _) in &w.zweige {
                    liest_expr(bed, t);
                }
            }
            StmtArt::Match(m) => liest_expr(&m.gegenstand, t),
            StmtArt::Narrow(x) => t.liest.push((x.ort.text(), x.ort.span)),
            StmtArt::Schleife(sch) => {
                // Eine `traverse` mit `touches` traegt ihre eigene Wirkungsliste; sie muss
                // trotzdem von der Funktion gedeckt sein, also zaehlt der Rumpf mit.
                // **Die Domaene selbst wird gelesen** -- `slots of c` liest `c`.
                if let Schleife::Traverse(x) = sch.as_ref() {
                    domaene_liest(&x.domaene, t);
                }
            }
            _ => {}
        }
        for k in crate::unterbloecke(s) {
            sammle_taten(k, t);
        }
    }
}

/// **Der Rumpfabgleich.** Bis zum 2026-08-14 pruefte dieser Pass nur die DEKLARATION --
/// Anwesenheit, `pure` allein, `diverges`. Ein `effects { pure }` ueber einer Funktion, die
/// schreibt, kam durch, und damit war die Zusage *„`effects` ist nicht fail-open"* auf ihrer
/// wichtigsten Haelfte leer: sie erzwang eine Liste, nicht ihre Wahrheit.
///
/// **Was hier geprueft wird und was nicht:** jedes **Schreiben** und jedes **`locks`** muss
/// von einer erklaerten Wirkung gedeckt sein. **Lesen wird nicht geprueft** — `FRAGMENTE.md`
/// liest in jeder Funktion Stellen, die keine `reads`-Zeile nennt, und ob das ein Befund ist
/// oder die gemeinte Bedeutung, entscheidet nicht dieser Pass. **Aufrufwirkungen ebenso
/// nicht:** dazu muessten die Wirkungen des Gerufenen auf die Argumente des Aufrufers
/// abgebildet werden, und das ist ein eigener Posten.
/// **`E011` -- `touches` wird gegen den Rumpf gehalten («NL.2.2», 2026-08-19).**
///
/// `pruefe-klauseln.py` fuehrte `touches` als ZUSAGE mit dem Satz *„die Wirkungsmenge eines
/// `traverse`; deklariert, nie gegen den Rumpf gehalten."* Gemessen am selben Tag:
///
/// ```gabbro
/// traverse i over slots of w by unvisited
///     touches reads w.slots
/// { fremd = 1; }              -- 0 Fehler
/// ```
///
/// ## Warum die Zeile ueberhaupt dasteht, wenn `effects` sie schon deckt
///
/// Die `effects` der Funktion decken den ganzen Rumpf, Schleifen eingeschlossen. `touches`
/// ist die **engere, oertliche** Zusage: *diese Traversierung fasst genau DAS an.* Sie ist
/// die Grundlage der Kostenrechnung und der Sperrargumente -- und sie war bis heute
/// unverbindlich.
///
/// > **Eine engere Zusage, die niemand haelt, ist schlimmer als keine:** wer sie liest,
/// > rechnet mit weniger Beruehrung, als der Rumpf hat.
///
/// **Gedeckt wird `writes` und `reads` gegen die genannten Orte**, mit derselben `deckt`
/// -Funktion wie `E005`/`E010`. *Konstanten und lokale Namen zaehlen nicht* -- dieselbe
/// Ausnahme, aus demselben Grund.
fn traverse_gegen_touches(
    b: &Block,
    fname: &str,
    konstanten: &[String],
    weltnamen: &[String],
    absagen: &mut Absagen,
) {
    for s in &b.anweisungen {
        if let StmtArt::Schleife(sch) = &s.art {
            if let Schleife::Traverse(t) = sch.as_ref() {
                if let Some(w) = &t.touches {
                    pruefe_touches(t, w, fname, konstanten, weltnamen, absagen);
                }
            }
        }
        let unter = crate::unterbloecke(s);
        for u in unter {
            traverse_gegen_touches(u, fname, konstanten, weltnamen, absagen);
        }
    }
}

fn pruefe_touches(
    t: &Traverse,
    w: &Wirkungen,
    fname: &str,
    konstanten: &[String],
    weltnamen: &[String],
    absagen: &mut Absagen,
) {
    let mut taten = Taten::default();
    sammle_taten(&t.rumpf, &mut taten);
    let schreibt: Vec<String> = w
        .liste
        .iter()
        .filter_map(|e| match &e.art {
            WirkungArt::Schreibt(o) | WirkungArt::Verbraucht(o) | WirkungArt::Veroeffentlicht(o) => {
                Some(o.text())
            }
            _ => None,
        })
        .collect();
    let liest: Vec<String> = w
        .liste
        .iter()
        .filter_map(|e| match &e.art {
            WirkungArt::Liest(o) => Some(o.text()),
            WirkungArt::Schreibt(o) => Some(o.text()), // schreiben deckt lesen
            _ => None,
        })
        .collect();
    let bekannt = |o: &String| {
        !konstanten.iter().any(|k| k == o)
            && weltnamen
                .iter()
                .any(|n| o == n || o.starts_with(&format!("{n}.")) || o.starts_with(&format!("{n}[")))
    };
    let mut gemeldet: Vec<String> = Vec::new();
    for (ort, span) in taten.schreibt.iter().chain(taten.liest.iter()) {
        if !bekannt(ort) || gemeldet.contains(ort) {
            continue;
        }
        let schreibend = taten.schreibt.iter().any(|(o, _)| o == ort);
        let gedeckt = if schreibend {
            schreibt.iter().any(|e| deckt(e, ort))
        } else {
            liest.iter().any(|e| deckt(e, ort))
        };
        if gedeckt {
            continue;
        }
        gemeldet.push(ort.clone());
        // Lane 187: the loop names the missing entry -- `writes` where the body
        // writes, `reads` where it only reads -- so the repair is unique. The
        // `touches` line carries no braces, hence a plain append at its end.
        let entry =
            if schreibend { format!("writes {ort}") } else { format!("reads {ort}") };
        absagen.schiebe(
            Absage::fehler(
                "E011",
                *span,
                format!(
                    "`{ort}` is touched by this `traverse` in `{fname}` but stands in no `touches` effect"
                ),
            )
            .mit_notiz(
                "`touches` is the NARROWER, local promise beside `effects` -- whoever \
                    reads it counts on less contact than the body has",
            )
            .mit_fix(crate::fix::append_item(w.span.bis, entry)),
        );
    }
}

/// **What the BODY does, written as an effect list -- and not as a refusal.**
///
/// «A4» asks: can the compiler COMPUTE the caller's `effects` line instead of demanding
/// it? This function is one half of the answer -- the body's direct deeds. The other is
/// `aufrufgraph::huelle_der_gerufenen`.
///
/// **It filters by exactly the same rules as `rumpf_gegen_wirkungen`**, and that is not
/// convenience but the condition under which the measurement means anything: a computed
/// list that filters differently from the pass checking the written one measures the
/// difference between two filters, not between two lists. *W7 -- two registers over the
/// same thing.*
///
/// Local names drop (stack, not world), parameters drop when READ (they belong to the
/// caller), constants drop, and only a known world name counts as read. **When WRITING
/// only the local drops** -- exactly the asymmetry `E005` has against `E010`.
/// **The same computation, but WITH the reads over parameters and over names this unit
/// does not declare.**
///
/// `E010` leaves both out, and with a reason: *"a parameter is no world state"* (what the
/// caller hands in, HIS `effects` cover), and *"no known world state -- the pass says
/// nothing"* (an excerpt does not declare everything).
///
/// **For «A4» that is precisely the question.** An elaborator that WRITES the line must
/// write `reads p.slots` -- the caller wants to know what happens to his pointer. *The
/// difference between the two sets is therefore not an imprecision but the measurement: it
/// says how much work still lies between the pass that CHECKS it and the elaborator that
/// would WRITE it.*
pub fn rumpfwirkungen_mit(
    f: &FnDecl,
    b: &Block,
    konstanten: &[String],
    weltnamen: &[String],
    weit: bool,
) -> std::collections::BTreeSet<String> {
    rumpfwirkungen_mit_ort(f, b, konstanten, weltnamen, weit)
        .into_keys()
        .collect()
}

/// **The same set, but each effect with the SPAN of the deed that produced it.**
///
/// The derivation (`ableitung.rs`) has to answer *"where does this effect come from?"* --
/// and the honest answer for the body's own half is a line of that body.
///
/// > It is a wrapper and not a copy **on purpose.** Two functions that both decide what
/// > counts as an effect are two registers over the same thing (`W7`), and the one that
/// > nobody reads drifts. *The filter lives here once; `rumpfwirkungen_mit` throws the
/// > spans away and keeps the set.*
///
/// A `BTreeMap` and not a list: the same place may be touched twice, and the effect is one.
/// **The FIRST deed wins** -- the earliest line in the body is the one a reader wants
/// pointed at.
pub fn rumpfwirkungen_mit_ort(
    f: &FnDecl,
    b: &Block,
    konstanten: &[String],
    weltnamen: &[String],
    weit: bool,
) -> std::collections::BTreeMap<String, Span> {
    let mut taten = Taten::default();
    sammle_taten(b, &mut taten);
    let mut lok = Vec::new();
    lokale(b, &mut lok);
    let mut aus: std::collections::BTreeMap<String, Span> = Default::default();
    let grund = |o: &str| o.split(['.', '[', '-']).next().unwrap_or(o).to_string();

    for (ort, sp) in &taten.schreibt {
        if lok.iter().any(|l| l == &grund(ort)) {
            continue;
        }
        aus.entry(format!("writes {ort}")).or_insert(*sp);
    }
    for (ort, sp) in &taten.liest {
        let gr = grund(ort);
        if lok.iter().any(|l| l == &gr) || konstanten.iter().any(|k| k == &gr) {
            continue;
        }
        let ist_parameter = f.parameter.iter().any(|p| p.name.text == gr);
        if !weit && (ist_parameter || !weltnamen.iter().any(|k| k == &gr)) {
            continue;
        }
        // **Even `weit` keeps ONE boundary: reading the VALUE of a parameter is no
        // effect.** `f(n : u32) { return n + 1; }` touches nothing -- `n` sits in a
        // register. Only a suffix makes it a memory access: `p.slots[i]` goes through the
        // pointer the caller handed over, and THAT is what he wants to see in the line.
        //
        // *Without this line `reads n` stood in the computed list of every function with a
        // numeric parameter* -- and the comparison measured register allocation instead of
        // the frame.
        if weit && ist_parameter && ort == &gr {
            continue;
        }
        aus.entry(format!("reads {ort}")).or_insert(*sp);
    }
    for (ort, sp, geteilt) in &taten.sperrt {
        aus.entry(if *geteilt {
            format!("locks shared {ort}")
        } else {
            format!("locks {ort}")
        })
        .or_insert(*sp);
    }
    aus
}

/// The world names and constants of a unit -- **read off at the same place as in `pass`**,
/// so that no two lists arise that can drift apart.
pub fn welt_und_konstanten(baum: &Programm) -> (Vec<String>, Vec<String>) {
    let mut konstanten: Vec<String> = Vec::new();
    let mut weltnamen: Vec<String> = Vec::new();
    crate::fuer_jedes_item(baum, &mut |item| match &item.art {
        ItemArt::Konst(k) => konstanten.push(k.name.text.clone()),
        ItemArt::Statisch(x) => weltnamen.push(x.name.text.clone()),
        ItemArt::Atomic(x) => weltnamen.push(x.name.text.clone()),
        ItemArt::Tabelle(x) => weltnamen.push(x.name.text.clone()),
        ItemArt::Device(x) => weltnamen.push(x.name.text.clone()),
        ItemArt::State(x) => weltnamen.push(x.name.text.clone()),
        _ => {}
    });
    (konstanten, weltnamen)
}

/// **Does a declared effect cover a performed one?** Public because «A4» asks the same
/// question as `E005`/`E010` -- and it must get the same answer.
pub fn deckt_wirkung(erklaert: &str, getan: &str) -> bool {
    // The verbs must agree, the place may be a prefix.
    let (ve, oe) = trenne(erklaert);
    let (vg, og) = trenne(getan);
    ve == vg && deckt(oe, og)
}

/// `writes a.b` -> (`writes`, `a.b`). `locks shared X` -> (`locks shared`, `X`).
/// `pure`/`diverges` have no place.
/// `pub(crate)`: lane 191 reads the same split in `ableitung.rs`
/// (`deckungsluecke`) — one splitter for the derived line, not two (W7).
pub(crate) fn trenne(w: &str) -> (&str, &str) {
    for v in ["locks shared ", "reads ", "writes ", "locks ", "masks ", "allocs ",
              "consumes ", "publishes "] {
        if let Some(r) = w.strip_prefix(v) {
            return (v.trim_end(), r);
        }
    }
    (w, "")
}

fn rumpf_gegen_wirkungen(
    f: &FnDecl,
    w: &Wirkungen,
    b: &Block,
    konstanten: &[String],
    weltnamen: &[String],
    absagen: &mut Absagen,
) {
    let mut taten = Taten::default();
    sammle_taten(b, &mut taten);
    traverse_gegen_touches(b, &f.name.text, konstanten, weltnamen, absagen);

    let ist_rein = w.liste.iter().any(|e| matches!(e.art, WirkungArt::Rein));
    let schreibrechte: Vec<String> = w
        .liste
        .iter()
        .filter_map(|e| match &e.art {
            WirkungArt::Schreibt(o)
            | WirkungArt::Verbraucht(o)
            | WirkungArt::Veroeffentlicht(o) => Some(o.text()),
            WirkungArt::Belegt(i) | WirkungArt::Maskiert(i) => Some(i.text.clone()),
            _ => None,
        })
        .collect();
    // Exklusiv erklaerte Sperren -- sie decken BEIDE Nahmen, denn exklusiv ist staerker.
    let sperren: Vec<String> = w
        .liste
        .iter()
        .filter_map(|e| match &e.art {
            WirkungArt::Sperrt(o) => Some(o.text()),
            _ => None,
        })
        .collect();
    // Geteilt erklaerte Sperren -- sie decken NUR die geteilte Nahme. Die Umkehrung waere
    // die gefaehrliche Richtung: ein Aufrufer, der `locks shared` liest, rechnet mit
    // Nebenlaeufigkeit, die es nicht gibt.
    let geteilte: Vec<String> = w
        .liste
        .iter()
        .filter_map(|e| match &e.art {
            WirkungArt::SperrtGeteilt(o) => Some(o.text()),
            _ => None,
        })
        .collect();

    // **Lokale Namen sind keine Wirkung.** Der Vergleich geht ueber den GRUNDNAMEN: ein
    // Schreibzugriff auf `i` oder `i.feld` gehoert dem Stapel, einer auf `p.slots[i]` der Welt.
    let mut lok = Vec::new();
    lokale(b, &mut lok);
    for (ort, span) in &taten.schreibt {
        let grund = ort.split(['.', '[', '-']).next().unwrap_or(ort);
        if lok.iter().any(|l| l == grund) {
            continue;
        }
        if ist_rein {
            absagen.schiebe(
                Absage::fehler(
                    "E005",
                    *span,
                    format!("`{}` writes `{ort}` but declares `pure`", f.name.text),
                )
                .mit_notiz("`pure` means: touches nothing -- not even by reading")
                // Lane 187: the hull names the missing entry, so the repair is unique --
                // a lone `pure` is contradicted by this write and gives way to it.
                .mit_fix(crate::fix::append_effect(w, format!("writes {ort}"))),
            );
            continue;
        }
        if !schreibrechte.iter().any(|e| deckt(e, ort)) {
            absagen.schiebe(
                Absage::fehler(
                    "E005",
                    *span,
                    format!(
                        "`{ort}` is written but appears in no effect of `{}`",
                        f.name.text
                    ),
                )
                .mit_notiz(
                    "SPRACHE.md §7: `effects` is obligatory and not fail-open -- a \
                        missing clause is a missing promise, not an empty one",
                )
                .mit_notiz(format!(
                    "declared are: {}",
                    if schreibrechte.is_empty() {
                        "no write effect".to_string()
                    } else {
                        schreibrechte.join(", ")
                    }
                ))
                // Lane 187: the hull names the missing entry, so the repair is unique.
                .mit_fix(crate::fix::append_effect(w, format!("writes {ort}"))),
            );
        }
    }

    // **Die Lesehaelfte -- Lesart A, seit 2026-08-16.**
    //
    // Bis hierher prueft der Pass Schreiben und `locks`. Das Lesen blieb offen, weil
    // `FRAGMENTE.md` ueberall ohne `reads`-Zeile liest und die Frage war, ob das ein Befund
    // ist oder die gemeinte Bedeutung. **Sie ist ein Befund.** Der Grund steht im `TODO.md`
    // und hat zwei Teile: E3-Konsistenz (nichts ist implizit, auch kein Lesen), und
    // Meldbarkeit -- diese Absage nennt Funktion UND Ort, die gruebere Lesart koennte nur
    // eine Gegend nennen.
    let leserechte: Vec<String> = w
        .liste
        .iter()
        .filter_map(|e| match &e.art {
            WirkungArt::Liest(o) => Some(o.text()),
            // **Ein `awaits`-Laden liest den Ort, den `publishes` nennt** -- wer
            // veroeffentlicht, hat ihn vorher gelesen zu duerfen; das ist keine Grosszuegigkeit,
            // sondern dieselbe Stelle unter zwei Namen.
            WirkungArt::Veroeffentlicht(o) => Some(o.text()),
            _ => None,
        })
        .collect();
    let mut gemeldet: Vec<String> = Vec::new();
    for (ort, span) in &taten.liest {
        let grund = ort.split(['.', '[', '-']).next().unwrap_or(ort);
        if lok.iter().any(|l| l == grund) {
            continue;
        }
        // **Ein Parameter ist kein Weltzustand.** Was der Aufrufer hereingibt, gehoert ihm;
        // seine `effects` decken es. Sonst muesste jede Funktion ihre eigene Signatur
        // nachdeklarieren -- eine Zeile, die nichts sagt.
        if f.parameter.iter().any(|p| p.name.text == grund) {
            continue;
        }
        if konstanten.iter().any(|k| k == grund) {
            continue; // Konstante -- keine Stelle der Welt
        }
        if !weltnamen.iter().any(|k| k == grund) {
            continue; // kein bekannter Weltzustand -- der Pass sagt nichts (s. Kopf)
        }
        if ist_rein {
            if gemeldet.iter().any(|g| g == ort) {
                continue;
            }
            gemeldet.push(ort.clone());
            absagen.schiebe(
                Absage::fehler(
                    "E010",
                    *span,
                    format!("`{}` reads `{ort}` but declares `pure`", f.name.text),
                )
                .mit_notiz("`pure` means: touches nothing -- not even by reading")
                // Lane 187: the hull names the missing entry, so the repair is unique.
                .mit_fix(crate::fix::append_effect(w, format!("reads {ort}"))),
            );
            continue;
        }
        if !leserechte.iter().any(|e| deckt(e, ort)) {
            if gemeldet.iter().any(|g| g == ort) {
                continue; // eine Fundstelle je Ort reicht; zehn Meldungen sind eine
            }
            gemeldet.push(ort.clone());
            absagen.schiebe(
                Absage::fehler(
                    "E010",
                    *span,
                    format!(
                        "`{ort}` is read but appears in no `reads` effect of `{}`",
                        f.name.text
                    ),
                )
                .mit_notiz(
                    "reading A: reads are declared as completely as writes -- a frame \
                        promise that knows only the write side says nothing about WHAT the \
                        function saw",
                )
                .mit_notiz(format!(
                    "declared are: {}",
                    if leserechte.is_empty() {
                        "no read effect".to_string()
                    } else {
                        leserechte.join(", ")
                    }
                ))
                // Lane 187: the hull names the missing entry, so the repair is unique.
                .mit_fix(crate::fix::append_effect(w, format!("reads {ort}"))),
            );
        }
    }

    for (ort, span, geteilt) in &taten.sperrt {
        if sperren.iter().any(|e| deckt(e, ort)) {
            continue; // exklusiv erklaert deckt beide Nahmen
        }
        if *geteilt && geteilte.iter().any(|e| deckt(e, ort)) {
            continue;
        }
        // **E007 ist die gefaehrliche Richtung und bekommt darum eigenen Text:** der Rumpf
        // nimmt exklusiv, die Wirkung sagt geteilt. Wer die Signatur liest, rechnet mit
        // Nebenlaeufigkeit, die es nicht gibt -- und baut seine Latenzrechnung darauf.
        if !*geteilt && geteilte.iter().any(|e| deckt(e, ort)) {
            // Lane 187: strengthening the declaration to what the body takes is the
            // unique repair -- the converse (declaring exclusive) is expressly allowed,
            // so no other declaration can hold this body.
            let stronger = w.liste.iter().find_map(|e| match &e.art {
                WirkungArt::SperrtGeteilt(o) if deckt(&o.text(), ort) => Some(
                    gabbro_syntax::diag::Fix::new(e.span, format!("locks {}", o.text())),
                ),
                _ => None,
            });
            let mut a = Absage::fehler(
                "E007",
                *span,
                format!(
                    "`{}` takes `{ort}` EXCLUSIVELY but declares `locks shared {ort}`",
                    f.name.text
                ),
            )
            .mit_notiz(
                "declaring shared and taking exclusively is the dangerous direction: \
                    whoever reads the signature counts on concurrency that does not \
                    exist",
            )
            .mit_notiz("the converse is allowed -- declaring exclusive covers the shared acquisition");
            if let Some(fx) = stronger {
                a = a.mit_fix(fx);
            }
            absagen.schiebe(a);
            continue;
        }
        absagen.schiebe(
            Absage::fehler(
                "E006",
                *span,
                format!(
                    "`locks {}{ort}` is in the body but not in the effects of `{}`",
                    if *geteilt { "shared " } else { "" },
                    f.name.text
                ),
            )
            .mit_notiz("the lock order follows from the declared locks, not from the body")
            // Lane 187: the hull names the missing entry, so the repair is unique.
            .mit_fix(crate::fix::append_effect(
                w,
                format!(
                    "locks {}{ort}",
                    if *geteilt { "shared " } else { "" }
                ),
            )),
        );
    }
}

fn funktion(
    f: &FnDecl,
    modul: &str,
    g: &crate::aufrufgraph::Graph,
    konstanten: &[String],
    weltnamen: &[String],
    schreiber: &std::collections::BTreeSet<String>,
    ab: &crate::ableitung::Ableitung,
    absagen: &mut Absagen,
) {
    match &f.effects {
        None => {
            // **Lane 191: a body derives its clause.** Where the fixpoint
            // settles, the omitted clause IS the derived set — no refusal.
            // Where it stays a lower bound (`unvollstaendig`), or where the
            // callees promise more than the deeds cover, the omission stays
            // a refusal (`N305`) with the reason. A function WITHOUT a body
            // (`extern`, `prim`) has nothing to derive from — `E001` stays,
            // and so does the `spec fn` exemption: a spec carries no runtime
            // effect, so there is no deed to derive.
            if f.klasse != Some(FnKlasse::Spec) {
                if matches!(f.rumpf, FnRumpf::Block(_)) {
                    omissionspruefung(f, modul, g, ab, absagen);
                } else {
                    absagen.schiebe(
                        Absage::fehler(
                            "E001",
                            f.name.span,
                            format!("`{}` has no `effects` clause", f.name.text),
                        )
                        .mit_notiz(
                            "SPRACHE.md §7: `effects` is obligatory and not fail-open",
                        )
                        .mit_notiz(
                            "the omission was at once the strongest promise and the cheapest \
                                one to write",
                        )
                        // **«B3» hint 1, and it is the one that shortens the whole session.**
                        //
                        // Measured: after this refusal the next two attempts were `effects {}`
                        // and `effects pure`. Both are correct refusals of their own, and both
                        // are attempts that were spent GUESSING THE SHAPE of a clause this
                        // message named without showing. *Naming what is missing and not what
                        // to write costs one attempt per reader, every time.*
                        .mit_notiz(
                            "the clause is a BRACE LIST and it is never empty: `effects { pure }` \
                                for a function that touches nothing, otherwise \
                                `effects { reads p, writes q }`",
                        ),
                    );
                }
            }
        }
        Some(w) => {
            rein_allein(w, absagen);
            vertrag_gegen_wirkungen(f, Some(w), konstanten, weltnamen, schreiber, &[], absagen);
            if let FnRumpf::Block(b) = &f.rumpf {
                rumpf_gegen_wirkungen(f, w, b, konstanten, weltnamen, absagen);
                aufrufwirkungen(f, modul, w, g, weltnamen, absagen);
            }
        }
    }
    if f.effects.is_none() {
        // **Lane 191:** over a non-`spec` body the derived clause covers the
        // contract; without one nothing does, as before.
        let erbt = if f.klasse != Some(FnKlasse::Spec) && matches!(f.rumpf, FnRumpf::Block(_)) {
            ererbte_deckung(ab, modul, f)
        } else {
            Vec::new()
        };
        vertrag_gegen_wirkungen(f, None, konstanten, weltnamen, schreiber, &erbt, absagen);
    }

    if f.klasse == Some(FnKlasse::Divergent) {
        let divergiert = f
            .effects
            .as_ref()
            .map(|w| w.liste.iter().any(|e| matches!(e.art, WirkungArt::Divergiert)))
            .unwrap_or(false);
        if !divergiert {
            // Lane 187: the missing word is named exactly (`diverges`), so the repair
            // is unique where the clause stands. Without a clause `E001` owns the line
            // and this hint carries no fix.
            let missing = f
                .effects
                .as_ref()
                .map(|w| crate::fix::append_effect(w, "diverges".to_string()));
            let mut a = Absage::hinweis(
                "E003",
                f.name.span,
                format!(
                    "`divergent fn {}` does not name `diverges` among its effects",
                    f.name.text
                ),
            )
            .mit_notiz(
                "SYNTAX.md §14 writes `divergent fn idle() effects { diverges }` -- \
                    the clause carries the divergence",
            );
            if let Some(fx) = missing {
                a = a.mit_fix(fx);
            }
            absagen.schiebe(a);
        }
    }

    // Eine `spec fn` mit `= pred;` ist die einzige Form, in der ein Quantor im Rumpf steht.
    if f.klasse != Some(FnKlasse::Spec) {
        if let FnRumpf::Pred(p) = &f.rumpf {
            absagen.schiebe(
                Absage::fehler(
                    "E004",
                    p.span,
                    "a predicate as a body is allowed only for a `spec fn`",
                )
                .mit_notiz("`fndecl`: `= pred ;` only for `spec fn`"),
            );
        }
    }
}

/// **Lane 191 (`N305`): the omission that stays a refusal.**
///
/// An omitted `effects` over a body is derived — unless the derivation is a
/// lower bound or the callees promise more than the deeds cover. The first
/// shape is `unvollstaendig`: an unknown callee, a silent edge, a
/// contract-less indirect call, an unbuildable bridge. The second is an
/// over-declared callee, whose padding the derived set does not carry (the
/// fixpoint runs over BODIES precisely so padding never passes silently —
/// `ableitung.rs`). Both name their reason: the fix is to WRITE the clause,
/// and the note shows its shape. That shape note is «B3» hint 1, moved here
/// with the rule — a refusal that names what is missing without showing what
/// to write costs one attempt per reader, every time.
fn omissionspruefung(
    f: &FnDecl,
    modul: &str,
    g: &crate::aufrufgraph::Graph,
    ab: &crate::ableitung::Ableitung,
    absagen: &mut Absagen,
) {
    let key = crate::umgebung::qualifiziere(modul, &f.name.text);
    let mut grund: Option<String> = None;
    let mut abgeleitet: std::collections::BTreeSet<String> = Default::default();
    if let Some(a) = ab.je.get(&key) {
        abgeleitet = a.wirkungen.clone();
        grund = a.unvollstaendig.clone();
    }
    if grund.is_none() {
        // The fixpoint settled: the callees may still promise more than the
        // deeds cover — one check, shared with the view (`ableitung.rs`).
        grund = crate::ableitung::deckungsluecke(&abgeleitet, &g.huelle(&key));
    }
    let Some(grund) = grund else {
        return;
    };
    absagen.schiebe(
        Absage::fehler(
            "N305",
            f.name.span,
            format!(
                "`{}` declares no `effects`, and the clause cannot be derived: {grund}",
                f.name.text
            ),
        )
        .mit_notiz(
            "an omitted clause means \"whatever it is\" — but only where the \
             derivation settles: a lower bound is not an answer (R16)",
        )
        .mit_notiz(
            "the caller covers what its callees promise — a derived set that \
             leaves a promise uncovered is not a contract the caller can hold",
        )
        .mit_notiz(
            "the clause is a BRACE LIST and it is never empty: `effects { pure }` \
                for a function that touches nothing, otherwise \
                `effects { reads p, writes q }`",
        ),
    );
}

/// **Lane 191: what the derived clause covers of the contract.**
///
/// `vertrag_gegen_wirkungen` holds `requires`/`ensures` reads against the
/// effect list. For an omitted clause over a settled derivation, the derived
/// places stand where the written ones would — exactly like a written line.
/// Under an unsettled derivation nothing is covered (as before: the deckung
/// of an omission was always empty), so `E220`/`E221` keep speaking there.
fn ererbte_deckung(ab: &crate::ableitung::Ableitung, modul: &str, f: &FnDecl) -> Vec<String> {
    let key = crate::umgebung::qualifiziere(modul, &f.name.text);
    let Some(a) = ab.je.get(&key) else {
        return Vec::new();
    };
    if a.unvollstaendig.is_some() {
        return Vec::new();
    }
    a.wirkungen
        .iter()
        .filter_map(|w| {
            let (verb, ort) = trenne(w);
            match verb {
                "reads" | "writes" if !ort.is_empty() => Some(ort.to_string()),
                _ => None,
            }
        })
        .collect()
}

/// `pure` heisst „fasst nichts an". Eine zweite Wirkung daneben ist ein Widerspruch, kein
/// Zusatz -- und der Widerspruch faellt hier, nicht beim Leser.
fn rein_allein(w: &Wirkungen, absagen: &mut Absagen) {
    let rein: Vec<&Wirkung> = w
        .liste
        .iter()
        .filter(|e| matches!(e.art, WirkungArt::Rein))
        .collect();
    if rein.is_empty() {
        return;
    }
    if w.liste.len() > 1 {
        let andere: Vec<&str> = w
            .liste
            .iter()
            .filter(|e| !matches!(e.art, WirkungArt::Rein))
            .map(|e| e.art.benennung())
            .collect();
        let stelle = rein[0].span;
        absagen.schiebe(
            Absage::fehler(
                "E002",
                stelle,
                format!(
                    "`pure` stands next to {} -- `pure` means nothing is touched",
                    andere.join(", ")
                ),
            )
            .mit_notiz("either `effects { pure }` alone, or the effects without `pure`"),
        );
    }
    if rein.len() > 1 {
        // Lane 187: two identical entries, and removing one of them is the unique
        // repair -- the comma goes with it, so no stray comma is left behind. (The
        // arm above, `pure` beside other entries, gets no fix: the diagnostic itself
        // offers two directions there, so none is uniquely determined.)
        let spans = crate::fix::entry_spans(w);
        let second = w
            .liste
            .iter()
            .enumerate()
            .filter(|(_, e)| matches!(e.art, WirkungArt::Rein))
            .map(|(i, _)| i)
            .nth(1);
        let mut a = Absage::fehler(
            "E002",
            rein[1].span,
            "`pure` appears twice in the same effect list",
        );
        if let Some(j) = second {
            if j < spans.len() {
                a = a.mit_fix(crate::fix::delete_entry(&spans, j));
            }
        }
        absagen.schiebe(a);
    }
}

/// **E008 — die Wirkungen der Gerufenen gehoeren in die Liste des Rufers.**
///
/// *„Das ist der Posten, der `effects` erst kompositional macht"* (`TODO.md`). Ohne ihn galt
/// `effects { pure }` fuer eine Funktion, die eine schreibende rief — und die Rahmenaussage
/// endete an der ersten Aufrufgrenze.
///
/// **Die Fassung ist grob und in die sichere Richtung grob:** die Wirkung des Gerufenen wird
/// mit SEINEM Parameternamen gesehen, nicht auf die Argumente des Rufers abgebildet. Ein
/// `writes p.slots` beim Gerufenen verlangt beim Rufer eine Schreibwirkung — irgendeine.
/// **Das sieht mehr Wirkungen als da sind, nie weniger.** Die Abbildung auf Argumente ist
/// der naechste Schritt und braucht eine Alias-Analyse, die es nicht gibt.
///
/// **Die Grobheit hat eine Richtung, und nur deshalb ist sie zulaessig.** Dieser Pass rechnet
/// ueber **Mengen**, nicht ueber **Pfade** — das ist die richtige Grobheit, *aber nur weil sie
/// hier in die SICHERE Richtung grob ist*: er sieht mehr Wirkungen als da sind, nie weniger.
/// **Wo dieselbe Grobheit in die unsichere Richtung zeigte, wird sie nicht angewandt** — s.
/// `diverges` unten. *Das ist R8 auf Analysen statt auf Absagen: bevor eine Analyse
/// vergroebert, wird die Richtung geprueft, nicht die Bequemlichkeit.* **Der naechste Pass,
/// der ueber Mengen rechnet, faengt mit dieser Frage an.**
///
/// **Und wo die Huelle unvollstaendig ist, gibt es einen DRITTEN Zustand** (R16 + R15): ein
/// Zyklus oder ein Gerufener ohne `effects` macht die Menge zu einer unteren Schranke. Daraus
/// wird **nicht abgesagt** — eine Absage aus einer unteren Schranke waere eine Behauptung.
/// **Aber auch nicht bestaetigt**: eine untere Schranke ist eine *unsichere* Deckung fuer
/// `pure`, und ein stilles Durchlassen waere die Ausweg-Zusicherung aus R15 durch die
/// Hintertuer — *„erfuellt, weil nichts passiert ist"*. Der ehrliche dritte Zustand heisst
/// **`E009` — unentscheidbar**, und er ist sichtbar, nicht gruen.
fn aufrufwirkungen(
    f: &FnDecl,
    modul: &str,
    w: &Wirkungen,
    g: &crate::aufrufgraph::Graph,
    weltnamen: &[String],
    absagen: &mut Absagen,
) {
    // **Eine Wirkung auf einen EIGENEN lokalen Namen ist hier eingelöst** (2026-08-19).
    //
    // Seit der Aufrufgraph die Parameternamen des Gerufenen durch die Argumente des Rufers
    // ersetzt, kommt `consumes p` beim Rufer als `consumes y` an — und `y` ist ein Name, den
    // niemand ausserhalb dieser Funktion kennt. **Ihn in der eigenen `effects`-Liste zu
    // verlangen hiesse, über eine Stelle zu sprechen, die es draussen nicht gibt.**
    //
    // *Vorher war beides falsch:* der Rufer musste `consumes p` schreiben — den Parameter
    // des GERUFENEN — und `E008` fiel auf sauberem Code.
    let mut hier: Vec<String> = Vec::new();
    if let FnRumpf::Block(b) = &f.rumpf {
        lokale(b, &mut hier);
    }
    let h = g.huelle(&g.schluessel_von(modul, &f.name.text));
    if let Some(grund) = &h.unvollstaendig {
        // Weder Absage noch Bestaetigung: der dritte Zustand, und er steht da.
        absagen.schiebe(
            Absage::hinweis(
                "E009",
                f.name.span,
                format!(
                    "the call effects of `{}` are undecidable: {grund}",
                    f.name.text
                ),
            )
            .mit_notiz(
                "the effect set is only a LOWER bound here -- no completeness follows from it",
            )
            // **And since 2026-08-24 the check CONTINUES below** (the pass register booked
            // the old behaviour on 2026-08-21: *at a cycle `E009` is set and the pass
            // returns BEFORE any `E008` check -- one unresolvable edge deep down devalues
            // `E008` for the whole call chain above it*).
            //
            // **The hull is a LOWER bound, and that is exactly what makes the rest sound:**
            // everything IN it really happens, so demanding that it be declared holds
            // regardless of what is missing. *What incompleteness costs is the other
            // direction* -- no completeness, and in particular no `pure` promise beyond
            // what the partial hull already refutes.
            //
            // > A hint that switches a check OFF is more expensive than the check is worth.
            // > Ten corpus sites carried `E009` and had their frame unchecked entirely.
            .mit_notiz(
                "what still IS checked below: every effect the PARTIAL hull already \
                 contains must be declared -- a lower bound refutes, it just cannot confirm",
            ),
        );
    }
    let ist_rein = w.liste.iter().any(|e| matches!(e.art, WirkungArt::Rein));
    let eigene: Vec<String> = w.liste.iter().map(|e| e.art.benennung().to_string()).collect();
    // Dieselben Wirkungen, aber MIT ihrem Ort -- `writes c.slots`, nicht bloss `writes`.
    let eigene_orte: Vec<String> = w.liste.iter().map(|e| e.art.text()).collect();
    for wirkung in &h.wirkungen {
        // Der Ort steht am Ende; `y.slots` und `y` zaehlen beide.
        if let Some((_, ort)) = wirkung.rsplit_once(' ') {
            let grund = ort.split(['.', '[']).next().unwrap_or(ort);
            if hier.iter().any(|l| l == grund) {
                continue;
            }
        }
        // **Die Benennung ist zweiwortig, wo sie es ist.** `locks shared X` heisst
        // `locks shared`, nicht `locks` -- ein Vergleich am ersten Leerzeichen liess eine
        // Funktion an ihrer EIGENEN Wirkung scheitern. Gefunden an `beispiele/10`, sofort
        // beim ersten Lauf des neuen Passes.
        let art = if wirkung.starts_with("locks shared") {
            "locks shared"
        } else {
            wirkung.split_whitespace().next().unwrap_or("")
        };
        if art == "pure" {
            continue;
        }
        // **`diverges` wandert NICHT nach oben.** Wer eine divergierende Funktion ruft,
        // divergiert nicht -- nur wer sie auf JEDEM Weg ruft. Das ist eine Aussage ueber
        // Pfade, und dieser Pass rechnet ueber Mengen. Die grobe Fassung waere hier in die
        // UNSICHERE Richtung grob: sie erzwaenge `diverges` an Funktionen, die zurueckkehren.
        // (`beispiele/11a`: der Fehlerzweig ruft `abbruch()`, der Normalfall kehrt zurueck.)
        if art == "diverges" {
            continue;
        }
        // Eine geteilte Nahme ist von einer exklusiven Erklaerung gedeckt -- dieselbe
        // Asymmetrie wie `E007`, eine Ebene hoeher.
        if art == "locks shared" && eigene.iter().any(|e| e == "locks") {
            continue;
        }
        // **`consumes X` deckt `writes X`** -- dieselbe Asymmetrie, eine Klasse weiter.
        //
        // Wer eine Stelle VERBRAUCHT, sagt ueber sie mehr, als wer sie beschreibt: sie ist
        // danach nicht mehr da. Der Rahmen soll dem Leser sagen, was ein Ruf mit der Welt
        // machen darf, und `consumes` beantwortet diese Frage strenger als `writes`.
        //
        // *Der Korpus liest es auch so:* `einsammeln` fuehrt `consumes Kappenraum.slots`
        // und kein `writes` daneben (`beispiele/09`), waehrend der Gerufene
        // `writes Kappenraum.slots` fuehrt. Ohne diese Zeile muesste jedes `consumes` ein
        // `writes` neben sich haben -- **und stuende dann nie fuer sich.**
        if art == "writes" {
            if let Some((_, ort)) = wirkung.rsplit_once(' ') {
                let grund = ort.split(['.', '[']).next().unwrap_or(ort);
                if eigene_orte.iter().any(|e| {
                    e.strip_prefix("consumes ")
                        .is_some_and(|o| o.split(['.', '[']).next().unwrap_or(o) == grund)
                }) {
                    continue;
                }
            }
        }
        if ist_rein {
            absagen.schiebe(
                Absage::fehler(
                    "E008",
                    f.name.span,
                    format!(
                        "`{}` declares `pure` but calls something with `{wirkung}`",
                        f.name.text
                    ),
                )
                .mit_notiz(
                    "`effects` is compositional: the effects of the callees belong to the \
                        caller",
                ),
            );
            return;
        }
        // **Der Rahmen endete an der Aufrufgrenze** (behoben 2026-08-19). Bis hier verglich
        // dieser Pass nur die ART: `effects { writes a }` deckte ein `writes b` des
        // Gerufenen, weil beides „writes" heisst.
        //
        // ```gabbro
        // impl fn schreibt_b() effects { writes b } { b = 1; }
        // impl fn eng() effects { writes a } { a = 1; schreibt_b(); }   -- 0 Fehler
        // ```
        //
        // Die Begruendung im Modulkopf -- *„sieht mehr Wirkungen als da sind, nie weniger"* --
        // gilt fuer die HUELLE, nicht fuer diesen Vergleich. **Er sieht weniger**, und damit
        // zeigte die Grobheit in die unsichere Richtung: genau die Frage, die der Kopf zu
        // stellen verlangt und hier nicht gestellt wurde.
        //
        // Verglichen wird, **wo der Ort ueberhaupt vergleichbar ist**: bei bekanntem
        // Weltzustand (`static`, `atomic`, `table`, `device`, `state`) -- dieselbe Linie wie
        // `E010`, und aus demselben Grund. Ein Parametername des Gerufenen, den kein Argument
        // aufloest, macht die Huelle `unvollstaendig` und faellt bei `E009`, nicht hier.
        if eigene.iter().any(|e| e == art) {
            let Some((_, ort)) = wirkung.rsplit_once(' ') else {
                continue;
            };
            let grund = ort.split(['.', '[']).next().unwrap_or(ort);
            if !weltnamen.iter().any(|k| k == grund) {
                continue; // kein bekannter Weltzustand -- der Pass sagt nichts
            }
            if eigene_orte.iter().any(|e| {
                let Some((a, o)) = e.rsplit_once(' ') else {
                    return false;
                };
                a == art && o.split(['.', '[']).next().unwrap_or(o) == grund
            }) {
                continue;
            }
            absagen.schiebe(
                Absage::fehler(
                    "E008",
                    f.name.span,
                    format!(
                        "`{}` declares `{art}` but calls something with `{wirkung}` -- \
                         a different place",
                        f.name.text
                    ),
                )
                .mit_notiz(
                    "`effects` is the FRAME: it names the places, not merely the kind of \
                     touch -- otherwise one `writes` covers every place in the program",
                ),
            );
            return;
        }
        if !eigene.iter().any(|e| e == art) {
            absagen.schiebe(
                Absage::fehler(
                    "E008",
                    f.name.span,
                    format!(
                        "`{}` calls something with `{wirkung}` but names no `{art}` effect",
                        f.name.text
                    ),
                )
                .mit_notiz(
                    "the effect comes from a callee -- `effects` covered only the first \
                        level until 2026-08-15",
                )
                .mit_notiz(format!(
                    "declared are: {}",
                    if eigene.is_empty() { "nichts".into() } else { eigene.join(", ") }
                )),
            );
        }
    }
}

/// **Die Domaene einer `traverse` ist ein Lesen.** `traverse s of c over slots of c` liest
/// `c` -- wer die Sammlung laeuft, greift sie an, auch wenn der Rumpf nur schreibt.
fn domaene_liest(d: &Domaene, t: &mut Taten) {
    match d {
        Domaene::SlotsVon(o)
        | Domaene::NachfahrenVon(o)
        | Domaene::VorfahrenVon(o)
        | Domaene::Schlange(o)
        | Domaene::ElementeVon(o)
        | Domaene::AbbildungenVon(o)
        | Domaene::KetteIn { ort: o, .. } => t.liest.push((o.text(), o.span)),
        // `fields of <pfad>` nennt einen TYP, keinen Ort; `threads` nennt gar nichts.
        Domaene::FelderVon(_) | Domaene::Threads => {}
    }
}

/// **E220/E221 -- the contract footprint: `requires`/`ensures` may read only what the
/// function's effects cover, or what nobody writes.**
///
/// Lane 101 proved the Lean half (`vertragFussB`, `hReqTAll_aus_B` and its three
/// siblings): every carrier a contract reads must lie in the function's write
/// signature. It also proved the finding -- on the reference fixture itself the
/// write-signature containment is unsatisfiable for a read-only function, so the
/// checker rule repaired here asks for `reads` OR `writes` cover, and frees
/// carriers that no function of the program writes at all (read-only).
///
/// The collection reuses the body reader (`liest_expr`) arm for arm, with exactly
/// two deltas, each with its reason:
/// * `old(p)` (`Alt`) is a read of `p` -- in a body it cannot occur, so the body
///   reader never learned it; in `ensures` it is the most ordinary read there is.
/// * a call to a predicate word (`Has`/`Held`) is pruned WITH its arguments --
///   `requires Has(RDTSCP)` names a capability, not a read of a register, the same
///   distinction `ist_praedikatswort` draws for the call graph.
fn vertrag_liest(e: &Expr, t: &mut Taten) {
    match &e.art {
        ExprArt::Ruf(r) if crate::ist_praedikatswort(r) => {}
        ExprArt::Ruf(r) => {
            for a in &r.argumente {
                vertrag_liest(a, t);
            }
        }
        ExprArt::Alt(o) => {
            t.liest.push((o.text(), o.span));
            for suf in &o.suffixe {
                if let OrtSuffix::Index(ix) = suf {
                    vertrag_liest(ix, t);
                }
            }
        }
        _ => liest_expr(e, t),
    }
}

/// Every place a contract predicate reads, plus the quantifier binders it binds.
/// `Erreicht { von, nach }` names two places outside any expression, and a quantifier
/// domain (`mappings of k`, `slots of c`) reads its carrier -- both are reads no
/// expression walker reaches, so they stand here explicitly. `Held(L)` names a lock
/// and reads nothing. Binders are popped after the quantifier body: a name bound
/// inside `forall` is local only there, and a world carrier of the same name outside
/// stays a read.
fn vertrag_orte(p: &Pred, binder: &mut Vec<String>, t: &mut Taten) {
    match &p.art {
        PredArt::Vergleich(e) => vertrag_liest(e, t),
        PredArt::Element(e, d) => {
            vertrag_liest(e, t);
            domaene_liest(d, t);
        }
        PredArt::Erreicht { von, nach, .. } => {
            t.liest.push((von.text(), von.span));
            ziel_indizes(von, t);
            t.liest.push((nach.text(), nach.span));
            ziel_indizes(nach, t);
        }
        PredArt::Quantor(q) => {
            let marke = binder.len();
            binder.push(q.variable.text.clone());
            domaene_liest(&q.domaene, t);
            vertrag_orte(&q.rumpf, binder, t);
            binder.truncate(marke);
        }
        PredArt::Klammer(x) | PredArt::Nicht(x) => vertrag_orte(x, binder, t),
        PredArt::Und(a, b) | PredArt::Oder(a, b) | PredArt::Folgt(a, b) => {
            vertrag_orte(a, binder, t);
            vertrag_orte(b, binder, t);
        }
        PredArt::Held { .. } => {}
    }
}

/// The carrier roots the whole program writes -- the read-only boundary of E220/E221.
/// Declared `writes`/`consumes`/`publishes` targets of every function, the writes of
/// every function body (a body that writes without declaring already falls at E005,
/// but the carrier is written either way), and the `writes` of every device
/// transition (they move registers the functions observe). Only known world roots
/// count -- a parameter-rooted place (`writes p.slots`) belongs to the caller, the
/// same cut `bau.rs` makes for `schreibt_fn`.
fn schreiber_des_programms(
    baum: &Programm,
    weltnamen: &[String],
) -> std::collections::BTreeSet<String> {
    let mut aus: std::collections::BTreeSet<String> = Default::default();
    crate::fuer_jedes_item(baum, &mut |item| match &item.art {
        ItemArt::Funktion(f) => {
            if let Some(w) = &f.effects {
                merke_schreiber(&mut aus, w, weltnamen);
            }
            if let FnRumpf::Block(b) = &f.rumpf {
                let mut taten = Taten::default();
                sammle_taten(b, &mut taten);
                for (ort, _) in &taten.schreibt {
                    let grund = ort.split(['.', '[']).next().unwrap_or(ort).to_string();
                    if weltnamen.iter().any(|k| k == &grund) {
                        aus.insert(grund);
                    }
                }
            }
        }
        ItemArt::Device(d) => {
            for u in &d.uebergaenge {
                if let Some(w) = &u.effects {
                    merke_schreiber(&mut aus, w, weltnamen);
                }
            }
        }
        _ => {}
    });
    aus
}

/// One declared effect list's contribution to the writer set: the roots of every
/// `writes`/`consumes`/`publishes` target that names known world state. A free
/// function (not a closure) so the whole-program walk above holds the only
/// mutable borrow of the set.
fn merke_schreiber(
    aus: &mut std::collections::BTreeSet<String>,
    w: &Wirkungen,
    weltnamen: &[String],
) {
    for e in &w.liste {
        match &e.art {
            WirkungArt::Schreibt(o) | WirkungArt::Verbraucht(o) | WirkungArt::Veroeffentlicht(o) => {
                let grund = o.text().split(['.', '[']).next().unwrap_or("").to_string();
                if weltnamen.iter().any(|k| k == &grund) {
                    aus.insert(grund);
                }
            }
            _ => {}
        }
    }
}

/// **E245-E249 -- the footprint guard (`fussOrtGB` of `ziel_ort_geraet`).**
///
/// The goal theorem asks, per function `f` over the complete member list, that every
/// carrier of the widened footprint `fussOrteG P f` be guarded by a lock `f` holds BY
/// SIGNATURE, or be written by no function at all (`ZielOrtGeraetSem.lean:459-480`,
/// soundness `fussOrtGB_ok`). Lane 120 built the weaker effects-cover form (E220/E221:
/// contract carriers in `reads`/`writes` or unwritten). This section brings the exact
/// shape: contract carriers AND direct callees' contract carriers (1), guarded by a
/// signature-held lock -- `requires Held(L)` with `lock L protects` over the carrier --
/// not merely named in `effects`, or never written (2), plus the indirect-call admission
/// `kandB`/`KandOk` (3): an indirect call is admitted only if every function behind the
/// pointer keeps its contract carriers inside the caller's footprint
/// (`ZielOrtVollSem.lean:111-143`).
///
/// Carriers are whole tables and globals (roots), exactly the granularity of
/// `D.Tab + D.Glob` in the model: a place counts by its root before the first
/// `.`, `[` or `-`, the same root the writer set and the E220 leg use.
///
/// Five codes, one per footprint leg, all at HINT level: the strict premise refuses
/// ordinary single-threaded corpus programs (a reader over a written carrier with no
/// lock in the whole unit -- measured over `beispiele/*.gab`, reported in the lane
/// report), so refusing at error level would declare the corpus wrong. The condition
/// itself is exact; only the severity is not. One refusal per (function, carrier, leg).
///
/// Deliberate boundaries, each with its Lean ground:
/// * device-rooted reads are NO footprint: a register read contributes no `Orte` in the
///   model (`blockOrteP` for `regLies` reads only the rest, `ZielOrt.lean:180`), and the
///   device carriers enter only through `D.rtraeger`, which the surface cannot declare
///   (default none, `ZielOrtGeraetSem.lean:17-29`). The day the surface names them, the
///   `geraete` filter below is where they slot in.
/// * `syscall`/`axiom` contracts, `maintains` and `= pred ;` bodies are not read -- the
///   same boundary the E220 leg draws.
/// * lock identity is by short name (what `Held(L)` spells); a `Held` naming no declared
///   lock guards nothing (the `PHASE_ROH` precedent `geteilt.rs` documents for `H016`).
/// * shared holding counts as holding: the model keeps one lock list per signature, and
///   whether a shared guard suffices for a WRITER is `H001`'s question, not this one's.
///
/// The contract half of the frame promise: every KNOWN world carrier a `requires`
/// (E220) or `ensures` (E221) clause reads must be covered by a declared `reads` or
/// `writes` effect, unless no function of the program writes it at all. Same filters
/// as the E010 read half -- parameters, quantifier binders, constants and unknown
/// names are no world reads -- plus the read-only exception, which is the repair lane
/// 101 proposed after measuring that write-signature containment alone rejects
/// ordinary read contracts. One refusal per (function, carrier, clause kind).
///
/// NOT read: `syscall` and `axiom` contracts (same shape, other lanes), `maintains`
/// (names a spec function, not a carrier), the `= pred ;` body of a `spec fn` (the
/// specification itself, not a contract clause over it), and calls into spec
/// functions (only their arguments count -- the callee's own reads are its own
/// frame, stated, not shown).
fn vertrag_gegen_wirkungen(
    f: &FnDecl,
    w: Option<&Wirkungen>,
    konstanten: &[String],
    weltnamen: &[String],
    schreiber: &std::collections::BTreeSet<String>,
    erbt: &[String],
    absagen: &mut Absagen,
) {
    let mut deckung: Vec<String> = w
        .map(|w| {
            w.liste
                .iter()
                .filter_map(|e| match &e.art {
                    WirkungArt::Liest(o) | WirkungArt::Schreibt(o) => Some(o.text()),
                    _ => None,
                })
                .collect()
        })
        .unwrap_or_default();
    // **Lane 191:** the derived places cover the contract where the clause is
    // omitted over a settled derivation — see `ererbte_deckung`.
    deckung.extend(erbt.iter().cloned());
    for (klauseln, code, wort) in [
        (&f.requires, "E220", "requires"),
        (&f.ensures, "E221", "ensures"),
    ] {
        let mut gemeldet: Vec<String> = Vec::new();
        for p in klauseln {
            let mut taten = Taten::default();
            let mut binder = Vec::new();
            vertrag_orte(p, &mut binder, &mut taten);
            for (ort, span) in &taten.liest {
                let grund = ort.split(['.', '[', '-']).next().unwrap_or(ort);
                if f.parameter.iter().any(|x| x.name.text == grund) {
                    continue;
                }
                if binder.iter().any(|x| x == grund) {
                    continue;
                }
                if konstanten.iter().any(|k| k == grund) {
                    continue;
                }
                if !weltnamen.iter().any(|k| k == grund) {
                    continue;
                }
                if !schreiber.contains(grund) {
                    continue;
                }
                if deckung.iter().any(|e| deckt(e, ort)) {
                    continue;
                }
                if gemeldet.iter().any(|g| g == grund) {
                    continue;
                }
                gemeldet.push(grund.to_string());
                absagen.schiebe(
                    Absage::fehler(
                        code,
                        *span,
                        format!(
                            "`{ort}` is read by the `{wort}` of `{}` but neither \
                             `reads {grund}` nor `writes {grund}` stands in its effects",
                            f.name.text
                        ),
                    )
                    .mit_notiz(
                        "a contract is part of the frame: whoever relies on what the \
                         contract saw must find the carrier in the effect list",
                    )
                    .mit_notiz(format!(
                        "declared are: {}; carriers no function writes need no cover",
                        if deckung.is_empty() {
                            "no read or write effect".to_string()
                        } else {
                            deckung.join(", ")
                        }
                    )),
                );
            }
        }
    }
}

/// The root of a place: everything before the first `.`, `[` or `-`. Carriers are
/// whole tables and globals in the model, so the footprint compares roots.
///
/// `pub(crate)`: lane 175 (`fusswache2.rs`) reads the same roots for the decidable
/// footprint premise `FussS` -- one reader, one root function (W7).
pub(crate) fn carrier_root(ort: &str) -> &str {
    ort.split(['.', '[', '-']).next().unwrap_or(ort)
}

/// Full places one contract side reads, as (root, span) pairs. Same read detection
/// as the E220 leg (`vertrag_orte`: quantifier binders scoped, `Erreicht` places and
/// domains counted, `Held` naming no read) with the same filters (parameters, binders,
/// constants, unknown names), plus one: device-rooted reads are no footprint carriers
/// (see the section header).
///
/// `pub(crate)`: lane 175 (`fusswache2.rs`) builds the same footprint for `FussS`.
pub(crate) fn clause_roots(
    klauseln: &[Pred],
    f: &FnDecl,
    konstanten: &[String],
    weltnamen: &[String],
    geraete: &std::collections::BTreeSet<String>,
) -> Vec<(String, Span)> {
    let mut aus = Vec::new();
    for p in klauseln {
        let mut taten = Taten::default();
        let mut binder = Vec::new();
        vertrag_orte(p, &mut binder, &mut taten);
        for (ort, span) in &taten.liest {
            let grund = carrier_root(ort);
            if f.parameter.iter().any(|x| x.name.text == grund) {
                continue;
            }
            if binder.iter().any(|x| x == grund) {
                continue;
            }
            if konstanten.iter().any(|k| k == grund) {
                continue;
            }
            if !weltnamen.iter().any(|k| k == grund) {
                continue;
            }
            if geraete.contains(grund) {
                continue;
            }
            aus.push((grund.to_string(), *span));
        }
    }
    aus
}

/// Full places a body reads, as (root, span) pairs. The same deed walk the E005/E010
/// halves use (`sammle_taten`), the same stack filter (`lokale`), the same world
/// filters as the E010 read half (parameters, constants, unknown names), plus the
/// device-root exception of the section header. First span wins per root.
///
/// `pub(crate)`: lane 175 (`fusswache2.rs`) builds the same footprint for `FussS`.
pub(crate) fn body_roots(
    f: &FnDecl,
    b: &Block,
    konstanten: &[String],
    weltnamen: &[String],
    geraete: &std::collections::BTreeSet<String>,
) -> Vec<(String, Span)> {
    let mut taten = Taten::default();
    sammle_taten(b, &mut taten);
    let mut lok = Vec::new();
    lokale(b, &mut lok);
    let mut aus: Vec<(String, Span)> = Vec::new();
    for (ort, span) in &taten.liest {
        let grund = carrier_root(ort);
        if lok.iter().any(|l| l == grund) {
            continue;
        }
        if f.parameter.iter().any(|p| p.name.text == grund) {
            continue;
        }
        if konstanten.iter().any(|k| k == grund) {
            continue;
        }
        if !weltnamen.iter().any(|k| k == grund) {
            continue;
        }
        if geraete.contains(grund) {
            continue;
        }
        if aus.iter().any(|(g, _)| g == grund) {
            continue;
        }
        aus.push((grund.to_string(), *span));
    }
    aus
}

/// Direct calls of a body with their spans: statement calls and calls inside
/// expressions, over the same exhaustive walkers the graph uses. Predicate words
/// (`Has`/`Held`) are no calls. Indirect calls (`t->f()`) have no name and stand
/// apart -- the graph carries them, and E249 reads them there.
///
/// `pub(crate)`: lane 175 (`fusswache2.rs`) resolves the same call sites for `N292`.
pub(crate) fn calls_with_spans(b: &Block, aus: &mut Vec<(String, Span)>) {
    for s in &b.anweisungen {
        if let StmtArt::Ruf(r) = &s.art {
            if let Some(p) = r.path() {
                aus.push((p.text(), r.span));
            }
        }
        for e in crate::eigene_ausdruecke(s) {
            for x in crate::alle_ausdruecke(e) {
                if let ExprArt::Ruf(r) = &x.art {
                    if crate::ist_praedikatswort(r) {
                        continue;
                    }
                    if let Some(p) = r.path() {
                        aus.push((p.text(), x.span));
                    }
                }
            }
        }
        for k in crate::unterbloecke(s) {
            calls_with_spans(k, aus);
        }
    }
}

/// Every `&f` producer of the unit, by short name: the functions that can flow into
/// a pointer. Read from function bodies and `check` bodies alike -- a producer the
/// walk misses would shrink the E249 candidate set in the unsound direction.
fn address_taken(baum: &Programm) -> std::collections::BTreeSet<String> {
    let mut aus = std::collections::BTreeSet::new();
    let mut in_block = |b: &Block| {
        for s in &b.anweisungen {
            for e in crate::eigene_ausdruecke(s) {
                for x in crate::alle_ausdruecke(e) {
                    if let ExprArt::FnWert(p) = &x.art {
                        if let Some(letztes) = p.teile.last() {
                            aus.insert(letztes.text.clone());
                        }
                    }
                }
            }
            for k in crate::unterbloecke(s) {
                let mut stapel = vec![k];
                while let Some(bb) = stapel.pop() {
                    for ss in &bb.anweisungen {
                        for e in crate::eigene_ausdruecke(ss) {
                            for x in crate::alle_ausdruecke(e) {
                                if let ExprArt::FnWert(p) = &x.art {
                                    if let Some(letztes) = p.teile.last() {
                                        aus.insert(letztes.text.clone());
                                    }
                                }
                            }
                        }
                        for kk in crate::unterbloecke(ss) {
                            stapel.push(kk);
                        }
                    }
                }
            }
        }
    };
    crate::fuer_jedes_item(baum, &mut |item| match &item.art {
        ItemArt::Funktion(f) => {
            if let FnRumpf::Block(b) = &f.rumpf {
                in_block(b);
            }
        }
        ItemArt::Check(c) => in_block(&c.can_fail),
        _ => {}
    });
    aus
}

/// Whether a signature-held lock guards a carrier root: some `requires Held` lock of
/// the function whose `protects` names the root. Short names on both sides, the same
/// approximation the declaration gives `Held(L)`.
fn held_guards(
    gehalten: &[String],
    schutz: &std::collections::BTreeMap<String, Vec<String>>,
    wurzel: &str,
) -> bool {
    gehalten.iter().any(|l| {
        schutz
            .get(l)
            .is_some_and(|plaetze| plaetze.iter().any(|p| p == wurzel))
    })
}

/// **The footprint guard (E245-E249), read off `fussOrtGB` and `kandB`.**
///
/// Per function: its contract roots (E245 `requires`, E246 `ensures`), its body-read
/// roots (E247) and its direct callees' contract roots (E248) form the footprint; every
/// root some function writes must be held by signature through a guarding lock, or the
/// leg refuses. Indirect calls (E249) are admitted only where every function behind a
/// pointer keeps its contract roots inside the caller's footprint.
#[allow(clippy::too_many_arguments)]
fn footprint_against_guards(
    baum: &Programm,
    g: &crate::aufrufgraph::Graph,
    konstanten: &[String],
    weltnamen: &[String],
    schreiber: &std::collections::BTreeSet<String>,
    absagen: &mut Absagen,
) {
    let u = crate::umgebung::Umgebung::sammle(baum);
    let mut schutz: std::collections::BTreeMap<String, Vec<String>> =
        std::collections::BTreeMap::new();
    let mut geraete: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    let mut funktionen: std::collections::BTreeMap<String, FnDecl> =
        std::collections::BTreeMap::new();
    let mut kurz: std::collections::BTreeMap<String, Vec<String>> =
        std::collections::BTreeMap::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| match &item.art {
        ItemArt::Lock(l) => {
            schutz.insert(
                l.name.text.clone(),
                l.schuetzt
                    .iter()
                    .map(|o| carrier_root(&o.text()).to_string())
                    .collect(),
            );
        }
        ItemArt::Device(d) => {
            geraete.insert(d.name.text.clone());
        }
        ItemArt::Funktion(f) => {
            let schluessel = g.schluessel_von(modul, &f.name.text);
            funktionen.insert(schluessel.clone(), f.clone());
            kurz.entry(f.name.text.clone()).or_default().push(schluessel);
        }
        _ => {}
    });
    let genommen = address_taken(baum);
    // The E249 candidate pool: the functions behind a pointer where the unit takes
    // addresses, else every function of the unit (the complete member list the
    // soundness lemma quantifies over -- a pointer from outside could carry any of
    // them, and admitting on a smaller pool would be the unsound direction).
    let kandidaten: Vec<String> = if genommen.is_empty() {
        funktionen.keys().cloned().collect()
    } else {
        let mut pool = std::collections::BTreeSet::new();
        for name in &genommen {
            if let Some(schluessel) = kurz.get(name) {
                pool.extend(schluessel.iter().cloned());
            }
        }
        pool.into_iter().collect()
    };
    // Contract roots per function, memoised: callees and candidates read them often,
    // and recomputing walks every contract once per caller.
    let mut vertragskarte: std::collections::BTreeMap<String, Vec<(String, Span)>> =
        std::collections::BTreeMap::new();
    for (schluessel, f) in &funktionen {
        let mut orte = clause_roots(&f.requires, f, konstanten, weltnamen, &geraete);
        orte.extend(clause_roots(&f.ensures, f, konstanten, weltnamen, &geraete));
        let mut eng: Vec<(String, Span)> = Vec::new();
        for (w, sp) in orte {
            if eng.iter().any(|(g, _)| g == &w) {
                continue;
            }
            eng.push((w, sp));
        }
        vertragskarte.insert(schluessel.clone(), eng);
    }
    for (rufer_key, f) in &funktionen {
        let mut gehalten: Vec<String> = Vec::new();
        for p in &f.requires {
            let mut h = Vec::new();
            crate::aufrufgraph::held_aus_pred(p, &mut h);
            for (name, _geteilt) in h {
                if schutz.contains_key(&name) && !gehalten.contains(&name) {
                    gehalten.push(name);
                }
            }
        }
        let rufer = f.name.text.clone();
        let req = clause_roots(&f.requires, f, konstanten, weltnamen, &geraete);
        let ens = clause_roots(&f.ensures, f, konstanten, weltnamen, &geraete);
        let rumpf = match &f.rumpf {
            FnRumpf::Block(b) => body_roots(f, b, konstanten, weltnamen, &geraete),
            _ => Vec::new(),
        };
        // Direct callees with their call spans, resolved exactly like the graph
        // resolves them; an unresolvable path names nothing and contributes no
        // contract (its own pass refuses it elsewhere).
        let mut rufe: Vec<(String, Span)> = Vec::new();
        if let FnRumpf::Block(b) = &f.rumpf {
            calls_with_spans(b, &mut rufe);
        }
        let mut gerufene: Vec<(String, String, Span)> = Vec::new();
        for (pfad, span) in &rufe {
            if let Some(schluessel) = g.aufloesen(&u, rufer_key, pfad) {
                if funktionen.contains_key(&schluessel) {
                    let kurzname = pfad
                        .rsplit("::")
                        .next()
                        .unwrap_or(pfad)
                        .to_string();
                    gerufene.push((schluessel, kurzname, *span));
                }
            }
        }
        let mut fuss: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
        for (w, _) in req.iter().chain(ens.iter()).chain(rumpf.iter()) {
            fuss.insert(w.clone());
        }
        for (schluessel, _, _) in &gerufene {
            if let Some(orte) = vertragskarte.get(schluessel) {
                for (w, _) in orte {
                    fuss.insert(w.clone());
                }
            }
        }
        let mut gemeldet: Vec<(&str, String)> = Vec::new();
        let mut refuse = |code: &'static str,
                          wort: &str,
                          wurzel: &str,
                          span: Span,
                          extra: Option<String>,
                          absagen: &mut Absagen| {
            if !schreiber.contains(wurzel) {
                return;
            }
            if held_guards(&gehalten, &schutz, wurzel) {
                return;
            }
            let merker = (code, wurzel.to_string());
            if gemeldet.contains(&merker) {
                return;
            }
            gemeldet.push((code, wurzel.to_string()));
            let mut text = format!(
                "`{wurzel}` is read by the {wort} of `{rufer}` but no signature lock \
                 guarding it is held, and some function writes it",
            );
            if let Some(zusatz) = extra {
                text.push_str(&zusatz);
            }
            absagen.schiebe(
                Absage::hinweis(code, span, text)
                    .mit_notiz(
                        "the footprint carries what the contract saw: every written \
                         carrier wants a `requires Held(L)` guard over a `lock L \
                         protects` line, not merely a `reads` or `writes` entry in \
                         `effects`",
                    )
                    .mit_notiz(
                        "carriers no function writes need no guard; device registers \
                         read bare carry none either, until the declaration names \
                         their carriers",
                    ),
            );
        };
        for (w, sp) in &req {
            refuse("E245", "`requires`", w, *sp, None, absagen);
        }
        for (w, sp) in &ens {
            refuse("E246", "`ensures`", w, *sp, None, absagen);
        }
        for (w, sp) in &rumpf {
            refuse("E247", "body", w, *sp, None, absagen);
        }
        for (schluessel, kurzname, span) in &gerufene {
            if let Some(orte) = vertragskarte.get(schluessel) {
                for (w, _) in orte {
                    refuse(
                        "E248",
                        "contract of the callee",
                        w,
                        *span,
                        Some(format!(" (read by `{kurzname}`)")),
                        absagen,
                    );
                }
            }
        }
        // E249 -- the indirect-call admission: every candidate's contract roots must
        // lie in the caller footprint. Read at the first indirect site of the caller.
        if let Some(knoten) = g.knoten.get(rufer_key) {
            if !knoten.indirect.is_empty() {
                let span = knoten.indirect[0].span;
                for kand in &kandidaten {
                    let kname = kand
                        .rsplit("::")
                        .next()
                        .unwrap_or(kand)
                        .to_string();
                    if let Some(orte) = vertragskarte.get(kand) {
                        for (w, _) in orte {
                            if fuss.contains(w) {
                                continue;
                            }
                            let merker = ("E249", format!("{kname}:{w}"));
                            if gemeldet.contains(&merker) {
                                continue;
                            }
                            gemeldet.push(("E249", format!("{kname}:{w}")));
                            absagen.schiebe(
                                Absage::hinweis(
                                    "E249",
                                    span,
                                    format!(
                                        "the indirect call in `{rufer}` may reach `{kname}`, \
                                         whose contract reads `{w}` outside the caller \
                                         footprint",
                                    ),
                                )
                                .mit_notiz(
                                    "an indirect call is admitted only if every function \
                                     behind the pointer keeps its contract carriers inside \
                                     the caller footprint -- read the carrier in the caller \
                                     contract or body, or guard it, or write it nowhere",
                                ),
                            );
                        }
                    }
                }
            }
        }
    }
}
