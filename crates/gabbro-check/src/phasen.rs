//! **«B37» — die ORDNUNG auf einer linearen Geistmarke.**
//!
//! Das Bootfragment schreibt seinen eigenen Mangel hin (`FRAGMENTE.md`:1293–1299):
//!
//! > *„Die Marke traegt die Reihenfolge, aber sie traegt sie als **LINEARITAET**, nicht als
//! > **ORDNUNG**: `mmu_an` verbraucht die rohe Phase und gibt die gewoehnliche zurueck. Damit
//! > ist „vor der MMU" und „nach der MMU" unterscheidbar -- **aber „Cap-Tabellen vor dem
//! > ersten Cap" ist es nicht**, denn beide liegen in derselben Phase."*
//!
//! **Ein linearer Wert erzwingt eine KETTE, aber nicht WELCHE.** Bei sechs Bootschritten
//! typpruefen alle **720** Reihenfolgen; M2 sieht nur, dass jede Marke genau einmal
//! weitergereicht wird.
//!
//! ## Die Wahl, und das Fragment hatte beide genannt
//!
//! | | Preis |
//! |---|---|
//! | je Schritt eine eigene Marke | *„dann waechst der Wortschatz mit jedem Bootschritt"* |
//! | **eine Ordnung auf Marken** | **gewaehlt** -- zwei Woerter, einmal |
//!
//! ```gabbro
//! linear ghost type BootPhase order { roh, mmu, caps, eps, autoritaet, dienste };
//!
//! extern fn mmu_an(p : BootPhase) -> BootPhase
//!     advances roh -> mmu
//!     effects { consumes p, writes mmu } costs <= 4096 ops;
//! ```
//!
//! Die Stufen sind **Bezeichner in EINER Deklaration**. Der Wortschatz waechst um `order` und
//! `advances` -- einmal, nicht je Schritt.
//!
//! ## Was dieser Pass prueft, in drei Stufen
//!
//! 1. **Die Deklaration** (`O001`, `O002`): `advances a -> b` nennt Stufen, die es gibt, und
//!    geht **vorwaerts**. *Ohne die zweite Haelfte waere `order` eine Liste und keine Ordnung.*
//! 2. **Der Fluss** (`O003`): ein Schritt trifft eine Marke, die auf seiner Ausgangsstufe
//!    steht. **Das ist die Zeile, die `cap_tabellen` und `ipc_tabellen` unvertauschbar macht.**
//! 3. **Die Zusammensetzung** (`O004`): der Rumpf muss auf die Stufe kommen, die seine eigene
//!    `advances`-Zeile zusagt. *Eine Strecke, die unterwegs aufhoert, ist keine Strecke.*
//!
//! 4. **Der Zweig** (`O006`, seit K11.1): **alle Zweige erreichen dieselbe Stufe.** Ein
//!    Zweig, der mit `return` ENDET, schliesst sich nicht an -- er verlaesst die Funktion.
//!    Ein Schritt in einer **Schleife** wird abgelehnt: *ein Schritt geschieht einmal, eine
//!    Schleife oft.*
//!
//! ## `O005` ist ZURUECKGEZOGEN, und das gehoert hierher statt in eine Luecke
//!
//! Bis K11.1 stand dort ein Hinweis: *„ein Phasenschritt steht in einem Zweig -- dieser Pass
//! entscheidet das NICHT."* **Die Meldung war richtig und keine Loesung.** Sie ist durch
//! `O006` ersetzt, und der Code bleibt frei.
//!
//! > *Eine Absage, die heimlich ihre Bedeutung wechselt, ist schlimmer als eine Nummer, die
//! > ungenutzt bleibt.* Deshalb ein neuer Code und keine Umwidmung.
//!
//! ## Und was er NICHT prueft, mit seinem Grund
//!
//! **Die weichere Fassung des Zweigs ist nicht gebaut:** eine STUFENMENGE zu tragen und den
//! naechsten Schritt alle akzeptieren zu lassen. Gewaehlt ist die strenge --
//! *von ihr aus laesst sich lockern, umgekehrt nie* (`PLAN.md`, K11.1 (b)).

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};
use gabbro_syntax::span::Span;
use std::collections::{BTreeMap, BTreeSet};

/// Was eine Funktion auf einer Marke tut.
#[derive(Clone)]
struct Schritt {
    marke: String,
    von: String,
    nach: String,
}

/// **«B18»: what this body needs in order to read a phase-classed register.**
///
/// The class tables and the identifiers stay in `m3.rs` -- `pruefe-kennungen.py` allows one
/// identifier in one file, and `R005`/`R006` have lived there since «B23». What lives HERE
/// is the stage, because the stage is what this pass walks. *One register over classes, one
/// over stages, and the rule at the seam calls both.*
struct Regumfeld<'a> {
    geraete: &'a BTreeMap<String, BTreeMap<String, crate::m3::RegInfo>>,
    ordnungen: &'a BTreeMap<String, Vec<String>>,
    griffe: BTreeMap<String, String>,
    /// Local mark name -> the order it belongs to.
    marken: BTreeMap<String, String>,
}

/// Which local name carries a mark of which order? Parameters and the `let`-bound results of
/// steps. **Collected once per body and not per statement:** a name does not change the
/// order it belongs to, only the stage it stands on -- and that is what `stand` carries.
fn markenordnung(
    f: &FnDecl,
    u: &crate::umgebung::Umgebung,
    modul: &str,
    schritte: &BTreeMap<String, Schritt>,
    ordnungen: &BTreeMap<String, Vec<String>>,
) -> BTreeMap<String, String> {
    let mut m = BTreeMap::new();
    for p in &f.parameter {
        if let TypExpr::Pfad(pf) = &p.typ {
            if let Some(n) = pf.teile.last() {
                if ordnungen.contains_key(&n.text) {
                    m.insert(p.name.text.clone(), n.text.clone());
                }
            }
        }
    }
    if let FnRumpf::Block(b) = &f.rumpf {
        sammle_markenordnung(b, u, modul, schritte, &mut m);
    }
    m
}

fn sammle_markenordnung(
    b: &Block,
    u: &crate::umgebung::Umgebung,
    modul: &str,
    schritte: &BTreeMap<String, Schritt>,
    m: &mut BTreeMap<String, String>,
) {
    for s in &b.anweisungen {
        if let StmtArt::Let(l) = &s.art {
            if let ExprArt::Ruf(r) = &l.wert.art {
                if let Some(pf) = r.path() {
                    if let Some(sch) = u
                        .kandidaten_aufloesbar(modul, &pf.text())
                        .into_iter()
                        .find_map(|k| schritte.get(&k))
                    {
                        m.insert(l.name.text.clone(), sch.marke.clone());
                    }
                }
            }
        }
        for k in crate::unterbloecke(s) {
            sammle_markenordnung(k, u, modul, schritte, m);
        }
    }
}

/// **The register accesses of ONE statement, against the stage that holds before it.**
///
/// Only this statement's own places -- the descent into sub-blocks is `fluss`'s, and it
/// carries the stage that belongs to each branch.
fn registerzugriffe(
    s: &Stmt,
    umfeld: &Regumfeld<'_>,
    stand: &BTreeMap<String, String>,
    absagen: &mut Absagen,
) {
    if umfeld.griffe.is_empty() {
        return;
    }
    let pruefe = |o: &Ort, lesend: bool, absagen: &mut Absagen| {
        crate::m3::phasenzugriff(
            o,
            s.span,
            lesend,
            umfeld.geraete,
            &umfeld.griffe,
            umfeld.ordnungen,
            &umfeld.marken,
            stand,
            absagen,
        );
    };
    match &s.art {
        StmtArt::Zuweisung(z) => {
            pruefe(&z.ziel, false, absagen);
            // `X |= 1` is a read AND a write; a `class w` does not carry it.
            if !matches!(z.op, ZuwOp::Setzt) {
                pruefe(&z.ziel, true, absagen);
            }
        }
        StmtArt::Publish(pb) => pruefe(&pb.ziel, false, absagen),
        _ => {}
    }
    for e in crate::eigene_ausdruecke(s) {
        for o in crate::alle_orte(e) {
            pruefe(o, true, absagen);
        }
    }
}

pub fn pass(baum: &Programm, absagen: &mut Absagen) {
    // **Der Bootsatz haengt an derselben Marke** -- `O008`/`O009` reden ueber die lineare
    // Geistmarke, ueber die `O001`-`O007` schon reden. Ein eigener Pass waere W7: zwei
    // Register ueber einer Sache.
    bootsatz(baum, absagen);
    // **Modulbewusst seit 2026-08-19.** Zwei `oeffnen` in zwei Modulen waren EIN Schritt,
    // und welcher galt, entschied die Reihenfolge im Quelltext -- derselbe Fehler wie im
    // Aufrufgraphen, in einem siebten Pass.
    let u = crate::umgebung::Umgebung::sammle(baum);
    // 1. Die Ordnungen. Typname -> Stufen in Reihenfolge.
    let mut ordnungen: BTreeMap<String, Vec<String>> = BTreeMap::new();
    crate::fuer_jedes_item(baum, &mut |i| {
        if let ItemArt::Typ(t) = &i.art {
            if let Some(o) = &t.ordnung {
                ordnungen.insert(
                    t.name.text.clone(),
                    o.iter().map(|s| s.text.clone()).collect(),
                );
            }
        }
    });

    // 2. Die Schritte, und dabei faellt Stufe 1.
    let mut schritte: BTreeMap<String, Schritt> = BTreeMap::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |i, modul| {
        let ItemArt::Funktion(f) = &i.art else { return };
        let Some((von, nach)) = &f.advances else { return };
        // Welche Marke? Der erste Parameter, dessen Typ eine Ordnung hat.
        let marke = f.parameter.iter().find_map(|p| match &p.typ {
            TypExpr::Pfad(pf) => pf
                .teile
                .last()
                .map(|n| n.text.clone())
                .filter(|n| ordnungen.contains_key(n)),
            _ => None,
        });
        let Some(marke) = marke else {
            absagen.schiebe(
                Absage::fehler(
                    "O001",
                    f.name.span,
                    format!(
                        "`{}` promises `advances` but has no parameter of a stage-\
                            carrying type",
                        f.name.text
                    ),
                )
                .mit_notiz(
                    "a stage is a stage OF SOMETHING -- `linear ghost type` plus `order` \
                        is what carries it",
                ),
            );
            return;
        };
        let stufen = &ordnungen[&marke];
        let ix = |n: &Ident| stufen.iter().position(|s| *s == n.text);
        let (Some(a), Some(b)) = (ix(von), ix(nach)) else {
            for n in [von, nach] {
                if ix(n).is_none() {
                    absagen.schiebe(
                        Absage::fehler(
                            "O001",
                            n.span,
                            format!("`{}` has no stage `{}`", marke, n.text),
                        )
                        .mit_notiz(format!("the stages are: {}", stufen.join(", "))),
                    );
                }
            }
            return;
        };
        // **`O002` ist die Zeile, die aus einer Liste eine ORDNUNG macht.**
        if a >= b {
            absagen.schiebe(
                Absage::fehler(
                    "O002",
                    f.name.span,
                    format!(
                        "`{}` goes from `{}` to `{}` -- that is not a step forward",
                        f.name.text, von.text, nach.text
                    ),
                )
                .mit_notiz(format!("the order is: {}", stufen.join(" -> ")))
                .mit_notiz(
                    "without this check `order` would be a list and not an order",
                ),
            );
            return;
        }
        schritte.insert(
            crate::umgebung::qualifiziere(modul, &f.name.text),
            Schritt {
                marke,
                von: von.text.clone(),
                nach: nach.text.clone(),
            },
        );
    });

    // **«B18», 2026-08-28: the class per phase.** The declaration first -- a stage that does
    // not exist makes every statement about an access to it worthless.
    crate::m3::phasendeklarationen(baum, &ordnungen, absagen);
    let geraete = crate::m3::geraetetabelle(baum);
    let phasenregister = geraete
        .values()
        .any(|regs| regs.values().any(|i| !i.phasen.is_empty()));

    // **Without a step AND without a phase-classed register there is nothing to say.** Until
    // today only the first half stood here -- and a unit with a phase-classed register but no
    // `advances` would have run through unchecked, though that is exactly where the
    // intersection over all stages bites.
    if schritte.is_empty() && !phasenregister {
        return;
    }

    // 3. Der Fluss, je Rumpf.
    crate::fuer_jedes_item_im_modul(baum, &mut |i, modul| {
        let ItemArt::Funktion(f) = &i.art else { return };
        let FnRumpf::Block(rumpf) = &f.rumpf else { return };
        let umfeld = Regumfeld {
            geraete: &geraete,
            ordnungen: &ordnungen,
            griffe: crate::m3::griffe_von(f, &geraete),
            marken: markenordnung(f, &u, modul, &schritte, &ordnungen),
        };
        let Some(eigen) = schritte.get(&crate::umgebung::qualifiziere(modul, &f.name.text)) else {
            // Ein Rumpf ohne eigene `advances`-Zeile darf trotzdem Schritte tun -- dann ist
            // nur nichts zugesagt, was am Ende zu erreichen waere.
            //
            // **«B18»: and its marks stand on an UNDETERMINED stage.** `stand` stays empty,
            // so what holds at the register is what every stage permits -- not a guessed one.
            let mut stand = BTreeMap::new();
            fluss(rumpf, &u, modul, &schritte, &mut stand, absagen, false, &umfeld);
            return;
        };
        let mut stand: BTreeMap<String, String> = BTreeMap::new();
        for p in &f.parameter {
            if let TypExpr::Pfad(pf) = &p.typ {
                if pf.teile.last().map(|n| n.text.as_str()) == Some(eigen.marke.as_str()) {
                    stand.insert(p.name.text.clone(), eigen.von.clone());
                }
            }
        }
        let erreicht = fluss(rumpf, &u, modul, &schritte, &mut stand, absagen, true, &umfeld);
        // **`O004`.** Eine Strecke, die unterwegs aufhoert, ist keine Strecke.
        if let Some(letzte) = erreicht {
            if letzte != eigen.nach {
                absagen.schiebe(
                    Absage::fehler(
                        "O004",
                        f.name.span,
                        format!(
                            "`{}` promises `{} -> {}`, the body reaches `{}`",
                            f.name.text, eigen.von, eigen.nach, letzte
                        ),
                    )
                    .mit_notiz(
                        "the steps of the body must compose into the promise -- otherwise \
                            the declaration says something the body does not do",
                    ),
                );
            }
        }
    });
}

/// Verfolgt die Stufe je Marke durch einen Block. Gibt die zuletzt erreichte Stufe zurueck.
#[allow(clippy::too_many_arguments)]
fn fluss(
    b: &Block,
    u: &crate::umgebung::Umgebung,
    modul: &str,
    schritte: &BTreeMap<String, Schritt>,
    stand: &mut BTreeMap<String, String>,
    absagen: &mut Absagen,
    melden: bool,
    umfeld: &Regumfeld<'_>,
) -> Option<String> {
    let mut zuletzt = None;
    for s in &b.anweisungen {
        // **«B18»: BEFORE the statement takes effect.** A read in the initializer of
        // `let r = schritt(p);` happens while the mark still stands on the old stage.
        registerzugriffe(s, umfeld, stand, absagen);
        match &s.art {
            StmtArt::Let(l) => {
                if let ExprArt::Ruf(r) = &l.wert.art {
                    if let Some(neu) = anwenden(r, u, modul, schritte, stand, absagen) {
                        stand.insert(l.name.text.clone(), neu.clone());
                        zuletzt = Some(neu);
                    }
                }
            }
            StmtArt::Ruf(r) => {
                if let Some(neu) = anwenden(r, u, modul, schritte, stand, absagen) {
                    zuletzt = Some(neu);
                }
            }
            // **A step in a `return` was INVISIBLE** (2026-08-24). The walker handled `let`
            // and the bare call and stopped there -- so
            //
            //     impl fn f(p) -> P advances roh -> bereit { return schritt(p); }
            //
            // where `schritt` advances `roh -> mmu` passed with **zero errors**, while the
            // SAME lie written as `let q = schritt(p); return q;` fell at `O004`.
            //
            // > *Two bodies of identical meaning, one caught and one not, purely by where the
            // > call sits.* The same shape as the `else if` under-count in `kosten.rs`, and
            // > found the same way: by asking what the pass does NOT descend into (W16).
            StmtArt::Return(Some(e)) => {
                if let ExprArt::Ruf(r) = &e.art {
                    if let Some(neu) = anwenden(r, u, modul, schritte, stand, absagen) {
                        zuletzt = Some(neu);
                    }
                }
            }
            // **Ein `locks`-Block ist kein Zweig.** Er wird durchlaufen wie gerader Code --
            // und mit ihm `breaking`, `observes` und der `update`-Rumpf eines `exchange`.
            // *Vier Formen, eine Aussage; bis 2026-08-19 stand nur die erste hier.*
            StmtArt::Sperrt(_)
            | StmtArt::Bricht(_)
            | StmtArt::Observiert(_)
            | StmtArt::Exchange(_) => {
                for k in crate::unterbloecke(s) {
                    if let Some(n) = fluss(k, u, modul, schritte, stand, absagen, melden, umfeld) {
                        zuletzt = Some(n);
                    }
                }
            }
            // **Ein `else`-Zweig ist ein AUSWEG, kein Weiterweg.** `narrow … else` und
            // `let … else` verlassen den Hauptpfad; ihr Stand joint nicht zurück, und ein
            // Schritt darin wird trotzdem geprüft -- vorher wurde er gar nicht angesehen.
            StmtArt::Narrow(_) | StmtArt::LetSonst(_) => {
                for k in crate::unterbloecke(s) {
                    let mut ausweg = stand.clone();
                    fluss(k, u, modul, schritte, &mut ausweg, absagen, melden, umfeld);
                }
            }
            // **K11.1: die Zweige muessen sich EINIGEN** (`O006`).
            //
            // Bis zum 2026-08-17 stand hier `O005` -- ein Hinweis: *„ein Phasenschritt steht
            // in einem Zweig, und dieser Pass entscheidet das nicht."* **Die Meldung war
            // richtig und keine Loesung.**
            //
            // Gewaehlt ist die strenge Fassung: *alle Zweige muessen dieselbe Stufe
            // erreichen.* Ein Bootpfad, der je nach Zweig woanders endet, ist zwei Bootpfade.
            //
            // > **Wer streng anfaengt, kann spaeter lockern; wer permissiv anfaengt, kann nie
            // > mehr verschaerfen.** Die weichere Fassung -- eine STUFENMENGE tragen und den
            // > naechsten Schritt alle akzeptieren lassen -- bleibt moeglich und ist in
            // > `PLAN.md` (K11.1) als (b) benannt.
            StmtArt::Wenn(w) => {
                let mut zweige: Vec<(BTreeMap<String, String>, Span)> = Vec::new();
                for (_, r) in &w.zweige {
                    let mut k = stand.clone();
                    fluss(r, u, modul, schritte, &mut k, absagen, melden, umfeld);
                    if !crate::endet_immer(r, &[]) {
                        zweige.push((k, r.span));
                    }
                }
                // **Ein `if` ohne `else` hat einen unsichtbaren zweiten Zweig**, und der
                // aendert nichts. Ihn zu vergessen hiesse, den haeufigsten Fall zu uebersehen.
                match &w.sonst {
                    Some(r) => {
                        let mut k = stand.clone();
                        fluss(r, u, modul, schritte, &mut k, absagen, melden, umfeld);
                        if !crate::endet_immer(r, &[]) {
                            zweige.push((k, r.span));
                        }
                    }
                    // **Ein `if` ohne `else` hat einen unsichtbaren zweiten Zweig**, und der
                    // aendert nichts. Ihn zu vergessen hiesse, den haeufigsten Fall zu
                    // uebersehen -- er faellt aber weg, wenn ALLE `if`-Zweige enden.
                    None => zweige.push((stand.clone(), s.span)),
                }
                if let Some(neu) = einigen(&zweige, s.span, absagen, "Zweige eines `if`") {
                    *stand = neu;
                }
            }
            StmtArt::Match(m) => {
                let mut zweige: Vec<(BTreeMap<String, String>, Span)> = Vec::new();
                for z in &m.zweige {
                    let mut k = stand.clone();
                    fluss(&z.rumpf, u, modul, schritte, &mut k, absagen, melden, umfeld);
                    if !crate::endet_immer(&z.rumpf, &[]) {
                        zweige.push((k, z.rumpf.span));
                    }
                }
                if let Some(neu) = einigen(&zweige, s.span, absagen, "Zweige eines `match`") {
                    *stand = neu;
                }
            }
            // **Ein Schritt geschieht EINMAL, eine Schleife oft.** Hier wird nicht geeinigt,
            // sondern abgelehnt: eine Stufe, die ein Durchgang weiterschiebt, ist nach zwei
            // Durchgaengen eine andere -- und wie viele es sind, entscheidet die Laufzeit.
            StmtArt::Schleife(sch) => {
                let rumpf = match sch.as_ref() {
                    Schleife::Traverse(t) => &t.rumpf,
                    Schleife::Retry(r) => &r.rumpf,
                    Schleife::Forever(f) => &f.rumpf,
                };
                if enthaelt_schritt(s, u, modul, schritte) {
                    absagen.schiebe(
                        Absage::fehler(
                            "O006",
                            s.span,
                            "a phase step stands inside a loop",
                        )
                        .mit_notiz(
                            "a step happens once, a loop often -- after two passes the \
                                mark would stand two stages further",
                        ),
                    );
                } else {
                    let mut k = stand.clone();
                    fluss(rumpf, u, modul, schritte, &mut k, absagen, melden, umfeld);
                }
            }
            _ => {}
        }
    }
    zuletzt
}

/// **Ein Zweig, der ENDET, schliesst sich nicht an.**
///
/// `if k { let x = a(p); return x; }` hat nach dem `if` keinen zweiten Stand -- der Zweig
/// verlaesst die Funktion. Ihn in die Einigung zu nehmen hiesse, den haeufigsten sauberen
/// Fall abzulehnen.
///
/// > **Das fand die erste Probe, und zwar in der GEGENRICHTUNG:** die Giftprobe fiel wie
/// > gewollt, und die SAUBERE fiel mit. *Ein Tor, das nur in eine Richtung geprueft wird,
/// > misst die Haelfte.*

/// **Die Einigung der Zweige** (`O006`) -- K11.1.
///
/// Alle Zweige muessen denselben Stand hinterlassen. Das ist die strenge Fassung, und sie ist
/// mit Absicht die strenge: *ein Bootpfad, der je nach Zweig woanders endet, ist zwei
/// Bootpfade.*
///
/// Verglichen wird der ganze Stand, nicht nur die zuletzt erreichte Stufe -- **zwei Marken in
/// einem Rumpf sind moeglich**, und eine Einigung, die nur eine ansieht, ist keine.
fn einigen(
    zweige: &[(BTreeMap<String, String>, Span)],
    span: Span,
    absagen: &mut Absagen,
    was: &str,
) -> Option<BTreeMap<String, String>> {
    let (erster, _) = zweige.first()?;
    for (k, wo) in &zweige[1..] {
        if k != erster {
            let zeig = |m: &BTreeMap<String, String>| {
                if m.is_empty() {
                    "keine Marke".to_string()
                } else {
                    m.iter()
                        .map(|(n, st)| format!("{n} auf {st}"))
                        .collect::<Vec<_>>()
                        .join(", ")
                }
            };
            absagen.schiebe(
                Absage::fehler(
                    "O006",
                    *wo,
                    format!("the {was} bring the mark to different stages"),
                )
                .mit_notiz(format!("here: {}", zeig(k)))
                .mit_notiz(format!("anderswo: {}", zeig(erster)))
                .mit_notiz(
                    "the strict reading is chosen: all branches reach the same stage. \
                        From strict one can loosen, never the other way",
                ),
            );
            let _ = span;
            return None;
        }
    }
    Some(erster.clone())
}

/// Wendet einen Ruf auf den Stand an. `None`, wenn er kein Schritt ist.
fn anwenden(
    r: &Ruf,
    u: &crate::umgebung::Umgebung,
    modul: &str,
    schritte: &BTreeMap<String, Schritt>,
    stand: &mut BTreeMap<String, String>,
    absagen: &mut Absagen,
) -> Option<String> {
    // **An indirect call advances no mark.** `advances a -> b` stands at an `fn`
    // DECLARATION and has no place in a `fn(…)` type -- the grammar does not admit it, and
    // this `?` is therefore a fact about the language, not a shortcut past a case.
    let name = r.path()?.teile.last()?.text.clone();
    let sch = u
        .kandidaten_aufloesbar(modul, &r.path()?.text())
        .into_iter()
        .find_map(|k| schritte.get(&k))?;
    // Welches Argument ist die Marke? Das erste, dessen Name einen Stand hat.
    let arg = r.argumente.iter().find_map(|a| match &a.art {
        ExprArt::Ort(o) if o.suffixe.is_empty() => stand
            .get(&o.basis.text)
            .map(|st| (o.basis.text.clone(), st.clone(), o.span)),
        _ => None,
    });
    let (marke, ist, span) = match arg {
        Some(x) => x,
        // Ohne bekannten Stand wird nichts behauptet -- das ist der Fall „die Marke kommt
        // von aussen und der Rufer sagt nichts zu".
        None => return Some(sch.nach.clone()),
    };
    // **`O003` -- die Zeile, die die 720 Reihenfolgen auf eine reduziert.**
    if ist != sch.von {
        absagen.schiebe(
            Absage::fehler(
                "O003",
                span,
                format!(
                    "`{name}` presupposes `{}`, `{marke}` stands at `{ist}`",
                    sch.von
                ),
            )
            .mit_notiz(
                "a linear value forces a CHAIN, but not WHICH -- the stage is what says \
                    where in the chain one stands",
            ),
        );
        return None;
    }
    stand.remove(&marke);
    Some(sch.nach.clone())
}

fn enthaelt_schritt(
    s: &Stmt,
    u: &crate::umgebung::Umgebung,
    modul: &str,
    schritte: &BTreeMap<String, Schritt>,
) -> bool {
    // **Tief, und ueber die erschoepfenden Laeufer** (Rezension 2026-08-20).
    //
    // Vorher wurden nur die Anweisungen der OBERSTEN Ebene des Schleifenrumpfs angesehen,
    // und von denen nur `Ruf` und ein `Let` mit direktem Ruf. Ein `locks { }` um denselben
    // Schritt genuegte, damit `O006` schwieg:
    //
    // ```gabbro
    // retry … { locks L { boot_schritt(); } }      -- 0 Fehler
    // retry … { boot_schritt(); }                  -- O006
    // ```
    //
    // > *Eine Regel, die an der Einrueckung endet, ist keine Regel ueber den Fluss.*
    fn ist_schritt(
        r: &Ruf,
        u: &crate::umgebung::Umgebung,
        modul: &str,
        schritte: &BTreeMap<String, Schritt>,
    ) -> bool {
        // **An indirect call is never a phase step.** A step is a function that carries
        // `advances a -> b`, that clause stands at an `fn` DECLARATION, and the grammar
        // admits none at a `fn(…)` type. *So `false` here is a fact about the language, not a
        // pass declining to look.*
        let Some(p) = r.path() else {
            return false;
        };
        u.kandidaten_aufloesbar(modul, &p.text())
            .into_iter()
            .any(|k| schritte.contains_key(&k))
    }
    fn im_block(
        b: &Block,
        u: &crate::umgebung::Umgebung,
        modul: &str,
        schritte: &BTreeMap<String, Schritt>,
    ) -> bool {
        for k in &b.anweisungen {
            if let StmtArt::Ruf(r) = &k.art {
                if ist_schritt(r, u, modul, schritte) {
                    return true;
                }
            }
            for e in crate::eigene_ausdruecke(k) {
                for x in crate::alle_ausdruecke(e) {
                    if let ExprArt::Ruf(r) = &x.art {
                        if ist_schritt(r, u, modul, schritte) {
                            return true;
                        }
                    }
                }
            }
            for pr in crate::eigene_praedikate(k) {
                for e in crate::ausdruecke_im_praedikat(pr) {
                    for x in crate::alle_ausdruecke(e) {
                        if let ExprArt::Ruf(r) = &x.art {
                            if ist_schritt(r, u, modul, schritte) {
                                return true;
                            }
                        }
                    }
                }
            }
            for inner in crate::unterbloecke(k) {
                if im_block(inner, u, modul, schritte) {
                    return true;
                }
            }
        }
        false
    }
    crate::unterbloecke(s)
        .into_iter()
        .any(|b| im_block(b, u, modul, schritte))
}

/// **The boot theorem, layer S1 and half of S2 -- and `raw fn` had NO reader at all.**
///
/// `SPRACHE.md` §12 states the theorem in three layers: *"after `boot_end` no `raw` code is
/// reachable."* Measured on 2026-08-28: `FnKlasse::Raw` is matched by **zero** passes. `raw fn`
/// parsed, was stored, and no rule attached to it -- **the same class as `@version` and as
/// `obermenge`/`gates`/`mirrors` before «K5».** A word that promises a discipline and is read by
/// nobody is worse than no word: it reads like protection.
///
/// * **`O008` (layer S1, types)** -- a `raw fn` carries `requires T` with `T` a declared
///   `linear ghost type`. The token is what makes the code unreachable later: it is linear, so
///   it cannot be copied and cannot be restored, and whoever consumes it ends the boot phase.
///   *Without the clause a `raw fn` is callable forever, and the theorem is about nothing.*
/// * **`O009` (layer S2, references)** -- `&f` on a `raw fn` is refused. A function pointer to
///   boot code survives the token: the call would no longer type, but the JUMP would still
///   stand. **S1 alone catches the static call chain and not the dynamic one** -- that is why
///   `SPRACHE.md` gives it its own layer, and why it costs a second rule and not a note.
///
/// * **`O010`–`O012` (layer S3, hardware)** -- the `retires` clause, built 2026-08-28. It is
///   ONE clause with three parts, and that is the whole point: `SPRACHE.md` §12 demands that
///   `boot_end` consume the token **and** remove the mapping of `.boot` as **one event**, and
///   *two promises one can keep separately are not one*. So the clause names the token, the
///   address space and the falsifier together, `O011` holds it against the `effects` block, and
///   `O012` demands the `walk` fact that says what is gone.
///
/// > **Which half is a proof duty and which an assumption, and the line runs through the
/// > middle of the clause.** The postcondition `!exists m in mappings of root : …` is a
/// > statement about a DATA STRUCTURE the checker knows -- it is formulable, it is demanded
/// > (`O012`), and it is owed. That the absence of a mapping makes the bytes UNREACHABLE is a
/// > statement about the MMU and the TLB; no pass will ever see it. That half is booked in
/// > `gabbro annahmen` out of this clause, with the probe the clause names -- an access to a
/// > `.boot` address after `boot_end` must fault.
pub fn bootsatz(baum: &Programm, absagen: &mut Absagen) {
    // Die linearen Geistmarken -- Modul-uebergreifend, wie `ordnungen` oben.
    let mut marken: BTreeSet<String> = BTreeSet::new();
    crate::fuer_jedes_item(baum, &mut |i| {
        if let ItemArt::Typ(t) = &i.art {
            if t.linear && t.ghost {
                marken.insert(t.name.text.clone());
            }
        }
    });
    // Welche Funktionen sind `raw`? Fuer `O009` -- der Name genuegt, ein Zeiger auf einen
    // fremden `raw`-Rumpf ist derselbe Sprung.
    let mut rohe: BTreeSet<String> = BTreeSet::new();
    crate::fuer_jedes_item(baum, &mut |i| {
        if let ItemArt::Funktion(f) = &i.art {
            if f.klasse == Some(FnKlasse::Raw) {
                rohe.insert(f.name.text.clone());
            }
        }
    });

    crate::fuer_jedes_item(baum, &mut |i| {
        let ItemArt::Funktion(f) = &i.art else { return };
        if f.klasse != Some(FnKlasse::Raw) {
            return;
        }
        let hat_marke = f.requires.iter().any(|p| nennt_marke(p, &marken));
        if !hat_marke {
            absagen.schiebe(
                Absage::fehler(
                    "O008",
                    f.name.span,
                    format!(
                        "`raw fn {}` demands no `linear ghost` token",
                        f.name.text
                    ),
                )
                .mit_notiz(
                    "the boot theorem (SPRACHE.md §12, layer S1) rests on it: the token is \
                     linear, so it cannot be copied and cannot be restored, and whoever \
                     consumes it ends the boot phase. Without `requires <token>` this \
                     function stays callable forever -- write `requires BootPhase` or \
                     whatever the module's token is called",
                ),
            );
        }
    });

    schicht_s3(baum, &marken, absagen);

    // `O009`: `&f` auf eine `raw fn`.
    if rohe.is_empty() {
        return;
    }
    crate::fuer_jedes_item(baum, &mut |i| {
        let ItemArt::Funktion(f) = &i.art else { return };
        let FnRumpf::Block(b) = &f.rumpf else { return };
        im_block_fnwert(b, &rohe, absagen);
    });
}

/// **Layer S3 -- the `retires` clause, and why it is ONE clause and not three.**
///
/// `SPRACHE.md` §12 states the demand in five words: `boot_end` consumes the token **and**
/// removes the mapping of `.boot`, **one event**. The tempting build is two clauses --
/// `effects { consumes t }` plus something that says "and unmap". **That build is wrong, and
/// the reason is mechanical rather than aesthetic:** each of the two is satisfiable alone, so
/// a function that keeps only the first is a well-typed function that ends the boot phase for
/// the type checker and leaves the bytes mapped. *That is exactly the state `beispiele/07`
/// was in until today* -- `effects { consumes t, writes code_abbildung }`, an effect NAME
/// beside the consumption, checked by nobody, satisfiable by anything.
///
/// So the event is one clause with three parts, and the three rules hold it together:
///
/// | | |
/// |---|---|
/// | **`O010`** | a token a `raw fn` demands is retired by **no** function -- layer S3 has no event at all |
/// | **`O011`** | the clause and the `effects` block name **different** tokens -- then they are two promises again |
/// | **`O012`** | no postcondition over `mappings of` says WHAT disappeared -- `retires` would be a name and not a mechanism |
///
/// **What this pass does NOT do, and it is the larger half.** It does not check that the
/// mapping really goes away, and it cannot: `boot_end` has no body, and even with one the
/// statement "no mapping, therefore not reachable" is about the MMU and the TLB. That half
/// leaves the checker and enters the axiom layer -- `manifest.rs::stilllegungsannahme` books
/// it out of this very clause, with the probe the clause names. *`O012` demands the
/// formulable half; the probe carries the rest, and the manifest says which is which.*
fn schicht_s3(baum: &Programm, marken: &BTreeSet<String>, absagen: &mut Absagen) {
    // Which token does a `raw fn` demand? The site is carried along so that `O010` refuses
    // where the unprotected code stands -- not at a module boundary.
    let mut verlangt: BTreeMap<String, (String, Span)> = BTreeMap::new();
    // Which token does somebody retire? The type name of the parameter the clause names.
    let mut stillgelegt: BTreeSet<String> = BTreeSet::new();

    crate::fuer_jedes_item(baum, &mut |i| {
        let ItemArt::Funktion(f) = &i.art else { return };
        if f.klasse == Some(FnKlasse::Raw) {
            for p in &f.requires {
                sammle_marken(p, marken, &mut |m| {
                    verlangt
                        .entry(m)
                        .or_insert_with(|| (f.name.text.clone(), f.name.span));
                });
            }
        }
        if let Some(st) = &f.retires {
            if let Some(t) = markentyp(f, &st.marke.text, marken) {
                stillgelegt.insert(t);
            }
        }
    });

    // **`O011` and `O012` -- at the clause itself.**
    crate::fuer_jedes_item(baum, &mut |i| {
        let ItemArt::Funktion(f) = &i.art else { return };
        let Some(st) = &f.retires else { return };
        let name = &st.marke.text;

        // The clause names a parameter of a declared `linear ghost type` ...
        if markentyp(f, name, marken).is_none() {
            absagen.schiebe(
                Absage::fehler(
                    "O011",
                    st.marke.span,
                    format!("`retires {name}` names no parameter of a `linear ghost type`"),
                )
                .mit_notiz(
                    "the retirement ends a TOKEN, and the token is what makes the boot code \
                     unreachable afterwards: it is linear, so it cannot be copied and cannot \
                     be restored. A retirement of something else ends nothing",
                ),
            );
            return;
        }
        // ... and the SAME token stands as `consumes` in the effects. **This is the line that
        // makes one promise out of two:** without it the clause may retire a token the
        // function does not consume at all -- and then the unmapping stands beside a token
        // that lives on.
        let verbraucht = f.effects.as_ref().is_some_and(|w| {
            w.liste.iter().any(|e| match &e.art {
                WirkungArt::Verbraucht(o) => o.suffixe.is_empty() && o.basis.text == *name,
                _ => false,
            })
        });
        if !verbraucht {
            absagen.schiebe(
                Absage::fehler(
                    "O011",
                    st.span,
                    format!(
                        "`{}` retires `{name}`, and its `effects` do not consume `{name}`",
                        f.name.text
                    ),
                )
                .mit_notiz(
                    "consuming the token and unmapping the space are ONE event (SPRACHE.md \
                     §12, layer S3) -- two promises one can keep separately are not one",
                )
                .mit_notiz(format!(
                    "the effects list must carry `consumes {name}` -- the same name the \
                     clause names, not another one"
                )),
            );
        }

        // **`O012` -- the event must say WHAT disappears.**
        if !f.ensures.iter().any(nennt_abbildungen_verneinend) {
            absagen.schiebe(
                Absage::fehler(
                    "O012",
                    st.span,
                    format!(
                        "`{}` retires an address space and no postcondition says what is gone",
                        f.name.text
                    ),
                )
                .mit_notiz(
                    "SPRACHE.md §12 gives the shape: `ensures !exists m in mappings of \
                     <root> : <m lies in the retired space>` -- a `walk` fact, and the one \
                     half of layer S3 that is FORMULABLE at all",
                )
                .mit_notiz(
                    "without it `retires` is an effect name beside a consumption, which is \
                     the state this rule was built against",
                ),
            );
        }
    });

    // **`O010` -- the token without an event.**
    for (marke, (wo, span)) in &verlangt {
        if stillgelegt.contains(marke) {
            continue;
        }
        absagen.schiebe(
            Absage::fehler(
                "O010",
                *span,
                format!("`raw fn {wo}` demands `{marke}`, and no function retires it"),
            )
            .mit_notiz(
                "layer S1 makes the boot code untypable after the token is consumed. That \
                 the BYTES also stop being reachable is layer S3, and it needs an event: \
                 `retires <token> from boot falsifier <probe>` at the function that ends the \
                 boot phase",
            )
            .mit_notiz(
                "a token that is consumed somewhere and retires nothing leaves `.boot` \
                 mapped -- and the theorem of SPRACHE.md §12 then talks about the call graph \
                 and not about the machine",
            ),
        );
    }
}

/// The type name of the parameter `name`, if it is a declared `linear ghost type`.
fn markentyp(f: &FnDecl, name: &str, marken: &BTreeSet<String>) -> Option<String> {
    f.parameter.iter().find_map(|p| {
        if p.name.text != name {
            return None;
        }
        match &p.typ {
            TypExpr::Pfad(pf) => pf
                .teile
                .last()
                .map(|n| n.text.clone())
                .filter(|n| marken.contains(n)),
            _ => None,
        }
    })
}

/// Does this `requires` predicate name a declared token? Like `nennt_marke`, but collecting.
fn sammle_marken(p: &Pred, marken: &BTreeSet<String>, aus: &mut impl FnMut(String)) {
    match &p.art {
        PredArt::Vergleich(e) => {
            if let ExprArt::Ort(o) = &e.art {
                if o.suffixe.is_empty() && marken.contains(&o.basis.text) {
                    aus(o.basis.text.clone());
                }
            }
        }
        PredArt::Klammer(inner) => sammle_marken(inner, marken, aus),
        PredArt::Und(a, b) => {
            sammle_marken(a, marken, aus);
            sammle_marken(b, marken, aus);
        }
        _ => {}
    }
}

/// **A NEGATIVE statement over `mappings of`** -- and the negation is half the rule.
///
/// `SPRACHE.md` §12 writes the postcondition as `!exists m in mappings of kernel_root :
/// m.section == boot`. Both usual spellings count -- `!exists … : p` and `forall … : ¬p` are
/// the same thing, and a rule that admits only one of them refuses a correct form (W22).
///
/// > **What is NOT checked here, and it stands in `saetze.rs` as the reservation:** whether
/// > the statement really covers the retired space. The pass sees the DOMAIN and the
/// > negation; that `m.rahmen >= BOOT_UNTEN && m.rahmen < BOOT_OBEN` means the boot frames it
/// > does not see. *That is the same coarseness `maintains` has -- the clause must name
/// > something, and whether it names the right thing is read by a human.*
fn nennt_abbildungen_verneinend(p: &Pred) -> bool {
    match &p.art {
        // `!exists m in mappings of w : …`
        PredArt::Nicht(inner) => ueber_abbildungen(inner),
        PredArt::Klammer(inner) => nennt_abbildungen_verneinend(inner),
        PredArt::Und(a, b) | PredArt::Oder(a, b) => {
            nennt_abbildungen_verneinend(a) || nennt_abbildungen_verneinend(b)
        }
        // `forall m in mappings of w : <etwas Verneinendes>`
        PredArt::Quantor(q) => {
            q.art == QuantorArt::Alle
                && matches!(q.domaene, Domaene::AbbildungenVon(_))
                && verneinend(&q.rumpf)
        }
        _ => false,
    }
}

/// Does this predicate quantify over `mappings of`?
fn ueber_abbildungen(p: &Pred) -> bool {
    match &p.art {
        PredArt::Quantor(q) => matches!(q.domaene, Domaene::AbbildungenVon(_)),
        PredArt::Klammer(inner) => ueber_abbildungen(inner),
        _ => false,
    }
}

/// Does this predicate DENY something? `!p`, `a != b`, and the connectives above them.
fn verneinend(p: &Pred) -> bool {
    match &p.art {
        PredArt::Nicht(_) => true,
        PredArt::Vergleich(e) => ungleich(e),
        PredArt::Klammer(inner) => verneinend(inner),
        PredArt::Und(a, b) | PredArt::Oder(a, b) => verneinend(a) || verneinend(b),
        // `p => !q` -- the restricted case, and it is the commonest one in a real table:
        // *over the boot frames no mapping holds.*
        PredArt::Folgt(_, b) => verneinend(b),
        _ => false,
    }
}

fn ungleich(e: &Expr) -> bool {
    match &e.art {
        ExprArt::Binaer(op, _, _) => *op == BinOp::Ungleich,
        ExprArt::Klammer(inner) => ungleich(inner),
        _ => false,
    }
}

fn im_block_fnwert(b: &Block, rohe: &BTreeSet<String>, absagen: &mut Absagen) {
    for s in &b.anweisungen {
        for e in crate::eigene_ausdruecke(s) {
            for sub in crate::alle_ausdruecke(e) {
                let ExprArt::FnWert(pf) = &sub.art else { continue };
                let Some(n) = pf.teile.last() else { continue };
                if !rohe.contains(&n.text) {
                    continue;
                }
                absagen.schiebe(
                    Absage::fehler(
                        "O009",
                        sub.span,
                        format!("`&{}` makes a pointer to a `raw fn`", n.text),
                    )
                    .mit_notiz(
                        "the boot theorem's layer S2: a function pointer into boot code \
                         SURVIVES the token. After `boot_end` the call would no longer type, \
                         and the jump would still stand -- that is the reachability S1 cannot \
                         see",
                    ),
                );
            }
        }
        for ub in crate::unterbloecke(s) {
            im_block_fnwert(ub, rohe, absagen);
        }
    }
}

/// `requires BootPhase` steht als blosser Ort in einem Vergleich -- ein Praedikat ohne
/// Operator. Klammer/Und werden mitgelesen, damit `requires (BootPhase) && p` nicht durchfaellt.
fn nennt_marke(p: &Pred, marken: &BTreeSet<String>) -> bool {
    match &p.art {
        PredArt::Vergleich(e) => match &e.art {
            ExprArt::Ort(o) => o.suffixe.is_empty() && marken.contains(&o.basis.text),
            _ => false,
        },
        PredArt::Klammer(inner) => nennt_marke(inner, marken),
        PredArt::Und(a, b) => nennt_marke(a, marken) || nennt_marke(b, marken),
        _ => false,
    }
}
