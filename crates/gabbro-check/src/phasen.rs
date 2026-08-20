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
use std::collections::BTreeMap;

/// Was eine Funktion auf einer Marke tut.
#[derive(Clone)]
struct Schritt {
    marke: String,
    von: String,
    nach: String,
}

pub fn pass(baum: &Programm, absagen: &mut Absagen) {
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
                    "a stage is a stage OF SOMETHING -- `linear ghost type` plus `order`\
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

    if schritte.is_empty() {
        return;
    }

    // 3. Der Fluss, je Rumpf.
    crate::fuer_jedes_item_im_modul(baum, &mut |i, modul| {
        let ItemArt::Funktion(f) = &i.art else { return };
        let FnRumpf::Block(rumpf) = &f.rumpf else { return };
        let Some(eigen) = schritte.get(&crate::umgebung::qualifiziere(modul, &f.name.text)) else {
            // Ein Rumpf ohne eigene `advances`-Zeile darf trotzdem Schritte tun -- dann ist
            // nur nichts zugesagt, was am Ende zu erreichen waere.
            let mut stand = BTreeMap::new();
            fluss(rumpf, &u, modul, &schritte, &mut stand, absagen, false);
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
        let erreicht = fluss(rumpf, &u, modul, &schritte, &mut stand, absagen, true);
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
fn fluss(
    b: &Block,
    u: &crate::umgebung::Umgebung,
    modul: &str,
    schritte: &BTreeMap<String, Schritt>,
    stand: &mut BTreeMap<String, String>,
    absagen: &mut Absagen,
    melden: bool,
) -> Option<String> {
    let mut zuletzt = None;
    for s in &b.anweisungen {
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
            // **Ein `locks`-Block ist kein Zweig.** Er wird durchlaufen wie gerader Code --
            // und mit ihm `breaking`, `observes` und der `update`-Rumpf eines `exchange`.
            // *Vier Formen, eine Aussage; bis 2026-08-19 stand nur die erste hier.*
            StmtArt::Sperrt(_)
            | StmtArt::Bricht(_)
            | StmtArt::Observiert(_)
            | StmtArt::Exchange(_) => {
                for k in crate::unterbloecke(s) {
                    if let Some(n) = fluss(k, u, modul, schritte, stand, absagen, melden) {
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
                    fluss(k, u, modul, schritte, &mut ausweg, absagen, melden);
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
                    fluss(r, u, modul, schritte, &mut k, absagen, melden);
                    if !crate::endet_immer(r, &[]) {
                        zweige.push((k, r.span));
                    }
                }
                // **Ein `if` ohne `else` hat einen unsichtbaren zweiten Zweig**, und der
                // aendert nichts. Ihn zu vergessen hiesse, den haeufigsten Fall zu uebersehen.
                match &w.sonst {
                    Some(r) => {
                        let mut k = stand.clone();
                        fluss(r, u, modul, schritte, &mut k, absagen, melden);
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
                    fluss(&z.rumpf, u, modul, schritte, &mut k, absagen, melden);
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
                    fluss(rumpf, u, modul, schritte, &mut k, absagen, melden);
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
                    "the strict reading is chosen: all branches reach the same stage.\
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
    let name = r.pfad.teile.last()?.text.clone();
    let sch = u
        .kandidaten_aufloesbar(modul, &r.pfad.text())
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
        u.kandidaten_aufloesbar(modul, &r.pfad.text())
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
