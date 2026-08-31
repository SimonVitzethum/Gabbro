//! **Pass 5 — M2, echte Linearität. Der Mechanismus, den kein vorhandenes Werkzeug liefert.**
//!
//! Gemessen (`MESSUNGEN.md`): Verus' `tracked` ist **affin**, Rust ist affin, SPARKs
//! Leckprüfung hängt an einer **Allokation**. Affin heisst: *höchstens einmal verbraucht* —
//! ein Wert darf fallengelassen werden. **Linear heisst: genau einmal**, und der Unterschied
//! ist die ganze Zusage:
//!
//! * `Held(L)` fallenlassen = eine Sperre, die niemand freigibt.
//! * `BootPhase` verdoppeln = zwei Kerne glauben, sie booten allein.
//! * `Parked` doppelt verbrauchen = ein Thread wird zweimal geweckt.
//! * `Duty(check)` fallenlassen = eine Prüfpflicht, die niemand einlöst.
//! * `own`-Zeiger verdoppeln = zwei Besitzer derselben Region.
//!
//! **Das ist der einzige Mechanismus des Ordners, für den es keinen Ersatz gibt** — und der
//! Grund, warum die Sprache überhaupt gerechtfertigt sein könnte.
//!
//! ## Was dieser Pass prüft und was nicht
//!
//! Er prüft **je Weg durch einen Rumpf**: jeder lineare Wert, der entsteht, wird auf jedem
//! Weg **genau einmal** verbraucht. Verbraucht wird durch:
//!
//! * einen Aufruf, dessen `effects` den Parameter unter `consumes` nennt,
//! * eine Rückgabe.
//!
//! **`leaves` verbraucht nicht** — die Klausel nennt die Werte, die den Ausgang *verlassen*
//! (`SPRACHE.md`:858), also die Schleife **überleben**.
//!
//! **Er prüft nicht** die Aliasfrage — dafür steht M3 — und **nicht** die Ghost-Löschung: ein
//! `ghost`-Wert existiert zur Laufzeit nicht, seine Linearität ist eine Aussage über den
//! **Beweis**, nicht über den Code. *Beides steht hier, damit niemand die Deckung grösser
//! liest, als sie ist.*
//!
//! ## Die Grobheit hat eine Richtung (W9)
//!
//! Bei einer Verzweigung wird **jeder Zweig einzeln** gerechnet und danach verlangt, dass
//! alle dasselbe tun. Wo ein Zweig divergiert (`-> never`), zählt er nicht mit — sonst wäre
//! jede Fehlerbehandlung ein Leck. **Die Vergröberung geht damit in die strenge Richtung:
//! sie meldet mehr, nicht weniger**, und ein falscher Alarm ist hier billiger als ein
//! übersehenes Leck.

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};
use gabbro_syntax::span::Span;
use std::collections::{BTreeMap, BTreeSet};

/// Was ein linearer Wert im Rumpf erlebt.
#[derive(Debug, Clone, Copy, PartialEq)]
enum Zustand {
    Lebt,
    Verbraucht,
}

/// **Die `consumes`-Listen der Gerufenen -- modulbewusst seit 2026-08-19.**
///
/// Vorher war der Schlüssel der kurze Name: zwei `uebergeben` in zwei Modulen waren EIN
/// Vertrag, und die Linearitätsprüfung las am Aufrufrand die Liste der falschen Funktion.
struct Vertraege<'a> {
    u: &'a crate::umgebung::Umgebung,
    param: &'a BTreeMap<String, BTreeSet<String>>,
    /// **Die Parameternamen des Gerufenen IN REIHENFOLGE.** Ohne sie ist die Position eines
    /// Arguments nicht auf einen Parameter abbildbar -- und genau daran fehlte es:
    /// `ruf` band `i` und benutzte es nie, also galt an einer Rufstelle JEDES lineare
    /// Argument als verbraucht, sobald der Gerufene IRGENDEINEN Parameter verbraucht.
    reihenfolge: &'a BTreeMap<String, Vec<String>>,
    ergebnis: &'a BTreeMap<String, String>,
    linear: &'a BTreeSet<String>,
    /// **The functions whose call does not come back**, for `endet`. Without them a branch
    /// ending in `abort();` counts as falling through, and its state enters the join.
    divergent: &'a [String],
    modul: &'a str,
}

impl Vertraege<'_> {
    /// **Liefert dieser Ausdruck einen linearen Wert?** Ein Ruf, dessen erklaertes Ergebnis
    /// einen `linear`-Typ nennt.
    fn linearer_ruf(&self, e: &Expr) -> Option<String> {
        let ExprArt::Ruf(r) = &e.art else { return None };
        let name = self
            .u
            .kandidaten_aufloesbar(self.modul, &r.path()?.text())
            .into_iter()
            .find_map(|k| self.ergebnis.get(&k))?;
        self.linear.contains(name).then(|| name.clone())
    }

    fn verbraucht(&self, pfad: &str) -> Option<&BTreeSet<String>> {
        self.u
            .kandidaten_aufloesbar(self.modul, pfad)
            .into_iter()
            .find_map(|k| self.param.get(&k))
    }

    /// Die Parameternamen des Gerufenen, in der Reihenfolge der Deklaration.
    fn parameter(&self, pfad: &str) -> Option<&Vec<String>> {
        self.u
            .kandidaten_aufloesbar(self.modul, pfad)
            .into_iter()
            .find_map(|k| self.reihenfolge.get(&k))
    }
}

pub fn pass(baum: &Programm, absagen: &mut Absagen) {
    // 1. Welche Typen sind linear?
    let mut linear: BTreeSet<String> = BTreeSet::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Typ(t) = &item.art {
            if t.linear {
                linear.insert(t.name.text.clone());
            }
        }
    });
    // **`L106` laeuft VOR dem fruehen Ausstieg, und das war ein Loch.**
    //
    // M2 kehrt zurueck, wenn die Einheit keinen linearen Typ hat -- richtig fuer die
    // Linearitaetspruefung, falsch fuer diese: **`leaves q` in einer Datei ganz ohne lineare
    // Typen ist der Fall, in dem die Klausel am ehesten falsch ist.** *Gefunden an der
    // eigenen Giftprobe, die durchging.*
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Funktion(f) = &item.art {
            leaves_pruefen(f, &linear, absagen);
        }
    });
    if linear.is_empty() {
        return;
    }

    // 2. Welcher Parameter welcher Funktion wird verbraucht? Aus `effects { consumes … }`.
    let u = crate::umgebung::Umgebung::sammle(baum);
    let mut verbraucht_param: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    // **Der ERKLAERTE Ergebnistypname, kurz** -- so, wie `linear` seine Namen fuehrt. Der
    // aufgeloeste `Typ` taugt hier nicht: ein `linear ghost type P;` hat keinen Rumpf und
    // loest auf `Unbekannt` auf.
    let mut ergebnistyp: BTreeMap<String, String> = BTreeMap::new();
    let mut reihenfolge: BTreeMap<String, Vec<String>> = BTreeMap::new();
    // **All three ways a function can promise not to come back**, and all three count. A
    // `-> never` result, the `divergent` class and `effects { diverges }` say the same
    // thing to a caller, and a list that knows only one of them makes `endet` answer
    // `false` for a branch that provably ends. *`schleifen.rs` reads all three for `S002`;
    // `namen.rs` reads only the class for `N045` -- a third register, and it is narrower
    // than the rule it serves.*
    let mut divergent: Vec<String> = Vec::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Funktion(f) = &item.art {
            let nie = matches!(&f.ergebnis, Some(TypExpr::Never(_)));
            let div = f.klasse == Some(FnKlasse::Divergent)
                || f.effects.as_ref().is_some_and(|w| {
                    w.liste.iter().any(|e| matches!(e.art, WirkungArt::Divergiert))
                });
            if nie || div {
                divergent.push(f.name.text.clone());
            }
        }
    });
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        if let ItemArt::Funktion(f) = &item.art {
            let mut menge = BTreeSet::new();
            if let Some(w) = &f.effects {
                for e in &w.liste {
                    if let WirkungArt::Verbraucht(o) = &e.art {
                        menge.insert(o.basis.text.clone());
                    }
                }
            }
            let q = crate::umgebung::qualifiziere(modul, &f.name.text);
            if let Some(TypExpr::Pfad(pf)) = &f.ergebnis {
                if let Some(n) = pf.teile.last() {
                    ergebnistyp.insert(q.clone(), n.text.clone());
                }
            }
            reihenfolge.insert(
                q.clone(),
                f.parameter.iter().map(|p| p.name.text.clone()).collect(),
            );
            verbraucht_param.insert(q, menge);
        }
    });

    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let ItemArt::Funktion(f) = &item.art else {
            return;
        };
        let FnRumpf::Block(b) = &f.rumpf else {
            return;
        };
        let v = Vertraege {
            u: &u,
            param: &verbraucht_param,
            reihenfolge: &reihenfolge,
            ergebnis: &ergebnistyp,
            linear: &linear,
            divergent: &divergent,
            modul,
        };
        // Lineare Parameter, die die Funktion NICHT unter `consumes` nennt, sind geliehen --
        // sie muessen am Ende noch leben. Die genannten muessen weg sein.
        let eigene = v
            .verbraucht(&f.name.text)
            .cloned()
            .unwrap_or_default();
        let mut zust: BTreeMap<String, (Zustand, Span, bool, bool)> = BTreeMap::new();
        for p in &f.parameter {
            if let TypExpr::Pfad(pf) = &p.typ {
                if let Some(n) = pf.teile.last() {
                    if linear.contains(&n.text) {
                        let soll_weg = eigene.contains(&p.name.text);
                        zust.insert(p.name.text.clone(), (Zustand::Lebt, p.name.span, soll_weg, false));
                    }
                }
            }
        }
        // **Kein frueher Rueckstieg mehr, wenn kein PARAMETER linear ist** -- der Wert kann
        // im Rumpf entstehen. Genau diese Zeile machte die Erweiterung oben unwirksam.
        gehe(b, &linear, &v, &mut zust, absagen);
        // Am Ende: geliehene leben, verbrauchte sind weg.
        for (name, (z, span, soll_weg, lokal)) in &zust {
            match (z, soll_weg) {
                // **`L107` -- ein im Rumpf entstandener linearer Wert, der liegen bleibt.**
                //
                // Der Fall, den M2 bis 2026-08-19 gar nicht sah: es verfolgte lineare
                // PARAMETER, und ein `let x = erzeuge();` war unsichtbar. *Genau-einmal war
                // damit eine Aussage ueber Argumente und nicht ueber Werte.*
                (Zustand::Lebt, true) if *lokal => absagen.schiebe(
                    Absage::fehler(
                        "L107",
                        *span,
                        format!("`{name}` is created here and consumed on no path"),
                    )
                    .mit_notiz(
                        "a linear value that arises in the body belongs to nobody else -- \
                         it is consumed, or it leaves through `return`",
                    ),
                ),
                (Zustand::Lebt, true) => absagen.schiebe(
                    Absage::fehler(
                        "L101",
                        *span,
                        format!(
                            "`{name}` is listed under `consumes` but is consumed on no path"
                        ),
                    )
                    .mit_notiz(
                        "`consumes` is a promise to the caller: the value is gone afterwards",
                    ),
                ),
                (Zustand::Verbraucht, false) => absagen.schiebe(
                    Absage::fehler(
                        "L102",
                        *span,
                        format!("`{name}` is borrowed and is consumed anyway"),
                    )
                    .mit_notiz(
                        "a parameter is consumed when `effects` names it under `consumes`",
                    ),
                ),
                _ => {}
            }
        }
    });
}

/// **`L109` — ein linearer Wert, der in einem ZWEIG geboren wird und ihn nicht verlaesst.**
///
/// `abgleich` laeuft ueber `zust.keys()` — den Stand VOR der Verzweigung. Ein Wert, der
/// erst im Zweig entsteht, steht dort nicht und fiel damit an der Vereinigung heraus:
///
/// ```gabbro
/// if k == 1 {
///     let p = parken();      -- parken() -> Parked, linear
/// }                          -- 0 Fehler
/// ```
///
/// > `L107` sagt denselben Satz eine Ebene hoeher — *„ein Wert, der im Rumpf entsteht,
/// > gehoert niemandem sonst"*. Er galt nur nicht fuer den Rumpf eines Zweiges.
fn zweig_geborene(
    vorher: &BTreeMap<String, (Zustand, Span, bool, bool)>,
    nachher: &BTreeMap<String, (Zustand, Span, bool, bool)>,
    endet_hier: bool,
    absagen: &mut Absagen,
) {
    if endet_hier {
        return; // wer den Zweig mit `return` verlaesst, reicht weiter -- das bucht `Return`.
    }
    for (name, (z, span, soll_weg, _)) in nachher {
        if vorher.contains_key(name) || !*soll_weg || *z == Zustand::Verbraucht {
            continue;
        }
        absagen.schiebe(
            Absage::fehler(
                "L109",
                *span,
                format!("`{name}` arises in this branch and is never consumed in it"),
            )
            .mit_notiz(
                "a linear value born inside a branch cannot survive it -- the branch is the \
                 whole of its life, and `exactly once` has to happen here",
            ),
        );
    }
}

fn gehe(
    b: &Block,
    linear: &BTreeSet<String>,
    v: &Vertraege,
    zust: &mut BTreeMap<String, (Zustand, Span, bool, bool)>,
    absagen: &mut Absagen,
) {
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Ruf(r) => ruf(r, s.span, v, zust, absagen),
            StmtArt::Let(l) => {
                ausdruck(&l.wert, s.span, v, zust, absagen);
                // **Ein linearer Wert, der im RUMPF entsteht** (2026-08-19). Bis dahin
                // verfolgte M2 ausschliesslich lineare PARAMETER, und
                //
                // ```gabbro
                // let x = erzeuge();   -- erzeuge() -> P, P ist `linear`
                // return;              -- x wird nie verbraucht
                // ```
                //
                // ging mit null Fehlern durch. *Genau-einmal war damit eine Aussage ueber
                // Argumente, nicht ueber Werte.*
                //
                // `soll_weg` ist hier IMMER wahr: ein hier entstandener Wert gehoert
                // niemandem sonst, also muss er auf jedem Weg verbraucht werden oder die
                // Funktion verlassen (`return`, s. unten).
                if let Some(t) = v.linearer_ruf(&l.wert) {
                    let _ = t;
                    zust.insert(l.name.text.clone(), (Zustand::Lebt, l.name.span, true, true));
                }
            }
            StmtArt::LetSonst(l) => {
                if let Some(r) = l.als_ruf() {
                    ruf(r, s.span, v, zust, absagen);
                }
                einseitig(&l.sonst, s.span, linear, v, zust, absagen);
            }
            // **`narrow … else` is a BRANCH, and it was walked as a body** («L104»,
            // 2026-08-31). See `einseitig` for the whole argument.
            StmtArt::Narrow(n) => einseitig(&n.sonst, s.span, linear, v, zust, absagen),
            StmtArt::Return(Some(e)) => {
                ausdruck(e, s.span, v, zust, absagen);
                // **Wer zurueckgibt, verbraucht nicht -- er reicht WEITER.** Fuer diese
                // Buchhaltung ist beides dasselbe: der Wert ist hier nicht mehr offen.
                if let ExprArt::Ort(o) = &e.art {
                    if o.suffixe.is_empty() {
                        if let Some((z, _, _, _)) = zust.get_mut(&o.basis.text) {
                            *z = Zustand::Verbraucht;
                        }
                    }
                }
            }
            StmtArt::Zuweisung(z) => ausdruck(&z.wert, s.span, v, zust, absagen),
            StmtArt::Wenn(w) => {
                // **Jeder Zweig einzeln, dann Abgleich** -- ein Wert, der nur in einem Zweig
                // verbraucht wird, ist auf dem anderen Weg noch da. Das ist ein Leck.
                let vorher = zust.clone();
                let mut ergebnisse = Vec::new();
                for (bed, r) in &w.zweige {
                    let mut z = vorher.clone();
                    ausdruck(bed, s.span, v, &mut z, absagen);
                    gehe(r, linear, v, &mut z, absagen);
                    // **One descent, not two.** `endet` walks the block itself; asking it
                    // twice per branch makes the pass 2^depth over nested `if`s.
                    let endet_hier = endet(r, v);
                    zweig_geborene(&vorher, &z, endet_hier, absagen);
                    ergebnisse.push((z, endet_hier));
                }
                if let Some(r) = &w.sonst {
                    let mut z = vorher.clone();
                    gehe(r, linear, v, &mut z, absagen);
                    let endet_hier = endet(r, v);
                    zweig_geborene(&vorher, &z, endet_hier, absagen);
                    ergebnisse.push((z, endet_hier));
                } else {
                    ergebnisse.push((vorher.clone(), false));
                }
                abgleich(&ergebnisse, s.span, zust, absagen);
            }
            StmtArt::Match(m) => {
                let vorher = zust.clone();
                let mut ergebnisse = Vec::new();
                for zw in &m.zweige {
                    let mut z = vorher.clone();
                    gehe(&zw.rumpf, linear, v, &mut z, absagen);
                    let endet_hier = endet(&zw.rumpf, v);
                    zweig_geborene(&vorher, &z, endet_hier, absagen);
                    ergebnisse.push((z, endet_hier));
                }
                abgleich(&ergebnisse, s.span, zust, absagen);
            }
            StmtArt::Schleife(_) => {
                // **`leaves` verbraucht NICHT.** `SPRACHE.md`:858: *„die `leaves`-Klausel
                // nennt die linearen Werte, die den Ausgang VERLASSEN"* -- sie ueberleben die
                // Schleife, sie enden nicht in ihr.
                //
                // Meine erste Fassung buchte sie als verbraucht und meldete daraufhin
                // `beispiele/04` als Fehler. **Der Pass hatte unrecht, nicht das Beispiel** --
                // und er hatte es an der Stelle, an der die Sprache ihre eigene Klausel am
                // genauesten erklaert. *Ein Pass, der eine Klausel umdeutet, statt sie zu
                // lesen, ist gefaehrlicher als einer, der sie ignoriert.*
            }
            _ => {}
        }
        // **The straight-line bodies over `crate::unterbloecke`** — `locks`, `breaking`,
        // `observes`, the `exchange` `update` body and every loop body run in the order of
        // the body and not as branches. *`if`, `match`, `narrow … else` and `let … else`
        // stay above: there the paths are RECONCILED, not written on.*
        //
        // `exchange` was missing once: a linear value consumed inside an `update(x) { … }`
        // did not count as consumed at all.
        if !matches!(
            &s.art,
            StmtArt::Wenn(_) | StmtArt::Match(_) | StmtArt::Narrow(_) | StmtArt::LetSonst(_)
        ) {
            // **`L108` — ein Schleifenrumpf laeuft OFT, gezaehlt wird er einmal**
            // (Rezension 2026-08-20).
            //
            // Der Rumpf laeuft hier als geradliniger Code. Fuer `locks`, `narrow … else`
            // und `update` ist das richtig — sie laufen einmal. **Fuer einen
            // Schleifenrumpf ist es falsch:** `wecken(p)` darin verbraucht `p` bei jedem
            // Durchlauf, gezaehlt wurde eine Verbrauchung.
            //
            // > *Genau einmal* ist eine Aussage ueber die AUSFUEHRUNG, nicht ueber den
            // > Quelltext. Ein Rumpf, der zweimal laufen kann, verbraucht zweimal.
            //
            // Geprueft wird der Wert, der VOR der Schleife schon da war: einer, der im
            // Rumpf entsteht und dort verbraucht wird, lebt und stirbt je Durchlauf und
            // ist in Ordnung.
            let vor_schleife: Option<BTreeMap<_, _>> =
                matches!(&s.art, StmtArt::Schleife(_)).then(|| zust.clone());
            for k in crate::unterbloecke(s) {
                gehe(k, linear, v, zust, absagen);
            }
            if let Some(vor) = vor_schleife {
                for (name, (z, span, _, _)) in zust.iter() {
                    let war_lebendig = matches!(vor.get(name), Some((Zustand::Lebt, _, _, _)));
                    if war_lebendig && *z == Zustand::Verbraucht {
                        absagen.schiebe(
                            Absage::fehler(
                                "L108",
                                *span,
                                format!("`{name}` is consumed inside a LOOP body"),
                            )
                            .mit_notiz(
                                "the body may run more than once, and `exactly once` then \
                                 becomes `once per pass` -- move the consumption out, or \
                                 let the value arise inside the body",
                            ),
                        );
                    }
                }
            }
        }
    }
}

/// **The one-armed branch — `narrow … else` and `let … else`.**
///
/// Both carry a block for the OTHER path, and until 2026-08-31 M2 walked that block as
/// straight-line code: whatever the `else` did was written straight into the state of the
/// path that never entered it. One consumption in the `else` arm therefore made the value
/// consumed for the continuation as well, and the next consumption there was reported as a
/// second one:
///
/// ```gabbro
/// narrow i to 0 ..< backed else { drop_handle(g); return; }
/// a.slots[i].taken = false;
/// drop_handle(g);                    -- `[L104] `g` is consumed a second time`
/// ```
///
/// > **The `if` spelling of the very same program was silent.** `emit.rs` lowers
/// > `narrow p to a..b else { S }` to `if (!(a <= p && p < b)) { S }` — one construct, one
/// > C form — so the two texts denote the same control flow, and a pass that answers them
/// > differently is reading the source and not the language. *This is the fourth instance
/// > of that class* (`D018`, `D017` twice, `K003`): **a pass that runs before the lowering
/// > and re-interprets control flow per construct.**
///
/// The arm is now what the lowering says it is: one branch that may end, plus the
/// fall-through path that skipped it, reconciled by `abgleich` exactly as an `if` without an
/// `else` is. For `let … else` the branch always ends (`S002` refuses one that falls
/// through), so it contributes nothing — which is the same answer the old code gave only by
/// accident, and only as long as nobody consumed anything in it.
fn einseitig(
    sonst: &Block,
    span: Span,
    linear: &BTreeSet<String>,
    v: &Vertraege,
    zust: &mut BTreeMap<String, (Zustand, Span, bool, bool)>,
    absagen: &mut Absagen,
) {
    let vorher = zust.clone();
    let mut z = vorher.clone();
    gehe(sonst, linear, v, &mut z, absagen);
    let endet_dort = endet(sonst, v);
    zweig_geborene(&vorher, &z, endet_dort, absagen);
    abgleich(&[(z, endet_dort), (vorher.clone(), false)], span, zust, absagen);
}

/// **Does the block end on every path?** Then it contributes nothing to the reconciliation.
///
/// This was a fourth copy of one question. `crate::endet_immer`, `m1`'s own method and this
/// one each carried the terminator list `Return | Leave | Next` in their own words, and the
/// three answers were not the same one:
///
/// | | diverging call | `locks`/`observes`/`breaking` arm | empty `match` |
/// |---|---|---|---|
/// | `crate::endet_immer` | ends | descends | **ends** (vacuous `all`) |
/// | `m2::endet` (before) | **falls through** | **falls through** | falls through |
///
/// The left column is what it cost. A `let … else` whose arm ends in `abort();` — the shape
/// every kernel writes its error handling in — was read as falling through, so its state
/// entered the join and `L103`/`L104` fired on a correct program. *`S002` demands that the
/// arm diverge or return, and M2 could see only the second half of the very rule that makes
/// the construct safe.*
///
/// > **One predicate cannot serve two questions, but this is not two questions.** `endet`
/// > asks *does control leave for good*, and both callers want the same answer; what
/// > differed was only how much each copy knew. **A copy is not a specialisation** — it is
/// > the same rule with less of the evidence.
///
fn endet(b: &Block, v: &Vertraege) -> bool {
    // **The empty `match` is the one place the two registers disagree**, and it is
    // reachable: `match x { }` parses and passes every pass today (measured 2026-08-31).
    // `crate::endet_immer` answers `true` for it -- `all()` over no arms is vacuously true
    // -- and that is the dangerous direction: a body ending in an empty `match` would count
    // as leaving for good. *Kept here rather than repaired there because `lib.rs` is not
    // this pass's file; the disagreement is reported, not papered over.*
    if let Some(s) = b.anweisungen.last() {
        if matches!(&s.art, StmtArt::Match(m) if m.zweige.is_empty()) {
            return false;
        }
    }
    crate::endet_immer(b, v.divergent)
}

/// **L103 — die Zweige müssen dasselbe tun.** Ein Wert, der nur auf einem Weg verbraucht
/// wird, ist auf dem anderen ein Leck; einer, der auf beiden verbraucht wird, ist keins.
fn abgleich(
    ergebnisse: &[(BTreeMap<String, (Zustand, Span, bool, bool)>, bool)],
    span: Span,
    zust: &mut BTreeMap<String, (Zustand, Span, bool, bool)>,
    absagen: &mut Absagen,
) {
    let lebendige: Vec<_> = ergebnisse.iter().filter(|(_, endet)| !endet).collect();
    let Some((erste, _)) = lebendige.first() else {
        // **A `return` stood here, and with it the consumption was LOST** (2026-08-25).
        //
        // ```gabbro
        // impl fn f(m : Marke, b : bool) -> u64 effects { consumes m } {
        //     if b { nimm(m); return 1; } else { nimm(m); return 2; }
        // }
        // ```
        //
        // gave **`L101` -- „`m` is listed under `consumes` but is consumed on no path"**.
        // Consumed on BOTH paths, and the checker said: on none.
        //
        // The old note *„every branch ends -- nothing to reconcile"* was right about the
        // SUCCESSOR STATE -- the code after it is unreachable -- and wrong about the
        // OBLIGATION. `zust` stayed at the state from before, and the check at the end of
        // the body read from it that nothing was ever consumed.
        //
        // > **A false rejection of a correct program** -- the same class as `U005`. A
        // > programmer who hits this can repair nothing, because nothing is broken.
        //
        // Adopted is only what ALL ending branches agree on: if one branch consumes and
        // another does not, the value stays alive and `L101` still fires -- *then it is a
        // leak on one path and not a false rejection.*
        for name in zust.keys().cloned().collect::<Vec<_>>() {
            let consumed_on_every_path = !ergebnisse.is_empty()
                && ergebnisse
                    .iter()
                    .all(|(z, _)| z.get(&name).map(|e| e.0) == Some(Zustand::Verbraucht));
            if consumed_on_every_path {
                if let Some(e) = zust.get_mut(&name) {
                    e.0 = Zustand::Verbraucht;
                }
            }
        }
        return;
    };
    for name in zust.keys().cloned().collect::<Vec<_>>() {
        let z0 = erste.get(&name).map(|e| e.0);
        let uneins = lebendige
            .iter()
            .any(|(z, _)| z.get(&name).map(|e| e.0) != z0);
        if uneins {
            absagen.schiebe(
                Absage::fehler(
                    "L103",
                    span,
                    format!("`{name}` is not treated the same on every path"),
                )
                .mit_notiz(
                    "linear means EXACTLY once, not at most once: a value that survives \
                        on one path is a leak on that path",
                )
                .mit_notiz(
                    "a branch that diverges or returns does not count -- not every path \
                        has to consume, only every path that ends normally",
                ),
            );
        }
        if let (Some(e), Some(z)) = (zust.get_mut(&name), z0) {
            e.0 = z;
        }
    }
}

fn ruf(
    r: &Ruf,
    span: Span,
    v: &Vertraege,
    zust: &mut BTreeMap<String, (Zustand, Span, bool, bool)>,
    absagen: &mut Absagen,
) {
    // **An indirect call consumes nothing, and `N036` is why that is a statement.**
    //
    // `consumes` cannot stand in a `fn(…)` contract: the position of a linear parameter comes
    // from the callee's signature, and an indirect call has none to read. *So this is not a
    // pass keeping quiet about a case it cannot handle -- it is a pass relying on a refusal
    // that already happened one pass earlier.*
    let Some(pfad) = r.path() else {
        return;
    };
    let Some(_name) = pfad.teile.last() else {
        return;
    };
    let leer = BTreeSet::new();
    let verbraucht = v.verbraucht(&pfad.text()).unwrap_or(&leer);
    // **Position fuer Position, und diesmal wirklich** (2026-08-20).
    //
    // Hier stand `let sig: Vec<String> = verbraucht.iter().cloned().collect();` -- die
    // Namen des Gerufenen SORTIERT, nicht in Deklarationsreihenfolge -- und darunter
    //
    //     let wird_verbraucht = !sig.is_empty() && i < r.argumente.len()
    //                           && !verbraucht.is_empty();
    //
    // `i` war gebunden und wurde nie gelesen. **Also galt an einer Rufstelle JEDES lineare
    // Argument als verbraucht, sobald der Gerufene irgendeinen Parameter verbraucht** --
    // in beide Richtungen falsch: ein zweiter Gebrauch eines NICHT verbrauchten Arguments
    // gab `L104`, und ein wirklich verbrauchtes wurde nur zufaellig getroffen.
    let sig: &[String] = v.parameter(&pfad.text()).map(|x| &x[..]).unwrap_or(&[]);
    for (i, a) in r.argumente.iter().enumerate() {
        let ExprArt::Ort(o) = &a.art else { continue };
        let arg = o.basis.text.clone();
        let Some((z, _, _, _)) = zust.get_mut(&arg) else {
            continue;
        };
        // Wird dieses Argument verbraucht? Nur wenn der Gerufene den Parameter an DIESER
        // Stelle unter `consumes` fuehrt -- die Namensmenge reicht dafuer nicht, also
        // wird sie hier ueber die Position genommen, so grob wie ehrlich.
        let wird_verbraucht = sig.get(i).is_some_and(|n| verbraucht.contains(n));
        if wird_verbraucht {
            if *z == Zustand::Verbraucht {
                absagen.schiebe(
                    Absage::fehler(
                        "L104",
                        span,
                        format!("`{arg}` is consumed a second time"),
                    )
                    .mit_notiz(
                        "linear means exactly once -- the first consumption took the value",
                    )
                    .mit_notiz("the first consumption is further up in the same body"),
                );
            }
            *z = Zustand::Verbraucht;
        } else if *z == Zustand::Verbraucht {
            absagen.schiebe(
                Absage::fehler(
                    "L105",
                    span,
                    format!("`{arg}` is used after it was consumed"),
                )
                .mit_notiz("after consumption the value no longer exists"),
            );
        }
    }
}

fn ausdruck(
    e: &Expr,
    span: Span,
    v: &Vertraege,
    zust: &mut BTreeMap<String, (Zustand, Span, bool, bool)>,
    absagen: &mut Absagen,
) {
    // **Ueber `alle_ausdruecke`, und das war ein DOUBLE-FREE mit gruenem Haken**
    // (Rezension 2026-08-20).
    //
    // ```gabbro
    // let a = aussen(wecken(p));    -- verbraucht p
    // let b = wecken(p);            -- verbraucht p ein zweites Mal
    // ```
    //
    // gab **null Fehler**. Beide Rufe auf oberster Ebene: `L104`. *Einer davon
    // geschachtelt: stumm* -- der Handlaeufer stieg nicht in die Argumente eines Rufes ab
    // und hatte ausserdem `_ => {}`.
    //
    // > M2 ist der Pass, den der eigene Modulkopf „das einzige Mittel in diesem Ordner, fuer
    // > das es keinen Ersatz gibt" nennt.
    //
    // **Die Reihenfolge ist die des Baumes, also von aussen nach innen.** Fuer die Frage
    // *„wurde derselbe Wert zweimal verbraucht"* genuegt das: beide Rufe werden gesehen,
    // und der zweite trifft auf `Zustand::Verbraucht`.
    for x in crate::alle_ausdruecke(e) {
        if let ExprArt::Ruf(r) = &x.art {
            ruf(r, span, v, zust, absagen);
        }
    }
}

/// **`L106` -- `leaves` nennt LINEARE Werte, und sie muessen es sein («NL.2.6», 2026-08-19).**
///
/// `pruefe-klauseln.py` fuehrte `verlaesst` als ZUSAGE: *„`leaves` an `forever` -- welche Wege
/// die Schleife verlassen darf; ungelesen."*
///
/// **Der Satz der Klausel war falsch, und das ist der eigentliche Fund.** `SPRACHE.md`:730
/// sagt es: *„`leave`/`return` from a scope holding linear values demands that they be named
/// (`leaves`)."* **`leaves` nennt die linearen WERTE, die den Geltungsbereich verlassen** --
/// nicht die Ausgaenge. Die Ausgaenge nennt `leave <schleife>`, und das ist eine
/// Schleifenmarke.
///
/// > *Der erste Anlauf am 2026-08-19 baute die falsche Regel und meldete an
/// > `beispiele/04-schleifen.gab` zwei Befunde -- `leaves marke` gegen `leave dienst`. Beide
/// > waren richtig, und die Regel war es nicht.* **Eine Klauselbeschreibung, die seit Wochen
/// > in der Waechtertabelle steht, ist keine Quelle -- die Spezifikation ist eine.**
///
/// Geprueft wird die Wohlgeformtheit: **der genannte Name ist eine Bindung dieser Funktion,
/// und ihr Typ ist linear.** Dass er den Bereich tatsaechlich verlaesst, ist M2s uebrige
/// Arbeit.
fn leaves_pruefen(
    f: &FnDecl,
    linear: &BTreeSet<String>,
    absagen: &mut gabbro_syntax::diag::Absagen,
) {
    let FnRumpf::Block(b) = &f.rumpf else { return };
    let mut schleifen = Vec::new();
    sammle_forever(b, &mut schleifen);
    for fo in schleifen {
        for v in &fo.verlaesst {
            let typ = f
                .parameter
                .iter()
                .find(|p| p.name.text == v.text)
                .map(|p| &p.typ);
            let ist_linear = matches!(typ, Some(TypExpr::Pfad(pf))
                if pf.teile.last().is_some_and(|n| linear.contains(&n.text)));
            if ist_linear {
                continue;
            }
            absagen.schiebe(
                gabbro_syntax::diag::Absage::fehler(
                    "L106",
                    v.span,
                    match typ {
                        None => format!("`leaves {}` names no binding of `{}`", v.text, f.name.text),
                        Some(_) => format!("`leaves {}` names a value that is not linear", v.text),
                    },
                )
                .mit_notiz(
                    "SPRACHE.md:730: leaving a scope that holds LINEAR values demands that \
                     they be named -- `leaves` names the values, not the exits",
                )
                .mit_notiz(
                    "the exits are named by `leave <loop>`, and that is a loop label -- two \
                     different things that share a word stem",
                ),
            );
        }
    }
}

fn sammle_forever<'a>(b: &'a Block, aus: &mut Vec<&'a Forever>) {
    for s in &b.anweisungen {
        if let StmtArt::Schleife(sch) = &s.art {
            if let Schleife::Forever(f) = sch.as_ref() {
                aus.push(f);
            }
        }
        for k in crate::unterbloecke(s) {
            sammle_forever(k, aus);
        }
    }
}
