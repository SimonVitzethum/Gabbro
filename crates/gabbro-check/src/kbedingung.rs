//! **Die K-Bedingung, mechanisch — und der Prüfer arbeitet damit für die Messung, die vor
//! ihm stehen sollte.**
//!
//! Das Messprotokoll für Messung 2 ([`MESSUNGEN.md`](MESSUNGEN.md)) sagt:
//!
//! > *„«Der Erzeuger zeigt es einmal» gilt nur, wenn **ALLE** Mutationen des Traegers erzeugte
//! > Operationen sind. Eine einzige Handmutation — ein `breaking`-Block, ein Schreibpfad
//! > ausserhalb der `ops`-Liste — und die Erhaltung ist **Menschenarbeit**, also A oder W.
//! > **Je Pflicht ist das eine mechanische Frage: sind alle Schreibstellen des Traegers
//! > erzeugt?**"*
//!
//! **Genau diese Frage beantwortet dieses Modul.** Damit wird der Übersetzer zum Messgerät
//! für die Zählung, die ihn eigentlich blockieren sollte — die einzige Bewegung, die die
//! Schere zwischen gebautem Prüfer und ungefahrener Messung von der anderen Seite schliesst.
//!
//! **Nebenertrag, den das Protokoll ausdrücklich nennt:** dieselbe Prüfung liefert die
//! **Liste der `breaking`-Stellen** — Posten L3 der Restliste.
//!
//! ## Und die Regel dahinter ist ohnehin eine
//!
//! `SPRACHE.md` §10.2: *„Handgeschriebene Mutation an einer `table` mit `ops` ist ein
//! **Uebersetzungsfehler**."* Der Bericht unten ist die Messform derselben Sache; die Absage
//! `D001` ist die Sprachform.

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};
use gabbro_syntax::span::Span;
use std::collections::{BTreeMap, BTreeSet};

/// Was über einen Träger festgestellt wurde.
#[derive(Debug, Clone)]
pub struct Traeger {
    pub name: String,
    /// Nennt die Tabelle erzeugte Mutationen (`ops …`)?
    pub hat_ops: bool,
    /// Handschriftliche Schreibstellen auf die Slots — Datei:Zeile fällt beim Aufrufer an.
    pub handschrift: Vec<(String, Span)>,
    /// `breaking`-Blöcke, die eine Invariante dieses Trägers ruhen lassen (L3).
    pub breaking: Vec<(String, Span)>,
}

impl Traeger {
    /// **Die K-Bedingung selbst.** Nur wo sie hält, darf eine Pflicht als „durch
    /// Konstruktion" gebucht werden.
    pub fn k_haelt(&self) -> bool {
        self.hat_ops && self.handschrift.is_empty() && self.breaking.is_empty()
    }
}

/// Erhebt je Tabelle, ob alle Schreibstellen erzeugt sind.
pub fn erhebe(baum: &Programm) -> Vec<Traeger> {
    let traeger_der_invariante = invariantentraeger(baum);
    let mut traeger: BTreeMap<String, Traeger> = BTreeMap::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Tabelle(t) = &item.art {
            traeger.insert(
                t.name.text.clone(),
                Traeger {
                    name: t.name.text.clone(),
                    hat_ops: !t.ops.is_empty(),
                    handschrift: Vec::new(),
                    breaking: Vec::new(),
                },
            );
        }
    });

    crate::fuer_jedes_item(baum, &mut |item| {
        let ItemArt::Funktion(f) = &item.art else {
            return;
        };
        let FnRumpf::Block(b) = &f.rumpf else {
            return;
        };
        let mut ziele = Vec::new();
        let mut brueche = Vec::new();
        sammle(b, &mut ziele, &mut brueche);
        for (ort, span) in ziele {
            // Auf welche Tabelle zielt der Schreibzugriff? Der Grundname eines Ortes ist
            // entweder die Tabelle selbst (`Kappenraum.slots[s]`) oder ein Zeiger auf sie.
            for (name, t) in traeger.iter_mut() {
                if ort.basis.text == *name
                    || ort
                        .suffixe
                        .iter()
                        .any(|s| matches!(s, OrtSuffix::Feld(i) if i.text == "slots"))
                        && ort.basis.text != *name
                        && ort_zeigt_auf(f, &ort.basis.text, name)
                {
                    t.handschrift.push((f.name.text.clone(), span));
                }
            }
        }
        for (inv, span) in brueche {
            // **Which carrier does the resting statement belong to?** Until 2026-08-28 this
            // loop ran over ALL carriers with `ops`, and the invariant name was never looked
            // up. Measured: a `breaking` on an invariant of `Endpoint` produced
            //
            //     [D009] `breaking` lets `paarig in oeffnen` rest, and `Objekte` declares `ops`
            //
            // -- `paarig` is not an invariant of `Objekte`, and the block never touched it.
            // **The refusal named the wrong carrier**, and it read like a finding while
            // doing so. Same class as `W16`: a plausible, wrong measurement.
            //
            // *The narrowing was only possible once `D013` made the name resolve* -- the
            // missing rule and the wrong one had one cause.
            for name in traeger_der_invariante.get(&inv).into_iter().flatten() {
                if let Some(t) = traeger.get_mut(name) {
                    if t.hat_ops {
                        t.breaking
                            .push((format!("{} in {}", inv, f.name.text), span));
                    }
                }
            }
        }
    });
    traeger.into_values().collect()
}

/// **Invariant name -> the carriers it stands over.**
///
/// `breaking I { … }` names an invariant, and until 2026-08-28 nothing resolved `I`. Four
/// declaration sites can supply one, and they are **exactly the four `maintains` accepts**
/// (`m1.rs::sammle_spezifikationen`) -- a second list would let the two clauses drift:
///
/// * a `table` invariant -- the carrier is that table;
/// * a `group` invariant -- the carriers are all its members;
/// * a `spec fn` -- the carriers are the tables its parameters point at;
/// * a `walk` invariant -- it stands over a traversal, not over a table, so the list is
///   EMPTY. *An empty list is not an unknown name:* the key is present, so `D013` stays
///   silent and `D009` has nothing to attribute. The difference matters, which is why the
///   entry is created rather than skipped.
pub fn invariantentraeger(baum: &Programm) -> BTreeMap<String, Vec<String>> {
    let mut tabellen: Vec<String> = Vec::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Tabelle(t) = &item.art {
            tabellen.push(t.name.text.clone());
        }
    });
    let mut aus: BTreeMap<String, Vec<String>> = BTreeMap::new();
    crate::fuer_jedes_item(baum, &mut |item| match &item.art {
        ItemArt::Tabelle(t) => {
            for i in &t.invarianten {
                let e = aus.entry(i.name.text.clone()).or_default();
                if !e.contains(&t.name.text) {
                    e.push(t.name.text.clone());
                }
            }
        }
        ItemArt::Walk(w) => {
            for i in &w.invarianten {
                aus.entry(i.name.text.clone()).or_default();
            }
        }
        // A `group` invariant names at least two carriers (`U007`) and is exactly the
        // statement that sits on none of them alone -- `maintains` accepts it, so
        // `breaking` must too, and the break belongs to **every** carrier it spans.
        ItemArt::Gruppe(g) => {
            let mitglieder: Vec<String> = g.traeger.iter().map(|t| t.text.clone()).collect();
            for i in &g.invarianten {
                let e = aus.entry(i.name.text.clone()).or_default();
                for m in &mitglieder {
                    if !e.contains(m) {
                        e.push(m.clone());
                    }
                }
            }
        }
        ItemArt::Funktion(f) if f.klasse == Some(FnKlasse::Spec) => {
            let e = aus.entry(f.name.text.clone()).or_default();
            for p in &f.parameter {
                if let Some(n) = zeigt_auf_tabelle(&p.typ, &tabellen) {
                    if !e.contains(&n) {
                        e.push(n);
                    }
                }
            }
        }
        _ => {}
    });
    aus
}

/// Names this parameter type one of the declared tables -- directly or through a pointer?
fn zeigt_auf_tabelle(t: &TypExpr, tabellen: &[String]) -> Option<String> {
    let pfad = match t {
        TypExpr::Zeiger(z) => match &z.ziel {
            TypExpr::Pfad(p) => p,
            _ => return None,
        },
        TypExpr::Pfad(p) => p,
        _ => return None,
    };
    let n = pfad.teile.last()?.text.clone();
    tabellen.contains(&n).then_some(n)
}

/// **`D013` -- `breaking I { … }` where `I` names nothing.**
///
/// `SPRACHE.md` §8.3 hangs three promises on that name: inside the block `I` is not
/// available as a premise, functions with `requires I`/`maintains I` are not callable, and
/// at the end `I` is restored or booked. **All three are promises about a name that was
/// never looked up.** Measured through the unchanged checker (W24), 2026-08-28:
///
/// ```text
/// breaking gibt_es_gar_nicht { e.slots[kern].caller = 1; }
///     ->  0 Fehler, 0 Hinweise
/// ```
///
/// This is the fifth member of a class this folder already names: a clause whose subject
/// stands nowhere -- `M133` (a loop `invariant` naming nothing), `N033` (`step`), `S007`
/// (`on_exceeded`), `N020` (`gates`). *`breaking` was the one that had the class and not
/// the rule.*
///
/// > **And it is the base of the other half.** `D009` attributed a break to every carrier
/// > with `ops`, because with no resolution there was no better candidate. One resolution
/// > closes both.
fn breaking_nennt_eine_invariante(baum: &Programm, absagen: &mut Absagen) {
    let bekannt = invariantentraeger(baum);
    crate::fuer_jedes_item(baum, &mut |item| {
        let ItemArt::Funktion(f) = &item.art else {
            return;
        };
        let FnRumpf::Block(b) = &f.rumpf else {
            return;
        };
        let mut offen = Vec::new();
        sammle_brueche(b, &mut offen);
        for i in offen {
            if bekannt.contains_key(&i.text) {
                continue;
            }
            absagen.schiebe(
                Absage::fehler(
                    "D013",
                    i.span,
                    format!(
                        "`breaking {}` names nothing this unit declares as an invariant",
                        i.text
                    ),
                )
                .mit_notiz(
                    "SPRACHE.md §8.3 hangs three promises on this name -- the invariant is \
                     blocked as a premise, `requires I`/`maintains I` are not callable, and \
                     at the end it is restored or booked",
                )
                .mit_notiz(
                    "the same class as `on_exceeded` without a name (`S007`), `step` \
                     (`N033`) and a loop `invariant` naming nothing (`M133`) -- a clause \
                     whose subject stands nowhere",
                )
                .mit_notiz(
                    "an invariant of a `table`, of a `group`, of a `walk`, or a `spec fn` \
                     -- the four `maintains` accepts",
                ),
            );
        }
    });
}

/// **`N531` -- `breaking I { … }` over a block that touches no carrier of `I`.**
///
/// `D013` makes sure the name resolves; it says in its own sentence what it does not buy:
/// *"a `breaking` on the wrong-but-existing invariant still passes"* (`SPRACHE.md` §8.3.1,
/// `GABBROV.md` §3 -- the site OFFEN O1's `L34` is about). This rule closes the part of that
/// gap a syntactic check can close: a block that writes NONE of the carriers of `I` -- no
/// assignment, no `publish`, no `exchange`, no transition on a table `I` stands over, and no
/// call that could write one -- cannot let `I` rest. It is a region named for the wrong
/// invariant, and it is refused.
///
/// **Conservative on purpose** (Opus agent G, 2026-09-26): a block that contains ANY call is
/// accepted, because a callee's writes are not resolved here; a walk invariant (no carrier)
/// is not asked. *The rule refuses only where the answer is certain.* What it does NOT
/// establish is that `I` is really false inside the block, or that the block restores it --
/// the first is a statement about one run (the goal theorem's `tabelle_gebrochen` shape), the
/// second is claimed at every writer's return (`invRueck`), not at the block's end.
fn breaking_rests_here(baum: &Programm, absagen: &mut Absagen) {
    let bekannt = invariantentraeger(baum);
    let mut tabellen: Vec<String> = Vec::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Tabelle(t) = &item.art {
            tabellen.push(t.name.text.clone());
        }
    });
    let (konstanten, weltnamen) = crate::wirkungen::welt_und_konstanten(baum);
    // The declared functions: a call counts only if it resolves to one (or is indirect) --
    // `Some(x)` and a tag constructor parse as calls and write nothing.
    let mut funktionen: BTreeSet<String> = BTreeSet::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Funktion(f) = &item.art {
            funktionen.insert(f.name.text.clone());
        }
    });
    crate::fuer_jedes_item(baum, &mut |item| {
        let ItemArt::Funktion(f) = &item.art else {
            return;
        };
        let FnRumpf::Block(b) = &f.rumpf else {
            return;
        };
        let mut stellen: Vec<&BrichtStmt> = Vec::new();
        collect_breaking_sites(b, &mut stellen);
        for x in stellen {
            if calls_a_function(&x.rumpf, &funktionen) {
                continue;
            }
            // The carriers the block writes: a carrier by name -- a table, and also a
            // `static`/`state` a `group` spans (`U001` admits all three; review of Opus agent
            // G, 2026-09-26: counting tables only refused a block that writes a static group
            // carrier) -- or a table through a parameter that points at one.
            let geschrieben: BTreeSet<String> =
                crate::wirkungen::rumpfwirkungen_mit(f, &x.rumpf, &konstanten, &weltnamen, false)
                    .into_iter()
                    .filter_map(|w| {
                        let ort = w.strip_prefix("writes ")?;
                        let wurzel = crate::wirkungen::carrier_root(ort).to_string();
                        if let Some(t) = f
                            .parameter
                            .iter()
                            .find(|p| p.name.text == wurzel)
                            .and_then(|p| zeigt_auf_tabelle(&p.typ, &tabellen))
                        {
                            return Some(t);
                        }
                        Some(wurzel)
                    })
                    .collect();
            for i in &x.invarianten {
                let Some(ts) = bekannt.get(&i.text) else {
                    continue; // `D013` refuses the name
                };
                if ts.is_empty() || ts.iter().any(|t| geschrieben.contains(t)) {
                    continue;
                }
                let namen: Vec<String> = ts.iter().map(|t| format!("`{t}`")).collect();
                absagen.schiebe(
                    Absage::fehler(
                        "N531",
                        i.span,
                        format!(
                            "`breaking {}` lets an invariant over {} rest, and this block \
                             writes none of them and calls nothing",
                            i.text,
                            namen.join(", ")
                        ),
                    )
                    .mit_notiz(
                        "a region in which an invariant rests is a region that writes its \
                         carriers -- this one is named for the wrong invariant",
                    )
                    .mit_notiz(
                        "SPRACHE.md §8.3.1: `D013` checks that the name resolves; a `breaking` \
                         on the wrong-but-existing invariant passed it",
                    ),
                );
            }
        }
    });
}

/// **`N532` -- inside `breaking I { … }`, a call of a function that `maintains I`.**
///
/// `SPRACHE.md` §8.3: *"Inside the block the invariant is not available as a premise:
/// functions with `requires I` or `maintains I` are not callable."* Until 2026-09-26 no pass
/// read it (`D013`'s sentence: "NONE of them is checked"). A function that `maintains I` owes
/// `I` at its return and is written against a state in which `I` holds; called while `I`
/// rests it would start from a state its own clause excludes.
///
/// **What it does not cover:** `requires I` as a predicate word (a `spec fn` named in a
/// `requires` clause) is not resolved here; an indirect call is not resolved either.
fn breaking_blocks_maintainers(baum: &Programm, absagen: &mut Absagen) {
    let mut pflegt: BTreeMap<String, Vec<String>> = BTreeMap::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Funktion(f) = &item.art {
            pflegt.insert(
                f.name.text.clone(),
                f.maintains.iter().map(|m| m.text.clone()).collect(),
            );
        }
    });
    crate::fuer_jedes_item(baum, &mut |item| {
        let ItemArt::Funktion(f) = &item.art else {
            return;
        };
        let FnRumpf::Block(b) = &f.rumpf else {
            return;
        };
        let mut stellen: Vec<&BrichtStmt> = Vec::new();
        collect_breaking_sites(b, &mut stellen);
        for x in stellen {
            let mut rufe = Vec::new();
            crate::wirkungen::calls_with_spans(&x.rumpf, &mut rufe);
            for (pfad, span) in rufe {
                let kurz = pfad.rsplit("::").next().unwrap_or(&pfad).to_string();
                let Some(ms) = pflegt.get(&kurz) else {
                    continue;
                };
                for i in &x.invarianten {
                    if !ms.iter().any(|m| m == &i.text) {
                        continue;
                    }
                    absagen.schiebe(
                        Absage::fehler(
                            "N532",
                            span,
                            format!(
                                "`{kurz}` maintains `{}` and is called inside `breaking {}`, \
                                 where that invariant rests",
                                i.text, i.text
                            ),
                        )
                        .mit_notiz(
                            "SPRACHE.md §8.3: inside the block the invariant is not available \
                             as a premise -- functions with `maintains I` are not callable",
                        )
                        .mit_notiz("call it after the block, once the invariant is restored"),
                    );
                }
            }
        }
    });
}

/// The `breaking` statements of a body, nested ones included.
fn collect_breaking_sites<'a>(b: &'a Block, aus: &mut Vec<&'a BrichtStmt>) {
    for s in &b.anweisungen {
        if let StmtArt::Bricht(x) = &s.art {
            aus.push(x);
        }
        for k in crate::unterbloecke(s) {
            collect_breaking_sites(k, aus);
        }
    }
}

/// Does the block call a FUNCTION -- a statement call or a call inside an expression that
/// resolves to a declared function, or any indirect call? Predicate words (`Has`/`Held`),
/// `Some(x)` and tag constructors are no calls of a function.
fn calls_a_function(b: &Block, funktionen: &BTreeSet<String>) -> bool {
    let ist_ruf = |r: &Ruf| -> bool {
        if crate::ist_praedikatswort(r) {
            return false;
        }
        match r.path() {
            None => true,
            Some(p) => p.teile.last().is_some_and(|i| funktionen.contains(&i.text)),
        }
    };
    for s in &b.anweisungen {
        if let StmtArt::Ruf(r) = &s.art {
            if ist_ruf(r) {
                return true;
            }
        }
        for e in crate::eigene_ausdruecke(s) {
            for x in crate::alle_ausdruecke(e) {
                if let ExprArt::Ruf(r) = &x.art {
                    if ist_ruf(r) {
                        return true;
                    }
                }
            }
        }
        if crate::unterbloecke(s).into_iter().any(|k| calls_a_function(k, funktionen)) {
            return true;
        }
    }
    false
}

/// The `breaking` names of a body, **with the span of the NAME** -- `sammle` keeps only the
/// span of the whole statement, which is what `D009` points at and the wrong place for a
/// refusal about one word.
fn sammle_brueche(b: &Block, aus: &mut Vec<Ident>) {
    for s in &b.anweisungen {
        if let StmtArt::Bricht(x) = &s.art {
            aus.extend(x.invarianten.iter().cloned());
        }
        for k in crate::unterbloecke(s) {
            sammle_brueche(k, aus);
        }
    }
}

/// Zeigt der Parameter `basis` von `f` auf die Tabelle `tabelle`?
fn ort_zeigt_auf(f: &FnDecl, basis: &str, tabelle: &str) -> bool {
    f.parameter.iter().any(|p| {
        p.name.text == basis
            && match &p.typ {
                TypExpr::Zeiger(z) => matches!(&z.ziel, TypExpr::Pfad(pf)
                    if pf.teile.last().is_some_and(|i| i.text == tabelle)),
                TypExpr::Pfad(pf) => pf.teile.last().is_some_and(|i| i.text == tabelle),
                _ => false,
            }
    })
}

fn sammle(b: &Block, ziele: &mut Vec<(Ort, Span)>, brueche: &mut Vec<(String, Span)>) {
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Zuweisung(z) => ziele.push((z.ziel.clone(), s.span)),
            StmtArt::Publish(p) => ziele.push((p.ziel.clone(), s.span)),
            StmtArt::Exchange(e) => ziele.push((e.ort.clone(), s.span)),
            StmtArt::Bricht(x) => {
                for i in &x.invarianten {
                    brueche.push((i.text.clone(), s.span));
                }
            }
            _ => {}
        }
        // **Der Abstieg über `crate::unterbloecke`** — vorher fehlte `observes`: eine
        // Handmutation an einer `ops`-Tabelle in einem RCU-Leseblock fiel nicht.
        for k in crate::unterbloecke(s) {
            sammle(k, ziele, brueche);
        }
    }
}

/// **`by ops` am Feld — die schärfere Fassung (2026-08-16).**
///
/// `D001` fällt an einer `table`, die `ops` nennt: dort ist **jede** Handmutation ein Fehler.
/// **`by ops` steht am FELD** und trägt damit einen Fall, den `D001` nicht kann: eine Tabelle,
/// deren Slots teils erzeugt und teils von Hand geschrieben werden — *`refcount` gehört den
/// Operationen, `benutzt` nicht.*
///
/// **Und das ist der Unterschied zwischen einer Prüfvorschrift und einer
/// Grammatikeigenschaft:** die K-Bedingung des Messprotokolls lautet *„gilt nur, wenn ALLE
/// Mutationen des Trägers erzeugte Operationen sind"* — mit `by ops` ist sie **je Feld
/// abgeschlossen**, statt je Tabelle nachgezählt.
fn nur_ops_felder(baum: &Programm) -> Vec<(String, String)> {
    let mut aus = Vec::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Tabelle(t) = &item.art {
            if let Some(sd) = &t.slot {
                for f in &sd.felder {
                    if f.nur_ops {
                        aus.push((t.name.text.clone(), f.name.text.clone()));
                    }
                }
            }
        }
    });
    aus
}

/// **Die Sprachform:** eine `table` mit `ops` duldet keine Handmutation (`SPRACHE.md` §10.2).
pub fn pass(baum: &Programm, absagen: &mut Absagen) {
    erschoepfendes_match(baum, absagen);
    baumkanten(baum, absagen);
    belegtfeld(baum, absagen);
    eigner(baum, absagen);
    // **The other half of `D001`** (2026-08-28): this pass forbids the hand mutation, and
    // `crate::opsruf` holds the generated operation that takes its place -- `D012` demands
    // that the proof's premises stand where it is called. *A prohibition whose replacement
    // owes nothing would have moved the work, not removed it.*
    crate::opsruf::pass(baum, absagen);
    // **D002 -- `by ops` am Feld.** Schärfer als `D001`: es trifft auch dort, wo die Tabelle
    // als Ganzes Handmutationen duldet, das EINE Feld aber nicht.
    let geschuetzt = nur_ops_felder(baum);
    if !geschuetzt.is_empty() {
        crate::fuer_jedes_item(baum, &mut |item| {
            let ItemArt::Funktion(f) = &item.art else {
                return;
            };
            let FnRumpf::Block(b) = &f.rumpf else {
                return;
            };
            let mut ziele = Vec::new();
            let mut brueche = Vec::new();
            sammle(b, &mut ziele, &mut brueche);
            for (ort, span) in &ziele {
                let text = ort.text();
                for (tab, feld) in &geschuetzt {
                    if text.split(['.', '[']).any(|x| x == feld) {
                        absagen.schiebe(
                            Absage::fehler(
                                "D002",
                                *span,
                                format!(
                                    "`{text}` carries `by ops` in `{tab}` and is mutated \
                                        by hand here"
                                ),
                            )
                            .mit_notiz(
                                "`by ops` means: only the generated operations of the \
                                    table write this field",
                            )
                            .mit_notiz(
                                "that is exactly what makes `refcount -= 1` by hand \
                                    unwritable, and it is the point of the clause",
                            ),
                        );
                    }
                }
            }
        });
    }
    breaking_nennt_eine_invariante(baum, absagen);
    breaking_rests_here(baum, absagen);
    breaking_blocks_maintainers(baum, absagen);
    for t in erhebe(baum) {
        if !t.hat_ops {
            continue;
        }
        // **`D009` -- a `breaking` block on an `ops` carrier, 2026-08-21.**
        //
        // This half was collected, counted, printed -- and never refused. `k_haelt()`
        // demanded `breaking.is_empty()` from the first day; the pass reported only
        // `handschrift`. **A program could pass this pass without satisfying the K
        // condition**, and that condition is not merely a check: it is the mechanical
        // criterion under which the K/A/W count booked 28 of 73 obligations as *"by
        // construction"*.
        //
        // > *Found not by a tool but by writing down the statement this pass owes* (PL.1).
        // > Thirteen text guardians and 268 mutations did not see it: they can find that a
        // > clause has no reader, not that a reader reads the wrong thing.
        //
        // **Measured before the build: ZERO `breaking` sites in the clean corpus**, so the
        // refusal changes no counted number. *That is the answer to the follow-up question,
        // and it is a measurement rather than a "probably not".*
        for (was, span) in &t.breaking {
            absagen.schiebe(
                Absage::fehler(
                    "D009",
                    *span,
                    format!(
                        "`breaking` lets `{was}` rest, and `{}` declares `ops`",
                        t.name
                    ),
                )
                .mit_notiz(
                    "the K condition holds only if ALL mutations of the carrier are \
                        generated operations -- a resting invariant is a write the \
                        generator did not make",
                )
                .mit_notiz(
                    "until 2026-08-21 this site was counted and printed and never \
                        refused: the pass reported it while `k_haelt()` demanded its \
                        absence",
                ),
            );
        }
        for (fn_name, span) in &t.handschrift {
            absagen.schiebe(
                Absage::fehler(
                    "D001",
                    *span,
                    format!(
                        "`{}` writes `{}` by hand although the table declares `ops`",
                        fn_name, t.name
                    ),
                )
                .mit_notiz(
                    "SPRACHE.md §10.2: a hand-written mutation on a `table` with `ops` is \
                        a compile error",
                )
                .mit_notiz(
                    "otherwise the K condition of the measurement protocol falls: it \
                        holds only if ALL mutations of the carrier are generated operations",
                ),
            );
        }
    }
}

/// **Die Messform:** der Bericht, der in Messung 2 eingeht.
pub fn zeige(traeger: &[Traeger]) -> String {
    let mut out = String::new();
    out.push_str(
        "-- The K condition per carrier: are ALL write sites generated? Only then may a\n",
    );
    let (mut haelt, mut faellt) = (0, 0);
    for t in traeger {
        if t.k_haelt() {
            haelt += 1;
        } else {
            faellt += 1;
        }
        out.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\n",
            t.name,
            if t.hat_ops { "ja" } else { "NEIN" },
            t.handschrift.len(),
            t.breaking.len(),
            if t.k_haelt() { "haelt" } else { "FAELLT" }
        ));
    }
    out.push_str(&format!(
        "-- {} carriers: K holds {haelt} times, falls {faellt} times.\n",
        traeger.len()
    ));
    // Der Nebenertrag, den das Protokoll ausdruecklich nennt: die breaking-Liste ist L3.
    let brueche: Vec<&(String, Span)> = traeger.iter().flat_map(|t| t.breaking.iter()).collect();
    out.push_str(&format!(
        "-- {} `breaking` site(s) -- which is also item L3 of the remaining list.\n",
        brueche.len()
    ));
    out
}

/// **`D005` — ein `match` über einen `tagged type` nennt jede Variante.**
///
/// Die letzte offene Zeile an Pass 2, und sie stand seit dem ersten Tag so da:
/// *„NOT built: exhaustive `match` over `tagged`."*
///
/// **Warum das zu D1/D2 gehört und nicht zu M1:** ein `tagged type` ist die einzige Form, in
/// der die Sprache eine ABGESCHLOSSENE Fallunterscheidung ausspricht. `SYNTAX.md`, *„was
/// ausdrücklich nicht existiert"*: **kein Sammelzweig.** Ohne diese Regel ist die
/// Abgeschlossenheit eine Zusage der Grammatik, die kein Pass einlöst — und eine fehlende
/// Variante fällt dann erst dort auf, wo sie zur Laufzeit vorkommt.
///
/// > *Dieselbe Bauart wie `unterbloecke`: ein `match` ohne alle Zweige ist genau der
/// > `_ => {}`-Zweig, den der Prüfer sich selbst verboten hat* (W15).
fn erschoepfendes_match(baum: &Programm, absagen: &mut Absagen) {
    let mut varianten: std::collections::BTreeMap<String, Vec<String>> =
        std::collections::BTreeMap::new();
    crate::fuer_jedes_item(baum, &mut |i| {
        let ItemArt::Typ(t) = &i.art else { return };
        if !t.tagged {
            return;
        }
        if let Some(TypExpr::Varianten(v, _)) = &t.rumpf {
            varianten.insert(
                t.name.text.clone(),
                v.iter().map(|x| x.name.text.clone()).collect(),
            );
        }
    });
    if varianten.is_empty() {
        return;
    }
    let u = crate::umgebung::Umgebung::sammle(baum);
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let ItemArt::Funktion(f) = &item.art else { return };
        let FnRumpf::Block(b) = &f.rumpf else { return };
        let lokal: std::collections::HashMap<String, crate::typen::Typ> = f
            .parameter
            .iter()
            .map(|p| (p.name.text.clone(), u.typ_von_ausdruck_decl(modul, &p.typ)))
            .collect();
        matchpruefen(b, &u, modul, &lokal, &varianten, absagen);
    });
}

fn matchpruefen(
    b: &Block,
    u: &crate::umgebung::Umgebung,
    modul: &str,
    lokal: &std::collections::HashMap<String, crate::typen::Typ>,
    varianten: &std::collections::BTreeMap<String, Vec<String>>,
    absagen: &mut Absagen,
) {
    for s in &b.anweisungen {
        if let StmtArt::Match(m) = &s.art {
            // **`match (a)` named no variants at all** (measured 2026-09-02). The subject
            // was read with a bare `if let ExprArt::Ort(…)`, so one pair of brackets took
            // the whole check away: `match a { Speicher, Endpunkt }` over a three-variant
            // `tagged type` fell at `D005`, `match (a) { … }` gave **0 errors**.
            //
            // *The rule this pass carries is the one the language states about ITSELF* --
            // "a `tagged type` is the one form in which the language states a CLOSED case
            // distinction, and there is no catch-all branch". **A closedness that a bracket
            // suspends is none.**
            if let ExprArt::Ort(o) = &crate::ohne_klammern(&m.gegenstand).art {
                let t = u.typ_von_ort(modul, o, lokal);
                // **Der Name des Summentyps, nicht seine Struktur.** Ein `tagged` löst auf
                // `Typ::Summe { name, .. }` auf; nur über den Namen finden wir die
                // Deklaration wieder, und nur sie kennt die vollständige Liste.
                // **Der Schluessel der Deklaration ist QUALIFIZIERT** (`tg::Art`), die
                // Variantentabelle steht unter dem kurzen Namen. *Der erste Anlauf verglich
                // beide direkt und traf nie -- die Probe war still, und still ist hier
                // dasselbe wie kaputt* (R11).
                let name = match t.durchgreifen() {
                    crate::typen::Typ::Summe { name, .. } if !name.is_empty() => {
                        crate::umgebung::kurzname(name).to_string()
                    }
                    _ => match &t {
                        crate::typen::Typ::Benannt { name, .. } => {
                            crate::umgebung::kurzname(name).to_string()
                        }
                        _ => String::new(),
                    },
                };
                if let Some(alle) = varianten.get(&name) {
                    let genannt: Vec<&str> =
                        m.zweige.iter().map(|z| z.variante.text.as_str()).collect();
                    let fehlt: Vec<&String> =
                        alle.iter().filter(|v| !genannt.contains(&v.as_str())).collect();
                    if !fehlt.is_empty() {
                        absagen.schiebe(
                            Absage::fehler(
                                "D005",
                                s.span,
                                format!(
                                    "this `match` over `{name}` does not name: {}",
                                    fehlt
                                        .iter()
                                        .map(|x| format!("`{x}`"))
                                        .collect::<Vec<_>>()
                                        .join(", ")
                                ),
                            )
                            .mit_notiz(
                                "a `tagged type` is the one form in which the language \
                                 states a CLOSED case distinction -- and there is no \
                                 catch-all branch (SYNTAX.md, \"what deliberately does not \
                                 exist\")",
                            )
                            .mit_notiz(
                                "without this the closedness is a promise of the grammar \
                                 that no pass redeems, and a missing variant shows up where \
                                 it occurs at RUN time",
                            ),
                        );
                    }
                }
            }
        }
        for k in crate::unterbloecke(s) {
            matchpruefen(k, u, modul, lokal, varianten, absagen);
        }
    }
}

/// **«B41b»: die Kante einer Tabelle wird EINMAL geprueft, nicht an jedem Durchlauf.**
///
/// `tree { parent elter, child erstes_kind, sibling naechstes }` nennt die Felder, an denen
/// `descendants of` und `ancestors of` laufen. Drei Regeln halten die Deklaration:
///
/// * **`D006`** -- das Feld steht im `slot`. Ein Name, der nirgends steht, ist keine Kante.
/// * **`D007`** -- es ist `option index into Self`. Die Kante muss ENDEN koennen, und der
///   Sonderwert dafuer ist `count` selbst (`beweise/Option_Sonderwert.thy`). Ein `index into
///   T` ohne `option` hat kein Ende, ein `u32` hat nicht einmal eine Schranke.
/// * **`D008`** -- sie zeigt auf die EIGENE Tabelle. `parent` in eine fremde Tabelle waere
///   keine Baumkante, sondern eine Fremdschluesselbeziehung, und darueber sagt `descendants
///   of` nichts.
///
/// > **Und diese drei stehen im PRUEFER, nicht im Erzeuger** -- das ist die Lehre aus «B24»:
/// > *eine Regel, die nur auf der Erzeugerflaeche steht, beruehren die meisten Programme
/// > nie.* Wer `tree { parent nichtsda }` schreibt, soll es von `gabbro pruefe` hoeren und
/// > nicht erst von `gabbro emit`.
/// **`occupied f` -- the field at which a slot is OCCUPIED, and two rules hold it.**
///
/// The generator for `ops` (cut (c)) needs `sigma s = Some sl` from
/// `beweise/Table_Ops_Erhaltung.thy` as a PROGRAM: `einfuegen_erhaelt` assumes the slot is
/// FRESH, `blatt_loeschen_erhaelt` that it is free afterwards. **Without a named field
/// neither has a subject.**
///
/// * **`D010`** -- `occupied f` names a `bool` field of its own slot. Word for word `D006`/
///   `D007` at the tree edge, and in the CHECKER rather than the generator for the same
///   reason: a rule that lives only on the generator surface, most programs never touch.
/// * **`D011`** -- a `table` with `ops` carries an `occupied`. *Otherwise `D001` forbids hand
///   mutation and the generator puts nothing in its place -- the one position in which a
///   construct is worse than none.*
///
/// > Why not the name heuristic: the corpus names that field under **eleven** names
/// > (`belegt` 8, `benutzt` 6, `used` 3, `aktiv` 3, plus seven singletons). *A rule that knows
/// > `belegt` and not `quiescing` zeroes the wrong field in `beispiele/31`* -- and a generator
/// > that zeroes the wrong field is worse than no generator.
/// > The decision stands in `messung/OPS-ERZEUGER.md`.
fn belegtfeld(baum: &Programm, absagen: &mut Absagen) {
    crate::fuer_jedes_item(baum, &mut |item| {
        let ItemArt::Tabelle(t) = &item.art else { return };
        match &t.belegt {
            Some(f) => {
                let treffer = t
                    .slot
                    .iter()
                    .flat_map(|s| s.felder.iter())
                    .find(|sf| sf.name.text == f.text);
                let ist_bool = matches!(
                    treffer.map(|sf| &sf.typ),
                    Some(SlotTyp::Typ(TypExpr::Bool(_)))
                );
                if !ist_bool {
                    absagen.schiebe(
                        Absage::fehler(
                            "D010",
                            f.span,
                            format!(
                                "`occupied {}` is not a `bool` field of `{}`'s slot",
                                f.text, t.name.text
                            ),
                        )
                        .mit_notiz(
                            "occupancy is two-valued: `Some sl` or `None` in \
                             beweise/Table_Ops_Erhaltung.thy. A field with more values would \
                             make the generated `remove` say something the proof does not",
                        ),
                    );
                }
            }
            None if !t.ops.is_empty() => {
                absagen.schiebe(
                    Absage::fehler(
                        "D011",
                        t.name.span,
                        format!(
                            "`table {}` declares `ops` but no `occupied` field",
                            t.name.text
                        ),
                    )
                    .mit_notiz(
                        "`D001` already forbids hand mutation here -- without `occupied` the \
                         generator has nothing to put in its place, and \"the slot is fresh\" \
                         has no subject",
                    ),
                );
            }
            None => {}
        }
    });
}

/// **Every table with an `owner` clause.**
struct EignerTabelle {
    tabelle: String,
    marke: String,
    span: Span,
}

/// **Every signature that can carry linear values: functions (except `spec
/// fn`, which is proof-only and touches nothing at run time -- the same
/// exemption `H007` carries), axioms and syscalls (both foreign by
/// construction, like an `extern fn`).**
struct Stelle {
    name: String,
    span: Span,
    /// The graph key (`mod::name`): what call sites resolve to.
    schluessel: String,
    modul: String,
    fremd: bool,
    rueckgabe: Option<(String, Span)>,
    parameter: Vec<(String, TypExpr)>,
    wirkungen: Vec<Wirkung>,
    /// The checkable body, if there is one (`Block` only: `asm` is a sealed
    /// hole and reads like a foreign body for touch purposes).
    koerper: Option<Block>,
    /// `requires` plus `ensures`: contracts evaluate calls too (a contract
    /// calling the minter executes it), so they are call sites like bodies.
    vertraege: Vec<Pred>,
}

/// **D026 -- `owner m` without a producer is parsed and refused, by name** («SG-9»).
///
/// The grammar promises that every access to the table holds the mark `m`, and
/// that nobody mints it (`eigner_nie_erzeugt`, `Syntax.lean`). What it does not
/// say is who mints the FIRST one -- and a guard nobody holds is a sentence,
/// not a discipline. Until the producer story stands (which linear value
/// becomes the first mark, and at whose hands), the checker refuses the clause
/// instead of claiming a memory safety no pass enforces. *Open item, named in
/// SYNTAX.md §9 -- not a gap in the goal, which speaks about what the language
/// carries, and an uncarried guard is not carried.*
///
/// Since lane 151 the refusal is no longer unconditional: a table whose mark
/// has a complete producer (`D265` clean, `D266` clean, exactly one foreign
/// minter, every toucher holds the mark, at least one toucher) is NOT refused
/// here. An incomplete producer (no minter, or a minter nobody guards with)
/// keeps this refusal; a malformed one is refused under its own code and stays
/// silent here -- one fault, one refusal.
fn eigner(baum: &Programm, absagen: &mut Absagen) {
    // **The declared linear marks, by short name** -- the same resolution the
    // legacy refusal below uses for tables. Two modules naming one mark is a
    // merge-time question this pass does not decide.
    let mut linear: BTreeSet<String> = BTreeSet::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Typ(t) = &item.art {
            if t.linear {
                linear.insert(t.name.text.clone());
            }
        }
    });
    // **Every table with an `owner` clause.**
    let mut tabellen: Vec<EignerTabelle> = Vec::new();
    // **Every signature that can carry linear values (see `Stelle`).**
    // With the module: call sites resolve to graph keys, and the single-mint
    // rule (`D268`) counts them.
    let mut stellen: Vec<Stelle> = Vec::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| match &item.art {
        ItemArt::Tabelle(t) => {
            if let Some(m) = &t.eigner {
                tabellen.push(EignerTabelle {
                    tabelle: t.name.text.clone(),
                    marke: m.text.clone(),
                    span: m.span,
                });
            }
        }
        ItemArt::Funktion(f) => {
            if matches!(f.klasse, Some(FnKlasse::Spec)) {
                return;
            }
            stellen.push(Stelle {
                name: f.name.text.clone(),
                span: f.name.span,
                schluessel: crate::umgebung::qualifiziere(modul, &f.name.text),
                modul: modul.to_string(),
                fremd: matches!(f.rumpf, FnRumpf::Keiner),
                rueckgabe: nackter_name(&f.ergebnis),
                parameter: f.parameter.iter().map(|p| (p.name.text.clone(), p.typ.clone())).collect(),
                wirkungen: f.effects.as_ref().map(|w| w.liste.clone()).unwrap_or_default(),
                koerper: match &f.rumpf {
                    FnRumpf::Block(b) => Some(b.clone()),
                    _ => None,
                },
                vertraege: f.requires.iter().chain(f.ensures.iter()).cloned().collect(),
            });
        }
        ItemArt::Axiom(a) => {
            stellen.push(Stelle {
                name: a.name.text.clone(),
                span: a.name.span,
                schluessel: crate::umgebung::qualifiziere(modul, &a.name.text),
                modul: modul.to_string(),
                fremd: true,
                rueckgabe: nackter_name(&a.rueckgabe),
                parameter: a.parameter.iter().map(|p| (p.name.text.clone(), p.typ.clone())).collect(),
                wirkungen: a.effects.liste.clone(),
                koerper: None,
                vertraege: a.requires.clone(),
            });
        }
        ItemArt::Syscall(s) => {
            stellen.push(Stelle {
                name: s.name.text.clone(),
                span: s.name.span,
                schluessel: crate::umgebung::qualifiziere(modul, &s.name.text),
                modul: modul.to_string(),
                fremd: true,
                rueckgabe: nackter_name(&s.ergebnis),
                parameter: s.parameter.iter().map(|p| (p.name.text.clone(), p.typ.clone())).collect(),
                wirkungen: s.effects.liste.clone(),
                koerper: None,
                vertraege: s.requires.iter().chain(s.ensures.iter()).cloned().collect(),
            });
        }
        _ => {}
    });
    // **D265 -- the mark must be a declared linear type.** Without a linear
    // value there is nothing to hold, and the rest of the story has no subject.
    // A mark refused here takes its tables with it: the specific refusal owns
    // the fault, `D026` stays silent for them.
    let mut schlecht: BTreeSet<String> = BTreeSet::new();
    let mut marken: Vec<String> = tabellen.iter().map(|t| t.marke.clone()).collect();
    marken.sort();
    marken.dedup();
    for m in &marken {
        if linear.contains(m) {
            continue;
        }
        schlecht.insert(m.clone());
        for t in tabellen.iter().filter(|t| &t.marke == m) {
            absagen.schiebe(
                Absage::fehler(
                    "D265",
                    t.span,
                    format!(
                        "`table {}` names `owner {}`, and `{}` is no declared `linear` type",
                        t.tabelle, m, m
                    ),
                )
                .mit_notiz(
                    "the guard is a linear value: nothing holds it unless the mark is one -- \
                     declare `linear [ghost] type` under that name",
                ),
            );
        }
    }
    // Carrier names for touch resolution: every table, owner-guarded or not.
    let mut traeger: BTreeSet<String> = BTreeSet::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Tabelle(t) = &item.art {
            traeger.insert(t.name.text.clone());
        }
    });
    // Owner of each carrier, where there is one.
    let mut eigner_von: BTreeMap<String, String> = BTreeMap::new();
    for t in &tabellen {
        eigner_von.entry(t.tabelle.clone()).or_insert(t.marke.clone());
    }
    // **D266 -- one mint, and no signature production.** The foreign minter's
    // return is the single introduction of the mark (a named assumption, like
    // every foreign body); `allocs` of the mark or a bodied function returning
    // it without taking it would be a second mint through a signature -- the
    // shape `eigner_nie_erzeugt` (`Syntax.lean:149`) forbids.
    let mut minter: BTreeMap<String, (String, Span, String)> = BTreeMap::new();
    // Collected up front: the loops below refuse into `schlecht`, which the
    // lazy filter would otherwise borrow across the mutation.
    let gute: Vec<String> = marken.iter().filter(|m| !schlecht.contains(*m)).cloned().collect();
    for m in &gute {
        let mut erste: Option<(String, Span, String)> = None;
        for s in &stellen {
            let Some((ret, _)) = &s.rueckgabe else { continue };
            if ret != m {
                continue;
            }
            if haelt_marke(s, m) {
                continue;
            }
            if s.fremd {
                if erste.is_none() {
                    erste = Some((s.name.clone(), s.span, s.schluessel.clone()));
                    continue;
                }
                absagen.schiebe(
                    Absage::fehler(
                        "D266",
                        s.span,
                        format!(
                            "`{}` returns `owner` mark `{m}`, and `{}` already mints it",
                            s.name,
                            erste.as_ref().map(|e| e.0.as_str()).unwrap_or("?"),
                        ),
                    )
                    .mit_notiz(
                        "one mark, one minter: a second mint is a second owner of the same slots",
                    ),
                );
                schlecht.insert(m.clone());
            } else {
                absagen.schiebe(
                    Absage::fehler(
                        "D266",
                        s.span,
                        format!(
                            "`{}` returns `{m}` without taking it, and `{m}` is an `owner` mark",
                            s.name
                        ),
                    )
                    .mit_notiz(
                        "only the single foreign minter introduces the mark -- a body forwards \
                         what it is given, so take `{m}` as a parameter",
                    ),
                );
                schlecht.insert(m.clone());
            }
        }
        if let Some(e) = erste {
            minter.insert(m.clone(), e);
        }
        for s in &stellen {
            for w in &s.wirkungen {
                if let WirkungArt::Belegt(i) = &w.art {
                    if i.text == *m {
                        absagen.schiebe(
                            Absage::fehler(
                                "D266",
                                i.span,
                                format!(
                                    "`{}` names `allocs {m}`, and `{m}` is an `owner` mark",
                                    s.name
                                ),
                            )
                            .mit_notiz(
                                "no signature (re)produces an owner mark (`eigner_nie_erzeugt`) -- \
                                 the foreign minter's return is the single introduction, and the \
                                 mark travels by handoff, not by fresh `allocs`",
                            ),
                        );
                        schlecht.insert(m.clone());
                    }
                }
            }
        }
    }
    // **D267 -- every toucher holds the mark.** For a bodied function the
    // touch is a body SITE: an assignment/`publish`/`exchange` target or a
    // read that resolves to an owner-guarded carrier (directly by carrier
    // name, or through a pointer parameter into it) -- an `effects` line
    // alone is the call-graph hull (`runde` declaring what `schreibe`
    // writes) and no access of its own. Reads come through the very walk
    // `E010` reads (`wirkungen::lese_orte`), not a second walk over the body.
    // For a foreign signature (no checkable body: `extern`, `axiom`,
    // `syscall`, `asm`) the declared `reads`/`writes`/`consumes`/
    // `publishes` effects are all there is, and each carrier touch owes a
    // linear parameter of the mark -- borrowed or consumed, both stand in the
    // entry holdings. A bare `consumes m` of a linear parameter is a value,
    // not a carrier touch, and stays out.
    let mut beruehrt: BTreeMap<(String, String), Vec<String>> = BTreeMap::new();
    let gute2: Vec<String> = marken.iter().filter(|m| !schlecht.contains(*m)).cloned().collect();
    for m in &gute2 {
        for s in &stellen {
            let mut braucht: BTreeMap<String, Vec<String>> = BTreeMap::new();
            let mut zeiger: BTreeMap<String, String> = BTreeMap::new();
            for (pname, ptyp) in &s.parameter {
                if let Some(t) = zeiger_ziel(ptyp) {
                    zeiger.insert(pname.clone(), t);
                }
            }
            // **A read in `E010` text form** (`Plaetze.slots[…]`): the base up
            // to the first `.`/`[`/`-` is the resolution `loese` does on the
            // `Ort` -- a bare name that is a parameter is a value, anything
            // else resolves like a touch.
            let loese_lese = |text: &str, braucht: &mut BTreeMap<String, Vec<String>>| {
                let base = text.split(['.', '[', '-']).next().unwrap_or(text);
                if text == base && s.parameter.iter().any(|(p, _)| p == base) {
                    return;
                }
                let ziel = if traeger.contains(base) {
                    Some(base.to_string())
                } else {
                    zeiger.get(base).cloned()
                };
                let Some(t) = ziel else { return };
                if eigner_von.get(&t) == Some(m) {
                    braucht.entry(m.clone()).or_default().push(t);
                }
            };
            let loese = |ort: &Ort, braucht: &mut BTreeMap<String, Vec<String>>| {
                let name = ort.basis.text.clone();
                if ort.suffixe.is_empty() && s.parameter.iter().any(|(p, _)| *p == name) {
                    return;
                }
                let ziel = if traeger.contains(&name) {
                    Some(name.clone())
                } else {
                    zeiger.get(&name).cloned()
                };
                let Some(t) = ziel else { return };
                if eigner_von.get(&t) == Some(m) {
                    braucht.entry(m.clone()).or_default().push(t);
                }
            };
            match &s.koerper {
                Some(b) => {
                    let mut ziele = Vec::new();
                    let mut brueche = Vec::new();
                    sammle(b, &mut ziele, &mut brueche);
                    for (ort, _) in &ziele {
                        loese(ort, &mut braucht);
                    }
                    for (text, _) in crate::wirkungen::lese_orte(b) {
                        loese_lese(&text, &mut braucht);
                    }
                    for w in &s.wirkungen {
                        match &w.art {
                            WirkungArt::Verbraucht(o) | WirkungArt::Veroeffentlicht(o) => {
                                loese(o, &mut braucht);
                            }
                            _ => {}
                        }
                    }
                }
                None => {
                    for w in &s.wirkungen {
                        match &w.art {
                            WirkungArt::Liest(o)
                            | WirkungArt::Schreibt(o)
                            | WirkungArt::Verbraucht(o)
                            | WirkungArt::Veroeffentlicht(o) => {
                                loese(o, &mut braucht);
                            }
                            _ => {}
                        }
                    }
                }
            }
            for (marke, mut traegerliste) in braucht {
                if haelt_marke(s, &marke) {
                    for t in traegerliste.drain(..) {
                        beruehrt.entry((t, marke.clone())).or_default().push(s.name.clone());
                    }
                    continue;
                }
                traegerliste.sort();
                traegerliste.dedup();
                absagen.schiebe(
                    Absage::fehler(
                        "D267",
                        s.span,
                        format!(
                            "`{}` touches `owner {marke}` table{} `{}` but holds no `{marke}`",
                            s.name,
                            if traegerliste.len() == 1 { "" } else { "s" },
                            traegerliste.join("`, `"),
                        ),
                    )
                    .mit_notiz(
                        "every access holds the mark: take `{marke}` as a linear parameter, \
                         borrowed or consumed -- a guard nobody holds at the access is a \
                         sentence, not a discipline",
                    ),
                );
                schlecht.insert(marke.clone());
            }
        }
    }
    // **D268 -- one mint, executed once.** `D266` refuses the second minter
    // DECLARATION; this refuses the second mint EXECUTION. The single minter
    // called twice (`let a = erste(); let b = erste();`) mints two live
    // marks, hence two owners -- exactly what the owner discipline excludes.
    // The mint executes exactly when its site executes, so the rule holds the
    // site: exactly one in the unit, outside every loop form, in a root no
    // call site reaches (an entry: nothing calls it), and that root started
    // at most once (no two thread starts name it). A unit with no starts at
    // all is a library: the closed-world count is zero, and re-invocation
    // from outside is the importer's duty, like every `pub fn` called twice.
    // Taking the minter's address (`&erste`) hides the execution from this
    // count and is refused with it.
    let u = crate::umgebung::Umgebung::sammle(baum);
    let g = crate::aufrufgraph::erhebe_mit(baum, &u);
    // Thread starts, one pool like `startexklusiv.rs`: `concurrent` members,
    // `entry` dispatch roots, `boot` dispatch. Each names its function key.
    let mut startet: Vec<(String, Span, String)> = Vec::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        if let ItemArt::Concurrent(c) = &item.art {
            for pfad in &c.koerper {
                let span = pfad.teile.last().map(|i| i.span).unwrap_or(item.span);
                if let Some(k) = g.aufloesen(&u, modul, &pfad.text()) {
                    startet.push((k, span, format!("concurrent member `{}`", pfad.text())));
                }
            }
        }
        if let ItemArt::Boot(b) = &item.art {
            if let Some(k) = g.aufloesen(&u, modul, &b.dispatch.text()) {
                startet.push((k, item.span, format!("boot `{}`", b.name.text)));
            }
        }
    });
    for k in crate::kontexte::erhebe(baum) {
        if let Some(voll) = g.aufloesen(&u, &k.modul, &k.wurzel) {
            startet.push((voll, k.span, format!("entry `{}`", k.name)));
        }
    }
    let gute3: Vec<String> = marken
        .iter()
        .filter(|m| minter.contains_key(*m) && !schlecht.contains(*m))
        .cloned()
        .collect();
    // Mint executions per mark, for the lift below: a minter nobody calls is
    // an unexercised producer (`D026`), not a held one.
    let mut mint_aufrufe: BTreeMap<String, usize> = BTreeMap::new();
    for m in &gute3 {
        let (_, _, mschluessel) = &minter[m.as_str()];
        // Every static call of the minter: enclosing root key, site span,
        // and whether a loop form may repeat it. Contract calls count: a
        // contract calling the minter executes it.
        struct Treffer {
            wurzel: String,
            name: String,
            span: Span,
            schleife: bool,
        }
        let mut treffer: Vec<Treffer> = Vec::new();
        let mut adressen: Vec<Span> = Vec::new();
        let nimm = |wurzel: &str, name: &str, modul: &str, fund: &RufFund,
                        treffer: &mut Vec<Treffer>, adressen: &mut Vec<Span>| {
            let Some(k) = g.aufloesen(&u, modul, &fund.pfad) else { return };
            if k != *mschluessel {
                return;
            }
            if fund.adresse {
                adressen.push(fund.span);
            } else {
                treffer.push(Treffer {
                    wurzel: wurzel.to_string(),
                    name: name.to_string(),
                    span: fund.span,
                    schleife: fund.schleife,
                });
            }
        };
        for s in &stellen {
            if let Some(b) = &s.koerper {
                let mut funde = Vec::new();
                rufe_in_block(b, false, &mut funde);
                for f in &funde {
                    nimm(&s.schluessel, &s.name, &s.modul, f, &mut treffer, &mut adressen);
                }
            }
            for pr in &s.vertraege {
                for e in crate::ausdruecke_im_praedikat(pr) {
                    let mut funde = Vec::new();
                    rufe_in_expr(e, false, &mut funde);
                    for f in &funde {
                        nimm(&s.schluessel, &s.name, &s.modul, f, &mut treffer, &mut adressen);
                    }
                }
            }
        }
        // Boot steps execute once, at boot: they count as sites under a
        // caller-free synthetic root (nothing calls a boot).
        crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
            let ItemArt::Boot(b) = &item.art else { return };
            let wurzel = crate::umgebung::qualifiziere(modul, &b.name.text);
            for schritt in &b.schritte {
                match schritt {
                    BootSchritt::Ruf(r) => {
                        let mut funde = Vec::new();
                        ruf_fund(r, false, &mut funde);
                        for a in &r.argumente {
                            rufe_in_expr(a, false, &mut funde);
                        }
                        for f in &funde {
                            nimm(&wurzel, &b.name.text, modul, f, &mut treffer, &mut adressen);
                        }
                    }
                    BootSchritt::Setzt { wert, .. } => {
                        let mut funde = Vec::new();
                        rufe_in_expr(wert, false, &mut funde);
                        for f in &funde {
                            nimm(&wurzel, &b.name.text, modul, f, &mut treffer, &mut adressen);
                        }
                    }
                }
            }
        });
        mint_aufrufe.insert(m.clone(), treffer.len());
        // (a) A second static site mints a second live mark.
        if treffer.len() >= 2 {
            absagen.schiebe(
                Absage::fehler(
                    "D268",
                    treffer[1].span,
                    format!(
                        "`{}` calls the minter `{m}` a second time -- one mark, one mint",
                        treffer[1].name,
                    ),
                )
                .mit_notiz(
                    "the single minter called twice mints two live marks, hence two owners: \
                     call it exactly once, outside every loop, from a root nothing calls",
                ),
            );
            schlecht.insert(m.clone());
        }
        // (b) A site inside a loop form executes on every pass.
        for t in treffer.iter().filter(|t| t.schleife) {
            absagen.schiebe(
                Absage::fehler(
                    "D268",
                    t.span,
                    format!(
                        "`{}` calls the minter `{m}` inside a loop -- the mint repeats",
                        t.name,
                    ),
                )
                .mit_notiz(
                    "a mint inside `traverse`/`retry`/`forever` executes on every pass and \
                     mints a live mark per pass: lift the call before the loop",
                ),
            );
            schlecht.insert(m.clone());
        }
        // (c) A root that is itself called executes the mint on every call.
        // (d) A root started twice executes the mint on every start.
        let mut wurzeln: Vec<String> = treffer.iter().map(|t| t.wurzel.clone()).collect();
        wurzeln.sort();
        wurzeln.dedup();
        for w in &wurzeln {
            let rufer: Vec<String> = g
                .knoten
                .iter()
                .filter(|(_, k)| k.ruft.contains(w))
                .map(|(k, _)| k.clone())
                .collect();
            if let Some(rufer1) = rufer.first() {
                let t = treffer.iter().find(|t| &t.wurzel == w).unwrap_or(&treffer[0]);
                // Graph keys are qualified (`mod::f`); the message names the short form.
                let kurz = rufer1.rsplit("::").next().unwrap_or(rufer1);
                absagen.schiebe(
                    Absage::fehler(
                        "D268",
                        t.span,
                        format!(
                            "`{}` calls the minter `{m}`, but `{kurz}` calls `{}` -- the mint repeats",
                            t.name, t.name,
                        ),
                    )
                    .mit_notiz(
                        "the mint executes exactly when its site executes: hold the single site \
                         in a root no call site reaches (an entry), so it runs once",
                    ),
                );
                schlecht.insert(m.clone());
            }
            let starts: Vec<(Span, String)> = startet
                .iter()
                .filter(|(k, _, _)| k == w)
                .map(|(_, s, q)| (*s, q.clone()))
                .collect();
            if starts.len() >= 2 {
                let t = treffer.iter().find(|t| &t.wurzel == w).unwrap_or(&treffer[0]);
                absagen.schiebe(
                    Absage::fehler(
                        "D268",
                        starts[1].0,
                        format!(
                            "`{}` is started twice ({} and {}) and calls the minter `{m}` -- the mint repeats",
                            t.name, starts[0].1, starts[1].1,
                        ),
                    )
                    .mit_notiz(
                        "one live mark means one execution: start the minting root at most once",
                    ),
                );
                schlecht.insert(m.clone());
            }
        }
        // (e) Taking the minter's address hides the execution from this count.
        for span in &adressen {
            absagen.schiebe(
                Absage::fehler(
                    "D268",
                    *span,
                    format!(
                        "the minter `{m}` is taken as a value here -- the mint could execute through the pointer",
                    ),
                )
                .mit_notiz(
                    "one mark, one statically counted mint: a minter behind a pointer may \
                     execute any number of times, so its address must not be taken",
                ),
            );
            schlecht.insert(m.clone());
        }
    }
    // **The lift.** A table is refused here only while its mark's story is
    // incomplete: no minter, no guarded access exercising it, or no mint
    // execution reaching it. A malformed story (`schlecht`) is refused above
    // and stays silent here.
    crate::fuer_jedes_item(baum, &mut |item| {
        let ItemArt::Tabelle(t) = &item.art else { return };
        let Some(m) = &t.eigner else { return };
        if schlecht.contains(&m.text) {
            return;
        }
        let vollstaendig = minter.contains_key(&m.text)
            && mint_aufrufe.get(&m.text).is_some_and(|&n| n == 1)
            && beruehrt.keys().any(|(tabelle, marke)| tabelle == &t.name.text && marke == &m.text);
        if vollstaendig {
            return;
        }
        absagen.schiebe(
            Absage::fehler(
                "D026",
                m.span,
                format!(
                    "`table {}` names `owner {}`, and no pass holds that mark yet",
                    t.name.text, m.text
                ),
            )
            .mit_notiz(
                "the grammar promises a guard (`SYNTAX.md` §9) that the checker \
                 cannot enforce: who mints the FIRST mark is unwritten, and a \
                 guard nobody holds is a sentence, not a discipline",
            )
            .mit_notiz(
                "until the producer story stands, an `owner` table is unwritable \
                 -- remove the clause and guard the table with `protects`",
            ),
        );
    });
}

/// The bare name of a return or parameter type (`-> Marke`), if it is one.
fn nackter_name(typ: &Option<TypExpr>) -> Option<(String, Span)> {
    match typ {
        Some(t @ TypExpr::Pfad(pf)) => pf.teile.last().map(|i| (i.text.clone(), t.span())),
        _ => None,
    }
}

/// Whether the signature holds the mark: some parameter is of that bare type,
/// borrowed or consumed -- both stand in the entry holdings.
fn haelt_marke(s: &Stelle, marke: &str) -> bool {
    s.parameter.iter().any(|(_, t)| match t {
        TypExpr::Pfad(pf) => pf.teile.last().is_some_and(|i| i.text == marke),
        _ => false,
    })
}

/// The table a pointer type points at (`ptr<…, …> T`), if it names one by a
/// bare path. Deeper targets (arrays, compounds) are not carriers.
fn zeiger_ziel(typ: &TypExpr) -> Option<String> {
    match typ {
        TypExpr::Zeiger(z) => match &z.ziel {
            TypExpr::Pfad(pf) => pf.teile.last().map(|i| i.text.clone()),
            _ => None,
        },
        _ => None,
    }
}

fn baumkanten(baum: &Programm, absagen: &mut Absagen) {
    crate::fuer_jedes_item(baum, &mut |item| {
        let ItemArt::Tabelle(t) = &item.art else { return };
        let Some(b) = &t.baum else { return };
        let felder: BTreeMap<&str, &TypExpr> = t
            .slot
            .iter()
            .flat_map(|s| s.felder.iter())
            .filter_map(|f| match &f.typ {
                SlotTyp::Typ(x) => Some((f.name.text.as_str(), x)),
                // Ein umlaufender Ganzzahlslot ist nie `option index into` -- er faellt
                // gleich hier heraus und dann an `D007`.
                SlotTyp::Wrapping(_) => None,
            })
            .collect();
        for (wort, kante) in [
            ("parent", &b.elter),
            ("child", &b.kind),
            ("sibling", &b.geschwister),
        ] {
            let Some(k) = kante else { continue };
            let Some(typ) = felder.get(k.text.as_str()) else {
                absagen.schiebe(
                    Absage::fehler(
                        "D006",
                        k.span,
                        format!(
                            "`tree {wort} {}` names no field of `{}`'s slot",
                            k.text, t.name.text
                        ),
                    )
                    .mit_notiz("an edge is a FIELD of the slot -- a name that stands nowhere is none"),
                );
                continue;
            };
            match typ {
                TypExpr::Index { tabelle, optional: true, .. } if tabelle.text == t.name.text => {}
                TypExpr::Index { tabelle, optional: true, .. } => {
                    absagen.schiebe(
                        Absage::fehler(
                            "D008",
                            k.span,
                            format!(
                                "`tree {wort} {}` points into `{}`, not into `{}` itself",
                                k.text, tabelle.text, t.name.text
                            ),
                        )
                        .mit_notiz(
                            "a tree edge stays inside its own table -- an edge into another \
                             one is a foreign key, and `descendants of` says nothing about that",
                        ),
                    );
                }
                _ => {
                    absagen.schiebe(
                        Absage::fehler(
                            "D007",
                            k.span,
                            format!(
                                "`tree {wort} {}` is not `option index into {}`",
                                k.text, t.name.text
                            ),
                        )
                        .mit_notiz(
                            "the edge must be able to END, and the sentinel for that is `count` \
                             itself (beweise/Option_Sonderwert.thy) -- an `index into T` without \
                             `option` has no end",
                        ),
                    );
                }
            }
        }
    });
}

/// One static execution of a call for the single-mint count (`D268`): the
/// written path, where it stands, whether a loop form may repeat it, and
/// whether it takes an address instead of calling (`&f` hides the execution
/// from the count).
struct RufFund {
    pfad: String,
    span: Span,
    schleife: bool,
    adresse: bool,
}

/// One `Ruf` node as a find: named callees only (an indirect call through a
/// place names nothing statically, and a minter behind a pointer is (e) --
/// the address refused where it is taken).
fn ruf_fund(r: &Ruf, schleife: bool, aus: &mut Vec<RufFund>) {
    if crate::ist_praedikatswort(r) {
        return;
    }
    if let CallTarget::Path(p) = &r.ziel {
        aus.push(RufFund {
            pfad: p.text(),
            span: r.span,
            schleife,
            adresse: false,
        });
    }
}

/// Every static call and address-taken inside one expression, through the
/// same descent the hull and the graph read (`crate::alle_ausdruecke`).
fn rufe_in_expr(e: &Expr, schleife: bool, aus: &mut Vec<RufFund>) {
    for x in crate::alle_ausdruecke(e) {
        match &x.art {
            ExprArt::Ruf(r) => {
                if crate::ist_praedikatswort(r) {
                    continue;
                }
                if let CallTarget::Path(p) = &r.ziel {
                    aus.push(RufFund {
                        pfad: p.text(),
                        span: r.span,
                        schleife,
                        adresse: false,
                    });
                }
            }
            ExprArt::FnWert(p) => {
                aus.push(RufFund {
                    pfad: p.text(),
                    span: x.span,
                    schleife,
                    adresse: true,
                });
            }
            _ => {}
        }
    }
}

/// Every static call and address-taken in a body, carrying whether a loop
/// form (`traverse`/`retry`/`forever`) may repeat the site. A `retry … until`
/// predicate evaluates on every pass, so the statement's own expressions
/// count as inside the loop exactly where the statement is one.
fn rufe_in_block(b: &Block, schleife: bool, aus: &mut Vec<RufFund>) {
    for s in &b.anweisungen {
        let innen = schleife || matches!(&s.art, StmtArt::Schleife(_));
        for e in crate::eigene_ausdruecke(s) {
            rufe_in_expr(e, innen, aus);
        }
        for pr in crate::eigene_praedikate(s) {
            for e in crate::ausdruecke_im_praedikat(pr) {
                rufe_in_expr(e, innen, aus);
            }
        }
        match &s.art {
            // `eigene_ausdruecke` carries no `Ruf`-statement arguments (the
            // call stands in the statement, not in an `Expr`), so they are
            // read here.
            StmtArt::Ruf(r) => {
                ruf_fund(r, innen, aus);
                for a in &r.argumente {
                    rufe_in_expr(a, innen, aus);
                }
            }
            StmtArt::LetSonst(l) => {
                if let Some(r) = l.als_ruf() {
                    ruf_fund(r, innen, aus);
                    for a in &r.argumente {
                        rufe_in_expr(a, innen, aus);
                    }
                }
            }
            _ => {}
        }
        for k in crate::unterbloecke(s) {
            rufe_in_block(k, innen, aus);
        }
    }
}
