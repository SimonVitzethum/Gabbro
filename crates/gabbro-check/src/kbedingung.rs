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
use std::collections::BTreeMap;

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
            if let ExprArt::Ort(o) = &m.gegenstand.art {
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
