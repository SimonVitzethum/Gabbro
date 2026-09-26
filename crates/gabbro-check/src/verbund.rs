//! **`gabbro link` -- two separately compiled units, and whether they make ONE program.**
//!
//! Opus agent E, 2026-09-26. The Lean side is `GabbroZielVerbund`
//! (`grammatik/Grammatik/Zielsatz/Spec.lean`, proved as `gabbro_ziel_verbund` in
//! `Zielsatz/Verbund.lean`): two units over ONE link declaration, each accepted ALONE, the
//! link check, the SAME hardware assumptions -- then every leg of the goal holds on the linked
//! program. This module is the checker's half of that statement's premises that the per-unit
//! passes cannot see.
//!
//! ## What a unit sees of the other one
//!
//! An importer names an imported function by an `extern fn` HEAD -- written by hand, or
//! pasted in through `--with lib.gabi` (`gabbro abi` writes the exporter's heads). Its own
//! check then relies on that head: the parameters and the result, the `requires`/`ensures`,
//! the `effects` (the footprint summary of the exporter's hull) and the `costs`. **Nothing
//! held the head against the body it stands for.** A `.gabi` written before the library
//! changed its contract, or a head typed from memory, passed both units' checks and linked
//! (`ld` resolves by NAME, and a name says nothing about a contract).
//!
//! ## The five refusals
//!
//! | code | the link declaration is not ONE declaration because | Lean |
//! |---|---|---|
//! | `N501` | a head's parameters, result or error channel differ from the body's; the head names a private function; both units define one function; a shared exported declaration (table, lock, type, …) differs | `Verbindbar`, the shared `D` |
//! | `N502` | the head's `requires`/`ensures` differ from the exporter's -- a weaker OR a stronger contract | `Verbindbar.requires`/`.ensures` |
//! | `N503` | the footprints do not compose: the head's `effects` differ from the exporter's; the exporter's hull calls BACK into the importer; or BOTH units start threads (the cross-unit race check over composed hulls is Lean's `SchnittstelleSpec`, not built here) | `SchnittstelleSpec` (`keinRueckruf`, `lok`, `renn`, `einzeln`) |
//! | `N504` | the head promises a smaller `costs` bound than the exporter declares | (costs are not in G) |
//! | `N505` | the hardware assumptions differ: an `assume`/`axiom`, a `device`, the `profile`, or a foreign `extern fn` both units name, with different content | `E₂.Q = E₁.Q` |
//!
//! ## What this does NOT check, named
//!
//! * **Semantic** contract comparison. Two contracts are the same when their conjuncts are the
//!   same TEXT (whitespace-normalised, order-free). An importer that relies on LESS than the
//!   exporter promises is refused too: the Lean statement has ONE contract per function.
//! * **Threads on both sides.** Refused (`N503`) rather than checked: the per-unit passes see
//!   one side's threads each, and the composed-hull check of `SchnittstelleSpec` is not
//!   ported to Rust.
//! * **Multi-file units, and `gabbro build`.** A unit is one file here (plus `--with`
//!   preambles on the importer side); the manifest build does not call this check yet.
//! * **The C link step** -- symbol resolution, calling convention, layout: translation
//!   validation's, like every "machine G is the meaning of the C".

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};
use gabbro_syntax::span::Span;
use std::collections::{BTreeMap, BTreeSet};

/// One unit as the linker reads it.
pub struct Einheit<'a> {
    /// The unit's name in reports (its file).
    pub name: &'a str,
    pub baum: &'a Programm,
    /// The source the spans point into (preamble included).
    pub quelle: &'a str,
    /// Byte offset where the unit's OWN text begins; everything before came in via `--with`.
    pub ab: usize,
}

/// What the link found, for the one-line summary.
#[derive(Debug, Default)]
pub struct Bericht {
    pub importe: usize,
    pub geteilte_deklarationen: usize,
    pub geteilte_annahmen: usize,
}

fn norm(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn schnitt(quelle: &str, sp: Span) -> String {
    norm(quelle.get(sp.von as usize..sp.bis as usize).unwrap_or(""))
}

fn schluessel(modul: &str, name: &str) -> String {
    if modul.is_empty() {
        name.to_string()
    } else {
        format!("{modul}::{name}")
    }
}

/// A function of a unit, by qualified name.
struct Fn<'a> {
    decl: &'a FnDecl,
    modul: String,
}

impl Fn<'_> {
    fn hat_rumpf(&self) -> bool {
        matches!(self.decl.rumpf, FnRumpf::Block(_))
    }
    fn ist_kopf(&self) -> bool {
        matches!(self.decl.rumpf, FnRumpf::Keiner)
            && !matches!(self.decl.klasse, Some(FnKlasse::Spec))
    }
}

/// Every item with its module path -- `fuer_jedes_item_im_modul`, with the borrow kept.
fn alle_items<'a>(baum: &'a Programm) -> Vec<(&'a Item, String)> {
    fn geh<'a>(items: &'a [Item], pfad: &str, aus: &mut Vec<(&'a Item, String)>) {
        for i in items {
            aus.push((i, pfad.to_string()));
            if let ItemArt::Modul(m) = &i.art {
                let innen = if pfad.is_empty() {
                    m.pfad.text()
                } else {
                    format!("{pfad}::{}", m.pfad.text())
                };
                geh(&m.items, &innen, aus);
            }
        }
    }
    let mut aus = Vec::new();
    geh(&baum.items, "", &mut aus);
    aus
}

fn funktionen<'a>(e: &Einheit<'a>) -> BTreeMap<String, Fn<'a>> {
    let mut aus = BTreeMap::new();
    for (item, modul) in alle_items(e.baum) {
        if let ItemArt::Funktion(f) = &item.art {
            aus.insert(schluessel(&modul, &f.name.text), Fn { decl: f, modul });
        }
    }
    aus
}

/// The exported declarations other than functions, by kind and qualified name, as text.
fn deklarationen(e: &Einheit) -> BTreeMap<(String, String), (String, Span)> {
    let mut aus = BTreeMap::new();
    crate::fuer_jedes_item_im_modul(e.baum, &mut |item, modul| {
        if matches!(item.art, ItemArt::Funktion(_) | ItemArt::Device(_)) {
            return;
        }
        let Some(name) = crate::bindung::ausgefuehrter_name(item) else { return };
        let art = match &item.art {
            ItemArt::Statisch(_) => "static",
            ItemArt::Konst(_) => "const",
            ItemArt::Typ(_) => "type",
            ItemArt::Atomic(_) => "atomic",
            ItemArt::Tabelle(_) => "table",
            ItemArt::Arena(_) => "arena",
            ItemArt::Lock(_) => "lock",
            ItemArt::Format(_) => "format",
            _ => "item",
        };
        aus.insert(
            (art.to_string(), schluessel(modul, &name.text)),
            (schnitt(e.quelle, item.span).trim_start_matches("pub ").to_string(), item.span),
        );
    });
    aus
}

/// The hardware-assumption items of a unit: `assume`, `axiom`, `device`, `profile`, by name.
fn annahmen(e: &Einheit) -> BTreeMap<String, (String, Span)> {
    let mut aus = BTreeMap::new();
    crate::fuer_jedes_item_im_modul(e.baum, &mut |item, modul| {
        let schl = match &item.art {
            ItemArt::Assume(a) => format!(
                // An assumption is a fact about the MACHINE, not about a module: the manifest
                // keys it by name and `arch` (`manifest::vereinige`), and so does the link.
                "assume {}{}",
                a.name.text,
                a.arch.as_ref().map(|x| format!(" arch {}", x.text)).unwrap_or_default()
            ),
            ItemArt::Axiom(a) => format!("axiom {}", a.name.text),
            ItemArt::Device(d) => format!("device {}", schluessel(modul, &d.name.text)),
            ItemArt::Profil(_) => "profile".to_string(),
            _ => return,
        };
        aus.insert(
            schl,
            (schnitt(e.quelle, item.span).trim_start_matches("pub ").to_string(), item.span),
        );
    });
    aus
}

/// The signature of a head: parameters with names and types, the result, the error channel.
fn signatur(f: &FnDecl, quelle: &str) -> String {
    let ps: Vec<String> = f
        .parameter
        .iter()
        .map(|p| format!("{} : {}", p.name.text, schnitt(quelle, p.typ.span())))
        .collect();
    format!(
        "({}){}{}",
        ps.join(", "),
        f.ergebnis
            .as_ref()
            .map(|t| format!(" -> {}", schnitt(quelle, t.span())))
            .unwrap_or_default(),
        f.fehler.as_ref().map(|r| format!(" or {}", r.text)).unwrap_or_default()
    )
}

fn saetze(ps: &[Pred], quelle: &str) -> BTreeSet<String> {
    ps.iter().map(|p| schnitt(quelle, p.span)).collect()
}

fn zeige(m: &BTreeSet<String>) -> String {
    if m.is_empty() {
        "(none)".to_string()
    } else {
        m.iter().cloned().collect::<Vec<_>>().join(", ")
    }
}

fn wirkungen(f: &FnDecl, quelle: &str) -> Option<BTreeSet<String>> {
    f.effects
        .as_ref()
        .map(|w| w.liste.iter().map(|x| schnitt(quelle, x.span)).collect())
}

fn kosten(f: &FnDecl, quelle: &str) -> Option<String> {
    f.costs.as_ref().map(|c| schnitt(quelle, c.span))
}

/// Does the unit start threads -- `concurrent`, `entry`, `boot`, a hosted `start`, a `child`?
fn faden_ort(baum: &Programm) -> Option<Span> {
    fn im_block(b: &Block) -> Option<Span> {
        for s in &b.anweisungen {
            match &s.art {
                StmtArt::Start(_) | StmtArt::Child(_) => return Some(s.span),
                _ => {
                    for k in crate::unterbloecke(s) {
                        if let Some(x) = im_block(k) {
                            return Some(x);
                        }
                    }
                }
            }
        }
        None
    }
    let mut ort = None;
    crate::fuer_jedes_item_im_modul(baum, &mut |item, _| {
        if ort.is_some() {
            return;
        }
        match &item.art {
            ItemArt::Concurrent(_) | ItemArt::Entry(_) | ItemArt::Boot(_) => ort = Some(item.span),
            ItemArt::Funktion(f) => {
                if let FnRumpf::Block(b) = &f.rumpf {
                    ort = im_block(b);
                }
            }
            _ => {}
        }
    });
    ort
}

/// **The link check.** Refusals land in the Absagen of the unit whose text they point into.
/// Both directions: each unit may import from the other.
pub fn verbinde(
    a: &Einheit,
    b: &Einheit,
    abs_a: &mut Absagen,
    abs_b: &mut Absagen,
) -> Bericht {
    let mut bericht = Bericht::default();
    let fa = funktionen(a);
    let fb = funktionen(b);
    // ---- functions: imports, double definitions, foreign heads ----
    for (schl, x) in &fa {
        let Some(y) = fb.get(schl) else { continue };
        if x.hat_rumpf() && y.hat_rumpf() {
            abs_b.schiebe(
                Absage::fehler(
                    "N501",
                    y.decl.name.span,
                    format!(
                        "`{schl}` has a body in both units ({} and {}): the linked program \
                         would define one function twice",
                        a.name, b.name
                    ),
                )
                .mit_notiz(
                    "a function has ONE owner (`verbinde` in `Zielsatz/Spec.lean` takes every \
                     body from its owner); let the other unit import it by an `extern fn` head",
                ),
            );
            continue;
        }
        let richtung = if x.hat_rumpf() && y.ist_kopf() {
            Some(true)
        } else if y.hat_rumpf() && x.ist_kopf() {
            Some(false)
        } else {
            None
        };
        let Some(a_exportiert) = richtung else {
            // Two heads, no body on either side: a FOREIGN function both units rely on -- a
            // hardware assumption (`D.Ax` in the model), so its two statements must agree.
            if x.ist_kopf() && y.ist_kopf() {
                let tx = schnitt(a.quelle, x.decl.span);
                let ty = schnitt(b.quelle, y.decl.span);
                bericht.geteilte_annahmen += 1;
                if tx.trim_start_matches("pub ") != ty.trim_start_matches("pub ") {
                    abs_b.schiebe(
                        Absage::fehler(
                            "N505",
                            y.decl.name.span,
                            format!(
                                "the foreign function `{schl}` is declared differently in the \
                                 two units: the linked program would run under two statements \
                                 of one hardware assumption"
                            ),
                        )
                        .mit_notiz(format!("{}: {tx}", a.name))
                        .mit_notiz(format!("{}: {ty}", b.name))
                        .mit_notiz(
                            "linking is claimed only under the SAME hardware assumptions \
                             (`E₂.Q = E₁.Q` in `GabbroZielVerbund`): state it once, identically",
                        ),
                    );
                }
            }
            continue;
        };
        let (ex, im, ex_e, im_e) = if a_exportiert { (x, y, a, b) } else { (y, x, b, a) };
        let abs_im: &mut Absagen = if a_exportiert { &mut *abs_b } else { &mut *abs_a };
        bericht.importe += 1;
        let ort = im.decl.name.span;
        if !ex.decl.oeffentlich {
            abs_im.schiebe(
                Absage::fehler(
                    "N501",
                    ort,
                    format!(
                        "`{schl}` is imported, but {} does not export it (no `pub`)",
                        ex_e.name
                    ),
                )
                .mit_notiz("only a `pub fn` crosses the unit boundary (`gabbro abi` writes exactly those)"),
            );
            continue;
        }
        let (s_ex, s_im) = (signatur(ex.decl, ex_e.quelle), signatur(im.decl, im_e.quelle));
        if s_ex != s_im {
            abs_im.schiebe(
                Absage::fehler(
                    "N501",
                    ort,
                    format!("the head of `{schl}` does not match its body's signature"),
                )
                .mit_notiz(format!("head ({}): {s_im}", im_e.name))
                .mit_notiz(format!("body ({}): {s_ex}", ex_e.name))
                .mit_notiz(
                    "the importer was checked against this head: parameters, result and error \
                     channel are part of the ONE link declaration (`Verbindbar`)",
                ),
            );
        }
        let (rq_ex, rq_im) = (saetze(&ex.decl.requires, ex_e.quelle), saetze(&im.decl.requires, im_e.quelle));
        let (en_ex, en_im) = (saetze(&ex.decl.ensures, ex_e.quelle), saetze(&im.decl.ensures, im_e.quelle));
        if rq_ex != rq_im || en_ex != en_im {
            let mut a = Absage::fehler(
                "N502",
                ort,
                format!(
                    "the contract the importer relies on for `{schl}` is not the exporter's"
                ),
            );
            if en_im.difference(&en_ex).next().is_some() {
                a = a.mit_notiz(format!(
                    "the head promises `ensures {}`, the body only `ensures {}` -- the \
                     exported contract is too weak for this importer",
                    zeige(&en_im),
                    zeige(&en_ex)
                ));
            } else if en_im != en_ex {
                a = a.mit_notiz(format!(
                    "`ensures` differs: head {}, body {}",
                    zeige(&en_im),
                    zeige(&en_ex)
                ));
            }
            if rq_ex.difference(&rq_im).next().is_some() {
                a = a.mit_notiz(format!(
                    "the body needs `requires {}`, the head asks only `requires {}` -- the \
                     importer's calls are not held to the exporter's precondition",
                    zeige(&rq_ex),
                    zeige(&rq_im)
                ));
            } else if rq_ex != rq_im {
                a = a.mit_notiz(format!(
                    "`requires` differs: head {}, body {}",
                    zeige(&rq_im),
                    zeige(&rq_ex)
                ));
            }
            abs_im.schiebe(a.mit_notiz(
                "the linked program has ONE contract per function (`Verbindbar.requires`, \
                 `.ensures` in `Zielsatz/Spec.lean`): regenerate the head with `gabbro abi`",
            ));
        }
        match (wirkungen(ex.decl, ex_e.quelle), wirkungen(im.decl, im_e.quelle)) {
            (Some(w_ex), Some(w_im)) if w_ex == w_im => {}
            (w_ex, w_im) => {
                abs_im.schiebe(
                    Absage::fehler(
                        "N503",
                        ort,
                        format!(
                            "the effects the importer relies on for `{schl}` are not the \
                             exporter's: the footprints do not compose"
                        ),
                    )
                    .mit_notiz(format!(
                        "head: {}",
                        w_im.map(|m| format!("effects {{ {} }}", zeige(&m)))
                            .unwrap_or_else(|| "no effects clause".into())
                    ))
                    .mit_notiz(format!(
                        "body: {}",
                        w_ex.map(|m| format!("effects {{ {} }}", zeige(&m)))
                            .unwrap_or_else(|| "no written effects clause".into())
                    ))
                    .mit_notiz(
                        "the head's effects are the summary of the exporter's hull the \
                         importer's race and footprint checks read (`HuelleV`, \
                         `SchnittstelleSpec.lok`/`.renn` in `Zielsatz/Spec.lean`)",
                    ),
                );
            }
        }
        match (kosten(ex.decl, ex_e.quelle), kosten(im.decl, im_e.quelle)) {
            (_, None) => {}
            (Some(k_ex), Some(k_im)) => {
                let passt = match (k_ex.parse::<u64>(), k_im.parse::<u64>()) {
                    (Ok(x), Ok(y)) => x <= y,
                    _ => k_ex == k_im,
                };
                if !passt {
                    abs_im.schiebe(
                        Absage::fehler(
                            "N504",
                            ort,
                            format!(
                                "the head of `{schl}` promises `costs <= {k_im}`, the \
                                 exporter declares `costs <= {k_ex}`"
                            ),
                        )
                        .mit_notiz(
                            "the importer's cost bounds were computed with the head's number; \
                             a larger exported bound breaks every one of them",
                        ),
                    );
                }
            }
            (None, Some(k_im)) => {
                abs_im.schiebe(
                    Absage::fehler(
                        "N504",
                        ort,
                        format!(
                            "the head of `{schl}` promises `costs <= {k_im}`, the exporter \
                             declares no cost bound"
                        ),
                    )
                    .mit_notiz("an undeclared cost is no bound the importer may add up"),
                );
            }
        }
    }
    // ---- callbacks: an imported function's hull must stay in its owner ----
    for (ex_e, im_e, f_ex, f_im, abs_im) in [
        (a, b, &fa, &fb, &mut *abs_b),
        (b, a, &fb, &fa, &mut *abs_a),
    ] {
        let g = crate::aufrufgraph::erhebe(ex_e.baum);
        for (schl, im) in f_im.iter() {
            let Some(ex) = f_ex.get(schl) else { continue };
            if !(ex.hat_rumpf() && im.ist_kopf()) {
                continue;
            }
            let start = g.schluessel_von(&ex.modul, &ex.decl.name.text);
            for fremd in g.fremde_in_huelle(&start) {
                if fremd == start {
                    continue;
                }
                if f_im.get(&fremd).is_some_and(|z| z.hat_rumpf()) {
                    abs_im.schiebe(
                        Absage::fehler(
                            "N503",
                            im.decl.name.span,
                            format!(
                                "`{schl}` calls back into {}: its hull in {} reaches \
                                 `{fremd}`, which {} defines",
                                im_e.name, ex_e.name, im_e.name
                            ),
                        )
                        .mit_notiz(
                            "an imported head summarises the exporter's hull; a hull that \
                             re-enters the importer is no summary (`KeinRueckruf` in \
                             `Zielsatz/Spec.lean`)",
                        ),
                    );
                }
            }
        }
    }
    // ---- threads on both sides ----
    if let (Some(_), Some(ort_b)) = (faden_ort(a.baum), faden_ort(b.baum)) {
        abs_b.schiebe(
            Absage::fehler(
                "N503",
                ort_b,
                format!(
                    "both {} and {} start threads: their footprints are checked per unit, \
                     and no pass here composes one unit's threads with the other's",
                    a.name, b.name
                ),
            )
            .mit_notiz(
                "the composed-hull check is `SchnittstelleSpec` (`lok`, `renn`, `einzeln`) in \
                 `Zielsatz/Spec.lean` -- decided in Lean, not ported to this linker; start the \
                 threads in ONE unit",
            ),
        );
    }
    // ---- shared exported declarations: ONE link declaration ----
    let (da, db) = (deklarationen(a), deklarationen(b));
    for (schl, (tb, sp_b)) in &db {
        let Some((ta, _)) = da.get(schl) else { continue };
        bericht.geteilte_deklarationen += 1;
        if ta != tb {
            abs_b.schiebe(
                Absage::fehler(
                    "N501",
                    *sp_b,
                    format!(
                        "the {} `{}` is declared differently in the two units",
                        schl.0, schl.1
                    ),
                )
                .mit_notiz(format!("{}: {ta}", a.name))
                .mit_notiz(format!("{}: {tb}", b.name))
                .mit_notiz("both units must be checked over ONE link declaration (`Verbindbar`)"),
            );
        }
    }
    // ---- hardware assumptions: the SAME for both units ----
    let (ha, hb) = (annahmen(a), annahmen(b));
    for (schl, (tb, sp_b)) in &hb {
        let Some((ta, _)) = ha.get(schl) else { continue };
        bericht.geteilte_annahmen += 1;
        if ta != tb {
            abs_b.schiebe(
                Absage::fehler(
                    "N505",
                    *sp_b,
                    format!(
                        "`{schl}` is stated differently in the two units: the linked program \
                         would run under two different hardware assumptions"
                    ),
                )
                .mit_notiz(format!("{}: {ta}", a.name))
                .mit_notiz(format!("{}: {tb}", b.name))
                .mit_notiz(
                    "linking is claimed only under the SAME hardware assumptions (`E₂.Q = E₁.Q` \
                     in `GabbroZielVerbund`, `Zielsatz/Spec.lean`)",
                ),
            );
        }
    }
    bericht
}

#[cfg(test)]
mod tests {
    //! Snippet probes of the refusals the probe files under `messung/proben/verbund/` do not
    //! reach (those are driven by `crates/gabbro-cli/tests/verbund.rs`).
    use super::*;

    /// Links two snippet units and returns every code, in unit order (A's, then B's).
    fn links(a: &str, b: &str) -> Vec<&'static str> {
        let (ba, _) = gabbro_syntax::lies("a.gab", a);
        let (bb, _) = gabbro_syntax::lies("b.gab", b);
        let ea = Einheit { name: "a.gab", baum: &ba, quelle: a, ab: 0 };
        let eb = Einheit { name: "b.gab", baum: &bb, quelle: b, ab: 0 };
        let mut xa = Absagen::neu("a.gab");
        let mut xb = Absagen::neu("b.gab");
        verbinde(&ea, &eb, &mut xa, &mut xb);
        xa.absagen.iter().chain(xb.absagen.iter()).map(|x| x.code).collect()
    }

    const BIB: &str = "module bib {
pub impl fn f() effects { pure } costs <= 8 ops { return; }
}
";
    const APP: &str = "module bib {
pub extern fn f() effects { pure } costs <= 8 ops;
}
module app {
impl fn w() effects { pure } costs <= 16 ops { bib::f(); return; }
}
";

    #[test]
    fn ein_passender_kopf_verbindet_ohne_absage() {
        assert_eq!(links(BIB, APP), Vec::<&str>::new());
    }

    #[test]
    fn ein_rueckruf_durch_den_import_faellt_mit_n503() {
        // `bib::f` calls `app::g` -- a head in the library, a BODY in the app: the hull of
        // the import re-enters the importer.
        let bib = "module app {
pub extern fn g() effects { pure } costs <= 1 ops;
}
module bib {
pub impl fn f() effects { pure } costs <= 8 ops { app::g(); return; }
}
";
        let app = "module bib {
pub extern fn f() effects { pure } costs <= 8 ops;
}
module app {
pub impl fn g() effects { pure } costs <= 1 ops { return; }
impl fn w() effects { pure } costs <= 16 ops { bib::f(); return; }
}
";
        let codes = links(bib, app);
        assert!(codes.contains(&"N503"), "a callback through an import falls with N503: {codes:?}");
    }

    #[test]
    fn faeden_auf_beiden_seiten_fallen_mit_n503() {
        let bib = "module bib {
pub impl fn f() effects { pure } costs <= 8 ops { return; }
impl fn eigen() effects { pure } costs <= 8 ops { return; }
concurrent { eigen, eigen };
}
";
        let app = "module bib {
pub extern fn f() effects { pure } costs <= 8 ops;
}
module app {
impl fn w() effects { pure } costs <= 16 ops { bib::f(); return; }
concurrent { w, w };
}
";
        assert_eq!(links(bib, app), vec!["N503"]);
        // Threads in ONE unit only: silent.
        assert_eq!(links(BIB, app), Vec::<&str>::new());
    }

    #[test]
    fn ein_rumpf_in_beiden_einheiten_faellt_mit_n501() {
        assert_eq!(links(BIB, BIB), vec!["N501"]);
    }

    #[test]
    fn ein_nicht_exportierter_rumpf_faellt_mit_n501() {
        let bib = "module bib {
impl fn f() effects { pure } costs <= 8 ops { return; }
}
";
        assert_eq!(links(bib, APP), vec!["N501"]);
    }

    #[test]
    fn eine_verschieden_erklaerte_tabelle_faellt_mit_n501() {
        let a = "module bib {
pub table T count 2 { slot { a : u32 in 0 .. 10, } }
}
";
        let b = "module bib {
pub table T count 3 { slot { a : u32 in 0 .. 10, } }
}
";
        assert_eq!(links(a, b), vec!["N501"]);
        assert_eq!(links(a, a), Vec::<&str>::new());
    }

    #[test]
    fn eine_fremde_funktion_verschieden_erklaert_faellt_mit_n505() {
        // A foreign function both units rely on, with no body in either: a hardware
        // assumption, and its two statements differ.
        let a = "module c {
pub extern fn uhr() -> u64 effects { pure } costs <= 4 ops;
}
";
        let b = "module c {
pub extern fn uhr() -> u64 ensures result > 0 effects { pure } costs <= 4 ops;
}
";
        assert_eq!(links(a, b), vec!["N505"]);
        assert_eq!(links(a, a), Vec::<&str>::new());
    }
}
