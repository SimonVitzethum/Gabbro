//! **`gabbro link` -- separately compiled units, and whether they make ONE program.**
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
//! ## The refusals
//!
//! | code | the link declaration is not ONE declaration because | Lean |
//! |---|---|---|
//! | `N501` | a head's parameters, result or error channel differ from the body's; the head names a private function; both units define one function; a shared exported declaration (table, lock, type, …) differs | `Verbindbar`, the shared `D` |
//! | `N502` | the head's `requires`/`ensures` differ from the exporter's as TREES -- a weaker OR a stronger contract | `Verbindbar.requires`/`.ensures` |
//! | `N503` | the footprints do not compose: the head's `effects` differ from the exporter's; the exporter's hull calls BACK into the importer | `SchnittstelleSpec.keinRueckruf`, the heads as `HuelleV` summaries |
//! | `N504` | the head promises a smaller `costs` bound than the exporter declares | (costs are not in G) |
//! | `N505` | the hardware assumptions differ: an `assume`/`axiom`, a `device`, the `profile`, or a foreign `extern fn` both units name, with different content | `E₂.Q = E₁.Q` |
//! | `N516` | a module holds items in two units: no linked program can be composed (Opus F) | `verbinde` needs one owner per function |
//!
//! ## The linked program (Opus agent F, review E F1, OFFEN O28)
//!
//! When no head is stale, `pruefe_verbund` composes the units into ONE source -- every body
//! from its owner, every head whose body another unit holds dropped, every shared
//! declaration once, EVERY start of every unit kept (`verbundtext`, the surface of
//! `verbinde e E₁ E₂`) -- and runs the whole checker over it. Its errors keep their one-file
//! codes and land in the unit whose text they point into. That is the Rust decision of
//! `SchnittstelleSpec.lok`/`.renn`/`.einzeln`: the race passes (`fusswache2.rs`) over the
//! linked call graphs, which under `KeinRueckruf` are the composed hulls `HuelleV`. It
//! replaces Opus E's blanket refusal of threads on both sides (`N503`), and it closes the
//! false accept of review E F1 at the link. The same F1 is closed per unit too: a body-less
//! head's declared READS now join the importer's footprint (`fusswache2.rs`), so `gabbro
//! check --with` falls on the reproduction with the one-file `N291`/`N301` already.
//!
//! ## What this does NOT check, named
//!
//! * **Semantic** contract comparison. Two contracts are the same when their conjuncts are the
//!   same TREE (`normalform`: positions and redundant parentheses dropped, order-free). An
//!   equivalent contract written as a different tree is refused, and an importer that relies
//!   on LESS than the exporter promises is refused too: the Lean statement has ONE contract
//!   per function.
//! * **More than Lean re-decides.** The linked program passes EVERY pass, not only the three
//!   whole-program components of the Lean link check; a refusal of another pass there is
//!   reported, not filtered (the safe direction).
//! * **A module split over units** (`N516`): refused, not merged.
//! * **The C link step** -- symbol resolution, calling convention, layout: translation
//!   validation's, like every "machine G is the meaning of the C". No certificate is written
//!   for a linked program (the exporter exports one `Einheit`).

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
    /// Whether the linked program was composed and checked whole (`pruefe_verbund`).
    pub verbund_geprueft: bool,
    /// Errors the whole-program check of the linked program found.
    pub verbund_fehler: usize,
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

/// **The normal form of a syntax node** (Opus F, OFFEN O28 "contracts as text"): the tree's
/// `Debug` form with every source position dropped and every pair of redundant parentheses
/// (`Klammer` around a predicate or an expression) taken out. Two spellings of one tree --
/// other whitespace, other line breaks, `(a)` for `a`, `0x10` for `16` -- give one text; two
/// different trees never do, because nothing but positions and parentheses is removed.
pub fn normalform<T: std::fmt::Debug>(x: &T) -> String {
    let roh = format!("{x:?}");
    // 1. Positions: every `Span { von: N, bis: N }` becomes `_`.
    let mut s = String::with_capacity(roh.len());
    let mut rest = roh.as_str();
    while let Some(i) = rest.find("Span { von: ") {
        s.push_str(&rest[..i]);
        let ab = &rest[i..];
        let Some(ende) = ab.find('}') else {
            rest = ab;
            break;
        };
        s.push('_');
        rest = &ab[ende + 1..];
    }
    s.push_str(rest);
    // 2. Parentheses: `X { art: Klammer(X { art: INNER, span: _ }), span: _ }` becomes
    //    `X { art: INNER, span: _ }` -- for predicates and for expressions.
    loop {
        let mut geaendert = false;
        for knoten in ["Pred", "Expr"] {
            let aussen = format!("{knoten} {{ art: Klammer(");
            let schluss = ", span: _ }";
            let mut von = 0;
            while let Some(k) = s[von..].find(&aussen).map(|k| k + von) {
                let auf = k + aussen.len() - 1;
                let Some(zu) = passende_klammer(&s, auf) else { break };
                if s[auf + 1..].starts_with(&format!("{knoten} {{ ")) && s[zu + 1..].starts_with(schluss) {
                    let innen = s[auf + 1..zu].to_string();
                    s = format!("{}{innen}{}", &s[..k], &s[zu + 1 + schluss.len()..]);
                    geaendert = true;
                    break;
                }
                von = k + 1;
            }
        }
        if !geaendert {
            break;
        }
    }
    s
}

/// The index of the `)` that closes the `(` at the given index, skipping quoted strings.
fn passende_klammer(s: &str, auf: usize) -> Option<usize> {
    let b = s.as_bytes();
    if b.get(auf) != Some(&b'(') {
        return None;
    }
    let (mut tiefe, mut i, mut in_text) = (0i32, auf, false);
    while i < b.len() {
        let c = b[i];
        if in_text {
            if c == b'\\' {
                i += 1;
            } else if c == b'"' {
                in_text = false;
            }
        } else if c == b'"' {
            in_text = true;
        } else if c == b'(' {
            tiefe += 1;
        } else if c == b')' {
            tiefe -= 1;
            if tiefe == 0 {
                return Some(i);
            }
        }
        i += 1;
    }
    None
}

/// The conjuncts of a contract, in normal form: `requires a, b` and `requires (a && b)` are
/// one set -- a contract is the conjunction of its clauses, and order means nothing.
fn konjunkte(ps: &[Pred]) -> BTreeSet<String> {
    fn geh<'a>(p: &'a Pred, aus: &mut Vec<&'a Pred>) {
        match &p.art {
            PredArt::Klammer(x) => geh(x, aus),
            PredArt::Und(a, b) => {
                geh(a, aus);
                geh(b, aus);
            }
            _ => aus.push(p),
        }
    }
    let mut v = Vec::new();
    for p in ps {
        geh(p, &mut v);
    }
    v.into_iter().map(normalform).collect()
}

/// The effects of a head as a set of normal forms (`reads konto.slots` by its tree).
fn wirkungsformen(f: &FnDecl) -> Option<BTreeSet<String>> {
    f.effects
        .as_ref()
        .map(|w| w.liste.iter().map(|x| normalform(&x.art)).collect())
}

/// The signature in normal form: parameter names and type trees, result, error channel.
fn signaturform(f: &FnDecl) -> String {
    let ps: Vec<String> = f
        .parameter
        .iter()
        .map(|p| format!("{}:{}", p.name.text, normalform(&p.typ)))
        .collect();
    format!(
        "({})->{}|{}",
        ps.join(","),
        f.ergebnis.as_ref().map(normalform).unwrap_or_default(),
        f.fehler.as_ref().map(|r| r.text.clone()).unwrap_or_default()
    )
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
        if signaturform(ex.decl) != signaturform(im.decl) {
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
        // Compared as TREES (normal form, conjunct sets), shown as text.
        if konjunkte(&ex.decl.requires) != konjunkte(&im.decl.requires)
            || konjunkte(&ex.decl.ensures) != konjunkte(&im.decl.ensures)
        {
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
        match (wirkungsformen(ex.decl), wirkungsformen(im.decl)) {
            (Some(w_ex), Some(w_im)) if w_ex == w_im => {}
            _ => {
                let (w_ex, w_im) = (wirkungen(ex.decl, ex_e.quelle), wirkungen(im.decl, im_e.quelle));
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

// ======================================================================================
// The linked program (Opus F, OFFEN O28): the units composed as ONE source, checked whole.
// ======================================================================================

/// The linked program as one source text: every unit's text in order, joined by a newline,
/// with each item that another text already contributes blanked out (spaces, newlines kept,
/// so every byte keeps its position). `ab[i]` is where unit `i` begins in `text`.
pub struct Verbundtext {
    pub text: String,
    pub ab: Vec<usize>,
    /// Modules that hold surviving items in two units: `(unit, span, module path)`.
    pub konflikte: Vec<(usize, Span, String)>,
}

/// The key under which an item is ONE item of the linked declaration, and whether it is a
/// definition (a function with a body). `None` for a module (handled by its contents).
fn item_schluessel(item: &Item, modul: &str, quelle: &str) -> Option<(String, bool)> {
    let text = || schnitt(quelle, item.span).trim_start_matches("pub ").to_string();
    Some(match &item.art {
        ItemArt::Modul(_) => return None,
        ItemArt::Funktion(f) => (
            format!("fn {}", schluessel(modul, &f.name.text)),
            !matches!(f.rumpf, FnRumpf::Keiner),
        ),
        ItemArt::Assume(a) => (
            format!(
                "assume {}{}",
                a.name.text,
                a.arch.as_ref().map(|x| format!(" arch {}", x.text)).unwrap_or_default()
            ),
            false,
        ),
        ItemArt::Axiom(a) => (format!("axiom {}", a.name.text), false),
        ItemArt::Profil(_) => ("profile".to_string(), false),
        _ => match crate::bindung::ausgefuehrter_name(item) {
            Some(n) => (
                format!("{:?} {}", std::mem::discriminant(&item.art), schluessel(modul, &n.text)),
                false,
            ),
            // A `use` twice in one module is one `use`. Every other unnamed item -- above
            // all a `concurrent`/`entry`/`boot` start -- is its own item even when two units
            // spell it alike: dropping one would drop threads.
            None if matches!(item.art, ItemArt::Use(_)) => {
                (format!("text {modul} {}", text()), false)
            }
            None => (format!("einzig {:p}", item as *const Item), false),
        },
    })
}

fn leere(text: &mut [u8], sp: Span) {
    let (von, bis) = (sp.von as usize, (sp.bis as usize).min(text.len()));
    for b in text.iter_mut().take(bis).skip(von) {
        if *b != b'\n' {
            *b = b' ';
        }
    }
}

/// Where the one kept copy of an item of the linked program stands.
struct Eigner {
    einheit: usize,
    von: u32,
    rumpf: bool,
    text: String,
}

/// Walks one item list of unit `i`; returns whether every item of it was blanked.
#[allow(clippy::too_many_arguments)]
fn verbund_geh(
    i: usize,
    e: &Einheit,
    items: &[Item],
    pfad: &str,
    definiert: &BTreeMap<String, Eigner>,
    gesehen: &mut BTreeMap<String, String>,
    module_gesehen: &mut BTreeSet<String>,
    text: &mut [u8],
    konflikte: &mut Vec<(usize, Span, String)>,
) -> bool {
    let mut alle = true;
    for item in items {
        if let ItemArt::Modul(m) = &item.art {
            let innen = if pfad.is_empty() {
                m.pfad.text()
            } else {
                format!("{pfad}::{}", m.pfad.text())
            };
            let schon = module_gesehen.contains(&innen);
            let leer = verbund_geh(
                i, e, &m.items, &innen, definiert, gesehen, module_gesehen, text, konflikte,
            );
            if leer {
                // Nothing of it survives (a preamble's copy of another unit's module, or an
                // empty interface): it contributes nothing, and it claims no module.
                leere(text, item.span);
            } else {
                if schon {
                    konflikte.push((i, item.span, innen.clone()));
                }
                module_gesehen.insert(innen);
                alle = false;
            }
            continue;
        }
        let Some((k, _)) = item_schluessel(item, pfad, e.quelle) else { continue };
        let text_hier = schnitt(e.quelle, item.span).trim_start_matches("pub ").to_string();
        let behalten = match definiert.get(&k) {
            // The owner's copy stays: a function's body, else the copy in a unit's OWN text
            // (not in a `--with` preamble). A DIFFERENT copy of a declaration stays too, so the
            // whole-program check names the clash instead of this composition hiding it.
            Some(o) => {
                (o.einheit == i && o.von == item.span.von) || (!o.rumpf && o.text != text_hier)
            }
            // No owner (only preamble copies, e.g. a third library's heads): the first copy
            // stays, and a different one beside it.
            None => gesehen.get(&k).is_none_or(|t| t != &text_hier),
        };
        if behalten {
            gesehen.insert(k, text_hier);
            alle = false;
        } else {
            leere(text, item.span);
        }
    }
    alle
}

/// **Composes the units into the linked program** -- `verbinde e E₁ E₂` of
/// `Zielsatz/Spec.lean` on the surface: every function body from its owner (a head whose body
/// another unit holds is dropped), every shared declaration and hardware assumption once (the
/// pairwise check has already held the copies equal), each unit's starts kept.
pub fn verbundtext(es: &[Einheit]) -> Verbundtext {
    // The owner of each item: for a function, the first unit with a BODY; for anything else
    // (and a function no unit defines), the first copy in a unit's OWN text.
    let mut definiert: BTreeMap<String, Eigner> = BTreeMap::new();
    for rumpfrunde in [true, false] {
        for (i, e) in es.iter().enumerate() {
            for (item, modul) in alle_items(e.baum) {
                let Some((k, rumpf)) = item_schluessel(item, &modul, e.quelle) else { continue };
                let eigen = (item.span.von as usize) >= e.ab;
                if (rumpfrunde && rumpf) || (!rumpfrunde && eigen) {
                    definiert.entry(k).or_insert_with(|| Eigner {
                        einheit: i,
                        von: item.span.von,
                        rumpf,
                        text: schnitt(e.quelle, item.span).trim_start_matches("pub ").to_string(),
                    });
                }
            }
        }
    }
    let mut gesehen: BTreeMap<String, String> = BTreeMap::new();
    let mut module_gesehen: BTreeSet<String> = BTreeSet::new();
    let mut konflikte = Vec::new();
    let mut text = String::new();
    let mut ab = Vec::new();
    for (i, e) in es.iter().enumerate() {
        let mut t = e.quelle.as_bytes().to_vec();
        verbund_geh(
            i,
            e,
            &e.baum.items,
            "",
            &definiert,
            &mut gesehen,
            &mut module_gesehen,
            &mut t,
            &mut konflikte,
        );
        ab.push(text.len());
        // Blanking replaces whole items by ASCII spaces, so the bytes stay UTF-8.
        text.push_str(&String::from_utf8_lossy(&t));
        text.push('\n');
    }
    Verbundtext { text, ab, konflikte }
}

/// **The whole-program check of the linked program** (Opus F, closing review E F1 and the
/// two-sided residue of OFFEN O28). The composed source is read and checked by EVERY pass, as
/// one unit; each error lands, with its own code, in the unit whose text it points into.
///
/// Correspondence with the Lean link check: `SchnittstelleSpec` re-decides thread-locality
/// (`lok`), write separation (`renn`) and pool safety (`einzeln`) over the COMPOSED hulls
/// `HuelleV`, i.e. over the call graphs of `verbinde e E₁ E₂` (with `KeinRueckruf`, `N503`
/// here, a root's linked graph IS its composed hull -- `huelle_of_reach`). This function runs
/// the Rust deciders of exactly those components (`N290`-`N304`, `N456`/`N457`/`N462` in
/// `fusswache2.rs`) over that linked program -- every start of both units, every footprint
/// read from the owner's body -- and every other whole-program pass beside them. It
/// therefore refuses at least what `schnittstelleB` refuses (the Rust twin of `vm_abgelehnt`
/// falls with the one-file codes `N291`/`N301`), and possibly more: a whole-program refusal
/// of another pass is a finding about the linked program, reported, not filtered. Returns the
/// number of errors pushed.
pub fn pruefe_verbund(es: &[Einheit], absagen: &mut [Absagen]) -> usize {
    let vt = verbundtext(es);
    let mut n = 0;
    if !vt.konflikte.is_empty() {
        for (i, sp, m) in &vt.konflikte {
            absagen[*i].schiebe(
                Absage::fehler(
                    "N516",
                    *sp,
                    format!(
                        "module `{m}` holds items in two units: the linked program cannot be \
                         composed, so its whole-program check did not run"
                    ),
                )
                .mit_notiz(
                    "a module belongs to ONE unit (`gabbro build` refuses the same); the other \
                     unit reaches it through `use` and the heads `gabbro abi` writes",
                ),
            );
            n += 1;
        }
        return n;
    }
    let (baum, mut gesamt) = gabbro_syntax::lies("<linked>", &vt.text);
    crate::pruefe(&baum, &mut gesamt);
    let namen = es.iter().map(|e| e.name).collect::<Vec<_>>().join(" + ");
    for a in gesamt.absagen {
        if a.stufe != gabbro_syntax::Stufe::Fehler {
            continue;
        }
        let von = a.span.von as usize;
        let i = vt.ab.iter().rposition(|&x| x <= von).unwrap_or(0);
        let d = vt.ab[i] as u32;
        let mut b = a;
        b.span = Span::neu(b.span.von.saturating_sub(d), b.span.bis.saturating_sub(d));
        b.fix = None;
        b.notizen.push(format!(
            "found on the LINKED program ({namen} composed as one unit, each body from its \
             owner): each unit alone is clean, so this refusal is the link's -- the \
             whole-program components the Lean link check re-decides over the composed hulls \
             (`SchnittstelleSpec.lok`/`.renn`/`.einzeln`)"
        ));
        absagen[i].schiebe(b);
        n += 1;
    }
    n
}

/// **The link of N units**: every pair's heads held against the bodies (`verbinde`), then --
/// only if no head is stale, so the composition means what the units were checked against --
/// the whole-program check of the linked program (`pruefe_verbund`). `absagen[i]` belongs to
/// `es[i]`.
pub fn verbinde_alle(es: &[Einheit], absagen: &mut [Absagen]) -> Bericht {
    let mut bericht = Bericht::default();
    for i in 0..es.len() {
        for j in (i + 1)..es.len() {
            let (links, rechts) = absagen.split_at_mut(j);
            let b = verbinde(&es[i], &es[j], &mut links[i], &mut rechts[0]);
            bericht.importe += b.importe;
            bericht.geteilte_deklarationen += b.geteilte_deklarationen;
            bericht.geteilte_annahmen += b.geteilte_annahmen;
        }
    }
    if absagen.iter().all(|a| a.fehler_zahl() == 0) {
        bericht.verbund_geprueft = true;
        bericht.verbund_fehler = pruefe_verbund(es, absagen);
    }
    bericht
}

#[cfg(test)]
mod tests {
    //! Snippet probes of the refusals the probe files under `messung/proben/verbund/` do not
    //! reach (those are driven by `crates/gabbro-cli/tests/verbund.rs`).
    use super::*;

    /// The error codes of one snippet unit checked ALONE.
    fn allein(q: &str) -> Vec<&'static str> {
        let (baum, mut abs) = gabbro_syntax::lies("u.gab", q);
        crate::pruefe(&baum, &mut abs);
        abs.absagen
            .iter()
            .filter(|a| a.stufe == gabbro_syntax::Stufe::Fehler)
            .map(|a| a.code)
            .collect()
    }

    /// Links two snippet units the way `gabbro link` does -- each must be clean ALONE (a unit
    /// with errors links nothing), then the heads, then the linked program -- and returns
    /// every code, in unit order (A's, then B's).
    fn links(a: &str, b: &str) -> Vec<&'static str> {
        assert_eq!(allein(a), Vec::<&str>::new(), "unit A is clean alone:\n{a}");
        assert_eq!(allein(b), Vec::<&str>::new(), "unit B is clean alone:\n{b}");
        let (ba, _) = gabbro_syntax::lies("a.gab", a);
        let (bb, _) = gabbro_syntax::lies("b.gab", b);
        let es = [
            Einheit { name: "a.gab", baum: &ba, quelle: a, ab: 0 },
            Einheit { name: "b.gab", baum: &bb, quelle: b, ab: 0 },
        ];
        let mut abs = [Absagen::neu("a.gab"), Absagen::neu("b.gab")];
        verbinde_alle(&es, &mut abs);
        abs.iter().flat_map(|x| x.absagen.iter()).map(|x| x.code).collect()
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
    fn faeden_auf_beiden_seiten_werden_beurteilt_nicht_pauschal_abgelehnt() {
        // Opus F (OFFEN O28): threads in BOTH units are judged over the linked program. Two
        // pools that share nothing link clean -- before, this pair fell with a blanket N503.
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
        assert_eq!(links(bib, app), Vec::<&str>::new());
        // Threads in ONE unit only: silent.
        assert_eq!(links(BIB, app), Vec::<&str>::new());
    }

    /// The library's thread writes the unguarded table, the app's thread reads it through
    /// the imported head: each unit is clean alone (one start per unit, and neither unit
    /// sees the other's thread) -- the linked program has the write-read race.
    const RENN_BIB: &str = "module bib {
pub type Stand = u32 in 0 .. 100;
pub table konto count 2 { slot { stand : Stand, } }
pub impl fn lies() -> Stand effects { reads konto.slots } costs <= 16 ops { return konto.slots[0].stand; }
impl fn schreiber() effects { writes konto.slots } costs <= 16 ops { konto.slots[0].stand = 1; return; }
impl fn ruhig() effects { pure } costs <= 4 ops { return; }
concurrent { schreiber, ruhig };
}
";
    const RENN_APP: &str = "module bib {
pub type Stand = u32 in 0 .. 100;
pub table konto count 2 { slot { stand : Stand, } }
pub extern fn lies() -> Stand effects { reads konto.slots } costs <= 16 ops;
}
module app {
use bib::lies;
use bib::konto;
impl fn leser() effects { reads konto.slots } costs <= 64 ops { let x = lies(); return; }
impl fn still() effects { pure } costs <= 4 ops { return; }
concurrent { leser, still };
}
";

    #[test]
    fn ein_rennen_ueber_beide_einheiten_faellt_am_verbund() {
        // The codes are the race pass's (`N29x`/`N30x`, the one-file codes -- exactly which
        // is pinned by probe 1247 in `crates/gabbro-cli/tests/verbund.rs`; this file names no
        // code it does not issue, `pruefe-kennungen.py`).
        let codes = links(RENN_BIB, RENN_APP);
        assert!(!codes.is_empty(), "the cross-unit write-read race falls on the linked program");
        assert!(
            codes.iter().all(|c| c.starts_with("N29") || c.starts_with("N30")),
            "judged by the race pass, not blanket-refused: {codes:?}"
        );
    }

    #[test]
    fn der_verbundtext_behaelt_jeden_rumpf_und_jeden_start() {
        let (ba, _) = gabbro_syntax::lies("a.gab", RENN_BIB);
        let (bb, _) = gabbro_syntax::lies("b.gab", RENN_APP);
        let es = [
            Einheit { name: "a.gab", baum: &ba, quelle: RENN_BIB, ab: 0 },
            Einheit { name: "b.gab", baum: &bb, quelle: RENN_APP, ab: 0 },
        ];
        let vt = verbundtext(&es);
        assert!(vt.konflikte.is_empty());
        assert_eq!(vt.text.matches("concurrent {").count(), 2, "both units' starts stay");
        assert_eq!(vt.text.matches("fn lies").count(), 1, "the head is dropped, the body stays");
        assert!(!vt.text.contains("extern fn lies"));
        assert_eq!(vt.text.matches("table konto").count(), 1, "one declaration");
        assert_eq!(vt.ab, vec![0, RENN_BIB.len() + 1], "byte positions are kept");
    }

    #[test]
    fn ein_modul_in_zwei_einheiten_faellt_mit_n516() {
        let a = "module m {
pub impl fn f() effects { pure } costs <= 8 ops { return; }
}
";
        let b = "module m {
pub impl fn g() effects { pure } costs <= 8 ops { return; }
}
";
        assert_eq!(links(a, b), vec!["N516"]);
    }

    #[test]
    fn vertraege_werden_als_baum_verglichen() {
        // OFFEN O28 "contracts as text": the head spells the exporter's contract with other
        // parentheses, another conjunct split and other line breaks -- the same tree, so no
        // N502. A different tree still falls.
        let bib = "module bib {
pub impl fn f(x : u32 in 0 .. 10) -> u32 in 0 .. 20 requires x < 5 && x > 0 ensures result == x + 1 effects { pure } costs <= 8 ops { return x + 1; }
}
";
        let app = "module bib {
pub extern fn f(x : u32 in 0 .. 10) -> u32 in 0 .. 20
    requires (x > 0), (x < 5)
    ensures result == (x + 1)
    effects { pure } costs <= 8 ops;
}
";
        assert_eq!(links(bib, app), Vec::<&str>::new());
        let falsch = app.replace("(x + 1)", "(x + 2)");
        assert_eq!(links(bib, &falsch), vec!["N502"]);
        // Parentheses that change the tree are not dropped: (a + b) * c is not a + b * c.
        assert_ne!(
            normalform(&gabbro_syntax::lies("p.gab", "const K : u32 = (1 + 2) * 3;").0.items[0].art),
            normalform(&gabbro_syntax::lies("p.gab", "const K : u32 = 1 + 2 * 3;").0.items[0].art)
        );
        assert_eq!(
            normalform(&gabbro_syntax::lies("p.gab", "const K : u32 = (1 + 2);").0.items[0].art),
            normalform(&gabbro_syntax::lies("p.gab", "const  K : u32 =  1 + 2 ;").0.items[0].art)
        );
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
