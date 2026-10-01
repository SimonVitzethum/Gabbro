//! **`N575`-`N577` -- code handed in by GENERATED C, never formed in Gabbro** (C-free lane, C2
//! slice 3, 2026-10-01; OFFEN O39).
//!
//! A kernel starts a thread by running a function it is HANDED (`kthread_create_on_node(threadfn,
//! …)`); `N574` refuses every function pointer at a foreign body, because a Gabbro function handed
//! out leaves every effect and concurrency rule behind. The hosted twin of the problem was closed
//! by a checked form (the `child` region, `N572`) and a proved trampoline whose code addresses
//! are C DESIGNATORS written by the generator. This file is the same answer for a foreign body
//! that takes code as an ARGUMENT: the type `entry fn(…) -> R`.
//!
//! * Its values come from generated C only. No Gabbro expression has this type: it cannot be
//!   written as a literal, `&f` gives an ordinary `fn(…)`, and a function that takes one is
//!   named by no Gabbro source at all (`N576`) -- its callers are the generated drivers, which
//!   hand the designator of a wrapper they wrote around a DECLARED root (template `faden.modul`).
//! * Inside such a function the parameter goes ONE way: as the argument of one `extern fn`
//!   whose parameter at that position has the same signature, once, outside every loop
//!   (`N577`). So one driver call hands one root to one foreign start, and no Gabbro body
//!   calls through it, stores it, compares it or hands it twice.
//! * It stands only where that reading is complete (`N575`): as the own type of a parameter
//!   of an `extern fn` or of a Gabbro function with a body, carrying a C signature of
//!   integers and pointers and no contract -- a contract would be read by nobody, since no
//!   Gabbro code ever calls through it.
//!
//! | code | rule | where |
//! |---|---|---|
//! | `N575` | an `entry fn(…)` type stands only as the own type of a parameter of an `extern fn` or a Gabbro function with a body (not behind `...`), with integer, `bool` and `ptr<normal, …>` integer parameters and result, and no contract | `eintritt_ort` |
//! | `N576` | a Gabbro function with an `entry fn` parameter is called, taken (`&f`) or dispatched to by no Gabbro source | `eintritt_ohne_rufer` |
//! | `N577` | an `entry fn` parameter is mentioned once in its body: as the whole argument of a call of an `extern fn` whose parameter at that position has the same signature, outside every loop; and every argument at such a position is such a parameter | `eintritt_weitergabe` |
//!
//! **What this does NOT claim.** That the foreign start runs the code once, on a new thread, and
//! never after the driver's join returned -- that is the binding's declared contract, user
//! logic, premise (c). That the root the driver wraps is a declared `concurrent` root is the
//! driver's (`faden.modul`, `bau.rs::treiberregel`).

use std::collections::BTreeMap;

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};

/// The `entry fn` at a type, if it is one.
pub fn eintrittstyp(t: &TypExpr) -> Option<&FnZeiger> {
    match t {
        TypExpr::FnZeiger(z) if z.eintritt.is_some() => Some(z),
        _ => None,
    }
}

/// **The C signature of an `entry fn`, as one comparable text** -- or why it has none.
///
/// Integers without a range, `bool`, and `ptr<normal, r|w|rw>` at an integer: the shapes whose
/// C type is fixed by the word alone, so two equal texts are two equal C types. A range, a
/// record or a named type would make the comparison a question about the unit.
pub fn signatur(z: &FnZeiger) -> Result<String, String> {
    fn wort(t: &TypExpr) -> Result<String, String> {
        match t {
            TypExpr::Int(i) if i.bereich.is_none() && i.zucker.is_none() => {
                Ok(format!("{:?}", i.wort).to_lowercase())
            }
            TypExpr::Bool(_) => Ok("bool".into()),
            TypExpr::Zeiger(p) => {
                if !matches!(p.raum, Raum::Normal) {
                    return Err("a pointer outside the `normal` space".into());
                }
                let mut r = String::new();
                for x in &p.rechte {
                    r.push_str(match x {
                        Recht::Lesen => "r",
                        Recht::Schreiben => "w",
                        Recht::LesenSchreiben => "rw",
                        Recht::Ausfuehren | Recht::Eigen(_) => {
                            return Err("a pointer right other than `r`, `w`, `rw`".into())
                        }
                    });
                }
                match &p.ziel {
                    TypExpr::Int(i) if i.bereich.is_none() && i.zucker.is_none() => {
                        Ok(format!("ptr<normal, {r}> {}", format!("{:?}", i.wort).to_lowercase()))
                    }
                    _ => Err("a pointer at something other than a plain integer".into()),
                }
            }
            _ => Err("a type other than a plain integer, `bool` or a pointer at one".into()),
        }
    }
    let mut teile = Vec::new();
    for p in &z.parameter {
        teile.push(wort(&p.typ)?);
    }
    let erg = match &z.ergebnis {
        Some(e) => wort(e)?,
        None => "void".into(),
    };
    Ok(format!("entry fn({}) -> {erg}", teile.join(", ")))
}

fn schluessel(modul: &str, name: &str) -> String {
    if modul.is_empty() {
        name.to_string()
    } else {
        format!("{modul}::{name}")
    }
}

/// Every function that takes an `entry fn`: its key, its declaration, and per parameter the
/// signature text (`None` where the parameter is no `entry fn`).
struct Traeger {
    decl: FnDecl,
    sig: Vec<Option<String>>,
}

fn ist_gabbro_rumpf(f: &FnDecl) -> bool {
    matches!(f.rumpf, FnRumpf::Block(_))
        && matches!(f.klasse, None | Some(FnKlasse::Impl))
        && !f.bibliothek
        && f.translator_fuer.is_none()
}

pub fn pass(baum: &Programm, absagen: &mut Absagen) {
    let u = crate::umgebung::Umgebung::sammle(baum);
    let mut traeger: BTreeMap<String, Traeger> = BTreeMap::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        eintritt_ort(item, absagen);
        if let ItemArt::Funktion(f) = &item.art {
            if f.parameter.iter().any(|p| eintrittstyp(&p.typ).is_some()) {
                let sig = f
                    .parameter
                    .iter()
                    .map(|p| eintrittstyp(&p.typ).and_then(|z| signatur(z).ok()))
                    .collect();
                traeger.insert(schluessel(modul, &f.name.text), Traeger { decl: f.clone(), sig });
            }
        }
    });
    if traeger.is_empty() {
        return;
    }
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        eintritt_ohne_rufer(item, modul, &u, &traeger, absagen);
        if let ItemArt::Funktion(f) = &item.art {
            eintritt_weitergabe(f, modul, &u, &traeger, absagen);
        }
    });
}

fn aufloesen<'a>(
    u: &crate::umgebung::Umgebung,
    traeger: &'a BTreeMap<String, Traeger>,
    von: &str,
    pfad: &Pfad,
) -> Option<(&'a String, &'a Traeger)> {
    u.kandidaten_aufloesbar(von, &pfad.text())
        .into_iter()
        .find_map(|k| traeger.get_key_value(&k))
}

/// **`N575`** -- where an `entry fn` type may stand, and what it may say.
///
/// The legal places are counted from the declaration; every `entry fn` anywhere in the item
/// is counted from the item's whole tree (the derived `Debug` of the item names the marker
/// once per type, wherever the type stands -- a `let`, a field, a result, a pointer, a
/// function pointer's parameter). More of them than legal places is a refusal at the item:
/// *a count that does not need to know every position cannot forget one.*
fn eintritt_ort(item: &Item, absagen: &mut Absagen) {
    // A module is walked item by item; its own `Debug` would count its members' types.
    if matches!(item.art, ItemArt::Modul(_)) {
        return;
    }
    let gesamt = format!("{item:?}").matches("eintritt: Some(").count();
    if gesamt == 0 {
        return;
    }
    let mut legal = 0;
    if let ItemArt::Funktion(f) = &item.art {
        let ort_ok = f.klasse == Some(FnKlasse::Extern) || ist_gabbro_rumpf(f);
        for (i, p) in f.parameter.iter().enumerate() {
            let Some(z) = eintrittstyp(&p.typ) else { continue };
            legal += 1;
            let hinter_dem_rest = f.variadisch_ab.is_some_and(|v| i >= v);
            let grund = if !ort_ok {
                Some("only an `extern fn` or a Gabbro function with a body takes one".to_string())
            } else if hinter_dem_rest {
                Some("behind `...` its C type would be promoted, not passed".to_string())
            } else if !z.requires.is_empty()
                || !z.ensures.is_empty()
                || z.effects.is_some()
                || z.costs.is_some()
            {
                Some(
                    "it carries a contract -- no Gabbro code calls through an `entry fn`, so \
                     nobody would read it"
                        .to_string(),
                )
            } else {
                signatur(z).err()
            };
            if let Some(g) = grund {
                absagen.schiebe(
                    Absage::fehler(
                        "N575",
                        p.name.span,
                        format!(
                            "the parameter `{}` of `{}` is an `entry fn`, and {g}",
                            p.name.text, f.name.text
                        ),
                    )
                    .mit_notiz(
                        "an `entry fn` is code a generated driver hands in; it stands only as a \
                         parameter of an `extern fn` or of a Gabbro function, with a signature of \
                         integers, `bool` and pointers at integers, and no contract",
                    ),
                );
            }
        }
    }
    if gesamt > legal {
        let span = item.art.name().map(|n| n.span).unwrap_or(item.span);
        let name = item.art.name().map(|n| n.text.clone()).unwrap_or_default();
        absagen.schiebe(
            Absage::fehler(
                "N575",
                span,
                format!(
                    "`{name}` carries an `entry fn` type that is not the own type of a parameter \
                     -- {} in the item, {legal} of them parameters",
                    gesamt
                ),
            )
            .mit_notiz(
                "a value of this type exists only as a parameter a generated driver filled; \
                 stored, returned, bound by `let`, put behind a pointer or into another type it \
                 would be code that Gabbro source holds",
            ),
        );
    }
}

/// Every call (`Ruf`) and every `&f` in a block, with whether it stands inside a loop.
fn rufe_im_block<'a>(
    b: &'a Block,
    in_schleife: bool,
    rufe: &mut Vec<(&'a Ruf, bool)>,
    werte: &mut Vec<&'a Pfad>,
) {
    for s in &b.anweisungen {
        let schleife = in_schleife || matches!(s.art, StmtArt::Schleife(_));
        let mut ausdruecke: Vec<&Expr> = crate::eigene_ausdruecke(s);
        for p in crate::eigene_praedikate(s) {
            ausdruecke.extend(crate::ausdruecke_im_praedikat(p));
        }
        let mut direkte: Vec<&Ruf> = Vec::new();
        match &s.art {
            StmtArt::Ruf(r) => direkte.push(r),
            StmtArt::LetSonst(l) => {
                if let Some(r) = l.als_ruf() {
                    direkte.push(r);
                }
            }
            _ => {}
        }
        for r in direkte {
            rufe.push((r, schleife));
            ausdruecke.extend(r.argumente.iter());
        }
        for e in ausdruecke {
            for x in crate::alle_ausdruecke(e) {
                match &x.art {
                    ExprArt::Ruf(r) => rufe.push((r, schleife)),
                    ExprArt::FnWert(p) => werte.push(p),
                    _ => {}
                }
            }
        }
        for unter in crate::unterbloecke(s) {
            rufe_im_block(unter, schleife, rufe, werte);
        }
    }
}

/// **`N576`** -- a function that takes an `entry fn` has no Gabbro caller.
fn eintritt_ohne_rufer(
    item: &Item,
    modul: &str,
    u: &crate::umgebung::Umgebung,
    traeger: &BTreeMap<String, Traeger>,
    absagen: &mut Absagen,
) {
    let mut genannt: Vec<(&Pfad, &str)> = Vec::new();
    let mut rufe = Vec::new();
    let mut werte = Vec::new();
    match &item.art {
        ItemArt::Funktion(f) => {
            if let FnRumpf::Block(b) = &f.rumpf {
                rufe_im_block(b, false, &mut rufe, &mut werte);
            }
        }
        ItemArt::Entry(e) => genannt.push((&e.dispatch, "dispatches to")),
        ItemArt::Boot(b) => genannt.push((&b.dispatch, "dispatches to")),
        ItemArt::Concurrent(c) => {
            for k in &c.koerper {
                genannt.push((k, "names as a concurrent body"));
            }
        }
        _ => {}
    }
    for p in crate::praedikate_im_item(item) {
        for e in crate::ausdruecke_im_praedikat(p) {
            for x in crate::alle_ausdruecke(e) {
                match &x.art {
                    ExprArt::Ruf(r) => rufe.push((r, false)),
                    ExprArt::FnWert(p) => werte.push(p),
                    _ => {}
                }
            }
        }
    }
    for (r, _) in &rufe {
        if let CallTarget::Path(p) = &r.ziel {
            genannt.push((p, "calls"));
        }
    }
    for p in werte {
        genannt.push((p, "takes the address of"));
    }
    for (p, wie) in genannt {
        let Some((k, t)) = aufloesen(u, traeger, modul, p) else { continue };
        if !ist_gabbro_rumpf(&t.decl) {
            continue;
        }
        absagen.schiebe(
            Absage::fehler(
                "N576",
                p.span,
                format!(
                    "this {wie} `{k}`, which takes an `entry fn` -- a function that takes code \
                     is named by no Gabbro source"
                ),
            )
            .mit_notiz(
                "its caller is a generated driver that hands the designator of a wrapper it wrote \
                 around a declared root; a Gabbro caller would have to form code, and Gabbro \
                 cannot",
            ),
        );
    }
}

/// **`N577`** -- an `entry fn` parameter goes one way: once, whole, to a foreign body's
/// `entry fn` parameter of the same signature, outside every loop.
fn eintritt_weitergabe(
    f: &FnDecl,
    modul: &str,
    u: &crate::umgebung::Umgebung,
    traeger: &BTreeMap<String, Traeger>,
    absagen: &mut Absagen,
) {
    let FnRumpf::Block(b) = &f.rumpf else { return };
    let eigene: BTreeMap<&str, Option<String>> = f
        .parameter
        .iter()
        .filter_map(|p| {
            eintrittstyp(&p.typ).map(|z| (p.name.text.as_str(), signatur(z).ok()))
        })
        .collect();
    let mut rufe = Vec::new();
    let mut werte = Vec::new();
    rufe_im_block(b, false, &mut rufe, &mut werte);
    // Per own parameter: the legal hand-overs found.
    let mut weiter: BTreeMap<&str, usize> = BTreeMap::new();
    for (r, schleife) in &rufe {
        let CallTarget::Path(pfad) = &r.ziel else { continue };
        let Some((k, t)) = aufloesen(u, traeger, modul, pfad) else { continue };
        if t.decl.klasse != Some(FnKlasse::Extern) {
            continue; // a Gabbro callee is `N576`'s
        }
        for (i, sig) in t.sig.iter().enumerate() {
            if eintrittstyp(&t.decl.parameter[i].typ).is_none() {
                continue;
            }
            let arg = r.argumente.get(i).map(crate::ohne_klammern);
            let name = arg.and_then(|a| match &a.art {
                ExprArt::Ort(o) if o.suffixe.is_empty() => Some(o.basis.text.as_str()),
                _ => None,
            });
            let passt = match name.and_then(|n| eigene.get_key_value(n)) {
                Some((n, eigen)) if eigen.is_some() && eigen == sig => {
                    *weiter.entry(n).or_insert(0) += 1;
                    if *schleife {
                        Err(format!("`{n}` is handed on inside a loop"))
                    } else {
                        Ok(())
                    }
                }
                Some((n, _)) => Err(format!(
                    "`{n}`'s signature is not the one `{k}` takes at this position"
                )),
                None => Err(format!(
                    "the argument at `{k}`'s `entry fn` position {} is not an `entry fn` parameter \
                     of `{}`",
                    i + 1,
                    f.name.text
                )),
            };
            if let Err(g) = passt {
                let span = arg.map(|a| a.span).unwrap_or(pfad.span);
                absagen.schiebe(
                    Absage::fehler("N577", span, format!("{g} -- an `entry fn` goes one way, once"))
                        .mit_notiz(
                            "code a generated driver handed in is passed whole, once, to a foreign \
                             body's `entry fn` parameter of the same signature, outside every \
                             loop; so one driver call hands one root to one foreign start",
                        ),
                );
            }
        }
    }
    // Every mention of an own `entry fn` parameter, anywhere in the body and the contract,
    // counted from the derived `Debug` of the declaration (an `Ident` prints its text as
    // `text: "<name>"`). The parameter list names it once; every mention beyond that and
    // beyond the legal hand-overs is a use this rule does not admit -- a call through it, a
    // store, a comparison, a second hand-over. Fail-closed: a name shared with a field or a
    // callee counts too.
    let ganz = format!("{f:?}");
    for (n, sig) in &eigene {
        if sig.is_none() {
            continue; // `N575` refused the signature already
        }
        let erwaehnt = ganz.matches(&format!("text: \"{n}\"")).count();
        let legal = 1 + weiter.get(n).copied().unwrap_or(0).min(1);
        let gezaehlt = weiter.get(n).copied().unwrap_or(0);
        if erwaehnt > legal || gezaehlt > 1 {
            let span = f
                .parameter
                .iter()
                .find(|p| p.name.text == *n)
                .map(|p| p.name.span)
                .unwrap_or(f.name.span);
            absagen.schiebe(
                Absage::fehler(
                    "N577",
                    span,
                    format!(
                        "`{n}` is named {} time(s) in `{}` beyond its declaration, and the one \
                         use an `entry fn` has is a single hand-over to a foreign body",
                        erwaehnt - 1,
                        f.name.text
                    ),
                )
                .mit_notiz(
                    "no Gabbro body calls through, stores, compares or hands twice the code a \
                     generated driver handed in; every mention but one hand-over is refused, and \
                     a field or callee of the same name counts as a mention",
                ),
            );
        }
    }
}
