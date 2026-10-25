//! **Name spaces of a unit made of several projects** -- the rule of the Lean model
//! (`grammatik/Grammatik/Parser/Namen/Namensraum.lean`, `SYNTAX.md` at `usedecl`), carried out on
//! the tokens of each file before the unit reaches the checker.
//!
//! A name of the unit is (copy, path): every project's top-level modules are placed below its
//! name space (`module stock` of the copy `store` becomes `module store::stock`), a path whose
//! first segment is the LOCAL name of a declared dependency goes into that dependency's name space,
//! and every other path stays as it was written (relative to the project root, or to the enclosing
//! modules). So two projects with `module util` share no name, and the checker's resolution is the
//! one of a single project.
//!
//! **Visibility** is then a matter of path heads: after the rewrite every path into another copy
//! starts with that copy's name space, so a head naming a copy the file's project did not declare,
//! or a module of a dependency it does not export, is refused (`pruefe_sicht`). Nothing of an
//! undeclared project and no private library of a dependency is reachable.

use std::collections::{BTreeMap, BTreeSet};

use gabbro_syntax::kw::Kw;
use gabbro_syntax::lex::{zerlege, Art, Token, Z};

fn ist_name(t: &Token) -> bool {
    matches!(t.art, Art::Ident | Art::Wort(_))
}

fn ist(t: Option<&Token>, z: Z) -> bool {
    matches!(t.map(|t| t.art), Some(Art::Zeichen(x)) if x == z)
}

/// The heads of every path of the file: a name followed by `::` and not preceded by `::`.
fn koepfe(toks: &[Token]) -> Vec<usize> {
    let mut aus = Vec::new();
    for i in 0..toks.len() {
        if ist_name(&toks[i]) && ist(toks.get(i + 1), Z::Kolon2) && !(i > 0 && ist(toks.get(i - 1), Z::Kolon2)) {
            aus.push(i);
        }
    }
    aus
}

/// **Rewrites one file of the copy `ns`.** `eigene` are the copy's top-level modules in the unit,
/// `deps` maps the copy's local dependency names to their name spaces.
pub fn umschreibe(
    datei: &str,
    text: &str,
    ns: &str,
    eigene: &BTreeSet<String>,
    deps: &BTreeMap<String, String>,
) -> Result<String, String> {
    let mut absagen = gabbro_syntax::Absagen::neu(datei);
    let toks = zerlege(text, &mut absagen);
    let zeile = |t: &Token| text[..t.span.von as usize].matches('\n').count() + 1;
    // (start, end, replacement)
    let mut ersatz: Vec<(usize, usize, String)> = Vec::new();
    let mut tiefe: i64 = 0;
    let mut i = 0;
    while i < toks.len() {
        let t = &toks[i];
        match t.art {
            Art::Zeichen(Z::GeschweiftAuf) => tiefe += 1,
            Art::Zeichen(Z::GeschweiftZu) => tiefe -= 1,
            Art::Ende => {}
            _ if tiefe == 0 => {
                // At the top of a file of a unit with name spaces, only modules stand.
                let mut j = i;
                if matches!(toks[j].art, Art::Wort(Kw::Pub)) {
                    j += 1;
                }
                if !matches!(toks.get(j).map(|t| t.art), Some(Art::Wort(Kw::Module))) {
                    return Err(format!(
                        "{datei}:{}: `{}` stands outside a module -- in a program made of several projects every \
                         item stands in a `module`, or it would share the root of the program",
                        zeile(t),
                        t.text(text)
                    ));
                }
                let Some(kopf) = toks.get(j + 1).filter(|k| ist_name(k)) else {
                    return Err(format!("{datei}:{}: `module` without a name", zeile(t)));
                };
                let name = kopf.text(text);
                if deps.contains_key(name) {
                    return Err(format!(
                        "{datei}:{}: module `{name}` has the name of a dependency of this project -- a path \
                         `{name}::…` would mean both",
                        zeile(kopf)
                    ));
                }
                ersatz.push((kopf.span.von as usize, kopf.span.von as usize, format!("{ns}::")));
                // Skip to the module's `{`.
                i = j + 2;
                while i < toks.len() && !matches!(toks[i].art, Art::Zeichen(Z::GeschweiftAuf)) {
                    i += 1;
                }
                continue;
            }
            _ => {}
        }
        i += 1;
    }
    for k in koepfe(&toks) {
        let t = &toks[k];
        // The head of a top-level module declaration is placed already.
        if k > 0 && matches!(toks[k - 1].art, Art::Wort(Kw::Module)) && ersatz.iter().any(|e| e.0 == t.span.von as usize) {
            continue;
        }
        let name = t.text(text);
        if let Some(d) = deps.get(name) {
            ersatz.push((t.span.von as usize, t.span.bis as usize, d.clone()));
        } else if eigene.contains(name) {
            ersatz.push((t.span.von as usize, t.span.von as usize, format!("{ns}::")));
        }
    }
    ersatz.sort_by_key(|e| (e.0, e.1));
    let mut aus = String::with_capacity(text.len() + ersatz.len() * (ns.len() + 2));
    let mut pos = 0;
    for (von, bis, neu) in ersatz {
        aus.push_str(&text[pos..von]);
        aus.push_str(&neu);
        pos = bis;
    }
    aus.push_str(&text[pos..]);
    Ok(aus)
}

/// **What a file of the copy `ns` may reach**, after the rewrite: its own name space, and of each
/// declared dependency the modules it exports.
pub fn pruefe_sicht(
    datei: &str,
    text: &str,
    ns: &str,
    alle: &BTreeMap<String, String>,
    sicht: &BTreeMap<String, BTreeSet<String>>,
) -> Result<(), String> {
    let mut absagen = gabbro_syntax::Absagen::neu(datei);
    let toks = zerlege(text, &mut absagen);
    let zeile = |t: &Token| text[..t.span.von as usize].matches('\n').count() + 1;
    for k in koepfe(&toks) {
        let t = &toks[k];
        let name = t.text(text);
        if name == ns {
            continue;
        }
        let Some(projekt) = alle.get(name) else { continue };
        let Some(export) = sicht.get(name) else {
            return Err(format!(
                "{datei}:{}: the path reaches project `{projekt}`, which this file's project does not declare -- \
                 add `{projekt} = dependency('{projekt}', …)` and name it in the target's `dependencies:`",
                zeile(t)
            ));
        };
        let modul = toks.get(k + 2).filter(|m| ist_name(m)).map(|m| m.text(text)).unwrap_or("");
        if !export.contains(modul) {
            return Err(format!(
                "{datei}:{}: `{projekt}::{modul}` -- project `{projekt}` exports no module `{modul}` (its \
                 exported libraries are marked `export: true`)",
                zeile(t)
            ));
        }
    }
    Ok(())
}
