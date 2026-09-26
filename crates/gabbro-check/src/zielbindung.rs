//! **System calls as named variables, bound per target** (OFFEN O31, Opus agent L) -- and
//! the entry's register binding against its dispatch (OFFEN O32 residue (7)).
//!
//! The parser fills every `via V` gate from the ACTIVE target's binding
//! (`gabbro_syntax::ziel`); every other pass then reads an ordinary gate. What this pass holds
//! is everything the fill cannot say by itself:
//!
//! | code | rule | probe |
//! |---|---|---|
//! | `N561` | an `entry`'s `regs in` are its dispatch's parameters, one register each, and its `regs out` its result (at most one register, and only if the dispatch answers a value -- an answer with no out register is dropped; no `or R` channel) | gift 1351 |
//! | `N562` | a gate's `via V` names a declared `syscall V;`, and no other gate uses `V` | gift 1352, 1353 |
//! | `N563` | EVERY target binds every variable a gate uses (switching targets never meets an unbound gate) | gift 1354 |
//! | `N564` | a binding names a declared variable, once per target | gift 1355, 1356 |
//! | `N565` | the active target is determined: one selection or one block name, a selection or `GABBRO_TARGET` names a block, one name is one ABI | gift 1357, 1358 |
//! | `N566` | two targets never bind one variable under ONE named assumption: a different kernel is a different assumption, never silently the same | gift 1359 |
//! | `N567` | a unit with `target` blocks writes no literal gate (`abi … number …` at the gate): every gate follows the binding | gift 1360 |
//!
//! Inactive targets are held to the gate's shape too: every binding of every non-active
//! target is filled into a copy of its gate and run through the same `syscall.rs` rules
//! (`N063`-`N068`, `A006`) and the named-assumption rule (`N004`/`N005`), each refusal
//! noted with the target it came from. **Not checked for an inactive target:** the
//! emitter's template rules (`C180`-`C184`) -- they run where the target is emitted.
//! The link rule (`N568`: two linked units bind the same target) is `verbund.rs`'s.

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};
use gabbro_syntax::span::Span;
use gabbro_syntax::ziel::{gebunden, zielbild, Zielbild};
use std::collections::BTreeMap;

pub fn pass(baum: &Programm, absagen: &mut Absagen) {
    eintritte(baum, absagen);
    let bild = zielbild(baum);
    // The unit's variables and gates.
    let mut vars: BTreeMap<String, Span> = BTreeMap::new();
    let mut tore: Vec<(SyscallDecl, String)> = Vec::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| match &item.art {
        ItemArt::SysVar(v) => {
            vars.entry(v.name.text.clone()).or_insert(v.name.span);
        }
        ItemArt::Syscall(s) => tore.push((s.clone(), modul.to_string())),
        _ => {}
    });
    let hat_ziele = !bild.bloecke.is_empty();
    wahl(&bild, absagen);
    // **N567 -- no literal gate beside a target.**
    if hat_ziele {
        for (s, _) in tore.iter().filter(|(s, _)| s.via.is_none()) {
            absagen.schiebe(
                Absage::fehler(
                    "N567",
                    s.abi.span,
                    format!(
                        "`syscall {}` writes its ABI at the gate (`abi {} … number …`) in a unit \
                         that binds system calls per target",
                        s.name.text, s.abi.text
                    ),
                )
                .mit_notiz(
                    "a literal gate keeps ONE kernel whatever target is active -- the target \
                     would change every other gate and silently not this one; declare \
                     `syscall V;`, write `via V` here and bind `V` in every `target` block",
                ),
            );
        }
    }
    // **N562 -- a gate's variable is declared, and it is ONE gate's.**
    let mut benutzt: BTreeMap<String, &SyscallDecl> = BTreeMap::new();
    for (s, _) in &tore {
        let Some(v) = &s.via else { continue };
        if !vars.contains_key(&v.text) {
            absagen.schiebe(
                Absage::fehler(
                    "N562",
                    v.span,
                    format!(
                        "`syscall {}` calls through `via {}`, and no `syscall {};` declares that \
                         variable",
                        s.name.text, v.text, v.text
                    ),
                )
                .mit_notiz(
                    "a system-call variable is declared once (`syscall V;`) and bound per target \
                     -- an undeclared name has no binding anyone could check",
                ),
            );
            continue;
        }
        if let Some(erster) = benutzt.get(&v.text) {
            absagen.schiebe(
                Absage::fehler(
                    "N562",
                    v.span,
                    format!(
                        "`syscall {}` calls through `via {}`, and `syscall {}` already does",
                        s.name.text, v.text, erster.name.text
                    ),
                )
                .mit_notiz(
                    "a binding's register map names ONE gate's parameters; two gates on one \
                     variable would each read a map written for the other",
                ),
            );
            continue;
        }
        benutzt.insert(v.text.clone(), s);
    }
    // **N564 -- a binding names a declared variable, once per target.**
    let mut je_ziel: BTreeMap<(String, String), Span> = BTreeMap::new();
    for block in &bild.bloecke {
        let ZielArt::Block { bindungen, .. } = &block.art else { continue };
        for b in bindungen {
            if !vars.contains_key(&b.var.text) {
                absagen.schiebe(
                    Absage::fehler(
                        "N564",
                        b.var.span,
                        format!(
                            "`target {}` binds `{}`, and no `syscall {};` declares that variable",
                            block.name.text, b.var.text, b.var.text
                        ),
                    )
                    .mit_notiz(
                        "a binding of nothing binds nothing -- a misspelt variable here leaves \
                         the one it meant unbound",
                    ),
                );
                continue;
            }
            let k = (block.name.text.clone(), b.var.text.clone());
            if let Some(erste) = je_ziel.get(&k) {
                absagen.schiebe(
                    Absage::fehler(
                        "N564",
                        b.var.span,
                        format!("`target {}` binds `{}` twice", block.name.text, b.var.text),
                    )
                    .mit_notiz(format!("the first binding is at offset {}", erste.von))
                    .mit_notiz(
                        "one variable, one binding per target -- two would give one gate two \
                         numbers, and the fill takes the first without saying so",
                    ),
                );
                continue;
            }
            je_ziel.insert(k, b.var.span);
        }
    }
    // **N563 -- every target binds every variable a gate uses.**
    for name in bild.namen() {
        let erster = bild.bloecke.iter().find(|b| b.name.text == name).unwrap();
        for (var, s) in &benutzt {
            if je_ziel.contains_key(&(name.clone(), var.clone())) {
                continue;
            }
            let aktiv = bild.aktiv.as_deref() == Some(name.as_str());
            let span = if aktiv { s.via.as_ref().unwrap().span } else { erster.name.span };
            absagen.schiebe(
                Absage::fehler(
                    "N563",
                    span,
                    format!(
                        "`syscall {}` calls through `{var}`, and `target {name}`{} does not bind it",
                        s.name.text,
                        if aktiv { " (the active target)" } else { "" }
                    ),
                )
                .mit_notiz(
                    "every target binds every variable a gate uses: switching the target must \
                     never meet a gate with no number, no registers and no named assumption",
                ),
            );
        }
    }
    if !hat_ziele {
        for s in benutzt.values() {
            absagen.schiebe(
                Absage::fehler(
                    "N563",
                    s.via.as_ref().unwrap().span,
                    format!(
                        "`syscall {}` calls through `via {}`, and the unit binds no target",
                        s.name.text,
                        s.via.as_ref().unwrap().text
                    ),
                )
                .mit_notiz(
                    "`target T abi A arch X { V = number … assume …; }` says which kernel the \
                     gate calls; without one it calls none",
                ),
            );
        }
    }
    // **N566 -- a different target is a different named assumption.**
    let mut annahme_von: BTreeMap<(String, String), String> = BTreeMap::new();
    for block in &bild.bloecke {
        let ZielArt::Block { bindungen, .. } = &block.art else { continue };
        for b in bindungen {
            let SyscallPaarung::Annahme { annahme, .. } = &b.paarung else { continue };
            let k = (b.var.text.clone(), annahme.text.clone());
            match annahme_von.get(&k) {
                Some(anderes) if anderes != &block.name.text => absagen.schiebe(
                    Absage::fehler(
                        "N566",
                        annahme.span,
                        format!(
                            "`target {}` binds `{}` under `{}`, the assumption `target {}` \
                             binds it under",
                            block.name.text, b.var.text, annahme.text, anderes
                        ),
                    )
                    .mit_notiz(
                        "a gate's named assumption is a statement about ONE kernel: another \
                         target is another kernel, and it keeps its contract under its own \
                         name, never silently under the first one's",
                    ),
                ),
                Some(_) => {}
                None => {
                    annahme_von.insert(k, block.name.text.clone());
                }
            }
        }
    }
    // **N566, second shape -- a target's assumption is named only by its target.** A
    // `progress A` over an assumption some target binds would keep resting on `A` under
    // every other target; `progress V` over the variable follows the binding
    // (`schleifen.rs`).
    let gebundene: BTreeMap<String, String> = bild
        .bloecke
        .iter()
        .flat_map(|blk| match &blk.art {
            ZielArt::Block { bindungen, .. } => bindungen
                .iter()
                .filter_map(|b| match &b.paarung {
                    SyscallPaarung::Annahme { annahme, .. } => {
                        Some((annahme.text.clone(), blk.name.text.clone()))
                    }
                    _ => None,
                })
                .collect::<Vec<_>>(),
            ZielArt::Wahl => Vec::new(),
        })
        .collect();
    if !gebundene.is_empty() {
        fn geh(b: &Block, g: &BTreeMap<String, String>, absagen: &mut Absagen) {
            for s in &b.anweisungen {
                if let StmtArt::Schleife(sch) = &s.art {
                    let f = match sch.as_ref() {
                        Schleife::Retry(x) => x.fortschritt.as_ref(),
                        Schleife::Forever(x) => x.fortschritt.as_ref(),
                        _ => None,
                    };
                    if let Some(z) = f {
                        if let Some(t) = g.get(&z.text) {
                            absagen.schiebe(
                                Absage::fehler(
                                    "N566",
                                    z.span,
                                    format!(
                                        "`progress {}` names the assumption `target {t}` binds \
                                         a system call under -- under another target the loop \
                                         would still rest on it",
                                        z.text
                                    ),
                                )
                                .mit_notiz(
                                    "name the system-call VARIABLE instead (`progress V`): it \
                                     resolves to the assumption the active target binds",
                                ),
                            );
                        }
                    }
                }
                for u in crate::unterbloecke(s) {
                    geh(u, g, absagen);
                }
            }
        }
        crate::fuer_jedes_item(baum, &mut |item| {
            if let ItemArt::Funktion(f) = &item.art {
                if let FnRumpf::Block(b) = &f.rumpf {
                    geh(b, &gebundene, absagen);
                }
            }
        });
    }
    // **Inactive targets are held to the gate's shape** (the active one is the tree).
    let annahmen = crate::annahmen(baum);
    for block in &bild.bloecke {
        if bild.aktiv.as_deref() == Some(block.name.text.as_str()) {
            continue;
        }
        let ZielArt::Block { bindungen, .. } = &block.art else { continue };
        for b in bindungen {
            let Some((s, modul)) = tore
                .iter()
                .find(|(s, _)| s.via.as_ref().is_some_and(|v| v.text == b.var.text))
            else {
                continue;
            };
            let t = gebunden(s, block, b);
            let mut innen = Absagen::neu("");
            crate::syscall::gestalt(baum, modul, &t, &mut innen);
            if let SyscallPaarung::Annahme { annahme, .. } = &b.paarung {
                match annahmen.get(&annahme.text) {
                    None => innen.schiebe(Absage::fehler(
                        "N004",
                        annahme.span,
                        format!("`syscall {}` names no declared assumption", s.name.text),
                    )),
                    Some(false) => innen.schiebe(Absage::fehler(
                        "N005",
                        annahme.span,
                        format!("`syscall {}` rests on an unfalsifiable assumption", s.name.text),
                    )),
                    Some(true) => {}
                }
            }
            for a in innen.absagen {
                absagen.schiebe(a.mit_notiz(format!(
                    "under `target {}` (not the active target -- every binding is checked)",
                    block.name.text
                )));
            }
        }
    }
}

/// **N565 -- the active target is determined, and a name is one ABI.**
fn wahl(bild: &Zielbild, absagen: &mut Absagen) {
    let namen = bild.namen();
    // One name, one ABI.
    let mut abi_von: BTreeMap<String, (String, String)> = BTreeMap::new();
    for b in &bild.bloecke {
        let ZielArt::Block { abi, arch, .. } = &b.art else { continue };
        let paar = (abi.text.clone(), arch.text.clone());
        match abi_von.get(&b.name.text) {
            Some(p) if p != &paar => fehler565(
                absagen,
                b.name.span,
                format!(
                    "`target {}` is declared `abi {} arch {}` here and `abi {} arch {}` before",
                    b.name.text, paar.0, paar.1, p.0, p.1
                ),
            ),
            Some(_) => {}
            None => {
                abi_von.insert(b.name.text.clone(), paar);
            }
        }
    }
    let mut erste_wahl: Option<&Ident> = None;
    for w in &bild.wahlen {
        if !namen.contains(&w.text) {
            fehler565(
                absagen,
                w.span,
                format!("`target {};` selects a target no `target {} abi … {{ … }}` block binds", w.text, w.text),
            );
        }
        match erste_wahl {
            Some(e) if e.text != w.text => fehler565(
                absagen,
                w.span,
                format!("`target {};` selects a second target beside `target {};`", w.text, e.text),
            ),
            Some(_) => {}
            None => erste_wahl = Some(w),
        }
    }
    if let Some(v) = &bild.vorgabe {
        if !namen.is_empty() && !namen.contains(v) {
            fehler565(
                absagen,
                bild.bloecke[0].name.span,
                format!(
                    "`GABBRO_TARGET={v}` (or `--target {v}`) names no target of this unit -- it binds `{}`",
                    namen.join("`, `")
                ),
            );
        }
    } else if bild.wahlen.is_empty() && namen.len() > 1 {
        fehler565(
            absagen,
            bild.bloecke[0].name.span,
            format!(
                "the unit binds {} targets (`{}`) and selects none -- `target T;` says which one \
                 the gates call",
                namen.len(),
                namen.join("`, `")
            ),
        );
    }
}

fn fehler565(absagen: &mut Absagen, span: Span, text: String) {
    absagen.schiebe(Absage::fehler("N565", span, text).mit_notiz(
        "which kernel a gate calls is ONE fact of the unit: one selection, or one target, and \
         a target name means one ABI",
    ));
}

/// **N561 -- an entry's register binding is its dispatch's signature** (OFFEN O32 (7)).
///
/// The bare-metal stub (`METALL_EINTRITT`, `gabbro build`'s metal driver) passes the
/// `regs in` registers, in order, as the dispatch's arguments and stores its result into
/// the one `regs out` register. With a mismatch there is no honest stub: it could only
/// guess which register feeds which parameter. Checked where the dispatch resolves to a
/// function of this unit (an unresolved dispatch is `N006`'s); the widths are not held
/// (every register is a 64-bit word, and a narrower parameter takes its low bits).
fn eintritte(baum: &Programm, absagen: &mut Absagen) {
    fn sammle<'a>(items: &'a [Item], pfad: &str, aus: &mut Vec<(String, &'a FnDecl)>) {
        for i in items {
            match &i.art {
                ItemArt::Funktion(f) => aus.push((pfad.to_string(), f)),
                ItemArt::Modul(m) => {
                    let innen = if pfad.is_empty() {
                        m.pfad.text()
                    } else {
                        format!("{pfad}::{}", m.pfad.text())
                    };
                    sammle(&m.items, &innen, aus);
                }
                _ => {}
            }
        }
    }
    let mut fns: Vec<(String, &FnDecl)> = Vec::new();
    sammle(&baum.items, "", &mut fns);
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let ItemArt::Entry(e) = &item.art else { return };
        let ziel = e.dispatch.text();
        let f = fns.iter().find(|(m, f)| {
            let voll = if m.is_empty() { f.name.text.clone() } else { format!("{m}::{}", f.name.text) };
            voll == ziel || (e.dispatch.teile.len() == 1 && m == modul && f.name.text == ziel)
        });
        let Some((_, f)) = f else { return };
        let n_par = f.parameter.len();
        // A `-> never` dispatch answers nothing: an out register would receive nothing
        // (the metal stub cannot store a `void` call), as `gabbro build` reads it too.
        let antwortet = f.ergebnis.is_some() && !matches!(f.ergebnis, Some(TypExpr::Never(_)));
        let mut fehler: Vec<String> = Vec::new();
        if e.regs_in.len() != n_par {
            fehler.push(format!(
                "`regs in` names {} register(s) and `{}` takes {} parameter(s)",
                e.regs_in.len(),
                f.name.text,
                n_par
            ));
        }
        if e.regs_out.len() > 1 {
            fehler.push(format!(
                "`regs out` names {} registers, and a dispatch answers at most one value",
                e.regs_out.len()
            ));
        } else if e.regs_out.len() == 1 && !antwortet {
            // An answer with NO out register is dropped -- nothing is guessed, and the
            // entry promises to change no register; a register with no answer is.
            fehler.push(format!(
                "`regs out` names `{}` and `{}` answers nothing to put there",
                e.regs_out[0].1.text, f.name.text
            ));
        }
        if let Some(r) = &f.fehler {
            fehler.push(format!(
                "`{}` answers through `or {}`, and a register carries no reason",
                f.name.text, r.text
            ));
        }
        if fehler.is_empty() {
            return;
        }
        absagen.schiebe(
            Absage::fehler(
                "N561",
                e.name.span,
                format!(
                    "`entry {}` does not bind the signature of its dispatch `{}`: {}",
                    e.name.text,
                    ziel,
                    fehler.join("; ")
                ),
            )
            .mit_notiz(
                "the entry stub passes the `regs in` registers, in order, as the dispatch's \
                 arguments and stores its result into the `regs out` register -- with a \
                 mismatch no stub can bind them without guessing",
            ),
        );
    });
}
