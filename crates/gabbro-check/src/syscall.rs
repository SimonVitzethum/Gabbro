//! **`syscall` -- the user side of a system call** (PLAN-SYSCALL.md, lane S5).
//!
//! The parser reads the `syscalldecl` production (SYNTAX.md §12.1) into
//! `SyscallDecl`; this pass holds the declaration against its own shape. The
//! stub template is lane S6's -- until it lands the emitter refuses every unit
//! carrying a syscall (`C001`), so nothing here promises a lowering.
//!
//! The six rules, each with its probe:
//!
//! | code | rule | probe |
//! |---|---|---|
//! | `N057` | the in-registers are pairwise distinct | gift: duplicate in-register |
//! | `N058` | an out register is never clobbered | gift: clobbered out-register |
//! | `N059` | every parameter is bound exactly once | gift: unbound parameter |
//! | `N060` | every named register is an x86_64 general register | gift: unknown register |
//! | `N061` | the `errors` map is total over the listed errnos and every target is a case of the `or R` channel | gift: errno mapped to an undeclared reason |
//! | `N062` | a `kernel` pairing is refused until the pairing check lands | gift: kernel path |
//! | `A006` | the syscall names no sealed architecture -- x86_64 only | gift: arch mismatch |
//!
//! Three questions belong to existing rules and are NOT re-issued here: the
//! `arch` against the declared arches (`A005`, `namen.rs`), the named
//! assumption (`N004`/`N005` shape, `namen.rs`), and the call boundary
//! (`H007` at call sites, `geteilt.rs`, over the `Signatur` this declaration
//! carries in `Umgebung` exactly like an `extern fn`).

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};
use std::collections::{HashMap, HashSet};

/// The x86_64 general registers -- and only they. `aarch64` stays sealed, and
/// a control, segment or floating-point register has no binding in the Linux
/// syscall ABI this declaration mirrors. `rsp`/`rbp` are general registers by
/// name; holding the stack against the declaration is the stub's business
/// (lane S6), not this pass's.
const REGISTER: &[&str] = &[
    "rax", "rbx", "rcx", "rdx", "rsi", "rdi", "rbp", "rsp", "r8", "r9", "r10", "r11",
    "r12", "r13", "r14", "r15",
];

pub fn pass(baum: &Programm, absagen: &mut Absagen) {
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let ItemArt::Syscall(s) = &item.art else { return };
        registerkarte(s, absagen);
        fehlertabelle(baum, modul, s, absagen);
        bauart(s, absagen);
    });
}

/// **`N057`/`N058`/`N059`/`N060` -- the register map is well-formed.**
///
/// Four refusals, one walk, in clause order: unknown registers first (a name
/// the ABI table does not know poisons every later question about it), then
/// the duplicate in-register, the clobbered out-register and the parameter
/// binding. Each code has exactly one issuance site in this file.
fn registerkarte(s: &SyscallDecl, absagen: &mut Absagen) {
    // **N060 -- every named register is an x86_64 general register.**
    for (reg, wo) in s
        .regs_in
        .iter()
        .map(|(r, _)| (r, "regs in"))
        .chain(s.regs_out.iter().map(|r| (r, "regs out")))
        .chain(s.clobbers.iter().map(|r| (r, "clobbers")))
    {
        if !REGISTER.contains(&reg.text.as_str()) {
            absagen.schiebe(
                Absage::fehler(
                    "N060",
                    reg.span,
                    format!(
                        "`{}` names `{}` in `{}`, and that is no x86_64 general register",
                        s.name.text, reg.text, wo
                    ),
                )
                .mit_notiz(
                    "the binding names one of `rax` `rbx` `rcx` `rdx` `rsi` `rdi` \
                     `rbp` `rsp` `r8`-`r15` -- a control, segment or floating-point \
                     register has no binding in this ABI",
                ),
            );
        }
    }
    // **N057 -- the in-registers are pairwise distinct.**
    let mut gesehen: HashMap<&str, gabbro_syntax::span::Span> = HashMap::new();
    for (reg, _) in &s.regs_in {
        if let Some(erste) = gesehen.get(reg.text.as_str()) {
            absagen.schiebe(
                Absage::fehler(
                    "N057",
                    reg.span,
                    format!(
                        "`{}` binds `{}` twice in `regs in`",
                        s.name.text, reg.text
                    ),
                )
                .mit_notiz(format!("the first binding is at offset {}", erste.von))
                .mit_notiz(
                    "two parameters in one register have no reading -- the stub \
                     writes the register once, and one of the two values never arrives",
                ),
            );
        } else {
            gesehen.insert(reg.text.as_str(), reg.span);
        }
    }
    // **N058 -- an out register is never clobbered.**
    for r in &s.regs_out {
        if let Some(c) = s.clobbers.iter().find(|c| c.text == r.text) {
            absagen.schiebe(
                Absage::fehler(
                    "N058",
                    c.span,
                    format!(
                        "`{}` carries `{}` out and lists it under `clobbers`",
                        s.name.text, r.text
                    ),
                )
                .mit_notiz(
                    "what is carried out is not destroyed -- the contract would \
                     promise the answer in a register the declaration hands to the \
                     kernel as scratch",
                ),
            );
        }
    }
    // **N059 -- every parameter is bound exactly once.**
    let mut bindungen: HashMap<&str, usize> = HashMap::new();
    for (_, p) in &s.regs_in {
        *bindungen.entry(p.text.as_str()).or_default() += 1;
    }
    for p in &s.parameter {
        match bindungen.get(p.name.text.as_str()).copied().unwrap_or(0) {
            1 => {}
            0 => absagen.schiebe(
                Absage::fehler(
                    "N059",
                    p.name.span,
                    format!(
                        "`{}` never binds parameter `{}` to a register",
                        s.name.text, p.name.text
                    ),
                )
                .mit_notiz(
                    "an unbound parameter has no register on entry -- the stub \
                     would read a value nobody put there",
                ),
            ),
            n => absagen.schiebe(
                Absage::fehler(
                    "N059",
                    p.name.span,
                    format!(
                        "`{}` binds parameter `{}` to {n} registers",
                        s.name.text, p.name.text
                    ),
                )
                .mit_notiz(
                    "one parameter in two registers has no reading -- the second \
                     binding overwrites the first before the kernel reads either",
                ),
            ),
        }
    }
    for (_, p) in &s.regs_in {
        if !s.parameter.iter().any(|q| q.name.text == p.text) {
            absagen.schiebe(
                Absage::fehler(
                    "N059",
                    p.span,
                    format!(
                        "`{}` binds `{}` to a register, and no parameter is so named",
                        s.name.text, p.text
                    ),
                )
                .mit_notiz(
                    "a binding without a parameter binds nothing -- the register \
                     carries a value the declaration never names",
                ),
            );
        }
    }
}

/// **`N061` -- the `errors` map is total over the listed errnos.**
///
/// Four ways of failing, ONE issuance site below: a target outside the declared
/// `or R` channel, a channel that is not declared here at all, a map with no
/// channel, and an errno with two arms. What is NOT checked here is the errno
/// side against a kernel table -- the map itself lists the admitted errnos, and
/// an errno outside the table is the named hardware outcome (`hardware
/// (annahme a)`), not a declaration fault.
fn fehlertabelle(baum: &Programm, modul: &str, s: &SyscallDecl, absagen: &mut Absagen) {
    /// One fault of the map, with the span it points at and the detail behind
    /// the shared sentence.
    struct Fehler {
        span: gabbro_syntax::span::Span,
        detail: String,
    }
    let u = crate::umgebung::Umgebung::sammle(baum);
    // The declared cases of the `or R` channel, resolved from the syscall's own
    // module outward -- the same order every name resolution uses. **One fault,
    // one refusal:** a missing channel falls ONCE, not once per arm.
    let faelle: Option<Vec<String>> = match &s.fehler {
        None => None,
        Some(r) => u
            .kandidaten_aufloesbar(modul, &r.text)
            .into_iter()
            .find_map(|k| u.gruende.get(&k).cloned()),
    };
    let mut fehler: Vec<Fehler> = Vec::new();
    if !s.errors.is_empty() {
        match (&s.fehler, &faelle) {
            (None, _) => {
                let (errno, ziel) = &s.errors[0];
                fehler.push(Fehler {
                    span: ziel.span,
                    detail: format!(
                        "`{}` => `{}` with no `or R` channel -- the decoding has nowhere to deliver",
                        errno.text, ziel.text
                    ),
                });
            }
            (Some(r), None) => {
                fehler.push(Fehler {
                    span: r.span,
                    detail: format!(
                        "`or {}` declares nothing -- a channel without cases is none",
                        r.text
                    ),
                });
            }
            (Some(_), Some(_)) => {}
        }
    }
    if fehler.is_empty() {
        let faelle = faelle.unwrap_or_default();
        let mut errnos: HashSet<&str> = HashSet::new();
        for (errno, ziel) in &s.errors {
            if !errnos.insert(errno.text.as_str()) {
                fehler.push(Fehler {
                    span: errno.span,
                    detail: format!(
                        "`{}` twice -- the second arm decides nothing, and the decoding it \
                         generates would carry a dead branch",
                        errno.text
                    ),
                });
            }
            if !faelle.iter().any(|c| c == &ziel.text) {
                fehler.push(Fehler {
                    span: ziel.span,
                    detail: format!(
                        "`{}` => `{}` -- an undeclared reason never arrives, and the decoding \
                         it generates would carry a dead arm",
                        errno.text, ziel.text
                    ),
                });
            }
        }
    }
    // **The one issuance site of this rule.** Every fault above shares the
    // sentence; the detail behind the dash names which arm failed and how.
    // *One fault, one refusal:* a missing channel falls ONCE, not once per arm
    // -- but two bad arms are two faults, and both are refused.
    for f in fehler {
        absagen.schiebe(
            Absage::fehler(
                "N061",
                f.span,
                format!(
                    "`{}` mistargets its `errors` map -- {}",
                    s.name.text, f.detail
                ),
            )
            .mit_notiz(
                "every listed errno has exactly one arm, and every target is a case \
                 of the reason the signature declares -- a total map answers each \
                 admitted errno once, with nowhere else to deliver",
            ),
        );
    }
}

/// **`A006`/`N062` -- the machine and the counterpart.**
///
/// `A006`: the syscall names no sealed architecture -- x86_64 only, as the
/// whole emitter is. `N062`: a `kernel` pairing is refused until the pairing
/// check and the stub land (lane S6) -- with its own name, never silence.
fn bauart(s: &SyscallDecl, absagen: &mut Absagen) {
    if s.arch.text != "x86_64" {
        absagen.schiebe(
            Absage::fehler(
                "A006",
                s.arch.span,
                format!(
                    "`{}` declares `arch {}` after `abi {}`, and only `x86_64` is implemented",
                    s.name.text, s.arch.text, s.abi.text
                ),
            )
            .mit_notiz(
                "`aarch64` stays sealed -- a syscall for a machine the emitter \
                 cannot lower would promise a stub nobody writes",
            ),
        );
    }
    if let SyscallPaarung::Kernel { pfad } = &s.paarung {
        absagen.schiebe(
            Absage::fehler(
                "N062",
                pfad.span,
                format!(
                    "`{}` pairs with kernel `{}`, and kernel pairing not implemented yet",
                    s.name.text,
                    pfad.text()
                ),
            )
            .mit_notiz(
                "the call is paired with a Gabbro kernel's dispatch entry for the \
                 same number, and no assumption is named -- the pairing check and \
                 the stub land in lane S6, and until then every `kernel` form \
                 falls here, by name",
            ),
        );
    }
}
