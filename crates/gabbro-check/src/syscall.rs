//! **`syscall` -- the user side of a system call** (PLAN-SYSCALL.md, lane S5).
//!
//! The parser reads the `syscalldecl` production (SYNTAX.md §12.1) into
//! `SyscallDecl`; this pass holds the declaration against its own shape. The
//! stub template is lane S6's (`syscall_stumpf` in `emit.rs`, rules
//! `C180`-`C184`) -- what stands here is the declaration side, and nothing
//! here promises the lowering.
//!
//! The six rules, each with its probe:
//!
//! | code | rule | probe |
//! |---|---|---|
//! | `N063` | the in-registers are pairwise distinct | gift: duplicate in-register |
//! | `N064` | an out register is never clobbered | gift: clobbered out-register |
//! | `N065` | every parameter is bound exactly once | gift: unbound parameter |
//! | `N066` | every named register is an x86_64 general register | gift: unknown register |
//! | `N067` | the `errors` map is total over the listed errnos and every target is a case of the `or R` channel | gift: errno mapped to an undeclared reason |
//! | `N068` | a `kernel` pairing is refused until the pairing check lands | gift: kernel path |
//! | `N322` | the `syscall` declares a countable `costs` promise (the lane-114 gap, closed) | gift 986: costless syscall |
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
        kostenversprechen(baum, modul, s, absagen);
    });
}

/// **`N063`/`N064`/`N065`/`N066` -- the register map is well-formed.**
///
/// Four refusals, one walk, in clause order: unknown registers first (a name
/// the ABI table does not know poisons every later question about it), then
/// the duplicate in-register, the clobbered out-register and the parameter
/// binding. Each code has exactly one issuance site in this file.
fn registerkarte(s: &SyscallDecl, absagen: &mut Absagen) {
    // **N066 -- every named register is an x86_64 general register.**
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
                    "N066",
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
    // **N063 -- the in-registers are pairwise distinct.**
    let mut gesehen: HashMap<&str, gabbro_syntax::span::Span> = HashMap::new();
    for (reg, _) in &s.regs_in {
        if let Some(erste) = gesehen.get(reg.text.as_str()) {
            absagen.schiebe(
                Absage::fehler(
                    "N063",
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
    // **N064 -- an out register is never clobbered.**
    for r in &s.regs_out {
        if let Some(c) = s.clobbers.iter().find(|c| c.text == r.text) {
            absagen.schiebe(
                Absage::fehler(
                    "N064",
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
    // **N065 -- every parameter is bound exactly once.**
    let mut bindungen: HashMap<&str, usize> = HashMap::new();
    for (_, p) in &s.regs_in {
        *bindungen.entry(p.text.as_str()).or_default() += 1;
    }
    for p in &s.parameter {
        match bindungen.get(p.name.text.as_str()).copied().unwrap_or(0) {
            1 => {}
            0 => absagen.schiebe(
                Absage::fehler(
                    "N065",
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
                    "N065",
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
                    "N065",
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

/// **`N067` -- the `errors` map is total over the listed errnos.**
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
                "N067",
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

/// **`A006`/`N068` -- the machine and the counterpart.**
///
/// `A006`: the syscall names no sealed architecture -- x86_64 only, as the
/// whole emitter is. `N068`: a `kernel` pairing is refused until the pairing
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
                "N068",
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

/// **`N322` -- the `syscall` declares a countable `costs` promise.**
///
/// The lane-114 gap, closed at the declaration: a foreign edge counts its
/// DECLARED cost `fa` on top of the §1 dispatch step (`fremd_kein_null_*`,
/// `KostenG.lean` §13), so a `syscall` without a countable promise is
/// cost-opaque -- no bounded loop can host a call through it (`beispiele/96`)
/// and a caller with a cost promise meets `K003` over it. Three shapes, one
/// issuance site below: a missing clause, a clause the pass cannot read as
/// one number, and a bound below zero (less than the dispatch step every
/// foreign edge pays).
///
/// What is NOT demanded here is HONESTY: `fa` is a promise about the kernel,
/// like `costs` at an `extern fn` -- the checker counts it, it does not
/// re-measure it. And symbolic bounds (`64 + 12 * lenof(m)`, readable at an
/// `fn`) stay refused: the trip-count division (`durchgangskosten`) divides
/// by one number, and a symbol is none.
fn kostenversprechen(baum: &Programm, modul: &str, s: &SyscallDecl, absagen: &mut Absagen) {
    let u = crate::umgebung::Umgebung::sammle(baum);
    if u.syscall_kosten(modul, s).is_some() {
        return;
    }
    let (span, detail) = match &s.costs {
        None => (
            s.name.span,
            "declares no `costs` -- a call through it counts nothing, and no \
             bounded loop can host one"
                .to_string(),
        ),
        Some(c) => match u.konst_wert(modul, c) {
            None => (
                c.span,
                "promises costs the pass cannot read as one number -- `40`, \
                 `NSLOTS * 8`, never `n * 100`"
                    .to_string(),
            ),
            Some(n) => (
                c.span,
                format!(
                    "promises `{n} ops`, below the dispatch step every foreign edge pays"
                ),
            ),
        },
    };
    // **The one issuance site of this rule.** Missing, unreadable and negative
    // are mutually exclusive -- one declaration carries one clause -- so one
    // fault falls here at most once.
    absagen.schiebe(
        Absage::fehler(
            "N322",
            span,
            format!(
                "`{}` carries no countable cost promise -- {}",
                s.name.text, detail
            ),
        )
        .mit_notiz(
            "a foreign edge counts its DECLARED cost on top of the dispatch step \
             (`KostenG.lean` §13: `fa` plus dispatch, never zero) -- without a \
             number here there is nothing to count",
        )
        .mit_notiz(
            "the clause stands behind `effects` in fixed order: \
             `effects { … } costs <= N ops assume … ;`",
        ),
    );
}
