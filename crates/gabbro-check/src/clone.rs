//! **`child` + `stack` -- the checked clone handoff** (lane O-1, K-1).
//!
//! K-1 measured the gap: a `syscall` gate can DECLARE the raw clone call
//! (number, registers, error map -- all user-made, all in the declaration,
//! the bm5 shape precedent), but the handoff itself -- *"the child starts
//! on the stack from the handed register and must never return into the
//! caller's frame"* -- had no checked shape. This pass holds the two new
//! shapes against each other:
//!
//! * the `stack r` clause names the handed-stack register AS a stack -- the
//!   one clause that may claim stack-ness, and only between `regs out` and
//!   `clobbers` (E4: fixed order);
//! * the `child { … }` statement is the child path: the block that runs on
//!   the handed stack.
//!
//! The four (+1) rules, each with its probe:
//!
//! | code | rule | probe |
//! |---|---|---|
//! | `N446` | `stack r` names a register that is bound in `regs in`, kept out of `clobbers` and out of `regs out` | gift 1107 |
//! | `N447` | stack-ness is claimed once -- a second `stack` clause falls | gift 1108 |
//! | `N448` | the child path never leaves: no `return` inside, no `leave`/`next` past the region | gift 1109 |
//! | `N449` | the child path never falls through: with no `return` inside, every path ends in a never-returning call or a never-exiting loop | gift 1110 |
//! | `N450` | a `child` block runs behind a stack-carrying gate -- a handoff with no handed stack falls | gift 1111 |
//!
//! What is NOT checked here is the link the machine keeps: that the child
//! really starts on the handed stack is the stub's business (`emit.rs`,
//! part 3) and the runtime's assumption (d2, `KlonAnnahme`), not this
//! pass's. What stands here is the shape the program can break: a gate
//! handing no register, a path returning into the caller frame, a path
//! falling past its end, a path with no gate behind it.
//!
//! BINDING CONSTRAINT (owner): no OS data enters this file -- no clone
//! number, no flag, no errno. The register FILE (`REGISTER` below) is the
//! pre-existing machine vocabulary `syscall.rs` holds too (its twin, named
//! here on purpose: the syntax crate takes no checker dependency question,
//! and this pass reads no checker map but its own walk).

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};
use std::collections::HashSet;

/// The x86_64 general registers -- and only they. The twin of `REGISTER`
/// in `syscall.rs`, named here on purpose (see the module head): this pass
/// reads the declaration, not the other pass's table, so a drift between
/// the two reads as two refusals, never as silence.
const REGISTER: &[&str] = &[
    "rax", "rbx", "rcx", "rdx", "rsi", "rdi", "rbp", "rsp", "r8", "r9", "r10", "r11",
    "r12", "r13", "r14", "r15",
];

pub fn pass(baum: &Programm, absagen: &mut Absagen) {
    let divergent = nie_kehrende(baum);
    let mut tore_mit_stapel = 0;
    crate::fuer_jedes_item_im_modul(baum, &mut |item, _modul| {
        if let ItemArt::Syscall(s) = &item.art {
            stapelklausel(s, absagen);
            if s.stapel.len() == 1 {
                tore_mit_stapel += 1;
            }
        }
    });
    // **The bodies, second:** a `child` block lives in a function body, and
    // the gate count above is unit-wide -- a path with no gate behind it
    // (`N450`) needs both.
    crate::fuer_jedes_item_im_modul(baum, &mut |item, _modul| {
        if let ItemArt::Funktion(f) = &item.art {
            if let FnRumpf::Block(b) = &f.rumpf {
                kindpfade(&f.name.text, b, &divergent, tore_mit_stapel, absagen, true);
            }
        }
    });
}

/// The callees that never return: every declared function and every
/// `syscall` gate whose result is `-> never` (an `extern` exit gate, an
/// `asm` watchdog, a never-answering syscall alike -- the declaration is
/// the promise, and the emitter writes `_Noreturn` on the prototype).
/// Last segments, like `endet_immer`'s `divergent` list beside which this
/// one is read.
fn nie_kehrende(baum: &Programm) -> Vec<String> {
    let mut aus = Vec::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, _| match &item.art {
        ItemArt::Funktion(f) => {
            if matches!(f.ergebnis, Some(TypExpr::Never(_))) {
                aus.push(f.name.text.clone());
            }
        }
        ItemArt::Syscall(s) => {
            if matches!(s.ergebnis, Some(TypExpr::Never(_))) {
                aus.push(s.name.text.clone());
            }
        }
        _ => {}
    });
    aus
}

/// **`N446`/`N447` -- the `stack` clause names one handed register.**
///
/// `N446`: the named register is an x86_64 general register, bound in
/// `regs in`, kept out of `clobbers` and out of `regs out` -- the handed
/// stack arrives in it, so scratch or the answer register never reaches
/// the child. Four ways of failing, ONE issuance site below.
/// `N447`: a second (or third) `stack` clause -- stack-ness is claimed
/// once, and only here.
fn stapelklausel(s: &SyscallDecl, absagen: &mut Absagen) {
    if s.stapel.len() > 1 {
        for dup in s.stapel.iter().skip(1) {
            absagen.schiebe(
                Absage::fehler(
                    "N447",
                    dup.span,
                    format!(
                        "`{}` claims stack-ness twice -- `{}` and `{}`",
                        s.name.text, s.stapel[0].text, dup.text
                    ),
                )
                .mit_notiz(
                    "one clause names the handed stack; a second has no reading -- the stub \
                     hands one register to the child, and two names would split it",
                ),
            );
        }
    }
    let Some(stapel) = s.stapel.first() else { return };
    let detail = if !REGISTER.contains(&stapel.text.as_str()) {
        Some(format!(
            "`{}` is no x86_64 general register -- the binding names one of `rax` `rbx` \
             `rcx` `rdx` `rsi` `rdi` `rbp` `rsp` `r8`-`r15`",
            stapel.text
        ))
    } else if !s.regs_in.iter().any(|(r, _)| r.text == stapel.text) {
        Some(format!(
            "`{}` is bound in no `regs in` -- the handed stack arrives in a register the \
             declaration never fills",
            stapel.text
        ))
    } else if s.clobbers.iter().any(|c| c.text == stapel.text) {
        Some(format!(
            "`{}` stands under `clobbers` -- the kernel takes it as scratch, and a handed \
             stack in scratch never reaches the child",
            stapel.text
        ))
    } else if s.regs_out.iter().any(|r| r.text == stapel.text) {
        Some(format!(
            "`{}` carries the answer out -- the decoding overwrites the handed stack with \
             the raw return value",
            stapel.text
        ))
    } else {
        None
    };
    // **The one issuance site of this rule.** Every fault above shares the
    // sentence; the detail behind the dash names which demand failed.
    if let Some(detail) = detail {
        absagen.schiebe(
            Absage::fehler(
                "N446",
                stapel.span,
                format!(
                    "`{}` names no handed stack register -- {}",
                    s.name.text, detail
                ),
            )
            .mit_notiz(
                "the handed stack arrives in one of `regs in`, kept out of `clobbers` and \
                 out of `regs out` -- a stack in scratch or in the answer register never \
                 reaches the child",
            ),
        );
    }
}

/// The outermost `child` blocks of a body: a nested `child` is part of its
/// outer region, not a region of its own.
fn kindpfade(
    fname: &str,
    b: &Block,
    divergent: &[String],
    tore_mit_stapel: usize,
    absagen: &mut Absagen,
    aussen: bool,
) {
    for s in &b.anweisungen {
        if let StmtArt::Child(region) = &s.art {
            if aussen {
                kindregion(fname, region, divergent, tore_mit_stapel, absagen);
            }
            // Nested regions walk for deeper nesting, but refuse nothing
            // twice: the outer region already covers them.
            kindpfade(fname, region, divergent, tore_mit_stapel, absagen, false);
        } else {
            for k in crate::unterbloecke(s) {
                kindpfade(fname, k, divergent, tore_mit_stapel, absagen, aussen);
            }
        }
    }
}

/// **`N448`/`N449`/`N450` -- one child region.**
///
/// `N450` first: with no stack-carrying gate in the unit the handoff has
/// no handed stack. `N448`: no `return` in the region, no `leave`/`next`
/// past it. `N449`: with no `return` inside, the region never falls
/// through -- `endet_immer` over the unit's never-returning callees.
fn kindregion(
    fname: &str,
    region: &Block,
    divergent: &[String],
    tore_mit_stapel: usize,
    absagen: &mut Absagen,
) {
    if tore_mit_stapel == 0 {
        absagen.schiebe(
            Absage::fehler(
                "N450",
                region.span,
                format!("`{fname}` runs a `child` path with no `stack` gate in the unit"),
            )
            .mit_notiz(
                "a `child` block runs on the handed stack of a `syscall … stack r` gate -- \
                 with no gate claiming a stack in the unit no stack is ever handed, and the \
                 path has nothing to stand on (a faulted gate still counts here: its own \
                 fault names what is broken about it)",
            ),
        );
    }
    let mut rueckkehr = Vec::new();
    sammel_rueckkehr(region, &mut rueckkehr);
    let marken = sammel_marken(region);
    let mut flucht = Vec::new();
    sammel_flucht(region, &marken, &mut flucht);
    // **The one issuance site of this rule.** Every leaving statement --
    // a `return` into the caller frame, a `leave`/`next` past the region --
    // shares the sentence; the span names which one left.
    for span in rueckkehr.into_iter().chain(flucht) {
        absagen.schiebe(
            Absage::fehler(
                "N448",
                span,
                format!("`{fname}` leaves its `child` path -- the child runs on the handed stack"),
            )
            .mit_notiz(
                "the child never returns into the caller's frame: neither by `return` nor \
                 by jumping past the block (`leave`/`next` out of the region) -- the caller \
                 stood where the handed stack no longer is",
            ),
        );
    }
    // **With no `return` inside, the fall-through is the fault.** Where a
    // `return` already fell, the return is the fault and the fall-through
    // behind it is none -- one fault, one refusal.
    if !enthaelt_rueckkehr(region) && !crate::endet_immer(region, divergent) {
        absagen.schiebe(
            Absage::fehler(
                "N449",
                region.span,
                format!("`{fname}`'s `child` path can fall through -- past the block stands the caller frame"),
            )
            .mit_notiz(
                "every path through the block must end in a call that never returns (a \
                 `-> never` gate) or in a loop that never exits -- the fall-through past \
                 the block IS the return `N448` forbids, one statement later",
            ),
        );
    }
}

/// Every `return` in the region, by span.
fn sammel_rueckkehr(b: &Block, aus: &mut Vec<gabbro_syntax::span::Span>) {
    for s in &b.anweisungen {
        if let StmtArt::Return(_) = &s.art {
            aus.push(s.span);
        }
        for k in crate::unterbloecke(s) {
            sammel_rueckkehr(k, aus);
        }
    }
}

/// Whether any `return` stands in the region.
fn enthaelt_rueckkehr(b: &Block) -> bool {
    b.anweisungen.iter().any(|s| {
        matches!(&s.art, StmtArt::Return(_))
            || crate::unterbloecke(s).into_iter().any(enthaelt_rueckkehr)
    })
}

/// The loop marks defined in the region: a `leave`/`next` naming one of
/// these stays on the path; any other jumps past it.
fn sammel_marken(b: &Block) -> HashSet<String> {
    let mut aus = HashSet::new();
    fn gang(b: &Block, aus: &mut HashSet<String>) {
        for s in &b.anweisungen {
            if let StmtArt::Schleife(sch) = &s.art {
                let marke = match sch.as_ref() {
                    Schleife::Traverse(_) => None,
                    Schleife::Retry(r) => r.marke.as_ref(),
                    Schleife::Forever(f) => f.marke.as_ref(),
                };
                if let Some(m) = marke {
                    aus.insert(m.text.clone());
                }
            }
            for k in crate::unterbloecke(s) {
                gang(k, aus);
            }
        }
    }
    gang(b, &mut aus);
    aus
}

/// Every `leave`/`next` in the region whose mark is NOT defined in it, by
/// span: the jump leaves the child path for the caller frame.
fn sammel_flucht(b: &Block, marken: &HashSet<String>, aus: &mut Vec<gabbro_syntax::span::Span>) {
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Leave(m) | StmtArt::Next(m) => {
                if !marken.contains(&m.text) {
                    aus.push(s.span);
                }
            }
            _ => {}
        }
        for k in crate::unterbloecke(s) {
            sammel_flucht(k, marken, aus);
        }
    }
}
