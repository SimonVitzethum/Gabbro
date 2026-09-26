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
//! | `N450` | a stack-gate call dominates the `child` block, and one call hands to one region (fix lane F3: per region, no longer unit-wide) | gifts 1111, 1139, 1140 |
//! | `N451` | the child path reads no caller `let`-temporary it was not handed (the gate answer, every other caller `let`; the read set is the exhaustive `kindzugriff`, `grow` and lock places included since fix lane F3) | gifts 1113, 1146, 1147 |
//! | `N452` | the child path reads no caller parameter (or loop/match binder) it was not handed | gifts 1115, 1116 |
//! | `N456` | the child holds nothing the parent holds: no `child` inside `locks`/`observes`/`breaking` or under a signature `requires Held` (fix lane F3) | gifts 1141, 1142 |
//! | `N457` | the child is a thread for race freedom: every carrier its path touches that anyone writes is guarded, atomic or per-core (in `fusswache2.rs`, fix lane F3) | gifts 1143, 1144, 1145 |
//! | `C185` | the `child` block has no lowering in the stub template and is refused by name (in `emit.rs`, beside the best-effort block) | gift 1112 |
//!
//! What is NOT checked here is the link the machine keeps: that the child
//! really starts on the handed stack is the stub's business (`emit.rs`,
//! part 3) and the runtime's assumption (d2, `CloneAssume`, on branch `opus/clone-handoff` only), not this
//! pass's. What stands here is the shape the program can break: a gate
//! handing no register, a path returning into the caller frame, a path
//! falling past its end, a path with no gate behind it.
//!
//! BINDING CONSTRAINT (Simon): no OS data enters this file -- no clone
//! number, no flag, no errno. The register FILE (`REGISTER` below) is the
//! pre-existing machine vocabulary `syscall.rs` holds too (its twin, named
//! here on purpose: the syntax crate takes no checker dependency question,
//! and this pass reads no checker map but its own walk).

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};
use std::collections::{BTreeSet, HashMap, HashSet};

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
    // **Fix lane F3: the stack gates by short name** -- a faulted gate still counts
    // for `N450` (its own fault names what is broken), exactly as the unit count did.
    let mut stapeltore: HashSet<String> = HashSet::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, _modul| {
        if let ItemArt::Syscall(s) = &item.art {
            stapelklausel(s, absagen);
            if s.stapel.len() == 1 {
                tore_mit_stapel += 1;
                stapeltore.insert(s.name.text.clone());
            }
        }
    });
    // **Lane 249: the spill-read map.** Short gate name to the stack
    // parameter's position in the gate's parameter list -- the slot whose
    // call-site argument travels to the child. A faulted gate (`N446`:
    // the stack register bound nowhere, `N447`: claimed twice) hands
    // nothing soundly and stays out of the map; its own fault names it.
    let mut tore: HashMap<String, usize> = HashMap::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, _modul| {
        if let ItemArt::Syscall(s) = &item.art {
            if s.stapel.len() == 1 {
                let stapel = &s.stapel[0].text;
                if let Some((_, param)) = s.regs_in.iter().find(|(r, _)| r.text == *stapel) {
                    if let Some(stellung) =
                        s.parameter.iter().position(|p| p.name.text == param.text)
                    {
                        tore.insert(s.name.text.clone(), stellung);
                    }
                }
            }
        }
    });
    // **The bodies, second:** a `child` block lives in a function body. The
    // gate count above is unit-wide and gates only the spill rule; `N450` is
    // per region since fix lane F3 (`torpfade`).
    crate::fuer_jedes_item_im_modul(baum, &mut |item, _modul| {
        if let ItemArt::Funktion(f) = &item.art {
            if let FnRumpf::Block(b) = &f.rumpf {
                kindpfade(&f.name.text, b, &divergent, absagen, true);
                // **Fix lane F3 (review G11 F4): `N450` per region.** A gate call
                // must DOMINATE the region -- stand before it on every path --
                // and one call hands to at most one region.
                let mut genommen: HashSet<gabbro_syntax::span::Span> = HashSet::new();
                torpfade(&f.name.text, b, &stapeltore, None, &mut genommen, absagen, true);
                // **Fix lane F3 (review G11 F2): `N456`, the child holds nothing.**
                let mut sig: Vec<String> = Vec::new();
                for p in &f.requires {
                    let mut h = Vec::new();
                    crate::aufrufgraph::held_aus_pred(p, &mut h);
                    for (n, _) in h {
                        if !sig.contains(&n) {
                            sig.push(n);
                        }
                    }
                }
                let start = if sig.is_empty() {
                    None
                } else {
                    Some(format!("`requires Held({})` of `{}`", sig.join(", "), f.name.text))
                };
                kontextpfade(&f.name.text, b, start.as_deref(), absagen);
                // **Lane 249: the spill reads (round 2: prefix-handed).**
                // Caller scope against the handed slots, per enclosing
                // function -- a gate call in one function hands nothing to
                // the child of another, and a gate call AFTER the region
                // hands nothing to it either: only calls preceding the
                // region in program order travel (`spill_block` carries
                // the prefix set down).
                if tore_mit_stapel > 0 {
                    let mut kontext = RuferKontext {
                        lets: HashSet::new(),
                        umfang: HashSet::new(),
                    };
                    for p in &f.parameter {
                        kontext.umfang.insert(p.name.text.clone());
                    }
                    sammel_anrufer(b, &mut kontext.lets, &mut kontext.umfang);
                    spill_block(
                        &f.name.text,
                        b,
                        &kontext,
                        &tore,
                        &HashSet::new(),
                        absagen,
                        true,
                    );
                }
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
    absagen: &mut Absagen,
    aussen: bool,
) {
    for s in &b.anweisungen {
        if let StmtArt::Child(region) = &s.art {
            if aussen {
                kindregion(fname, region, divergent, absagen);
            }
            // Nested regions walk for deeper nesting, but refuse nothing
            // twice: the outer region already covers them.
            kindpfade(fname, region, divergent, absagen, false);
        } else {
            for k in crate::unterbloecke(s) {
                kindpfade(fname, k, divergent, absagen, aussen);
            }
        }
    }
}

/// Whether this statement ITSELF calls a stack gate -- its own call, its own
/// expressions; never its sub-blocks (a call inside a branch does not stand
/// before a region after the branch on every path). A call this walk misses
/// only makes `N450` stricter: the fail-safe side.
fn ruft_stapeltor(s: &Stmt, tore: &HashSet<String>) -> bool {
    let trifft = |r: &Ruf| {
        r.path()
            .and_then(|p| p.teile.last())
            .is_some_and(|n| tore.contains(&n.text))
    };
    let in_expr = |e: &Expr| {
        crate::alle_ausdruecke(e).into_iter().any(|x| match &x.art {
            ExprArt::Ruf(r) => trifft(r),
            _ => false,
        })
    };
    match &s.art {
        StmtArt::Ruf(r) => trifft(r) || r.argumente.iter().any(in_expr),
        StmtArt::LetSonst(l) => match &l.quelle {
            LetQuelle::Ruf(r) => trifft(r) || r.argumente.iter().any(in_expr),
            LetQuelle::Ort(_) => false,
        },
        // The region hands nothing to itself.
        StmtArt::Child(_) => false,
        _ => crate::eigene_ausdruecke(s).into_iter().any(in_expr),
    }
}

/// Whether a `child` block stands anywhere under this statement.
fn enthaelt_kind(s: &Stmt) -> bool {
    matches!(&s.art, StmtArt::Child(_))
        || crate::unterbloecke(s)
            .into_iter()
            .any(|k| k.anweisungen.iter().any(enthaelt_kind))
}

/// **`N450` -- a stack-gate call dominates the region** (fix lane F3, review G11 F4).
///
/// `offen`: the stack-gate call (by its statement span) that stands before this point
/// on every path. The walk is structured dominance: a statement's own call opens the
/// gate for everything after it in the block and for its sub-blocks (the call is
/// evaluated first); a call inside a sub-block opens nothing outside it (each
/// sub-block walks its own copy). **One call hands to ONE region, statically**
/// (`genommen`): under the "child entered by jump" lowering the call has one jump
/// target, so a second region behind the same call falls -- in sequence (the parent
/// runs past the first region: the child never falls through, `N449`) and in a
/// sibling branch alike. Any statement with a region below it closes the call for
/// what follows. A gate call inside a region hands nothing outside it.
fn torpfade(
    fname: &str,
    b: &Block,
    tore: &HashSet<String>,
    vorher: Option<gabbro_syntax::span::Span>,
    genommen: &mut HashSet<gabbro_syntax::span::Span>,
    absagen: &mut Absagen,
    aussen: bool,
) {
    let mut offen = vorher;
    for s in &b.anweisungen {
        if let StmtArt::Child(region) = &s.art {
            let getragen = match offen {
                Some(ruf) => genommen.insert(ruf),
                None => false,
            };
            // **The one issuance site of this rule.**
            if aussen && !getragen {
                absagen.schiebe(
                    Absage::fehler(
                        "N450",
                        region.span,
                        if tore.is_empty() {
                            format!("`{fname}` runs a `child` path with no `stack` gate in the unit")
                        } else {
                            format!(
                                "`{fname}` runs a `child` path that no `stack`-gate call \
                                 dominates -- no call stands before it on every path, or \
                                 another region already took that call"
                            )
                        },
                    )
                    .mit_notiz(
                        "a `child` block runs on the handed stack of a `syscall … stack r` \
                         gate CALL -- that call must stand before the region on every path \
                         (in the same block or an enclosing one, not in a branch beside it \
                         and not in another function), and one call hands to one region \
                         (a faulted gate still counts here: its own fault names what is \
                         broken about it)",
                    ),
                );
            }
            // Nested regions are part of the outer one, as under `N448`/`N449`.
            torpfade(fname, region, tore, None, genommen, absagen, false);
            offen = None;
            continue;
        }
        if ruft_stapeltor(s, tore) {
            offen = Some(s.span);
        }
        for k in crate::unterbloecke(s) {
            torpfade(fname, k, tore, offen, genommen, absagen, aussen);
        }
        if enthaelt_kind(s) {
            offen = None;
        }
    }
}

/// **`N456` -- the child holds nothing the parent holds** (fix lane F3, review G11 F2).
///
/// The child runs BESIDE the parent from its first statement: it holds no lock the parent
/// holds, stands in no RCU read section the parent stands in, and inherits no invariant
/// the parent's `breaking` suspended. Every held-set walker of the checker (`H007`,
/// `H020`, `H001`/`H006` chains, `N291`, `H009`/`H010`, `H018`, the hold-time costs)
/// carries the enclosing `locks`/`observes`/`breaking` stack and the signature-held
/// locks down through `crate::unterbloecke` -- into the child, where they are false. This
/// rule makes that inherited stack EMPTY in every accepted program: a `child` inside a
/// `locks`, `observes` or `breaking` block, or in a function that holds a lock by
/// signature (`requires Held(L)`), falls. The function-level `effects { locks L }` line is
/// no holding context (the body takes the lock), and the walkers that read it as held
/// reset it at the `Child` arm themselves (`geteilt.rs`, `fusswache2.rs`).
fn kontextpfade(fname: &str, b: &Block, kontext: Option<&str>, absagen: &mut Absagen) {
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Child(region) => {
                // **The one issuance site of this rule.**
                if let Some(k) = kontext {
                    absagen.schiebe(
                        Absage::fehler(
                            "N456",
                            region.span,
                            format!(
                                "`{fname}` starts a `child` path inside {k} -- the child \
                                 runs beside the parent and holds none of it"
                            ),
                        )
                        .mit_notiz(
                            "the child is its own thread from its first statement: a lock \
                             the parent holds, an `observes` section it stands in or an \
                             invariant its `breaking` suspends is the PARENT's -- start \
                             the child outside them, and take what the child needs inside \
                             the child (`child { locks L { … } … }`)",
                        ),
                    );
                }
                // The child's own context starts empty.
                kontextpfade(fname, region, None, absagen);
            }
            StmtArt::Sperrt(l) => {
                let k = format!("`locks {}`", l.sperre.text());
                kontextpfade(fname, &l.rumpf, Some(&k), absagen);
            }
            StmtArt::Observiert(o) => {
                let k = format!("`observes {}`", o.domaene.text);
                kontextpfade(fname, &o.rumpf, Some(&k), absagen);
            }
            StmtArt::Bricht(x) => {
                let namen: Vec<String> = x.invarianten.iter().map(|i| i.text.clone()).collect();
                let k = format!("`breaking {}`", namen.join(", "));
                kontextpfade(fname, &x.rumpf, Some(&k), absagen);
            }
            _ => {
                for k in crate::unterbloecke(s) {
                    kontextpfade(fname, k, kontext, absagen);
                }
            }
        }
    }
}

/// **`N448`/`N449` -- one child region** (`N450` is `torpfade`'s since fix lane F3).
///
/// `N448`: no `return` in the region, no `leave`/`next`
/// past it. `N449`: with no `return` inside, the region never falls
/// through -- `endet_immer` over the unit's never-returning callees.
fn kindregion(fname: &str, region: &Block, divergent: &[String], absagen: &mut Absagen) {
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

/// **`N451`/`N452` -- the spill-read rule (lane 249).**
///
/// The child runs on the handed stack, not in the caller frame: a caller
/// name the gate never handed dies at the gate, and the child reading it
/// reads a dead slot. The rule is a dataflow over the shared read set
/// (`crate::emit::benutzte_namen`, the same walker the `(void)k;`
/// decision trusts) against the caller scope -- not a second effects
/// system:
///
/// * `lets` (`N451`): every `let`-family name bound in the enclosing
///   function body outside any `child` region -- `let`, `let … else`
///   (value and error name), `alloc`, `awaits`, `exchange`. The gate
///   answer (`let v = gate(…) else …`) is one of them: the return slot.
/// * `umfang` (`N452`): the function parameters plus the `traverse`
///   variable and `match` binders bound outside any region.
/// * the prefix set: the caller slots handed across -- the bare-place
///   call argument at the stack parameter's position of every
///   stack-gate call PRECEDING the region in program order (round 2:
///   a call after the region hands nothing to it -- the child already
///   runs). A computed argument hands nothing; neither does a call
///   inside a region (the child hands nothing to itself).
///
/// Legal in the region: the handed slots, and every name that is no
/// caller local at all (globals, tables, statics, callees). A
/// region-local sharing a caller name stays refused (round 2, option
/// (a)): the read set is positional-blind, so the pre-definition read
/// -- which resolves to the caller slot, a dead slot -- is the fault,
/// and the benign shadow pays the same refusal. Soundness first.
/// One refusal per offending name per outermost region, at the region
/// span, naming the variable. Nested regions are part of their outer
/// region here as under `N448`/`N449`.
///
/// What this does NOT do, by decision: with no stack-carrying gate in
/// the unit (`N450` already fell) handedness is moot and nothing fires
/// here. A faulted gate hands nothing (its own fault names it), so a
/// region behind only a faulted gate reports its reads on top. Gate
/// resolution is by short name, like the `endet_immer` list beside
/// which this map stands. A loop-back-edge call hands nothing either:
/// the prefix is textual, and the first pass through the region runs
/// before any later call.
struct RuferKontext {
    lets: HashSet<String>,
    umfang: HashSet<String>,
}

/// Caller bindings outside any `child` region: a nested `child` binds
/// the handed stack's locals, never the caller's.
fn sammel_anrufer(b: &Block, lets: &mut HashSet<String>, umfang: &mut HashSet<String>) {
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Let(l) => {
                lets.insert(l.name.text.clone());
            }
            StmtArt::LetSonst(l) => {
                lets.insert(l.name.text.clone());
                lets.insert(l.fehlername.text.clone());
            }
            StmtArt::Alloc(a) => {
                lets.insert(a.name.text.clone());
            }
            StmtArt::AwaitLoad(a) => {
                lets.insert(a.name.text.clone());
            }
            StmtArt::Exchange(e) => {
                lets.insert(e.name.text.clone());
            }
            StmtArt::Schleife(sch) => {
                if let Schleife::Traverse(t) = sch.as_ref() {
                    umfang.insert(t.variable.text.clone());
                }
            }
            StmtArt::Match(m) => {
                for z in &m.zweige {
                    if let Some(binder) = &z.binder {
                        umfang.insert(binder.text.clone());
                    }
                }
            }
            // **The region binds its own locals.** Nothing inside is a
            // caller slot, so the walk stops here -- like `kindpfade`
            // refusing only the outer region, from the other side.
            StmtArt::Child(_) => continue,
            _ => {}
        }
        for k in crate::unterbloecke(s) {
            sammel_anrufer(k, lets, umfang);
        }
    }
}

/// One statement's handoff: its own calls hand the slots for every
/// region after it in the block. Subblocks are NOT walked here -- the
/// block walk (`spill_block`) descends into them with the prefix so far,
/// and their contributions never leak into sibling branches.
fn sammel_stmt_uebergeben(s: &Stmt, tore: &HashMap<String, usize>, laufend: &mut HashSet<String>) {
    match &s.art {
        StmtArt::Ruf(r) => {
            ruf_uebergabe(r, tore, laufend);
            for a in &r.argumente {
                expr_uebergabe(a, tore, laufend);
            }
        }
        StmtArt::LetSonst(l) => {
            if let LetQuelle::Ruf(r) = &l.quelle {
                ruf_uebergabe(r, tore, laufend);
                for a in &r.argumente {
                    expr_uebergabe(a, tore, laufend);
                }
            }
        }
        // **The region hands nothing to itself** -- and neither does a
        // call inside it to anything after it.
        StmtArt::Child(_) => {}
        _ => {
            for e in crate::eigene_ausdruecke(s) {
                expr_uebergabe(e, tore, laufend);
            }
        }
    }
}

/// One call site: where the stack argument is a bare caller place, that
/// slot travels. Every other shape -- a computed argument, an unknown
/// callee, a missing position -- hands nothing: the fail-safe side.
fn ruf_uebergabe(r: &Ruf, tore: &HashMap<String, usize>, uebergeben: &mut HashSet<String>) {
    let CallTarget::Path(pfad) = &r.ziel else {
        return;
    };
    let Some(letztes) = pfad.teile.last() else {
        return;
    };
    let Some(stellung) = tore.get(&letztes.text) else {
        return;
    };
    let Some(arg) = r.argumente.get(*stellung) else {
        return;
    };
    let mut bloecke = arg;
    while let ExprArt::Klammer(innen) = &bloecke.art {
        bloecke = innen;
    }
    if let ExprArt::Ort(o) = &bloecke.art {
        if o.suffixe.is_empty() {
            uebergeben.insert(o.basis.text.clone());
        }
    }
}

/// Gate calls nested in value position (`let x = f(gate(…))`, an index
/// carrying one): the same handoff, one level down. Predicates
/// (`Zaehle`) are not executed state and carry none.
fn expr_uebergabe(x: &Expr, tore: &HashMap<String, usize>, uebergeben: &mut HashSet<String>) {
    match &x.art {
        ExprArt::Ruf(r) => {
            ruf_uebergabe(r, tore, uebergeben);
            for a in &r.argumente {
                expr_uebergabe(a, tore, uebergeben);
            }
        }
        ExprArt::LibraryCall(r) => {
            for a in &r.args {
                expr_uebergabe(a, tore, uebergeben);
            }
        }
        ExprArt::Klammer(y) | ExprArt::Unaer(_, y) => expr_uebergabe(y, tore, uebergeben),
        ExprArt::Binaer(_, a, b) => {
            expr_uebergabe(a, tore, uebergeben);
            expr_uebergabe(b, tore, uebergeben);
        }
        ExprArt::ArrayLit(es) => {
            for e in es {
                expr_uebergabe(e, tore, uebergeben);
            }
        }
        ExprArt::Eingebaut(e) => match e.as_ref() {
            Eingebaut::Sizeof(TypOderOrt::Ort(o)) | Eingebaut::Lenof(TypOderOrt::Ort(o)) => {
                ort_uebergabe(o, tore, uebergeben);
            }
            Eingebaut::Aligned(a, b) => {
                expr_uebergabe(a, tore, uebergeben);
                expr_uebergabe(b, tore, uebergeben);
            }
            _ => {}
        },
        ExprArt::Ort(o) | ExprArt::Alt(o) => ort_uebergabe(o, tore, uebergeben),
        ExprArt::Zahl(_)
        | ExprArt::Gleitkomma { .. }
        | ExprArt::Wahr
        | ExprArt::Falsch
        // **Lane 261:** a string literal hands nothing -- bytes name no gate.
        | ExprArt::Kette(_)
        | ExprArt::FnWert(_)
        | ExprArt::Grund { .. }
        | ExprArt::Ergebnis
        | ExprArt::Zaehle { .. } => {}
    }
}

/// A call hiding in an index suffix hands like any nested call.
fn ort_uebergabe(o: &Ort, tore: &HashMap<String, usize>, uebergeben: &mut HashSet<String>) {
    for s in &o.suffixe {
        if let OrtSuffix::Index(x) = s {
            expr_uebergabe(x, tore, uebergeben);
        }
    }
}

/// The outermost `child` blocks of a body, for the spill reads -- the
/// same regions `kindpfade` refuses, walked beside it, carrying the
/// handed prefix down: each statement's calls join the set every later
/// region reads, and each subblock is walked with its own clone -- a
/// call in one branch hands nothing to a region in its sibling.
fn spill_block(
    fname: &str,
    b: &Block,
    kontext: &RuferKontext,
    tore: &HashMap<String, usize>,
    vorher: &HashSet<String>,
    absagen: &mut Absagen,
    aussen: bool,
) {
    let mut laufend = vorher.clone();
    for s in &b.anweisungen {
        if let StmtArt::Child(region) = &s.art {
            if aussen {
                spillregion(fname, region, kontext, &laufend, absagen);
            }
            spill_block(fname, region, kontext, tore, &laufend, absagen, false);
        } else {
            sammel_stmt_uebergeben(s, tore, &mut laufend);
            for k in crate::unterbloecke(s) {
                spill_block(fname, k, kontext, tore, &laufend, absagen, aussen);
            }
        }
    }
}

/// **`N451`/`N452` -- one child region against its caller.**
///
/// `N451`: a read of a caller `let`-temporary outside the handed
/// prefix. `N452`: a read of a caller parameter (or loop/match binder)
/// outside it. The handed prefix is checked first; a name in both
/// caller sets reports as the temporary. Region binds are NOT counted
/// off (round 2, option (a)): the shared read set cannot tell the
/// pre-definition read (caller slot, dead) from the benign shadow, so
/// both refuse -- soundness first. The read set is `kindzugriff`
/// (exhaustive over `StmtArt`) -- a write target counts as a mention, because a
/// write to a dead slot is the same fault from the other side.
fn spillregion(
    fname: &str,
    region: &Block,
    kontext: &RuferKontext,
    uebergeben: &HashSet<String>,
    absagen: &mut Absagen,
) {
    // **Fix lane F3 (review G11 F3): the exhaustive walk**, not the emission walker --
    // `grow … else { … }` and lock-place indices are read here too.
    let gelesen: BTreeSet<String> = kindzugriff(region).namen;
    // **Sorted by construction** (`BTreeSet`): the refusal order is the
    // name order, and two runs refuse in the same order.
    for n in &gelesen {
        if uebergeben.contains(n) {
            continue;
        }
        if kontext.lets.contains(n) {
            absagen.schiebe(
                Absage::fehler(
                    "N451",
                    region.span,
                    format!(
                        "`{fname}` reads `{n}` on its `child` path -- `{n}` is a caller \
                         temporary that dies at the gate"
                    ),
                )
                .mit_notiz(
                    "the child runs on the handed stack, not in the caller frame: only \
                     the slot handed at a preceding `stack`-gate call site travels (the \
                     bare-place argument at the stack parameter), every other caller \
                     `let` -- the gate answer with it -- stays behind",
                ),
            );
        } else if kontext.umfang.contains(n) {
            absagen.schiebe(
                Absage::fehler(
                    "N452",
                    region.span,
                    format!(
                        "`{fname}` reads `{n}` on its `child` path -- `{n}` is a caller \
                         parameter the gate never handed"
                    ),
                )
                .mit_notiz(
                    "the child runs on the handed stack, not in the caller frame: only \
                     the slot handed at a preceding `stack`-gate call site travels (the \
                     bare-place argument at the stack parameter) -- a parameter beside \
                     it, and a loop or match binder beside that, stays behind",
                ),
            );
        }
    }
}

/// **What a `child` path touches -- the exhaustive walk (fix lane F3, review G11 F3).**
///
/// Until 2026-09-21 the spill rule read `emit::benutzte_namen`, the `(void)k;` walker.
/// That walker answers an EMISSION question and skips on purpose what the emitter does
/// not lower: `grow` (a caller `let` read in `grow … else { … }` escaped `N451`), the
/// lock place of a `locks` block (a caller `let` as a lock index escaped too), `old`,
/// `sizeof`/`lenof`. The child path asks a different question -- *which names does this
/// path mention at run time or could* -- and the answer must over-approximate. This walk
/// matches every `StmtArt` by name (no `_` arm), so a new statement kind is a compile
/// error here, not a silent hole; expressions go through `crate::alle_ausdruecke`, which
/// descends into every index, argument and element.
///
/// Mentioned names: every place root (reads and write targets alike, index roots
/// included), every call target (a path's last segment, an indirect call's place), every
/// `&f`, every arena, lock place, RCU domain and `start` root named. Ghost clauses
/// (`invariant`, loop `touches` effects) are NOT walked: they are never executed.
/// The calls are collected beside the names so the race rule (`fusswache2`, `N457`) can
/// close the child's call graph; `indirekt` records an indirect call anywhere on the path.
pub(crate) struct Kindzugriff {
    pub namen: BTreeSet<String>,
    pub rufe: Vec<String>,
    pub indirekt: bool,
}

pub(crate) fn kindzugriff(b: &Block) -> Kindzugriff {
    let mut z = Kindzugriff {
        namen: BTreeSet::new(),
        rufe: Vec::new(),
        indirekt: false,
    };
    zugriff_block(b, &mut z);
    z
}

fn zugriff_block(b: &Block, z: &mut Kindzugriff) {
    for s in &b.anweisungen {
        zugriff_stmt(s, z);
    }
}

fn zugriff_ruf(r: &Ruf, z: &mut Kindzugriff) {
    match &r.ziel {
        CallTarget::Path(p) => {
            if !crate::ist_praedikatswort(r) {
                z.rufe.push(p.text());
            }
            if let Some(letztes) = p.teile.last() {
                z.namen.insert(letztes.text.clone());
            }
        }
        CallTarget::Place(o) => {
            z.indirekt = true;
            zugriff_ort(o, z);
        }
    }
    for a in &r.argumente {
        zugriff_expr(a, z);
    }
}

fn zugriff_ort(o: &Ort, z: &mut Kindzugriff) {
    z.namen.insert(o.basis.text.clone());
    for i in crate::ausdruecke_im_ort(o) {
        zugriff_expr(i, z);
    }
}

fn zugriff_pred(p: &Pred, z: &mut Kindzugriff) {
    for e in crate::ausdruecke_im_praedikat(p) {
        zugriff_expr(e, z);
    }
}

fn zugriff_expr(e: &Expr, z: &mut Kindzugriff) {
    for x in crate::alle_ausdruecke(e) {
        match &x.art {
            ExprArt::Ort(o) | ExprArt::Alt(o) => {
                z.namen.insert(o.basis.text.clone());
            }
            // The arguments arrive through `alle_ausdruecke`; the target does not.
            ExprArt::Ruf(r) => match &r.ziel {
                CallTarget::Path(p) => {
                    if !crate::ist_praedikatswort(r) {
                        z.rufe.push(p.text());
                    }
                    if let Some(letztes) = p.teile.last() {
                        z.namen.insert(letztes.text.clone());
                    }
                }
                CallTarget::Place(o) => {
                    z.indirekt = true;
                    zugriff_ort(o, z);
                }
            },
            ExprArt::FnWert(p) => {
                z.namen.insert(p.text());
                if let Some(letztes) = p.teile.last() {
                    z.namen.insert(letztes.text.clone());
                }
            }
            ExprArt::Eingebaut(g) => {
                if let Eingebaut::Sizeof(TypOderOrt::Ort(o)) | Eingebaut::Lenof(TypOderOrt::Ort(o)) =
                    &**g
                {
                    z.namen.insert(o.basis.text.clone());
                }
            }
            ExprArt::Zaehle { domaene, .. } => zugriff_domaene(domaene, z),
            // Sub-expressions arrive through `alle_ausdruecke`; these name nothing.
            // **Lane 261:** a string literal names nothing either.
            ExprArt::LibraryCall(_)
            | ExprArt::Klammer(_)
            | ExprArt::Unaer(_, _)
            | ExprArt::Binaer(_, _, _)
            | ExprArt::ArrayLit(_)
            | ExprArt::Kette(_)
            | ExprArt::Zahl(_)
            | ExprArt::Gleitkomma { .. }
            | ExprArt::Wahr
            | ExprArt::Falsch
            | ExprArt::Grund { .. }
            | ExprArt::Ergebnis => {}
        }
    }
}

fn zugriff_domaene(d: &Domaene, z: &mut Kindzugriff) {
    match d {
        Domaene::SlotsVon(o)
        | Domaene::NachfahrenVon(o)
        | Domaene::VorfahrenVon(o)
        | Domaene::Schlange(o)
        | Domaene::ElementeVon(o)
        | Domaene::AbbildungenVon(o) => zugriff_ort(o, z),
        Domaene::KetteIn { a, b, ort } => {
            z.namen.insert(a.text.clone());
            z.namen.insert(b.text.clone());
            zugriff_ort(ort, z);
        }
        Domaene::FelderVon(p) => {
            z.namen.insert(p.text());
        }
        Domaene::Threads => {}
    }
}

fn zugriff_nutzlast(n: &Nutzlast, z: &mut Kindzugriff) {
    match n {
        Nutzlast::Orte(orte) => {
            for o in orte {
                zugriff_ort(o, z);
            }
        }
        Nutzlast::Nichts(_) => {}
    }
}

fn zugriff_stmt(s: &Stmt, z: &mut Kindzugriff) {
    match &s.art {
        StmtArt::Let(l) => zugriff_expr(&l.wert, z),
        StmtArt::LetSonst(l) => {
            match &l.quelle {
                LetQuelle::Ruf(r) => zugriff_ruf(r, z),
                LetQuelle::Ort(o) => zugriff_ort(o, z),
            }
            zugriff_block(&l.sonst, z);
        }
        StmtArt::Zuweisung(x) => {
            zugriff_ort(&x.ziel, z);
            zugriff_expr(&x.wert, z);
        }
        StmtArt::Wenn(w) => {
            for (bed, rumpf) in &w.zweige {
                zugriff_expr(bed, z);
                zugriff_block(rumpf, z);
            }
            if let Some(sonst) = &w.sonst {
                zugriff_block(sonst, z);
            }
        }
        StmtArt::Match(m) => {
            zugriff_expr(&m.gegenstand, z);
            for zw in &m.zweige {
                zugriff_block(&zw.rumpf, z);
            }
        }
        StmtArt::Schleife(sch) => match sch.as_ref() {
            Schleife::Traverse(t) => {
                zugriff_domaene(&t.domaene, z);
                if let Some(g) = &t.gegenstand {
                    zugriff_expr(g, z);
                }
                if let Some(m) = &t.mass {
                    zugriff_expr(m, z);
                }
                zugriff_block(&t.rumpf, z);
            }
            Schleife::Retry(r) => {
                if let Some(bis) = &r.bis {
                    zugriff_pred(bis, z);
                }
                zugriff_expr(&r.schranke, z);
                zugriff_block(&r.rumpf, z);
            }
            Schleife::Forever(f) => {
                zugriff_expr(&f.je_durchgang, z);
                zugriff_block(&f.rumpf, z);
            }
        },
        StmtArt::Bricht(x) => zugriff_block(&x.rumpf, z),
        StmtArt::Narrow(x) => {
            zugriff_ort(&x.ort, z);
            if let NarrowZiel::Bereich(b) = &x.ziel {
                zugriff_expr(&b.von, z);
                zugriff_expr(&b.bis, z);
            }
            zugriff_block(&x.sonst, z);
        }
        // **The lock place is read** -- `locks L[i] { … }` evaluates `i` (review G11 F3).
        StmtArt::Sperrt(x) => {
            zugriff_ort(&x.sperre, z);
            zugriff_block(&x.rumpf, z);
        }
        StmtArt::Observiert(x) => {
            z.namen.insert(x.domaene.text.clone());
            zugriff_block(&x.rumpf, z);
        }
        StmtArt::Leave(_) | StmtArt::Next(_) => {}
        StmtArt::Publish(p) => {
            zugriff_ort(&p.ziel, z);
            zugriff_expr(&p.wert, z);
            zugriff_nutzlast(&p.nutzlast, z);
        }
        StmtArt::AwaitLoad(a) => {
            zugriff_ort(&a.quelle, z);
            for o in &a.erwartet {
                zugriff_ort(o, z);
            }
        }
        StmtArt::Exchange(x) => {
            zugriff_ort(&x.ort, z);
            match &x.form {
                XForm::Update { schranke, rumpf, .. } => {
                    if let Some(e) = schranke {
                        zugriff_expr(e, z);
                    }
                    zugriff_block(rumpf, z);
                }
                XForm::Vergleich { wert, bedingung, .. } => {
                    zugriff_expr(wert, z);
                    zugriff_pred(bedingung, z);
                }
            }
            if let Some(n) = &x.nutzlast {
                zugriff_nutzlast(n, z);
            }
            if let Some(orte) = &x.erwartet {
                for o in orte {
                    zugriff_ort(o, z);
                }
            }
        }
        StmtArt::Return(e) => {
            if let Some(e) = e {
                zugriff_expr(e, z);
            }
        }
        StmtArt::Ruf(r) => zugriff_ruf(r, z),
        StmtArt::LibraryCall(r) => {
            for a in &r.args {
                zugriff_expr(a, z);
            }
        }
        StmtArt::Alloc(a) => {
            z.namen.insert(a.tisch.text.clone());
            zugriff_expr(&a.wert, z);
            if let Some(sonst) = &a.sonst {
                zugriff_block(sonst, z);
            }
        }
        StmtArt::ResetArena(t) => {
            z.namen.insert(t.text.clone());
        }
        // **`grow` is walked** -- the amount AND the failure continuation (review G11 F3:
        // the emission walker skips the whole statement).
        StmtArt::Grow(g) => {
            z.namen.insert(g.tisch.text.clone());
            zugriff_expr(&g.mehr, z);
            zugriff_block(&g.sonst, z);
        }
        StmtArt::Child(x) => zugriff_block(x, z),
        StmtArt::Start(st) => {
            for p in &st.roots {
                z.namen.insert(p.text());
                if let Some(letztes) = p.teile.last() {
                    z.namen.insert(letztes.text.clone());
                }
            }
        }
    }
}
