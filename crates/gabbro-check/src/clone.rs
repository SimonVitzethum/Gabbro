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
//! | `N451` | the child path reads no caller `let`-temporary it was not handed (the gate answer, every other caller `let`) | gift 1113 |
//! | `N452` | the child path reads no caller parameter (or loop/match binder) it was not handed | gifts 1115, 1116 |
//! | `C185` | the `child` block has no lowering in the stub template and is refused by name (in `emit.rs`, beside the best-effort block) | gift 1112 |
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
    crate::fuer_jedes_item_im_modul(baum, &mut |item, _modul| {
        if let ItemArt::Syscall(s) = &item.art {
            stapelklausel(s, absagen);
            if s.stapel.len() == 1 {
                tore_mit_stapel += 1;
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
    // **The bodies, second:** a `child` block lives in a function body, and
    // the gate count above is unit-wide -- a path with no gate behind it
    // (`N450`) needs both.
    crate::fuer_jedes_item_im_modul(baum, &mut |item, _modul| {
        if let ItemArt::Funktion(f) = &item.art {
            if let FnRumpf::Block(b) = &f.rumpf {
                kindpfade(&f.name.text, b, &divergent, tore_mit_stapel, absagen, true);
                // **Lane 249: the spill reads.** Caller scope against the
                // handed slots, per enclosing function -- a gate call in one
                // function hands nothing to the child of another.
                if tore_mit_stapel > 0 {
                    let mut kontext = RuferKontext {
                        lets: HashSet::new(),
                        umfang: HashSet::new(),
                        uebergeben: HashSet::new(),
                    };
                    for p in &f.parameter {
                        kontext.umfang.insert(p.name.text.clone());
                    }
                    sammel_anrufer(b, &mut kontext.lets, &mut kontext.umfang);
                    sammel_uebergeben(b, &tore, &mut kontext.uebergeben);
                    spillpfade(&f.name.text, b, &kontext, absagen, true);
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
/// * `uebergeben`: the caller slots handed across -- the bare-place call
///   argument at the stack parameter's position of every stack-gate call
///   in the enclosing body outside any region. A computed argument hands
///   nothing; neither does a call inside a region (the child hands
///   nothing to itself).
///
/// Legal in the region: the handed slots, the names the region binds
/// itself (its own `let`s, counted off before the scope), and every name
/// that is no caller local at all (globals, tables, statics, callees).
/// One refusal per offending name per outermost region, at the region
/// span, naming the variable. Nested regions are part of their outer
/// region here as under `N448`/`N449`.
///
/// What this does NOT do, by decision: with no stack-carrying gate in
/// the unit (`N450` already fell) handedness is moot and nothing fires
/// here. A faulted gate hands nothing (its own fault names it), so a
/// region behind only a faulted gate reports its reads on top. Gate
/// resolution is by short name, like the `endet_immer` list beside
/// which this map stands. Shadowing inside the region is positional and
/// this set is not: a read of a region-local sharing a caller name stays
/// refused and names the caller slot.
struct RuferKontext {
    lets: HashSet<String>,
    umfang: HashSet<String>,
    uebergeben: HashSet<String>,
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

/// The handed caller slots: bare-place arguments at the stack position
/// of stack-gate calls outside any region. Parentheses change nothing
/// and are seen through; anything else computed hands no slot.
fn sammel_uebergeben(b: &Block, tore: &HashMap<String, usize>, uebergeben: &mut HashSet<String>) {
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Ruf(r) => {
                ruf_uebergabe(r, tore, uebergeben);
                for a in &r.argumente {
                    expr_uebergabe(a, tore, uebergeben);
                }
            }
            StmtArt::LetSonst(l) => {
                if let LetQuelle::Ruf(r) = &l.quelle {
                    ruf_uebergabe(r, tore, uebergeben);
                    for a in &r.argumente {
                        expr_uebergabe(a, tore, uebergeben);
                    }
                }
            }
            StmtArt::Child(_) => continue,
            _ => {
                for e in crate::eigene_ausdruecke(s) {
                    expr_uebergabe(e, tore, uebergeben);
                }
            }
        }
        for k in crate::unterbloecke(s) {
            sammel_uebergeben(k, tore, uebergeben);
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
/// same regions `kindpfade` refuses, walked beside it.
fn spillpfade(
    fname: &str,
    b: &Block,
    kontext: &RuferKontext,
    absagen: &mut Absagen,
    aussen: bool,
) {
    for s in &b.anweisungen {
        if let StmtArt::Child(region) = &s.art {
            if aussen {
                spillregion(fname, region, kontext, absagen);
            }
            spillpfade(fname, region, kontext, absagen, false);
        } else {
            for k in crate::unterbloecke(s) {
                spillpfade(fname, k, kontext, absagen, aussen);
            }
        }
    }
}

/// **`N451`/`N452` -- one child region against its caller.**
///
/// `N451`: a read of a caller `let`-temporary outside the handed set.
/// `N452`: a read of a caller parameter (or loop/match binder) outside
/// it. Region-bound names are counted off first; a name in both caller
/// sets reports as the temporary. The read set is the shared
/// `benutzte_namen` -- a write target counts as a mention, because a
/// write to a dead slot is the same fault from the other side.
fn spillregion(fname: &str, region: &Block, kontext: &RuferKontext, absagen: &mut Absagen) {
    let mut gelesen: BTreeSet<String> = BTreeSet::new();
    crate::emit::benutzte_namen(region, &mut gelesen);
    let mut innen_lets: HashSet<String> = HashSet::new();
    let mut innen_umfang: HashSet<String> = HashSet::new();
    sammel_anrufer(region, &mut innen_lets, &mut innen_umfang);
    // **Sorted by construction** (`BTreeSet`): the refusal order is the
    // name order, and two runs refuse in the same order.
    for n in &gelesen {
        if innen_lets.contains(n) || innen_umfang.contains(n) {
            continue;
        }
        if kontext.uebergeben.contains(n) {
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
                     the slot handed at a `stack`-gate call site travels (the bare-place \
                     argument at the stack parameter), every other caller `let` -- the \
                     gate answer with it -- stays behind",
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
                     the slot handed at a `stack`-gate call site travels (the bare-place \
                     argument at the stack parameter) -- a parameter beside it, and a \
                     loop or match binder beside that, stays behind",
                ),
            );
        }
    }
}
