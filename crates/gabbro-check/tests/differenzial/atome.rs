#![allow(non_upper_case_globals)]
//! The catalogue of ATOMS: one per form of the Lean model (`Kern/Syntax/Syntax.lean`:
//! `Expr`, `Stmt`, `Block`, `Endblock`, `Ty`; the lock, atomic, arena, gate and contract
//! components of `Akzeptiert`), each written as Gabbro source text, with the neighbouring
//! UNSAFE variants (`bad`) that must stay refused.
//!
//! An atom is a fragment of a function: its parameters, the effects it needs, its body, the
//! declarations it stands on. `@` inside a name becomes the atom's slot index, so two atoms in
//! one unit never share a local. The assembler (`bau.rs`) builds units out of one atom
//! (`One`, `Pool`) or two (`Seq`, `Par`, `Call`) under the guard modes of `Mode`.
//!
//! **The designer's belief `sicher` is not a verdict.** It says whether the atom is meant to
//! be a safe program; the Lean model decides, and the harness reports every atom whose
//! belief and the model's verdict part.

/// Which carrier an atom touches that a lock may guard (`Mode` decides how it is guarded).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Wache {
    /// Touches no guardable carrier.
    Keine,
    /// The table `T`.
    T,
    /// The static `s`.
    S,
}

#[derive(Clone, Copy, Debug)]
pub struct Atom {
    pub id: &'static str,
    /// The Lean family and constructors the atom mirrors.
    pub lean: &'static str,
    /// Top-level declaration lines the atom stands on (deduplicated across atoms).
    pub decls: &'static [&'static str],
    /// Extra function items (callees); deduplicated.
    pub items: &'static [&'static str],
    /// Parameter list, comma separated, `@` replaced by the slot.
    pub params: &'static str,
    /// Effect items, e.g. `reads T.slots`.
    pub eff: &'static [&'static str],
    /// Result type text (` -> u32 in 0 .. 9`) when the body ends in a `return`.
    pub ret: &'static str,
    pub body: &'static str,
    pub wache: Wache,
    /// The designer's belief: a safe program.
    pub sicher: bool,
    /// Extra clause text after the contract (`decreases n`).
    pub klausel: &'static str,
    /// Extra `requires` text (without the word), joined with `Held(L)` where the mode asks.
    pub req: &'static str,
    /// The function carries no `costs` clause (a `forever` body has no total cost).
    pub ohne_kosten: bool,
}

pub const A: Atom = Atom {
    id: "",
    lean: "",
    decls: &[],
    items: &[],
    params: "",
    eff: &[],
    ret: "",
    body: "",
    wache: Wache::Keine,
    sicher: true,
    klausel: "",
    req: "",
    ohne_kosten: false,
};

const T: &str = "table T count 4 { slot { v : u32 in 0 .. 100, w : u32 in 0 .. 100, } }";
const U: &str = "table U count 4 { slot { v : u32 in 0 .. 100, } }";
const S: &str = "static mut s : u32 in 0 .. 100 = 7;";
const NTN: &str = "table N count 4 { slot { v : u32 in 0 .. 100, n : option index into N, } }";
const LA: &str = "lock LA protects { U } rank 0 held <= 100 ops;";
const PQ: &str = "table P count 2 { slot { x : u32 in 0 .. 100, } }\ntable Q count 2 { slot { y : u32 in 0 .. 100, } }";
const LK: &str = "lock K protects { P, Q } rank 0 held <= 50 ops invariant P.slots[0].x + Q.slots[0].y == 100;";
const LB: &str = "table V count 4 { slot { v : u32 in 0 .. 100, } }\nlock LB protects { V } rank 1 held <= 100 ops;";
const CALLEE_PURE: &str = "impl fn h(x : u32 in 0 .. 9) -> u32 in 0 .. 9 effects { pure } costs <= 4 ops { return x; }";
const CALLEE_UNIT: &str = "impl fn hv() effects { pure } costs <= 4 ops { return; }";
const REASON: &str = "reason G { Weg = 1 \"weg\" exhaustive }";
const REASON_FN: &str = "impl fn hr(x : u32 in 0 .. 9) -> u32 in 0 .. 9 or G effects { pure } costs <= 4 ops {\n    if x == 0 { return G::Weg; }\n    return x;\n}";
const EXTERN_NIE: &str = "extern fn zeit() -> never effects { diverges } costs <= 1 ops;";
const GATE: &str = "assume linux_getpid \"getpid answers a pid\" falsifier sonde_getpid;\nsyscall getpid() -> u64 in 1 .. 4194304\n    abi linux arch x86_64 number 39\n    regs in { }\n    regs out { rax }\n    clobbers { rcx, r11 }\n    errors { }\n    effects { pure }\n    costs <= 8 ops\n    assume linux_getpid falsifier sonde_getpid;";

pub fn katalog() -> Vec<Atom> {
    let mut v: Vec<Atom> = Vec::new();
    // ---------------------------------------------------------------- expressions (Expr)
    let zwei = "a@ : i32 in -100 .. 100, b@ : i32 in -100 .. 100";
    let pos = "a@ : u32 in 0 .. 100, b@ : u32 in 1 .. 50";
    let null = "a@ : u32 in 0 .. 100, b@ : u32 in 0 .. 50";
    let bits = "a@ : u32 in 0 .. 100, b@ : u32 in 0 .. 7";
    let bits_weit = "a@ : u32 in 0 .. 100, b@ : u32 in 0 .. 40";
    v.extend([
        Atom { id: "e.add", lean: "Expr.add", params: zwei, body: "let r@ : i32 in -200 .. 200 = a@ + b@;", ..A },
        Atom { id: "e.add.bad", lean: "Expr.add", params: zwei, body: "let r@ : i32 in -150 .. 150 = a@ + b@;", sicher: false, ..A },
        Atom { id: "e.sub", lean: "Expr.sub", params: zwei, body: "let r@ : i32 in -200 .. 200 = a@ - b@;", ..A },
        Atom { id: "e.sub.bad", lean: "Expr.sub", params: zwei, body: "let r@ : i32 in -100 .. 100 = a@ - b@;", sicher: false, ..A },
        Atom { id: "e.mul", lean: "Expr.mul", params: zwei, body: "let r@ : i32 in -10000 .. 10000 = a@ * b@;", ..A },
        Atom { id: "e.mul.bad", lean: "Expr.mul", params: zwei, body: "let r@ : i32 in -5000 .. 5000 = a@ * b@;", sicher: false, ..A },
        Atom { id: "e.neg", lean: "Expr.neg", params: "a@ : i32 in -100 .. 100", body: "let r@ : i32 in -100 .. 100 = -a@;", ..A },
        Atom { id: "e.neg.bad", lean: "Expr.neg", params: "a@ : i32 in -100 .. 100", body: "let r@ : i32 in 0 .. 100 = -a@;", sicher: false, ..A },
        Atom { id: "e.div", lean: "Expr.div", params: pos, body: "let r@ : u32 in 0 .. 100 = a@ / b@;", ..A },
        Atom { id: "e.div.zero", lean: "Expr.div", params: null, body: "let r@ : u32 in 0 .. 100 = a@ / b@;", sicher: false, ..A },
        Atom { id: "e.rem", lean: "Expr.rem", params: pos, body: "let r@ : u32 in 0 .. 49 = a@ % b@;", ..A },
        Atom { id: "e.rem.zero", lean: "Expr.rem", params: null, body: "let r@ : u32 in 0 .. 49 = a@ % b@;", sicher: false, ..A },
        Atom { id: "e.sdiv", lean: "Expr.sdiv", params: "a@ : i32 in -100 .. 100, b@ : i32 in 1 .. 50", body: "let r@ : i32 in -100 .. 100 = a@ / b@;", ..A },
        Atom { id: "e.sdiv.zero", lean: "Expr.sdiv", params: "a@ : i32 in -100 .. 100, b@ : i32 in -5 .. 50", body: "let r@ : i32 in -100 .. 100 = a@ / b@;", sicher: false, ..A },
        Atom { id: "e.srem", lean: "Expr.srem", params: "a@ : i32 in -100 .. 100, b@ : i32 in 1 .. 50", body: "let r@ : i32 in -50 .. 50 = a@ % b@;", ..A },
        Atom { id: "e.band", lean: "Expr.band", params: bits, body: "let r@ : u32 in 0 .. 127 = a@ & b@;", ..A },
        Atom { id: "e.bor", lean: "Expr.bor", params: bits, body: "let r@ : u32 in 0 .. 127 = a@ | b@;", ..A },
        Atom { id: "e.bxor", lean: "Expr.bxor", params: bits, body: "let r@ : u32 in 0 .. 127 = a@ ^ b@;", ..A },
        Atom { id: "e.shl", lean: "Expr.shl", params: bits, body: "let r@ : u32 in 0 .. 12800 = a@ << b@;", ..A },
        Atom { id: "e.shl.weit", lean: "Expr.shl", params: bits_weit, body: "let r@ : u32 in 0 .. 12800 = a@ << b@;", sicher: false, ..A },
        Atom { id: "e.shr", lean: "Expr.shr", params: bits, body: "let r@ : u32 in 0 .. 100 = a@ >> b@;", ..A },
        Atom { id: "e.lt", lean: "Expr.lt", params: zwei, body: "let r@ : bool = a@ < b@;", ..A },
        Atom { id: "e.le", lean: "Expr.le", params: zwei, body: "let r@ : bool = a@ <= b@;", ..A },
        Atom { id: "e.eq", lean: "Expr.eq", params: zwei, body: "let r@ : bool = a@ == b@;", ..A },
        Atom { id: "e.andor", lean: "Expr.and/or/not", params: zwei, body: "let r@ : bool = (a@ < b@ && b@ < 5) || !(a@ == 0);", ..A },
        Atom { id: "e.widen", lean: "Expr.widen", params: "a@ : u32", body: "let r@ : u64 = a@;", ..A },
        Atom { id: "e.widen.bad", lean: "Expr.widen", params: "a@ : u64", body: "let r@ : u32 = a@;", sicher: false, ..A },
        Atom { id: "e.lit", lean: "Expr.lit", body: "let r@ : u32 in 0 .. 9 = 7;", ..A },
        Atom { id: "e.lit.bad", lean: "Expr.lit", body: "let r@ : u32 in 0 .. 9 = 70;", sicher: false, ..A },
        Atom { id: "e.bool", lean: "Expr.tru/fls", body: "let r@ : bool = true;\n    let q@ : bool = false;", ..A },
    ]);
    // ------------------------------------------------------------ statements and blocks
    v.extend([
        Atom { id: "s.if", lean: "Stmt.ite", params: "a@ : u32 in 0 .. 100", body: "if a@ < 50 { let r@ : u32 in 0 .. 9 = 1; }", ..A },
        Atom { id: "s.ifelse", lean: "Stmt.ite", params: "a@ : u32 in 0 .. 100", body: "if a@ < 50 { let r@ : u32 in 0 .. 9 = 1; } else if a@ < 70 { let q@ : u32 in 0 .. 9 = 2; } else { let z@ : u32 in 0 .. 9 = 3; }", ..A },
        Atom { id: "s.let.mut", lean: "Stmt.assignVar", body: "let mut x@ : u32 in 0 .. 100 = 3;\n    x@ = 9;", ..A },
        Atom { id: "s.let.mut.bad", lean: "Stmt.assignVar", body: "let mut x@ : u32 in 0 .. 10 = 3;\n    x@ = 90;", sicher: false, ..A },
        Atom { id: "s.narrow", lean: "Block.narrow", params: "a@ : u32 in 0 .. 100", ret: " -> u32 in 0 .. 10", body: "narrow a@ to 0 .. 10 else { return 0; }\n    return a@;", ..A },
        Atom { id: "s.narrow.bad", lean: "Block.narrow", params: "a@ : u32 in 0 .. 100", ret: " -> u32 in 0 .. 10", body: "narrow a@ to 0 .. 50 else { return 0; }\n    return a@;", sicher: false, ..A },
        Atom { id: "s.ret.val", lean: "Endblock.ret", ret: " -> u32 in 0 .. 9", body: "return 4;", ..A },
        Atom { id: "s.ret.bad", lean: "Endblock.ret", ret: " -> u32 in 0 .. 9", body: "return 40;", sicher: false, ..A },
        Atom { id: "s.ret.void", lean: "Endblock.ret", body: "return;", ..A },
        Atom { id: "s.ret.if", lean: "Endblock.ret", params: "a@ : u32 in 0 .. 100", ret: " -> u32 in 0 .. 3", body: "if a@ < 50 { return 1; } else { return 2; }", ..A },
    ]);
    // ---------------------------------------------------------------- loops
    v.extend([
        Atom { id: "l.traverse", lean: "Stmt.traverse", decls: &[T], params: "t@ : ptr<normal, rw> T", eff: &["writes t@.slots"], body: "traverse e@ over slots of t@ by unvisited touches writes t@.slots {\n        t@.slots[e@].v = 3;\n    }", ..A },
        Atom { id: "l.traverse.leave", lean: "Stmt.traverse/leave", decls: &[T], params: "t@ : ptr<normal, r> T", eff: &["reads t@.slots"], body: "traverse e@ over slots of t@ by unvisited touches reads t@.slots {\n        if t@.slots[e@].v == 3 { leave e@; }\n    }", ..A },
        Atom { id: "l.retry", lean: "Stmt.retry", decls: &[T, EXTERN_NIE, "assume ok_ \"the cell changes\" falsifier sonde_ok;"], params: "t@ : ptr<normal, r> T", eff: &["reads t@.slots"], body: "retry warten@ until t@.slots[0].v == 1\n        bounded 8 ops\n        progress ok_\n        on_exceeded zeit\n        effects { reads t@.slots }\n    { }", ..A },
        Atom { id: "l.forever", lean: "Stmt.forever", decls: &[EXTERN_NIE, "extern fn tick() effects { pure } costs <= 1 ops;", "assume tickt \"the timer ticks\" falsifier sonde_tickt;"], eff: &["diverges"], ohne_kosten: true, body: "forever dienst@ per_pass bounded 64 ops on_exceeded zeit effects { pure } progress tickt {\n        tick();\n    }", ..A },
    ]);
    // ---------------------------------------------------------------- calls
    v.extend([
        Atom { id: "c.call", lean: "Stmt.call", items: &[CALLEE_UNIT], body: "hv();", ..A },
        Atom { id: "c.bindcall", lean: "Block.bindCall", items: &[CALLEE_PURE], body: "let y@ = h(4);", ..A },
        Atom { id: "c.bindcall.bad", lean: "Block.bindCall", items: &[CALLEE_PURE], body: "let y@ = h(40);", sicher: false, ..A },
        Atom { id: "c.bindcall.else", lean: "Block.bindCallElse", decls: &[REASON], items: &[REASON_FN], ret: " -> u32 in 0 .. 9 or G", body: "let y@ = hr(4) else (e@) { return e@; }\n    return y@;", ..A },
        Atom { id: "c.reason.ret", lean: "Endblock.retWhy", decls: &[REASON], ret: " -> u32 in 0 .. 9 or G", body: "return G::Weg;", ..A },
        Atom { id: "c.rec", lean: "Stmt.call/recursion", params: "n@ : u32 in 0 .. 5", ret: " -> u32 in 0 .. 5", klausel: "decreases n@", body: "if n@ == 0 { return 0; }\n    return f(n@ - 1);", ..A },
        Atom { id: "c.rec.bad", lean: "Stmt.call/recursion", params: "n@ : u32 in 0 .. 5", ret: " -> u32 in 0 .. 5", body: "if n@ == 0 { return 0; }\n    return f(n@ - 1);", sicher: false, ..A },
        Atom { id: "c.fnptr", lean: "Stmt.callInd/fnref", items: &[CALLEE_PURE], decls: &["type Tr = { f : fn(u32 in 0 .. 9) -> u32 in 0 .. 9 effects { pure } costs <= 4 ops, };"], ret: " -> u32 in 0 .. 9", body: "let t@ : Tr = Tr(f: &h);\n    let y@ = t@.f(3);\n    return y@;", ..A },
        Atom { id: "c.gate", lean: "Stmt.axiomCall/Block.bindAxiom", decls: &[GATE], ret: " -> u64 in 1 .. 4194304", body: "let p@ = getpid();\n    return p@;", ..A },
    ]);
    // ---------------------------------------------------------------- match
    v.extend([
        Atom { id: "m.option", lean: "Stmt.onOption", decls: &[NTN], params: "i@ : index into N", eff: &["reads N.slots"], ret: " -> u32 in 0 .. 100", body: "let o@ : option index into N = N.slots[i@].n;\n    match o@ {\n        Some(k@) => { return N.slots[k@].v; }\n        None => { return 0; }\n    }\n    return 0;", ..A },
        Atom { id: "m.tagged", lean: "Stmt.onTag/Ty.sum", decls: &["tagged type M = { Leer, Kurz(u32 in 0 .. 100) };"], params: "m@ : M", ret: " -> u32 in 0 .. 100", body: "match m@ {\n        Leer => { return 0; }\n        Kurz(k@) => { return k@; }\n    }\n    return 0;", ..A },
        Atom { id: "m.tagged.make", lean: "Expr.case", decls: &["tagged type M = { Leer, Kurz(u32 in 0 .. 100) };"], params: "k@ : bool", ret: " -> M", body: "if k@ { return Kurz(7); }\n    return Leer;", ..A },
        Atom { id: "m.reason", lean: "Stmt.onWhy", decls: &[REASON], items: &[REASON_FN], ret: " -> u32 in 0 .. 9", body: "let y@ = hr(4) else (e@) {\n        match e@ {\n            Weg => { return 0; }\n        }\n        return 0;\n    }\n    return y@;", ..A },
    ]);
    // ---------------------------------------------------------------- tables
    let tr = Wache::T;
    v.extend([
        Atom { id: "t.read", lean: "Expr.slot", decls: &[T], eff: &["reads T.slots"], wache: tr, body: "let x@ : u32 in 0 .. 100 = T.slots[2].v;", ..A },
        Atom { id: "t.write", lean: "Stmt.assignSlot", decls: &[T], eff: &["writes T.slots"], wache: tr, body: "T.slots[2].v = 3;", ..A },
        Atom { id: "t.write.bad", lean: "Stmt.assignSlot", decls: &[T], eff: &["writes T.slots"], wache: tr, body: "T.slots[2].v = 300;", sicher: false, ..A },
        Atom { id: "t.rmw", lean: "Stmt.assignSlot/Expr.add", decls: &[T], eff: &["reads T.slots", "writes T.slots"], wache: tr, body: "let c@ : u32 in 0 .. 100 = T.slots[1].v;\n    if c@ < 50 { T.slots[1].v = 60; }", ..A },
        Atom { id: "t.write.noeffect", lean: "Stmt.assignSlot", decls: &[T], eff: &[], wache: tr, body: "T.slots[2].v = 3;", sicher: false, ..A },
        Atom { id: "t.write.idx", lean: "Stmt.assignSlot", decls: &[T], params: "i@ : index into T", eff: &["writes T.slots"], wache: tr, body: "T.slots[i@].v = 3;", ..A },
        Atom { id: "t.read.idx", lean: "Expr.slot", decls: &[T], params: "i@ : index into T", eff: &["reads T.slots"], wache: tr, ret: " -> u32 in 0 .. 100", body: "return T.slots[i@].v;", ..A },
        Atom { id: "t.thru.w", lean: "Stmt.assignThru", decls: &[T], params: "p@ : ptr<normal, rw> T, i@ : index into T", eff: &["writes p@.slots"], wache: tr, body: "p@.slots[i@].v = 3;", ..A },
        Atom { id: "t.thru.r", lean: "Expr.thru", decls: &[T], params: "p@ : ptr<normal, r> T, i@ : index into T", eff: &["reads p@.slots"], wache: tr, ret: " -> u32 in 0 .. 100", body: "return p@.slots[i@].v;", ..A },
        Atom { id: "t.thru.ro.bad", lean: "Stmt.assignThru", decls: &[T], params: "p@ : ptr<normal, r> T, i@ : index into T", eff: &["writes p@.slots"], wache: tr, body: "p@.slots[i@].v = 3;", sicher: false, ..A },
        Atom { id: "t.two", lean: "Expr.slot/assignSlot", decls: &[T], eff: &["reads T.slots", "writes T.slots"], wache: tr, body: "let c@ : u32 in 0 .. 100 = T.slots[0].v;\n    T.slots[1].v = c@;", ..A },
        Atom { id: "t.u.write", lean: "Stmt.assignSlot", decls: &[U], eff: &["writes U.slots"], body: "U.slots[0].v = 5;", ..A },
        Atom { id: "t.traverse.locked", lean: "Stmt.traverse", decls: &[T], eff: &["reads T", "writes T.slots"], wache: tr, body: "traverse e@ over slots of T by unvisited touches writes T.slots {\n        T.slots[e@].w = 3;\n    }", ..A },
    ]);
    // ---------------------------------------------------------------- statics and atomics
    let sr = Wache::S;
    v.extend([
        Atom { id: "g.read", lean: "Expr.glob", decls: &[S], eff: &["reads s"], wache: sr, body: "let x@ : u32 in 0 .. 100 = s;", ..A },
        Atom { id: "g.write", lean: "Stmt.assignGlob", decls: &[S], eff: &["writes s"], wache: sr, body: "s = 3;", ..A },
        Atom { id: "g.write.bad", lean: "Stmt.assignGlob", decls: &[S], eff: &["writes s"], wache: sr, body: "s = 300;", sicher: false, ..A },
        Atom { id: "g.rmw", lean: "Stmt.assignGlob/Expr.glob", decls: &[S], eff: &["reads s", "writes s"], wache: sr, body: "let x@ : u32 in 0 .. 100 = s;\n    if x@ < 50 { s = 60; }", ..A },
        Atom { id: "a.store", lean: "Stmt.publish(nothing)", decls: &["atomic A : u32 relaxed;"], eff: &["writes A"], body: "A = 7 publishes nothing;", ..A },
        Atom { id: "a.load", lean: "Expr.glob(atomic)", decls: &["atomic A : u32 relaxed;"], eff: &["reads A"], body: "let n@ : u32 = A;", ..A },
        Atom { id: "a.store.plain", lean: "Stmt.assignGlob(atomic)", decls: &["atomic A : u32 relaxed;"], eff: &["writes A"], body: "A = 7;", sicher: false, ..A },
        Atom { id: "a.publish", lean: "Stmt.publish(payload)", decls: &["static mut p : u64 = 0;", "atomic B : bool release;"], eff: &["writes p", "publishes B"], body: "p = 5;\n    B = true publishes { p };", ..A },
        Atom { id: "a.await", lean: "Block.awaits", decls: &["static mut p : u64 = 0;", "atomic B : bool acquire;"], eff: &["reads B", "reads p"], body: "let fertig@ = B awaits { p };\n    if fertig@ { let x@ : u64 = p; }", ..A },
        Atom { id: "a.exchange", lean: "Block.exchange", decls: &["atomic C : u32 in 0 .. 100 relaxed;", EXTERN_NIE], eff: &["reads C", "writes C"], ret: " -> u32 in 0 .. 100", body: "let alt@ = C exchange update(v) bounded 8 ops on_exceeded zeit {\n        if v < 100 { return v + 1; }\n        return v;\n    } publishes nothing;\n    return alt@;", ..A },
        Atom { id: "a.exchange.when", lean: "Block.exchange", decls: &["atomic D : u32 relaxed;"], eff: &["reads D", "writes D"], ret: " -> bool", body: "let ok@ = D exchange 1 when old(D) == 0 returns erfolg publishes nothing;\n    return ok@;", ..A },
    ]);
    // ---------------------------------------------------------------- arenas
    const ar: &str = "arena R capacity 2 .. 8 of u32;";
    v.extend([
        Atom { id: "r.alloc", lean: "Block.arenaAlloc", decls: &[ar], eff: &["writes R", "reads R"], ret: " -> u32", body: "let a@ = alloc R (10) else { return 0; };\n    return R[a@];", ..A },
        Atom { id: "r.alloc.noelse", lean: "Block.arenaAlloc", decls: &[ar], eff: &["writes R"], body: "let a@ = alloc R (10);", ..A },
        Atom { id: "r.reset", lean: "Stmt.arenaReset", decls: &[ar], eff: &["writes R"], body: "reset R;", ..A },
        Atom { id: "r.stale", lean: "Stmt.arenaReset", decls: &[ar], eff: &["writes R", "reads R"], ret: " -> u32", body: "let a@ = alloc R (10) else { return 0; };\n    reset R;\n    return R[a@];", sicher: false, ..A },
        Atom { id: "r.free", lean: "Stmt.free", decls: &[ar], eff: &["writes R", "reads R"], ret: " -> u32", body: "let a@ = alloc R (10) else { return 0; };\n    free R[a@];\n    return 1;", ..A },
        Atom { id: "r.free.twice", lean: "Stmt.free", decls: &[ar], eff: &["writes R", "reads R"], ret: " -> u32", body: "let a@ = alloc R (10) else { return 0; };\n    free R[a@];\n    free R[a@];\n    return 1;", sicher: false, ..A },
        Atom { id: "r.grow", lean: "Stmt.grow", decls: &[ar], eff: &["writes R"], body: "grow R by 2 else { return; };", ..A },
    ]);
    // ---------------------------------------------------------------- locks
    v.extend([
        Atom { id: "k.nest.ok", lean: "Stmt.locks(rank)", decls: &[T, LA, LB, U], eff: &["writes U.slots", "writes V.slots", "locks LA", "locks LB"], body: "locks LA { locks LB { U.slots[0].v = 1; V.slots[0].v = 2; } }", ..A },
        Atom { id: "k.nest.rev", lean: "Stmt.locks(rank)", decls: &[T, LA, LB, U], eff: &["writes U.slots", "writes V.slots", "locks LA", "locks LB"], body: "locks LB { locks LA { U.slots[0].v = 1; V.slots[0].v = 2; } }", sicher: false, ..A },
        Atom { id: "k.twice", lean: "Stmt.locks(rank)", decls: &[T, LA, U], eff: &["writes U.slots", "locks LA"], body: "locks LA { locks LA { U.slots[0].v = 1; } }", sicher: false, ..A },
        Atom { id: "k.masks", lean: "Deklaration.maskiert", decls: &[U, "lock LM protects { U } rank 0 held <= 100 ops masks irqs;"], eff: &["writes U.slots", "locks LM"], body: "locks LM { U.slots[0].v = 1; }", ..A },
        Atom { id: "k.call.in", lean: "Stmt.call(held)", decls: &[U, LA], items: &["impl fn ku() requires Held(LA) effects { writes U.slots, locks LA } costs <= 8 ops { U.slots[0].v = 1; }"], eff: &["writes U.slots", "locks LA"], body: "locks LA { ku(); }", ..A },
        Atom { id: "k.call.out", lean: "Stmt.call(held)", decls: &[U, LA], items: &["impl fn ku() requires Held(LA) effects { writes U.slots, locks LA } costs <= 8 ops { U.slots[0].v = 1; }"], eff: &["writes U.slots", "locks LA"], body: "ku();", sicher: false, ..A },
    ]);
    // ---------------------------------------------------------------- floats and gates
    v.extend([
        Atom { id: "k.inv.held", lean: "SperrInv", decls: &[PQ, LK], params: "k@ : ptr<normal, rw> P, m@ : ptr<normal, rw> Q", req: "Held(K)", eff: &["writes k@.slots", "writes m@.slots", "locks K"], body: "k@.slots[0].x = 30;\n    m@.slots[0].y = 70;", ..A },
        Atom { id: "k.inv.held.bad", lean: "SperrInv", decls: &[PQ, LK], params: "k@ : ptr<normal, rw> P, m@ : ptr<normal, rw> Q", req: "Held(K)", eff: &["writes k@.slots", "writes m@.slots", "locks K"], body: "k@.slots[0].x = 30;\n    m@.slots[0].y = 71;", sicher: false, ..A },
        Atom { id: "k.inv.block", lean: "SperrInv", decls: &[PQ, LK], params: "k@ : ptr<normal, rw> P, m@ : ptr<normal, rw> Q", eff: &["writes k@.slots", "writes m@.slots", "locks K"], body: "locks K {\n        k@.slots[0].x = 30;\n        m@.slots[0].y = 70;\n    }", ..A },
        Atom { id: "k.inv.block.bad", lean: "SperrInv", decls: &[PQ, LK], params: "k@ : ptr<normal, rw> P, m@ : ptr<normal, rw> Q", eff: &["writes k@.slots", "writes m@.slots", "locks K"], body: "locks K {\n        k@.slots[0].x = 30;\n        m@.slots[0].y = 71;\n    }", sicher: false, ..A },
        Atom { id: "f.add", lean: "Block.float", params: "x@ : f64 in 0.0 .. 1.0", ret: " -> f64 in 0.0 .. 2.0", body: "let y@ : f64 in 0.0 .. 2.0 = x@ + x@;\n    return y@;", ..A },
        Atom { id: "f.add.bad", lean: "Block.float", params: "x@ : f64 in 0.0 .. 1.0", ret: " -> f64 in 0.0 .. 1.0", body: "let y@ : f64 in 0.0 .. 1.0 = x@ + x@;\n    return y@;", sicher: false, ..A },
        Atom { id: "f.narrow", lean: "Block.floatNarrow", params: "x@ : f64", ret: " -> f64 in 0.0 .. 1.0", body: "narrow x@ to 0.0 .. 1.0 else { return 0.5; }\n    return x@;", ..A },
        Atom { id: "f.lit", lean: "Block.floatLit", ret: " -> f64 in 0.0 .. 1.0", body: "let y@ : f64 in 0.0 .. 1.0 = 0.5 rounded;\n    return y@;", ..A },
    ]);
    v
}

pub fn alle_ids() -> Vec<&'static str> {
    katalog().iter().map(|a| a.id).collect()
}

/// The unsafe-variant ids (the designer's belief).
pub fn bad_ids() -> Vec<&'static str> {
    katalog().iter().filter(|a| !a.sicher).map(|a| a.id).collect()
}

#[allow(dead_code)]
const _: &str = GATE;
