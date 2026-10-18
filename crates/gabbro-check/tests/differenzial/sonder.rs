//! Whole units that do not decompose into atoms: a form that needs a declaration beside two
//! functions (`concurrent`, `entry`, a lock shared by a thread and a handler), written out. They
//! stand in the space as one-atom programs (`One`/`Free`), named `u.*`.

const THREAD_UND_HANDLER_MASKIERT: &str = "module gen::u {
table Takte count 8 { slot { stand : u64, } }
lock TAKT protects { Takte } rank 0 held <= 40 ops masks irqs;
impl fn zaehle(i : index into Takte)
    requires Held(TAKT)
    effects { writes Takte.slots, locks TAKT }
    costs <= 8 ops
{ Takte.slots[i].stand = 1; }
impl fn verteiler() effects { writes Takte.slots, locks TAKT } costs <= 40 ops {
    locks TAKT { zaehle(0); }
}
entry zeitgeber via irq arch x86_64 {
    regs in  { }
    regs out { }
    preserves { rbx, rbp, r12, r13, r14, r15 }
    clobbers  { rax, rcx, rdx, rsi, rdi, r8, r9, r10, r11 }
    stack takt_stapel per cpu nested never
    dispatch verteiler;
}
}
";

const HANDLER_OHNE_MASKE: &str = "module gen::u {
table Takte count 8 { slot { stand : u64, } }
lock TAKT protects { Takte } rank 0 held <= 40 ops;
impl fn verteiler() effects { writes Takte.slots, locks TAKT } costs <= 40 ops {
    locks TAKT { Takte.slots[0].stand = 1; }
}
entry zeitgeber via irq arch x86_64 {
    regs in  { }
    regs out { }
    preserves { rbx, rbp, r12, r13, r14, r15 }
    clobbers  { rax, rcx, rdx, rsi, rdi, r8, r9, r10, r11 }
    stack takt_stapel per cpu nested never
    dispatch verteiler;
}
}
";

const START_MITGLIED: &str = "module gen::u {
static mut g : u64 = 0;
lock L protects { g } rank 0 held <= 100 ops;
impl fn arbeiterA() effects { writes g, locks L } costs <= 20 ops { locks L { g = 1; } }
impl fn chef() effects { writes g, locks L } costs <= 100 ops { start { arbeiterA }; }
concurrent { arbeiterA, chef };
}
";

const START_UND_LOCKS: &str = "module gen::u {
static mut g : u64 = 0;
lock L protects { g } rank 0 held <= 100 ops;
impl fn arbeiterA() effects { writes g, locks L } costs <= 20 ops { locks L { g = 1; } }
impl fn chef() effects { writes g, locks L } costs <= 100 ops { locks L { start { arbeiterA }; } }
}
";

const ZWEI_FAEDEN_GESCHUETZT: &str = "module gen::u {
static mut g : u64 = 0;
lock L protects { g } rank 0 held <= 100 ops;
impl fn a() effects { writes g, locks L } costs <= 20 ops { locks L { g = 1; } }
impl fn b() effects { writes g, locks L } costs <= 20 ops { locks L { g = 2; } }
concurrent { a, b };
}
";

const ZWEI_FAEDEN_LESER_SCHREIBER: &str = "module gen::u {
static mut g : u64 = 0;
impl fn a() effects { writes g } costs <= 20 ops { g = 1; }
impl fn b() effects { reads g } costs <= 20 ops { let x : u64 = g; }
concurrent { a, b };
}
";

const ZWEI_FAEDEN_LESER_LESER: &str = "module gen::u {
static mut g : u64 = 0;
impl fn a() effects { reads g } costs <= 20 ops { let x : u64 = g; }
impl fn b() effects { reads g } costs <= 20 ops { let x : u64 = g; }
concurrent { a, b };
}
";

const ZWEI_FAEDEN_ATOMAR_ZAEHLER: &str = "module gen::u {
atomic Z : u32 relaxed;
impl fn a() effects { writes Z } costs <= 20 ops { Z = 1 publishes nothing; }
impl fn b() effects { writes Z } costs <= 20 ops { Z = 2 publishes nothing; }
concurrent { a, b };
}
";

const MESSAGE_PASSING: &str = "module gen::u {
static mut p : u64 = 0;
atomic B : bool release;
impl fn melde(w : u64) effects { writes p, publishes B } costs <= 8 ops { p = w; B = true publishes { p }; }
impl fn lies() -> u64 effects { reads B, reads p } costs <= 8 ops {
    let fertig = B awaits { p };
    if fertig { return p; }
    return 0;
}
}
";

const MESSAGE_PASSING_PAAR: &str = "module gen::u {
static mut p : u64 = 0;
atomic B : bool release;
impl fn melde() effects { writes p, publishes B } costs <= 8 ops { p = 5; B = true publishes { p }; }
impl fn lies() effects { reads B, reads p } costs <= 8 ops {
    let fertig = B awaits { p };
    if fertig { let x : u64 = p; }
}
concurrent { melde, lies };
}
";

const RANG_RING: &str = "module gen::u {
table T count 4 { slot { v : u32 in 0 .. 100, } }
table V count 4 { slot { v : u32 in 0 .. 100, } }
lock LA protects { T } rank 0 held <= 100 ops;
lock LB protects { V } rank 1 held <= 100 ops;
impl fn a() effects { writes T.slots, writes V.slots, locks LA, locks LB } costs <= 200 ops {
    locks LA { locks LB { T.slots[0].v = 1; V.slots[0].v = 2; } }
}
impl fn b() effects { writes T.slots, writes V.slots, locks LA, locks LB } costs <= 200 ops {
    locks LB { locks LA { T.slots[0].v = 1; V.slots[0].v = 2; } }
}
concurrent { a, b };
}
";

const RANG_GLEICH: &str = "module gen::u {
table T count 4 { slot { v : u32 in 0 .. 100, } }
table V count 4 { slot { v : u32 in 0 .. 100, } }
lock LA protects { T } rank 0 held <= 100 ops;
lock LB protects { V } rank 0 held <= 100 ops;
impl fn a() effects { writes T.slots, writes V.slots, locks LA, locks LB } costs <= 200 ops {
    locks LA { locks LB { T.slots[0].v = 1; V.slots[0].v = 2; } }
}
}
";

const LOCK_UEBER_AUFRUF_GUT: &str = "module gen::u {
table T count 4 { slot { v : u32 in 0 .. 100, } }
table V count 4 { slot { v : u32 in 0 .. 100, } }
lock LA protects { T } rank 0 held <= 400 ops;
lock LB protects { V } rank 1 held <= 100 ops;
impl fn g() effects { writes V.slots, locks LB } costs <= 100 ops { locks LB { V.slots[0].v = 2; } }
impl fn f() effects { writes T.slots, writes V.slots, locks LA, locks LB } costs <= 300 ops {
    locks LA { T.slots[0].v = 1; g(); }
}
}
";

const LOCK_UEBER_AUFRUF_UMGEKEHRT: &str = "module gen::u {
table T count 4 { slot { v : u32 in 0 .. 100, } }
table V count 4 { slot { v : u32 in 0 .. 100, } }
lock LA protects { T } rank 0 held <= 100 ops;
lock LB protects { V } rank 1 held <= 400 ops;
impl fn g() effects { writes T.slots, locks LA } costs <= 100 ops { locks LA { T.slots[0].v = 1; } }
impl fn f() effects { writes T.slots, writes V.slots, locks LA, locks LB } costs <= 300 ops {
    locks LB { V.slots[0].v = 2; g(); }
}
}
";

const SPERRE_GESCHUETZT_UEBER_ZEIGER_AUFRUFER: &str = "module gen::u {
table T count 4 { slot { v : u32 in 0 .. 100, } }
lock L protects { T } rank 0 held <= 100 ops;
impl fn w(p : ptr<normal, rw> T, i : index into T) requires Held(L) effects { writes p.slots, locks L } costs <= 8 ops {
    p.slots[i].v = 3;
}
impl fn f(p : ptr<normal, rw> T) effects { writes p.slots, locks L } costs <= 100 ops {
    locks L { w(p, 0); }
}
}
";

pub fn sonder() -> Vec<(&'static str, &'static str)> {
    vec![
        ("u.irq.masked", THREAD_UND_HANDLER_MASKIERT),
        ("u.irq.unmasked", HANDLER_OHNE_MASKE),
        ("u.start.member", START_MITGLIED),
        ("u.start.in.locks", START_UND_LOCKS),
        ("u.par.locked", ZWEI_FAEDEN_GESCHUETZT),
        ("u.par.reader.writer", ZWEI_FAEDEN_LESER_SCHREIBER),
        ("u.par.reader.reader", ZWEI_FAEDEN_LESER_LESER),
        ("u.par.atomic.writers", ZWEI_FAEDEN_ATOMAR_ZAEHLER),
        ("u.mp.single", MESSAGE_PASSING),
        ("u.mp.pair", MESSAGE_PASSING_PAAR),
        ("u.rank.ring", RANG_RING),
        ("u.rank.equal", RANG_GLEICH),
        ("u.rank.call.good", LOCK_UEBER_AUFRUF_GUT),
        ("u.rank.call.reverse", LOCK_UEBER_AUFRUF_UMGEKEHRT),
        ("u.ptr.held.chain", SPERRE_GESCHUETZT_UEBER_ZEIGER_AUFRUFER),
    ]
}
