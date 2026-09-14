//! **Bare atomics (lane 152) in both directions.**
//!
//! The T4 C-semantics lane reported two emitter findings from reading; this
//! file measures them:
//!
//! * a bare read of an `atomic` global (`let x = AT;`) checked clean and came
//!   out as the plain name -- over `_Atomic` C treats that as a `seq_cst`
//!   access while the declaration said `relaxed`, and the C model
//!   (`C-SPEICHERMODELL.md` §1c) makes a plain access to an atomic stuck.
//!   The fix is the emitter's: a bare read lowers to
//!   `atomic_load_explicit` in the DECLARED load order, through the one place
//!   every runtime read funnels through (`ort()` -- expressions, `retry …
//!   until` conditions via `pred_c`, narrow bounds, indices). Refusing the
//!   read instead would make payload-free atomics (`publishes nothing`,
//!   `SPRACHE.md` §1.1) unreadable and the `retry`-spin inexpressible.
//! * a bare store (`AT = w;`) is refused with `N270`: `SPRACHE.md` §11.3 says
//!   every store to an atomic IS a `publishstmt`, so the bare store has no
//!   form. Lowering it to an explicit store is no fix -- the store is where
//!   the payload promise stands (V001-V004), and an explicit store without
//!   one would carry the pairing past the checker in silence.
//! * a suffixed place over an atomic (`AT[0]`) is refused with `N271`: the
//!   atomic is a scalar, so no suffix names anything -- it checked clean (the
//!   indexed type falls out as untyped) and emitted an index into a scalar.
//!   The legal indexed atomics (`FP_OWNER[core]` at `publishes` / `awaits` /
//!   `exchange`) are their own statements and never stand in an expression.
//!
//! What each row is:
//!
//! * a bare `=` store falls with `N270` ALONE;
//! * so does a compound `&=` store (the op family), and a `+=` store draws
//!   `N270` beside its range neighbours (`M104`, `M101` -- the arithmetic
//!   half, not the atomicity half);
//! * a bare store falls with `N270` ALONE even where a pairing lives
//!   (`beispiele/gift/937` over a file, this row over a snippet);
//! * a parameter shadowing the atomic stays silent on store AND read -- the
//!   store is the parameter's, and the read lowers as the plain C local;
//! * a bare read of a `relaxed` / `release` / `seq` atomic lowers to an
//!   explicit load in `relaxed` / `acquire` / `seq_cst` (the load side of the
//!   declaration -- a `release` declaration loads `acquire`);
//! * a `retry … until` spin over an atomic lowers explicitly, in the declared
//!   order -- the shape `messung/proben/probe-transport-poll-used.gab`
//!   expresses, and the one `C-SPEICHERMODELL.md` §1c counts;
//! * the legal stores stay silent: `publishes { … }`, `publishes nothing`,
//!   and the `awaits` load;
//! * a variant constructor in a body fell with `H021` (the call graph owned
//!   the refusal -- M1 left the callee untyped, costs had no declaration);
//!   since lane 167 the construction is legal and lowers to the compound
//!   literal the `match` reads, so the two rows below pin the new behaviour
//!   and the old `H021` pin moved to `beispiele/gift/938`'s successor shape;
//!   the same shape in a `static` initialiser, which no body pass visits, was
//!   refused by the emitter with `C001` -- since lane 167 it lowers in braces,
//!   and the row pins that instead.

use gabbro_syntax::diag::Stufe;

fn errors(source: &str) -> Vec<String> {
    let (tree, mut refusals) = gabbro_syntax::lies("bare_atomic", source);
    let _ = gabbro_check::pruefe(&tree, &mut refusals);
    refusals
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code.to_string())
        .collect()
}

fn emitted(source: &str) -> (String, Vec<String>) {
    let (tree, mut refusals) = gabbro_syntax::lies("bare_atomic", source);
    let _ = gabbro_check::pruefe(&tree, &mut refusals);
    let fall: Vec<String> = refusals
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code.to_string())
        .collect();
    assert!(
        fall.is_empty(),
        "the positive probe does not check clean -- fell with {fall:?}"
    );
    let c = gabbro_check::emit::emittiere(&tree, &mut refusals);
    let nachher: Vec<String> = refusals
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code.to_string())
        .collect();
    (c, nachher)
}

const HEAD: &str = "module test::bare_atomic {\natomic AT : u32 relaxed;\n";

fn unit(extra: &str) -> String {
    format!("{HEAD}{extra}}}\n")
}

#[test]
fn n270_bare_store_falls_alone() {
    let src = unit(
        "impl fn schreibe(w : u32) effects { writes AT } costs <= 4 ops { AT = w; }\n",
    );
    assert_eq!(errors(&src), vec!["N270"], "a bare `=` store to an atomic");
}

#[test]
fn n270_compound_and_store_falls_alone() {
    let src = unit(
        "impl fn schneide(w : u32) effects { writes AT } costs <= 4 ops { AT &= w; }\n",
    );
    assert_eq!(errors(&src), vec!["N270"], "a bare `&=` store to an atomic");
}

#[test]
fn n270_plus_store_draws_n270_beside_the_range() {
    let src = unit(
        "impl fn lege_drauf(w : u32) effects { writes AT } costs <= 4 ops { AT += w; }\n",
    );
    assert_eq!(
        errors(&src),
        vec!["N270", "M104", "M101"],
        "a bare `+=` store: N270 owns the atomicity, the M-rules the range"
    );
}

#[test]
fn n270_bare_store_falls_despite_a_live_pairing() {
    let src = "module test::bare_atomic {\n\
         static mut bericht : u64 = 0;\n\
         atomic FLAG : bool release;\n\
         impl fn melde(w : u64) effects { writes bericht, publishes FLAG } costs <= 8 ops \
         { bericht = w; FLAG = true publishes { bericht }; }\n\
         impl fn lies() -> u64 effects { reads FLAG, reads bericht } costs <= 8 ops \
         { let fertig = FLAG awaits { bericht }; if fertig { return bericht; } return 0; }\n\
         impl fn rueck() effects { writes FLAG } costs <= 4 ops { FLAG = false; }\n\
         }\n";
    assert_eq!(
        errors(src),
        vec!["N270"],
        "a live pairing does not bless the bare store"
    );
}

#[test]
fn n270_shadowed_parameter_stays_silent() {
    let src = unit(
        "impl fn f(AT : u32, w : u32) -> u32 effects { writes AT } costs <= 4 ops \
         { AT = w; return AT; }\n",
    );
    assert_eq!(
        errors(&src),
        Vec::<String>::new(),
        "a shadowing parameter owns its store -- N270 reads the global only"
    );
}

#[test]
fn bare_read_lowers_to_the_declared_relaxed_load() {
    let src = unit(
        "impl fn lies() -> u32 effects { reads AT } costs <= 4 ops \
         { let n : u32 = AT; return n; }\n",
    );
    let (c, nachher) = emitted(&src);
    assert!(nachher.is_empty(), "the read probe refuses at emit: {nachher:?}");
    assert!(
        c.contains("atomic_load_explicit(&AT, memory_order_relaxed)"),
        "a bare read is an explicit load in the declared order, not the plain name:\n{c}"
    );
    assert!(
        !c.contains("uint32_t n = AT;"),
        "the plain access is gone:\n{c}"
    );
}

#[test]
fn bare_read_takes_the_load_side_of_the_declaration() {
    let src = "module test::bare_atomic {\n\
         atomic LADE : bool release;\n\
         atomic FOLGE : u32 seq;\n\
         impl fn ob() -> bool effects { reads LADE } costs <= 4 ops \
         { return LADE; }\n\
         impl fn lies() -> u32 effects { reads FOLGE } costs <= 4 ops \
         { return FOLGE; }\n\
         }\n";
    let (c, nachher) = emitted(src);
    assert!(nachher.is_empty(), "the order probe refuses at emit: {nachher:?}");
    assert!(
        c.contains("atomic_load_explicit(&LADE, memory_order_acquire)"),
        "a `release` declaration loads `acquire` (C11 has no releasing load):\n{c}"
    );
    assert!(
        c.contains("atomic_load_explicit(&FOLGE, memory_order_seq_cst)"),
        "a `seq` declaration loads `seq_cst`:\n{c}"
    );
}

#[test]
fn bare_read_of_a_shadowed_parameter_stays_plain() {
    let src = unit(
        "impl fn f(AT : u32) -> u32 effects { pure } costs <= 4 ops { return AT; }\n",
    );
    let (c, nachher) = emitted(&src);
    assert!(nachher.is_empty(), "the shadow probe refuses at emit: {nachher:?}");
    assert!(
        c.contains("return AT;"),
        "the parameter read stays the plain C local:\n{c}"
    );
    assert!(
        !c.contains("atomic_load_explicit(&AT"),
        "no explicit load about a parameter:\n{c}"
    );
}

#[test]
fn spin_until_over_an_atomic_lowers_explicitly() {
    // What this row owns is the spin condition, lowered through `pred_c` --
    // the shape `messung/proben/probe-transport-poll-used.gab` expresses, and
    // the one `C-SPEICHERMODELL.md` §1c counts.
    let spin = "module test::bare_atomic_spin {\n\
         atomic BEREIT : bool acquire;\n\
         assume karte_antwortet \"A working device answers.\" falsifier sonde_stumm;\n\
         extern fn gib_auf() -> never effects { diverges } costs <= 1 ops;\n\
         impl fn warte() effects { reads BEREIT } costs <= 4096 ops {\n\
         \x20   retry warten until BEREIT == true\n\
         \x20       bounded 2048 ops\n\
         \x20       progress karte_antwortet\n\
         \x20       on_exceeded gib_auf\n\
         \x20       effects { reads BEREIT }\n\
         \x20   { }\n\
         }\n\
         }\n";
    let (c, nachher) = emitted(spin);
    assert!(nachher.is_empty(), "the spin probe refuses at emit: {nachher:?}");
    assert!(
        c.contains("atomic_load_explicit(&BEREIT, memory_order_acquire)"),
        "the spin reads explicitly in the declared order:\n{c}"
    );
}

#[test]
fn legal_atomic_forms_stay_silent() {
    let src = "module test::bare_atomic {\n\
         static mut bericht : u64 = 0;\n\
         atomic FLAG : bool release;\n\
         atomic Z : u32 relaxed;\n\
         impl fn melde(w : u64) effects { writes bericht, publishes FLAG } costs <= 8 ops \
         { bericht = w; FLAG = true publishes { bericht }; }\n\
         impl fn lies() -> u64 effects { reads FLAG, reads bericht } costs <= 8 ops \
         { let fertig = FLAG awaits { bericht }; if fertig { return bericht; } return 0; }\n\
         impl fn zaehle(t : u32) effects { writes Z } costs <= 4 ops \
         { Z = t publishes nothing; }\n\
         }\n";
    assert_eq!(
        errors(src),
        Vec::<String>::new(),
        "`publishes`, `awaits` and `publishes nothing` are N270's silent direction"
    );
}

#[test]
fn n271_index_into_an_atomic_falls_alone() {
    let src = unit(
        "impl fn lies() -> u32 effects { reads AT } costs <= 4 ops \
         { let x : u32 = AT[0]; return x; }\n",
    );
    assert_eq!(
        errors(&src),
        vec!["N271"],
        "an indexed read over a scalar atomic (`beispiele/gift/939` over a file)"
    );
}

#[test]
fn variant_constructor_in_a_body_builds_and_lowers() {
    // **Lane 167: `Kurz(x)` is a construction, not a call.** It checks clean
    // (no `H021`, no `K003` -- the graph carries no edge, the cost pass prices
    // one op) and lowers to the compound literal the `match` reads back.
    let src = "module test::variante {\n\
         tagged type Nachricht = { Leer, Kurz(u32), Lang(u64) };\n\
         impl fn baue(x : u32) -> Nachricht effects { pure } costs <= 4 ops \
         { return Kurz(x); }\n\
         }\n";
    assert_eq!(
        errors(src),
        Vec::<String>::new(),
        "a variant construction checks clean -- fell with {:?}",
        errors(src)
    );
    let (c, nachher) = emitted(src);
    assert!(
        nachher.is_empty(),
        "the construction emits without refusal -- fell with {nachher:?}"
    );
    assert!(
        c.contains("(Nachricht){ .marke = Nachricht_Kurz, .last.Kurz = x }"),
        "the construction lowers to the compound literal the `match` reads:\n{c}"
    );
}

#[test]
fn variant_constructor_in_a_static_init_lowers_in_braces() {
    let quelle = "module test::variante {\n\
         tagged type Nachricht = { Leer, Kurz(u32), Lang(u64) };\n\
         static N : Nachricht = Kurz(5);\n\
         impl fn lies() -> u32 effects { pure } costs <= 4 ops { return 0; }\n\
         }\n";
    // The checker visits the initialiser against the declared sum type, and the
    // emitter writes the brace form -- a compound literal is no constant
    // expression, so the file-scope spelling carries the same designators in
    // braces.
    assert_eq!(
        errors(quelle),
        Vec::<String>::new(),
        "the checker holds the static initialiser against the sum type"
    );
    let (baum, mut absagen) = gabbro_syntax::lies("variante_statisch", quelle);
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    let c = gabbro_check::emit::emittiere(&baum, &mut absagen);
    let gefallen: Vec<String> = absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code.to_string())
        .collect();
    assert!(
        gefallen.is_empty(),
        "the emitter lowers the variant initialiser -- fell with {gefallen:?}"
    );
    assert!(
        c.contains("{ .marke = Nachricht_Kurz, .last.Kurz = 5 }"),
        "the static initialiser lowers in braces:\n{c}"
    );
}
