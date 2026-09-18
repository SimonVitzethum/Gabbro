//! **Export `.gab` to a G program term (`gabbro lean-g`), over snippets.**
//!
//! The file half is `beispiele/104-referenz.gab` (mechanical export checks
//! with `./lean-probe`, pinned in `grammatik/Grammatik/Export104.lean`) and
//! `beispiele/108-disjoint-start-locks.gab` (`Export108.lean`); what stands
//! here pins the same exporter over snippets -- the two positives and every
//! refusal code (`LG001`-`LG005`), so a form that stops being refused fails
//! here even where no corpus file has the shape.

use gabbro_check::lean_g::{export, Refusal};

fn tree(quelle: &str) -> gabbro_syntax::ast::Programm {
    let (baum, _) = gabbro_syntax::lies("lean_g", quelle);
    baum
}

fn refuse_of(quelle: &str) -> Refusal {
    export("lean_g", &tree(quelle)).expect_err("must refuse")
}

const KOPF: &str = "module test::leang {\n\
    table T count 4 { slot { v : u32, } }\n\
    lock L protects { T } rank 0 held <= 100 ops;\n";

fn einheit(extra: &str) -> String {
    format!("{KOPF}{extra}}}\n")
}

fn beispiele(name: &str) -> String {
    let pfad = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../beispiele").join(name);
    std::fs::read_to_string(&pfad).expect("example readable")
}

fn export_file(name: &str) -> String {
    let q = beispiele(name);
    let (baum, _) = gabbro_syntax::lies(name, &q);
    export(name, &baum).expect("example must export")
}

/// **104 exports**: the declaration, the program, the member list and both
/// decidable checks travel; names are file-derived so two exports never
/// collide.
#[test]
fn export_104_succeeds() {
    let text = export_file("104-referenz.gab");
    for teil in [
        "namespace G104_referenz",
        "inductive GTab where",
        "| Konto",
        "inductive GLock where",
        "| M",
        "def gSig_einzahlen",
        "def gSig_lies",
        "theorem gHp_einzahlen_lies",
        "def gP : Programm gD where",
        "def gFs : List gD.Fn",
        "example : programmImFragmentG gP gFs = true := by decide",
        "example : fussOrtGB gP gFs = true := by decide",
    ] {
        assert!(text.contains(teil), "104 export must contain {teil:?}");
    }
}

/// **108 exports**: one table, two lock-free readers over it, no calls.
#[test]
fn export_108_succeeds() {
    let text = export_file("108-disjoint-start-locks.gab");
    for teil in [
        "namespace G108_disjoint_start_locks",
        "| T",
        "def gSig_read_a",
        "def gSig_read_c",
        ".int 0 4294967295",
        "haelt := []",
        "example : programmImFragmentG gP gFs = true := by decide",
        "example : fussOrtGB gP gFs = true := by decide",
    ] {
        assert!(text.contains(teil), "108 export must contain {teil:?}");
    }
    assert!(
        !text.contains("RufPasst"),
        "108 has no calls, so no RufPasst proof may travel"
    );
}

/// **124 exports**: a floored caller (`hauptA` takes `L`) calling a lock-free
/// callee (`setze`, `pruefeA`). Before 2026-09-15 the exporter gave a
/// lock-free body the floor `none` -- the one value that promises callers
/// nothing -- and refused the call at `RufPasst.hb`. The floor is now the
/// minimum rank taken in the reachable call graph, `HOCH` where there is none.
#[test]
fn export_124_succeeds() {
    let text = export_file("124-two-threads-private.gab");
    assert!(text.contains("def gSig_setze"), "{text}");
    // `L` has rank 0, so `HOCH` is 1: the lock-free callees carry it, and
    // `hauptA`, which takes `L`, carries 0.
    assert!(text.contains("boden := some 1"), "a lock-free body gets HOCH: {text}");
    assert!(text.contains("boden := some 0"), "a body taking rank 0 gets 0: {text}");
    assert!(text.contains("theorem gHp_hauptA_in_L_setze"), "{text}");
}

/// **`gSp0` parenthesises both halves.** `⟨fun t => nomatch t, (fun g => …)⟩`
/// does NOT parse as two fields -- `nomatch` takes a comma-separated list of
/// discriminants and swallows the second half. Every table-less export
/// carried that since `gSp0` was introduced.
#[test]
fn sp0_halves_are_parenthesised() {
    let text = export("ohnetab.gab", &tree(
        "module test::ohnetab {\n\
         impl fn f(x : u32) -> u32 effects { pure } costs <= 1 ops { return x; }\n\
         }\n",
    ))
    .expect("a table-less unit must export");
    assert!(
        text.contains("⟨(fun t => nomatch t), (fun g => nomatch g)⟩"),
        "both halves must stand parenthesised: {text}"
    );
}

/// **O14, the exporter half**: an `arena` travels as the PAIR
/// `ArenaZucker.lean` names -- a table of `count = hi` with one field beside
/// a `used` global -- with `Stmt.arenaReset`, `Block.arenaAlloc` and the
/// arena read `A[i]`.
#[test]
fn exports_arena_as_its_pair() {
    let text = export("arena.gab", &tree(
        "module test::arena {\n\
         arena Log capacity 2 .. 8 of u32;\n\
         impl fn f(k : bool) -> u32\n\
             effects { writes Log, reads Log }\n\
             costs   <= 64 ops\n\
         {\n\
             if k {\n\
                 let a = alloc Log (10) else {\n            return 0;\n        };\n\
                 return Log[a];\n\
             } else {\n        reset Log;\n    }\n\
             return 1;\n\
         }\n\
         }\n",
    ))
    .expect("an arena must export");
    for teil in [
        "import Grammatik.ArenaZucker",
        "inductive GTab where",
        "| Log",
        "| wert",
        "| Log_used",
        "count := fun | .Log => 8",
        "gtyp := fun | .Log_used => (.int 0 8)",
        "def gArena_Log : ArenaForm gD where",
        "tab := GTab.Log",
        "zaehl := GGlob.Log_used",
        "Block.arenaAlloc (D := gD) gArena_Log",
        "Stmt.arenaReset (D := gD) gArena_Log",
        // the counter starts at zero, and the reservation `2` travels nowhere
        "| .Log_used => ⟨0, by decide, by decide⟩",
    ] {
        assert!(text.contains(teil), "arena export must contain {teil:?}\n{text}");
    }
    assert!(!text.contains("capacity"), "the reservation must not travel");
}

/// **LG004**: an `alloc` WITHOUT `else` is refused by name. `Block.arenaAlloc`
/// always carries a full-arena branch and the emitted C carries none; what
/// makes the branch dead is `N212`, which does not travel into the term.
#[test]
fn refuses_alloc_without_else() {
    let w = refuse_of(
        "module test::arena2 {\n\
         arena Log capacity 2 .. 8 of u32;\n\
         impl fn f(k : bool) effects { writes Log } costs <= 64 ops\n\
         {\n    if k {\n        let a = alloc Log (10);\n    }\n}\n\
         }\n",
    );
    assert_eq!(w.code, "LG004", "{w}");
    assert!(w.message.contains("no `else`"), "must name the cause: {w}");
    assert!(w.message.contains("N212"), "must name what makes it dead: {w}");
}

/// **LG004**: an `alloc` at the top level of a body has no form --
/// `Block.arenaAlloc` is a `Block` former and a body is an `Endblock`. This
/// is what still stops `beispiele/98` and `99`, and it is named as such.
#[test]
fn refuses_top_level_alloc() {
    let w = refuse_of(
        "module test::arena3 {\n\
         arena Log capacity 2 .. 8 of u32;\n\
         impl fn f() effects { writes Log } costs <= 64 ops\n\
         {\n    let a = alloc Log (10) else {\n        return;\n    };\n}\n\
         }\n",
    );
    assert_eq!(w.code, "LG004", "{w}");
    assert!(w.message.contains("top level"), "{w}");
}

/// The namespace is derived from the file name, so two exports never
/// declare the same names.
#[test]
fn namespace_comes_from_filename() {
    let text = export("a/b-c.gab", &tree(&einheit(
        "impl fn f() -> u32 effects { pure } costs <= 1 ops { return 1; }\n",
    )))
    .expect("must export");
    assert!(text.contains("namespace b_c"), "stem b-c becomes b_c");
}

/// **An `opaque` alias travels as its range** (2026-09-15): `opaque` is a
/// rule about a UNIT BOUNDARY, like `pub`, and `Deklaration` has no boundary.
#[test]
fn opaque_alias_travels_as_its_range() {
    let text = export("undurchsichtig.gab", &tree(&einheit(
        "opaque type Pa = u32 in 0 .. 7;\n\
         impl fn f(x : Pa) -> Pa effects { pure } costs <= 1 ops { return x; }\n",
    )))
    .expect("an opaque integer alias must export");
    assert!(text.contains("params := [(.int 0 7)]"), "{text}");
    assert!(text.contains("`opaque`"), "the NO-FORM ledger must name the drop");
}

/// **An exclusive bound travels as `lo .. hi-1`** -- the same numbers the
/// checker computes with, spelled with the half-open form.
#[test]
fn exclusive_range_travels_closed() {
    let text = export("exkl.gab", &tree(&einheit(
        "type Idx = u32 in 0 ..< 4;\n\
         impl fn f(x : Idx) -> Idx effects { pure } costs <= 1 ops { return x; }\n",
    )))
    .expect("an exclusive range must export");
    assert!(text.contains("params := [(.int 0 3)]"), "{text}");
}

/// **LG001**: a `linear`, `ghost` or `tagged` type still has no G form --
/// widening `opaque` did not widen those.
#[test]
fn refuses_tagged_and_linear_types() {
    for zeile in [
        "tagged type M = { Leer, Kurz(u32) };\n",
        "linear ghost type M;\n",
        "ghost type M = u32;\n",
    ] {
        let w = refuse_of(&einheit(zeile));
        assert_eq!(w.code, "LG001", "{zeile}: {w}");
    }
}

/// **No item kind leaves through a catch-all.** Every refusal names the item
/// (where the kind has a name) and says what the specification would carry it
/// as -- the defect `N320` and `OFFEN.md` O14 were written for.
#[test]
fn every_item_kind_refuses_with_a_reason() {
    for (zeile, wort, grund) in [
        ("device D(basis : u64) at mmio {\n    reg R : u32 @0x00 class r\n}\n", "device D", "D.Reg"),
        ("assume a \"the device answers\" falsifier probe_a;\n", "assume a", "D.Annahme"),
        ("atomic A : u32 release;\n", "atomic A", "atomar"),
        ("group G over { T, T } {\n    invariant nichtnull cost O(n) runs offline :\n        \
          forall k in slots of T : T.slots[k].v == 0;\n}\n", "group G", "D.Inv"),
        ("use andere::stelle::Pa;\n", "use", "unit boundary"),
    ] {
        let quelle = einheit(&format!(
            "{zeile}impl fn f() -> u32 effects {{ pure }} costs <= 1 ops {{ return 1; }}\n"));
        let w = refuse_of(&quelle);
        assert_eq!(w.code, "LG001", "{zeile}: {w}");
        assert!(w.message.contains(wort), "must name the item: {w}");
        assert!(w.message.contains(grund), "must name the form it would have: {w}");
    }
}

/// **LG001**: an `extern fn` has no G form (no body to translate).
#[test]
fn refuses_extern_fn() {
    let w = refuse_of(&einheit(
        "extern fn e(x : u32) -> u32 effects { pure } costs <= 1 ops;\n",
    ));
    assert_eq!(w.code, "LG001", "{w}");
}

/// **Lane 250: a `stack`-carrying gate names its `D.klon` pair (LG001), and
/// a `child` block names its entry function (LG004).** Nothing is mapped --
/// this tree's `Deklaration` has no `klon` field and the export writes
/// `Ax := Empty` -- so both arms still refuse; what narrowed is the name:
/// the gate arm carries the gate and the handed register, the child arm the
/// enclosing function. A gate WITHOUT `stack` keeps the foreign-body shape.
#[test]
fn refuses_child_carrying_gate_by_name() {
    let tor = "syscall tor(a : u64, s : u64) -> u64\n\
         abi linux arch x86_64 number 1000\n\
         regs in { rdi = a, rsi = s }\n\
         regs out { rax }\n\
         stack rsi\n\
         clobbers { rcx }\n\
         errors { NSTACK => KeinStapel }\n\
         effects { pure }\n\
         kernel kern::start;\n";
    let w = refuse_of(&einheit(&format!(
        "{tor}impl fn f() -> u64 effects {{ pure }} costs <= 1 ops {{ return 1; }}\n"
    )));
    assert_eq!(w.code, "LG001", "{w}");
    assert!(w.message.contains("tor"), "must name the gate: {w}");
    assert!(w.message.contains("rsi"), "must name the handed register: {w}");
    assert!(w.message.contains("D.klon"), "must name the pair it would fill: {w}");
    let w = refuse_of(&einheit(
        "impl fn f() -> u64 effects { pure } costs <= 1 ops { child { return 1; } return 0; }\n",
    ));
    assert_eq!(w.code, "LG004", "{w}");
    assert!(w.message.contains("child"), "must name the statement: {w}");
    assert!(w.message.contains("f"), "must name the entry function: {w}");
    assert!(w.message.contains("D.klon"), "must name the pair it would fill: {w}");
    // A gate without `stack` keeps the old foreign-body refusal, by name.
    let schlicht = tor.replace("stack rsi\n", "");
    let w = refuse_of(&einheit(&format!(
        "{schlicht}impl fn f() -> u64 effects {{ pure }} costs <= 1 ops {{ return 1; }}\n"
    )));
    assert_eq!(w.code, "LG001", "{w}");
    assert!(w.message.contains("D.Ax"), "a plain gate keeps the Ax shape: {w}");
}

/// **A scalar `static` IS a `Glob`** (2026-09-15): the declaration carries
/// `GGlob`/`gtyp`, the initialiser is the `gSp0` entry, a read is
/// `Expr.glob`, a write is `Stmt.assignGlob` under the write right off
/// `effects { writes s }`, and `lock L protects { s }` puts `L` in
/// `gbraucht s`.
#[test]
fn exports_scalar_static() {
    let text = export("statik.gab", &tree(
        "module test::statik {\n\
         table T count 4 { slot { v : u32, } }\n\
         static mut s : u32 in 0 .. 100 = 7;\n\
         lock L protects { s } rank 0 held <= 100 ops;\n\
         impl fn f(x : u32 in 0 .. 100)\n\
             requires Held(L)\n\
             ensures  s == x\n\
             effects  { reads s, writes s }\n\
             costs    <= 4 ops\n\
         {\n    s = x;\n}\n\
         }\n",
    ))
    .expect("a scalar static must export");
    for teil in [
        "inductive GGlob where",
        "| s",
        "gtyp := fun | .s => (.int 0 100)",
        "gbraucht := fun | .s => [.inl GLock.L]",
        "ggeteilt := fun | .s => true",
        "theorem gGDarf_f_s : gdarf gD GGlob.s gL_f",
        ".assignGlob GGlob.s",
        "Expr.glob (D := gD) GGlob.s",
        "(.inr GGlob.s)",
        // the declared initialiser, not zero
        "| .s => ⟨7, by decide, by decide⟩",
    ] {
        assert!(text.contains(teil), "static export must contain {teil:?}\n{text}");
    }
}

/// **LG002**: an ARRAY `static` has no `Glob` form -- a `Glob` carries ONE
/// `Wert`, not a row -- and it is refused BY NAME, never by a catch-all.
#[test]
fn refuses_array_static() {
    let w = refuse_of(&einheit("static mut s : [u8; 4] = 0;\n"));
    assert_eq!(w.code, "LG002", "{w}");
    assert!(w.message.contains("static s"), "must name the static: {w}");
    assert!(w.message.contains("ONE value"), "must say why: {w}");
}

/// **LG001**: a `section` at a `static` is a PLACEMENT, and a `Glob` has
/// none. Before the `Glob` arm this hid behind the blanket `static` refusal.
#[test]
fn refuses_static_with_section() {
    let w = refuse_of(&einheit("static mut s : u32 = 1 section \".data\";\n"));
    assert_eq!(w.code, "LG001", "{w}");
    assert!(w.message.contains("section"), "must name the cause: {w}");
}

/// **LG004**: a write to a global the `effects` do not name has no write
/// right; it is refused here rather than left to a failing `by decide`.
#[test]
fn refuses_unowned_global_write() {
    let w = refuse_of(
        "module test::statik2 {\n\
         table T count 4 { slot { v : u32, } }\n\
         static mut s : u32 in 0 .. 100 = 0;\n\
         impl fn f() effects { reads s } costs <= 4 ops\n\
         {\n    s = 1;\n}\n\
         }\n",
    );
    assert_eq!(w.code, "LG004", "{w}");
    assert!(w.message.contains("global s"), "must name the global: {w}");
}

/// **LG001**: `locks L` in the effects without `requires Held(L)` would need
/// the `locks` statement, which has no form here.
#[test]
fn refuses_locks_without_held() {
    let w = refuse_of(&einheit(
        "impl fn f() -> u32 effects { reads T.slots, locks L } costs <= 4 ops\n\
        {\n    return T.slots[0].v;\n}\n",
    ));
    assert_eq!(w.code, "LG001", "{w}");
}

/// **LG001**: nothing to declare over.
#[test]
fn refuses_empty_unit() {
    let w = refuse_of("module test::leer {\n}\n");
    assert_eq!(w.code, "LG001", "{w}");
}

/// **LG002**: a float parameter has no `Ty` form.
#[test]
fn refuses_float_param() {
    let w = refuse_of(&einheit(
        "impl fn f(x : f32) -> u32 effects { pure } costs <= 1 ops { return 1; }\n",
    ));
    assert_eq!(w.code, "LG002", "{w}");
}

/// **LG003**: a call inside an `ensures` has no `Expr` form.
#[test]
fn refuses_call_in_ensures() {
    let w = refuse_of(&einheit(
        "impl fn g() -> u32 ensures g() == 1 effects { pure } costs <= 1 ops\n\
        {\n    return 1;\n}\n",
    ));
    assert_eq!(w.code, "LG003", "{w}");
}

/// **LG003**: an index outside `count` has no G form (held here, so the
/// guard check passes and the range check fires).
#[test]
fn refuses_index_out_of_range() {
    let w = refuse_of(&einheit(
        "impl fn f() -> u32 requires Held(L) effects { reads T.slots, locks L } costs <= 4 ops\n\
        {\n    return T.slots[9].v;\n}\n",
    ));
    assert_eq!(w.code, "LG003", "{w}");
}

/// **LG004**: `if` has no `Stmt` form here.
#[test]
fn refuses_wenn() {
    let w = refuse_of(&einheit(
        "impl fn f(x : u32) -> u32 effects { pure } costs <= 4 ops\n\
        {\n    if x == 1 { return 1; } else { return 0; }\n}\n",
    ));
    assert_eq!(w.code, "LG004", "{w}");
}

/// **Lane 174 -- `let` binds through `bind`**: a pure value binds anywhere,
/// including at the top level of an `Endblock`.
#[test]
fn accepts_let() {
    let text = export("lean_g", &tree(&einheit(
        "impl fn f() -> u32 effects { pure } costs <= 4 ops\n\
        {\n    let z = 1; return z;\n}\n",
    )))
    .expect("let must export");
    assert!(text.contains("(.bind"), "let travels as bind:\n{text}");
}

/// **LG004**: a call-valued `let` binds through `bindCall`, which only
/// blocks have -- at the top level of an `Endblock` it is refused by name.
#[test]
fn refuses_top_level_let_call() {
    let w = refuse_of(&einheit(
        "impl fn g() -> u32 effects { pure } costs <= 1 ops { return 1; }\n\
          impl fn f() -> u32 effects { pure } costs <= 8 ops\n\
        {\n    let z = g(); return z;\n}\n",
    ));
    assert_eq!(w.code, "LG004", "{w}");
}

/// **LG004**: `+=` has no `Stmt` form here.
#[test]
fn refuses_compound_assign() {
    let w = refuse_of(&einheit(
        "impl fn f() effects { writes T.slots } costs <= 4 ops\n\
        {\n    T.slots[0].v += 1;\n}\n",
    ));
    assert_eq!(w.code, "LG004", "{w}");
}

/// **LG004**: only the last statement may return.
#[test]
fn refuses_mid_return() {
    let w = refuse_of(&einheit(
        "impl fn f() -> u32 effects { pure } costs <= 4 ops\n\
        {\n    return 1; return 2;\n}\n",
    ));
    assert_eq!(w.code, "LG004", "{w}");
}

/// **LG004**: a call across different held sets has no `RufPasst` term
/// (`RufPasst.hh` names exactly the witnesses the caller holds -- the
/// checker accepts the helper, the model cannot type the call).
#[test]
fn refuses_held_mismatch() {
    let w = refuse_of(&einheit(
        "impl fn h() requires Held(L) effects { reads T.slots, locks L } costs <= 4 ops\n\
        {\n    return T.slots[0].v;\n}\n\
         impl fn mit() -> u32 requires Held(L) effects { reads T.slots, locks L } costs <= 8 ops\n\
        {\n    return h();\n}\n\
         impl fn ohne() -> u32 effects { pure } costs <= 8 ops\n\
        {\n    return h();\n}\n",
    ));
    assert_eq!(w.code, "LG004", "{w}");
}

/// **LG005**: a call nobody declares names nothing.
#[test]
fn refuses_unknown_call() {
    let w = refuse_of(&einheit(
        "impl fn f() effects { pure } costs <= 4 ops\n{\n    nope();\n}\n",
    ));
    assert_eq!(w.code, "LG005", "{w}");
}

/// **LG005**: a pointer at an undeclared table names nothing.
#[test]
fn refuses_unknown_table_param() {
    let w = refuse_of(&einheit(
        "impl fn f(p : ptr<normal, r> GibtEsNicht) effects { pure } costs <= 1 ops\n\
        {\n}\n",
    ));
    assert_eq!(w.code, "LG005", "{w}");
}

/// **LG005**: `concurrent` must name declared functions.
#[test]
fn refuses_concurrent_unknown() {
    let w = refuse_of(&einheit(
        "impl fn f() -> u32 effects { pure } costs <= 1 ops { return 1; }\n\
         concurrent { f, nope };\n",
    ));
    assert_eq!(w.code, "LG005", "{w}");
}

/// **Lane 156 -- the lock invariant family travels.** A lock with an
/// `invariant` clause exports `gS : SperrInv gD` (`orte` is the `protects`
/// set, `inv` the predicate over the snapshot) plus one `by decide` per
/// protected carrier for the guard half of `SperrInvOk`.
#[test]
fn export_lock_invariant_family() {
    let q = "module test::leang_inv {\n\
        table T count 4 { slot { v : u32, } }\n\
        table U count 4 { slot { w : u32, } }\n\
        lock L protects { T, U } rank 0 held <= 100 ops invariant T.slots[0].v + U.slots[1].w == 7;\n\
        impl fn f(t : ptr<normal, rw> T, u : ptr<normal, rw> U)\n\
        requires Held(L)\n\
        effects { writes t.slots, writes u.slots, locks L } costs <= 16 ops\n\
        {\n    t.slots[0].v = 3;\n    u.slots[1].w = 4;\n}\n\
        }\n";
    let text = export("leang_inv", &tree(q)).expect("must export");
    for teil in [
        "def gS : SperrInv gD where",
        "fun s =>",
        "gS.orte",
        "gD.braucht",
        "by decide",
    ] {
        assert!(text.contains(teil), "invariant export must contain {teil:?}:\n{text}");
    }
}

/// **Lane 156 -- `beispiele/118` exports**: the conserved-sum program prints
/// the family its checker duty stands beside.
#[test]
fn export_118_succeeds() {
    let text = export_file("118-sperrinvariante-erhaltung.gab");
    for teil in [
        "namespace G118_sperrinvariante_erhaltung",
        "def gS : SperrInv gD where",
        "by decide",
    ] {
        assert!(text.contains(teil), "118 export must contain {teil:?}");
    }
}

/// **LG003**: `old` in a lock invariant has no snapshot form.
#[test]
fn refuses_old_in_invariant() {
    let q = "module test::leang_old {\n\
        table T count 4 { slot { v : u32, } }\n\
        lock L protects { T } rank 0 held <= 100 ops invariant T.slots[0].v == old(T.slots[0].v);\n\
        impl fn f() -> u32 effects { pure } costs <= 1 ops { return 1; }\n\
        }\n";
    let w = export("leang_old", &tree(q)).expect_err("must refuse");
    assert_eq!(w.code, "LG003", "{w}");
}

/// **Lane 174 -- the subset (`RufPasst.hh`) with a floor**: the caller
/// holds `A`, the callee requires nothing and floors above it. The call
/// travels with explicit `hx`/`hb` proofs.
#[test]
fn accepts_subset_call_with_floor() {
    let q = "module test::leang_subset {\n\
        table T count 4 { slot { v : u32, } }\n\
        table U count 4 { slot { w : u32, } }\n\
        lock A protects { T } rank 0 held <= 100 ops;\n\
        lock C protects { U } rank 10 held <= 100 ops;\n\
        impl fn h(u : ptr<normal, rw> U)\n\
        effects { writes u.slots, locks C } costs <= 4 ops\n\
        {\n    locks C {\n        u.slots[0].w = 1;\n}\n}\n\
        impl fn caller(t : ptr<normal, rw> T, u : ptr<normal, rw> U)\n\
        requires Held(A)\n\
        effects { writes t.slots, writes u.slots, locks A, locks C } costs <= 16 ops\n\
        {\n    h(u);\n    locks C {\n        t.slots[0].v = 2;\n}\n}\n\
        }\n";
    let text = export("leang_subset", &tree(q)).expect("subset call must export");
    for teil in [
        "boden := some 10",
        "gHp_caller",
        "hx := fun L hL hn => by cases L",
        "hb := fun c h => by have hV",
    ] {
        assert!(text.contains(teil), "subset export must contain {teil:?}:\n{text}");
    }
}

/// **LG004 (`RufPasst.hx`)**: an extra lock at or above the callee's floor
/// has no proof -- the checker accepts the call, the model cannot type it.
#[test]
fn refuses_extra_above_floor() {
    let q = "module test::leang_hx {\n\
        table T count 4 { slot { v : u32, } }\n\
        table U count 4 { slot { w : u32, } }\n\
        lock A protects { T } rank 0 held <= 100 ops;\n\
        lock C protects { U } rank 10 held <= 100 ops;\n\
        impl fn h(u : ptr<normal, rw> U)\n\
        effects { writes u.slots, locks C } costs <= 4 ops\n\
        {\n    locks C {\n        u.slots[0].w = 1;\n}\n}\n\
        impl fn caller(t : ptr<normal, rw> T, u : ptr<normal, rw> U)\n\
        requires Held(A), Held(C)\n\
        effects { writes t.slots, writes u.slots, locks A, locks C } costs <= 16 ops\n\
        {\n    h(u);\n}\n\
        }\n";
    let w = export("leang_hx", &tree(q)).expect_err("must refuse");
    assert_eq!(w.code, "LG004", "{w}");
    assert!(w.message.contains("hx"), "{w}");
}

/// **LG004 (`RufPasst.hh`)**: a callee requiring a lock its caller does not
/// hold still has no term -- the subset relaxes one direction only.
#[test]
fn refuses_callee_needing_more() {
    let w = refuse_of(&einheit(
        "impl fn h() requires Held(L) effects { reads T.slots, locks L } costs <= 4 ops\n\
        {\n    return T.slots[0].v;\n}\n\
          impl fn ohne() -> u32 effects { pure } costs <= 8 ops\n\
        {\n    return h();\n}\n",
    ));
    assert_eq!(w.code, "LG004", "{w}");
}

/// **Lane 174 -- `locks L { … }`**: the 119 shape (taking without holding
/// by signature) travels as `Stmt.locks`, with the floor on the signature.
/// The old signature-held footprint does not apply, so no `fussOrtGB`
/// check travels -- and none is guessed.
#[test]
fn accepts_locks_block() {
    let q = "module test::leang_locks {\n\
        table T count 4 { slot { v : u32, } }\n\
        lock L protects { T } rank 0 held <= 100 ops;\n\
        impl fn f(t : ptr<normal, rw> T)\n\
        effects { writes t.slots, locks L } costs <= 16 ops\n\
        {\n    locks L {\n        t.slots[0].v = 3;\n}\n}\n\
        }\n";
    let text = export("leang_locks", &tree(q)).expect("locks must export");
    for teil in [
        "(.locks",
        "boden := some 0",
        "example : programmImFragmentG gP gFs = true := by decide",
    ] {
        assert!(text.contains(teil), "locks export must contain {teil:?}:\n{text}");
    }
    assert!(
        !text.contains("fussOrtGB gP gFs = true"),
        "locks export prints no guessed footprint check:\n{text}"
    );
}

/// **Lane 174 -- `beispiele/119` exports**: the lock-invariant program that
/// takes instead of holding.
#[test]
fn export_119_succeeds() {
    let text = export_file("119-sperrinvariante-bloecke.gab");
    for teil in [
        "namespace G119_sperrinvariante_bloecke",
        "(.locks",
        "example : programmImFragmentG gP gFs = true := by decide",
    ] {
        assert!(text.contains(teil), "119 export must contain {teil:?}");
    }
}

/// **LG004**: shared taking has no `Stmt` form.
#[test]
fn refuses_shared_locks() {
    let q = "module test::leang_shared {\n\
        table T count 4 { slot { v : u32, } }\n\
        lock L protects { T } rank 0 held <= 100 ops;\n\
        impl fn f(t : ptr<normal, rw> T)\n\
        requires Held(L)\n\
        effects { writes t.slots, locks L } costs <= 16 ops\n\
        {\n    locks shared L {\n        t.slots[0].v = 3;\n}\n}\n\
        }\n";
    let w = export("leang_shared", &tree(q)).expect_err("must refuse");
    assert_eq!(w.code, "LG004", "{w}");
}

/// **LG004**: taking a lock of no higher rank than everything held (`H006`,
/// decided here).
#[test]
fn refuses_locks_rank_violation() {
    let q = "module test::leang_rang {\n\
        table T count 4 { slot { v : u32, } }\n\
        lock A protects { T } rank 1 held <= 100 ops;\n\
        lock B protects { T } rank 0 held <= 100 ops;\n\
        impl fn f(t : ptr<normal, rw> T)\n\
        requires Held(A)\n\
        effects { writes t.slots, locks A, locks B } costs <= 16 ops\n\
        {\n    locks B {\n        t.slots[0].v = 3;\n}\n}\n\
        }\n";
    let w = export("leang_rang", &tree(q)).expect_err("must refuse");
    assert_eq!(w.code, "LG004", "{w}");
}

/// **Lane 174 -- `if`/`else` travels as `Stmt.ite`**: a tail `if` with
/// return-free branches, and a mid-body `if` whose branch returns through
/// `Stmt.ret` (the continuation is real, so nothing is invented).
#[test]
fn accepts_wenn() {
    let text = export("lean_g", &tree(&einheit(
        "impl fn f(x : u32) effects { pure } costs <= 8 ops\n\
        {\n    let z = x;\n    if z == 1 {\n        let w = z;\n    } else {\n        let w = 2;\n    }\n}\n",
    )))
    .expect("if must export");
    assert!(text.contains("(.ite"), "if travels as ite:\n{text}");
    let text = export("lean_g", &tree(&einheit(
        "impl fn g(x : u32) -> u32 effects { pure } costs <= 8 ops\n\
        {\n    if x == 1 {\n        return 1;\n    }\n    let z = 2;\n    return z;\n}\n",
    )))
    .expect("if with a returning branch must export");
    assert!(text.contains("(.ite"), "branch return travels:\n{text}");
}

/// **LG003**: a non-literal index in a lock invariant has no snapshot form.
#[test]
fn refuses_param_index_in_invariant() {
    let q = "module test::leang_idx {\n\
        table T count 4 { slot { v : u32, } }\n\
        lock L protects { T } rank 0 held <= 100 ops invariant T.slots[k].v == 1;\n\
        impl fn f() -> u32 effects { pure } costs <= 1 ops { return 1; }\n\
        }\n";
    let w = export("leang_idx", &tree(q)).expect_err("must refuse");
    assert_eq!(w.code, "LG003", "{w}");
}

/// **Lane 174 -- `traverse i over slots of T` travels as `Stmt.traverse`**,
/// the binder as the model's loop index.
#[test]
fn accepts_traverse_slots() {
    let q = "module test::leang_trav {\n\
        table T count 4 { slot { v : u32, } }\n\
        lock L protects { T } rank 0 held <= 100 ops;\n\
        impl fn f(t : ptr<normal, rw> T)\n\
        requires Held(L)\n\
        effects { writes t.slots, locks L } costs <= 64 ops\n\
        {\n    traverse i over slots of T by unvisited\n\
        {\n        t.slots[i].v = 0;\n}\n}\n\
        }\n";
    let text = export("leang_trav", &tree(q)).expect("traverse must export");
    assert!(text.contains("(.traverse"), "traverse travels:\n{text}");
}

/// **Lane 207 -- `traverse` over a pointer resolves to ITS table**
/// (positive probe): with two tables in scope, `over slots of t` is the
/// domain of `T`, not of `U`. This shape was `LG006` before the pointer
/// arm; the refusal now holds only where the name is no pointer.
#[test]
fn traverse_pointer_domain_resolves_to_its_table() {
    let q = "module test::leang_travp {\n\
        table T count 4 { slot { v : u32, } }\n\
        lock L protects { T } rank 0 held <= 100 ops;\n\
        impl fn f(t : ptr<normal, rw> T)\n\
        requires Held(L)\n\
        effects { writes t.slots, locks L } costs <= 64 ops\n\
        {\n    traverse i over slots of t by unvisited\n\
        {\n        t.slots[i].v = 0;\n}\n}\n\
        }\n";
    let text = export("leang_travp", &tree(q)).expect("pointer-domain traverse must export");
    assert!(
        text.contains("(.traverse GTab.T"),
        "the domain is the table the pointer names:\n{text}"
    );
}

/// **LG006**: `retry` and `forever` have no form in this fragment (the
/// spelling is the corpus shape of `beispiele/66`).
#[test]
fn refuses_retry_forever() {
    let w = refuse_of(&einheit(
        "impl fn oops() effects { pure } costs <= 1 ops { }\n\
          impl fn f(b : bool) effects { pure } costs <= 70 ops\n\
        {\n    retry warten until b\n\
        bounded 64 ops\n\
        on_exceeded oops\n\
        effects { pure }\n\
        {\n    }\n}\n",
    ));
    assert_eq!(w.code, "LG006", "{w}");
}

/// **Lane 174 -- `-> T or R` pins the case count**: `gruende` is the
/// declaration's cases, and a valueless body still travels.
#[test]
fn accepts_reason_channel() {
    let q = "module test::leang_else {\n\
        table T count 4 { slot { v : u32, } }\n\
        reason E {\n    Leer = 1 \"leer\"\n    Voll = 2 \"voll\"\n    exhaustive\n}\n\
        impl fn g() -> u32 or E effects { pure } costs <= 1 ops { return 1; }\n\
        impl fn f() -> u32 effects { pure } costs <= 8 ops\n\
        {\n    return 0;\n}\n\
        }\n";
    // The shape pins the reason count on the signature; the call itself
    // lives in a block below.
    let text = export("leang_else", &tree(q)).expect("reason fn must export");
    assert!(text.contains("gruende := 2"), "reason count travels:\n{text}");
}

/// **Lane 174 -- `let … else` over a call inside a branch**: the value
/// binds through `bindCallElse`, the `else` ends in a `return`.
#[test]
fn accepts_let_else_call() {
    let q = "module test::leang_else2 {\n\
        table T count 4 { slot { v : u32, } }\n\
        reason E {\n    Leer = 1 \"leer\"\n    Voll = 2 \"voll\"\n    exhaustive\n}\n\
        impl fn g() -> u32 or E effects { pure } costs <= 1 ops { return 1; }\n\
        impl fn f(x : u32) -> u32 effects { pure } costs <= 8 ops\n\
        {\n    if x == 0 {\n        let y = g() else (e) { return 2; }\n        return y;\n    }\n    let z = 0;\n    return z;\n}\n\
        }\n";
    let text = export("leang_else2", &tree(q)).expect("let-else must export");
    assert!(text.contains("(.bindCallElse"), "let-else travels:\n{text}");
}

/// **LG007**: `let … else` over a place has no form here.
#[test]
fn refuses_let_else_place() {
    let q = "module test::leang_elsep {\n\
        table T count 4 { slot { v : u32, } }\n\
        reason E {\n    Leer = 1 \"leer\"\n    Voll = 2 \"voll\"\n    exhaustive\n}\n\
        impl fn g() -> u32 or E effects { pure } costs <= 1 ops { return 1; }\n\
        impl fn f(x : u32) -> u32 effects { pure } costs <= 8 ops\n\
        {\n    if x == 0 {\n        let y = T.slots[0].v else (e) { return 2; }\n        return y;\n    }\n    let z = 0;\n    return z;\n}\n\
        }\n";
    let w = export("leang_elsep", &tree(q)).expect_err("must refuse");
    assert_eq!(w.code, "LG007", "{w}");
}

/// **Lane 174 -- `return` of an arithmetic expression**: the computed
/// range widens to the result.
#[test]
fn accepts_return_arith() {
    let text = export("lean_g", &tree(&einheit(
        "impl fn f(a : u32 in 0 .. 100, b : u32 in 0 .. 100) -> u32 effects { pure } costs <= 8 ops\n\
        {\n    return a + b;\n}\n",
    )))
    .expect("arithmetic return must export");
    assert!(text.contains("(.add"), "addition travels:\n{text}");
}

/// **LG003**: a call in `return` position has no `Expr` form (`Endblock`
/// binds no calls).
#[test]
fn refuses_return_call() {
    let w = refuse_of(&einheit(
        "impl fn g() -> u32 effects { pure } costs <= 1 ops { return 1; }\n\
          impl fn f() -> u32 effects { pure } costs <= 8 ops\n\
        {\n    return g();\n}\n",
    ));
    assert_eq!(w.code, "LG003", "{w}");
}

/// **Lane 174 -- `bool` travels**: a `bool` field reads in conditions and
/// returns, and `true`/`false` assign.
#[test]
fn accepts_bool_field() {
    let q = "module test::leang_bool {\n\
        table T count 4 { slot { v : u32, b : bool, } }\n\
        impl fn f(t : ptr<normal, rw> T, i : index into T) -> bool\n\
        effects { reads t.slots, writes t.slots } costs <= 8 ops\n\
        {\n    if t.slots[i].b {\n        return t.slots[i].b;\n    }\n    t.slots[i].b = true;\n    return t.slots[i].b;\n}\n\
        }\n";
    let text = export("leang_bool", &tree(q)).expect("bool must export");
    for teil in ["| .T, .b => (.bool)", "(.ite", ".wahr"] {
        assert!(text.contains(teil), "bool export must contain {teil:?}:\n{text}");
    }
}

/// **Lane 174 -- `beispiele/15` and `16` export**: the `own`-pointer reader
/// and the `bool`-field reader/writer with no other blocker.
#[test]
fn export_15_16_succeed() {
    for name in ["15-own-traegt-beide-rechte.gab", "16-by-ops-am-feld.gab"] {
        let text = export_file(name);
        assert!(
            text.contains("example : programmImFragmentG gP gFs = true := by decide"),
            "{name} exports its fragment check"
        );
    }
}

/// **Lane 174 -- bit operations travel with the width off the operand**:
/// `~` is the complement over the storage width, `^` the xor beside it.
#[test]
fn accepts_bitops() {
    let text = export("lean_g", &tree(&einheit(
        "impl fn f(m : u8) -> u8 effects { pure } costs <= 4 ops\n\
        {\n    return ~m;\n}\n",
    )))
    .expect("complement must export");
    assert!(text.contains("(.bxor 8"), "complement travels:\n{text}");
}

/// **Lane 174 -- conversions and limit words travel**: `u64(x)` is the
/// widening, `u32::max` its number.
#[test]
fn accepts_conversion_grenzwort() {
    let text = export("lean_g", &tree(&einheit(
        "impl fn f(a : u32, b : u32) -> u64 effects { pure } costs <= 5 ops\n\
        {\n    return u64(a);\n}\n",
    )))
    .expect("conversion must export");
    assert!(text.contains(".int 0 18446744073709551615"), "u64 travels:\n{text}");
}

/// **Lane 174 -- `beispiele/62`, `69` and `73` export**: xor/mask/compare,
/// the conversion-or-combination over bare words, and the sugar widths --
/// all three tableless (pure computation over parameters, `Tab := Empty`).
#[test]
fn export_62_69_73_succeed() {
    for name in [
        "62-grenzwort-im-ausdruck.gab",
        "69-integer-conversion.gab",
        "73-sugar-widths.gab",
    ] {
        let text = export_file(name);
        assert!(
            text.contains("example : programmImFragmentG gP gFs = true := by decide"),
            "{name} exports its fragment check"
        );
    }
}

/// **Lane 174 -- a tableless unit travels with `Tab := Empty`**, never a
/// fresh empty inductive.
#[test]
fn accepts_tableless_unit() {
    let text = export("lean_g", &tree(
        "module test::leer_tab {\n\
        impl fn f(a : u32) -> u32 effects { pure } costs <= 2 ops { return a; }\n\
        }\n",
    ))
    .expect("tableless unit must export");
    assert!(text.contains("abbrev GTab := Empty"), "empty Tab travels:\n{text}");
}

/// **LG004**: a bare call of a reason-carrying function has no form (its
/// `hr` needs `gruende = 0`) -- `let … else` has it.
#[test]
fn refuses_bare_call_of_reason_fn() {
    let q = "module test::leang_rruf {\n\
        table T count 4 { slot { v : u32, } }\n\
        reason E {\n    Leer = 1 \"leer\"\n    Voll = 2 \"voll\"\n    exhaustive\n}\n\
        impl fn g() -> u32 or E effects { pure } costs <= 1 ops { return 1; }\n\
        impl fn f() -> u32 effects { pure } costs <= 8 ops\n\
        {\n    g();\n    return 0;\n}\n\
        }\n";
    let w = export("leang_rruf", &tree(q)).expect_err("must refuse");
    assert_eq!(w.code, "LG004", "{w}");
}

/// **Lane 198 -- the program as ONE declaration.** Beside `gP` the export
/// assembles `gE : Zielsatz.Einheit gD`: the lock/carrier member lists, the
/// zero-memory `gSp0` and the declared starts (104 declares none).
#[test]
fn export_104_carries_the_unit() {
    let text = export_file("104-referenz.gab");
    for teil in [
        "import Grammatik.Zielsatz.Spec",
        "def gLs : List gD.Lock",
        "def gCs : List (gD.Tab ⊕ gD.Glob)",
        "def gSp0 : Speicher gD",
        "def gE : Zielsatz.Einheit gD where",
        "  P := gP",
        "  S := gS",
        "  Q := fun _ _ _ => true",
        "  starts := []",
        "  sp0 := gSp0",
    ] {
        assert!(text.contains(teil), "104 export must contain {teil:?}");
    }
}

/// **Lane 198 -- 104's `requires` is `Held`-only**, so every arm stays
/// `.wahr`: the signature-held set travels in the signature, never in a
/// `gReq` definition.
#[test]
fn export_104_requires_stays_true() {
    let text = export_file("104-referenz.gab");
    for teil in ["    | .einzahlen => .wahr", "    | .lies => .wahr"] {
        assert!(text.contains(teil), "104 export must contain {teil:?}");
    }
    assert!(
        !text.contains("gReq_"),
        "Held-only requires travel no gReq definition:\n{text}"
    );
}

/// **Lane 198 -- a value `requires` travels as `gReq`** (positive probe):
/// the clause over the slot reads exactly like an `ensures`, over the
/// parameters alone. (Over an unprotected table: a protected one still
/// needs its guard, `LG004`.)
#[test]
fn requires_value_travels() {
    let q = "module test::leang_req {\n\
        table U count 4 { slot { w : u32, } }\n\
        impl fn f() -> u32 requires U.slots[0].w == 7 ensures result == U.slots[0].w\n\
        effects { reads U.slots } costs <= 8 ops\n\
        {\n    return U.slots[0].w;\n}\n\
        }\n";
    let text = export("leang_req", &tree(q)).expect("value requires must export");
    for teil in ["def gReq_f", "| .f => gReq_f"] {
        assert!(text.contains(teil), "value requires must travel as {teil:?}:\n{text}");
    }
}

/// **Lane 198 -- `Held` beside a value clause still names the signature
/// set** (positive probe): the lock travels in `haelt`, the value in
/// `gReq_f`.
#[test]
fn requires_held_and_value_travel() {
    let text = export("lean_g", &tree(&einheit(
        "impl fn f() requires Held(L), T.slots[0].v == 7\n\
        effects { reads T.slots, locks L } costs <= 4 ops\n\
        {\n}\n",
    )))
    .expect("mixed requires must export");
    for teil in ["haelt := [GLock.L]", "def gReq_f", "| .f => gReq_f"] {
        assert!(text.contains(teil), "mixed requires must travel as {teil:?}:\n{text}");
    }
}

/// **Lane 198, LG003 -- a `requires` with no `Expr` form is refused by
/// name** (poison probe): a call travels in no contract.
#[test]
fn refuses_call_in_requires() {
    let w = refuse_of(&einheit(
        "impl fn g() -> u32 effects { pure } costs <= 1 ops { return 1; }\n\
        impl fn f() -> u32 requires g() == 1 effects { pure } costs <= 1 ops { return 1; }\n",
    ));
    assert_eq!(w.code, "LG003", "{w}");
}

/// **Lane 198, LG003 -- `result` has no form in a `requires`** (poison
/// probe): the context is the parameters alone.
#[test]
fn refuses_result_in_requires() {
    let w = refuse_of(&einheit(
        "impl fn f() -> u32 requires result == 7 effects { pure } costs <= 1 ops { return 7; }\n",
    ));
    assert_eq!(w.code, "LG003", "{w}");
}

/// **Lane 198 -- `concurrent` members travel as declared starts**
/// (positive probe): every start is parameterless, its argument list
/// `.nil`.
#[test]
fn concurrent_members_travel_to_starts() {
    let text = export("lean_g", &tree(&einheit(
        "impl fn f() -> u32 effects { pure } costs <= 1 ops { return 1; }\n\
        impl fn g() -> u32 effects { pure } costs <= 1 ops { return 2; }\n\
        concurrent { f, g };\n",
    )))
    .expect("concurrent starts must export");
    assert!(
        text.contains("starts := [⟨g_f, .nil⟩, ⟨g_g, .nil⟩]"),
        "starts travel with .nil arguments:\n{text}"
    );
}

/// **Lane 198 -- 108's starts travel**: the two lock-free readers are the
/// declared starts of the unit.
#[test]
fn export_108_starts_travel() {
    let text = export_file("108-disjoint-start-locks.gab");
    assert!(
        text.contains("starts := [⟨g_read_a, .nil⟩, ⟨g_read_c, .nil⟩]"),
        "108 starts travel:\n{text}"
    );
}

/// **Lane 198, LG001 -- a start with parameters has no start-argument
/// form** (poison probe): the declaration carries no arguments.
#[test]
fn refuses_start_with_params() {
    let w = refuse_of(&einheit(
        "impl fn f(x : u32) -> u32 effects { pure } costs <= 1 ops { return x; }\n\
        concurrent { f };\n",
    ));
    assert_eq!(w.code, "LG001", "{w}");
}

/// **Lane 198, LG003 -- an integer range holding no zero has no `sp0`
/// value** (poison probe): the declared initial memory is the zero memory.
#[test]
fn refuses_sp0_outside_zero() {
    let q = "module test::leang_sp0 {\n\
        type P = u32 in 1 .. 10;\n\
        table T count 4 { slot { v : P, } }\n\
        impl fn f() -> u32 effects { pure } costs <= 1 ops { return 1; }\n\
        }\n";
    let w = export("leang_sp0", &tree(q)).expect_err("must refuse");
    assert_eq!(w.code, "LG003", "{w}");
}

/// **Lane 198 -- an `entry` dispatch root travels as a declared start**
/// (positive probe): the vector, the registers and the steps have no G
/// form, only the dispatched function travels.
#[test]
fn entry_root_travels_to_starts() {
    let q = "module test::leang_entry {\n\
        impl fn root() effects { pure } costs <= 1 ops { }\n\
        entry e vector 0x80 arch x86_64 {\n\
        regs in { } regs out { } preserves { rbx } clobbers { rcx }\n\
        stack ka per cpu nested never\n\
        dispatch test::leang_entry::root;\n}\n\
        }\n";
    let text = export("leang_entry", &tree(q)).expect("entry root must export");
    assert!(
        text.contains("starts := [⟨g_root, .nil⟩]"),
        "entry root travels:\n{text}"
    );
}

// ---------------------------------------------------------------------------
// `tagged type` -- `Ty.sum` (2026-09-15)
//
// The type declaration used to be `LG001 type X has no G form`, and that
// stopped TEN corpus programs before the exporter had looked at a single
// statement. `Ty.sum`, `Expr.fall`, `Stmt.onTag` and `Arms` are all in
// `Syntax.lean`/`Typen.lean`; what is NOT there -- a payload that is not one
// integer range, a case list that is empty -- is refused BY NAME below.
// ---------------------------------------------------------------------------

/// **A `tagged` parameter, its construction and its `match`** (positive
/// probe): the type is `Ty.sum`, the constructor `Expr.fall` and the match
/// `Stmt.onTag` with one arm per case in DECLARATION order.
#[test]
fn tagged_type_travels_as_sum() {
    let q = "module test::leang_tag {\n\
        tagged type N = { Leer, Kurz(u32 in 0 .. 100) };\n\
        impl fn baue(k : bool, x : u32 in 0 .. 100) -> N effects { pure } costs <= 8 ops {\n\
        if k { return Kurz(x); }\n\
        return Leer;\n}\n\
        impl fn nimm(m : N) -> u32 in 0 .. 100 effects { pure } costs <= 8 ops {\n\
        match m { Leer => { return 0; } Kurz(v) => { return v; } }\n\
        return 0;\n}\n\
        }\n";
    let text = export("leang_tag", &tree(q)).expect("tagged unit must export");
    for teil in [
        "params := [(.sum [none, some (0, 100)])]",
        "erg := some ((.sum [none, some (0, 100)]))",
        ".fall [none, some (0, 100)] ⟨1, by decide⟩ (.zahl",
        ".fall [none, some (0, 100)] ⟨0, by decide⟩ .keine",
        ".onTag",
    ] {
        assert!(text.contains(teil), "tagged export must contain {teil:?}:\n{text}");
    }
}

/// **A `tagged` slot field and a `tagged` static** (positive probe): the
/// field type is `Ty.sum`, and `gSp0` starts the slot at case 0 and the
/// global at the case its `static` names.
#[test]
fn tagged_slot_and_static_travel() {
    let q = "module test::leang_tagm {\n\
        tagged type N = { Leer, Kurz(u32) };\n\
        table T count 2 { slot { was : N, } }\n\
        static ANFANG : N = Kurz(5);\n\
        impl fn lies(t : ptr<normal, r> T, i : index into T) -> u32\n\
        effects { reads t.slots } costs <= 8 ops {\n\
        match t.slots[i].was { Leer => { return 0; } Kurz(v) => { return v; } }\n\
        return 0;\n}\n\
        }\n";
    let text = export("leang_tagm", &tree(q)).expect("tagged carrier unit must export");
    for teil in [
        "| .T, .was => ((.sum [none, some (0, 4294967295)]))",
        "| .T, .was => ⟨⟨0, by decide⟩, ()⟩",
        "| .ANFANG => ⟨⟨1, by decide⟩, ⟨5, by decide, by decide⟩⟩",
        ".onTag (Expr.durch",
    ] {
        assert!(text.contains(teil), "tagged carrier export must contain {teil:?}:\n{text}");
    }
}

/// **LG002 -- a payload that is no integer range has no `Nutzlast`** (poison
/// probe): `Nutzlast` is `Option (Int × Int)`, so a `bool` payload has none.
#[test]
fn refuses_tagged_payload_without_range() {
    let q = "module test::leang_tagb {\n\
        tagged type N = { Leer, Flag(bool) };\n\
        impl fn f() -> u32 effects { pure } costs <= 1 ops { return 1; }\n\
        }\n";
    let w = export("leang_tagb", &tree(q)).expect_err("must refuse");
    assert_eq!(w.code, "LG002", "{w}");
    assert!(w.message.contains("Flag") && w.message.contains("Nutzlast"), "{w}");
}

/// **A `tagged` type with no case never reaches the exporter** -- the READER
/// refuses `{ }` with `P035` ("neither a record nor a sum type"), and the
/// item is dropped before `collect` sees it. The exporter's own LG002 guard
/// for the empty case list is therefore a SECOND reader of the same rule, and
/// it is what makes `cases[0]` (the `sp0` value of a `tagged` slot) total.
/// *Measured, not assumed: this test exists because the guard's poison probe
/// exported cleanly and the reason was upstream.*
#[test]
fn empty_tagged_type_is_refused_by_the_reader() {
    let q = "module test::leang_tage {\n\
        tagged type N = { };\n\
        impl fn f() -> u32 effects { pure } costs <= 1 ops { return 1; }\n\
        }\n";
    let (_, absagen) = gabbro_syntax::lies("leang_tage", q);
    assert!(
        format!("{absagen:?}").contains("P035"),
        "the reader refuses an empty sum before the exporter sees it: {absagen:?}"
    );
}

/// **LG001 -- `linear` and `ghost` still refuse** (poison probe): the
/// `tagged` arm must not have opened a door for the resource marks, which
/// are `D.Marke`/`Res.marke` and not a `Ty`.
#[test]
fn linear_type_still_refuses_after_tagged() {
    for q in [
        "module test::leang_lin { linear ghost type M;\n\
         impl fn f() -> u32 effects { pure } costs <= 1 ops { return 1; } }\n",
        "module test::leang_ord { linear ghost type M order { a, b };\n\
         impl fn f() -> u32 effects { pure } costs <= 1 ops { return 1; } }\n",
    ] {
        let w = export("leang_lin", &tree(q)).expect_err("must refuse");
        assert_eq!(w.code, "LG001", "{w}");
    }
}

/// **A `match` over an `option` is not a `match` over a tagged value**
/// (poison probe): `Stmt.onOption` is its form and is not built here, and
/// the refusal must name a form rather than fall through the tagged arm.
#[test]
fn refuses_option_match_by_name() {
    let q = "module test::leang_opt {\n\
        table T count 4 { slot { n : option index into T, } }\n\
        impl fn f(t : ptr<normal, r> T, i : index into T) -> u32\n\
        effects { reads t.slots } costs <= 8 ops {\n\
        match t.slots[i].n { None => { return 0; } Some(j) => { return 1; } }\n\
        return 0;\n}\n\
        }\n";
    let w = export("leang_opt", &tree(q)).expect_err("must refuse");
    assert!(
        w.message.contains("onOption") || w.code == "LG002",
        "an option match names its own form: {w}"
    );
}

// ---------------------------------------------------------------------------
// The record -- a CARRIER (`Tab` with `count 1`), never a value (2026-09-15)
//
// `Syntax.lean` §1/§9: "ein `format` und ein Verbund sind Tabellen mit
// `count 1`". That half is class (i) and is built. A record as a VALUE is
// class (ii): `Typen.lean` §1 lists every `Ty` there is, and none of them is
// a product -- so `-> Completion` and `let c = fertig(k, 7)` name no type,
// and no exporter work makes them one.
// ---------------------------------------------------------------------------

/// **A record behind a pointer travels** (positive probe): the record is a
/// table of `count 1`, `p->f` is `Expr.durch` at index 0, `p->f = e` is
/// `Stmt.assignDurch`, and a bare `writes p` is the table's write right.
#[test]
fn record_travels_as_table_of_count_one() {
    let q = "module test::leang_rec {\n\
        type Zelle = { wert : u32 in 0 .. 1000, fertig : bool, };\n\
        impl fn lies(p : ptr<normal, r> Zelle) -> u32 in 0 .. 1000\n\
        effects { reads p } costs <= 2 ops { return p->wert; }\n\
        impl fn setze(p : ptr<normal, rw> Zelle, v : u32 in 0 .. 1000)\n\
        effects { writes p } costs <= 4 ops { p->wert = v; p->fertig = true; }\n\
        }\n";
    let text = export("leang_rec", &tree(q)).expect("record carrier must export");
    for teil in [
        "| Zelle",
        "count := fun | .Zelle => 1",
        "| .Zelle, .wert => ((.int 0 1000)) | .Zelle, .fertig => (.bool)",
        "Expr.durch",
        ".assignDurch",
    ] {
        assert!(text.contains(teil), "record export must contain {teil:?}:\n{text}");
    }
}

/// **The footprint mirror must SEE `p->f`** -- and this test exists because
/// Lean found that it did not. With the record access uncounted, `fuss_holds`
/// said the old footprint check passes and the export printed
/// `example : fussOrtGB gP gFs = true := by decide`, which Lean DISPROVED.
/// A guarded record must therefore print the claim, and an unguarded shared
/// one must not.
#[test]
fn record_access_counts_in_the_footprint_mirror() {
    let q = "module test::leang_recf {\n\
        type Zelle = { wert : u32, };\n\
        impl fn lies(p : ptr<normal, r> Zelle) -> u32\n\
        effects { reads p } costs <= 2 ops { return p->wert; }\n\
        impl fn setze(p : ptr<normal, rw> Zelle, v : u32)\n\
        effects { writes p } costs <= 4 ops { p->wert = v; }\n\
        }\n";
    let text = export("leang_recf", &tree(q)).expect("record carrier must export");
    assert!(
        !text.contains("example : fussOrtGB gP gFs = true"),
        "a written, lock-free record is not in the old footprint fragment, and the CLAIM must \
         not be printed (the header may still name the check and say why):\n{text}"
    );
}

/// **LG002 -- a record as a VALUE is class (ii)** (poison probe): the result
/// type, a parameter and a `let` annotation each name the record, and each
/// refusal says that `Ty` has no product former.
#[test]
fn refuses_record_as_a_value_by_name() {
    let kopf = "module test::leang_recv {\n\
        type C = { id : u32, len : u32, };\n";
    for (extra, wo) in [
        ("impl fn f(k : u32) -> C effects { pure } costs <= 4 ops { return C(id: k, len: 1); }\n",
         "the result of f"),
        ("impl fn g(c : C) -> u32 effects { pure } costs <= 4 ops { return 1; }\n",
         "a parameter of g"),
    ] {
        let w = export("leang_recv", &tree(&format!("{kopf}{extra}}}\n"))).expect_err("must refuse");
        assert_eq!(w.code, "LG002", "{w}");
        assert!(w.message.starts_with(wo), "the refusal names the position: {w}");
        assert!(
            w.message.contains("no product") && w.message.contains("count 1"),
            "the refusal names the class-(ii) reason AND the carrier form that does work: {w}"
        );
    }
}

/// **LG002 -- a record field that is no `Ty` is refused BY NAME** (poison
/// probe): an array field and a function-pointer field are the two shapes
/// the corpus actually has, and both name the field and the rule.
#[test]
fn refuses_record_field_without_ty() {
    for q in [
        "module test::leang_recA { const K = 4;\n\
         type T = { bytes : [u8; K], len : u32, };\n\
         impl fn f(p : ptr<normal, r> T) -> u32 effects { reads p } costs <= 2 ops \
         { return p->len; } }\n",
        "module test::leang_recB {\n\
         type D = { senden : fn(u8) effects { pure } costs <= 4 ops, };\n\
         impl fn f(p : ptr<normal, r> D) -> u32 effects { reads p } costs <= 2 ops \
         { return 1; } }\n",
    ] {
        let w = export("leang_rec_f", &tree(q)).expect_err("must refuse");
        assert_eq!(w.code, "LG002", "{w}");
        assert!(w.message.contains("of record"), "the refusal names the field and its record: {w}");
    }
}

/// **A `->` through a pointer to a real TABLE stays refused** (poison probe):
/// a table has more than one slot, so the access must name it. The record arm
/// must not have turned every table pointer into a one-slot read.
#[test]
fn refuses_arrow_through_a_table_pointer() {
    let q = "module test::leang_recT {\n\
        table T count 4 { slot { v : u32, } }\n\
        impl fn f(p : ptr<normal, r> T) -> u32 effects { reads p.slots } costs <= 2 ops \
        { return p->v; } }\n";
    let w = export("leang_recT", &tree(q)).expect_err("must refuse");
    assert_eq!(w.code, "LG003", "{w}");
    assert!(w.message.contains("no record"), "{w}");
    assert!(w.message.contains(".slots[i]."), "the refusal names the spelling that works: {w}");
}

/// **LG001 -- the linear family is refused BY NAME, with its fields**
/// (poison probe): the type arm was the last catch-all of its kind, and
/// every shape must now say what the specification would carry it as.
#[test]
fn linear_family_names_its_fields() {
    for (q, wort) in [
        ("module test::l1 { linear type M;\n\
          impl fn f() -> u32 effects { pure } costs <= 1 ops { return 1; } }\n", "D.Marke"),
        ("module test::l2 { linear ghost type M order { a, b };\n\
          impl fn f() -> u32 effects { pure } costs <= 1 ops { return 1; } }\n", "Stmt.advances"),
    ] {
        let w = export("l", &tree(q)).expect_err("must refuse");
        assert_eq!(w.code, "LG001", "{w}");
        assert!(w.message.contains(wort), "the refusal names the field: {w}");
        assert!(
            w.message.contains("RESOURCE"),
            "and it says WHY a mark is not a `Ty`: {w}"
        );
    }
}

/// **LG002 -- a float alias names `Ty.fl`** (poison probe): the alias arm
/// used to say only "is not an integer range" over five different shapes.
#[test]
fn float_alias_names_its_form() {
    let q = "module test::lf { type A = f64 in 0.0 .. 1.0;\n\
        impl fn f() -> u32 effects { pure } costs <= 1 ops { return 1; } }\n";
    let w = export("lf", &tree(q)).expect_err("must refuse");
    assert_eq!(w.code, "LG002", "{w}");
    assert!(w.message.contains("Ty.fl"), "{w}");
}

/// **The three corpus programs the `tagged` work moved into sieve (b)**
/// (positive probe, on the files): a construction unit, a file-scope
/// initialiser and the carrier/parameter unit.
#[test]
fn tagged_corpus_programs_export() {
    for name in [
        "120-tagged-construction.gab",
        "121-tagged-static-init.gab",
        "34-markierter-wert.gab",
    ] {
        let text = export_file(name);
        assert!(text.contains(".sum ["), "{name} must carry a `Ty.sum`:\n{text}");
    }
}

// ---------------------------------------------------------------------------
// Lane 207 -- `traverse i over slots of p` where `p` is a pointer-typed name
//
// A `ptr<normal, _> T` statically names its table `T`, and the slots of what
// it points to are the slots of `T` itself -- the same domain the table
// spelling names. `beispiele/19` and `46` spell it this way (and both stop
// at a SECOND wall, `+=` on a `let mut` local, which has no `Stmt` form:
// a first-refusal count is not a count of programs gained).
// ---------------------------------------------------------------------------

/// **A `traverse` over a pointer-typed parameter travels** (positive probe):
/// with two tables in scope the domain is the table the pointer statically
/// names, never the other one.
#[test]
fn accepts_traverse_over_pointer_domain() {
    let q = "module test::leang_travd {\n\
        table T count 4 { slot { v : u32, } }\n\
        table U count 4 { slot { w : u32, } }\n\
        lock L protects { T } rank 0 held <= 100 ops;\n\
        lock C protects { U } rank 10 held <= 100 ops;\n\
        impl fn f(t : ptr<normal, rw> T, u : ptr<normal, rw> U)\n\
        requires Held(L)\n\
        effects { writes t.slots, locks L } costs <= 64 ops\n\
        {\n    traverse i over slots of t by unvisited\n\
        {\n        t.slots[i].v = 0;\n}\n}\n\
        }\n";
    let text = export("leang_travd", &tree(q)).expect("pointer-domain traverse must export");
    assert!(
        text.contains("(.traverse GTab.T"),
        "the domain is the table the pointer names:\n{text}"
    );
    assert!(
        !text.contains("(.traverse GTab.U"),
        "and never the table it does not name:\n{text}"
    );
}

/// **LG006 -- a `traverse` over an integer is still no table** (poison
/// probe): only a pointer-typed name resolves, never a value.
#[test]
fn refuses_traverse_over_integer_domain() {
    let q = "module test::leang_travi {\n\
        table T count 4 { slot { v : u32, } }\n\
        impl fn f(x : u32)\n\
        effects { pure } costs <= 64 ops\n\
        {\n    traverse i over slots of x by unvisited\n\
        {\n        let z = i;\n}\n}\n\
        }\n";
    let w = export("leang_travi", &tree(q)).expect_err("must refuse");
    assert_eq!(w.code, "LG006", "{w}");
    assert!(w.message.contains("is not a table"), "must name the domain failure: {w}");
}

/// **LG006 -- a `traverse` over an unknown name is still no table**
/// (poison probe): the pointer arm resolves names in scope, it does not
/// invent them.
#[test]
fn refuses_traverse_over_unknown_domain() {
    let q = "module test::leang_travu {\n\
        table T count 4 { slot { v : u32, } }\n\
        impl fn f(t : ptr<normal, rw> T)\n\
        effects { writes t.slots } costs <= 64 ops\n\
        {\n    traverse i over slots of nope by unvisited\n\
        {\n        t.slots[i].v = 0;\n}\n}\n\
        }\n";
    let w = export("leang_travu", &tree(q)).expect_err("must refuse");
    assert_eq!(w.code, "LG006", "{w}");
    assert!(w.message.contains("is not a table"), "must name the domain failure: {w}");
}

/// **Lane 207 -- the `Einheit` width in one unit** (positive probe): the
/// real `requires` (`gReq_arbeiter`), the declared start with its argument
/// list, the declared initial memory (`gSp0`: slots at zero, the global at
/// its initialiser), the lock-invariant family (`gS`) and the unit itself
/// (`gE : Zielsatz.Einheit gD`).
#[test]
fn einheit_width_travels_together() {
    let q = "module test::leang_einheit {\n\
        table T count 4 { slot { v : u32, } }\n\
        static mut s : u32 in 0 .. 100 = 3;\n\
        lock L protects { T, s } rank 0 held <= 100 ops invariant T.slots[0].v == 1;\n\
        impl fn starter() effects { pure } costs <= 1 ops { }\n\
        impl fn arbeiter(t : ptr<normal, rw> T)\n\
        requires Held(L), T.slots[0].v == 7\n\
        effects { writes t.slots, locks L } costs <= 8 ops\n\
        {\n    t.slots[0].v = 8;\n}\n\
        concurrent { starter };\n\
        }\n";
    let text = export("leang_einheit", &tree(q)).expect("the unit must export");
    for teil in [
        "def gReq_arbeiter",
        "starts := [⟨g_starter, .nil⟩]",
        "| .T, .v => ⟨0, by decide, by decide⟩",
        "| .s => ⟨3, by decide, by decide⟩",
        "def gS : SperrInv gD where",
        "def gE : Zielsatz.Einheit gD where",
        "  P := gP",
        "  S := gS",
        "  sp0 := gSp0",
    ] {
        assert!(text.contains(teil), "unit export must contain {teil:?}:\n{text}");
    }
}
