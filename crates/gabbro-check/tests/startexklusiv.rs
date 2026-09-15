//! **Start exclusivity (N240) in both directions, over snippets.**
//!
//! The file half of the probes is `beispiele/gift/910-914` (poison over
//! files); what stands here pins the same rule over snippets -- poison and
//! positive twin side by side, so a rule that goes silent fails here even
//! where the gift corpus has no file for the shape.

use gabbro_syntax::diag::Stufe;

fn fehler(quelle: &str) -> Vec<String> {
    let (baum, mut absagen) = gabbro_syntax::lies("startexklusiv", quelle);
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code.to_string())
        .collect()
}

const KOPF: &str = "module test::startexklusiv {\n\
    table T count 4 { slot { v : u32, } }\n\
    lock L protects { T } rank 0 held <= 100 ops;\n";

fn einheit(extra: &str) -> String {
    format!("{KOPF}{extra}}}\n")
}

fn reader(name: &str, contract: &str) -> String {
    format!(
        "impl fn {name}() -> u32\n    {contract}\n    effects {{ reads T.slots }}\n    \
         costs <= 4 ops\n{{\n    return T.slots[0].v;\n}}\n"
    )
}

#[test]
fn shared_lock_at_two_starts_falls() {
    let codes = fehler(&einheit(&format!(
        "{} {}\nconcurrent {{ read_a, read_b }};\n",
        reader("read_a", "requires Held(L)"),
        reader("read_b", "requires Held(L)")
    )));
    assert!(
        codes.iter().any(|c| c == "N240"),
        "two starts under one signature lock must fall with N240: {codes:?}"
    );
}

#[test]
fn disjoint_locks_stay_silent() {
    // Since lane 183 (`wurzelnB`) starts hold NO signature lock at all -- the
    // old `requires Held` shape falls with N303 (see `beispiele/108` and gift
    // 967). Disjointness now shows as disjoint locks TAKEN INSIDE.
    let codes = fehler(&einheit(&format!(
        "table U count 4 {{ slot {{ v : u32, }} }}\n\
         lock M protects {{ U }} rank 1 held <= 100 ops;\n\
         impl fn read_a() -> u32\n    effects {{ reads T.slots, locks L }}\n    \
         costs <= 64 ops\n{{\n    locks L {{ return T.slots[0].v; }}\n}}\n\
         impl fn read_c() -> u32\n    effects {{ reads U.slots, locks M }}\n    \
         costs <= 64 ops\n{{\n    locks M {{ return U.slots[1].v; }}\n}}\n\
         concurrent {{ read_a, read_c }};\n",
    )));
    assert!(
        codes.is_empty(),
        "disjoint locks taken inside must stay silent: {codes:?}"
    );
}

#[test]
fn shared_shared_falls() {
    // Strict transfer: the model premise bans ANY common signature lock,
    // and knows no compatible shared holding -- so shared-shared falls too.
    let codes = fehler(&einheit(&format!(
        "{} {}\nconcurrent {{ read_a, read_b }};\n",
        reader("read_a", "requires Held(L, shared)"),
        reader("read_b", "requires Held(L, shared)")
    )));
    assert!(
        codes.iter().any(|c| c == "N240"),
        "two shared starts under one signature lock must fall with N240: {codes:?}"
    );
}

#[test]
fn same_function_on_two_entries_falls() {
    let codes = fehler(&einheit(&format!(
        "{}\nentry entry_a vector 0x80 arch x86_64 {{\n    regs in {{ }} regs out {{ }} \
         preserves {{ rbx }} clobbers {{ rcx }} stack ka per cpu nested never \
         dispatch test::startexklusiv::read_a;\n}}\n\
         entry entry_b vector 0x81 arch x86_64 {{\n    regs in {{ }} regs out {{ }} \
         preserves {{ rbx }} clobbers {{ rcx }} stack kb per cpu nested never \
         dispatch test::startexklusiv::read_a;\n}}\n",
        reader("read_a", "requires Held(L)")
    )));
    assert!(
        codes.iter().any(|c| c == "N240"),
        "one lock-holding routine on two entries must fall with N240: {codes:?}"
    );
}

#[test]
fn lockfree_entries_stay_silent() {
    let codes = fehler(&einheit(
        "impl fn idle_a() -> u32\n    effects { pure }\n    costs <= 1 ops\n{\n    return 0;\n}\n\
         impl fn idle_b() -> u32\n    effects { pure }\n    costs <= 1 ops\n{\n    return 1;\n}\n\
         entry entry_a vector 0x80 arch x86_64 {\n    regs in { } regs out { } \
         preserves { rbx } clobbers { rcx } stack ka per cpu nested never \
         dispatch test::startexklusiv::idle_a;\n}\n\
         entry entry_b vector 0x81 arch x86_64 {\n    regs in { } regs out { } \
         preserves { rbx } clobbers { rcx } stack kb per cpu nested never \
         dispatch test::startexklusiv::idle_b;\n}\n",
    ));
    assert!(
        codes.is_empty(),
        "lock-free entry roots must stay silent: {codes:?}"
    );
}
