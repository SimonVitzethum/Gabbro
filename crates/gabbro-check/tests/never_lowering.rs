//! Lane 235 -- lowering of accepted `-> never` bodies (TODO §-1 wave C).
//!
//! Lane 225 accepted two honest never-shapes in the checker (sentences +
//! probes, zero behavior change) and left the emitter one lane behind: a
//! `-> never` `asm` body without `out` fell at the older `hat_ergebnis` arm
//! (`C001`), because `f.ergebnis` is `Some` for `-> never`. That arm now
//! counts `never` as "no result" (`emit.rs`): the shape lowers to a bare
//! `__asm__` under a `_Noreturn void` prototype, with no `result` local and
//! no `return`. What this file pins per shape: what lowers (with the C-level
//! noreturn proof -- `cc -fsyntax-only` over the emitted unit), and what
//! stays refused by name (existing codes, narrowed).
//!
//! Snippet tests only: nothing here enters `beispiele/`, so no `MARKE_EMIT*`
//! counter moves.

use gabbro_syntax::diag::Stufe;

fn fehlercodes(quelle: &str) -> Vec<String> {
    let (baum, mut absagen) = gabbro_syntax::lies("never_lowering", quelle);
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code.to_string())
        .collect()
}

fn emitfehlercodes(quelle: &str) -> Vec<String> {
    let (baum, mut absagen) = gabbro_syntax::lies("never_lowering", quelle);
    assert_eq!(absagen.fehler_zahl(), 0, "probe does not parse:\n{}", absagen.zeige(quelle));
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    assert_eq!(absagen.fehler_zahl(), 0, "probe refused by checker:\n{}", absagen.zeige(quelle));
    let _ = gabbro_check::emit::emittiere(&baum, &mut absagen);
    absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code.to_string())
        .collect()
}

/// Checker-clean programs lower: parse, then full `pruefe`, then `emit`.
fn c_nach_pruefung(quelle: &str) -> String {
    let (baum, mut absagen) = gabbro_syntax::lies("never_lowering", quelle);
    assert_eq!(absagen.fehler_zahl(), 0, "probe does not parse:\n{}", absagen.zeige(quelle));
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    assert_eq!(absagen.fehler_zahl(), 0, "probe refused by checker:\n{}", absagen.zeige(quelle));
    let c = gabbro_check::emit::emittiere(&baum, &mut absagen);
    assert_eq!(absagen.fehler_zahl(), 0, "probe refused by emitter:\n{}", absagen.zeige(quelle));
    c
}

/// The C-level noreturn proof: the emitted unit compiles under
/// `cc -std=c11 -Wall -Wextra -Werror -O0 -c`. A `_Noreturn` body that
/// returned, or a `return` in one, would fail here -- not hope.
///
/// **Not `-fsyntax-only`** (review G04, 2026-09-21): gcc's "'noreturn'
/// function does return" is a middle-end warning and does not run under
/// `-fsyntax-only`, so a bare `__asm__` falling off a `_Noreturn` function
/// passed this proof with gcc and failed `gcc -c -O0 -Werror` (measured).
fn cc_nimmt_an(c: &str, name: &str) {
    let ziel = std::env::temp_dir().join(format!("gabbro-never-{name}.c"));
    let objekt = std::env::temp_dir().join(format!("gabbro-never-{name}.o"));
    std::fs::write(&ziel, c).expect("emitted C is writable");
    let cc = std::process::Command::new("cc")
        .args(["-std=c11", "-Wall", "-Wextra", "-Werror", "-O0", "-c", "-o"])
        .arg(&objekt)
        .arg(&ziel)
        .output();
    let _ = std::fs::remove_file(&objekt);
    match cc {
        Ok(r) => assert!(
            r.status.success(),
            "{name} lowers but `cc` refuses the product:\n{}\n{}",
            ziel.display(),
            String::from_utf8_lossy(&r.stderr)
        ),
        // A missing `cc` is a missing measurement, never a green one.
        Err(e) => panic!("`cc` does not start ({e}) -- NOTHING measured"),
    }
    let _ = std::fs::remove_file(&ziel);
}

const ASM_OHNE_OUT: &str = "module t {\n\
    divergent fn halt() -> never\n\
    \x20   effects { diverges }\n\
    \x20   costs   <= 1 ops\n\
    \x20   arch    x86_64\n\
    \x20   = asm {\n\
    \x20       \"hlt\"\n\
    \x20       clobbers { memory }\n\
    \x20   };\n\
    }\n";

/// The handoff shape of lane 225 (was `gift/1066`, now lowered): checker-clean,
/// lane 235 lowers it to a bare `__asm__` under `_Noreturn` -- no `result`, no `return`.
#[test]
fn never_asm_ohne_out_wird_gesenkt() {
    assert!(fehlercodes(ASM_OHNE_OUT).is_empty(), "checker refuses: {:?}", fehlercodes(ASM_OHNE_OUT));
    let c = c_nach_pruefung(ASM_OHNE_OUT);
    assert!(c.contains("_Noreturn void halt(void)"), "noreturn prototype:\n{c}");
    assert!(c.contains("__asm__ __volatile__("), "asm stub:\n{c}");
    assert!(!c.contains("return result;"), "a never-body answers nothing:\n{c}");
    assert!(!c.contains("result;"), "no result slot:\n{c}");
    // `hlt` resumes after an interrupt: the call must still never continue.
    assert!(c.contains("for (;;) {"), "a returning asm text must not fall off `_Noreturn`:\n{c}");
    cc_nimmt_an(&c, "ohne-out");
}

const ASM_NUR_IN: &str = "module t {\n\
    static mut GERAET : u32 = 0;\n\
    divergent fn halt(w : u8) -> never\n\
    \x20   effects { writes GERAET, diverges }\n\
    \x20   costs   <= 1 ops\n\
    \x20   arch    x86_64\n\
    \x20   = asm {\n\
    \x20       \"outb %[w], $0x80\"\n\
    \x20       in { w : \"a\" }\n\
    \x20       clobbers { memory }\n\
    \x20   };\n\
    }\n";

/// Input operands read parameters -- well-defined under `-> never` too.
#[test]
fn never_asm_mit_nur_in_wird_gesenkt() {
    assert!(fehlercodes(ASM_NUR_IN).is_empty(), "checker refuses: {:?}", fehlercodes(ASM_NUR_IN));
    let c = c_nach_pruefung(ASM_NUR_IN);
    assert!(c.contains("_Noreturn void halt("), "noreturn prototype:\n{c}");
    assert!(c.contains("[w] \"a\" (w)"), "input operand:\n{c}");
    assert!(!c.contains("return result;"), "a never-body answers nothing:\n{c}");
    cc_nimmt_an(&c, "nur-in");
}

const ASM_MIT_OUT: &str = "module t {\n\
    static mut GERAET : u32 = 0;\n\
    divergent fn halt(w : u8) -> never\n\
    \x20   effects { writes GERAET, diverges }\n\
    \x20   costs   <= 1 ops\n\
    \x20   arch    x86_64\n\
    \x20   = asm {\n\
    \x20       \"outb %[w], $0x80\"\n\
    \x20       in { w : \"a\" }\n\
    \x20       out { w : \"=a\" }\n\
    \x20       clobbers { memory }\n\
    \x20   };\n\
    }\n";

/// A non-`result` `out` on a `-> never` body: the checker is silent (lane
/// 225, read-only), and the emitter refuses by name -- an output into a
/// by-value parameter dies with the call, so no lowering gives it meaning.
#[test]
fn never_asm_mit_out_bleibt_verweigert() {
    assert!(fehlercodes(ASM_MIT_OUT).is_empty(), "checker moved: {:?}", fehlercodes(ASM_MIT_OUT));
    assert_eq!(emitfehlercodes(ASM_MIT_OUT), vec!["C001"], "must stay refused by name");
}

const ASM_MIT_RESULT: &str = "module t {\n\
    divergent fn halt() -> never\n\
    \x20   effects { diverges }\n\
    \x20   costs   <= 1 ops\n\
    \x20   arch    x86_64\n\
    \x20   = asm {\n\
    \x20       \"hlt\"\n\
    \x20       out { result : \"=a\" }\n\
    \x20       clobbers { memory }\n\
    \x20   };\n\
    }\n";

/// The N321 line is intact (`gift/984`/`985`): refused on BOTH channels.
#[test]
fn never_asm_mit_result_bleibt_verweigert() {
    assert_eq!(fehlercodes(ASM_MIT_RESULT), vec!["N321"], "N321 moved");
    // The emitter refuses even with the checker rule dropped: `_Noreturn`
    // together with `return result` is not C.
    let (baum, mut absagen) = gabbro_syntax::lies("never_lowering", ASM_MIT_RESULT);
    let _ = gabbro_check::emit::emittiere(&baum, &mut absagen);
    let gefallen: Vec<String> = absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code.to_string())
        .collect();
    assert_eq!(gefallen, vec!["C001"], "emitter N321 arm moved");
}

const FOREVER_RUMPF: &str = "module t {\n\
    table K count 4 { slot { v : u32, } }\n\
    extern fn watchdog() -> never effects { diverges } costs <= 1 ops;\n\
    divergent fn dienst(s : ptr<normal, rw> K) -> never\n\
    \x20   effects { writes s.slots, diverges }\n\
    {\n\
    \x20   forever arbeit\n\
    \x20       per_pass bounded 64 ops\n\
    \x20       on_exceeded watchdog\n\
    \x20       effects { writes s.slots }\n\
    \x20   {\n\
    \x20       s.slots[0].v = 1;\n\
    \x20   }\n\
    }\n}\n";

/// The accepted `forever` end: a loop that never falls through under a
/// `_Noreturn` prototype, with a memory write inside (non-degenerate: the
/// run reaches the loop through a step that changes memory). Lowered before
/// lane 235; pinned, not repaired.
#[test]
fn never_forever_wird_gesenkt() {
    assert!(fehlercodes(FOREVER_RUMPF).is_empty(), "checker refuses: {:?}", fehlercodes(FOREVER_RUMPF));
    let c = c_nach_pruefung(FOREVER_RUMPF);
    assert!(c.contains("_Noreturn void dienst("), "noreturn prototype:\n{c}");
    assert!(c.contains("for (;;) {"), "the loop that never falls through:\n{c}");
    assert!(c.contains("s->slots[0].v = 1;"), "the memory write inside the loop:\n{c}");
    cc_nimmt_an(&c, "forever");
}

const TAILCALL_RUMPF: &str = "module t {\n\
    extern fn stop() -> never effects { diverges } costs <= 1 ops;\n\
    impl fn ruf() -> never\n\
    \x20   effects { diverges }\n\
    \x20   costs   <= 2 ops\n\
    {\n\
    \x20   stop();\n\
    }\n}\n";

/// A body ending in a call to a `-> never` routine: its divergence is the
/// callee's, so there is no new lowering -- pinned, not repaired.
#[test]
fn never_tailcall_wird_gesenkt() {
    assert!(fehlercodes(TAILCALL_RUMPF).is_empty(), "checker refuses: {:?}", fehlercodes(TAILCALL_RUMPF));
    let c = c_nach_pruefung(TAILCALL_RUMPF);
    assert!(c.contains("_Noreturn void ruf(void)"), "noreturn prototype:\n{c}");
    assert!(c.contains("stop();"), "the diverging call:\n{c}");
    cc_nimmt_an(&c, "tailcall");
}

const NIE_MIT_GRUND: &str = "module t {\n\
    reason Leer {\n\
    \x20   Leer = 1 \"leer\"\n\
    \x20   exhaustive\n\
    }\n\
    divergent fn halt() -> never or Leer\n\
    \x20   effects { diverges }\n\
    \x20   costs   <= 1 ops\n\
    \x20   arch    x86_64\n\
    \x20   = asm {\n\
    \x20       \"hlt\"\n\
    \x20       clobbers { memory }\n\
    \x20   };\n\
    }\n";

/// `-> never or R` promises both "never returns" and "answers false with a
/// reason" -- the `bool` channel and `_Noreturn` contradict each other, so
/// no lowering exists. The checker is silent; the emitter refuses by name
/// at the channel path (`return type`), before any stub is written.
#[test]
fn never_mit_grund_bleibt_verweigert() {
    assert!(fehlercodes(NIE_MIT_GRUND).is_empty(), "checker moved: {:?}", fehlercodes(NIE_MIT_GRUND));
    assert_eq!(emitfehlercodes(NIE_MIT_GRUND), vec!["C001"], "must stay refused by name");
}

const U64_ASM_OHNE_OUT: &str = "module t {\n\
    static mut GERAET : u32 = 0;\n\
    impl fn lesen() -> u64\n\
    \x20   effects { reads GERAET }\n\
    \x20   costs   <= 1 ops\n\
    \x20   arch    x86_64\n\
    \x20   = asm {\n\
    \x20       \"mov $1, %eax\"\n\
    \x20       clobbers { memory }\n\
    \x20   };\n\
    }\n";

/// The narrowing guard: the old `hat_ergebnis` arm still fires for a
/// non-`never` result without `out { result }` -- lane 235 narrowed it,
/// never widened it.
#[test]
fn nicht_never_asm_ohne_out_bleibt_verweigert() {
    assert_eq!(emitfehlercodes(U64_ASM_OHNE_OUT), vec!["C001"], "old arm moved");
}

/// The three still-refused `forever` ends (`gift/1062`-`1064`): total
/// `costs` over a loop with no total (K003), a returning watchdog (S006),
/// a loop that is left (S009). Checker codes, untouched by lane 235.
#[test]
fn never_forever_mit_kosten_bleibt_verweigert() {
    let q = FOREVER_RUMPF.replace(
        "divergent fn dienst(s : ptr<normal, rw> K) -> never\n\x20   effects { writes s.slots, diverges }\n{",
        "divergent fn dienst(s : ptr<normal, rw> K) -> never\n\x20   effects { writes s.slots, diverges }\n\x20   costs   <= 8 ops\n{",
    );
    assert_eq!(fehlercodes(&q), vec!["K003"], "K003 moved");
}

#[test]
fn never_forever_mit_kehrendem_waechter_bleibt_verweigert() {
    let q = FOREVER_RUMPF
        .replace("extern fn watchdog() -> never effects { diverges } costs <= 1 ops;",
            "extern fn heimkehr() -> u32 effects { pure } costs <= 1 ops;")
        .replace("on_exceeded watchdog", "on_exceeded heimkehr");
    assert_eq!(fehlercodes(&q), vec!["S006"], "S006 moved");
}

#[test]
fn never_forever_mit_ausgang_bleibt_verweigert() {
    let q = FOREVER_RUMPF.replace("        s.slots[0].v = 1;\n", "        s.slots[0].v = 1;\n        leave arbeit;\n");
    assert_eq!(fehlercodes(&q), vec!["S009"], "S009 moved");
}
