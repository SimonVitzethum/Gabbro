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

const TAILCALL_RUMPF: &str = "module t {\n\
    extern fn stop() -> never effects { diverges } costs <= 1 ops;\n\
    impl fn ruf() -> never\n\
    \x20   effects { diverges }\n\
    \x20   costs   <= 2 ops\n\
    {\n\
    \x20   stop();\n\
    }\n}\n";

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
