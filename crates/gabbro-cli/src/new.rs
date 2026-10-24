//! `gabbro new <name>` -- **the on-ramp, and its content is a MEASUREMENT.**
//!
//! *Eight attempts for "add two numbers", by someone with the whole grammar and 63 examples
//! open.* Five of the seven refusals were syntax paper cuts, every one of them correct and
//! well explained. **Nothing in the tree taught the SHAPE** -- so this command writes it.
//!
//! # What is irreducible, measured on 2026-09-01
//!
//! `beispiele/63-druckt.gab` was taken apart clause by clause, each removal checked with
//! `gabbro check` and then BUILT and RUN. Twelve variants; the table is the finding:
//!
//! | taken out | `check` | `build` + run |
//! |---|---|---|
//! | `module … { }` around everything | 0 errors | **builds, prints** |
//! | `pub` on the entry | 0 errors | **REFUSED** -- `static`, the linker never sees it |
//! | `in 0 .. 1` on the return type | 0 errors | builds, prints |
//! | `costs <= N ops` on the function | 0 errors | builds, prints |
//! | `costs` on the `extern fn` | **`K003`** *only while the caller promises costs* | -- |
//! | `effects { … }` on the function | **`E001`** | -- |
//! | `effects { … }` on the `extern fn` | **`E001`** + `E009` at the call | -- |
//!
//! **So the irreducible file is five lines and one body**, and the two that a newcomer will
//! never guess are the two the table marks in bold: `effects` is obligatory *on the extern
//! declaration too*, and `pub` on the entry is not decoration -- it is the difference between
//! a symbol the linker finds and one it does not.
//!
//! **The project file is the smallest one that builds, tests and installs**: `project`, one
//! `program` and one `test` that compares what the program prints.
//!
//! # What this command therefore writes
//!
//! The irreducible set, plus `costs` -- and `costs` carries its own reason in the file:
//! **`gabbro costs` PRINTS the number that a `costs` line must carry.** That tool sat in the
//! tree while a cost bound was guessed five times in one session. *A skeleton that does not
//! name it on the first `costs` line teaches the guessing.*
//!
//! **A skeleton that does not run is a seventh paper cut**, so `tests/onramp.rs` runs
//! `gabbro new` into a temp directory, builds it, executes the binary and compares the
//! output. Nothing here is asserted from reading.

use std::path::Path;

/// The name is a file name, a unit name and a directory name at once. **Refuse, never
/// interpret**: a name with a slash in it would silently write somewhere else.
fn name_ist_brauchbar(name: &str) -> Result<(), String> {
    if name.is_empty() {
        return Err(String::from("the name is empty"));
    }
    if !name.starts_with(|c: char| c.is_ascii_alphabetic()) {
        return Err(format!(
            "`{name}` does not start with an ASCII letter -- it becomes a unit name and a \
             directory name"
        ));
    }
    if let Some(bad) = name
        .chars()
        .find(|c| !(c.is_ascii_alphanumeric() || *c == '-' || *c == '_'))
    {
        return Err(format!(
            "`{name}` carries `{bad}` -- a name here may hold letters, digits, `-` and `_` \
             and nothing else"
        ));
    }
    Ok(())
}

/// The source. **Every comment in it answers a question the eight attempts asked.**
///
/// Since 2026-10-17 (the C backend is removed) the skeleton is a libc-free program: it calls
/// no C function, it makes the Linux `write` system call itself, through a `syscall` gate.
fn quelle(name: &str) -> String {
    format!(
        "\
// `{name}` -- written by `gabbro new`. **It checks, builds and runs as it stands:**
//
//     gabbro check {name}.gab     -- 0 errors
//     gabbro costs {name}.gab     -- what the body COSTS, beside what the line PROMISES
//     gabbro build                -- `gabbro.build`; LLVM: checker, IR, `opt`, `llc`, `ld.lld`
//     ./build/{name}              -- prints `Hi`
//     gabbro test -C build        -- runs the test `gabbro.build` declares
//
// There is no C library and no C compiler in this build. **The program asks the kernel
// itself:** the `syscall` item below is the raw Linux `write` (x86-64, number 1), with the
// registers named, and it is the whole of the program's operating-system interface.
// `dokumente/TUTORIAL.md` is the reason each clause is there. This file is the shape.
module {name} {{

// **(1) `assume` names what the kernel is trusted to do, and `falsifier` names the probe that
// would catch it lying.** The system call is user logic, not a language rule.
assume linux_schreibe
    \"The kernel writes at most len bytes from buf and answers the count.\"
    falsifier sonde_schreibe;

// **(2) The gate.** Registers in, registers out, what the instruction destroys (`rcx`,
// `r11`), and the contract: never more bytes than the buffer holds. `effects` is obligatory on
// EVERY function and gate; `writes ausgabe` names the sink.
syscall schreibe(fd : u64, puffer : ptr<normal, r> u8, laenge : u64) -> u64
    abi linux arch x86_64 number 1
    regs in {{ rdi = fd, rsi = puffer, rdx = laenge }}
    regs out {{ rax }}
    clobbers {{ rcx, r11 }}
    errors {{ }}
    requires laenge <= lenof(puffer)
    effects {{ writes ausgabe }}
    costs <= 8 ops
    assume linux_schreibe falsifier sonde_schreibe;

// **(3) The buffer is a `static`: the LLVM lowering hands a gate a global, not a local.** `check`
// says one `E247` hint about it (no lock guards a carrier the program writes) -- a hint, not a
// refusal; a one-thread program needs no lock.
pub static mut TEXT : [u8; 3] = 0;

// **(4) `pub fn main` is the entry.** The generator writes `_start` around it and hands the
// answer to `exit_group`; a `program` target names exactly one such function.
//
// **`costs <= 40 ops` is NOT irreducible** -- delete it and the file still checks. It stands
// here for the one habit worth having from the first day: **`gabbro costs {name}.gab` prints
// the number the body actually costs, beside the number this line promises.** Read it; never
// guess it. A promise that is too small is `K001`, and it is arithmetic, not opinion.
pub fn main() -> u64
    effects {{ reads TEXT, writes TEXT, writes ausgabe }}
    costs   <= 40 ops
{{
    TEXT[0] = 72;   // H
    TEXT[1] = 105;  // i
    TEXT[2] = 10;   // newline
    schreibe(1, TEXT, 3);
    return 0;
}}
}}
"
    )
}

/// The project file. **Every call in it is one a newcomer needs on the first day.**
fn projektdatei(name: &str) -> String {
    format!(
        "\
# The project `{name}`, written by `gabbro new`. `dokumente/BUILD-SYSTEM.md` is the long form.
#
#     gabbro build                 -- configures `build/` once, then compiles
#     gabbro test -C build         -- builds, then runs the test below
#     gabbro install -C build      -- copies the program into <prefix>/bin
#
# What does NOT stand here: the edges between files and libraries (they are read out of
# `module` and `use` in the sources), compiler flags (`arch`, `when TESTBUILD`, effects and
# costs stand in the source), and C (this build compiles none).
project('{name}', version: '0.1.0')

{name} = program('{name}', '{name}.gab', install: true)

test('prints-hi', {name}, stdout: 'Hi\\n')
"
    )
}

/// **Writes both files or neither.** A half-written skeleton is worse than none: the reader
/// would build a project file against a source that is not there and read a tool's refusal
/// instead of Gabbro's.
pub fn befehl(rest: &[String]) -> std::process::ExitCode {
    let benannt: Vec<&String> = rest.iter().filter(|a| !a.starts_with('-')).collect();
    if benannt.len() != 1 {
        eprintln!(
            "gabbro new <name>  -- writes `gabbro.build` and `<name>.gab` into this directory, \
             and they build, test and run as written. {} name(s) given",
            benannt.len()
        );
        return std::process::ExitCode::from(2);
    }
    let name = benannt[0].as_str();
    if let Err(grund) = name_ist_brauchbar(name) {
        eprintln!("gabbro new: {grund}");
        return std::process::ExitCode::from(2);
    }

    let gab = format!("{name}.gab");
    let bau = "gabbro.build".to_string();
    // **Both existence checks BEFORE the first write.** Otherwise a run over a half-present
    // pair overwrites one file and refuses on the other.
    for datei in [&gab, &bau] {
        if Path::new(datei).exists() {
            eprintln!(
                "gabbro new: `{datei}` is already here -- nothing was written. \
                 A skeleton over an existing file would be a silent loss"
            );
            return std::process::ExitCode::from(2);
        }
    }

    for (datei, inhalt) in [(&gab, quelle(name)), (&bau, projektdatei(name))] {
        if let Err(e) = std::fs::write(datei, inhalt) {
            eprintln!("gabbro new: `{datei}`: {e}");
            return std::process::ExitCode::from(2);
        }
    }

    println!(
        "written  {gab}\n\
         written  {bau}\n\
         \n\
         It checks, builds, tests and runs as it stands:\n\
         \n    gabbro check {gab}\n    gabbro costs {gab}\n    gabbro build\n    \
         gabbro test -C build\n    ./build/{name}\n\
         \n\
         `dokumente/TUTORIAL.md` says why each clause is there."
    );
    std::process::ExitCode::SUCCESS
}
