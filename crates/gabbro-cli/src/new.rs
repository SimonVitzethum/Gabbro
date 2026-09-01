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
//! **The manifest has no optional line at all.** All four of `compiler`, `out`,
//! `unit <name> <program|object>` and an INDENTED source path are refused by name when
//! missing -- measured against `lies_manifest`, which returns exactly those four refusals.
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
fn quelle(name: &str) -> String {
    format!(
        "\
-- `{name}` -- written by `gabbro new`. **It checks, builds and runs as it stands:**
--
--     gabbro check {name}.gab     -- 0 errors
--     gabbro costs {name}.gab     -- what the body COSTS, beside what the line PROMISES
--     gabbro build {name}.bau     -- writes the C, calls `cc`, links
--     ./target/{name}/{name}      -- prints `Hi`
--
-- **Four things here are irreducible, and that was measured and not chosen.** Each was taken
-- out on its own, checked, built and run. They carry `(1)` to `(4)` below. Everything else is
-- a comment, a body, or a line that stands because it teaches -- and says so.
--
-- `TUTORIAL.md` is the reason each clause is there. This file is the shape.

-- **(1) `effects {{ … }}` is obligatory on EVERY function -- the `extern` ones included.**
--
-- Leaving it out is `E001`, and it is not fail-open: a function without the clause is not a
-- function that does nothing. **The braces are part of the clause.** `effects pure` is a
-- syntax error -- `effects` takes a brace LIST -- and the list is never empty: the word for
-- \"no effects\" is `pure`, so a pure function writes `effects {{ pure }}`.
--
-- **(2) `extern fn` binds a C name, and the signature must be C's own.**
--
-- `putchar` is `int putchar(int)`, so the parameter is `i32` and not `u32`. `N046` compares
-- against C's declaration and refuses with the line that would fit. The effect names a SINK,
-- not a place of this unit -- `output` is a free name, and it is what `writes` is for.
extern fn putchar(c : i32) -> i32 effects {{ writes output }} costs <= 8 ops;

-- **(3) `pub` on the entry is not decoration.**
--
-- Without it the entry lowers to a `static` function and the linker never sees it. `check`
-- says nothing -- it is a build rule, and the build refuses by name.
--
-- **(4) A `unit … program` names exactly ONE entry, and it is called `main`.**
--
-- Gabbro does not mangle, so this name IS the C name.
--
-- **`costs <= 40 ops` is NOT irreducible** -- delete it and the file still checks. It stands
-- here for the one habit worth having from the first day: **`gabbro costs {name}.gab` prints
-- the number the body actually costs, beside the number this line promises.** Read it; never
-- guess it. A promise that is too small is `K001`, and it is arithmetic, not opinion.
pub fn main() -> i32
    effects {{ writes output }}
    costs   <= 40 ops
{{
    putchar(72);   -- H
    putchar(105);  -- i
    putchar(10);   -- newline
    return 0;
}}
"
    )
}

/// The manifest. **No line in it is optional**, and the file says which refusal each one
/// prevents.
fn manifest(name: &str) -> String {
    format!(
        "\
-- The manifest for `{name}`. **All four kinds of line are obligatory** -- each is refused by
-- name when it is missing, and the refusal is the whole documentation:
--
--     `compiler` -- \"no `compiler` line\"
--     `out`      -- \"no `out` line\"
--     `unit`     -- \"no `unit` line\"; `unit <name> <program|object>`, three words
--     a path     -- \"unit `{name}` names no file\"; INDENTED, one path per line
--
-- **The indent is the whole syntax.** An indented line is a source of the unit above it.
--
-- The unit graph is read out of `module` and `use` IN THE SOURCES and never from a line
-- here -- a manifest that repeated it would be a second register that can drift.
compiler cc -std=c11 -O0 -Wall -Wextra -Werror
out      target/{name}

unit {name} program
    {name}.gab
"
    )
}

/// **Writes both files or neither.** A half-written skeleton is worse than none: the reader
/// would build a manifest against a source that is not there and read `cc`'s refusal instead
/// of Gabbro's.
pub fn befehl(rest: &[String]) -> std::process::ExitCode {
    let benannt: Vec<&String> = rest.iter().filter(|a| !a.starts_with('-')).collect();
    if benannt.len() != 1 {
        eprintln!(
            "gabbro new <name>  -- writes `<name>.gab` and `<name>.bau` into this directory, \
             and they build and run as written. {} name(s) given",
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
    let bau = format!("{name}.bau");
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

    for (datei, inhalt) in [(&gab, quelle(name)), (&bau, manifest(name))] {
        if let Err(e) = std::fs::write(datei, inhalt) {
            eprintln!("gabbro new: `{datei}`: {e}");
            return std::process::ExitCode::from(2);
        }
    }

    println!(
        "written  {gab}\n\
         written  {bau}\n\
         \n\
         It checks, builds and runs as it stands:\n\
         \n    gabbro check {gab}\n    gabbro costs {gab}\n    gabbro build {bau}\n    \
         ./target/{name}/{name}\n\
         \n\
         `TUTORIAL.md` says why each clause is there."
    );
    std::process::ExitCode::SUCCESS
}
