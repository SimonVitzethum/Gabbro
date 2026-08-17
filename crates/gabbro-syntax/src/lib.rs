//! **Gabbro -- lexis, vocabulary, grammar.**
//!
//! Stage **P2** of the checker plan (`SPRACHE.md`, part III §6): *lexer + parser over all
//! fragments of the folder.* This crate reads source text and yields a core tree; it checks
//! **nothing** but form. Every promise of the language -- M1 to M4, D1/D2, pairing, effects,
//! costs -- lives in `gabbro-check`, in a fixed pass order.
//!
//! The generator holds `forbid(unsafe_code)` (workspace `Cargo.toml`) and has no dependency
//! outside `std`. `README.md`: *"A generator that can itself break out makes the property of
//! its product worthless."*

pub mod ast;
pub mod diag;
pub mod kw;
pub mod lex;
pub mod parse;
pub mod span;

pub use diag::{Absage, Absagen, Stufe};
pub use parse::parse;

/// Reads a source and yields tree and refusals.
pub fn lies(datei: &str, quelle: &str) -> (ast::Programm, Absagen) {
    let mut absagen = Absagen::neu(datei);
    let baum = parse::parse(quelle, &mut absagen);
    (baum, absagen)
}
