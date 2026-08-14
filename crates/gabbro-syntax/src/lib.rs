//! **Gabbro -- Lexik, Wortschatz, Grammatik.**
//!
//! Stufe **P2** aus dem Prueferplan (`SPRACHE.md`, Teil III §6): *Lexer + Parser ueber alle
//! Fragmente des Ordners.* Diese Kiste liest Quelltext und gibt einen Kernbaum; sie prueft
//! **nichts** ausser der Form. Jede Zusage der Sprache -- M1 bis M4, D1/D2, Paarung, Wirkungen,
//! Kosten -- liegt in `gabbro-check`, in fester Passfolge.
//!
//! Der Erzeuger haelt `forbid(unsafe_code)` (Arbeitsbereichs-`Cargo.toml`) und hat keine
//! Abhaengigkeit ausserhalb von `std`. `README.md`: *„Ein Erzeuger, der selbst ausbrechen kann,
//! macht die Eigenschaft seines Erzeugnisses wertlos."*

pub mod ast;
pub mod diag;
pub mod kw;
pub mod lex;
pub mod parse;
pub mod span;

pub use diag::{Absage, Absagen, Stufe};
pub use parse::parse;

/// Liest eine Quelle und gibt Baum und Absagen.
pub fn lies(datei: &str, quelle: &str) -> (ast::Programm, Absagen) {
    let mut absagen = Absagen::neu(datei);
    let baum = parse::parse(quelle, &mut absagen);
    (baum, absagen)
}
