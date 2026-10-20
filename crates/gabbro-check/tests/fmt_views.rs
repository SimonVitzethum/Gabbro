//! **Lane 197: `fmt --explicit` / `--elide` are pure views.**
//!
//! Lever 3 of `dokumente/CHECKER.md`: explicitness as a view, not a
//! storage format. For every corpus file the checker accepts, `pruefe(F)`,
//! `pruefe(explicit(F))` and `pruefe(elide(F))` give the same diagnostics
//! (codes, levels and texts — spans excluded, the views move bytes), the same
//! M1 coverage numbers and byte-identical emitted C; and the round trip closes
//! both ways (`elide(explicit(F)) == elide(F)`, `explicit(elide(F)) ==
//! explicit(F)`).
//!
//! What the comparison deliberately excludes: byte spans (insertions move
//! them), the rendered line numbers beside them, and fix spans (same reason;
//! the replacement texts compare). What it deliberately includes: every code,
//! every level, every message text and note, every fix replacement, the M1
//! pair and the C bytes.
//!
//! `FMT_ONLY=<substring>` restricts the run to matching file names (triage;
//! the gate runs the whole corpus).






