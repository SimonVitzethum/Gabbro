//! Printing the new syntax back to source (lane 222).
//!
//! The reader (`parse.rs`) owns the grammar; this module owns the
//! reverse direction for exactly the nodes lane 222 added: integer
//! `match` arm patterns (`IntPat`). A printed pattern re-parses to an
//! equal pattern (span aside) -- the round-trip the task demands -- and
//! two spellings of one value (`0x10`, `16`) print to one canonical
//! text, so the tree says what the arm means instead of how it was
//! spelled.
//!
//! What this module deliberately does NOT do is print whole programs:
//! expressions, blocks and contracts already have a surface and their
//! own readers, and a second pretty-printer over all of them would be
//! a second register beside the truth. The round-trip tests print a
//! pattern inside a fixed scaffold (`match x { … => { return 0; } }`)
//! and re-parse that.

use crate::ast::{IntBound, IntPat};

/// One integer bound as written, in canonical decimal.
pub fn int_bound(g: &IntBound) -> String {
    if g.negative {
        format!("-{}", g.value)
    } else {
        format!("{}", g.value)
    }
}

/// One integer arm pattern: `3`, `-1`, `0 .. 255`, `0 ..< 256`.
pub fn int_pattern(f: &IntPat) -> String {
    match f {
        IntPat::Exact(g) => int_bound(g),
        IntPat::Range { lo, hi, exclusive } => {
            let sep = if *exclusive { "..<" } else { ".." };
            format!("{} {} {}", int_bound(lo), sep, int_bound(hi))
        }
    }
}
