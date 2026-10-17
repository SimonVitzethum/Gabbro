//! **One flat level against four -- compiled with `-Werror` and RUN.**
//!
//! `parse.rs::bitexpr` is a single left-associative loop over `<< >> & ^ |`. C grades those
//! five into four levels. Until 2026-08-31 the emitter printed the tree as flat C text, so
//! C regrouped it: `a & b << c` is `(a & b) << c` in Gabbro and `a & (b << c)` in the
//! generated file. Nine of the 25 pairs computed a different value, and `gabbro pruefe`
//! said `0 errors, 0 hints` over all of them.
//!
//! **This probe does not read the emitted text and call that a measurement.** It compiles
//! it and runs it. Every form in `messung/proben/probe-vorrang-bitstufen.gab` stands twice:
//!
//! ```text
//!     flach_X      return a o1 b o2 c;        what the emitter ships
//!     klammer_X    return (a o1 b) o2 c;      what Gabbro MEANS
//! ```
//!
//! The parenthesised twin is not a claim -- a parenthesis in the source becomes
//! `ExprArt::Klammer` and is emitted as a parenthesis, so the C there is forced to compute
//! Gabbro's tree. The driver calls both with `a=3 b=5 c=2` and compares the values that
//! come back. **A single difference means a shipped program computes something other than
//! what the checker proved.**
//!
//! `a=3 b=5 c=2` is searched, not guessed: the smallest triple at which every structural
//! difference is also visible in the VALUE. A triple that maps a difference onto the same
//! value measures it away.







