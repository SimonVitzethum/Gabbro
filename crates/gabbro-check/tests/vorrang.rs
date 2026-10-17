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

use gabbro_syntax::diag::Stufe;
use std::path::{Path, PathBuf};
use std::process::Command;

/// The five operators of the flat level, with the stem each carries in the probe's names.
const OPS: [&str; 5] = ["schiebl", "schiebr", "und", "xor", "oder"];

/// The forms beside the 25 pairs, with the C type each returns.
///
/// The first four sit at the SECOND divergence: Gabbro's `cmpexpr = bitexpr [ cmp bitexpr ]`
/// puts the whole bit level BELOW the comparison, C puts `& ^ |` above it. The last two sit
/// at a boundary where both languages agree (`+ -` above `<< >>`) -- they belong here so the
/// count has a denominator, and because the emitter parenthesises them anyway: without that
/// `-Wparentheses` fires, and stage 9 of `pruefe-emission.sh` compiles with `-Werror`.
const GRENZEN: [(&str, &str); 6] = [
    ("grenze_und_gleich", "bool"),
    ("grenze_xor_gleich", "bool"),
    ("grenze_oder_gleich", "bool"),
    ("grenze_schiebl_klein", "bool"),
    ("grenze_plus_schiebl", "uint32_t"),
    ("grenze_schiebl_plus", "uint32_t"),
];

fn probe() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join("messung")
        .join("proben")
        .join("probe-vorrang-bitstufen.gab")
}

/// Every form in the probe, as (name without prefix, C return type).
fn formen() -> Vec<(String, &'static str)> {
    let mut v: Vec<(String, &'static str)> = Vec::new();
    for a in OPS {
        for b in OPS {
            v.push((format!("{a}_{b}"), "uint32_t"));
        }
    }
    for (n, t) in GRENZEN {
        v.push((n.to_string(), t));
    }
    v
}

/// The driver: one row per form, the flat call beside its parenthesised twin.
fn treiber(formen: &[(String, &'static str)]) -> String {
    let mut s = String::from("\n#include <stdio.h>\n\nint main(void) {\n");
    s.push_str("    const uint32_t a = 3, b = 5, c = 2;\n    int abweichungen = 0;\n");
    for (n, _) in formen {
        s.push_str(&format!(
            "    {{\n        unsigned long f = (unsigned long)flach_{n}(a, b, c);\n         \
             unsigned long g = (unsigned long)klammer_{n}(a, b, c);\n        if (f != g) \
             {{ abweichungen++; printf(\"ABWEICHUNG {n}: geliefert=%lu gemeint=%lu\\n\", f, g); }}\n    }}\n"
        ));
    }
    s.push_str(&format!(
        "    printf(\"geprueft=%d abweichungen=%d\\n\", {}, abweichungen);\n    return 0;\n}}\n",
        formen.len()
    ));
    s
}

