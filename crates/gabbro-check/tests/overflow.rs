//! **PLAN-BITS section 4 (lane 88): the overflow operators.**
//!
//! `+%`, `-%`, `*%`, `<<%` wrap modulo 2^N on an exact unsigned range
//! `0 .. 2^N-1` (`M153` elsewhere, naming `+|`); `+|` clamps into one shared
//! integer range (`M154` on two ranges). Three sides, each pinned:
//!
//! * the checker takes the exact shapes and refuses the rest, by code;
//! * the emitter writes the mask and the saturating call, not the operator;
//! * the generated C is compiled and RUN -- wrapping, masking and clamping
//!   compute the wrapped, masked and clamped values.

use gabbro_syntax::diag::Stufe;
use std::process::Command;

fn codes(source: &str) -> Vec<(&'static str, Stufe)> {
    let (baum, mut absagen) = gabbro_syntax::lies("<probe>", source);
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    absagen
        .absagen
        .iter()
        .map(|a| (a.code, a.stufe))
        .collect()
}

fn falls_with(source: &str, code: &str) {
    let c = codes(source);
    assert!(
        c.iter().any(|(k, s)| *k == code && *s == Stufe::Fehler),
        "expected {code}, got {c:?}\n{source}"
    );
}

fn falls_clean(source: &str) {
    let c = codes(source);
    assert!(
        !c.iter().any(|(_, s)| *s == Stufe::Fehler),
        "clean, but falls with {c:?}\n{source}"
    );
}

fn body(expr: &str, params: &str, result: &str) -> String {
    format!(
        "module t {{\n\
         impl fn f({params}) -> {result} effects {{ pure }} costs <= 40 ops {{\n\
         return {expr};\n}}\n}}"
    )
}

// -- the checker takes the exact shapes ------------------------------------------------

#[test]
fn wrapping_on_exact_ranges_passes() {
    falls_clean(&body("a +% b", "a : u32, b : u32", "u32"));
    falls_clean(&body("a -% b", "a : u32, b : u32", "u32"));
    falls_clean(&body("a *% b", "a : u32, b : u32", "u32"));
    falls_clean(&body(
        "a <<% s",
        "a : u32, s : u32 in 0 .. 31",
        "u32",
    ));
    // The `uN` sugar IS the exact range: `u13` is `u16 in 0 .. 8191`.
    falls_clean(&body("a +% b", "a : u13, b : u13", "u13"));
    // A literal takes the other's exact range when its value lies in it.
    falls_clean(&body("a +% 1", "a : u32", "u32"));
    falls_clean(&body("a <<% 2", "a : u16", "u16"));
}

#[test]
fn saturation_on_one_range_passes() {
    falls_clean(&body(
        "a +| b",
        "a : u8 in 0 .. 5, b : u8 in 0 .. 5",
        "u8 in 0 .. 5",
    ));
    // Signed too, and over the whole word: clamping is defined everywhere.
    falls_clean(&body(
        "a +| b",
        "a : i16 in -100 .. 100, b : i16 in -100 .. 100",
        "i16 in -100 .. 100",
    ));
    falls_clean(&body("a +| b", "a : u32, b : u32", "u32"));
    falls_clean(&body("a +| 1", "a : u8 in 0 .. 5", "u8 in 0 .. 5"));
}

// -- the checker refuses the rest, by code ----------------------------------------------

#[test]
fn wrapping_without_power_range_falls_m153() {
    // `0 .. 5` is no `0 .. 2^N-1`: wrapping would be ambiguous there.
    falls_with(
        &body("a +% b", "a : u32 in 0 .. 5, b : u32 in 0 .. 5", "u32 in 0 .. 5"),
        "M153",
    );
    falls_with(
        &body("a -% b", "a : u32 in 0 .. 5, b : u32 in 0 .. 5", "u32 in 0 .. 5"),
        "M153",
    );
    falls_with(
        &body("a *% b", "a : u32 in 0 .. 5, b : u32 in 0 .. 5", "u32 in 0 .. 5"),
        "M153",
    );
    // Signed is exact and still refused: signed overflow is undefined in C.
    falls_with(&body("a +% b", "a : i32, b : i32", "i32"), "M153");
    // Mixed widths are NOT `M153`: like plain `+` they have no common width and
    // answer `Unbekannt` -- the no-implicit-conversion convention, not a refusal.
    // A literal outside the exact range adopts nothing.
    falls_with(&body("a +% 70000", "a : u16", "u16"), "M153");
}

#[test]
fn shift_amount_outside_falls() {
    // The amount leaves `0 .. N-1`: the width refusal a plain shift gets.
    falls_with(&body("a <<% s", "a : u8, s : u8", "u8"), "M104");
    // ... and a value side that is not exact never reaches the amount question.
    falls_with(
        &body("a <<% 1", "a : u32 in 0 .. 5", "u32 in 0 .. 5"),
        "M153",
    );
}

#[test]
fn saturation_on_two_ranges_falls_m154() {
    // Clamping needs ONE interval to clamp into.
    falls_with(
        &body(
            "a +| b",
            "a : u8 in 0 .. 5, b : u8 in 0 .. 7",
            "u8 in 0 .. 7",
        ),
        "M154",
    );
}

// -- the emitter writes the mask and the call --------------------------------------------

const EMIT_SOURCE: &str = "module t {
    impl fn w_mask(a : u13, b : u13) -> u13 effects { pure } costs <= 40 ops {
        return a +% b;
    }
    impl fn w_voll(a : u32, b : u32) -> u32 effects { pure } costs <= 40 ops {
        return a +% b;
    }
    impl fn s_u(a : u8 in 0 .. 5, b : u8 in 0 .. 5) -> u8 in 0 .. 5 effects { pure } costs <= 40 ops {
        return a +| b;
    }
    impl fn s_i(a : i16 in -100 .. 100, b : i16 in -100 .. 100) -> i16 in -100 .. 100 effects { pure } costs <= 40 ops {
        return a +| b;
    }
}";

// -- the generated C computes the wrapped, masked and clamped values ---------------------

const RUN_SOURCE: &str = "module t {
    impl fn w_add(a : u32, b : u32) -> u32 effects { pure } costs <= 40 ops {
        return a +% b;
    }
    impl fn w_sub(a : u32, b : u32) -> u32 effects { pure } costs <= 40 ops {
        return a -% b;
    }
    impl fn w_mul(a : u32, b : u32) -> u32 effects { pure } costs <= 40 ops {
        return a *% b;
    }
    impl fn w_shl(a : u32, s : u32 in 0 .. 31) -> u32 effects { pure } costs <= 40 ops {
        return a <<% s;
    }
    impl fn w_mask(a : u13, b : u13) -> u13 effects { pure } costs <= 40 ops {
        return a +% b;
    }
    impl fn s_add(a : u8 in 0 .. 5, b : u8 in 0 .. 5) -> u8 in 0 .. 5 effects { pure } costs <= 40 ops {
        return a +| b;
    }
    impl fn s_add_i(a : i16 in -100 .. 100, b : i16 in -100 .. 100) -> i16 in -100 .. 100 effects { pure } costs <= 40 ops {
        return a +| b;
    }
}";

/// Case rows: (C expression, expected value). Each is a fact the checker proved
/// (the range) and the C recomputes -- a single difference is a shipped program
/// computing something other than what was proved.
const CASES: &[(&str, &str)] = &[
    ("w_add(4294967295u, 1u)", "0"),
    ("w_sub(0u, 1u)", "4294967295"),
    ("w_mul(65536u, 65536u)", "0"),
    ("w_shl(1u, 31u)", "2147483648"),
    ("w_shl(4294967295u, 1u)", "4294967294"),
    ("w_mask(8191u, 1u)", "0"),
    ("w_mask(4096u, 4096u)", "0"),
    ("w_mask(100u, 23u)", "123"),
    ("s_add(4u, 3u)", "5"),
    ("s_add(0u, 0u)", "0"),
    ("s_add(2u, 2u)", "4"),
    ("s_add_i(100, 100)", "100"),
    ("s_add_i(-100, -100)", "-100"),
    ("s_add_i(50, 20)", "70"),
    ("s_add_i(-50, -60)", "-100"),
];

