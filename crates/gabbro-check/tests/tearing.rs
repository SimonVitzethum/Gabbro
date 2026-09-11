//! **The tearing ruling as an executable witness.**
//!
//! `gabbro_check::tearing::Shape::ruling` names the lane-70 verdict for
//! every lane-47 inventory row: five admissions with their atomicity
//! price, three refusals with the guarantee that redeems them, one open
//! row. These tests pin that table against the scanner (`check`) row by
//! row: the ruling verdict and the scan verdict must agree on every
//! shape, and the guarantee words in both places must be the same words.
//!
//! The placement is load-bearing, not taste: the kennungen guardian
//! counts one code per file, so a test asserting on `T001` findings
//! cannot live in an inline module of the file that assigns the code.
//! Tests NAME codes, only source files ASSIGN them -- the same rule
//! `tests/pflichten_zyklen.rs` states for its own codes.
//!
//! The C snippets below repeat the inline `ROWS` fixtures of
//! `src/tearing.rs` on purpose: the verdicts come from `ruling`, the
//! single register, while the snippets are the shared ground both suites
//! read. What would drift silently is the verdict, and that lives in one
//! place only.

use gabbro_check::tearing::{self, Ruling, Shape};

/// The declarations behind the inventory: tables and the shared global
/// name the carriers, the accumulates stem names the cells. A compound
/// assign to any other name is a local fold and passes.
fn sharing() -> tearing::SharedCarriers {
    tearing::SharedCarriers::new(&["c", "o", "farbbericht"], &["z"])
}

/// The emitted C per shape, in inventory words. The scanner reads this
/// text; the ruling reads the shape; the tests below hold the two
/// readings against each other.
fn shape_c(shape: Shape) -> &'static str {
    match shape {
        Shape::SlotPlain => "c->slots[s].benutzt = false;",
        Shape::GlobalPlain => "farbbericht = wert;",
        Shape::SlotCompound => "c->slots[s].marke += 1;",
        Shape::GuardedCompound => {
            "if (o->slots[obj].zaehler > 0) {\n    o->slots[obj].zaehler -= 1;\n}"
        }
        Shape::Cas => "ok = atomic_compare_exchange_strong_explicit(&BESITZER, &_erw, wert, \
            memory_order_release, memory_order_acquire);",
        Shape::RelAcq => "atomic_store_explicit(&FARBE_FERTIG, 1, memory_order_release);\n\
            x = atomic_load_explicit(&FARBE_FERTIG, memory_order_acquire);",
        Shape::MergeAdd => "static void z_melde(uint32_t roh) {\n\
            uint32_t v = roh;\n\
            uint32_t k = gabbro_kern();\n\
            uint32_t z = atomic_load_explicit(&z_zellen[k], memory_order_relaxed);\n\
            z += v;\n\
            atomic_store_explicit(&z_zellen[k], z, memory_order_relaxed);\n\
            }",
        Shape::LockOps => "KAPPEN_nimm();\nKAPPEN_gib();",
        Shape::Volatile => "x = (*(volatile uint16_t *)(d->basis + 0xc));",
    }
}

/// **Nine rows in, nine verdicts out.** The inventory has eight measured
/// rows and one open row; the ruling answers five admissions, three
/// refusals, one open. Any other split means a row moved without its
/// ruling moving along.
#[test]
fn all_nine_shapes_are_ruled() {
    let all = Shape::all();
    assert_eq!(all.len(), 9, "one constructor per inventory row");
    let mut seen = std::collections::BTreeSet::new();
    for s in all {
        assert!(seen.insert(s as u8), "each row ruled once: {:?}", s);
    }
    let mut admits = 0;
    let mut refuses = 0;
    let mut open = 0;
    for s in all {
        match s.ruling() {
            Ruling::Admit { .. } => admits += 1,
            Ruling::Refuse { .. } => refuses += 1,
            Ruling::Open => open += 1,
        }
    }
    assert_eq!(admits, 5, "five single-access admissions");
    assert_eq!(refuses, 3, "three sequence refusals");
    assert_eq!(open, 1, "the volatile row stays open");
}

/// **The three refusals name exactly the two ruling guarantees.**
/// Compound assign needs exclusive access, guarded or not; the merge
/// triple needs single-writer-per-cell.
#[test]
fn refusals_name_the_ruling_guarantees() {
    let mut got: Vec<(&str, &str)> = Shape::all()
        .iter()
        .filter_map(|s| match s.ruling() {
            Ruling::Refuse { guarantee } => Some((s.name(), guarantee)),
            _ => None,
        })
        .collect();
    got.sort();
    assert_eq!(
        got,
        [
            ("guarded compound assign", "exclusive access"),
            ("relaxed merge-add", "single-writer-per-cell"),
            ("slot compound assign", "exclusive access"),
        ],
    );
}

/// **The scanner agrees with the ruling on every shape.** Admitted rows
/// scan clean and silent; refused rows scan to exactly one refusal under
/// the code with the ruling guarantee; the open row scans to one open
/// site and no refusal.
#[test]
fn scanner_agrees_with_ruling_on_every_shape() {
    for shape in Shape::all() {
        let report = tearing::check(shape_c(shape), &sharing());
        match shape.ruling() {
            Ruling::Admit { .. } => {
                assert!(
                    report.refusals.is_empty(),
                    "{}: admitted but refused: {:?}",
                    shape.name(),
                    report.refusals
                );
                assert!(
                    report.open.is_empty(),
                    "{}: admitted but open: {:?}",
                    shape.name(),
                    report.open
                );
            }
            Ruling::Refuse { guarantee } => {
                assert_eq!(
                    report.refusals.len(),
                    1,
                    "{}: refused, but not exactly once: {:?}",
                    shape.name(),
                    report.refusals
                );
                let r = &report.refusals[0];
                assert_eq!(r.code, tearing::CODE, "{}", shape.name());
                assert_eq!(r.kind.guarantee(), guarantee, "{}", shape.name());
                assert!(report.open.is_empty(), "{}", shape.name());
            }
            Ruling::Open => {
                assert!(
                    report.refusals.is_empty(),
                    "{}: open but refused: {:?}",
                    shape.name(),
                    report.refusals
                );
                assert_eq!(report.open.len(), 1, "{}", shape.name());
            }
        }
    }
}

/// **The guarantee words come from one register.** The refusal named by
/// the scan carries the same string the ruling names: a rewording on
/// either side breaks this test instead of drifting silently.
#[test]
fn guarantee_words_match_the_scanner() {
    for shape in [Shape::SlotCompound, Shape::GuardedCompound, Shape::MergeAdd] {
        let ruling_guarantee = match shape.ruling() {
            Ruling::Refuse { guarantee } => guarantee,
            other => panic!("{} is refused in the ruling, got {:?}", shape.name(), other),
        };
        let report = tearing::check(shape_c(shape), &sharing());
        assert_eq!(report.refusals.len(), 1, "{}", shape.name());
        assert_eq!(
            report.refusals[0].kind.guarantee(),
            ruling_guarantee,
            "scan and ruling disagree on {}",
            shape.name()
        );
    }
}

/// **A sequence on an undeclared name is a local fold, not shared
/// traffic.** The carrier set comes from the declarations; without the
/// name in the set the scan stays silent instead of inventing a carrier.
#[test]
fn compound_assign_to_an_undeclared_carrier_passes() {
    let report = tearing::check("q->slots[s].marke += 1;", &sharing());
    assert!(report.is_clean(), "{:?}", report.refusals);
    assert!(report.open.is_empty(), "{:?}", report.open);
}
