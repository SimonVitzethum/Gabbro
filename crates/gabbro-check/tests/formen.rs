//! **One construct, one form -- and the pass that runs before the lowering.**
//!
//! Gabbro lowers `narrow p to a ..< b else { S }` to `if (!(p < b)) { S }` (`emit.rs`,
//! `StmtArt::Narrow`). The two spellings therefore denote **the same program**, and any pass
//! that answers them differently is reading the source instead of the language.
//!
//! On 2026-08-31 M2 did exactly that: the arm of a `narrow` ran as straight-line code, its
//! consumption was credited to the main path, and the `griff_weg(g)` after it was
//! *"consumed a second time"*. The `if` spelling of the same function was silent. **Fourth
//! instance of that class** -- `D018`, `D017` twice, `K003`.
//!
//! This file is the generic comparison the single case pulls behind it. It asks **one**
//! question of **every** construct that carries a block:
//!
//! > *Does this block lie on the main path?*
//!
//! It is measured with a linear witness consumed INSIDE the block and once more AFTER it.
//! If `L104` falls, the block lay on the main path; if it is clean, the block was a branch.
//! **The answer has to be the one the lowering gives** -- and where it is not, the
//! difference stands here as a line and not in someone's head.

use gabbro_syntax::diag::Stufe;

/// The frame every construct is measured in. It carries everything any one of them needs --
/// a lock, an RCU domain, an atomic, an invariant, a reason and a diverging function -- so
/// that the ten cases differ only in the body. *One frame per case would be a second
/// difference.*
const RAHMEN: &str = r#"module app::t {
static mut hinterlegt : u32 in 4 .. 16 = 4;
static mut zaehler : u32 in 0 .. 99 = 0;
static mut frei : option index into RTab = None;
lock L protects { zaehler } rank 0 held <= 100 ops;
rcu D protects { RTab } reclaims frei;
atomic z : u32 publishes nothing relaxed;
table RTab count 4 {
    slot { da : bool, }
}
table Arena count 16 {
    slot { belegt : bool, }

    invariant nie_leer cost O(1) runs online :
        forall s in slots of Self : Self.slots[s].belegt == Self.slots[s].belegt;
}
reason Grund {
    Weg = 1 "weg"
    exhaustive
}
linear ghost type Griff;
extern fn griff_weg(g : Griff) effects { consumes g } costs <= 0 ops;
extern fn hol() -> u32 or Grund effects { pure } costs <= 1 ops;
extern fn nie() -> never effects { diverges } costs <= 0 ops;
"#;

/// The codes the frame itself produces, which say nothing about the constructs. **They stand
/// here by name** so that a new one shows up instead of disappearing into a filter: `H008`
/// is the lock nobody takes, `E010` the reading half of the exchange.
const RAHMENRAUSCHEN: &[&str] = &["H008", "E010"];

fn codes(wirkungen: &str, rumpf: &str) -> Vec<String> {
    let q = format!(
        "{RAHMEN}impl fn f(a : ptr<normal, r> Arena, i : index into Arena, g : Griff)\n\
         \x20   effects {{ {wirkungen} }}\n\
         \x20   costs   <= 900 ops\n{{\n{rumpf}}}\n}}\n"
    );
    let (baum, mut absagen) = gabbro_syntax::lies("formen.gab", &q);
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    let mut aus: Vec<String> = absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler || a.stufe == Stufe::Hinweis)
        .map(|a| a.code.to_string())
        .filter(|c| !RAHMENRAUSCHEN.contains(&c.as_str()))
        .collect();
    aus.sort();
    aus.dedup();
    // A frame that no longer parses makes every line below it a statement about nothing.
    // **That falls here, and not as an empty list of codes.**
    assert!(
        !aus.iter().any(|c| c.starts_with('P') || c.starts_with("N04")),
        "the frame itself falls: {aus:?}\n{q}"
    );
    aus
}

/// **The table.** One row per construct: the body, and the codes that have to come out.
///
/// | construct | block is | measured |
/// |---|---|---|
/// | `if` without `else`, branch returns | a branch | clean |
/// | `narrow … else`, arm returns | a branch | clean |
/// | `let … else`, arm diverges | a branch | clean |
/// | `locks L { … }` | **the main path** | `L104` |
/// | `observes D { … }` | **the main path** | `L104` |
/// | `breaking m { … }` | **the main path** | `L104` |
/// | `exchange update(v) { … }` | **the main path** | `L104` |
/// | `traverse … { … }` | a loop | `L108` |
///
/// The upper three stood in the lower half until 2026-08-31, all three with `L104`: **for M2
/// the one-armed branches were bodies.**
#[test]
fn jeder_einarmige_zweig_ist_ein_zweig_und_kein_rumpf() {
    // `if` without `else` -- the reference form. It was always right, and it is the yardstick.
    assert!(
        codes(
            "reads hinterlegt, consumes g",
            "    if i >= hinterlegt { griff_weg(g); return; }\n    griff_weg(g);\n"
        )
        .is_empty(),
        "`if` without `else` is a branch"
    );
    // `narrow … else` -- **the same program**, the same C form, `L104` until 2026-08-31.
    assert!(
        codes(
            "reads hinterlegt, consumes g",
            "    narrow i to 0 ..< hinterlegt else { griff_weg(g); return; }\n    griff_weg(g);\n"
        )
        .is_empty(),
        "`narrow … else` lowers to exactly this `if` -- another answer is a pass error"
    );
    // `let … else` -- the arm diverges. `S002` demands precisely that; M2 knew only the
    // `return` half of it.
    assert!(
        codes(
            "consumes g",
            "    let x = hol() else (e) { griff_weg(g); nie(); }\n    griff_weg(g);\n"
        )
        .is_empty(),
        "a diverging `let … else` arm does not put its state into the join"
    );
}

/// The other half of the table: the bodies that really do lie on the main path.
///
/// **It is not decoration.** A pass that heals the one-armed branches by declaring every
/// block a branch passes the upper half and lets every double consumption inside a `locks`
/// body through. *The two halves together are the statement.*
#[test]
fn ein_rumpf_auf_dem_hauptweg_bleibt_ein_rumpf() {
    for (name, wirkungen, rumpf) in [
        ("locks", "locks L, consumes g", "    locks L { griff_weg(g); }\n    griff_weg(g);\n"),
        ("observes", "consumes g", "    observes D { griff_weg(g); }\n    griff_weg(g);\n"),
        ("breaking", "consumes g", "    breaking nie_leer { griff_weg(g); }\n    griff_weg(g);\n"),
        (
            "exchange update",
            "writes z, consumes g",
            "    let alt = z exchange update(v) { griff_weg(g); };\n    griff_weg(g);\n",
        ),
    ] {
        let c = codes(wirkungen, rumpf);
        assert!(
            c.contains(&"L104".to_string()),
            "the body of `{name}` runs on the main path and consumes there: {c:?}"
        );
    }
    // A loop body runs OFTEN -- that is `L108` and not `L104`, and the difference is the
    // whole statement of the rule.
    let c = codes(
        "reads a.slots, consumes g",
        "    traverse s over slots of a by unvisited { griff_weg(g); }\n",
    );
    assert!(c.contains(&"L108".to_string()), "a loop body consumes once per pass: {c:?}");
}

/// **The arm is still READ.**
///
/// The obvious wrong way from "body" to "branch" is to skip the arm: the state after it then
/// comes out right as well. This probe stands against that -- both calls are INSIDE the arm,
/// and whoever does not walk it sees neither.
///
/// *Measured: a mutation that drops the `gehe` over the arm falls exactly here.*
#[test]
fn der_arm_wird_gelaufen_und_nicht_uebersprungen() {
    for (name, wirkungen, rumpf) in [
        (
            "narrow",
            "reads hinterlegt, consumes g",
            "    narrow i to 0 ..< hinterlegt else { griff_weg(g); griff_weg(g); return; }\n    \
             griff_weg(g);\n",
        ),
        (
            "let … else",
            "consumes g",
            "    let x = hol() else (e) { griff_weg(g); griff_weg(g); nie(); }\n    griff_weg(g);\n",
        ),
    ] {
        let c = codes(wirkungen, rumpf);
        assert!(
            c.contains(&"L104".to_string()),
            "consuming twice INSIDE the `{name}` arm stays a double consumption: {c:?}"
        );
    }
}

/// **And the other direction of the same line: the arm no longer leaks onto the main path.**
///
/// Whoever removes the false alarm without building the branch keeps the leak: `g` is
/// consumed ONLY in the arm, the main path walks past it and leaves it lying. The old pass
/// saw `g` as consumed, because the arm had done it for the main path too, and said nothing.
///
/// *A false alarm and a missed leak out of the same line.*
#[test]
fn was_nur_im_arm_verbraucht_wird_leckt_auf_dem_hauptweg() {
    let c = codes(
        "reads hinterlegt, consumes g",
        "    narrow i to 0 ..< hinterlegt else { griff_weg(g); return; }\n    let k = i;\n",
    );
    assert!(
        c.contains(&"L101".to_string()),
        "the main path does not consume `g` -- a leak against the function's own promise: {c:?}"
    );
}

/// **What the comparison does NOT say** (W10).
///
/// The two forms are not interchangeable, and that is a statement about the LANGUAGE and not
/// a finding: `M105` demands that the arm of a `narrow` return or diverge, and an `if` may
/// fall through. **`narrow … else { S }` is therefore strictly narrower than
/// `if !cond { S }`** -- every `narrow` can be written as an `if`, not every `if` as a
/// `narrow`.
///
/// The comparison holds for the intersection: the cases in which the arm ends. There the
/// answer has to be the same, and there it is, since today.
#[test]
fn die_beiden_formen_sind_nicht_gleich_weit() {
    let c = codes(
        "reads hinterlegt, consumes g",
        "    narrow i to 0 ..< hinterlegt else { griff_weg(g); }\n    griff_weg(g);\n",
    );
    assert!(
        c.contains(&"M105".to_string()),
        "a falling-through `narrow` arm cannot be written at all: {c:?}"
    );
    // The same line as an `if` is a legal program -- and a leak that `L103` names. *The two
    // answers differ because the two programs do.*
    let w = codes(
        "reads hinterlegt, consumes g",
        "    if i >= hinterlegt { griff_weg(g); }\n    griff_weg(g);\n",
    );
    assert!(!w.contains(&"M105".to_string()), "an `if` may fall through: {w:?}");
    assert!(w.contains(&"L103".to_string()), "and then it is a leak on one path: {w:?}");
}
