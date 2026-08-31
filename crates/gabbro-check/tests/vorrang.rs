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

fn erzeuge(pfad: &Path) -> String {
    let quelle = std::fs::read_to_string(pfad).unwrap_or_else(|e| panic!("{}: {e}", pfad.display()));
    let (baum, mut absagen) = gabbro_syntax::lies(&pfad.display().to_string(), &quelle);
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    let fehler: Vec<&str> = absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code)
        .collect();
    assert!(
        fehler.is_empty(),
        "die Vorrangprobe muss sauber durchgehen, sie faellt mit {fehler:?}:\n{}",
        absagen.zeige(&quelle)
    );
    let c = gabbro_check::emit::emittiere(&baum, &mut absagen);
    assert!(!c.is_empty(), "die Vorrangprobe emittiert NICHTS -- nichts gemessen");
    c
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

/// **The counter-probe, and it RUNS.**
///
/// Compiles the emitted C with exactly the command stage 9 of `pruefe-emission.sh` uses,
/// executes it and demands that every form agrees with its parenthesised twin. Measured on
/// 2026-08-31 against the unrepaired emitter: nine of the 25 pairs and two of the four
/// comparison forms disagreed, and `cc -Werror` refused the file outright.
#[test]
fn jede_form_rechnet_was_gabbro_meint() {
    let f = formen();
    assert_eq!(f.len(), 31, "25 Paare und 6 Grenzformen -- sonst misst die Probe nicht alles");
    let mut c = erzeuge(&probe());
    c.push_str(&treiber(&f));

    let d = std::env::temp_dir().join("gabbro-vorrang");
    std::fs::create_dir_all(&d).expect("das Arbeitsverzeichnis liegt schreibbar");
    let quelle = d.join("lauf.c");
    let ziel = d.join("lauf");
    std::fs::write(&quelle, &c).expect("das erzeugte C liegt schreibbar");

    // **`-Werror` stands here because the parenthesis heals TWO defects, not one.** Without
    // it `-Wparentheses` fires at three of the 25 pairs that compute correctly -- and stage 9
    // of `pruefe-emission.sh` runs exactly this command over every emitting file.
    let bau = Command::new("cc")
        .args(["-std=c11", "-O2", "-Wall", "-Wextra", "-Werror"])
        .arg("-o")
        .arg(&ziel)
        .arg(&quelle)
        .output();
    let bau = match bau {
        Ok(r) => r,
        // **A missing `cc` is a missing measurement, never a green one** (W1).
        Err(e) => panic!("`cc` laesst sich nicht starten ({e}) -- NICHTS gemessen"),
    };
    assert!(
        bau.status.success(),
        "das erzeugte C uebersetzt nicht unter `-Wall -Wextra -Werror`:\n{}\n{}",
        String::from_utf8_lossy(&bau.stderr),
        quelle.display()
    );

    let lauf = Command::new(&ziel)
        .output()
        .unwrap_or_else(|e| panic!("das uebersetzte Programm laeuft nicht ({e}) -- NICHTS gemessen"));
    assert!(lauf.status.success(), "das uebersetzte Programm bricht ab");
    let aus = String::from_utf8_lossy(&lauf.stdout);
    assert!(
        aus.contains(&format!("geprueft={} abweichungen=0", f.len())),
        "das ausgelieferte C rechnet etwas anderes als das Gepruefte:\n{aus}"
    );
    let _ = std::fs::remove_file(&quelle);
    let _ = std::fs::remove_file(&ziel);
}

/// **The poison probe: the text, pinned in BOTH directions.**
///
/// The running probe above dies when the emitter parenthesises too LITTLE. It does not die
/// when it parenthesises too MUCH -- wrapping every operand computes the right value and
/// passes `-Werror` too, and it would rewrite the emitted C of the whole corpus. Measured
/// on 2026-08-31: the C of all 485 corpus files is byte-identical across this change, and a
/// version that wraps indiscriminately breaks exactly that.
///
/// So each row says what MUST carry parentheses and what must NOT.
#[test]
fn die_klammer_steht_wo_sie_gebraucht_wird_und_sonst_nicht() {
    // (Gabbro expression, the C the emitter owes)
    let faelle: [(&str, &str); 9] = [
        // the flat level regroups in C -- the tree has to be written down
        ("a & b << c", "return (a & b) << c;"),
        ("a | b ^ c", "return (a | b) ^ c;"),
        // C and Gabbro agree here, and `-Wparentheses` still fires -- stage 9 uses `-Werror`
        ("a & b ^ c", "return (a & b) ^ c;"),
        ("a ^ b | c", "return (a ^ b) | c;"),
        // same operator throughout: no regrouping, no warning, and still parenthesised --
        // the rule is one rule, not a list of pairs
        ("a & b & c", "return (a & b) & c;"),
        // the comparison boundary: Gabbro puts the bit level below `==`, C puts it above
        ("a & b == c", "return (a & b) == c;"),
        // a bit operator over an arithmetic one: the parenthesis is C's own grouping, but
        // without it `-Wparentheses` fires
        ("a + b << c", "return (a + b) << c;"),
        // and the two that must stay BARE -- strip the bit level and Gabbro's remaining
        // hierarchy is C's, so a parenthesis here would be noise the corpus would notice
        ("a + b * c", "return a + b * c;"),
        ("a * b + c", "return a * b + c;"),
    ];
    for (ausdruck, erwartet) in faelle {
        let typ = if ausdruck.contains("==") { "bool" } else { "u32" };
        let quelle = format!(
            "module p {{ type K = u32 in 0 .. 7;\n\
             impl fn f(a : K, b : K, c : K) -> {typ}\n\
             effects {{ pure }} costs <= 16 ops {{ return {ausdruck}; }} }}"
        );
        let (baum, mut absagen) = gabbro_syntax::lies("probe.gab", &quelle);
        let _ = gabbro_check::pruefe(&baum, &mut absagen);
        let fehler: Vec<&str> = absagen
            .absagen
            .iter()
            .filter(|a| a.stufe == Stufe::Fehler)
            .map(|a| a.code)
            .collect();
        assert!(fehler.is_empty(), "`{ausdruck}` faellt mit {fehler:?}");
        let c = gabbro_check::emit::emittiere(&baum, &mut absagen);
        assert!(
            c.contains(erwartet),
            "`{ausdruck}` muss `{erwartet}` erzeugen. Erzeugt wurde:\n{}",
            c.lines()
                .filter(|l| l.contains("return"))
                .collect::<Vec<_>>()
                .join("\n")
        );
    }
}
