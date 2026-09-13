//! Lane 111 -- compile-time constants, first cut (PLAN-BITS.md section 6).
//!
//! The checker evaluates total, effect-free `const` initializers and const
//! tables element-wise (`K190`-`K194` in `konstanten.rs`); the emitter lowers
//! a const table to one `static const` C array; `konstanten::certificate`
//! prints the evaluated values as a Lean certificate (encoding N). Three
//! sides, each pinned:
//!
//! * the checker takes the fragment and refuses the rest, by code, one fault
//!   keeping one refusal;
//! * the emitter writes the folded values, and the generated C compiles and
//!   computes them (summed at run time);
//! * the printed certificate carries the same literal the Lean witness
//!   (`Konstanten.squares64`) closes by `decide` -- a drift breaks this
//!   file, and the `decide` itself breaks `./lean-bau`.
//!
//! Lane 121: the defining equation is no longer handed in --
//! `konst_lean` translates the `const fn` body, and
//! `certificate_of_const_fn` assembles values plus translation, so Lean
//! checks the values against the SOURCE.

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

fn errors(source: &str) -> Vec<&'static str> {
    codes(source)
        .into_iter()
        .filter(|(_, s)| *s == Stufe::Fehler)
        .map(|(c, _)| c)
        .collect()
}

fn falls_only_with(source: &str, expected: &[&str]) {
    let f = errors(source);
    assert_eq!(
        f,
        expected,
        "exactly {expected:?} should fall, fell {f:?}\n{source}"
    );
}

fn falls_with(source: &str, code: &str) {
    let f = errors(source);
    assert!(
        f.contains(&code),
        "expected {code} among {f:?}\n{source}"
    );
}

fn falls_clean(source: &str) {
    let f = errors(source);
    assert!(f.is_empty(), "clean, but falls with {f:?}\n{source}");
}

fn emit_clean(source: &str) -> String {
    let (baum, mut absagen) = gabbro_syntax::lies("<probe>", source);
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    assert!(
        absagen.fehler_zahl() == 0,
        "emits only what checks:\n{}",
        absagen.zeige(source)
    );
    gabbro_check::emit::emittiere(&baum, &mut absagen)
}

// -- the fragment: literals, consts, arithmetic/bit operators, pure calls ---

const QUAD: &str = "const fn quad(i : u32 in 0 .. 64) -> u32 effects { pure } costs <= 4 ops { return i * i; }";

#[test]
fn scalar_fragment_accepted() {
    falls_clean(&format!(
        "module t {{\n\
         const A : u32 = 6 * 7;\n\
         const B : u32 = A + 2 * (A ^ 3) - (A >> 1);\n\
         {QUAD}\n\
         const C : u32 = quad(6);\n\
         const D : u32 = B - 3;\n\
         impl fn f() -> u32 effects {{ pure }} costs <= 4 ops {{ return C; }}\n\
         }}"
    ));
}

#[test]
fn table_over_const_fn_accepted_elementwise() {
    falls_clean(&format!(
        "module t {{\n\
         {QUAD}\n\
         const Q : [u32; 4] = [quad(0), quad(1), quad(2), quad(3)];\n\
         impl fn f() -> u32 effects {{ pure }} costs <= 4 ops {{ return Q[2]; }}\n\
         }}"
    ));
}

// -- the refusals, one fault keeping one refusal -----------------------------

#[test]
fn k190_table_read_in_element() {
    falls_only_with(
        "module t {\n\
         table T count 4 { slot { a : u32, } }\n\
         const Q : [u32; 2] = [1, T.slots[0].a];\n\
         }",
        &["K190"],
    );
}

#[test]
fn k190_pure_block_call_outside_fragment() {
    // A pure block-bodied call is outside the fragment: only single-return
    // `const fn` bodies evaluate. `m1` types the call without a word, so the
    // one refusal below is the only one.
    falls_only_with(
        "module t {\n\
         impl fn gib() -> u32 effects { pure } costs <= 2 ops { return 7; }\n\
         const A : u32 = gib();\n\
         }",
        &["K190"],
    );
}

#[test]
fn k191_laenge_gegen_anzahl() {
    falls_only_with(
        "module t {\nconst Q : [u32; 3] = [1, 2];\n}",
        &["K191"],
    );
}

#[test]
fn table_body_const_is_held() {
    // A table carries its own consts, and the item walk never yields them --
    // the pass descends into the table body itself. Same refusal as outside.
    falls_only_with(
        "module t {\ntable T count 2 { slot { a : u32, } const Q : [u32; 3] = [1, 2]; }\n}",
        &["K191"],
    );
}

#[test]
fn k192_impure_caller() {
    falls_only_with(
        "module t {\n\
         static mut Z : u32 = 0;\n\
         impl fn hol() -> u32 effects { reads Z } costs <= 2 ops { return Z; }\n\
         const A : u32 = hol();\n\
         }",
        &["K192"],
    );
}

#[test]
fn k192_through_const_fn() {
    // The impurity hides one call deep: `mittel` is pure and transparent, the
    // `hol()` inside it is not. The refusal stands at the inner site.
    falls_with(
        "module t {\n\
         static mut Z : u32 = 0;\n\
         impl fn hol() -> u32 effects { reads Z } costs <= 2 ops { return Z; }\n\
         const fn mittel() -> u32 effects { pure } costs <= 4 ops { return hol(); }\n\
         const A : u32 = mittel();\n\
         }",
        "K192",
    );
}

#[test]
fn k193_cycle_through_const() {
    // A bare two-cycle: no arithmetic, so no range rule speaks beside the
    // recursion one -- the file owes nothing but K193, once per member.
    let quelle = "module t {\nconst A : u32 = B;\nconst B : u32 = A;\n}";
    falls_with(quelle, "K193");
    let f = errors(quelle);
    assert!(
        f.iter().all(|c| *c == "K193"),
        "a const cycle owes nothing but K193, fell {f:?}"
    );
}

#[test]
fn k194_element_out_of_range() {
    falls_only_with(
        "module t {\nconst Q : [u8; 2] = [1, 300];\n}",
        &["K194"],
    );
}

// -- the emitter writes the folded values -------------------------------------

#[test]
fn table_lowers_to_static_array() {
    let c = emit_clean(&format!(
        "module t {{\n\
         {QUAD}\n\
         const Q : [u32; 4] = [quad(0), quad(1), quad(2), quad(3)];\n\
         impl fn f() -> u32 effects {{ pure }} costs <= 4 ops {{ return Q[3]; }}\n\
         }}"
    ));
    assert!(
        c.contains("static const uint32_t Q[4] __attribute__((unused)) = {0u, 1u, 4u, 9u};"),
        "the folded values stand in the C:\n{c}"
    );
}

#[test]
fn table_computes_at_runtime() {
    // The whole 64-entry square table, evaluated element-wise through 64
    // `quad` calls, read back at run time: entry 63 is 3969, entry 7 is 49.
    let c = emit_clean(&format!(
        "module t {{\n\
         {QUAD}\n\
         const Q : [u32; 64] = [{}];\n\
         impl fn wert(a : u32 in 0 .. 63, b : u32 in 0 .. 63) -> u64 effects {{ pure }} costs <= 16 ops {{\n\
         let x : u64 = Q[a];\n\
         let y : u64 = Q[b];\n\
         return x + y;\n}}\n}}",
        (0..64)
            .map(|i| format!("quad({i})"))
            .collect::<Vec<_>>()
            .join(", ")
    ));
    assert!(
        c.contains("static const uint32_t Q[64]"),
        "the 64-entry table stands in the C:\n{c}"
    );
    let mut prog = c;
    prog.push_str(
        "\n#include <stdio.h>\n\nint main(void) {\n\
        \x20   unsigned long long got = (unsigned long long)(wert(63u, 7u));\n\
        \x20   unsigned long long want = 4018ull;\n\
        \x20   if (got != want) { printf(\"MISMATCH got=%llu want=%llu\\n\", got, want); return 1; }\n\
        \x20   printf(\"squares-ok\\n\");\n\
        \x20   return 0;\n}\n",
    );
    let d = std::env::var("TMPDIR").map(std::path::PathBuf::from).unwrap_or_else(|_| std::env::temp_dir()).join("gabbro-konstanten");
    std::fs::create_dir_all(&d).expect("scratch dir is writable");
    let c_path = d.join("run.c");
    let bin_path = d.join("run");
    std::fs::write(&c_path, &prog).expect("the generated C is writable");
    let bau = Command::new("cc")
        .args(["-std=c11", "-O2", "-Wall", "-Wextra", "-Werror"])
        .arg("-o")
        .arg(&bin_path)
        .arg(&c_path)
        .output();
    let bau = match bau {
        Ok(r) => r,
        Err(e) => panic!("`cc` does not start ({e}) -- NOTHING measured"),
    };
    assert!(
        bau.status.success(),
        "the generated C does not compile under `-Wall -Wextra -Werror`:\n{}\n{}",
        String::from_utf8_lossy(&bau.stderr),
        c_path.display()
    );
    let lauf = Command::new(&bin_path)
        .output()
        .unwrap_or_else(|e| panic!("the compiled program does not run ({e}) -- NOTHING measured"));
    assert!(lauf.status.success(), "the compiled program aborts");
    assert!(
        String::from_utf8_lossy(&lauf.stdout).contains("squares-ok"),
        "the shipped C reads something other than the folded table"
    );
    let _ = std::fs::remove_file(&c_path);
    let _ = std::fs::remove_file(&bin_path);
}

// -- the certificate: printed values meet the Lean witness -----------------

/// The 64 squares, as the checker prints them and as `Konstanten.lean`
/// carries them: one literal, two readers, no drift between them. The
/// defining function is translated from the `quad` source (lane 121),
/// not handed in.
#[test]
fn certificate_meets_witness() {
    let values: Vec<u64> = (0..64).map(|i| i * i).collect();
    let (baum, _) = gabbro_syntax::lies("<probe>", &format!("module t {{{QUAD}}}"));
    let (_, body, _) = const_fn_body(&baum, "quad");
    let leer: std::collections::HashMap<String, String> = std::collections::HashMap::new();
    let cert = gabbro_check::konstanten::certificate_of_const_fn(
        "sq", &values, "quad", "i", &body, &leer,
    )
    .expect("quad is in the printable fragment");
    assert!(
        cert.contains("def quad (i : Nat) : Nat := i * i"),
        "the translated SOURCE stands in the certificate:\n{cert}"
    );
    assert!(
        cert.contains("def sqVals : List Nat :=") && cert.contains("(sqVals.zipIdx).all (fun p => p.1 == quad p.2)"),
        "values plus the translated function as a List.all predicate:\n{cert}"
    );
    assert!(
        cert.contains("theorem sq_zert : sqOk = true := by decide"),
        "closed by decide, encoding N:\n{cert}"
    );
    let wurzel = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join("grammatik")
        .join("Grammatik")
        .join("Konstanten.lean");
    let lean =
        std::fs::read_to_string(&wurzel).unwrap_or_else(|e| panic!("{}: {e}", wurzel.display()));
    let literal = format!(
        "[{}]",
        values
            .iter()
            .map(|w| w.to_string())
            .collect::<Vec<_>>()
            .join(", ")
    );
    // The Lean file wraps the literal over lines; the comparison ignores
    // layout, so only the value sequence joins the two readers.
    let flach = |s: &str| s.chars().filter(|c| !c.is_whitespace()).collect::<String>();
    assert!(
        flach(&lean).contains(&flach(&literal)),
        "the printed literal drifts from squares64 -- the decide would close over other values"
    );
    assert!(
        flach(&lean).contains(&flach("konstZert squares64 (fun i v => v == quad i) = true := by decide")),
        "the witness closes the same shape the printer prints"
    );
}

// -- lane 121: the printed Lean IS the translated source -------------------
// The VALUES below come from the checker's own folder at 0..64 (not hand
// numbers); the DEFINING FUNCTION is the translated `quad` body.

use gabbro_syntax::ast::{FnKlasse, FnRumpf, ItemArt, StmtArt};

// SQUARES-CERT-BEGIN
const SQUARES_CERT_EXPECTED: &str = r#"-- Compile-time certificate printed by gabbro-check (lanes 111/121):
-- the evaluated values of const-table `sq` and their defining
-- function, translated from the const fn source, as a `List.all`
-- predicate (encoding N).
def quad (i : Nat) : Nat := i * i
def sqVals : List Nat :=
  [0, 1, 4, 9, 16, 25, 36, 49, 64, 81, 100, 121, 144, 169, 196, 225, 256, 289, 324, 361, 400, 441, 484, 529, 576, 625, 676, 729, 784, 841, 900, 961, 1024, 1089, 1156, 1225, 1296, 1369, 1444, 1521, 1600, 1681, 1764, 1849, 1936, 2025, 2116, 2209, 2304, 2401, 2500, 2601, 2704, 2809, 2916, 3025, 3136, 3249, 3364, 3481, 3600, 3721, 3844, 3969]
def sqOk : Bool := (sqVals.zipIdx).all (fun p => p.1 == quad p.2)
theorem sq_zert : sqOk = true := by decide
"#;
// SQUARES-CERT-END

/// The single-expression body and parameter name of the named `const fn`,
/// with the module path the folder resolves it under.
fn const_fn_body(
    baum: &gabbro_syntax::ast::Programm,
    name: &str,
) -> (String, gabbro_syntax::ast::Expr, String) {
    let mut found: Option<(String, gabbro_syntax::ast::Expr, String)> = None;
    gabbro_check::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        if let ItemArt::Funktion(f) = &item.art {
            if f.name.text == name && matches!(f.klasse, Some(FnKlasse::Konst)) {
                if let FnRumpf::Block(b) = &f.rumpf {
                    if let [s] = &b.anweisungen[..] {
                        if let StmtArt::Return(Some(w)) = &s.art {
                            found = Some((
                                modul.to_string(),
                                w.clone(),
                                f.parameter[0].name.text.clone(),
                            ));
                        }
                    }
                }
            }
        }
    });
    found.unwrap_or_else(|| panic!("const fn {name} with a single return not found"))
}

#[test]
fn printed_lean_is_the_translation_of_quad() {
    let (baum, mut absagen) = gabbro_syntax::lies("quad.gab", &format!("module t {{{QUAD}}}"));
    assert_eq!(absagen.fehler_zahl(), 0, "{}", absagen.zeige(&format!("module t {{{QUAD}}}")));
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    let (modul, body, param) = const_fn_body(&baum, "quad");
    assert_eq!(param, "i");
    // The VALUES come from the checker's own folder at 0..64.
    let u = gabbro_check::umgebung::Umgebung::sammle(&baum);
    let werte = gabbro_check::konst_lean::werte_tabelle(&u, &modul, "quad", 64);
    let erwartet: Vec<u128> = (0..64).map(|k| k * k).collect();
    assert_eq!(werte, Some(erwartet));
    let values: Vec<u64> = (0..64).map(|k| k * k).collect();
    // The whole certificate file, byte for byte: translated function plus
    // evaluated table, no hand equation anywhere.
    let leer: std::collections::HashMap<String, String> = std::collections::HashMap::new();
    assert_eq!(
        gabbro_check::konstanten::certificate_of_const_fn(
            "sq", &values, "quad", "i", &body, &leer
        ),
        Some(SQUARES_CERT_EXPECTED.to_string())
    );
}

/// Parse `const K : u64 = <expr>;` and print the initializer.
fn const_init_of(expr: &str) -> gabbro_syntax::ast::Expr {
    let quelle = format!("module t {{ const K : u64 = {expr}; }}");
    let (baum, absagen) = gabbro_syntax::lies("probe.gab", &quelle);
    assert_eq!(absagen.fehler_zahl(), 0, "{}", absagen.zeige(&quelle));
    let mut found = None;
    gabbro_check::fuer_jedes_item_im_modul(&baum, &mut |item, _| {
        if let ItemArt::Konst(k) = &item.art {
            found = Some(k.wert.clone());
        }
    });
    found.expect("const initializer not found")
}

fn prints_as(expr: &str) -> Option<String> {
    let leer: std::collections::HashMap<String, String> = std::collections::HashMap::new();
    gabbro_check::konst_lean::ausdruck_lean(&const_init_of(expr), "i", &leer)
}

#[test]
fn every_operator_family_prints_its_nat_form() {
    assert_eq!(prints_as("2 * 3 + 1"), Some("(2 * 3) + 1".to_string()));
    assert_eq!(prints_as("i * i"), Some("i * i".to_string()));
    assert_eq!(prints_as("i - 1"), Some("i - 1".to_string()));
    assert_eq!(prints_as("7 / 2"), Some("7 / 2".to_string()));
    assert_eq!(prints_as("7 % 2"), Some("7 % 2".to_string()));
    assert_eq!(prints_as("1 << 10"), Some("Nat.shiftLeft 1 10".to_string()));
    assert_eq!(prints_as("1024 >> 10"), Some("Nat.shiftRight 1024 10".to_string()));
    assert_eq!(prints_as("3 & 5"), Some("Nat.land 3 5".to_string()));
    assert_eq!(prints_as("3 | 5"), Some("Nat.lor 3 5".to_string()));
    assert_eq!(prints_as("3 ^ 5"), Some("Nat.xor 3 5".to_string()));
    assert_eq!(prints_as("true"), Some("1".to_string()));
    assert_eq!(prints_as("false"), Some("0".to_string()));
    assert_eq!(prints_as("!true"), Some("(if 1 == 0 then 1 else 0)".to_string()));
    assert_eq!(prints_as("3 < 3"), Some("(if 3 < 3 then 1 else 0)".to_string()));
    assert_eq!(prints_as("NKERNE"), Some("NKERNE".to_string()));
}

#[test]
fn nested_const_calls_print_as_lean_application() {
    let quelle = "module t {\n\
const fn doppelt(n : u32 in 0 .. 256) -> u32 effects { pure } costs <= 4 ops\n\
{ return n + n; }\n\
const fn plusEins(n : u32 in 0 .. 256) -> u32 effects { pure } costs <= 4 ops\n\
{ return n + 1; }\n\
const fn zweimalPlusEins(n : u32 in 0 .. 256) -> u32 effects { pure } costs <= 4 ops\n\
{ return doppelt(plusEins(n)); } }";
    let (baum, absagen) = gabbro_syntax::lies("nest.gab", quelle);
    assert_eq!(absagen.fehler_zahl(), 0, "{}", absagen.zeige(quelle));
    let (_, body, _) = const_fn_body(&baum, "zweimalPlusEins");
    let mut funktionen: std::collections::HashMap<String, String> = std::collections::HashMap::new();
    funktionen.insert("doppelt".to_string(), "doppelt".to_string());
    funktionen.insert("plusEins".to_string(), "plusEins".to_string());
    assert_eq!(
        gabbro_check::konst_lean::ausdruck_lean(&body, "n", &funktionen),
        Some("doppelt (plusEins n)".to_string())
    );
    // And the checker agrees on the value at a probe point.
    // (Self-nesting like `doppelt(doppelt(n))` stays `None`: the recursion
    // guard names functions, not calls, and keeps rejecting it.)
    let u = gabbro_check::umgebung::Umgebung::sammle(&baum);
    let ruf = gabbro_check::konst_lean::ruf_ausdruck("zweimalPlusEins", &[21]);
    assert_eq!(u.konst_wert("t", &ruf), Some(44));
}

#[test]
fn unprintable_yields_no_certificate() {
    // Negation has no Nat form.
    assert_eq!(prints_as("-i"), None);
    // Division by zero is no value in the checker, so no table follows.
    let quelle = "module t {\n\
const fn d(x : u32 in 0 .. 256) -> u32 effects { pure } costs <= 4 ops\n\
{ return 1 / (x - x); } }";
    let (baum, absagen) = gabbro_syntax::lies("div0.gab", quelle);
    assert_eq!(absagen.fehler_zahl(), 0, "{}", absagen.zeige(quelle));
    let (modul, _, _) = const_fn_body(&baum, "d");
    let u = gabbro_check::umgebung::Umgebung::sammle(&baum);
    assert_eq!(gabbro_check::konst_lean::werte_tabelle(&u, &modul, "d", 4), None);
}
