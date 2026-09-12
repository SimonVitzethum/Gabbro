//! Const certificate from the source (lane 121).
//!
//! The printer in `gabbro_check::konst_lean` translates a `const fn` body to
//! a Lean `Nat` function. This file pins that the printed Lean for the
//! 64-entry square table is exactly the translation of `quad(i)`, with the
//! VALUES coming from the checker's own constant folder (not hand numbers).

use gabbro_syntax::ast::{FnKlasse, FnRumpf, ItemArt, StmtArt};
use std::collections::HashMap;

const QUAD_QUELLE: &str = "module t {\n\
const fn quad(i : u32 in 0 .. 256) -> u32 effects { pure } costs <= 4 ops\n\
{ return i * i; } }";

// QUAD-CERT-BEGIN
const QUAD_CERT_ERWARTET: &str = r#"def quad (i : Nat) : Nat := i * i
def quadTabelle : List Nat := [0, 1, 4, 9, 16, 25, 36, 49, 64, 81, 100, 121, 144, 169, 196, 225, 256, 289, 324, 361, 400, 441, 484, 529, 576, 625, 676, 729, 784, 841, 900, 961, 1024, 1089, 1156, 1225, 1296, 1369, 1444, 1521, 1600, 1681, 1764, 1849, 1936, 2025, 2116, 2209, 2304, 2401, 2500, 2601, 2704, 2809, 2916, 3025, 3136, 3249, 3364, 3481, 3600, 3721, 3844, 3969]
def quadPruefe : Bool := List.all (fun (v, i) => v == quad i) quadTabelle.zipIdx
example : quadPruefe = true := by decide
"#;
// QUAD-CERT-END

/// The single-expression body and parameter name of the named `const fn`.
fn const_rumpf(baum: &gabbro_syntax::ast::Programm, name: &str) -> (String, gabbro_syntax::ast::Expr, String) {
    let mut fund: Option<(String, gabbro_syntax::ast::Expr, String)> = None;
    gabbro_check::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        if let ItemArt::Funktion(f) = &item.art {
            if f.name.text == name && matches!(f.klasse, Some(FnKlasse::Konst)) {
                if let FnRumpf::Block(b) = &f.rumpf {
                    if let [s] = &b.anweisungen[..] {
                        if let StmtArt::Return(Some(w)) = &s.art {
                            fund = Some((
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
    fund.unwrap_or_else(|| panic!("const fn {name} with a single return not found"))
}

#[test]
fn gedrucktes_lean_ist_genau_die_uebersetzung_von_quad() {
    let (baum, mut absagen) = gabbro_syntax::lies("quad.gab", QUAD_QUELLE);
    assert_eq!(absagen.fehler_zahl(), 0, "{}", absagen.zeige(QUAD_QUELLE));
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    let (modul, rumpf, param) = const_rumpf(&baum, "quad");
    assert_eq!(param, "i");
    // The VALUES come from the checker's own folder at 0..64.
    let u = gabbro_check::umgebung::Umgebung::sammle(&baum);
    let werte = gabbro_check::konst_lean::werte_tabelle(&u, &modul, "quad", 64);
    let erwartet: Vec<u128> = (0..64).map(|k| k * k).collect();
    assert_eq!(werte, Some(erwartet.clone()));
    // The DEFINING EQUATION is the translated source, not a hand formula.
    let leer: HashMap<String, String> = HashMap::new();
    assert_eq!(
        gabbro_check::konst_lean::funktion_lean("quad", "i", &rumpf, &leer),
        Some("def quad (i : Nat) : Nat := i * i".to_string())
    );
    // The whole certificate file, byte for byte.
    assert_eq!(
        gabbro_check::konst_lean::zertifikat_lean(
            "quad",
            "i",
            &rumpf,
            "quadTabelle",
            "quadPruefe",
            &erwartet,
            &leer
        ),
        Some(QUAD_CERT_ERWARTET.to_string())
    );
}

/// Parse `const K : u64 = <expr>;` and print the initializer.
fn ausdruck_von(ausdruck: &str) -> gabbro_syntax::ast::Expr {
    let quelle = format!("module t {{ const K : u64 = {ausdruck}; }}");
    let (baum, absagen) = gabbro_syntax::lies("probe.gab", &quelle);
    assert_eq!(absagen.fehler_zahl(), 0, "{}", absagen.zeige(&quelle));
    let mut fund = None;
    gabbro_check::fuer_jedes_item_im_modul(&baum, &mut |item, _| {
        if let ItemArt::Konst(k) = &item.art {
            fund = Some(k.wert.clone());
        }
    });
    fund.expect("const initializer not found")
}

fn drucke(ausdruck: &str) -> Option<String> {
    let leer: HashMap<String, String> = HashMap::new();
    gabbro_check::konst_lean::ausdruck_lean(&ausdruck_von(ausdruck), "i", &leer)
}

#[test]
fn jede_operatorfamilie_druckt_ihre_nat_form() {
    assert_eq!(drucke("2 * 3 + 1"), Some("2 * 3 + 1".to_string()));
    assert_eq!(drucke("i * i"), Some("i * i".to_string()));
    assert_eq!(drucke("i - 1"), Some("i - 1".to_string()));
    assert_eq!(drucke("7 / 2"), Some("7 / 2".to_string()));
    assert_eq!(drucke("7 % 2"), Some("7 % 2".to_string()));
    assert_eq!(drucke("1 << 10"), Some("Nat.shiftLeft 1 10".to_string()));
    assert_eq!(drucke("1024 >> 10"), Some("Nat.shiftRight 1024 10".to_string()));
    assert_eq!(drucke("3 & 5"), Some("Nat.land 3 5".to_string()));
    assert_eq!(drucke("3 | 5"), Some("Nat.lor 3 5".to_string()));
    assert_eq!(drucke("3 ^ 5"), Some("Nat.xor 3 5".to_string()));
    assert_eq!(drucke("wahr"), Some("1".to_string()));
    assert_eq!(drucke("falsch"), Some("0".to_string()));
    assert_eq!(drucke("!wahr"), Some("(if 1 == 0 then 1 else 0)".to_string()));
    assert_eq!(drucke("3 < 3"), Some("(if 3 < 3 then 1 else 0)".to_string()));
    assert_eq!(drucke("NKERNE"), Some("NKERNE".to_string()));
}

#[test]
fn verschachtelte_const_rufe_drucken_lean_applikation() {
    let quelle = "module t {\n\
const fn doppelt(n : u32 in 0 .. 256) -> u32 effects { pure } costs <= 4 ops\n\
{ return n + n; }\n\
const fn vierfach(n : u32 in 0 .. 256) -> u32 effects { pure } costs <= 4 ops\n\
{ return doppelt(doppelt(n)); } }";
    let (baum, absagen) = gabbro_syntax::lies("nest.gab", quelle);
    assert_eq!(absagen.fehler_zahl(), 0, "{}", absagen.zeige(quelle));
    let (_, rumpf, _) = const_rumpf(&baum, "vierfach");
    let mut funktionen: HashMap<String, String> = HashMap::new();
    funktionen.insert("doppelt".to_string(), "doppelt".to_string());
    assert_eq!(
        gabbro_check::konst_lean::ausdruck_lean(&rumpf, "n", &funktionen),
        Some("doppelt (doppelt n)".to_string())
    );
    // And the checker agrees on the value at a probe point.
    let u = gabbro_check::umgebung::Umgebung::sammle(&baum);
    let ruf = gabbro_check::konst_lean::ruf_ausdruck("vierfach", &[21]);
    assert_eq!(u.konst_wert("t", &ruf), Some(84));
}

#[test]
fn nicht_druckbares_ergibt_kein_zertifikat() {
    // Negation has no Nat form.
    assert_eq!(drucke("-i"), None);
    // Division by zero is no value in the checker, so no table follows.
    let quelle = "module t {\n\
const fn d(x : u32 in 0 .. 256) -> u32 effects { pure } costs <= 4 ops\n\
{ return 1 / (x - x); } }";
    let (baum, absagen) = gabbro_syntax::lies("div0.gab", quelle);
    assert_eq!(absagen.fehler_zahl(), 0, "{}", absagen.zeige(quelle));
    let (modul, _, _) = const_rumpf(&baum, "d");
    let u = gabbro_check::umgebung::Umgebung::sammle(&baum);
    assert_eq!(gabbro_check::konst_lean::werte_tabelle(&u, &modul, "d", 4), None);
}
