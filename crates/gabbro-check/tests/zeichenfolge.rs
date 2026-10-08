//! **Bounded strings -- the length-fact index rule, the closed positions and the scoped name
//! table** (fix lane F6, review G12 F4/F5, 2026-09-22).
//!
//! The gifts `1159`-`1168` carry one probe per rule; the pins here cover the edges a gift
//! would only repeat: which facts count (strict vs. non-strict bounds, signed names, the
//! `else` branch, the right side of `&&`), where a fact dies (a loop that assigns the index),
//! and the positions `N455`/`N465` close besides the gift sites.

use gabbro_syntax::diag::Stufe;

fn fehler(quelle: &str) -> Vec<String> {
    let (baum, mut absagen) = gabbro_syntax::lies("zeichenfolge", quelle);
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code.to_string())
        .collect()
}

fn einheit(kopf: &str, rumpf: &str) -> String {
    format!(
        "module z {{
impl fn nimm(s: string max 8, t: string max 8, i: u32 in 0 .. 100, j: i32 in -5 .. 5, b: bool) -> u32
    {kopf}
    effects {{ pure }}
    costs <= 64 ops
{{
{rumpf}
    return 0;
}}
}}"
    )
}

fn sauber(kopf: &str, rumpf: &str) {
    let f = fehler(&einheit(kopf, rumpf));
    assert!(f.is_empty(), "expected no error, got {f:?} for:\n{rumpf}");
}

fn faellt(kopf: &str, rumpf: &str, code: &str) {
    let f = fehler(&einheit(kopf, rumpf));
    assert!(f.iter().any(|c| c == code), "expected {code}, got {f:?} for:\n{rumpf}");
}

#[test]
fn laengenfakten_beweisen_den_index() {
    sauber("", "    if lenof(s) > 7 { let c = s[7]; }");
    sauber("", "    if 7 < lenof(s) { let c = s[7]; }");
    sauber("", "    if lenof(s) >= 8 { let c = s[7]; }");
    sauber("", "    if lenof(s) == 3 { let c = s[2]; }");
    sauber("", "    if i < lenof(s) { let c = s[i]; }");
    sauber("", "    if lenof(s) > i { let c = s[i]; }");
    sauber("", "    if b && i < lenof(s) { let c = s[i]; }");
    sauber("", "    if !(lenof(s) <= 4) { let c = s[4]; }");
    sauber("requires lenof(s) > 5", "    let c = s[5];");
    sauber("", "    if lenof(s) < 3 || b { return 1; }\n    let c = s[2];");
}

#[test]
fn was_keinen_index_beweist() {
    // The max proves nothing: an empty string holds no index 0.
    faellt("", "    let c = s[0];", "N454");
    // `>=` is not `>`: `lenof(s) >= 7` leaves index 7 unproven.
    faellt("", "    if lenof(s) >= 7 { let c = s[7]; }", "N454");
    // A fact about `t` is no fact about `s`.
    faellt("", "    if lenof(t) > 7 { let c = s[7]; }", "N454");
    // The `else` branch knows the negation, which proves nothing here.
    faellt("", "    if lenof(s) > 7 { return 1; } else { let c = s[7]; }", "N454");
    // A signed index name proves nothing, whatever its guard.
    faellt("", "    if j < lenof(s) { let c = s[j]; }", "N454");
    // No fact crosses into the right side of `&&` within one expression.
    faellt("", "    if i < lenof(s) && s[i] == s[i] { return 1; }", "N454");
    // An `||` guard proves neither side.
    faellt("", "    if lenof(s) > 7 || b { let c = s[7]; }", "N454");
    // After an `if` that does NOT always end, the negation is not known.
    faellt("", "    if lenof(s) < 3 { let x = 1; }\n    let c = s[2];", "N454");
}

#[test]
fn eine_schleife_toetet_ihre_fakten() {
    faellt(
        "",
        "    let mut k = i;
    if k < lenof(s) {
        retry warten until k == 0
            bounded 64 ops
            on_exceeded weg
            effects { pure }
        {
            let c = s[k];
            k = 0;
        }
    }",
        "N454",
    );
}

#[test]
fn zeichenketten_nur_an_zeichenkettenplaetzen() {
    faellt("", "    if s { return 1; }", "N455");
    faellt("", "    let x = !s;", "N455");
    faellt("", "    let x: u32 = s;", "N455");
    faellt("", "    let x = i + s;", "N455");
    faellt("", "    let mut u = s;\n    u += t;", "N453");
}

#[test]
fn verschachtelte_und_unaufgeloeste_zeichenketten() {
    faellt("", "    let a: [string max 2; 2] = 0;", "N465");
    faellt("", "    let n = unbekannt(s);", "N465");
}

#[test]
fn geschwisterbloecke_sind_eigene_bindungen() {
    sauber(
        "",
        "    if b { let x = s; let n = lenof(x); } else { let x = 5; let m = x + 1; }",
    );
    // Inner bindings end with their block: the outer `s` is still the string.
    faellt("", "    if b { let s2 = 5; }\n    let c = s + 1;", "N455");
}

// -- String cells in table slots (`N581`, SPRACHE-EFFIZIENZ #13) ---------------------------

fn zellen_einheit(rumpf: &str) -> String {
    format!(
        "module z {{
table Namen count 4 {{ slot {{ n : string max 8, }} }}
lock K protects {{ Namen }} rank 0 held <= 100 ops;
impl fn f(t : ptr<normal, rw> Namen, i : index into Namen, s : string max 8, k : string max 16) -> u32
    requires Held(K)
    effects {{ reads t.slots, writes t.slots, locks K }}
    costs <= 64 ops
{{
{rumpf}
    return 0;
}}
}}"
    )
}

fn zelle_sauber(rumpf: &str) {
    let f = fehler(&zellen_einheit(rumpf));
    assert!(f.is_empty(), "expected no error, got {f:?} for:\n{rumpf}");
}

fn zelle_faellt(rumpf: &str, code: &str) {
    let f = fehler(&zellen_einheit(rumpf));
    assert!(f.iter().any(|c| c == code), "expected {code}, got {f:?} for:\n{rumpf}");
}

#[test]
fn eine_zelle_wird_ganz_gelesen_und_ganz_geschrieben() {
    zelle_sauber("    let a : string max 8 = t.slots[i].n;");
    zelle_sauber("    let a : string max 16 = t.slots[i].n;");
    zelle_sauber("    let a = t.slots[i].n;\n    let m = lenof(a);");
    zelle_sauber("    t.slots[i].n = s;");
    zelle_sauber("    t.slots[i].n = \"hi\";");
    // The facts speak about the LOCAL.
    zelle_sauber("    let a : string max 8 = t.slots[i].n;\n    if lenof(a) > 3 { let c = a[3]; }");
}

#[test]
fn eine_zelle_an_ort_und_stelle_faellt() {
    zelle_faellt("    let m = lenof(t.slots[i].n);", "N581");
    zelle_faellt("    let c = t.slots[i].n[0];", "N581");
    zelle_faellt("    let m = t.slots[i].n + s;", "N581");
    zelle_faellt("    if t.slots[i].n == s { return 1; }", "N581");
    zelle_faellt("    t.slots[i].n += s;", "N581");
    zelle_faellt("    t.slots[i].n = t.slots[i].n;", "N581");
}

#[test]
fn die_kopierregel_gilt_an_der_zelle() {
    zelle_faellt("    let a : string max 4 = t.slots[i].n;", "N455");
    zelle_faellt("    t.slots[i].n = k;", "N455");
}

#[test]
fn ein_verbundfeld_bleibt_verweigert() {
    let f = fehler("module z { type R = { n : string max 8, }; }");
    assert!(f.iter().any(|c| c == "N465"), "{f:?}");
}
