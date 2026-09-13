//! **The footprint guard (E245-E249) over snippets.**
//!
//! The hint-level twin of `vertragsfuss.rs`: `beispiele/gift/915-919` pin the fall
//! over files, what stands here pins it over snippets -- each leg fires with cover
//! but without guard, and stays silent under `requires Held`. Hints, not errors:
//! the strict premise refuses ordinary single-threaded programs, so the rule flags
//! instead of refusing.

use gabbro_syntax::diag::Stufe;

fn hinweise(quelle: &str) -> Vec<String> {
    let (baum, mut absagen) = gabbro_syntax::lies("fusswache", quelle);
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Hinweis)
        .map(|a| a.code.to_string())
        .collect()
}

const KOPF: &str = "module test::fusswache {\n\
    static mut z : u32 = 0;\n\
    static mut frei : u32 = 0;\n\
    lock WACHE protects { z } rank 0 held <= 8 ops;\n";

const SCHREIBER: &str = "impl fn schreibt() effects { writes z, locks WACHE } costs <= 8 ops \
    {{ locks WACHE {{ z = 1; }} }}\n";

fn einheit(vertrag: &str, wirkungen: &str, rumpf: &str) -> String {
    format!(
        "{KOPF}\
        impl fn ziel() -> u32\n\
            {vertrag}\n\
            effects {{ {wirkungen} }}\n\
            costs   <= 8 ops\n\
        {{\n\
            {rumpf}\n\
        }}\n\
        {SCHREIBER}}}\n"
    )
}

#[test]
fn requires_mit_deckung_aber_ohne_wache_faellt() {
    let codes = hinweise(&einheit("requires z == 0", "reads z", "return 0;"));
    assert!(
        codes.iter().any(|c| c == "E245"),
        "covered but unguarded `requires` must flag E245: {codes:?}"
    );
}

#[test]
fn requires_unter_signaturwache_schweigt() {
    let codes = hinweise(&einheit(
        "requires Held(WACHE), z == 0",
        "reads z",
        "return 0;",
    ));
    assert!(codes.is_empty(), "guarded `requires` must stay silent: {codes:?}");
}

#[test]
fn ensures_mit_deckung_aber_ohne_wache_faellt() {
    let codes = hinweise(&einheit("ensures result == z", "reads z", "return 0;"));
    assert!(
        codes.iter().any(|c| c == "E246"),
        "covered but unguarded `ensures` must flag E246: {codes:?}"
    );
}

#[test]
fn ensures_unter_signaturwache_schweigt() {
    let codes = hinweise(&einheit(
        "requires Held(WACHE)\n    ensures result == z",
        "reads z",
        "return 0;",
    ));
    assert!(codes.is_empty(), "guarded `ensures` must stay silent: {codes:?}");
}

#[test]
fn rumpf_mit_deckung_aber_ohne_wache_faellt() {
    let codes = hinweise(&einheit("", "reads z", "return z;"));
    assert!(
        codes.iter().any(|c| c == "E247"),
        "covered but unguarded body read must flag E247: {codes:?}"
    );
}

#[test]
fn rumpf_unter_signaturwache_schweigt() {
    let codes = hinweise(&einheit("requires Held(WACHE)", "reads z", "return z;"));
    assert!(codes.is_empty(), "guarded body read must stay silent: {codes:?}");
}

#[test]
fn leser_ueber_unbeschriebenem_traeger_schweigt() {
    // `frei` is never written: no guard owed on any leg.
    let codes = hinweise(&einheit("requires frei == 0", "pure", "return 0;"));
    assert!(codes.is_empty(), "read-only carrier needs no guard: {codes:?}");
}

#[test]
fn rufer_ohne_wache_ueber_vertrag_des_gerufenen_faellt() {
    let quelle = format!(
        "{KOPF}\
        impl fn geber() -> u32\n\
            requires z == 0\n\
            effects {{ reads z }}\n\
            costs   <= 8 ops\n\
        {{\n\
            return 0;\n\
        }}\n\
        impl fn rufer() -> u32\n\
            effects {{ reads z }}\n\
            costs   <= 16 ops\n\
        {{\n\
            let x = geber();\n\
            return x;\n\
        }}\n\
        impl fn rufer2() -> u32\n\
            requires Held(WACHE)\n\
            effects {{ reads z }}\n\
            costs   <= 16 ops\n\
        {{\n\
            let x = geber();\n\
            return x;\n\
        }}\n\
        {SCHREIBER}}}\n"
    );
    let codes = hinweise(&quelle);
    assert!(
        codes.iter().any(|c| c == "E248"),
        "unguarded caller over a callee contract must flag E248: {codes:?}"
    );
    assert!(
        !codes.iter().any(|c| c == "E248")
            || codes.iter().filter(|c| *c == "E248").count() == 1,
        "the guarded twin caller must not flag E248 again: {codes:?}"
    );
}

#[test]
fn indirekter_ruf_ausserhalb_des_fusses_faellt() {
    let quelle = "module test::fusswache {\n\
        static mut z : u8 = 0;\n\
        lock WACHE protects { z } rank 0 held <= 8 ops;\n\
        type T = { senden : fn(u8) effects { writes z } costs <= 4 ops, };\n\
        impl fn prod(b : u8)\n\
            requires z == 0\n\
            effects { writes z }\n\
            costs <= 3 ops\n\
        {\n\
            z = b;\n\
        }\n\
        impl fn nimm() -> T\n\
            effects { pure }\n\
            costs <= 2 ops\n\
        {\n\
            return T(senden: &prod);\n\
        }\n\
        impl fn ruf(t : ptr<normal, r> T, b : u8)\n\
            effects { reads t, writes z }\n\
            costs <= 12 ops\n\
        {\n\
            t->senden(b);\n\
        }\n\
        impl fn ruf2(t : ptr<normal, r> T, b : u8)\n\
            requires Held(WACHE), z == 0\n\
            effects { reads t, reads z, writes z }\n\
            costs <= 12 ops\n\
        {\n\
            t->senden(b);\n\
        }\n\
        impl fn schreibt(v : u8) effects { writes z, locks WACHE } costs <= 8 ops \
        { locks WACHE { z = v; } }\n\
        }\n";
    let codes = hinweise(quelle);
    assert!(
        codes.iter().any(|c| c == "E249"),
        "indirect call outside the caller footprint must flag E249: {codes:?}"
    );
    assert!(
        codes.iter().filter(|c| *c == "E249").count() == 1,
        "the admitted twin caller must not flag E249 again: {codes:?}"
    );
}
