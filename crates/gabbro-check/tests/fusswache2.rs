//! **The flagship footprint premise (`N290`-`N294`) over snippets.**
//!
//! The error-level twin of `fusswache.rs`: each leg refuses where the flagship's
//! decidable premise (`FussS` with thread-local carriers, guards at the access,
//! lock invariants, floors) is violated, and stays silent where the old hints
//! fired but the new premise holds (single thread, guard at the access).
//! Errors, not hints: the corpus stays green under the new rule.

use gabbro_syntax::diag::Stufe;

fn fehler(quelle: &str) -> Vec<String> {
    let (baum, mut absagen) = gabbro_syntax::lies("fusswache2", quelle);
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code.to_string())
        .collect()
}

fn hinweise(quelle: &str) -> Vec<String> {
    let (baum, mut absagen) = gabbro_syntax::lies("fusswache2", quelle);
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Hinweis)
        .map(|a| a.code.to_string())
        .collect()
}

const KOPF: &str = "module test::fusswache2 {\n\
    table G count 2 {\n\
        slot {\n\
            v : u32,\n\
        }\n\
    }\n\
    table P count 2 {\n\
        slot {\n\
            v : u32,\n\
        }\n\
    }\n";

#[test]
fn einzelner_faden_schweigt_wo_e247_hinweist() {
    // No `concurrent`: the single driver thread owns every carrier, so the new
    // legs stay silent -- while the old E247 hint still flags the read.
    let quelle = format!(
        "{KOPF}\
        impl fn schreibt() effects {{ writes G.slots }} costs <= 64 ops \
        {{ G.slots[0].v = 1; }}\n\
        impl fn lies() -> u32 effects {{ reads G.slots }} costs <= 64 ops \
        {{ return G.slots[0].v; }}\n\
        }}\n"
    );
    let codes = fehler(&quelle);
    assert!(
        !codes.iter().any(|c| c == "N290" || c == "N291" || c == "N292" || c == "N293"),
        "single-threaded readers stay silent under the new rule: {codes:?}"
    );
    let hints = hinweise(&quelle);
    assert!(
        hints.iter().any(|c| c == "E247"),
        "the old strictness still flags the same read as a hint: {hints:?}"
    );
}

#[test]
fn gemeinsame_lesung_ohne_wache_faellt_n291() {
    // Two threads share `G`; `leser` reads it bare. No signature guard, no
    // invariant, not thread-local -- N291.
    let quelle = format!(
        "{KOPF}\
        impl fn schreiber() effects {{ writes G.slots }} costs <= 64 ops \
        {{ G.slots[0].v = 1; }}\n\
        impl fn leser() -> u32 effects {{ reads G.slots }} costs <= 64 ops \
        {{ return G.slots[0].v; }}\n\
        concurrent {{ schreiber, leser }};\n\
        }}\n"
    );
    let codes = fehler(&quelle);
    assert!(
        codes.iter().any(|c| c == "N291"),
        "a bare shared read must flag N291: {codes:?}"
    );
}

#[test]
fn lesung_unter_umschliessender_sperre_schweigt() {
    // The probe-C shape: the read sits inside `locks L`, guarded at the access.
    // The old E247 hint fires; N291 stays silent.
    let quelle = format!(
        "{KOPF}\
        lock L protects {{ G }} rank 0 held <= 64 ops;\n\
        impl fn schreiber() effects {{ writes G.slots, locks L }} costs <= 64 ops \
        {{ locks L {{ G.slots[0].v = 1; }} }}\n\
        impl fn leser() -> u32 effects {{ reads G.slots, locks L }} costs <= 64 ops \
        {{ locks L {{ return G.slots[0].v; }} }}\n\
        concurrent {{ schreiber, leser }};\n\
        }}\n"
    );
    let codes = fehler(&quelle);
    assert!(
        !codes.iter().any(|c| c == "N291"),
        "a read guarded at the access stays silent: {codes:?}"
    );
}

#[test]
fn vertrag_ueber_gemeinsamem_traeger_faellt_n290() {
    let quelle = format!(
        "{KOPF}\
        impl fn geber() -> u32\n\
            requires G.slots[0].v == 0\n\
            effects {{ reads G.slots }}\n\
            costs <= 64 ops\n\
        {{\n\
            return 0;\n\
        }}\n\
        impl fn schreiber() effects {{ writes G.slots }} costs <= 64 ops \
        {{ G.slots[0].v = 1; }}\n\
        concurrent {{ geber, schreiber }};\n\
        }}\n"
    );
    let codes = fehler(&quelle);
    assert!(
        codes.iter().any(|c| c == "N290"),
        "an unguarded shared contract must flag N290: {codes:?}"
    );
}

#[test]
fn ruf_ueber_fremden_vertrag_faellt_n292() {
    // `aufrufer` (thread C) calls `geber` (thread A) whose contract reads `G`,
    // written on thread B: outside every admission -- N292.
    let quelle = format!(
        "{KOPF}\
        impl fn aufrufer() -> u32 effects {{ reads G.slots }} costs <= 128 ops \
        {{ let x = geber(); return x; }}\n\
        impl fn geber() -> u32\n\
            requires G.slots[0].v == 0\n\
            effects {{ reads G.slots }}\n\
            costs <= 64 ops\n\
        {{\n\
            return G.slots[0].v;\n\
        }}\n\
        impl fn schreiber() effects {{ writes G.slots }} costs <= 64 ops \
        {{ G.slots[0].v = 1; }}\n\
        concurrent {{ aufrufer, geber, schreiber }};\n\
        }}\n"
    );
    let codes = fehler(&quelle);
    assert!(
        codes.iter().any(|c| c == "N292"),
        "a call into a shared contract must flag N292: {codes:?}"
    );
}

#[test]
fn signaturwache_schweigt_weiter() {
    // The guarded shape stays silent under both rules.
    let quelle = format!(
        "{KOPF}\
        lock L protects {{ G }} rank 0 held <= 64 ops;\n\
        impl fn geber() -> u32\n\
            requires Held(L), G.slots[0].v == 0\n\
            effects {{ reads G.slots }}\n\
            costs <= 64 ops\n\
        {{\n\
            return G.slots[0].v;\n\
        }}\n\
        impl fn schreiber() effects {{ writes G.slots, locks L }} costs <= 64 ops \
        {{ locks L {{ G.slots[0].v = 1; }} }}\n\
        concurrent {{ geber, schreiber }};\n\
        }}\n"
    );
    let codes = fehler(&quelle);
    assert!(
        !codes.iter().any(|c| c.starts_with('N')),
        "the signature-guarded shape stays silent: {codes:?}"
    );
}

#[test]
fn nehmung_unter_signaturwache_faellt_n294() {
    // `haltend` holds `HOCH` (rank 5) by signature and takes `TIEF` (rank 1):
    // a floor violation both rank rules cannot see.
    let quelle = "module test::fusswache2 {\n\
        static mut z : u32 = 0;\n\
        static mut w : u32 = 0;\n\
        lock HOCH protects { z } rank 5 held <= 8 ops;\n\
        lock TIEF protects { w } rank 1 held <= 8 ops;\n\
        impl fn haltend()\n\
            requires Held(HOCH)\n\
            effects { writes w, locks TIEF }\n\
            costs <= 64 ops\n\
        {\n\
            locks TIEF {\n\
                w = 1;\n\
            }\n\
        }\n\
        }\n";
    let codes = fehler(quelle);
    assert!(
        codes.iter().any(|c| c == "N294"),
        "a take below a signature-held lock must flag N294: {codes:?}"
    );
    assert!(
        !codes.iter().any(|c| c == "H006" || c == "H012"),
        "the rank rules stay silent where the floor leg fires: {codes:?}"
    );
}

#[test]
fn ruf_unter_signaturwache_ueber_nehmende_huelle_faellt_n294() {
    // Same floor through a call: `rufend` holds `HOCH`, `nehmend` takes `TIEF`.
    let quelle = "module test::fusswache2 {\n\
        static mut z : u32 = 0;\n\
        static mut w : u32 = 0;\n\
        lock HOCH protects { z } rank 5 held <= 8 ops;\n\
        lock TIEF protects { w } rank 1 held <= 8 ops;\n\
        impl fn nehmend() effects { writes w, locks TIEF } costs <= 64 ops \
        { locks TIEF { w = 2; } }\n\
        impl fn rufend()\n\
            requires Held(HOCH)\n\
            effects { writes w, locks TIEF }\n\
            costs <= 64 ops\n\
        {\n\
            nehmend();\n\
        }\n\
        }\n";
    let codes = fehler(quelle);
    assert!(
        codes.iter().any(|c| c == "N294"),
        "a call taking below a signature-held lock must flag N294: {codes:?}"
    );
}
