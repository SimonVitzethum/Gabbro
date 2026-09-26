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
fn signaturwache_still_fuer_fuss_n303_fuer_wurzel() {
    // The guarded shape keeps the FOOTPRINT legs silent -- but since lane 183
    // (`wurzelnB`) a start holding a signature lock falls with N303: the
    // signature-guard admission and the start discipline part ways here.
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
        !codes
            .iter()
            .any(|c| c == "N290" || c == "N291" || c == "N292" || c == "N293" || c == "N294"),
        "the signature-guarded shape keeps the footprint legs silent: {codes:?}"
    );
    assert!(
        codes.iter().any(|c| c == "N303"),
        "a start holding a signature lock falls with N303: {codes:?}"
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

// --- Lane 183: the race component (`N300`/`N301`) with `wurzelnB` beside it ---

#[test]
fn zwei_schreiber_ohne_leser_fallen_n300() {
    // Two starts write `G`, no footprint anywhere reads it: the footprint legs
    // stay silent (footprints list reads), the race leg falls.
    let quelle = format!(
        "{KOPF}\
        impl fn schreiber_a() effects {{ writes G.slots }} costs <= 64 ops \
        {{ G.slots[0].v = 1; }}\n\
        impl fn schreiber_b() effects {{ writes G.slots }} costs <= 64 ops \
        {{ G.slots[1].v = 2; }}\n\
        concurrent {{ schreiber_a, schreiber_b }};\n\
        }}\n"
    );
    let codes = fehler(&quelle);
    assert!(
        codes.iter().any(|c| c == "N300"),
        "two writers with no reader must flag N300: {codes:?}"
    );
    assert!(
        !codes.iter().any(|c| c == "N301"),
        "a pair that writes on both sides belongs to N300 alone: {codes:?}"
    );
    assert!(
        !codes.iter().any(|c| c == "N290" || c == "N291" || c == "N292" || c == "N293"),
        "no footprint reads, so the footprint legs stay silent: {codes:?}"
    );
}

#[test]
fn schreiber_leser_fallen_n301() {
    // One start writes `G`, the other's footprint reads it: write-read.
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
        codes.iter().any(|c| c == "N301"),
        "a write-read pair across starts must flag N301: {codes:?}"
    );
    assert!(
        !codes.iter().any(|c| c == "N300"),
        "one-sided writing is not write-write: {codes:?}"
    );
}

#[test]
fn eigene_tabellen_schweigen_n300_n301() {
    // The positive twin: two starts writing their OWN tables stay silent.
    let quelle = format!(
        "{KOPF}\
        impl fn schreiber_a() effects {{ writes G.slots }} costs <= 64 ops \
        {{ G.slots[0].v = 1; }}\n\
        impl fn schreiber_b() effects {{ writes P.slots }} costs <= 64 ops \
        {{ P.slots[0].v = 2; }}\n\
        concurrent {{ schreiber_a, schreiber_b }};\n\
        }}\n"
    );
    let codes = fehler(&quelle);
    assert!(
        !codes
            .iter()
            .any(|c| c == "N300" || c == "N301" || c == "N302" || c == "N303" || c == "N304"),
        "private tables per start stay silent: {codes:?}"
    );
}

#[test]
fn bewachte_schreiber_schweigen_n300() {
    // The guarded shape: both starts write `G` under the guarding lock, taken
    // inside (the `109` discipline -- no signature lock, so N303 stays silent
    // too).
    let quelle = format!(
        "{KOPF}\
        lock L protects {{ G }} rank 0 held <= 64 ops;\n\
        impl fn schreiber_a() effects {{ writes G.slots, locks L }} costs <= 64 ops \
        {{ locks L {{ G.slots[0].v = 1; }} }}\n\
        impl fn schreiber_b() effects {{ writes G.slots, locks L }} costs <= 64 ops \
        {{ locks L {{ G.slots[1].v = 2; }} }}\n\
        concurrent {{ schreiber_a, schreiber_b }};\n\
        }}\n"
    );
    let codes = fehler(&quelle);
    assert!(
        !codes
            .iter()
            .any(|c| c == "N300" || c == "N301" || c == "N302" || c == "N303" || c == "N304"),
        "guarded writers stay silent: {codes:?}"
    );
}

#[test]
fn einziger_start_schweigt_n300() {
    // No declared start: the single driver thread owns every carrier.
    let quelle = format!(
        "{KOPF}\
        impl fn schreibt() effects {{ writes G.slots }} costs <= 64 ops \
        {{ G.slots[0].v = 1; }}\n\
        }}\n"
    );
    let codes = fehler(&quelle);
    assert!(
        !codes
            .iter()
            .any(|c| c == "N300" || c == "N301" || c == "N304"),
        "a single thread owns every carrier: {codes:?}"
    );
}

#[test]
fn start_mit_grund_faellt_n302() {
    // A start routine declaring `or E`: the reason has no caller behind the start.
    let quelle = format!(
        "{KOPF}\
        reason E {{\n\
            Leer = 1 \"the slot held nothing to take\"\n\
            exhaustive\n\
        }}\n\
        impl fn geber() -> u32 or E\n\
            effects {{ reads G.slots }}\n\
            costs <= 64 ops\n\
        {{\n\
            if G.slots[0].v == 0 {{\n\
                return E::Leer;\n\
            }}\n\
            return G.slots[0].v;\n\
        }}\n\
        impl fn nehmer() -> u32\n\
            effects {{ writes P.slots }}\n\
            costs <= 500 ops\n\
        {{\n\
            let n = geber() else (e) {{\n\
                match e {{\n\
                    Leer => {{ P.slots[0].v = 0; return 0; }}\n\
                }}\n\
            }}\n\
            P.slots[0].v = n;\n\
            return n;\n\
        }}\n\
        concurrent {{ geber, nehmer }};\n\
        }}\n"
    );
    let codes = fehler(&quelle);
    assert!(
        codes.iter().any(|c| c == "N302"),
        "a start declaring a reason must flag N302: {codes:?}"
    );
    assert!(
        !codes
            .iter()
            .any(|c| c == "N300" || c == "N301" || c == "N303" || c == "N304"),
        "each start owns its carrier -- only the reason refusal fires: {codes:?}"
    );
}

#[test]
fn start_mit_signaturwache_faellt_n303() {
    // A start routine holding a lock by signature: the strong form of N240.
    // `M` stands in one held set alone, so N240 stays silent beside it.
    let quelle = format!(
        "{KOPF}\
        table U count 2 {{\n\
            slot {{\n\
                v : u32,\n\
            }}\n\
        }}\n\
        lock L protects {{ G }} rank 0 held <= 64 ops;\n\
        lock M protects {{ U }} rank 1 held <= 64 ops;\n\
        impl fn leser_a() -> u32\n\
            requires Held(L)\n\
            effects {{ reads G.slots }}\n\
            costs <= 4 ops\n\
        {{\n\
            return G.slots[0].v;\n\
        }}\n\
        impl fn leser_b() -> u32\n\
            effects {{ reads U.slots }}\n\
            costs <= 4 ops\n\
        {{\n\
            return U.slots[1].v;\n\
        }}\n\
        concurrent {{ leser_a, leser_b }};\n\
        }}\n"
    );
    let codes = fehler(&quelle);
    assert!(
        codes.iter().any(|c| c == "N303"),
        "a start holding a signature lock must flag N303: {codes:?}"
    );
    assert!(
        !codes.iter().any(|c| c == "N240"),
        "disjoint held sets keep N240 silent -- N303 is the strong form: {codes:?}"
    );
    assert!(
        !codes.iter().any(|c| c == "N300" || c == "N301"),
        "guarded carriers keep the race legs silent: {codes:?}"
    );
}

#[test]
fn doppelter_schreibender_start_faellt_n304() {
    // One writing routine behind two entries: not idle, so `einmal` refuses.
    let quelle = "module test::fusswache2 {\n\
        table G count 2 {\n\
            slot {\n\
                v : u32,\n\
            }\n\
        }\n\
        impl fn schreibt() effects { writes G.slots } costs <= 64 ops \
        { G.slots[0].v = 1; }\n\
        entry entry_a vector 0x80 arch x86_64 {\n    regs in { } regs out { } \
        preserves { rbx } clobbers { rcx } stack ka per cpu nested never \
        dispatch test::fusswache2::schreibt;\n}\n\
        entry entry_b vector 0x81 arch x86_64 {\n    regs in { } regs out { } \
        preserves { rbx } clobbers { rcx } stack kb per cpu nested never \
        dispatch test::fusswache2::schreibt;\n}\n\
        }\n";
    let codes = fehler(quelle);
    assert!(
        codes.iter().any(|c| c == "N304"),
        "a writing routine on two threads must flag N304: {codes:?}"
    );
    assert!(
        !codes.iter().any(|c| c == "N315"),
        "the busy shape belongs to N304 alone: {codes:?}"
    );
}

#[test]
fn doppelter_ruhiger_start_bleibt_still() {
    // Fix lane F10 retired `N315`: an idle routine on two entries is the empty
    // pool -- it writes nothing, so it is pool-safe (`EinzelnPool`), the goal Bool
    // admits it and `gabbro_ziel` covers it. Lane 196 refused it only because the
    // goal Bool demanded `ws.Nodup`. No race or start refusal fires.
    let quelle = "module test::fusswache2 {\n\
        impl fn idle() -> u32 effects { pure } costs <= 1 ops { return 0; }\n\
        entry entry_a vector 0x80 arch x86_64 {\n    regs in { } regs out { } \
        preserves { rbx } clobbers { rcx } stack ka per cpu nested never \
        dispatch test::fusswache2::idle;\n}\n\
        entry entry_b vector 0x81 arch x86_64 {\n    regs in { } regs out { } \
        preserves { rbx } clobbers { rcx } stack kb per cpu nested never \
        dispatch test::fusswache2::idle;\n}\n\
        }\n";
    let codes = fehler(quelle);
    assert!(
        !codes.iter().any(|c| c == "N300"
            || c == "N301"
            || c == "N302"
            || c == "N303"
            || c == "N304"
            || c == "N315"),
        "an idle routine on two entries is an admitted pool: {codes:?}"
    );
}

#[test]
fn pool_fussabdruck_paart_vorkommen() {
    // Fix lane F10: the footprint legs pair thread OCCURRENCES (`Getrennt` with
    // `Mehrfach`). A pool routine that reads a carrier in its contract and writes
    // it -- guarded by a lock WITHOUT an invariant, read bare in the `requires` of
    // the start itself -- is not thread-local any more: the other instance writes
    // it. `N304` stays silent (the write is guarded); the footprint leg refuses.
    let quelle = "module test::fusswache2 {\n\
        table K count 2 {\n\
            slot {\n\
                v : u32,\n\
            }\n\
        }\n\
        lock L protects { K } rank 0 held <= 100 ops;\n\
        impl fn arbeiter()\n\
            requires K.slots[0].v == 0\n\
            effects { reads K.slots, writes K.slots, locks L }\n\
            costs <= 64 ops\n\
        {\n\
            locks L { K.slots[0].v = 1; }\n\
        }\n\
        concurrent { arbeiter, arbeiter };\n\
        }\n";
    let codes = fehler(quelle);
    assert!(
        !codes.iter().any(|c| c == "N304"),
        "guarded writes only: the pool shape itself is admitted: {codes:?}"
    );
    assert!(
        codes.iter().any(|c| c == "N290"),
        "the contract read of a carrier the other instance writes is no longer \
         thread-local: {codes:?}"
    );
    // The single start: the same routine once is thread-local and silent there.
    let einmal = quelle.replace("concurrent { arbeiter, arbeiter };", "concurrent { arbeiter };");
    let codes = fehler(&einmal);
    assert!(
        !codes.iter().any(|c| c == "N290" || c == "N304"),
        "one occurrence owns its carrier: {codes:?}"
    );
}

#[test]
fn nutzlast_zwillinge_fallen_n300() {
    // Lane 196 (verdict P3): two starts writing one unguarded payload are a
    // C11 race on a non-atomic object -- the payload exemption is gone, and
    // `N300` fires beside `W001`.
    let quelle = "module test::fusswache2 {\n\
        static mut bericht : u64 = 0;\n\
        atomic BEREIT : bool release;\n\
        impl fn melde_a(w : u64) effects { writes bericht, publishes BEREIT } costs <= 8 ops \
        { bericht = w; BEREIT = true publishes { bericht }; }\n\
        impl fn melde_b(w : u64) effects { writes bericht, publishes BEREIT } costs <= 8 ops \
        { bericht = w; BEREIT = true publishes { bericht }; }\n\
        concurrent { melde_a, melde_b };\n\
        }\n";
    let codes = fehler(&quelle);
    assert!(
        codes.iter().any(|c| c == "N300"),
        "a payload written by two starts must flag N300: {codes:?}"
    );
    assert!(
        !codes.iter().any(|c| c == "N301"),
        "a pair that writes on both sides belongs to N300 alone: {codes:?}"
    );
}

#[test]
fn pool_sauberer_arbeiter_bleibt_still() {
    // Lane 245 (symmetric worker pool): one routine on two threads whose
    // every written carrier is guarded. `arbeiter` writes `K` only under
    // `L`, holds nothing by signature, declares no reason -- pool-safe, so
    // `N304` stays silent, and so do `N300`/`N301` (no unguarded writer
    // anywhere). Since fix lane F10 the goal Bool admits it too (`EinzelnPool`).
    let quelle = "module test::fusswache2 {\n\
        type Stand = u32 in 0 .. 100;\n\
        table K count 2 {\n\
            slot {\n\
                stand : Stand,\n\
            }\n\
        }\n\
        lock L protects { K } rank 0 held <= 100 ops\n\
            invariant K.slots[0].stand == K.slots[1].stand;\n\
        impl fn setze(x : Stand)\n\
            requires Held(L), K.slots[0].stand == K.slots[1].stand\n\
            ensures K.slots[0].stand == K.slots[1].stand && K.slots[0].stand == x\n\
            effects { reads K.slots, writes K.slots, locks L }\n\
            costs <= 64 ops\n\
        {\n\
            K.slots[0].stand = x;\n\
            K.slots[1].stand = x;\n\
        }\n\
        impl fn arbeiter()\n\
            effects { reads K.slots, writes K.slots, locks L }\n\
            costs <= 512 ops\n\
        {\n\
            locks L {\n\
                setze(30);\n\
            }\n\
        }\n\
        concurrent { arbeiter, arbeiter };\n\
        }\n";
    let codes = fehler(quelle);
    assert!(
        !codes.iter().any(|c| c == "N300"
            || c == "N301"
            || c == "N302"
            || c == "N303"
            || c == "N304"
            || c == "N315"),
        "a pool-safe routine on two threads draws no race refusal: {codes:?}"
    );
}

#[test]
fn pool_reine_leser_bleiben_still() {
    // Lane 245: one routine on two threads that only reads. No writer
    // anywhere, so no race shape exists -- `N304` stays silent (pool-safe
    // with empty writes) and `N300`/`N301` have no writer to name.
    let quelle = "module test::fusswache2 {\n\
        table G count 2 {\n\
            slot {\n\
                v : u32,\n\
            }\n\
        }\n\
        impl fn leser() -> u32 effects { reads G.slots } costs <= 64 ops \
        { return G.slots[0].v; }\n\
        concurrent { leser, leser };\n\
        }\n";
    let codes = fehler(quelle);
    assert!(
        !codes.iter().any(|c| c == "N300"
            || c == "N301"
            || c == "N302"
            || c == "N303"
            || c == "N304"
            || c == "N315"),
        "a read-only routine on two threads draws no race refusal: {codes:?}"
    );
}

#[test]
fn pro_kern_zwillinge_schweigen_n300() {
    // Two starts writing one per-core cell: one name, N distinct carriers.
    let quelle = "module test::fusswache2 {\n\
        const NKERNE : u32 = 64;\n\
        accumulates zaehler : u32 merge add per cpu NKERNE;\n\
        impl fn ha() effects { writes zaehler } costs <= 8 ops { zaehler = 1; }\n\
        impl fn hb() effects { writes zaehler } costs <= 8 ops { zaehler = 2; }\n\
        concurrent { ha, hb };\n\
        }\n";
    let codes = fehler(&quelle);
    assert!(
        !codes.iter().any(|c| c == "N300" || c == "N301"),
        "a per-core cell stays silent: {codes:?}"
    );
}

// ===== N484 -- a contract over a shared atomic (Opus lane O25b, 2026-09-26) =====

/// Three starts over the atomic `FLAGGE`: `setzer` stores 1 and promises `FLAGGE == 1`,
/// `loescher` stores 0, `leser` reads it -- the shape of gift 1204.
const VERTRAG_ATOMAR: &str = "module test::fusswache2 {\n\
    atomic FLAGGE : u32 acquire;\n\
    pub static mut kopie : u32 = 0;\n\
    impl fn setzer() ensures FLAGGE == 1 effects { writes FLAGGE } costs <= 8 ops \
    { FLAGGE = 1 publishes nothing; }\n\
    impl fn loescher() effects { writes FLAGGE } costs <= 8 ops \
    { FLAGGE = 0 publishes nothing; }\n\
    impl fn leser() effects { reads FLAGGE, writes kopie } costs <= 8 ops \
    { let f : u32 = FLAGGE; kopie = f; }\n\
    concurrent { setzer, loescher, leser };\n\
    }\n";

#[test]
fn vertrag_ueber_geteiltem_atomic_faellt_mit_n484() {
    let codes = fehler(VERTRAG_ATOMAR);
    assert!(codes.iter().any(|c| c == "N484"), "N484 expected, fired: {codes:?}");
}

#[test]
fn geteiltes_atomic_im_rumpf_schweigt_n484() {
    // The same three starts, the contract dropped: the shared atomic is read in bodies only
    // (the flag of OFFEN O25) -- the leg stays silent.
    let codes = fehler(&VERTRAG_ATOMAR.replace("ensures FLAGGE == 1 ", ""));
    assert!(!codes.iter().any(|c| c == "N484"), "N484 must stay silent: {codes:?}");
}

#[test]
fn vertrag_ueber_faden_lokalem_atomic_schweigt_n484() {
    // Only `setzer` touches `FLAGGE`; `leser` reads `kopie` alone: the atomic is thread-local,
    // and a contract over it is an ordinary sequential claim.
    let quelle = "module test::fusswache2 {\n\
        atomic FLAGGE : u32 acquire;\n\
        pub static mut kopie : u32 = 0;\n\
        impl fn setzer() ensures FLAGGE == 1 effects { writes FLAGGE } costs <= 8 ops \
        { FLAGGE = 1 publishes nothing; }\n\
        impl fn leser() -> u32 effects { reads kopie } costs <= 8 ops { return kopie; }\n\
        concurrent { setzer, leser };\n\
        }\n";
    let codes = fehler(quelle);
    assert!(!codes.iter().any(|c| c == "N484"), "N484 must stay silent: {codes:?}");
}

#[test]
fn einzelner_faden_schweigt_n484() {
    // No `concurrent`: one driver thread owns every atomic.
    let codes = fehler(&VERTRAG_ATOMAR.replace("concurrent { setzer, loescher, leser };\n", ""));
    assert!(!codes.iter().any(|c| c == "N484"), "N484 must stay silent: {codes:?}");
}
