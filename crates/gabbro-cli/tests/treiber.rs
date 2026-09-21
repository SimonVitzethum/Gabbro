//! **Per-unit driver generation (lane 246): `gabbro build` writes the
//! hosted driver beside the emitted C.**
//!
//! The emitter translates each `concurrent` member to a plain function and
//! emits no caller and no `main`; the build writes `<unit>.treiber.c` in the
//! exact shape of `laufzeit/start.c` (one wrapper per root, one thread per
//! root, join all, idle root present, lock primitives as mutex). What is
//! held here:
//!
//! * the hand driver `laufzeit/start.c` still holds its pin (the probe lane
//!   202 described -- source set against `pthread_create` set);
//! * the GENERATED driver holds the same pin, over the same sources;
//! * a stale driver (a root added or dropped without regenerating) fails the
//!   pin loudly, naming both sets;
//! * `beispiele/124` runs through the GENERATED driver with the identical
//!   observable behaviour as through the hand file (same line shape, same
//!   predicate the hand `main` asserts -- the shared value itself is
//!   schedule-dependent, 30 or 70, as lane 202 measured over 200 runs).

use std::collections::BTreeMap;
use std::path::PathBuf;
use std::process::Command;

fn wurzel() -> PathBuf {
    PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/../.."))
}

fn gabbro(argumente: &[&str]) -> (String, String, i32) {
    let aus = Command::new(env!("CARGO_BIN_EXE_gabbro"))
        .args(argumente)
        .current_dir(wurzel())
        .output()
        .expect("gabbro runs");
    (
        String::from_utf8_lossy(&aus.stdout).into_owned(),
        String::from_utf8_lossy(&aus.stderr).into_owned(),
        aus.status.code().unwrap_or(-1),
    )
}

fn tmp(test: &str) -> PathBuf {
    let p = std::env::temp_dir().join(format!(
        "gabbro-treiber-246-{}-{test}",
        std::process::id()
    ));
    std::fs::create_dir_all(&p).expect("scratch dir writable");
    p
}

/// The declared roots of one source file, by short C name, COUNTED per
/// occurrence (fix lane F4: `concurrent { f, f }` is two starts) -- through
/// the REAL parser, not a text scan: the probe reads declarations, so it
/// reads what the checker read.
fn concurrent_kurz(datei: &str, quelle: &str) -> BTreeMap<String, usize> {
    use gabbro_syntax::ast::ItemArt;
    let (baum, _) = gabbro_syntax::lies(datei, quelle);
    fn sammle(items: &[gabbro_syntax::ast::Item], menge: &mut BTreeMap<String, usize>) {
        for i in items {
            match &i.art {
                ItemArt::Modul(m) => sammle(&m.items, menge),
                ItemArt::Concurrent(c) => {
                    for p in &c.koerper {
                        if let Some(letztes) = p.teile.last() {
                            *menge.entry(letztes.text.clone()).or_insert(0) += 1;
                        }
                    }
                }
                _ => {}
            }
        }
    }
    let mut menge = BTreeMap::new();
    sammle(&baum.items, &mut menge);
    menge
}

/// The `pthread_create` roots of a driver C file, COUNTED: every
/// `faden_<root>` named at a `pthread_create` call site, once per site. A
/// plain scanner is enough -- the generator is the only writer of the
/// generated file, and the hand file keeps the same one-wrapper-per-root
/// shape so the same probe reads both.
fn pthread_create_menge(treiber_c: &str) -> BTreeMap<String, usize> {
    let mut menge = BTreeMap::new();
    let mut rest = treiber_c;
    // Only CALL SITES count (`pthread_create(` up to its `;`): with counts a
    // mention in a comment would be a thread start that does not exist.
    while let Some(i) = rest.find("pthread_create(") {
        let nach = &rest[i + "pthread_create(".len()..];
        let aufruf = &nach[..nach.find(';').unwrap_or(nach.len())];
        if let Some(j) = aufruf.find("faden_") {
            let name: String = aufruf[j + "faden_".len()..]
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
                .collect();
            if !name.is_empty() {
                *menge.entry(name).or_insert(0) += 1;
            }
        }
        rest = nach;
    }
    menge
}

fn n_wurzeln(treiber_c: &str) -> Option<usize> {
    treiber_c.lines().find_map(|zeile| {
        zeile
            .trim()
            .strip_prefix("#define N_WURZELN")
            .and_then(|rest| rest.trim().parse::<usize>().ok())
    })
}

/// The pin lane 202 described, as a MULTISET since fix lane F4: the same
/// roots with the same counts, and `N_WURZELN` counting the starts. The
/// error names both sides -- a stale driver fails LOUDLY.
fn pin_pruefe(quelle: &BTreeMap<String, usize>, treiber_c: &str) -> Result<usize, String> {
    let treiber = pthread_create_menge(treiber_c);
    let zeige = |m: &BTreeMap<String, usize>| -> String {
        m.iter().map(|(n, k)| format!("{n} x{k}")).collect::<Vec<_>>().join(", ")
    };
    if treiber != *quelle {
        return Err(format!(
            "source: [{}], driver: [{}] -- regenerate the driver",
            zeige(quelle),
            zeige(&treiber)
        ));
    }
    let gesamt: usize = quelle.values().sum();
    match n_wurzeln(treiber_c) {
        Some(n) if n == gesamt => Ok(n),
        Some(n) => Err(format!("N_WURZELN is {n} but the sources declare {gesamt}")),
        None => Err("no `#define N_WURZELN <n>` line".to_string()),
    }
}

/// The 124 observation tail: the checks `laufzeit/start.c` runs after the
/// join, byte-equal but for the trailing `return 0;` (the generated file
/// provides that line itself, so the build artefact and the test artefact
/// differ by exactly this block -- verifiable by diff).
const BEOBACHTUNG_124: &str = r#"    unsigned konto0 = konto_speicher.slots[0].stand;
    unsigned konto1 = konto_speicher.slots[1].stand;
    unsigned pa0 = privA_speicher.slots[0].stand;
    unsigned pa1 = privA_speicher.slots[1].stand;
    unsigned pb0 = privB_speicher.slots[0].stand;

    printf("konto=%u konto=%u privA=%u privA=%u privB=%u\n",
        konto0, konto1, pa0, pa1, pb0);

    if (konto0 != konto1) {
        fprintf(stderr, "INVARIANT BROKEN: konto[0]=%u konto[1]=%u\n", konto0, konto1);
        return 1;
    }
    if (pa0 != 7 || pa1 != 7) {
        fprintf(stderr, "LOST WRITE: privA=%u,%u, want 7,7\n", pa0, pa1);
        return 1;
    }
    if (pb0 != 5) {
        fprintf(stderr, "LOST WRITE: privB=%u, want 5\n", pb0);
        return 1;
    }
"#;

/// The predicate the hand `main` asserts: the lock invariant holds and the
/// private slots are exact. The shared VALUE is schedule-dependent (30 or
/// 70) and is asserted only through the invariant -- the same reading lane
/// 202's 200 runs established.
fn behauptung_haelt(zeile: &str) -> bool {
    let teile: Vec<&str> = zeile.split_whitespace().collect();
    if teile.len() != 5 {
        return false;
    }
    let (Some(a), Some(b)) = (
        teile[0].strip_prefix("konto="),
        teile[1].strip_prefix("konto="),
    ) else {
        return false;
    };
    a == b && teile[2] == "privA=7" && teile[3] == "privA=7" && teile[4] == "privB=5"
}

/// **The hand driver's pin still holds.** This is lane 202's mechanical pin,
/// kept green: the `concurrent { ... }` set of 124 against the
/// `pthread_create` set of `laufzeit/start.c`, counted by `N_WURZELN`.
#[test]
fn pin_haelt_fuer_handtreiber_start_c() {
    let quelle = std::fs::read_to_string(wurzel().join("beispiele/124-two-threads-private.gab"))
        .expect("124 readable");
    let treiber = std::fs::read_to_string(wurzel().join("laufzeit/start.c"))
        .expect("start.c readable");
    let menge = concurrent_kurz("124-two-threads-private.gab", &quelle);
    assert_eq!(
        menge.iter().map(|(n, k)| (n.as_str(), *k)).collect::<Vec<_>>(),
        [("hauptA", 1), ("hauptB", 1)],
        "the source declares exactly its two roots, once each"
    );
    assert_eq!(pin_pruefe(&menge, &treiber), Ok(2), "the hand pin holds");
}

fn manifest_schreiben(arbeit: &std::path::Path) -> PathBuf {
    let gab = wurzel().join("beispiele/124-two-threads-private.gab");
    let ausgabe = arbeit.join("treiber124-out");
    let manifest = arbeit.join("treiber124.bau");
    std::fs::write(
        &manifest,
        format!(
            "compiler cc -std=c11 -O0 -Wall -Wextra -Werror -pthread\n\
             out {}\n\
             unit treiber124 object\n\
             \x20   {}\n",
            ausgabe.display(),
            gab.display()
        ),
    )
    .expect("manifest writable");
    manifest
}

/// **The build writes the driver, and the generated pin holds.** The dry
/// run names the plan first (roots, locks, artefact name).
#[test]
fn bau_schreibt_treiber_und_pin_haelt() {
    let arbeit = tmp("bau");
    let manifest = manifest_schreiben(&arbeit);
    let manifest_str = manifest.to_string_lossy().into_owned();

    let (aus, fehler, code) = gabbro(&["build", "--dry-run", &manifest_str]);
    assert_eq!(code, 0, "the plan holds:\n{aus}\n{fehler}");
    assert!(
        aus.contains("driver   treiber124: roots [hauptA, hauptB] locks [L]"),
        "the dry run names the driver plan:\n{aus}"
    );

    let (aus, fehler, code) = gabbro(&["build", &manifest_str]);
    assert_eq!(code, 0, "the unit builds:\n{aus}\n{fehler}");
    assert!(
        aus.contains("treiber124.treiber.c"),
        "the driver travels in the build line:\n{aus}"
    );

    let treiber_c = std::fs::read_to_string(arbeit.join("treiber124-out/treiber124.treiber.c"))
        .expect("the generated driver is on disk");
    let quelle = std::fs::read_to_string(wurzel().join("beispiele/124-two-threads-private.gab"))
        .expect("124 readable");
    let menge = concurrent_kurz("124-two-threads-private.gab", &quelle);
    assert_eq!(pin_pruefe(&menge, &treiber_c), Ok(2), "the generated pin holds");
    // **The runtime half carries no unit checks.** The invariant and the
    // private values are the TEST's business (appended at NACHLAUF); the
    // driver starts threads and defines the mutex, nothing more.
    assert!(!treiber_c.contains("konto"), "no unit observation in the driver");
    assert!(treiber_c.contains("void L_nimm(void)"), "the mutex half is defined");
    assert!(treiber_c.contains("/* NACHLAUF:"), "the test-half marker stands");
}

/// **A stale driver fails loudly, in both directions.** A root dropped or
/// added without regenerating names both sets -- the probe says what
/// changed, not just that something did.
#[test]
fn abgestandener_treiber_faellt_laut() {
    let arbeit = tmp("stale");
    let manifest = manifest_schreiben(&arbeit);
    let manifest_str = manifest.to_string_lossy().into_owned();
    let (_, _, code) = gabbro(&["build", &manifest_str]);
    assert_eq!(code, 0, "the preparing build runs");
    let treiber_c = std::fs::read_to_string(arbeit.join("treiber124-out/treiber124.treiber.c"))
        .expect("the generated driver is on disk");

    let gefallen = pin_pruefe(&BTreeMap::from([("hauptA".to_string(), 1)]), &treiber_c)
        .expect_err("a dropped root fails");
    assert!(
        gefallen.contains("hauptB") && gefallen.contains("hauptA"),
        "both sets are named:\n{gefallen}"
    );
    let gefallen = pin_pruefe(
        &BTreeMap::from([
            ("hauptA".to_string(), 1),
            ("hauptB".to_string(), 1),
            ("hauptC".to_string(), 1),
        ]),
        &treiber_c,
    )
    .expect_err("an added root fails");
    assert!(gefallen.contains("hauptC"), "the added root is named:\n{gefallen}");
}

fn cc_und_lauf(treiber_c_pfad: &std::path::Path, einheits_dir: &std::path::Path, einheit_c: &str, lauf_name: &str) -> (String, i32) {
    let binary = einheits_dir.join(lauf_name);
    // No shell runs here, so the `-D` value carries its C double quotes and
    // no shell single quotes (the documented build line quotes for the
    // shell; `Command` does not need it).
    let cc = Command::new("cc")
        .args([
            "-std=c11",
            "-O0",
            "-Wall",
            "-Wextra",
            "-Werror",
            "-pthread",
            "-I",
            &einheits_dir.to_string_lossy(),
            &format!("-DEINHEIT_INCLUDE=\"{einheit_c}\""),
            "-o",
            &binary.to_string_lossy(),
            &treiber_c_pfad.to_string_lossy(),
        ])
        .output()
        .expect("cc runs");
    assert!(
        cc.status.success(),
        "the driver compiles under -Werror:\n{}",
        String::from_utf8_lossy(&cc.stderr)
    );
    let lauf = Command::new(&binary).output().expect("the program runs");
    (
        String::from_utf8_lossy(&lauf.stdout).into_owned(),
        lauf.status.code().unwrap_or(-1),
    )
}

/// **124 runs through the GENERATED driver with the identical observable
/// behaviour as through the hand file.** The build artefact plus the 124
/// observation at NACHLAUF (differing by exactly that block, verifiable by
/// diff) compiles under the same strict flags and answers the same line
/// shape with the same predicate -- five runs, since the shared value is
/// schedule-dependent.
#[test]
fn lauf_124_durch_erzeugten_treiber() {
    let arbeit = tmp("lauf");
    let manifest = manifest_schreiben(&arbeit);
    let manifest_str = manifest.to_string_lossy().into_owned();
    let (aus, fehler, code) = gabbro(&["build", &manifest_str]);
    assert_eq!(code, 0, "the preparing build runs:\n{aus}\n{fehler}");
    let out = arbeit.join("treiber124-out");
    let erzeugt =
        std::fs::read_to_string(out.join("treiber124.treiber.c")).expect("driver on disk");
    assert!(
        out.join("treiber124.c").exists(),
        "the emitted C stands beside the driver"
    );

    // Build artefact + observation differ by exactly the observation block.
    let marke = "    /* NACHLAUF: unit-specific observation goes here in test runs. */";
    assert_eq!(erzeugt.matches(marke).count(), 1, "the marker stands exactly once");
    let mit_beobachtung = erzeugt.replace(marke, &format!("{marke}\n{BEOBACHTUNG_124}"));
    let ohne = mit_beobachtung.replace(&format!("{marke}\n{BEOBACHTUNG_124}"), marke);
    assert_eq!(ohne, erzeugt, "the two artefacts differ by the observation only");
    let lauf_c = arbeit.join("lauf-gen.c");
    std::fs::write(&lauf_c, &mit_beobachtung).expect("run driver writable");

    for _ in 0..5 {
        let (stdout, code) = cc_und_lauf(&lauf_c, &out, "treiber124.c", "lauf-gen");
        assert_eq!(code, 0, "the generated run exits 0");
        assert!(
            behauptung_haelt(stdout.trim()),
            "invariant holds, privates exact:\n{stdout}"
        );
    }

    // The hand file over the SAME emitted C answers the same shape.
    let (stdout, code) = cc_und_lauf(
        &wurzel().join("laufzeit/start.c"),
        &out,
        "treiber124.c",
        "lauf-hand",
    );
    assert_eq!(code, 0, "the hand run exits 0");
    assert!(
        behauptung_haelt(stdout.trim()),
        "hand and generated runs behave alike:\n{stdout}"
    );
}

/// A pool-safe routine declared twice (lane 245): the checker accepts it, and
/// the build must start it on TWO threads.
const POOL_EINHEIT: &str = r#"module probe::pool {

type Stand = u32 in 0 .. 100;

table konto count 2 {
    slot {
        stand : Stand,
    }
}

lock L protects { konto } rank 0 held <= 100 ops
    invariant konto.slots[0].stand == konto.slots[1].stand;

impl fn setze(x : Stand)
    requires Held(L), konto.slots[0].stand == konto.slots[1].stand
    ensures  konto.slots[0].stand == konto.slots[1].stand && konto.slots[0].stand == x
    effects  { reads konto.slots, writes konto.slots, locks L }
    costs    <= 64 ops
{
    konto.slots[0].stand = x;
    konto.slots[1].stand = x;
}

impl fn arbeiter()
    effects  { reads konto.slots, writes konto.slots, locks L }
    costs    <= 512 ops
{
    locks L {
        setze(30);
    }
}

concurrent { arbeiter, arbeiter };
}
"#;

/// **A pool declared twice runs on two threads** (fix lane F4, review G06 F5).
///
/// Until this lane the build merged repeated `concurrent` names into ONE
/// thread and the set pin passed over it: the runtime ran fewer starts than
/// the checker judged. The generated driver now carries one adapter and two
/// `pthread_create` sites, the multiset pin holds at 2, the driver compiles
/// under `-Werror`, and the run exits 0.
#[test]
fn pool_zweimal_deklariert_laeuft_zweifach() {
    let arbeit = tmp("pool");
    let gab = arbeit.join("pool.gab");
    std::fs::write(&gab, POOL_EINHEIT).expect("unit writable");
    let manifest = arbeit.join("pool.bau");
    let ausgabe = arbeit.join("pool-out");
    std::fs::write(
        &manifest,
        format!(
            "compiler cc -std=c11 -O0 -Wall -Wextra -Werror -pthread\n\
             out {}\n\
             unit pool object\n\
             \x20   {}\n",
            ausgabe.display(),
            gab.display()
        ),
    )
    .expect("manifest writable");
    let (aus, fehler, code) = gabbro(&["build", &manifest.to_string_lossy()]);
    assert_eq!(code, 0, "the pool unit builds:\n{aus}\n{fehler}");
    let treiber_c =
        std::fs::read_to_string(ausgabe.join("pool.treiber.c")).expect("driver on disk");
    let menge = concurrent_kurz("pool.gab", POOL_EINHEIT);
    assert_eq!(menge.get("arbeiter"), Some(&2), "the source declares two starts");
    assert_eq!(pin_pruefe(&menge, &treiber_c), Ok(2), "the multiset pin holds");
    let einmal = BTreeMap::from([("arbeiter".to_string(), 1)]);
    assert!(
        pin_pruefe(&einmal, &treiber_c).is_err(),
        "a one-thread reading of the pool fails the pin"
    );
    let (_, code) = cc_und_lauf(&ausgabe.join("pool.treiber.c"), &ausgabe, "pool.c", "lauf-pool");
    assert_eq!(code, 0, "the pool runs to completion on two threads");
}
