//! **Der LLVM-Erzeuger, in beide Richtungen.**
//!
//! Sauber: eine Handvoll Korpusdateien senkt für BEIDE Ziele ohne Absage (das IR
//! selbst steht hier; dass `clang` es frisst und das Binär läuft, misst
//! `instrumente/baue-llvm.sh` mit echtem Werkzeug — kein `clang` in `cargo test`).
//! Gift: `gift/1427`–`1432` fallen mit genau ihrem `Y`-Code (der Prüfer schweigt
//! dabei — das Programm ist in Ordnung, der ERZEUGER verweigert).

use gabbro_check::gatter::Bau;
use gabbro_check::llvm::{ZIEL_AARCH64, ZIEL_X86_64, ziel_fuer};
use gabbro_syntax::diag::Stufe;
use std::path::{Path, PathBuf};

fn wurzel() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join("beispiele")
}

/// Coverage is an explicit register of actual Lean constructors/fields, never
/// a count of successfully compiled examples. New model members fail closed.
#[test]
fn lean_model_coverage_register_is_complete() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let result = std::process::Command::new("python3")
        .arg(root.join("instrumente/teile/llvm-modelldeckung.py"))
        .current_dir(&root)
        .output()
        .expect("run the model coverage guardian");
    assert!(result.status.success(), "{}\n{}", String::from_utf8_lossy(&result.stdout), String::from_utf8_lossy(&result.stderr));
}

fn senke(
    quelle: &str,
    name: &str,
    ziel: &'static gabbro_check::llvm::Ziel,
) -> (String, Vec<(&'static str, Stufe)>) {
    let (baum, mut absagen) = gabbro_syntax::lies(name, quelle);
    gabbro_check::pruefe(&baum, &mut absagen);
    let pruefer_fehler = absagen.fehler_zahl();
    let ir = gabbro_check::llvm::emittiere_llvm(&baum, &mut absagen, Bau::Auslieferung, ziel);
    let codes = absagen.absagen.iter().map(|a| (a.code, a.stufe)).collect();
    // Der Prüfer zuerst: was er ablehnt, sagt über den Erzeuger nichts.
    assert!(
        pruefer_fehler == 0,
        "{name}: der Prüfer fällt -- keine Aussage über LLVM:\n{}",
        absagen.zeige(quelle)
    );
    (ir, codes)
}

fn fehler(codes: &[(&'static str, Stufe)]) -> Vec<&'static str> {
    codes.iter().filter(|(_, s)| *s == Stufe::Fehler).map(|(c, _)| *c).collect()
}

/// **Die Ziele stehen beim Wort.** Beide Tripletts, beide Layouts, und Unbekanntes
/// ist `None` — der Erzeuger rät kein Ziel.
#[test]
fn ziele_stehen_beim_wort() {
    assert!(ziel_fuer("x86_64").is_some_and(|z| z.triple == ZIEL_X86_64.triple));
    assert!(ziel_fuer("amd64").is_some_and(|z| z.triple == ZIEL_X86_64.triple));
    assert!(ziel_fuer("aarch64").is_some_and(|z| z.triple == ZIEL_AARCH64.triple));
    assert!(ziel_fuer("arm64").is_some_and(|z| z.triple == ZIEL_AARCH64.triple));
    assert!(ziel_fuer("riscv").is_none());
    assert!(ziel_fuer("").is_none());
    assert_ne!(ZIEL_X86_64.datalayout, ZIEL_AARCH64.datalayout);
}

/// **Der Kopf trägt Ziel und Ehrlichkeit.** Triplett, Layout und der Kandidat-Vermerk
/// stehen in jeder Datei, auf beiden Zielen.
#[test]
fn kopf_traegt_ziel_und_ehrlichkeit() {
    let quelle = std::fs::read_to_string(wurzel().join("63-druckt.gab")).expect("63 lesbar");
    for ziel in [&ZIEL_X86_64, &ZIEL_AARCH64] {
        let (ir, codes) = senke(&quelle, "63-druckt.gab", ziel);
        assert!(fehler(&codes).is_empty(), "63 fällt mit {codes:?}");
        assert!(ir.contains(&format!("target triple = \"{}\"", ziel.triple)), "kein Triplett");
        assert!(
            ir.contains(&format!("target datalayout = \"{}\"", ziel.datalayout)),
            "kein Layout"
        );
        assert!(ir.contains("CANDIDATE"), "kein Kandidat-Vermerk");
    }
}

/// **Hallo sagt Hallo (als IR).** `main` definiert, `putchar` deklariert und sechsmal
/// gerufen — die Form, die `baue-llvm.sh` danach übersetzt und ausführt.
#[test]
fn hallo_als_ir() {
    let quelle = std::fs::read_to_string(wurzel().join("63-druckt.gab")).expect("63 lesbar");
    let (ir, _) = senke(&quelle, "63-druckt.gab", &ZIEL_X86_64);
    assert!(ir.contains("define i32 @\"main\"()"), "kein main:\n{ir}");
    assert!(ir.contains("declare i32 @\"putchar\"(i32 noundef)"), "kein putchar:\n{ir}");
    assert_eq!(ir.matches("call i32 @\"putchar\"").count(), 6, "keine sechs Rufe:\n{ir}");
}

/// **Repräsentative Saubere senken auf beiden Zielen.** Traverse mit Tabelle (19),
/// Verbund-Literal (21), Zeiger-Bytes (168), Bereichsbindung (171) und der abgeleitete
/// Vertrag (130) — je ohne eine Absage. (`08` steht hier mit Absicht NICHT: es trägt
/// `tagged`-Typen und fällt mit `Y101` — das misst `gift/1427`.)
#[test]
fn saubere_senken_auf_beiden_zielen() {
    for datei in [
        "19-traversierung.gab",
        "21-verbundwert.gab",
        "168-bytes-through-a-pointer.gab",
        "171-narrow-nach-eigener-deklaration.gab",
        "130-derived-contract-pure.gab",
    ] {
        let quelle = std::fs::read_to_string(wurzel().join(datei)).expect("{datei} lesbar");
        for ziel in [&ZIEL_X86_64, &ZIEL_AARCH64] {
            let (_, codes) = senke(&quelle, datei, ziel);
            let f = fehler(&codes);
            assert!(f.is_empty(), "{datei} auf {} fällt mit {f:?}", ziel.name);
        }
    }
}

/// **Verweigerungen sind zielunabhängig.** Kein `Y`-Satz nennt ein Zielwort, also fällt
/// jede Giftdatei auf beiden Zielen mit demselben Code.
#[test]
fn verweigerung_ist_zielunabhaengig() {
    for (datei, code) in [
        ("1427-opaque-ohne-llvm.gab", "Y101"),
        ("1428-sperre-ohne-llvm.gab", "Y102"),
        ("196-descendants-nur-mit-elter.gab", "Y103"),
        ("1430-aligned-ohne-llvm.gab", "Y104"),
    ] {
        let quelle =
            std::fs::read_to_string(wurzel().join("gift").join(datei)).expect("{datei} lesbar");
        for ziel in [&ZIEL_X86_64, &ZIEL_AARCH64] {
            let (_, codes) = senke(&quelle, datei, ziel);
            let f = fehler(&codes);
            assert_eq!(f, vec![code], "{datei} auf {} fällt mit {f:?}", ziel.name);
        }
    }
}

/// **Was weder ganzzahlig noch Variante ist, fällt als Match.** `1432` (boolescher
/// Gegenstand, checker-sauber) trägt genau `Y106` auf beiden Zielen — der
/// Ganzzahl-`switch` und der Varianten-Versand greifen beide nicht.
#[test]
fn bool_match_faellt_benannt() {
    let quelle =
        std::fs::read_to_string(wurzel().join("gift").join("1432-bool-match-ohne-llvm.gab"))
            .expect("1432 lesbar");
    for ziel in [&ZIEL_X86_64, &ZIEL_AARCH64] {
        let (_, codes) = senke(&quelle, "1432", ziel);
        let f = fehler(&codes);
        assert_eq!(f, vec!["Y106"], "1432 auf {} fällt mit {f:?}", ziel.name);
    }
}

/// Kleines Tor-Programm (beide Architekturen, `via`-frei, kanal-frei): EIN Name,
/// zwei Tore — das Ziel wählt (wie `messung/llvm/summe.gab`). Die Form, die ohne C
/// auskommt — Gabbro-Registersyntax direkt zur Anweisung.
const TOR_QUELLE: &str = r#"module torprobe {
assume a_schreibe
    "Der Kern schreibt."
    falsifier s_schreibe;
syscall schreibe(fd : u64, puffer : ptr<normal, r> u8, laenge : u64) -> u64
    abi linux arch x86_64 number 1
    regs in { rdi = fd, rsi = puffer, rdx = laenge }
    regs out { rax }
    clobbers { rcx, r11 }
    errors { }
    requires laenge <= lenof(puffer)
    effects { writes ausgabe }
    costs <= 8 ops
    assume a_schreibe falsifier s_schreibe;
syscall schreibe(fd : u64, puffer : ptr<normal, r> u8, laenge : u64) -> u64
    abi linux arch aarch64 number 64
    regs in { x0 = fd, x1 = puffer, x2 = laenge }
    regs out { x0 }
    clobbers { }
    errors { }
    requires laenge <= lenof(puffer)
    effects { writes ausgabe }
    costs <= 8 ops
    assume a_schreibe falsifier s_schreibe;
pub static mut TEXT : [u8; 2] = 0;
pub fn main() -> u64
    effects { reads TEXT, writes TEXT, writes ausgabe, diverges }
    costs <= 200 ops
{
    TEXT[0] = 79;
    TEXT[1] = 10;
    let n = schreibe(1, TEXT, 2);
    return n;
}
}
"#;

/// **Ein Tor ist eine Anweisung.** x86-64 senkt zu `syscall` mit Nummer, Registern
/// und Clobbers; der Eintritt `_start` ruft `main` und reicht an 231 durch.
#[test]
fn tor_ist_eine_anweisung_x86_64() {
    let (ir, codes) = senke(TOR_QUELLE, "torprobe", &ZIEL_X86_64);
    let f = fehler(&codes);
    assert!(f.is_empty(), "Torprobe fällt mit {f:?}");
    assert!(ir.contains("call i64 asm sideeffect \"syscall\""), "kein syscall:\n{ir}");
    assert!(ir.contains("(i64 1, i64 1,"), "keine Nummer/Argumente:\n{ir}");
    assert!(ir.contains("~{rcx},~{r11},~{memory}"), "keine Clobbers:\n{ir}");
    assert!(ir.contains("define void @\"_start\"()"), "kein _start:\n{ir}");
    assert!(ir.contains("(i64 231, i64 %c)"), "kein Austritt 231:\n{ir}");
}

/// **Dasselbe auf AArch64.** `svc #0`, Nummer im `x8`, Ergebnis im `x0`,
/// Austritt 94 — und kein x86-Register im IR.
#[test]
fn tor_ist_eine_anweisung_aarch64() {
    let (ir, codes) = senke(TOR_QUELLE, "torprobe", &ZIEL_AARCH64);
    let f = fehler(&codes);
    assert!(f.is_empty(), "Torprobe fällt mit {f:?}");
    assert!(ir.contains("call i64 asm sideeffect \"svc #0\""), "kein svc:\n{ir}");
    assert!(ir.contains("(i64 64, i64 1,"), "keine Nummer/Argumente:\n{ir}");
    assert!(!ir.contains("{rdi}"), "x86-Register im ARM-IR:\n{ir}");
    assert!(ir.contains("(i64 94, i64 %c)"), "kein Austritt 94:\n{ir}");
}

/// **Falsche Architektur ist benannt.** Ein reines x86-Tor baut für AArch64 nicht —
/// `Y102` nennt die Architektur, statt still das Falsche zu senken.
#[test]
fn tor_falsche_architektur_ist_benannt() {
    // Nur-x86-Quelle: kein Tor passt auf ARM.
    let quelle = r#"module torfalsch {
assume a_s
    "Der Kern schreibt."
    falsifier s_s;
syscall schreibe(fd : u64, puffer : ptr<normal, r> u8, laenge : u64) -> u64
    abi linux arch x86_64 number 1
    regs in { rdi = fd, rsi = puffer, rdx = laenge }
    regs out { rax }
    clobbers { rcx, r11 }
    errors { }
    requires laenge <= lenof(puffer)
    effects { writes ausgabe }
    costs <= 8 ops
    assume a_s falsifier s_s;
pub static mut TEXT : [u8; 2] = 0;
pub fn main() -> u64
    effects { reads TEXT, writes TEXT, writes ausgabe, diverges }
    costs <= 200 ops
{
    TEXT[0] = 79;
    TEXT[1] = 10;
    let n = schreibe(1, TEXT, 2);
    return n;
}
}
"#;
    let (_, codes) = senke(&quelle, "torfalsch", &ZIEL_AARCH64);
    let f = fehler(&codes);
    assert!(f.contains(&"Y102"), "falsche Architektur fällt mit {f:?}");
}

/// **`main -> never` bekommt seinen Eintritt.** Der Ruf kehrt nie zurück — `_start`
/// ruft und trägt `unreachable`, ohne Austritts-Anweisung dahinter.
#[test]
fn never_eintritt_ohne_austritt() {
    let quelle = r#"module nie {
assume a_e
    "Der Kern beendet."
    falsifier s_e;
syscall ende(code : u64) -> never
    abi linux arch x86_64 number 231
    regs in { rdi = code }
    regs out { rax }
    clobbers { rcx, r11 }
    errors { }
    effects { diverges }
    costs <= 8 ops
    assume a_e falsifier s_e;
pub fn main() -> never
    effects { diverges }
    costs <= 32 ops
{
    ende(0);
}
}
"#;
    let (ir, codes) = senke(quelle, "nie", &ZIEL_X86_64);
    let f = fehler(&codes);
    assert!(f.is_empty(), "Nie-Probe fällt mit {f:?}");
    assert!(ir.contains("define void @\"_start\"()"), "kein _start:\n{ir}");
    assert!(ir.contains("call void @\"main\"()"), "kein Eintritt-Ruf:\n{ir}");
    assert!(
        ir.contains("call void asm sideeffect \"syscall\""),
        "kein Tor-Ruf:\n{ir}"
    );
}

/// **Der Beleg gehört zum Lauf (ohne LLVM darin).** `emittiere_llvm_mit_beleg`
/// liefert IR plus Beleg aus einem Senken — kein zweites Register; der Beleg
/// selbst trägt kein IR (Verfeinerung Gabbro→Binary).
#[test]
fn beleg_ohne_llvm() {
    let quelle = std::fs::read_to_string(wurzel().join("63-druckt.gab")).expect("63 lesbar");
    let (baum, mut absagen) = gabbro_syntax::lies("63", &quelle);
    gabbro_check::pruefe(&baum, &mut absagen);
    let (_, beleg) = gabbro_check::llvm::emittiere_llvm_mit_beleg(
        &baum,
        &mut absagen,
        Bau::Auslieferung,
        &ZIEL_X86_64,
    );
    assert!(absagen.fehler_zahl() == 0);
    let lean = beleg.als_lean("63-druckt.gab");
    // Kein LLVM darin (Verfeinerung Gabbro→Binary, nicht über Zwischentext).
    assert!(!lean.contains("define i32"), "IR im Beleg!");
    assert!(!lean.contains("target triple = "), "IR-Rest im Beleg!");
    assert!(lean.contains("x86_64-unknown-linux-gnu"), "Triplett fehlt");
    assert!(lean.contains("def llvmFunktionen"), "Funktionstafel fehlt");
    assert!(lean.contains("art := \"start\""), "Eintritt fehlt");
    assert!(lean.contains("name := \"main\""), "main fehlt");
}

/// **Annahmen reisen mit.** Ein `narrow`-Erfolg steht als Tatsache im Beleg —
/// Eingabe für Optimierer UND Validator (dieselbe Zeile, zwei Leser).
#[test]
fn annahmen_reisen_mit() {
    let quelle =
        std::fs::read_to_string(wurzel().join("171-narrow-nach-eigener-deklaration.gab"))
            .expect("171 lesbar");
    let (baum, mut absagen) = gabbro_syntax::lies("171", &quelle);
    gabbro_check::pruefe(&baum, &mut absagen);
    let (_, beleg) = gabbro_check::llvm::emittiere_llvm_mit_beleg(
        &baum,
        &mut absagen,
        Bau::Auslieferung,
        &ZIEL_X86_64,
    );
    assert!(absagen.fehler_zahl() == 0);
    assert!(!beleg.annahmen.is_empty(), "keine Annahme im Beleg");
    let lean = beleg.als_lean("171");
    assert!(lean.contains("narrow"), "Annahme fehlt im Lean-Text");
    assert!(lean.contains("def llvmAnnahmen"), "Annahmentafel fehlt");
}

/// **Tore stehen mit Nummer und Registern im Beleg.** Der Validator muss die
/// Anweisung nicht aus dem IR-Text parsen — die Bindung steht als Datum da.
#[test]
fn tore_stehen_als_datum_da() {
    let (baum, mut absagen) = gabbro_syntax::lies("torprobe", TOR_QUELLE);
    gabbro_check::pruefe(&baum, &mut absagen);
    let (_, beleg) = gabbro_check::llvm::emittiere_llvm_mit_beleg(
        &baum,
        &mut absagen,
        Bau::Auslieferung,
        &ZIEL_AARCH64,
    );
    assert!(absagen.fehler_zahl() == 0);
    let lean = beleg.als_lean("torprobe");
    assert!(lean.contains("nummer := 64"), "Nummer fehlt:\n{lean}");
    assert!(lean.contains("schablone := \"svc #0\""), "Schablone fehlt");
    assert!(lean.contains("x0=0"), "Registerbindung fehlt");
}

/// **Laufzeit steht im Beleg (generiert, nicht verlinkt).** Arenen, Schlösser und
/// Fäden legt der Erzeuger als Wörter/Regionen an — der Beleg nennt sie beim
/// Namen (der Validator findet sie an `<Name>.basis/.belegt/.bereit`, `<Name>`
/// und `gabbro_faden_N_*`), ohne je IR zu lesen.
#[test]
fn laufzeit_steht_im_beleg() {
    let quelle = r#"module laufzeitbeleg {
pub arena Vorrat capacity 1 .. 2 max 4 of u16;
pub static mut Z : u32 = 0;
pub lock L protects { Z } rank 0 held <= 8 ops;
impl fn arbeiter()
    effects { reads Z, writes Z, locks L }
    costs <= 32 ops
{
    locks L {
        Z = Z +% 1;
    }
}
pub fn main() -> u64
    effects { reads Z, writes Z, locks L, reads Vorrat, writes Vorrat }
    costs <= 1024 ops
{
    let a = alloc Vorrat (7);
    start { arbeiter };
    locks L {
        return Z;
    }
}
}
"#;
    let (baum, mut absagen) = gabbro_syntax::lies("laufzeitbeleg", quelle);
    gabbro_check::pruefe(&baum, &mut absagen);
    assert!(absagen.fehler_zahl() == 0, "Belegquelle fällt");
    let (_, beleg) = gabbro_check::llvm::emittiere_llvm_mit_beleg(
        &baum,
        &mut absagen,
        Bau::Auslieferung,
        &ZIEL_X86_64,
    );
    assert!(absagen.fehler_zahl() == 0);
    let lean = beleg.als_lean("laufzeitbeleg");
    assert!(lean.contains("def llvmArenen"), "Arenentafel fehlt");
    assert!(lean.contains("\"Vorrat\""), "Arena fehlt");
    assert!(lean.contains("def llvmSchloesser"), "Schlosstafel fehlt");
    assert!(lean.contains("\"L\""), "Schloss fehlt");
    assert!(lean.contains("def llvmFaeden"), "Fadentafel fehlt");
    assert!(lean.contains("\"arbeiter\""), "Wurzel fehlt");
    assert!(!lean.contains("define "), "IR im Beleg!");
}

/// **Die Abtastung steht vor dem Commit, nie im Schnellpfad.** Unbegrenzte Arena
/// (`pb frei blw 1048576`, Nutzer-Schwelle 1 MiB): das IR ruft die
/// Zählfrage, vergleicht gegen die Schwelle und läuft darunter in `voll` — auf
/// beiden Zielen, ohne ein Byte BSS (`= global [` steht nirgends).
#[test]
fn abtastung_vor_commit() {
    let quelle = r#"module abtastbeleg {
pub arena Vorrat capacity 0 .. 2 of u64 pb frei blw 1048576;
impl fn frei() -> u64 effects { pure } costs <= 4 ops {
    return 99999999;
}
pub fn main() -> u64
    effects { reads Vorrat, writes Vorrat }
    costs <= 64 ops
{
    let a = alloc Vorrat (7) else { return 1; };
    return Vorrat[a];
}
}
"#;
    for ziel in [&ZIEL_X86_64, &ZIEL_AARCH64] {
        let (ir, codes) = senke(quelle, "abtastbeleg", ziel);
        let f = fehler(&codes);
        assert!(f.is_empty(), "Abtastung auf {} fällt mit {f:?}", ziel.name);
        assert!(ir.contains("@\"frei\"()"), "kein Zählruf auf {}:\n{ir}", ziel.name);
        assert!(ir.contains("1048576"), "keine Schwelle auf {}:\n{ir}", ziel.name);
        assert!(ir.contains("arena_genug"), "kein Weiter-Zweig auf {}:\n{ir}", ziel.name);
        assert!(!ir.contains("= global ["), "BSS-Feld auf {}:\n{ir}", ziel.name);
    }
}

/// **Die Freigabe senkt als intrusive Liste.** `free` schreibt das Glied und
/// rückt den Kopf vor; der nächste `alloc` nimmt von der Liste (kein Commit,
/// keine Abtastung auf dem Pfad) -- auf beiden Zielen, ohne BSS-Feld.
#[test]
fn freigabe_als_liste() {
    let quelle = std::fs::read_to_string(wurzel().join("1161-platz-freigeben.gab"))
        .expect("1161 lesbar");
    for ziel in [&ZIEL_X86_64, &ZIEL_AARCH64] {
        let (ir, codes) = senke(&quelle, "1161-platz-freigeben.gab", ziel);
        let f = fehler(&codes);
        assert!(f.is_empty(), "Freigabe auf {} fällt mit {f:?}", ziel.name);
        assert!(ir.contains("alloc_freiliste"), "kein Listenpfad auf {}:\n{ir}", ziel.name);
        assert!(ir.contains("alloc_fertig"), "kein Fertig-Join auf {}:\n{ir}", ziel.name);
        assert!(!ir.contains("= global ["), "BSS-Feld auf {}:\n{ir}", ziel.name);
    }
}

/// **Fäden sind echt (keine direkten Rufe).** `start` senkt je Wurzel `clone`
/// plus Futex-Join mit globalem Fertig-Wort (`gabbro_faden_N_*`, nie
/// rahmen-relativ) -- auf beiden Zielen, ohne `llvm.assume`-gefaltete
/// Fehlerprüfung (laute Fallen: `ud2`/`brk`).
#[test]
fn faden_sind_echt() {
    let quelle = std::fs::read_to_string(wurzel().join("1162-echte-faeden.gab"))
        .expect("1162 lesbar");
    for ziel in [&ZIEL_X86_64, &ZIEL_AARCH64] {
        let (ir, codes) = senke(&quelle, "1162-echte-faeden.gab", ziel);
        let f = fehler(&codes);
        assert!(f.is_empty(), "Start auf {} fällt mit {f:?}", ziel.name);
        assert!(ir.contains("load atomic i32") && ir.contains(" acquire"), "kein atomarer Join auf {}:\n{ir}", ziel.name);
        assert!(ir.contains("faden_joined"), "kein Join auf {}:\n{ir}", ziel.name);
        assert!(!ir.contains("llvm.assume"), "gefaltete Prüfung auf {}:\n{ir}", ziel.name);
    }
}

/// **The Lean certificate ELABORATES (not only substring checks).** Runs `lean` on
/// the certificates of 63 (entry), the gate probe (gates with number) and the
/// runtime probe; skipped with a clear message when no `lean` is found.
#[test]
fn beleg_elaboriert_mit_lean() {
    let heim = std::env::var("HOME").unwrap_or_default();
    let kandidaten = ["lean".to_string(), format!("{heim}/.elan/bin/lean")];
    let lean = kandidaten.iter().find(|k| {
        std::process::Command::new(k.as_str())
            .arg("--version")
            .env_remove("ELAN_TOOLCHAIN")
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false)
    });
    let Some(lean) = lean else {
        eprintln!("SKIP beleg_elaboriert_mit_lean: no `lean` on PATH or in ~/.elan/bin");
        return;
    };
    let quelle63 = std::fs::read_to_string(wurzel().join("63-druckt.gab")).expect("63 lesbar");
    let faelle: [(&str, &str, &gabbro_check::llvm::Ziel); 3] = [
        ("beleg63", &quelle63, &ZIEL_X86_64),
        ("belegtor", TOR_QUELLE, &ZIEL_AARCH64),
        ("belegtorx", TOR_QUELLE, &ZIEL_X86_64),
    ];
    for (name, text, ziel) in faelle {
        let (baum, mut absagen) = gabbro_syntax::lies(name, text);
        gabbro_check::pruefe(&baum, &mut absagen);
        let (_, beleg) = gabbro_check::llvm::emittiere_llvm_mit_beleg(
            &baum,
            &mut absagen,
            Bau::Auslieferung,
            ziel,
        );
        assert!(absagen.fehler_zahl() == 0);
        let verz = std::env::temp_dir().join(format!("gabbro-beleg-{}-{name}", std::process::id()));
        std::fs::create_dir_all(&verz).unwrap();
        let datei = verz.join(format!("{name}.lean"));
        std::fs::write(&datei, beleg.als_lean(name)).unwrap();
        let aus = std::process::Command::new(lean)
            .arg(&datei)
            .env_remove("ELAN_TOOLCHAIN")
            .output()
            .expect("lean startet");
        let ausgabe = String::from_utf8_lossy(&aus.stdout).to_string()
            + &String::from_utf8_lossy(&aus.stderr);
        let _ = std::fs::remove_dir_all(&verz);
        assert!(aus.status.success(), "lean rejects certificate {name}:\n{ausgabe}");
    }
}

// ---------------------------------------------------------------------------------------
// Concurrency: `publish`/`await` with payload and the shared (reader) lock
// ---------------------------------------------------------------------------------------

fn atom_quelle(ordnung: &str) -> String {
    format!(
        "module atomprobe {{
static mut nutzlast : u64 = 0;
atomic FLAGGE : u32 {ordnung};
impl fn melde(w : u64)
    effects {{ writes nutzlast, publishes FLAGGE }}
    costs   <= 8 ops
{{
    nutzlast = w;
    FLAGGE = 1 publishes {{ nutzlast }};
}}
impl fn lies() -> u64
    effects {{ reads FLAGGE, reads nutzlast }}
    costs   <= 8 ops
{{
    let f = FLAGGE awaits {{ nutzlast }};
    if f == 1 {{
        return nutzlast;
    }}
    return 0;
}}
}}
"
    )
}

/// **`publishes { payload }` is a release store, `awaits { payload }` an acquire load** (the
/// payload writes precede the store in program order, the payload reads follow the load), on
/// both targets, and no `Y103` stands in the way any more.
#[test]
fn publish_mit_nutzlast_ist_release_await_ist_acquire() {
    for ordnung in ["release", "acquire"] {
        let quelle = atom_quelle(ordnung);
        for ziel in [&ZIEL_X86_64, &ZIEL_AARCH64] {
            let (ir, codes) = senke(&quelle, "atomprobe", ziel);
            assert!(fehler(&codes).is_empty(), "{ordnung} auf {}: {codes:?}", ziel.name);
            assert!(ir.contains("store atomic i32 %") && ir.contains(", ptr @\"FLAGGE\" release, align 4"), "kein release:\n{ir}");
            assert!(ir.contains("load atomic i32, ptr @\"FLAGGE\" acquire"), "kein acquire:\n{ir}");
            // The payload store stands BEFORE the flag store in the text of `melde`.
            let melde = ir.split("define void @\"melde\"").nth(1).expect("melde");
            let nutz = melde.find("store i64").expect("Nutzlast-Speicher");
            let flagge = melde.find("store atomic").expect("Flaggen-Speicher");
            assert!(nutz < flagge, "Nutzlast nach der Flagge:\n{melde}");
            // `await` is ONE load, not a loop.
            assert_eq!(ir.matches("load atomic i32, ptr @\"FLAGGE\"").count(), 1, "{ir}");
        }
    }
}

/// A `seq` atomic keeps its strength: never weaker than the declaration. (An atomic with no
/// ordering word and a payload is the checker's `V005`.)
#[test]
fn publish_und_await_halten_seq_cst() {
    for ordnung in ["seq"] {
        let quelle = atom_quelle(ordnung);
        let (ir, codes) = senke(&quelle, "atomprobe", &ZIEL_X86_64);
        assert!(fehler(&codes).is_empty(), "{ordnung}: {codes:?}");
        assert!(ir.contains(", ptr @\"FLAGGE\" seq_cst, align 4"), "{ordnung}:\n{ir}");
        assert!(ir.contains("load atomic i32, ptr @\"FLAGGE\" seq_cst"), "{ordnung}:\n{ir}");
    }
}

/// Examples that stood on `Y103: publish with payload` lower on both targets now.
#[test]
fn publish_beispiele_senken_auf_beiden_zielen() {
    for datei in [
        "117-message-passing-flag.gab",
        "141-atomic-array-pairing.gab",
        "14-paarung-ueber-zwischenfunktion.gab",
        "39-auftragsdienst.gab",
        "41-handschlag.gab",
        "42-zaehlwerk.gab",
        "43-gegenprobe.gab",
    ] {
        let quelle = std::fs::read_to_string(wurzel().join(datei)).expect("lesbar");
        for ziel in [&ZIEL_X86_64, &ZIEL_AARCH64] {
            let (_, codes) = senke(&quelle, datei, ziel);
            assert!(fehler(&codes).is_empty(), "{datei} auf {}: {codes:?}", ziel.name);
        }
    }
}

/// **The shared lock is a reader/writer lock:** a reader passes the ticket gate, counts itself
/// in (`acq_rel`), opens the gate again and counts itself out with `release`; a writer waits
/// for the count to reach zero (`acquire` load) after its ticket. Same on both targets.
#[test]
fn geteilte_sperre_ist_leser_schreiber() {
    for datei in ["10-geteilte-sperre.gab", "13-zeuge-mit-staerke.gab"] {
        let quelle = std::fs::read_to_string(wurzel().join(datei)).expect("lesbar");
        for ziel in [&ZIEL_X86_64, &ZIEL_AARCH64] {
            let (ir, codes) = senke(&quelle, datei, ziel);
            assert!(fehler(&codes).is_empty(), "{datei} auf {}: {codes:?}", ziel.name);
            assert!(ir.contains(".leser\" = global i32 0, align 4"), "{datei}: kein Leserwort:\n{ir}");
            assert!(ir.contains(".leser\", i32 1 acq_rel"), "{datei}: Eintritt\n{ir}");
            assert!(ir.contains(".leser\", i32 1 release"), "{datei}: Austritt\n{ir}");
        }
    }
    let quelle = std::fs::read_to_string(wurzel().join("10-geteilte-sperre.gab")).expect("lesbar");
    let (ir, _) = senke(&quelle, "10", &ZIEL_X86_64);
    // The writer (`rechte_setzen`) drains the readers after its ticket.
    let schreiber = ir.split("define void @\"rechte_setzen\"").nth(1).expect("Schreiber");
    assert!(schreiber.contains("load atomic i32, ptr @\"KAPPEN.leser\" acquire"), "{schreiber}");
    // An exclusive-only lock carries no reader word and no drain.
    let nur = "module nurex {
static mut x : u32 = 0;
lock L protects { x } rank 0 held <= 4 ops;
impl fn f()
    effects { writes x, locks L }
    costs <= 16 ops
{
    locks L {
        x = 1;
    }
}
}
";
    let (ir, codes) = senke(nur, "nurex", &ZIEL_X86_64);
    assert!(fehler(&codes).is_empty(), "{codes:?}");
    assert!(!ir.contains("L.leser"), "{ir}");
}

/// **A `return` inside an `if` inside `locks` releases on its own path only**; the path that
/// falls through still releases at the end of the block (it kept the lock for ever once).
#[test]
fn return_im_wenn_im_sperrblock_gibt_beide_pfade_frei() {
    let quelle = "module sperrpfad {
static mut x : u32 = 0;
lock L protects { x } rank 0 held <= 8 ops;
impl fn f(a : bool) -> u32
    effects { reads x, locks L }
    costs <= 32 ops
{
    locks L {
        if a {
            return x;
        }
    }
    return 0;
}
}
";
    let (ir, codes) = senke(quelle, "sperrpfad", &ZIEL_X86_64);
    assert!(fehler(&codes).is_empty(), "{codes:?}");
    let f = ir.split("define i32 @\"f\"").nth(1).expect("f");
    assert_eq!(f.matches("atomicrmw add ptr @\"L.bereit\", i32 1 seq_cst").count(), 2, "{f}");
}

/// **A field behind the first one is addressed by its own GEP** (it was read from the record's
/// base once: `paar.b` aliased `paar.a`).
#[test]
fn zweites_feld_hat_eigene_adresse() {
    let quelle = "module felder {
pub table paar count 1 {
    slot {
        a : u32,
        b : u32,
    }
}
pub fn f() -> u32
    effects { reads paar.slots, writes paar.slots }
    costs <= 16 ops
{
    paar.slots[0].b = 7;
    return paar.slots[0].b;
}
}
";
    let (ir, codes) = senke(quelle, "felder", &ZIEL_X86_64);
    assert!(fehler(&codes).is_empty(), "{codes:?}");
    // The pointer of the first GEP on field 1 is what the store uses.
    let gep = ir
        .lines()
        .filter(|z| z.trim_end().ends_with(", i32 0, i32 1"))
        .filter_map(|z| z.trim().split(" = ").next())
        .next()
        .expect("GEP auf Feld 1");
    assert!(ir.contains(&format!(", ptr {gep}, align 4, !tbaa")), "{ir}");
}
