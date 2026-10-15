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
        ("1433-geteilte-sperre-ohne-llvm.gab", "Y103"),
        ("1430-aligned-ohne-llvm.gab", "Y104"),
        ("1443-freigabe-kleines-element.gab", "Y103"),
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
/// (`druckfrage frei unter 1048576`, Nutzer-Schwelle 1 MiB): das IR ruft die
/// Zählfrage, vergleicht gegen die Schwelle und läuft darunter in `voll` — auf
/// beiden Zielen, ohne ein Byte BSS (`= global [` steht nirgends).
#[test]
fn abtastung_vor_commit() {
    let quelle = r#"module abtastbeleg {
pub arena Vorrat capacity 0 .. 2 of u64 druckfrage frei unter 1048576;
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
