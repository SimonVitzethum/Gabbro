//! **Der Beispielkorpus, in beide Richtungen.**
//!
//! `beispiele/*.gab` muss **sauber** durchgehen -- das ist die eine Richtung, und sie faellt,
//! sobald eine Regel enger wird, als die Sprache es sagt.
//!
//! `beispiele/gift/*.gab` muss **fallen**, und zwar mit dem Code, der in der ersten Zeile der
//! Datei steht (`-- erwartet: M104`). Das ist die andere Richtung, und sie faellt, sobald eine
//! Regel weiter wird oder eine Absage heimlich ihre Bedeutung wechselt.
//!
//! Ein Pruefer, der nicht fehlschlagen kann, ist kein Pruefer -- und ein Korpus, der nur aus
//! sauberen Faellen besteht, ist kein Korpus.

use gabbro_syntax::diag::Stufe;
use std::path::{Path, PathBuf};

fn wurzel() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join("beispiele")
}

fn dateien(unterordner: Option<&str>) -> Vec<PathBuf> {
    let d = match unterordner {
        Some(u) => wurzel().join(u),
        None => wurzel(),
    };
    let mut out: Vec<PathBuf> = std::fs::read_dir(&d)
        .unwrap_or_else(|e| panic!("{}: {e}", d.display()))
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.extension().and_then(|s| s.to_str()) == Some("gab"))
        .collect();
    out.sort();
    assert!(!out.is_empty(), "{}: keine Beispiele", d.display());
    out
}

fn absagen_von(pfad: &Path) -> (Vec<(&'static str, Stufe)>, String, String) {
    let quelle = std::fs::read_to_string(pfad).unwrap_or_else(|e| panic!("{}: {e}", pfad.display()));
    let name = pfad
        .file_name()
        .and_then(|s| s.to_str())
        .unwrap_or("?")
        .to_string();
    let (baum, mut absagen) = gabbro_syntax::lies(&name, &quelle);
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    // **Und der ERZEUGER laeuft mit, wenn die Datei ihn meint** (2026-08-20).
    //
    // Bis heute lief hier nur `pruefe`, und damit hatte `C001` **keine einzige Giftprobe** --
    // die Kennung des Erzeugers war die einzige, die der Giftkorpus nicht erreichte. Sie
    // aufzunehmen kostet eine Zeile und deckt eine Flaeche, die sonst allein an
    // `pruefe-emission.sh` haengt: *dort faellt auf, was NICHT emittiert; hier faellt auf,
    // was mit dem falschen GRUND nicht emittiert.*
    //
    // > Der Erzeuger laeuft nur fuer die Dateien, die ihn erwarten. Ueber einem Baum, den die
    // > Paesse abgelehnt haben, waere seine Absage ohnehin keine Aussage -- und die anderen
    // > Giftdateien sind genau das.
    if quelle.starts_with("-- erwartet: C001") {
        let _ = gabbro_check::emit::emittiere(&baum, &mut absagen);
    }
    let codes = absagen
        .absagen
        .iter()
        .map(|a| (a.code, a.stufe))
        .collect();
    (codes, absagen.zeige(&quelle), name)
}

#[test]
fn jedes_beispiel_geht_sauber_durch() {
    for pfad in dateien(None) {
        let (codes, bericht, name) = absagen_von(&pfad);
        let fehler: Vec<&str> = codes
            .iter()
            .filter(|(_, s)| *s == Stufe::Fehler)
            .map(|(c, _)| *c)
            .collect();
        assert!(
            fehler.is_empty(),
            "{name} ist ein Beispiel und faellt mit {fehler:?}:\n{bericht}"
        );
    }
}

#[test]
fn jedes_gift_faellt_mit_seinem_code() {
    for pfad in dateien(Some("gift")) {
        let quelle =
            std::fs::read_to_string(&pfad).unwrap_or_else(|e| panic!("{}: {e}", pfad.display()));
        let erwartet = quelle
            .lines()
            .next()
            .and_then(|z| z.strip_prefix("-- erwartet: "))
            .unwrap_or_else(|| {
                panic!(
                    "{}: die erste Zeile muss `-- erwartet: CODE` sein",
                    pfad.display()
                )
            })
            .trim()
            .to_string();
        // **Der DRITTE Zustand braucht auch Proben** (2026-08-19). Bis hierher nahm der
        // Giftkorpus nur Fehler an, und damit hatte keine einzige Hinweis-Kennung eine
        // Probe -- auch `E009` nicht, obwohl der Unterschied zwischen *„unentscheidbar"*
        // und *„in Ordnung"* genau die Stelle ist, an der der falsche Zyklus ein falsches
        // `pure` durchliess. `-- erwartet: Hinweis S007` verlangt die Stufe mit.
        // **And a FOURTH state, measured 2026-08-31: a poison whose defect is at `cc`.**
        //
        // `413` names a `format` field `gueltig`, and the emitter writes `{Format}_gueltig`
        // twice -- once for the field reader, once for the well-formedness function. The
        // checker sees **0 errors**, the emitter refuses **nothing**, and `cc` says
        // `Redefinition`. *`N041` does not catch it: that pass holds names C has taken,
        // while these two are both formed by the EMITTER.*
        //
        // Until today the poison corpus took it for granted that every poison falls at the
        // checker. **`-- erwartet: cc` says the opposite in both halves**, and that makes it
        // a stronger probe than the code form: the checker has to STAY silent, and `cc` has
        // to refuse. A one-sided version would pass over a checker that started refusing for
        // some unrelated reason.
        if erwartet == "cc" {
            let (codes, bericht, name) = absagen_von(&pfad);
            let fehler: Vec<&str> = codes
                .iter()
                .filter(|(_, s)| *s == Stufe::Fehler)
                .map(|(c, _)| *c)
                .collect();
            assert!(
                fehler.is_empty(),
                "{name} traegt `-- erwartet: cc`, also darf der Pruefer NICHTS sagen: \
                 {fehler:?}\n{bericht}"
            );
            // **The other half, and it is the one that carries the claim.** Without it the
            // probe passes over an emitter that has been repaired -- and a poison that can no
            // longer bite reads exactly like one that never could.
            let (baum, mut a2) = gabbro_syntax::lies(&pfad.display().to_string(), &quelle);
            let c = gabbro_check::emit::emittiere(&baum, &mut a2);
            let ziel = std::env::temp_dir().join(format!(
                "gabbro-gift-{}.c",
                pfad.file_stem().unwrap().to_string_lossy()
            ));
            std::fs::write(&ziel, &c).expect("das erzeugte C liegt schreibbar");
            let cc = std::process::Command::new("cc")
                .args(["-std=c11", "-Wall", "-Wextra", "-Werror", "-fsyntax-only"])
                .arg(&ziel)
                .output();
            match cc {
                Ok(r) => assert!(
                    !r.status.success(),
                    "{name} traegt `-- erwartet: cc`, also muss `cc` es ABWEISEN -- es hat \
                     angenommen. Der Erzeugerfehler ist geheilt, und die Probe gehoert \
                     nachgezogen:\n{}",
                    ziel.display()
                ),
                // **A missing `cc` is a missing measurement, never a green one** (W1).
                Err(e) => panic!("`cc` laesst sich nicht starten ({e}) -- NICHTS gemessen"),
            }
            let _ = std::fs::remove_file(&ziel);
            continue;
        }
        // **A FIFTH state, and it is the MIRROR of `cc`** (2026-08-31).
        //
        // `-- erwartet: cc` carries a defect the checker does not see and `cc` does. There is
        // a family where **neither** sees it: two Gabbro declarations become one C symbol,
        // the types agree, at most one side defines, and C11 calls that a legal repetition.
        // `lock TOR` beside `extern fn TOR_nimm()`; `boot b` beside
        // `extern fn gabbro_boot_b()`; `check c` beside `extern fn pruefe_c()`. Measured and
        // RUN in `messung/STILLE-KOLLISIONEN.md`: taking the lock executes the writer's body,
        // and the writer's own archive member is never linked.
        //
        // For those, `-- erwartet: N042` alone would be one-sided. It says the checker
        // speaks; it does not say **that the checker is the only thing that speaks**, and
        // that is the whole claim. A rule with a backstop and a rule without one look
        // identical from a one-sided probe.
        //
        // **`-- erwartet: CODE allein` says both halves:**
        //
        // 1. the checker MUST refuse with `CODE`, and
        // 2. the emitted C must be **ACCEPTED** by `cc -Werror`.
        //
        // Half 2 is the one that carries it, and it falls in the useful direction: the day
        // `cc` (or the emitter) starts catching this form, the probe goes red and asks to be
        // re-classified to `-- erwartet: cc` -- *because then the rule is no longer the only
        // line, and a file that says it is would be lying.*
        //
        // > The emitter runs on the PARSED tree and never consults the passes, so half 2
        // > measures the product as it would ship if this one rule were dropped. That is
        // > exactly the counterfactual the claim needs, and it costs no second build.
        if let Some(code) = erwartet.strip_suffix(" allein") {
            let code = code.trim();
            let (codes, bericht, name) = absagen_von(&pfad);
            let gefallen: Vec<&str> = codes
                .iter()
                .filter(|(_, s)| *s == Stufe::Fehler)
                .map(|(c, _)| *c)
                .collect();
            assert!(
                gefallen.contains(&code),
                "{name} traegt `-- erwartet: {code} allein`, also muss der Pruefer mit \
                 {code} fallen -- gefallen ist {gefallen:?}:\n{bericht}"
            );
            let (baum, mut a2) = gabbro_syntax::lies(&pfad.display().to_string(), &quelle);
            let c = gabbro_check::emit::emittiere(&baum, &mut a2);
            let ziel = std::env::temp_dir().join(format!(
                "gabbro-allein-{}.c",
                pfad.file_stem().unwrap().to_string_lossy()
            ));
            std::fs::write(&ziel, &c).expect("das erzeugte C liegt schreibbar");
            let cc = std::process::Command::new("cc")
                .args(["-std=c11", "-Wall", "-Wextra", "-Werror", "-fsyntax-only"])
                .arg(&ziel)
                .output();
            match cc {
                Ok(r) => assert!(
                    r.status.success(),
                    "{name} traegt `-- erwartet: {code} allein`, also muss `cc` das \
                     Erzeugnis ANNEHMEN -- ohne {code} faellt hier nichts, und genau das ist \
                     die Behauptung. `cc` hat abgewiesen, also gibt es jetzt einen zweiten \
                     Waechter und die Datei gehoert auf `-- erwartet: cc` nachgezogen:\n{}\n{}",
                    ziel.display(),
                    String::from_utf8_lossy(&r.stderr)
                ),
                // **A missing `cc` is a missing measurement, never a green one** (W1).
                Err(e) => panic!("`cc` laesst sich nicht starten ({e}) -- NICHTS gemessen"),
            }
            let _ = std::fs::remove_file(&ziel);
            continue;
        }
        let (stufe, erwartet) = match erwartet.strip_prefix("Hinweis ") {
            Some(c) => (Stufe::Hinweis, c.trim().to_string()),
            None => (Stufe::Fehler, erwartet),
        };
        let (codes, bericht, name) = absagen_von(&pfad);
        let gefallen: Vec<&str> = codes
            .iter()
            .filter(|(_, s)| *s == stufe)
            .map(|(c, _)| *c)
            .collect();
        assert!(
            gefallen.contains(&erwartet.as_str()),
            "{name} sollte mit {erwartet} ({stufe:?}) fallen, gefallen ist {gefallen:?}:\n{bericht}"
        );
    }
}

/// Sprechprobe ueber dem Korpus selbst: es muss beide Sorten geben.
#[test]
fn der_korpus_hat_beide_richtungen() {
    assert!(
        dateien(None).len() >= 5,
        "zu wenige saubere Beispiele -- ein Korpus aus drei Dateien misst nichts"
    );
    assert!(
        dateien(Some("gift")).len() >= 5,
        "zu wenige Gifte -- ein Korpus ohne Gegenprobe belohnt einen stummen Pruefer"
    );
}

/// **K100.4: das Zeugnis muss alles verbuchen, was der Erzeuger absenkt.**
///
/// Das ist die Kreuzprobe, um derentwillen die Einordnung in `zeugnis.rs` **unabhaengig** von
/// der `match`-Kaskade des Erzeugers gefuehrt wird. Zwei Lesungen derselben Datei, und sie
/// muessen sich decken:
///
/// * **Der Erzeuger senkt ab** → das Zeugnis muss die Form kennen.
/// * **Der Erzeuger weigert sich** (`C001`) → dann gibt es kein C, und die Weigerung steht
///   schon da; `UNZUGEORDNET` ist dort erwartbar und kein Befund.
///
/// > *Eine Vertrauensflaeche, die nur der Erzeuger kennt, ist keine gebuchte.*
///
/// **Beim ersten Lauf fand diese Probe sofort etwas:** `lock` senkt zu vier Prototypen ab
/// (`beispiele/10`, `/13` uebersetzen damit sauber), und die Einordnung kannte die Form nicht.
/// Daraus wurde die Klasse `Fremd` — *der Erzeuger schreibt den Prototyp, den Rumpf schreibt
/// jemand anderes*, und das ist weder direkt noch erzeugt.
#[test]
fn was_der_erzeuger_absenkt_steht_im_zeugnis() {
    let mut ohne_buchung = Vec::new();
    let mut emittiert = 0;
    for p in dateien(None) {
        let quelle = std::fs::read_to_string(&p).unwrap();
        let (baum, mut absagen) = gabbro_syntax::lies(&p.display().to_string(), &quelle);
        gabbro_check::pruefe(&baum, &mut absagen);
        let _ = gabbro_check::emit::emittiere(&baum, &mut absagen);
        if absagen.fehler_zahl() > 0 {
            // Der Erzeuger weigert sich -- die Weigerung steht da, das Zeugnis schuldet nichts.
            continue;
        }
        emittiert += 1;
        let e = gabbro_check::zeugnis::erhebe(&baum);
        if !e.unzugeordnet.is_empty() {
            let mut u = e.unzugeordnet.clone();
            u.sort();
            u.dedup();
            ohne_buchung.push(format!("{}: {}", p.display(), u.join(", ")));
        }
    }
    assert!(
        emittiert >= 6,
        "die Probe misst nur, wenn ueberhaupt etwas emittiert -- {emittiert} Dateien"
    );
    assert!(
        ohne_buchung.is_empty(),
        "der Erzeuger senkt Formen ab, die das Zeugnis nicht einordnet:\n  {}",
        ohne_buchung.join("\n  ")
    );
}

/// **Und die Gegenrichtung: das Zeugnis muss melden koennen.**
///
/// Eine Kreuzprobe, die nicht rot werden kann, misst nichts (R14). Hier steht darum eine Form,
/// die der Erzeuger **nicht** kennt und die Einordnung ebenfalls nicht — sie MUSS als
/// `UNZUGEORDNET` herausfallen.
#[test]
fn das_zeugnis_meldet_was_es_nicht_einordnen_kann() {
    // **`group` stand hier bis zum 2026-08-19** und wurde mit «C3c» eingeordnet -- sie
    // erzeugt nichts, und das ist eine Buchung. *Eine Gegenprobe, die durch den Fortschritt
    // ihres Gegenstands stumm wird, ist keine mehr*: sie steht jetzt auf `state`, das
    // weder der Erzeuger noch die Einordnung kennt.
    let q = "module t { state S { transition a { x : 0 -> 1 } } }";
    let (baum, a) = gabbro_syntax::lies("p.gab", q);
    assert_eq!(a.fehler_zahl(), 0, "{}", a.zeige(q));
    let e = gabbro_check::zeugnis::erhebe(&baum);
    assert!(
        e.unzugeordnet.iter().any(|u| u.contains("state")),
        "eine Form, die niemand eingeordnet hat, muss auffallen: {:?}",
        e.unzugeordnet
    );

    // **Und eine Ebene tiefer, denn die Buchung hat zwei Ebenen.** Ein Item, das durchfaellt,
    // und eine ANWEISUNG, die durchfaellt, sind zwei verschiedene Auffangzweige — und die
    // Probe oben deckte nur den ersten.
    //
    // **`breaking` stood here until 2026-08-31 and is no such form any more** -- the emitter
    // lowers it, so it has an `EINORDNUNG` entry, and the counter-probe died at its own
    // subject. *For the second time in this very place: first `group` («C3c», 2026-08-19),
    // now `breaking`.*
    //
    // Counted the same day: **there is no unbooked statement form left.** Every one that
    // `zeugnis::block` names stands in the table. So this does not hunt a third form that
    // lowers tomorrow -- it checks the PATH an unbooked statement would take: the statement
    // reading reaches `zaehle` (it would not find `breaking` otherwise), and `zaehle`s
    // `else` arm falls, which `zeugnis::proben::ein_name_ohne_einordnung_faellt_auf` holds.
    let mit_anweisung = "module t { table A count 4 { slot { a : u32, } invariant p : true; } \
                         impl fn f(x : ptr<normal, rw> A) -> bool effects { writes x } \
                         costs <= 4 ops { breaking p { return true; } } }";
    let (baum_a, _) = gabbro_syntax::lies("p.gab", mit_anweisung);
    let e_a = gabbro_check::zeugnis::erhebe(&baum_a);
    assert!(
        e_a.posten.contains_key("breaking"),
        "die Anweisungslesung muss `zaehle` erreichen: {:?}",
        e_a.posten
    );
    assert!(
        e_a.unzugeordnet.is_empty(),
        "und eine gebuchte Anweisung darf NICHT als unzugeordnet gemeldet werden: {:?}",
        e_a.unzugeordnet
    );

    // Und eine Datei, die vollstaendig gebucht ist, meldet NICHTS -- sonst waere die Probe
    // oben durch eine dauerrote Zeile erfuellt.
    let sauber = "module t { type P = { a : u32, b : bool, }; \
                  impl fn f() -> P effects { pure } costs <= 4 ops { return P(a: 1, b: true); } }";
    let (baum2, _) = gabbro_syntax::lies("p.gab", sauber);
    assert!(
        gabbro_check::zeugnis::erhebe(&baum2).unzugeordnet.is_empty(),
        "eine vollstaendig gebuchte Datei meldet nichts"
    );
}

/// **48 fremde Ruempfe im Korpus, NULL davon sagen, was sie herstellen muessen.**
///
/// `effects` und `costs` sind **Schranken, keine Pflichten.** `extern fn mmu_an(p) ->
/// BootPhase effects { consumes p, writes mmu } costs <= 4096 ops;` erlaubt einen Rumpf, der
/// **gar nichts tut**: er fasst nichts Verbotenes an und kostet null. *Was der Rufer wirklich
/// annimmt — „danach ist die MMU an" — steht nirgends.*
///
/// **`ensures` an einer Deklaration ohne Rumpf ist genau diese Zeile, und die Grammatik kennt
/// sie seit jeher.** Gemessen 2026-08-17: null Stueck im ganzen Korpus.
///
/// > Diese Probe nagelt die Null NICHT fest — sie soll fallen, sobald jemand die erste
/// > schreibt. Was sie festnagelt, ist, dass die Zaehlung **funktioniert**: eine
/// > ausgesprochene Pflicht muss auch als solche ankommen.
#[test]
fn eine_ausgesprochene_pflicht_wird_gezaehlt() {
    let ohne = "module t { linear ghost type P; \
                extern fn f(p : P) -> P effects { consumes p, writes mmu } costs <= 8 ops; }";
    let (baum, a) = gabbro_syntax::lies("p.gab", ohne);
    assert_eq!(a.fehler_zahl(), 0, "{}", a.zeige(ohne));
    let e = gabbro_check::zeugnis::erhebe(&baum);
    assert_eq!(e.fremde.len(), 1, "ein Rumpf, den diese Einheit nicht schreibt");
    assert_eq!(
        e.fremde_mit_pflicht, 0,
        "`effects` und `costs` sind Schranken -- ein Rumpf, der nichts tut, erfuellt sie"
    );

    let mit = "module t { linear ghost type P; \
               extern fn f(p : P) -> P ensures result != p \
               effects { consumes p, writes mmu } costs <= 8 ops; }";
    let (baum2, a2) = gabbro_syntax::lies("p.gab", mit);
    assert_eq!(a2.fehler_zahl(), 0, "{}", a2.zeige(mit));
    assert_eq!(
        gabbro_check::zeugnis::erhebe(&baum2).fremde_mit_pflicht,
        1,
        "eine ausgesprochene Pflicht muss ankommen -- sonst zaehlt die Spalte nichts"
    );
}

/// **Die Tiefenschranke haelt auf dem duennsten Stapel** — und zwar gemessen, nicht geglaubt.
///
/// Zweimal stand hier eine Zahl, die nur auf einem groesseren Stapel hielt: 512 (gemessen am
/// Hauptfaden mit 8 MiB) und danach 128 (gemessen an `lies` allein, also am halben Weg). Beide
/// Male fiel der TESTLAEUFER, nicht die Eingabe — *das Werkzeug fiel an seiner eigenen Probe*,
/// und ein „gruener Lauf" hing an einem `RUST_MIN_STACK`, das nirgends stand.
///
/// Dieser Test faehrt die ganze Kette auf **2 MiB** — dem Vorgabewert eines Rust-Testfadens,
/// dem duennsten Stapel, auf dem der Pruefer laufen soll — und zwar am **tiefsten Baum, den
/// der Parser noch ANNIMMT**. Ein abgewiesener Baum sagt nichts ueber den Stapel: der Parser
/// steigt gar nicht erst hinab.
///
/// Reisst der Stapel, bricht der Lauf mit `stack overflow` ab und nennt diesen Faden.
/// *Das ist die Absicht:* eine Grenze, die ueber ihren Stapel wandert, soll das nicht
/// heimlich koennen.
#[test]
fn die_tiefenschranke_haelt_auf_zwei_mebibyte() {
    let h = std::thread::Builder::new()
        .stack_size(2 * 1024 * 1024)
        .name("tiefenschranke".into())
        .spawn(|| {
            for n in (1..=gabbro_syntax::parse::TIEFE_MAX).rev() {
                let q = format!(
                    "module d {{ impl fn f() -> u32 effects {{ pure }} costs <= 1 ops \
                     {{ return {}1{}; }} }}",
                    "(".repeat(n),
                    ")".repeat(n)
                );
                let (baum, mut absagen) = gabbro_syntax::lies("tiefe.gab", &q);
                let _ = gabbro_check::pruefe(&baum, &mut absagen);
                if !absagen.absagen.iter().any(|a| a.code == "P038") {
                    return n;
                }
            }
            0
        })
        .unwrap();
    let tiefste = h.join().unwrap();
    assert!(
        tiefste >= gabbro_syntax::parse::TIEFE_MAX / 2,
        "der tiefste angenommene Baum liegt bei {tiefste} -- die Schranke laesst weniger \
         als die Haelfte ihrer eigenen Zahl durch"
    );
}

// ==========================================================================================
// Die Zusage eines FREMDEN Rumpfes, als eigener Posten im Zeugnis (2026-08-21)
// ==========================================================================================

/// Das Zeugnis einer echten Korpusdatei, als Text.
fn zeugnis_von(name: &str) -> String {
    let p = wurzel().join(name);
    let quelle = std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("{}: {e}", p.display()));
    let (baum, mut absagen) = gabbro_syntax::lies(name, &quelle);
    gabbro_check::pruefe(&baum, &mut absagen);
    assert_eq!(absagen.fehler_zahl(), 0, "{}", absagen.zeige(&quelle));
    gabbro_check::zeugnis::zeige(&baum, name, &quelle)
}

/// **Die Stelle steht mit Namen im Zeugnis -- an einer echten Korpusdatei.**
///
/// `beispiele/39-auftragsdienst.gab` ist die EINZIGE Datei des ganzen Korpus, in der der
/// Vertrag eines fremden Rumpfes heute etwas bewegt: `naechste_menge` verspricht
/// `result >= 1`, sein Ergebnistyp ist `Rest = u32 in 0 .. 4096`, und damit rechnet der
/// Rufer ab Zeile 127 mit `1 .. 4096`.
///
/// > **Das ist eine ANNAHME ueber fremden Code mit Wirkung im Erzeugnis** -- ein engerer
/// > Bereich besteht Pruefungen, die ein weiterer nicht bestuende. Sie wird nicht
/// > abgeschaltet; ein Vertrag SOLL wirken. Sie wird gebucht.
/// **`U005` fired FALSELY on a correct program until 2026-08-24.**
///
/// `sperren_je_traeger` resolved the rank with `konst_wert("", …)` -- from the ROOT, not from
/// the declaring module -- and turned the failure into `0`. Two locks with DIFFERENT,
/// perfectly well-defined ranks then both read `0` and counted as equal:
///
/// ```text
/// Fehler: [U005] `group G` spans `A` and `B` -- both `rank 0`
/// ```
///
/// **`H014` stayed silent**, because there the rank resolves fine (`geteilt.rs` passes the
/// module) -- so the only message the program got was the wrong one. *A wrong refusal is more
/// expensive than a missing one: it makes someone rewrite a program that was correct.*
///
/// The poison side is `beispiele/gift/262-gruppe-gleicher-rang.gab`, where the ranks really
/// are equal. This test is the other half of the pair.
#[test]
fn ein_modulweiter_rang_loest_auf() {
    let quelle = "\
module probe::rang {
const RANG_A : u32 = 1;
const RANG_B : u32 = 2;
table T count 8 { slot { v : u32, } }
table U count 8 { slot { v : u32, } }
lock A protects { T } rank RANG_A held <= 50 ops;
lock B protects { U } rank RANG_B held <= 50 ops;
group G over { T, U } {
    invariant beide cost O(1) runs offline : T.slots[0].v == U.slots[0].v;
}
}
";
    let (baum, mut absagen) = gabbro_syntax::lies("rang.gab", quelle);
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    let fehler: Vec<&str> = absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code)
        .collect();
    assert!(
        fehler.is_empty(),
        "zwei VERSCHIEDENE Raenge als Modulkonstante duerfen nicht als gleich gelten, \
         gefallen ist {fehler:?}:\n{}",
        absagen.zeige(quelle)
    );
}

/// **«B26»: a `requires` at a register is COUNTED, since 2026-08-24.**
///
/// Until then no pass read `RegDecl::requires` -- the clause parsed and vanished.
/// `PFLICHTEN.md` carried that as a hanging plumbing duty, and the note named the cure
/// itself: *"the same shape as `ensures` on an `extern fn`."* That one became a counted
/// foreign duty; this one becomes a counted **device promise**.
///
/// > **It is not checked, and that is the statement.** The register is volatile, a hostile
/// > device may report whatever it likes («B33»). *The promise is booked, not its holding*
/// > -- and with that it stands in the register instead of in nothing.
#[test]
fn ein_requires_am_register_wird_gezaehlt() {
    let p = wurzel().join("..").join("messung").join("fragmente").join("F04.gab");
    let q = std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("{}: {e}", p.display()));
    let (baum, _) = gabbro_syntax::lies("F04.gab", &q);
    let bericht = gabbro_check::pflichten::zeige(&baum, "F04.gab");
    for stueck in ["Device promise at a register", "reg QUEUE_SIZE requires", "1 device"] {
        assert!(bericht.contains(stueck), "fehlt: {stueck}\n{bericht}");
    }
}

#[test]
fn eine_fremdverengung_steht_mit_namen_im_zeugnis() {
    let z = zeugnis_von("39-auftragsdienst.gab");
    assert!(
        z.contains("F  FOREIGN CONTRACTS THAT NARROWED"),
        "der Abschnitt fehlt ganz:\n{z}"
    );
    for stueck in [
        "abarbeiten",
        "naechste_menge",
        "result >= 1",
        "u32 in 0 .. 4096  ->  u32 in 1 .. 4096",
        "1 narrowings from foreign contracts",
    ] {
        assert!(z.contains(stueck), "`{stueck}` fehlt im Zeugnis:\n{z}");
    }
}

/// **Und die Gegenrichtung, ohne die die Zahl nichts misst (R14/W17).**
///
/// `beispiele/41-handschlag.gab` hat dieselbe Klausel an derselben Bauform -- `extern fn
/// naechster_puffer() -> Laenge or Quellefehler ensures result >= 1`, gerufen in Zeile 210.
/// **`Laenge` ist `u32 in 1 .. 4096`, und damit bewegt die Klausel nichts.**
///
/// *Sie steht im Zeugnis unter E, weil sie Flaeche ist, und sie steht NICHT unter F, weil sie
/// niemanden bindet.* Genau diese Unterscheidung ist der Gegenstand des Postens: eine
/// Zaehlung, die jede vorhandene Klausel zaehlt, faellt hier.
#[test]
fn eine_klausel_ohne_wirkung_steht_nicht_unter_f() {
    let z = zeugnis_von("41-handschlag.gab");
    assert!(
        z.contains("6 foreign bodies (1 state their duty), 0 narrowings from foreign contracts"),
        "die Klausel ist da und bindet niemanden -- Flaeche ja, Verengung nein:\n{z}"
    );
    assert!(
        !z.contains("F  FOREIGN CONTRACTS THAT NARROWED"),
        "ein leerer Abschnitt F ist eine Zeile, die eine Wirkung behauptet:\n{z}"
    );
}

/// **Ein Rumpf, den Gabbro SIEHT, gehoert nicht in diese Buchung.**
///
/// Dieselbe Verengung an einem `impl fn` ist eine Ableitung, die Gabbro einmal selbst
/// nachrechnen wird -- keine Annahme ueber fremden Code. *Ohne diese Probe wuerde jede
/// Nachbedingung des eigenen Korpus in der Vertrauensflaeche landen, und die Zahl waere
/// zu gross statt zu klein.*
#[test]
fn ein_eigener_rumpf_zaehlt_nicht_als_fremdverengung() {
    let fremd = "module t { extern fn hole() -> u32 ensures result <= 100 \
                 effects { pure } costs <= 1 ops; \
                 impl fn nutze() -> u32 effects { pure } costs <= 4 ops \
                 { let x = hole(); return x; } }";
    let eigen = "module t { impl fn hole() -> u32 ensures result <= 100 \
                 effects { pure } costs <= 1 ops { return 7; } \
                 impl fn nutze() -> u32 effects { pure } costs <= 4 ops \
                 { let x = hole(); return x; } }";
    for (quelle, erwartet) in [(fremd, 1usize), (eigen, 0usize)] {
        let (baum, a) = gabbro_syntax::lies("p.gab", quelle);
        assert_eq!(a.fehler_zahl(), 0, "{}", a.zeige(quelle));
        assert_eq!(
            gabbro_check::fremdverengungen(&baum).len(),
            erwartet,
            "erwartet {erwartet} Fremdverengungen in:\n{quelle}"
        );
    }
}

/// **Die zweite Haelfte: die relationale Nachbedingung** (`result <op> <Ort>`).
///
/// Sie legt keinen Bereich an, sondern einen `Fakt::Beziehung` -- und ist damit dieselbe
/// Vertrauensflaeche in einer anderen Gestalt. *Waere nur die Bereichshaelfte gebucht, saehe
/// die Flaeche kleiner aus, als sie ist.*
///
/// **Wirksam heisst hier: eine Tatsache ist ENTSTANDEN**, nicht: sie wird gebraucht. Die Zahl
/// ist in dieser Richtung eine OBERE Schranke, und das steht in `messung/FREMDVERENGUNG.md`.
#[test]
fn auch_die_relationale_nachbedingung_wird_gebucht() {
    let q = "module t { \
             type Stapel = { len : u32, }; \
             extern fn frei(s : ptr<normal, r> Stapel) -> u32 ensures result <= s.len \
             effects { reads s } costs <= 8 ops; \
             impl fn nutze(s : ptr<normal, r> Stapel) -> u32 effects { reads s } \
             costs <= 16 ops { let f = frei(s); return f; } }";
    let (baum, a) = gabbro_syntax::lies("p.gab", q);
    assert_eq!(a.fehler_zahl(), 0, "{}", a.zeige(q));
    let stellen = gabbro_check::fremdverengungen(&baum);
    assert_eq!(stellen.len(), 1, "{:?}", stellen);
    assert!(
        matches!(stellen[0].wirkung, gabbro_check::fremdverengung::Wirkung::Beziehung),
        "die relationale Form ist eine Beziehung, kein Bereich: {:?}",
        stellen[0]
    );
    assert_eq!(stellen[0].klausel, "result <= s.len");
    assert_eq!(stellen[0].rufer, "nutze");
}

// --- Stufe 6, Teil D ---

/// **Die BEFUNDZEILE fuehrt die nicht falsifizierbaren Annahmen getrennt** (2026-08-21).
///
/// Jede `A`-Zeile trug seit jeher ihre Klasse -- `Sonde <x>` oder `NOT FALSIFIABLE --
/// <grund>`. **Die Buchung darunter warf beide in einen Topf.** Eine nicht falsifizierbare
/// Annahme ist aber eine andere Waehrung: gegen sie kann keine Sonde je etwas ausrichten,
/// und `S004` weist genau deshalb eine unfalsifizierbare Fortschrittsannahme ab.
///
/// *Dieselbe Klasse wie bei den Fremdverengungen -- eine Zahl, in der zwei Waehrungen
/// stecken, liest sich wie eine.*
///
/// **Since 2026-08-30 there are THREE currencies** -- `UNCOVERED` joined: an assumption naming
/// a probe that no program redeems. It is neither falsifiable (nobody does it) nor
/// not-falsifiable (somebody could), and counting it in the first group was exactly the blend
/// this test stands against.
#[test]
fn die_befundzeile_trennt_die_nicht_falsifizierbaren_annahmen() {
    let z = zeugnis_von("06-annahmen.gab");
    // Gezaehlt wird die LISTE, und die Befundzeile muss dieselbe Zahl tragen. *Ein Literal
    // hier waere ein Muster, das seine eigene Antwort enthaelt* -- die Klasse von W16.
    // **Both patterns mean the A LINE and not the finding line below it** -- and since
    // 2026-08-31, when the labels of the A line went English, that is a matter of two
    // characters. `NOT FALSIFIABLE --` separates against the finding line's
    // `NOT FALSIFIABLE,`; `UNCOVERED -- no program` against its `UNCOVERED -- named a
    // probe`. *A pattern that counts the summary too reports one too many and looks right.*
    let nicht_falsifizierbar = z.matches("NOT FALSIFIABLE --").count();
    let ungedeckt = z.matches("UNCOVERED -- no program").count();
    assert!(
        nicht_falsifizierbar > 0,
        "diese Datei muss nicht falsifizierbare Annahmen fuehren, sonst misst der Test nichts:\n{z}"
    );
    assert!(
        ungedeckt > 0,
        "diese Datei muss ungedeckte Annahmen fuehren, sonst misst die zweite Haelfte \
         nichts:\n{z}"
    );
    assert!(
        z.contains(&format!(
            "assumptions ({nicht_falsifizierbar} of them NOT FALSIFIABLE, {ungedeckt} UNCOVERED"
        )),
        "die Befundzeile muss BEIDE Klassen mitfuehren, und beide Zahlen muessen die der \
         Liste sein ({nicht_falsifizierbar} / {ungedeckt}):\n{z}"
    );
}

/// **Die GNADENFRIST wird verlangt (`H015`) -- und die Sprechprobe geht in BEIDE Richtungen.**
///
/// `beispiele/31-rcu.gab` gibt unter der Schreibersperre zurueck UND nennt die Gnadenfrist;
/// `beispiele/gift/230` tut alles Pruefbare richtig und nennt sie nicht. *Der Unterschied
/// zwischen beiden sind drei Zeilen, die kein Pass herstellen kann.*
#[test]
fn die_gnadenfrist_wird_verlangt_und_nur_sie() {
    let (codes, bericht, _) = absagen_von(&wurzel().join("31-rcu.gab"));
    assert!(
        !codes.iter().any(|(c, _)| *c == "H015"),
        "31-rcu.gab NENNT die Gnadenfrist -- H015 darf hier nicht fallen:\n{bericht}"
    );
    let (codes, bericht, _) = absagen_von(&wurzel().join("gift").join("230-gnadenfrist-fehlt.gab"));
    assert!(
        codes.iter().any(|(c, _)| *c == "H015"),
        "230 nennt sie nicht -- H015 muss fallen:\n{bericht}"
    );
    // **Und NUR sie.** Die Datei ist so gebaut, dass die zwei pruefbaren Haelften zufrieden
    // sind: unter `SCHREIBER` zurueckgegeben, nicht aus einem `observes` heraus. Faellt hier
    // zusaetzlich `H011` oder `H012`, misst die Giftprobe etwas anderes als ihren Gegenstand.
    for unerwuenscht in ["H011", "H012"] {
        assert!(
            !codes.iter().any(|(c, _)| *c == unerwuenscht),
            "230 soll GENAU an der Gnadenfrist fallen, nicht an {unerwuenscht}:\n{bericht}"
        );
    }
}

/// **Der SPERRABDRUCK ist eine benannte Annahme der Axiomschicht** (2026-08-21).
///
/// `beweise/Gruppe_Erhaltung.thy`, Locale `zug`, nimmt `abdruck_innen` an und schliesst
/// daraus, dass niemand hinsieht. Dass ein gehaltener Abdruck einen fremden Kern wirklich
/// fernhaelt, ist eine Aussage ueber das SPEICHERMODELL -- *vorher war die Praemisse
/// unsichtbar; jetzt steht sie in der Zahl.*
#[test]
fn eine_gruppe_bringt_ihre_sperrabdruckannahme_mit() {
    let z = zeugnis_von("17-gruppe-ueber-zwei-sperren.gab");
    assert!(
        z.contains("sperrabdruck_haelt_fremde_kerne_fern"),
        "eine `group` ruht auf dem Sperrabdruck -- die Annahme gehoert ins Zeugnis:\n{z}"
    );
    // **Nicht falsifizierbar, und das ist die Aussage.** Eine Sonde, die den Abdruck haelt
    // und nachsieht, zeigt nur, dass diesmal niemand hingesehen hat -- derselbe Grund wie
    // bei `release_stellt_sichtbarkeit_her`.
    assert!(
        z.lines().any(|z| z.contains("sperrabdruck_haelt_fremde_kerne_fern")
            && z.contains("NOT FALSIFIABLE")),
        "sie ist nicht falsifizierbar, und der Grund steht in ihrer Zeile:\n{z}"
    );
    // Und die Gegenrichtung: eine Datei OHNE `group` bringt sie nicht mit. *Eine Annahme,
    // die immer dasteht, unterscheidet nichts.*
    let ohne = zeugnis_von("31-rcu.gab");
    assert!(
        !ohne.contains("sperrabdruck_haelt_fremde_kerne_fern"),
        "ohne `group` ruht nichts auf dem Abdruck:\n{ohne}"
    );
}

// --- abi ---

/// **The TWO-FILE probe: the lock ring across a real library boundary.**
///
/// `beispiele/gift/250` is the union as ONE file -- what the checker gets to see. This test
/// walks the road a user walks, and it is the only one that measures the BRIDGE itself:
/// `gabbro abi` over library A and B, the two products put in front of the caller, then
/// checked.
///
/// **Until 2026-08-21 it was green without the ring falling** -- 0 errors, 0 hints, and the
/// program was a deadlock. `gabbro abi` did not write the `lock` line, so the rank rules in
/// the checker found no rank at the importer and stepped over it in silence.
///
/// > *The worst possible outcome of an ABI is not that it is missing, but that it is silent*
/// > -- then it has handed a class back without anybody seeing it.
#[test]
fn ring_across_two_libraries() {
    let (union, codes) = abi_union(&["lib-speicher.gab", "lib-geraet.gab"], "mischt.gab");
    // **The interface must EXPLAIN the lock, not merely name it.** Without that line
    // everything below is silent, and the assertion after it measures nothing.
    assert!(
        union.contains("lock SPEICHER") && union.contains("lock GERAET"),
        "an interface that carries `locks SPEICHER` and not `lock SPEICHER` is none -- \
         it names something and does not explain it:\n{union}"
    );
    let ring = codes.iter().filter(|c| **c == "H012").count();
    assert_eq!(
        ring, 2,
        "the ring has TWO directions, and both are errors -- fallen is {codes:?}"
    );
}

/// The other direction, and without it the one above measures nothing (R14/W17): **the same
/// bridge carries a program whose ranks fit.** `AUFTRAG` (rank 0) outside, the call takes
/// `ZAEHLER` (rank 1) inside -- ascending, hence allowed.
///
/// *The order `AUFTRAG < ZAEHLER` stands in neither of the two files; it comes into being
/// only at the union.* If `H016` were too sharp, or the interface carried the lock wrongly,
/// THIS test falls -- not the one above.
#[test]
fn the_same_bridge_carries_the_ascending_order() {
    let (_, codes) = abi_union(&["zaehlwerk.gab"], "dienst.gab");
    assert!(
        codes.is_empty(),
        "taken in ascending order is allowed, fallen is {codes:?}"
    );
}

/// **Without the bridge the same caller falls BY NAME.** The third state is the one that may
/// not exist: neither refused nor confirmed. `H016` says the lock name is unexplained,
/// `K003` that the function is not declared here -- both issued in the checker, not here.
#[test]
fn without_the_bridge_the_caller_falls_by_name() {
    let (_, codes) = abi_union(&[], "dienst.gab");
    for expected in ["H016", "K003"] {
        assert!(
            codes.contains(&expected),
            "without an interface {expected} must fall, fallen is {codes:?}"
        );
    }
}

/// `gabbro abi` over each library, the products in front of the caller, then check.
/// Returns the united source and the ERROR codes of the unit.
fn abi_union(libraries: &[&str], caller: &str) -> (String, Vec<&'static str>) {
    let ordner = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join("messung")
        .join("abi-proben");
    let mut preamble = String::new();
    for b in libraries {
        let pfad = ordner.join(b);
        let quelle =
            std::fs::read_to_string(&pfad).unwrap_or_else(|e| panic!("{}: {e}", pfad.display()));
        let (baum, mut absagen) = gabbro_syntax::lies(b, &quelle);
        let _ = gabbro_check::pruefe(&baum, &mut absagen);
        // **An interface out of a unit with errors is a promise about a program the checker
        // did not accept** -- the same rule as in the command.
        assert_eq!(
            absagen.fehler_zahl(),
            0,
            "{b} is the library and falls itself:\n{}",
            absagen.zeige(&quelle)
        );
        preamble.push_str(&gabbro_check::abi::schreibe(&baum, &quelle));
        preamble.push('\n');
    }
    let pfad = ordner.join(caller);
    let quelle =
        std::fs::read_to_string(&pfad).unwrap_or_else(|e| panic!("{}: {e}", pfad.display()));
    let ganz = if preamble.is_empty() {
        quelle.clone()
    } else {
        format!("{preamble}\n{quelle}")
    };
    let versatz = ganz.len() - quelle.len();
    let (baum, mut absagen) = gabbro_syntax::lies(caller, &ganz);
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    // Only the refusals of the UNIT -- what stands in the preamble belongs to the library.
    let codes = absagen
        .absagen
        .iter()
        .filter(|a| a.span.von as usize >= versatz && a.stufe == Stufe::Fehler)
        .map(|a| a.code)
        .collect();
    (ganz, codes)
}
