//! **`~` -- and the only question is the WIDTH.**
//!
//! The emitter writes `({c})~({c})(x)` and not a bare `~`. The reason is the integer
//! promotion: C lifts every operand narrower than `int` up to `int`, and `~(uint16_t)0xF0F0`
//! is `0xFFFF0F0F` there instead of `0x0F0F`.
//!
//! **This file measures that on a RUNNING program**, because neither the text probe alone
//! nor the return-value probe alone can:
//!
//! * *Measured 2026-09-01:* with and without the casts, `maske8`, `falte`, `maske32` and
//!   `loesche` yield **the same numbers** -- the `uint8_t`/`uint16_t` return type truncates
//!   the promotion away again. **A probe that measures the same thing in both directions
//!   measures nothing.**
//! * It becomes visible only where the complement's value is used without being cut back:
//!   in a COMPARISON (`~b == 3855`) and in a WIDENING (`let w : u32 = ~b;`).
//! * And `cc -Wall -Wextra -Werror` catches **exactly one** of those two: at the comparison
//!   `-Wsign-compare` fires; at the widening it compiles without a word and computes
//!   `4294905615`, where M1 says `u16 in 0 .. 65535`.
//!
//! > *A guardian that catches only the one case covers half of it* -- and that is why a RUN
//! > stands here and not a compilation.
//!
//! **The second half of the same item stands at the bottom of this file**: `u32::max` in an
//! expression. It is the same question -- a mask and its width -- and it had the same shape
//! of defect: the `const` path folded it, nobody else asked, and the expression path lowered
//! a WORD of the vocabulary as if it were a place.

use gabbro_syntax::diag::Stufe;
use std::path::PathBuf;
use std::process::Command;

fn wurzel() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|p| p.parent())
        .expect("the tree lies two levels above the crate")
        .to_path_buf()
}

/// The emitted C of `beispiele/61-invertierung.gab` -- and the checker has to stay silent
/// first, or this file measures a program that was never accepted.
fn erzeugtes_c() -> String {
    emittiere("61-invertierung.gab")
}

/// The emitted C of one clean example under `beispiele/`.
fn emittiere(datei: &str) -> String {
    let pfad = wurzel().join("beispiele").join(datei);
    let quelle = std::fs::read_to_string(&pfad).unwrap_or_else(|e| panic!("{datei}: {e}"));
    let (baum, mut absagen) = gabbro_syntax::lies(&pfad.display().to_string(), &quelle);
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    let fehler: Vec<&str> = absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code)
        .collect();
    assert!(
        fehler.is_empty(),
        "the complement probe is REFUSED ({fehler:?}) -- then the run below it measures \
         nothing:\n{}",
        absagen.zeige(&quelle)
    );
    let c = gabbro_check::emit::emittiere(&baum, &mut absagen);
    assert!(!c.is_empty(), "the complement probe emits NOTHING -- nothing measured");
    c
}

const TREIBER: &str = r#"
#include <stdio.h>

int main(void) {
    int abweichungen = 0;
#define P(name, wert, gemeint) \
    do { unsigned long g = (unsigned long)(wert); \
         if (g != (unsigned long)(gemeint)) { abweichungen++; \
             printf("ABWEICHUNG %s: geliefert=%lu gemeint=%lu\n", name, g, (unsigned long)(gemeint)); } \
    } while (0)
    /* ~0xF0 over eight bits */
    P("maske8", maske8(240u), 15u);
    /* RFC 1071: 0x0001 + 0x0002 = 3, complement 0xFFFC */
    P("falte", falte(0x00010002u), 65532u);
    /* the double fold: 0xFFFF + 0xFFFF folds to 0xFFFF, complement 0 */
    P("falte-rand", falte(0xFFFFFFFFu), 0u);
    P("maske32", maske32(240u), 4294967055u);
    P("loesche", loesche(0xFF0Fu, 0x0F0Fu), 61440u);
    /* THE two rows that carry the claim: without the cast the promotion is visible */
    P("vergleich", (unsigned)ist_gleich(0xF0F0u), 1u);
    P("verbreiterung", verbreitert(0xF0F0u), 3855u);
    /* the exact range: ~(u8 in 0..15) is u8 in 240..255, and the declaration says so */
    P("nibble", hohes_nibble(5u), 250u);
    printf("geprueft=8 abweichungen=%d\n", abweichungen);
    return 0;
}
"#;

/// **The poison probe, and it RUNS.**
///
/// Compiles the emitted C with exactly the command stage 9 of `pruefe-emission.sh` uses,
/// executes it and demands every one of the eight numbers. *Against an emitter without the
/// outer cast the `verbreiterung` row falls with `4294905615`* -- and `cc` compiles that
/// version without a single warning.
#[test]
fn das_ausgelieferte_c_komplementiert_in_der_erklaerten_breite() {
    let mut c = erzeugtes_c();
    c.push_str(TREIBER);

    let d = std::env::temp_dir().join("gabbro-komplement");
    std::fs::create_dir_all(&d).expect("the work directory is writable");
    let quelle = d.join("lauf.c");
    let ziel = d.join("lauf");
    std::fs::write(&quelle, &c).expect("the emitted C is writable");

    let bau = Command::new("cc")
        .args(["-std=c11", "-O2", "-Wall", "-Wextra", "-Werror"])
        .arg("-o")
        .arg(&ziel)
        .arg(&quelle)
        .output();
    let bau = match bau {
        Ok(r) => r,
        // **A missing `cc` is a missing measurement, never a green one** (W1).
        Err(e) => panic!("`cc` cannot be started ({e}) -- NOTHING measured"),
    };
    assert!(
        bau.status.success(),
        "the emitted C does not compile under `-Wall -Wextra -Werror`:\n{}\n{}",
        String::from_utf8_lossy(&bau.stderr),
        quelle.display()
    );

    let lauf = Command::new(&ziel)
        .output()
        .unwrap_or_else(|e| panic!("the compiled program does not run ({e}) -- NOTHING measured"));
    assert!(lauf.status.success(), "the compiled program aborts");
    let aus = String::from_utf8_lossy(&lauf.stdout);
    assert!(
        aus.contains("geprueft=8 abweichungen=0"),
        "the shipped C computes something other than what was checked:\n{aus}"
    );
    let _ = std::fs::remove_file(&quelle);
    let _ = std::fs::remove_file(&ziel);
}

/// **The counter-probe: the text, pinned in BOTH directions.**
///
/// The run above dies on an emitter that casts too LITTLE. It does not die on one that casts
/// too much -- `(uint64_t)~(uint64_t)(x)` over a `u16` computes the same number as long as
/// the return type cuts it back, and would be wrong all the same. So every row here says
/// which width must stand at which site.
#[test]
fn der_cast_traegt_die_breite_des_operanden_und_keine_andere() {
    let c = erzeugtes_c();
    for (zeile, gemeint) in [
        ("(uint8_t)~(uint8_t)(m)", "the `u8` case casts to `uint8_t`"),
        ("(uint16_t)~(uint16_t)(c)", "the `u16` case casts to `uint16_t`"),
        ("(uint32_t)~(uint32_t)(m)", "the `u32` case casts to `uint32_t`"),
        ("a & (uint16_t)~(uint16_t)(b)", "`a & ~b` brackets the complement, not the and"),
        ("(uint16_t)~(uint16_t)(b) == 3855", "the comparison cuts back BEFORE comparing"),
        ("uint32_t w = (uint16_t)~(uint16_t)(b);", "the widening cuts back BEFORE assigning"),
    ] {
        assert!(
            c.contains(zeile),
            "the emitted C does not carry `{zeile}` -- {gemeint}:\n{c}"
        );
    }
    // **And no bare `~` anywhere.** Without this line an emitter would stay green that
    // writes the six forms above and puts a seventh beside them without a cast.
    for zeile in c.lines() {
        if let Some(i) = zeile.find('~') {
            assert!(
                zeile[..i].ends_with(')'),
                "a `~` with no cast before it -- the integer promotion then decides the \
                 width:\n{zeile}"
            );
        }
    }
}

/// **`u32::max` in an EXPRESSION -- the second half of the same item.**
///
/// The `const` path folded it correctly from day one (`#define G 4294967295u`); the
/// expression path lowered it as a PLACE and wrote `w ^ u32->max`, which `cc` rejects as an
/// undeclared `u32`. **And M1 gave the form no type at all**, so the width rule that catches
/// the same mask spelled `4294967295` never ran.
///
/// The probe compiles the example and RUNS it, because a text probe alone would pass over an
/// emitter that folds `u32::max` to some other number.
#[test]
fn ein_benannter_grenzwert_ist_eine_zahl_und_kein_ort() {
    let mut c = emittiere("62-grenzwort-im-ausdruck.gab");
    assert!(
        !c.contains("u32->max") && !c.contains("->min"),
        "a limit word lowered as a PLACE:\n{c}"
    );
    // `i32::min` carries no `u` -- `-2147483648u` would be another number, not just ugly.
    assert!(c.contains("(-2147483648)"), "`i32::min` needs no `u` suffix:\n{c}");
    assert!(c.contains("4294967295u"), "`u32::max` folds to its value:\n{c}");
    c.push_str(GRENZTREIBER);

    let d = std::env::temp_dir().join("gabbro-grenzwort");
    std::fs::create_dir_all(&d).expect("the work directory is writable");
    let quelle = d.join("lauf.c");
    let ziel = d.join("lauf");
    std::fs::write(&quelle, &c).expect("the emitted C is writable");
    let bau = Command::new("cc")
        .args(["-std=c11", "-O2", "-Wall", "-Wextra", "-Werror"])
        .arg("-o")
        .arg(&ziel)
        .arg(&quelle)
        .output();
    let bau = match bau {
        Ok(r) => r,
        Err(e) => panic!("`cc` cannot be started ({e}) -- NOTHING measured"),
    };
    assert!(
        bau.status.success(),
        "the emitted C does not compile under `-Wall -Wextra -Werror`:\n{}\n{}",
        String::from_utf8_lossy(&bau.stderr),
        quelle.display()
    );
    let lauf = Command::new(&ziel)
        .output()
        .unwrap_or_else(|e| panic!("the compiled program does not run ({e}) -- NOTHING measured"));
    assert!(lauf.status.success(), "the compiled program aborts");
    let aus = String::from_utf8_lossy(&lauf.stdout);
    assert!(
        aus.contains("geprueft=6 abweichungen=0"),
        "the shipped C computes something other than what was checked:\n{aus}"
    );
    let _ = std::fs::remove_file(&quelle);
    let _ = std::fs::remove_file(&ziel);
}

const GRENZTREIBER: &str = r#"
#include <stdio.h>

int main(void) {
    int abweichungen = 0;
#define Q(name, wert, gemeint) \
    do { long long g = (long long)(wert); \
         if (g != (long long)(gemeint)) { abweichungen++; \
             printf("ABWEICHUNG %s: geliefert=%lld gemeint=%lld\n", name, g, (long long)(gemeint)); } \
    } while (0)
    Q("invertiere", invertiere(0x0F0F0F0Fu), 4042322160u);
    Q("passt-ja",   passt_in_16(65535u), 1);
    Q("passt-nein", passt_in_16(65536u), 0);
    Q("min-ja",     ist_kleinster(-2147483647 - 1), 1);
    Q("min-nein",   ist_kleinster(0), 0);
    /* the two spellings of one mask have to be one number */
    Q("zwei-wege",  zwei_wege_eine_maske(240u), 1);
    printf("geprueft=6 abweichungen=%d\n", abweichungen);
    return 0;
}
"#;
