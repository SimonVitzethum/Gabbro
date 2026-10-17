//! **Portraum (`device … at port`) für LLVM: `in` und `out`, und sonst nichts.**
//!
//! Ein Register eines Portgeräts liegt nicht im Speicher. Seine Adresse ist eine 16-Bit-
//! PORTNUMMER (`basis + versatz`); der Zugriff ist ein Befehl, dessen Breite der Befehl
//! trägt (`inb`/`inw`/`inl`, `outb`/`outw`/`outl`), und dazwischen gibt es nichts, was ein Ort
//! sein könnte. Darum:
//!
//! * `Adresse::port` markiert eine solche Stelle; ihr `addr` ist ein `i16`, kein Zeiger.
//!   Lesen und Schreiben (`senke_expr`, `senke_zuweisung`, Transitionen) gehen durch
//!   [`lesen`] und [`schreiben`]. **Jeder andere Gebrauch** (`+=`, Adresse nehmen, Atomar,
//!   Arena) trifft `adresse_von_ort_mit` mit `port_ok = false` und wird beim Namen
//!   verweigert (`Y102`) — nie als `load` an der Portnummer gelesen (das war der Fehler des
//!   alten C-Erzeugers, `gift/416`).
//! * Der Befehl ist inline `asm sideeffect` mit `~{memory}`: der Übersetzer darf ihn weder
//!   streichen noch mit Speicherzugriffen vertauschen noch verdoppeln.
//! * Die Breiten sind 8/16/32 (`sammle_device` verweigert 64). Die Portnummer läuft in `dx`.
//! * **aarch64 hat keinen Portraum:** `sammle_device` verweigert das Gerät dort beim Namen.
//!
//! **Was geprüft wird und was nicht:** `in`/`out` sind im Benutzermodus ohne IOPL ein `#GP`
//! (SIGSEGV); das Erzeugnis läuft darum nicht unter qemu-user. Geprüft wird der Text (`llc`,
//! `objdump -d` zeigt `inb %dx,%al` usw.), nicht die Wirkung am Gerät.

use super::*;

/// Die Portnummer aus dem Griff (`cur` ist die Zelle des Griffs: `ptr` oder `i64`) plus Versatz.
pub(super) fn portnummer(k: &mut Koerper, ll: &LlTyp, cur: &str, versatz: u64, span: Span) -> Option<String> {
    let zahl = match ll {
        LlTyp::Ptr => {
            let p = k.tmp();
            k.zeile(&format!("{p} = load ptr, ptr {cur}, align 8"));
            let z = k.tmp();
            k.zeile(&format!("{z} = ptrtoint ptr {p} to i64"));
            z
        }
        LlTyp::Int(_) => {
            let z = k.tmp();
            k.zeile(&format!("{z} = load i64, ptr {cur}, align 8"));
            z
        }
        _ => {
            weigere(k.s, "Y102", span, "port device handle of odd type".to_string());
            return None;
        }
    };
    Some(nummer_aus_zahl(k, &zahl, versatz))
}

/// `i64`-Griff + Versatz → `i16`-Portnummer (der Raum endet bei 16 Bit).
pub(super) fn nummer_aus_zahl(k: &mut Koerper, zahl: &str, versatz: u64) -> String {
    let t = k.tmp();
    k.zeile(&format!("{t} = trunc i64 {zahl} to i16"));
    let n = k.tmp();
    k.zeile(&format!("{n} = add i16 {t}, {}", versatz & 0xffff));
    n
}

fn breite_von(ll: &LlTyp) -> u32 {
    ll.breite().unwrap_or(32)
}

/// Ein Register lesen: `in` mit der Breite des Registers.
pub(super) fn lesen(k: &mut Koerper, port: &str, ll: &LlTyp) -> String {
    let b = breite_von(ll);
    let (befehl, reg) = match b {
        8 => ("inb %dx, %al", "al"),
        16 => ("inw %dx, %ax", "ax"),
        _ => ("inl %dx, %eax", "eax"),
    };
    let t = k.tmp();
    k.zeile(&format!(
        "{t} = call i{b} asm sideeffect \"{befehl}\", \"={{{reg}}},{{dx}},~{{memory}}\"(i16 {port})"
    ));
    t
}

/// Ein Register schreiben: `out` mit der Breite des Registers.
pub(super) fn schreiben(k: &mut Koerper, port: &str, ll: &LlTyp, wert: &str) {
    let b = breite_von(ll);
    let (befehl, reg) = match b {
        8 => ("outb %al, %dx", "al"),
        16 => ("outw %ax, %dx", "ax"),
        _ => ("outl %eax, %dx", "eax"),
    };
    k.zeile(&format!(
        "call void asm sideeffect \"{befehl}\", \"{{{reg}}},{{dx}},~{{memory}}\"(i{b} {wert}, i16 {port})"
    ));
}
