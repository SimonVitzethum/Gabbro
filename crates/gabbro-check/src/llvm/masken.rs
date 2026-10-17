//! **Maskierende Sperren (`lock L … masks irqs`) für LLVM.**
//!
//! `masks irqs` ist eine Aussage über die Umgebung: wer die Sperre nimmt, wird auf seinem
//! Kern von keinem Handler unterbrochen, bis er sie wieder gibt. Der Erzeuger schreibt es
//! als Befehlsfolge (nichts davon ist eine Laufzeit, es ist Inline-Assembler an den zwei
//! Stellen, an denen es sonst nichts gibt):
//!
//! * **Nehmen, VOR der Ticket-Ziehung:** das Zustandswort des Kerns sichern, dann maskieren.
//!   x86_64 `pushfq; popq r; cli`, aarch64 `mrs r, daif; msr daifset, #3`. Das gesicherte
//!   Wort liegt in einer Stapelzelle der Funktion (ein `alloca`), nicht in einem SSA-Wert:
//!   die zustandslose Rekursion (`stackless.rs`) trägt Zellen über Rufgrenzen, und jeder
//!   Pfad aus dem `locks`-Block (`return`, `leave`, `next`, Blockende) lädt sie wieder.
//! * **Geben, NACH der Ticket-Freigabe:** das gesicherte Wort wiederherstellen. x86_64
//!   `pushq r; popfq`, aarch64 `msr daif, r`. **Nie ein bedingungsloses `sti`:** eine
//!   Sperre, die unter schon maskierten Unterbrechungen genommen wurde, gibt sie maskiert
//!   zurück (so wie `raw_spin_lock_irqsave`, das die Sperre in `laufzeit/kmodul` übersetzt).
//!
//! **x86_64 und die Red Zone.** `pushfq` schreibt acht Bytes unter `rsp`; ein Blattbefehl
//! darf dort Daten halten. Die Folge hebt `rsp` darum zuerst um 128 Bytes (`leaq`, ändert
//! keine Flags) und stellt es danach her; ohne ein Funktionsattribut und ohne die Red Zone
//! zu verbieten.
//!
//! **Was das Linux-Benutzerprofil davon ausführen kann: nichts.** `cli`, `popfq` mit IF und
//! `msr daifset` sind privilegiert oder wirkungslos im Benutzermodus (`cli` ohne IOPL ist
//! #GP, also SIGSEGV; aarch64 trifft `msr daif` mit einem Trap nach EL1). Der Erzeuger
//! schreibt die Befehle trotzdem getreu; ein Programm, das eine maskierende Sperre bloß
//! DEKLARIERT, bekommt kein Befehlswort (Nehmen/Geben stehen nur an einem `locks`-Block).
//! Geprüft wird der Text: IR-Test, `llc -filetype=obj` und `objdump -d`.

use super::*;

/// Das Wort der Sperre (`irqs` ist die einzige Maske, die es gibt).
pub(super) fn wort_ist_irqs(w: &Ident) -> bool {
    w.text == "irqs"
}

/// Inline-Assembler zum Sichern und Maskieren (Ausgang: das alte Zustandswort, `i64`).
pub(super) fn sichern_text(ziel: &Ziel) -> &'static str {
    if ziel.name == "x86_64" {
        "leaq -128(%rsp), %rsp\\0A\\09pushfq\\0A\\09popq $0\\0A\\09cli\\0A\\09leaq 128(%rsp), %rsp"
    } else {
        "mrs $0, daif\\0A\\09msr daifset, #3"
    }
}

/// Inline-Assembler zum Wiederherstellen (Eingang: das gesicherte Zustandswort).
pub(super) fn zurueck_text(ziel: &Ziel) -> &'static str {
    if ziel.name == "x86_64" {
        "leaq -128(%rsp), %rsp\\0A\\09pushq $0\\0A\\09popfq\\0A\\09leaq 128(%rsp), %rsp"
    } else {
        "msr daif, $0"
    }
}

/// Zwang-Zeichenfolge des Sicherns (`=r`; `cc` nur, wo der Befehl Flags ändert).
fn sichern_zwang(ziel: &Ziel) -> &'static str {
    if ziel.name == "x86_64" { "=r,~{memory},~{cc}" } else { "=r,~{memory}" }
}

fn zurueck_zwang(ziel: &Ziel) -> &'static str {
    if ziel.name == "x86_64" { "r,~{memory},~{cc}" } else { "r,~{memory}" }
}

/// Eine maskierende Sperre nehmen: Zustand sichern und maskieren (vor dem Ticket).
pub(super) fn maskieren(k: &mut Koerper, name: &str) {
    let ziel = k.s.ziel;
    let zelle = match k.maske_zellen.get(name) {
        Some(z) => z.clone(),
        None => {
            let z = k.alloca("i64");
            k.maske_zellen.insert(name.to_string(), z.clone());
            z
        }
    };
    let alt = k.tmp();
    k.zeile(&format!(
        "{alt} = call i64 asm sideeffect \"{}\", \"{}\"()",
        sichern_text(ziel),
        sichern_zwang(ziel)
    ));
    k.zeile(&format!("store i64 {alt}, ptr {zelle}, align 8"));
}

/// Die Maske der Sperre zurücknehmen: das gesicherte Zustandswort wiederherstellen.
pub(super) fn wiederherstellen(k: &mut Koerper, name: &str) {
    let Some(zelle) = k.maske_zellen.get(name).cloned() else {
        return;
    };
    let ziel = k.s.ziel;
    let alt = k.tmp();
    k.zeile(&format!("{alt} = load i64, ptr {zelle}, align 8"));
    k.zeile(&format!(
        "call void asm sideeffect \"{}\", \"{}\"(i64 {alt})",
        zurueck_text(ziel),
        zurueck_zwang(ziel)
    ));
}
