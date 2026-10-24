//! **One unit, built: checker -> LLVM IR -> `opt -O3` -> `llc -O3` -> `.o` -> `ld.lld`.**
//!
//! A unit is the set of files ONE translation sees: a program's or an object's own files plus
//! the files of every library its `use` lines reach. There is no `cc`, no libc and no startup
//! file: the entry `_start` comes out of the generator around `pub fn main`, and every
//! operating-system call is a `syscall` gate of the program itself.
//!
//! **Incremental by CONTENT, never by timestamp.** The fingerprint covers the files' names and
//! bytes, the target, the build mode and the kind; the artefact's presence is checked, not
//! believed, and the record is written last.

use std::collections::BTreeSet;
use std::path::Path;

use super::sprache::Art;

/// **FNV-1a, 64 bit, by hand.** *It is NOT cryptographic, and that is said rather than left
/// to be assumed*: it guards against an artefact that is accidentally unchanged, not against
/// someone looking for a collision.
pub fn abdruck64(teile: &[&[u8]]) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for t in teile {
        // The length goes in too: `["ab", "c"]` and `["a", "bc"]` are two fingerprints.
        for b in (t.len() as u64).to_le_bytes() {
            h ^= u64::from(b);
            h = h.wrapping_mul(0x0000_0100_0000_01b3);
        }
        for b in *t {
            h ^= u64::from(*b);
            h = h.wrapping_mul(0x0000_0100_0000_01b3);
        }
    }
    h
}

/// The modules some files declare and the modules they use, out of ONE parse of each file.
pub fn modulkarte(quellen: &[(String, String)]) -> (BTreeSet<String>, BTreeSet<String>) {
    let mut deklariert = BTreeSet::new();
    let mut benutzt = BTreeSet::new();
    for (_datei, quelle) in quellen {
        let (baum, _) = gabbro_syntax::lies("<scan>", quelle);
        sammle(&baum.items, "", &mut deklariert, &mut benutzt);
    }
    (deklariert, benutzt)
}

fn sammle(
    items: &[gabbro_syntax::ast::Item],
    pfad: &str,
    deklariert: &mut BTreeSet<String>,
    benutzt: &mut BTreeSet<String>,
) {
    use gabbro_syntax::ast::ItemArt;
    for i in items {
        match &i.art {
            ItemArt::Modul(m) => {
                let voll = if pfad.is_empty() {
                    m.pfad.text()
                } else {
                    format!("{pfad}::{}", m.pfad.text())
                };
                deklariert.insert(voll.clone());
                sammle(&m.items, &voll, deklariert, benutzt);
            }
            ItemArt::Use(u) => {
                // `use a::b::C;` names the MODULE `a::b` -- the last part is the item.
                let t = u.pfad.text();
                if let Some(i) = t.rfind("::") {
                    benutzt.insert(t[..i].to_string());
                }
            }
            _ => {}
        }
    }
}

/// Runs one LLVM tool; a tool that is not installed is a refusal naming it, never a pass.
fn werkzeug(programm: &str, args: &[&str]) -> Result<(), String> {
    match std::process::Command::new(programm).args(args).output() {
        Ok(r) if r.status.success() => Ok(()),
        Ok(r) => Err(format!(
            "`{programm}` failed:\n{}",
            String::from_utf8_lossy(&r.stderr).trim_end()
        )),
        Err(e) => Err(format!(
            "`{programm}` cannot be started ({e}) -- the build needs the LLVM tools `opt`, \
             `llc` and `ld.lld` on PATH; nothing was built"
        )),
    }
}

/// The IR text of a unit declares `_start` exactly when the unit carries the entry `main`.
fn hat_eintritt(ir: &str) -> bool {
    ir.contains("define void @\"_start\"()")
}

pub enum Ergebnis {
    Gebaut,
    Aktuell,
    Abgesagt(String),
}

/// Builds the unit `name` of kind `art` from `quellen` (name, text) into `aus`.
///
/// A `library` is checked alone: IR is written and the entry rule held, no tool runs -- its
/// code reaches a binary only inside the units that use it.
pub fn baue(
    aus: &Path,
    name: &str,
    art: Art,
    quellen: &[(String, String)],
    bau: gabbro_check::gatter::Bau,
    ziel: &'static gabbro_check::llvm::Ziel,
) -> Ergebnis {
    let mut teile: Vec<&[u8]> = Vec::new();
    for (d, q) in quellen {
        teile.push(d.as_bytes());
        teile.push(q.as_bytes());
    }
    teile.push(ziel.triple.as_bytes());
    let modus: &[u8] = match bau {
        gabbro_check::gatter::Bau::Pruefbau => b"testbuild",
        _ => b"shipping",
    };
    teile.push(modus);
    teile.push(art.wort().as_bytes());
    let abdruck = format!("{:016x}", abdruck64(&teile));

    let endung = match art {
        Art::Bibliothek => "lib",
        _ => "unit",
    };
    let ll_pfad = aus.join(format!("{name}.{endung}.ll"));
    let objekt = aus.join(format!("{name}.o"));
    let erzeugnis = match art {
        Art::Programm => aus.join(name),
        Art::Objekt => objekt.clone(),
        Art::Bibliothek => ll_pfad.clone(),
    };
    let marke = aus.join(format!("{name}.{endung}.abdruck"));

    // **The artefact's PRESENCE is checked, not believed.**
    if let Ok(alt) = std::fs::read_to_string(&marke) {
        if alt.trim() == abdruck && erzeugnis.exists() {
            return Ergebnis::Aktuell;
        }
    }

    let ir = match crate::uebersetze_einheit_llvm("", quellen, bau, crate::Strom::Aus, ziel) {
        crate::Einheitsbau::Fertig { c, .. } => c,
        crate::Einheitsbau::Abgesagt(n) => {
            return Ergebnis::Abgesagt(format!("{n} error(s) -- no IR written"));
        }
    };
    // **The entry rule runs on the IR, before any tool does.** A program without `pub fn main`
    // has no `_start` and dies at the linker; an object or a library that carries one would
    // define the entry twice in a program that links it.
    match (art, hat_eintritt(&ir)) {
        (Art::Programm, false) => {
            return Ergebnis::Abgesagt(
                "a `program` names no entry -- it needs a `pub fn main` (the generator writes \
                 `_start` around it)"
                    .to_string(),
            )
        }
        (Art::Objekt | Art::Bibliothek, true) => {
            return Ergebnis::Abgesagt(format!(
                "{} `{}` carries the entry `main` -- the target that holds it is a `program`",
                if art == Art::Objekt { "an" } else { "a" },
                art.wort()
            ))
        }
        _ => {}
    }
    if let Err(err) = std::fs::write(&ll_pfad, &ir) {
        return Ergebnis::Abgesagt(format!("{}: {err}", ll_pfad.display()));
    }
    if art != Art::Bibliothek {
        let bc = aus.join(format!("{name}.bc"));
        let (ll_s, bc_s, o_s) = (
            ll_pfad.display().to_string(),
            bc.display().to_string(),
            objekt.display().to_string(),
        );
        let stufen = werkzeug("opt", &["-O3", &ll_s, "-o", &bc_s]).and_then(|_| {
            werkzeug(
                "llc",
                &["-O3", &format!("-mtriple={}", ziel.triple), "-filetype=obj", &bc_s, "-o", &o_s],
            )
        });
        if let Err(err) = stufen {
            return Ergebnis::Abgesagt(err);
        }
        if art == Art::Programm {
            let ziel_s = erzeugnis.display().to_string();
            if let Err(err) =
                werkzeug("ld.lld", &["-static", "-e", "_start", "-o", &ziel_s, &o_s])
            {
                return Ergebnis::Abgesagt(err);
            }
        }
    }
    // **The record goes out last**: a file on disk is not a claim that anything succeeded.
    if let Err(err) = std::fs::write(&marke, format!("{abdruck}\n")) {
        return Ergebnis::Abgesagt(format!("{}: {err}", marke.display()));
    }
    Ergebnis::Gebaut
}
