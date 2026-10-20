//! **`gabbro build` -- the build, out of a manifest and the `use` edges, through LLVM.**
//!
//! *Since 2026-10-17 LLVM is the only backend.* The C emitter, the generated C drivers, the
//! kernel-module and bare-metal products and the foreign compiler line are gone (tag
//! `archiv/c-emitter-2026-10-17` keeps them). A unit now goes
//!
//! ```text
//!   checker -> LLVM IR (`gabbro llvm`) -> opt -O3 -> llc -O3 -> .o -> ld.lld -static -e _start
//! ```
//!
//! with the LLVM tools found on `PATH` (`opt`, `llc`, `ld.lld`). There is no `cc`, no libc and
//! no startup file: the entry `_start` comes out of the generator, and every operating-system
//! call is a `syscall` gate of the program itself.
//!
//! The two sentences the manifest still turns on (`dokumente/BUILD-SYSTEM.md`):
//!
//! * **The manifest names FILES per unit and nothing else.** A module name is unique only
//!   INSIDE a unit.
//! * **Every edge is COMPUTED, never written.** `module` and `use` stand in the sources;
//!   writing them into the manifest as well would be a second register over the same thing.
//!
//! **Incremental by CONTENT, never by timestamp** (a tool that measures the time instead of the
//! content errs in both directions).
//!
//! **What this build REFUSES by name:** a `module` unit (a Linux kernel module needs the kernel's
//! C build), the `kmod`, `provision`, `note` and `metal` words (kernel and bare-metal images
//! were built from generated C), the `compiler` word (nothing foreign is compiled) and a `.c` or
//! `.h` file in a unit's list. *A refusal that names what was removed is the whole
//! documentation of it.*

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

/// What a unit becomes. **`object` is code the others link, `program` links.**
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Art {
    Objekt,
    Programm,
    /// Parsed only so that it can be refused by name (`module` needed generated C).
    Modul,
}

impl Art {
    fn lies(s: &str) -> Option<Art> {
        match s {
            "object" | "objekt" => Some(Art::Objekt),
            "program" | "programm" => Some(Art::Programm),
            "module" | "modul" => Some(Art::Modul),
            _ => None,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Einheit {
    pub name: String,
    pub art: Art,
    pub dateien: Vec<String>,
}

#[derive(Debug, Clone)]
pub struct Manifest {
    pub ausgabe: String,
    pub einheiten: Vec<Einheit>,
}

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

/// The words a manifest used to carry for the C pipeline. Each is refused by name, with what
/// replaced it.
fn entferntes_wort(wort: &str) -> Option<&'static str> {
    Some(match wort {
        "compiler" => {
            "the build runs the LLVM tools (`opt`, `llc`, `ld.lld`) and compiles no foreign C; \
             delete the line"
        }
        "nolibc" => "every program is libc-free now; delete the line",
        "kmod" | "provision" | "note" => {
            "a Linux kernel module needed the generated C driver, and the C backend was removed \
             on 2026-10-17 (tag `archiv/c-emitter-2026-10-17`)"
        }
        "metal" => {
            "a bare-metal image was linked from generated C (`<unit>.metall.c`), and the C \
             backend was removed on 2026-10-17 (tag `archiv/c-emitter-2026-10-17`)"
        }
        _ => return None,
    })
}

/// Reads the manifest. **Refuses by line number**, because a build that guesses what a
/// manifest meant undoes every pass behind it.
pub fn lies_manifest(pfad: &Path) -> Result<Manifest, String> {
    let text = std::fs::read_to_string(pfad).map_err(|e| format!("{}: {e}", pfad.display()))?;
    let mut ausgabe = String::new();
    let mut einheiten: Vec<Einheit> = Vec::new();
    for (nr, roh) in text.lines().enumerate() {
        let nr = nr + 1;
        let ohne_kommentar = match roh.find("--") {
            Some(i) => &roh[..i],
            None => roh,
        };
        if ohne_kommentar.trim().is_empty() {
            continue;
        }
        // **The indent is the whole syntax**: an indented line is a file of the unit above it.
        let eingerueckt = ohne_kommentar.starts_with(' ') || ohne_kommentar.starts_with('\t');
        let worte: Vec<&str> = ohne_kommentar.split_whitespace().collect();
        if eingerueckt {
            let Some(letzte) = einheiten.last_mut() else {
                return Err(format!("{}:{nr}: a file line before any `unit` line", pfad.display()));
            };
            if worte.len() != 1 {
                return Err(format!(
                    "{}:{nr}: a file line carries exactly one path, {} found",
                    pfad.display(),
                    worte.len()
                ));
            }
            if worte[0].ends_with(".c") || worte[0].ends_with(".h") {
                return Err(format!(
                    "{}:{nr}: `{}` is a C file -- this build compiles no C (the C backend was \
                     removed on 2026-10-17); an operating-system call is a `syscall` gate of \
                     the program",
                    pfad.display(),
                    worte[0]
                ));
            }
            letzte.dateien.push(worte[0].to_string());
            continue;
        }
        if let Some(grund) = entferntes_wort(worte[0]) {
            return Err(format!(
                "{}:{nr}: `{}` is a removed manifest word -- {grund}",
                pfad.display(),
                worte[0]
            ));
        }
        match worte[0] {
            "out" => {
                if worte.len() != 2 {
                    return Err(format!("{}:{nr}: `out` takes exactly one path", pfad.display()));
                }
                ausgabe = worte[1].to_string();
            }
            "unit" => {
                if worte.len() < 3 {
                    return Err(format!(
                        "{}:{nr}: `unit <name> <object|program>` -- {} word(s) found",
                        pfad.display(),
                        worte.len()
                    ));
                }
                let Some(art) = Art::lies(worte[2]) else {
                    return Err(format!(
                        "{}:{nr}: `{}` is none of `object`, `program`",
                        pfad.display(),
                        worte[2]
                    ));
                };
                if art == Art::Modul {
                    return Err(format!(
                        "{}:{nr}: `unit {} module` -- a Linux kernel module needed the \
                         generated C driver and the kernel's C build; the C backend was \
                         removed on 2026-10-17 (tag `archiv/c-emitter-2026-10-17`)",
                        pfad.display(),
                        worte[1]
                    ));
                }
                if worte.len() != 3 {
                    return Err(format!(
                        "{}:{nr}: `unit <name> {}` takes no further word, {} found",
                        pfad.display(),
                        worte[2],
                        worte.len() - 3
                    ));
                }
                if einheiten.iter().any(|e| e.name == worte[1]) {
                    return Err(format!(
                        "{}:{nr}: `{}` is a second unit of that name -- the artefacts would \
                         overwrite one another",
                        pfad.display(),
                        worte[1]
                    ));
                }
                einheiten.push(Einheit {
                    name: worte[1].to_string(),
                    art,
                    dateien: Vec::new(),
                });
            }
            andere => {
                return Err(format!(
                    "{}:{nr}: `{andere}` is no manifest word -- `out`, `unit`, or an INDENTED \
                     file path",
                    pfad.display()
                ));
            }
        }
    }
    if ausgabe.is_empty() {
        return Err(format!("{}: no `out` line", pfad.display()));
    }
    if einheiten.is_empty() {
        return Err(format!("{}: no `unit` line", pfad.display()));
    }
    if let Some(leer) = einheiten.iter().find(|e| e.dateien.is_empty()) {
        return Err(format!(
            "{}: unit `{}` names no file -- an empty unit builds nothing and says it built",
            pfad.display(),
            leer.name
        ));
    }
    Ok(Manifest { ausgabe, einheiten })
}

/// The modules a unit declares and the modules it uses, out of ONE parse of each file.
fn modulkarte(quellen: &[(String, String)]) -> (BTreeSet<String>, BTreeSet<String>) {
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

/// Everything a unit rests on, transitively, in build order (deepest interface first).
fn geschlossene_grundlage(
    name: &str,
    kanten: &[(String, String)],
    reihenfolge: &[String],
) -> Vec<String> {
    let mut erreicht: BTreeSet<String> = BTreeSet::new();
    let mut offen: Vec<String> = vec![name.to_string()];
    while let Some(n) = offen.pop() {
        for (von, nach) in kanten {
            if von == &n && nach != name && erreicht.insert(nach.clone()) {
                offen.push(nach.clone());
            }
        }
    }
    let mut aus: Vec<String> = erreicht.into_iter().collect();
    aus.sort_by_key(|n| reihenfolge.iter().position(|r| r == n).unwrap_or(usize::MAX));
    aus
}

/// The coverage line: "nothing found" and "nothing looked at" look the same otherwise.
fn deckungszeile(manifest: &Manifest, gebaut: usize, aktuell: usize, abgesagt: usize) {
    let genannt: BTreeSet<&String> =
        manifest.einheiten.iter().flat_map(|e| e.dateien.iter()).collect();
    println!(
        "built {gebaut} unit(s), {aktuell} up to date, {abgesagt} refused -- \
         {} file(s) named by this manifest",
        genannt.len()
    );
    let alle = zaehle_gab(Path::new("."));
    let ungesehen = alle.saturating_sub(genannt.len());
    println!(
        "NOT looked at: {ungesehen} `.gab` file(s) in this tree stand in no unit of this \
         manifest ({alle} in the tree)"
    );
    println!(
        "  the manifest is the reach -- a file no `unit` line names is not a file this \
         build passed"
    );
}

fn zaehle_gab(wurzel: &Path) -> usize {
    let mut n = 0;
    let Ok(eintraege) = std::fs::read_dir(wurzel) else {
        return 0;
    };
    for e in eintraege.flatten() {
        let p = e.path();
        let name = p.file_name().and_then(|s| s.to_str()).unwrap_or("");
        if name.starts_with('.') || name == "target" {
            continue;
        }
        if p.is_dir() {
            n += zaehle_gab(&p);
        } else if p.extension().and_then(|s| s.to_str()) == Some("gab") {
            n += 1;
        }
    }
    n
}

/// Units in an order where every used unit comes first. **A cycle is refused by name.**
fn sortiere(manifest: &Manifest, kanten: &[(String, String)]) -> Result<Vec<String>, String> {
    let mut offen: Vec<String> = manifest.einheiten.iter().map(|e| e.name.clone()).collect();
    let mut fertig: Vec<String> = Vec::new();
    while !offen.is_empty() {
        let naechste = offen.iter().position(|n| {
            kanten
                .iter()
                .filter(|(von, _)| von == n)
                .all(|(_, nach)| fertig.iter().any(|f| f == nach) || nach == n)
        });
        match naechste {
            Some(i) => fertig.push(offen.remove(i)),
            None => return Err(offen.join(" -> ")),
        }
    }
    Ok(fertig)
}

enum Ergebnis {
    Gebaut { gabi: String, abdruck: String },
    Aktuell { gabi: String, abdruck: String },
    Abgesagt(String),
}

/// What the unit rests on: interfaces in front of the source, fingerprints into the
/// fingerprint, names for the linker.
struct Unterbau {
    vorspann: String,
    abdruecke: Vec<String>,
    namen: Vec<String>,
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

#[allow(clippy::too_many_arguments)]
fn baue_einheit(
    manifest: &Manifest,
    e: &Einheit,
    quellen: &[(String, String)],
    unten: &Unterbau,
    bau: gabbro_check::gatter::Bau,
    pruefbau: bool,
    ziel: &'static gabbro_check::llvm::Ziel,
) -> Ergebnis {
    // **The fingerprint covers the content, the target, the build mode -- and the fingerprints
    // of everything this unit rests on** (a dependency's private body moves its object and not
    // its interface).
    let mut teile: Vec<&[u8]> = Vec::new();
    for (d, q) in quellen {
        teile.push(d.as_bytes());
        teile.push(q.as_bytes());
    }
    teile.push(ziel.triple.as_bytes());
    let modus: &[u8] = if pruefbau { b"testbuild" } else { b"shipping" };
    teile.push(modus);
    teile.push(match e.art {
        Art::Programm => b"program",
        _ => b"object",
    });
    for a in &unten.abdruecke {
        teile.push(a.as_bytes());
    }
    let abdruck_text = format!("{:016x}", abdruck64(&teile));

    let aus = PathBuf::from(&manifest.ausgabe);
    let ll_pfad = aus.join(format!("{}.ll", e.name));
    let gabi_pfad = aus.join(format!("{}.gabi", e.name));
    let objekt = aus.join(format!("{}.o", e.name));
    let erzeugnis = match e.art {
        Art::Programm => aus.join(&e.name),
        _ => objekt.clone(),
    };
    let marke = aus.join(format!("{}.abdruck", e.name));

    // **The artefact's PRESENCE is checked, not believed**, and so is the interface it hands
    // to its dependents.
    if let Ok(alt) = std::fs::read_to_string(&marke) {
        if alt.trim() == abdruck_text && erzeugnis.exists() {
            if let Ok(gabi) = std::fs::read_to_string(&gabi_pfad) {
                return Ergebnis::Aktuell { gabi, abdruck: abdruck_text };
            }
        }
    }

    let (ir, gabi) = match crate::uebersetze_einheit_llvm(
        &unten.vorspann,
        quellen,
        bau,
        crate::Strom::Aus,
        ziel,
    ) {
        crate::Einheitsbau::Fertig { c, gabi } => (c, gabi),
        crate::Einheitsbau::Abgesagt(n) => {
            return Ergebnis::Abgesagt(format!("{n} error(s) -- no IR written"));
        }
    };
    // **The entry rule runs on the IR, before any tool does.** A `program` without `pub fn
    // main` has no `_start` and dies at the linker; an `object` that carries one would define
    // the entry twice in a program that links it.
    match (e.art, hat_eintritt(&ir)) {
        (Art::Programm, false) => {
            return Ergebnis::Abgesagt(
                "a `program` unit names no entry -- it needs a `pub fn main` (the generator \
                 writes `_start` around it)"
                    .to_string(),
            )
        }
        (Art::Objekt, true) => {
            return Ergebnis::Abgesagt(
                "an `object` unit carries the entry `main` -- the unit that holds it is a \
                 `program`"
                    .to_string(),
            )
        }
        _ => {}
    }
    if let Err(err) = std::fs::write(&ll_pfad, &ir) {
        return Ergebnis::Abgesagt(format!("{}: {err}", ll_pfad.display()));
    }
    if let Err(err) = std::fs::write(&gabi_pfad, &gabi) {
        return Ergebnis::Abgesagt(format!("{}: {err}", gabi_pfad.display()));
    }
    let bc = aus.join(format!("{}.bc", e.name));
    let (ll_s, bc_s, o_s) = (
        ll_pfad.display().to_string(),
        bc.display().to_string(),
        objekt.display().to_string(),
    );
    let stufen = werkzeug("opt", &["-O3", &ll_s, "-o", &bc_s])
        .and_then(|_| werkzeug("llc", &["-O3", &format!("-mtriple={}", ziel.triple), "-filetype=obj", &bc_s, "-o", &o_s]));
    if let Err(err) = stufen {
        return Ergebnis::Abgesagt(err);
    }
    if e.art == Art::Programm {
        let mut objekte: Vec<String> = unten
            .namen
            .iter()
            .map(|n| aus.join(format!("{n}.o")).display().to_string())
            .collect();
        objekte.push(o_s.clone());
        let ziel_s = erzeugnis.display().to_string();
        let mut args: Vec<&str> = vec!["-static", "-e", "_start", "-o", &ziel_s];
        args.extend(objekte.iter().map(|s| s.as_str()));
        if let Err(err) = werkzeug("ld.lld", &args) {
            return Ergebnis::Abgesagt(err);
        }
    }
    // **The record goes out last**: a file on disk is not a claim that anything succeeded.
    if let Err(err) = std::fs::write(&marke, format!("{abdruck_text}\n")) {
        return Ergebnis::Abgesagt(format!("{}: {err}", marke.display()));
    }
    Ergebnis::Gebaut { gabi, abdruck: abdruck_text }
}

pub fn befehl(argumente: &[String]) -> std::process::ExitCode {
    let pruefbau = argumente.iter().any(|a| a == "--testbuild");
    let trocken = argumente.iter().any(|a| a == "--dry-run" || a == "--trocken");
    let ziel_wunsch = argumente
        .iter()
        .find_map(|a| a.strip_prefix("--target="))
        .unwrap_or("x86_64")
        .to_string();
    let Some(ziel) = gabbro_check::llvm::ziel_fuer(&ziel_wunsch) else {
        eprintln!("gabbro build: unknown target `{ziel_wunsch}` -- `x86_64` or `aarch64`");
        return std::process::ExitCode::from(2);
    };
    let pfade: Vec<&String> = argumente.iter().filter(|a| !a.starts_with("--")).collect();
    // **`gabbro build a.gab b.gab …` -- source files, not a manifest** (Opus F, OFFEN O28):
    // the link check only, exactly as `gabbro link` runs it; nothing is compiled.
    if pfade.len() >= 2 && pfade.iter().all(|p| p.ends_with(".gab")) {
        let mut namen = Vec::new();
        let mut roh = Vec::new();
        for p in &pfade {
            match std::fs::read_to_string(p) {
                Ok(q) => {
                    namen.push((*p).clone());
                    roh.push(q);
                }
                Err(e) => {
                    eprintln!("gabbro build: {p}: {e}");
                    return std::process::ExitCode::from(2);
                }
            }
        }
        let texte = crate::vorspaenne_aus_einheiten(&namen, &roh);
        let gut = crate::verbinde_quellen("gabbro build (link)", &namen, &texte);
        println!(
            "gabbro build: {} source file(s), no manifest -- the link check ran; NOTHING was \
             compiled (name the units in a `gabbro.bau` to build)",
            namen.len()
        );
        return if gut {
            std::process::ExitCode::SUCCESS
        } else {
            std::process::ExitCode::from(1)
        };
    }
    let manifestpfad = PathBuf::from(pfade.first().map(|s| s.as_str()).unwrap_or("gabbro.bau"));
    let manifest = match lies_manifest(&manifestpfad) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("gabbro build: {e}");
            return std::process::ExitCode::from(2);
        }
    };
    let bau = if pruefbau {
        gabbro_check::gatter::Bau::Pruefbau
    } else {
        gabbro_check::gatter::Bau::Auslieferung
    };

    // **The graph, computed and not read.**
    let mut quellen_je_einheit: BTreeMap<String, Vec<(String, String)>> = BTreeMap::new();
    let mut modul_zu_einheit: BTreeMap<String, String> = BTreeMap::new();
    let mut benutzt_je_einheit: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for e in &manifest.einheiten {
        let mut quellen = Vec::new();
        for d in &e.dateien {
            match std::fs::read_to_string(d) {
                Ok(q) => quellen.push((d.clone(), q)),
                Err(err) => {
                    eprintln!("gabbro build: {d}: {err}");
                    return std::process::ExitCode::from(2);
                }
            }
        }
        let (deklariert, benutzt) = modulkarte(&quellen);
        for m in deklariert {
            // A module name belongs to at most one unit of a build.
            if let Some(erster) = modul_zu_einheit.get(&m) {
                if erster != &e.name {
                    eprintln!(
                        "gabbro build: module `{m}` is declared in unit `{erster}` AND in \
                         unit `{}` -- a `use` edge onto it would have two targets",
                        e.name
                    );
                    return std::process::ExitCode::from(1);
                }
            }
            modul_zu_einheit.insert(m, e.name.clone());
        }
        benutzt_je_einheit.insert(e.name.clone(), benutzt);
        quellen_je_einheit.insert(e.name.clone(), quellen);
    }
    let mut kanten: Vec<(String, String)> = Vec::new();
    for e in &manifest.einheiten {
        for m in &benutzt_je_einheit[&e.name] {
            if let Some(ziel_e) = modul_zu_einheit.get(m) {
                if ziel_e != &e.name && !kanten.contains(&(e.name.clone(), ziel_e.clone())) {
                    kanten.push((e.name.clone(), ziel_e.clone()));
                }
            }
        }
    }
    // **A unit resting on another unit is refused by name.** The LLVM generator defines every
    // item of a unit and every item the `.gabi` preamble declares, so a second unit that used
    // the first would define its statics twice and fail at the linker (measured 2026-10-17,
    // `duplicate symbol` over `messung/einheit-proben/zwei-einheiten.bau`). Several FILES in ONE
    // unit build; separate compilation across units is not implemented in the LLVM backend.
    if let Some((von, nach)) = kanten.first() {
        eprintln!(
            "gabbro build: unit `{von}` uses unit `{nach}` -- separate compilation across \
             units is not implemented in the LLVM backend (the C backend that did it was \
             removed on 2026-10-17); put the files into ONE unit"
        );
        return std::process::ExitCode::from(1);
    }
    let reihenfolge = match sortiere(&manifest, &kanten) {
        Ok(r) => r,
        Err(zyklus) => {
            eprintln!("gabbro build: the unit graph carries a cycle: {zyklus}");
            return std::process::ExitCode::from(1);
        }
    };

    if trocken {
        println!("manifest {}", manifestpfad.display());
        println!("  out      {}", manifest.ausgabe);
        println!("  target   {}", ziel.triple);
        for name in &reihenfolge {
            let e = manifest.einheiten.iter().find(|x| &x.name == name).expect("named");
            println!("  unit {name} ({} file(s))", e.dateien.len());
        }
        println!("  {} computed edge(s) between units", kanten.len());
        deckungszeile(&manifest, 0, 0, 0);
        return std::process::ExitCode::SUCCESS;
    }

    if let Err(err) = std::fs::create_dir_all(&manifest.ausgabe) {
        eprintln!("gabbro build: {}: {err}", manifest.ausgabe);
        return std::process::ExitCode::from(2);
    }
    let mut gabi_je_einheit: BTreeMap<String, String> = BTreeMap::new();
    let mut abdruck_je_einheit: BTreeMap<String, String> = BTreeMap::new();
    let mut vorspann_je_einheit: BTreeMap<String, String> = BTreeMap::new();
    let (mut gebaut, mut aktuell, mut abgesagt) = (0usize, 0usize, 0usize);
    for name in &reihenfolge {
        let e = manifest.einheiten.iter().find(|x| &x.name == name).expect("named");
        let quellen = &quellen_je_einheit[name];
        // **The preamble is the interfaces of everything this unit rests on**, deepest first.
        let namen = geschlossene_grundlage(name, &kanten, &reihenfolge);
        let mut unten = Unterbau { vorspann: String::new(), abdruecke: Vec::new(), namen };
        let mut fehlt: Option<String> = None;
        for u in &unten.namen {
            match (gabi_je_einheit.get(u), abdruck_je_einheit.get(u)) {
                (Some(g), Some(a)) => {
                    unten.vorspann.push_str(g);
                    unten.vorspann.push('\n');
                    unten.abdruecke.push(a.clone());
                }
                _ => fehlt = Some(u.clone()),
            }
        }
        vorspann_je_einheit.insert(name.clone(), unten.vorspann.clone());
        if let Some(u) = fehlt {
            abgesagt += 1;
            println!("REFUSED  {name}: the unit `{u}` it rests on was not built");
            continue;
        }
        match baue_einheit(&manifest, e, quellen, &unten, bau, pruefbau, ziel) {
            Ergebnis::Gebaut { gabi, abdruck } => {
                gebaut += 1;
                gabi_je_einheit.insert(name.clone(), gabi);
                abdruck_je_einheit.insert(name.clone(), abdruck);
                println!("built    {name}");
            }
            Ergebnis::Aktuell { gabi, abdruck } => {
                aktuell += 1;
                gabi_je_einheit.insert(name.clone(), gabi);
                abdruck_je_einheit.insert(name.clone(), abdruck);
                println!("current  {name}  -- content unchanged, artefact present");
            }
            Ergebnis::Abgesagt(grund) => {
                abgesagt += 1;
                println!("REFUSED  {name}: {grund}");
            }
        }
    }
    // **The link check over the whole program (Opus F, OFFEN O28).** Every unit was checked
    // alone above, against the interfaces below it; two or more units are not done until the
    // units LINK (`verbund::verbinde_alle`, `gabbro link`).
    if abgesagt == 0 && reihenfolge.len() >= 2 {
        let mut namen = Vec::new();
        let mut texte = Vec::new();
        for name in &reihenfolge {
            let v = vorspann_je_einheit.get(name).cloned().unwrap_or_default();
            let t = crate::klebe_einheit(&v, &quellen_je_einheit[name]);
            namen.push(name.clone());
            texte.push((t.ganz, t.vorspann_ende));
        }
        if crate::verbinde_quellen("gabbro build (link)", &namen, &texte) {
            println!("linked   {} unit(s) -- the whole program checked", namen.len());
        } else {
            abgesagt += 1;
            println!("REFUSED  link: the units do not make ONE program (see the refusals above)");
        }
    }
    deckungszeile(&manifest, gebaut, aktuell, abgesagt);
    if abgesagt > 0 {
        std::process::ExitCode::from(1)
    } else {
        std::process::ExitCode::SUCCESS
    }
}
