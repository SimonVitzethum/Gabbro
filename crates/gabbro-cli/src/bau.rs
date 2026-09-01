//! **`gabbro build` -- the build, out of a manifest and the `use` edges.**
//!
//! The reckoning that decided the shape stands in `dokumente/BAUSYSTEM.md` and was written
//! before this file. The two sentences it turns on:
//!
//! * **The manifest names FILES per unit and nothing else.** Measured over 491 `.gab` files:
//!   only **16** carry the module name their file name suggests, **473** do not, and **14**
//!   module names belong to more than one file -- `module gift` to 122 of them. A convention
//!   "module name equals file name" is refuted, and a GLOBAL module map is impossible. A
//!   module name is unique only INSIDE a unit.
//! * **Every edge is COMPUTED, never written.** `module`, `use`, `arch` and `when` all stand
//!   in the sources. Writing them into the manifest as well would be a second register over
//!   the same thing (W7) -- and the first time a `use` line is added and the manifest line is
//!   not, the build would build out of a mixture. *The same class as `rsync -a` against
//!   `cargo`.*
//!
//! **Incremental by CONTENT, never by timestamp.** `CLAUDE.md` carries two traps of that
//! class, one in each direction: `rsync -a` against `cargo`, where the timestamp LIED, and
//! the bolt after `abnahme.py --voll`, where it told the truth about something that did not
//! matter. *A tool that measures the time instead of the content errs in both directions.*

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

/// What a unit becomes. **`object` compiles, `program` links** -- and the difference is not a
/// language question, which is why it stands in the manifest.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Art {
    Objekt,
    Programm,
}

impl Art {
    fn lies(s: &str) -> Option<Art> {
        match s {
            "object" | "objekt" => Some(Art::Objekt),
            "program" | "programm" => Some(Art::Programm),
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
    /// The foreign compiler and its flags, as written. **A different flag is a different
    /// artefact**, so the whole line goes into the fingerprint.
    pub compiler: Vec<String>,
    pub ausgabe: String,
    pub einheiten: Vec<Einheit>,
}

/// **FNV-1a, 64 bit, by hand.**
///
/// Wider than `abdruck` in `main.rs` on purpose: that one stands in output a human compares,
/// this one in a decision a machine makes.
///
/// > **It is NOT cryptographic, and that is said rather than left to be assumed.** It guards
/// > against an artefact that is accidentally unchanged, not against someone looking for a
/// > collision. Whoever took it for the second would have a promise nobody made.
///
/// By hand and not from a crate, for the reason `abdruck` gives: a dependency taken on for
/// convenience is trust surface, and this folder counts its trust surface.
pub fn abdruck64(teile: &[&[u8]]) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for t in teile {
        // **The length goes in too.** Without it `["ab", "c"]` and `["a", "bc"]` are one
        // fingerprint -- and two different file lists would look like one build.
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

/// Reads the manifest. **Refuses by line number**, because a build that guesses what a
/// manifest meant undoes every pass behind it.
pub fn lies_manifest(pfad: &Path) -> Result<Manifest, String> {
    let text = std::fs::read_to_string(pfad)
        .map_err(|e| format!("{}: {e}", pfad.display()))?;
    let mut compiler: Vec<String> = Vec::new();
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
        // **The indent is the whole syntax**: an indented line is a file of the unit above
        // it. Nothing nests deeper, so nothing has to be counted.
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
            letzte.dateien.push(worte[0].to_string());
            continue;
        }
        match worte[0] {
            "compiler" => {
                if worte.len() < 2 {
                    return Err(format!("{}:{nr}: `compiler` names no program", pfad.display()));
                }
                compiler = worte[1..].iter().map(|s| s.to_string()).collect();
            }
            "out" => {
                if worte.len() != 2 {
                    return Err(format!("{}:{nr}: `out` takes exactly one path", pfad.display()));
                }
                ausgabe = worte[1].to_string();
            }
            "unit" => {
                if worte.len() != 3 {
                    return Err(format!(
                        "{}:{nr}: `unit <name> <object|program>` -- {} word(s) found",
                        pfad.display(),
                        worte.len()
                    ));
                }
                let Some(art) = Art::lies(worte[2]) else {
                    return Err(format!(
                        "{}:{nr}: `{}` is neither `object` nor `program`",
                        pfad.display(),
                        worte[2]
                    ));
                };
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
                    "{}:{nr}: `{andere}` is no manifest word -- `compiler`, `out`, `unit`, \
                     or an INDENTED file path",
                    pfad.display()
                ));
            }
        }
    }
    if compiler.is_empty() {
        return Err(format!("{}: no `compiler` line", pfad.display()));
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
    Ok(Manifest { compiler, ausgabe, einheiten })
}

/// The modules a unit DECLARES, and the modules it USES -- both read out of the sources.
///
/// **This is the half the manifest must not carry.** `module` and `use` stand in the files;
/// asking them is a read, writing them down again is a second register.
fn modulkarte(quellen: &[(String, String)]) -> (BTreeSet<String>, BTreeSet<String>) {
    let mut deklariert = BTreeSet::new();
    let mut benutzt = BTreeSet::new();
    for (_, quelle) in quellen {
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

/// What one unit's build came to. **A built and a current unit both hand on the same two
/// things** -- its interface, so its dependents can be checked against it, and its
/// fingerprint, so a change anywhere upstream reaches them.
enum Ergebnis {
    Gebaut { gabi: String, abdruck: String },
    Aktuell { gabi: String, abdruck: String },
    Abgesagt(String),
}

pub fn befehl(argumente: &[String]) -> std::process::ExitCode {
    let pruefbau = argumente.iter().any(|a| a == "--testbuild");
    let trocken = argumente.iter().any(|a| a == "--dry-run" || a == "--trocken");
    let pfade: Vec<&String> = argumente.iter().filter(|a| !a.starts_with("--")).collect();
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

    // **The graph, computed and not read.** Module -> unit out of the sources; unit -> unit
    // out of the `use` lines through that map.
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
            // **A module name belongs to at most one unit of a build.** Across the whole tree
            // it does not (`module gift` has 122 files); inside one build it must, or a `use`
            // edge would have two targets and the graph would be a guess.
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
            if let Some(ziel) = modul_zu_einheit.get(m) {
                if ziel != &e.name && !kanten.contains(&(e.name.clone(), ziel.clone())) {
                    kanten.push((e.name.clone(), ziel.clone()));
                }
            }
        }
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
        println!("  compiler {}", manifest.compiler.join(" "));
        println!("  out      {}", manifest.ausgabe);
        for name in &reihenfolge {
            let e = manifest.einheiten.iter().find(|x| &x.name == name).expect("named");
            println!("  unit {name} ({} file(s))", e.dateien.len());
        }
        println!("  {} computed edge(s) between units", kanten.len());
        for (a, b) in &kanten {
            println!("    {a} -> {b}");
        }
        deckungszeile(&manifest, 0, 0, 0);
        return std::process::ExitCode::SUCCESS;
    }

    if let Err(e) = std::fs::create_dir_all(&manifest.ausgabe) {
        eprintln!("gabbro build: {}: {e}", manifest.ausgabe);
        return std::process::ExitCode::from(2);
    }

    let mut gebaut = 0usize;
    let mut aktuell = 0usize;
    let mut abgesagt = 0usize;
    // **What a unit hands its dependents: its interface and its fingerprint.**
    let mut gabi_je_einheit: BTreeMap<String, String> = BTreeMap::new();
    let mut abdruck_je_einheit: BTreeMap<String, String> = BTreeMap::new();
    for name in &reihenfolge {
        let e = manifest.einheiten.iter().find(|x| &x.name == name).expect("named");
        let quellen = &quellen_je_einheit[name];
        let unterbau = geschlossene_grundlage(name, &kanten, &reihenfolge);
        // **The preamble is the interfaces of everything this unit rests on**, deepest first.
        // *That is the edge*: without it `use fach::lies` in another unit is `E009`, and the
        // costs clause on top of it is `K003`. A build that computed the graph and did not
        // carry it was a graph with nothing on it.
        let mut vorspann = String::new();
        let mut unterabdruecke: Vec<String> = Vec::new();
        let mut fehlt: Option<String> = None;
        for u in &unterbau {
            match (gabi_je_einheit.get(u), abdruck_je_einheit.get(u)) {
                (Some(g), Some(a)) => {
                    vorspann.push_str(g);
                    vorspann.push('\n');
                    unterabdruecke.push(a.clone());
                }
                // A unit this one rests on was refused. **It is not built on top of the
                // wreck** -- and it is not called "current" either.
                _ => fehlt = Some(u.clone()),
            }
        }
        if let Some(u) = fehlt {
            abgesagt += 1;
            println!("REFUSED  {name}: the unit `{u}` it rests on was not built");
            continue;
        }
        match baue_einheit(&manifest, e, quellen, &vorspann, &unterabdruecke, &unterbau, bau, pruefbau) {
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
    deckungszeile(&manifest, gebaut, aktuell, abgesagt);
    if abgesagt > 0 {
        std::process::ExitCode::from(1)
    } else {
        std::process::ExitCode::SUCCESS
    }
}

/// **Everything a unit rests on, transitively, in build order.**
///
/// The direct edges are not enough, and the reason is the C and not the graph: unit `c` uses
/// `b`, `b` uses `a`, and `b`'s interface names a type `a` declares. A preamble with only
/// `b`'s interface would name `a`'s type and not explain it -- *which is exactly what `N038`
/// refuses inside a unit*, and it would be no better across the boundary.
///
/// The order is the build order, so a deeper interface always stands in front of the one that
/// names it.
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

/// **The coverage line, in the shape `abnahme.py` and `gabbro pruefe` use.**
///
/// *"nothing found" and "nothing looked at" look the same otherwise.* The second line is the
/// one that matters: a build over two files must not read like a build over the tree.
fn deckungszeile(manifest: &Manifest, gebaut: usize, aktuell: usize, abgesagt: usize) {
    let genannt: BTreeSet<&String> =
        manifest.einheiten.iter().flat_map(|e| e.dateien.iter()).collect();
    println!(
        "built {gebaut} unit(s), {aktuell} up to date, {abgesagt} refused -- \
         {} file(s) named by this manifest",
        genannt.len()
    );
    // **Falle 80 in tool form**: a number over a corpus one has looked at while building is
    // not a measurement. So the build says what it did NOT look at, and it counts it.
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

/// Units in an order where every used unit comes first. **A cycle is refused by name**, not
/// broken silently.
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

#[allow(clippy::too_many_arguments)]
fn baue_einheit(
    manifest: &Manifest,
    e: &Einheit,
    quellen: &[(String, String)],
    vorspann: &str,
    unterabdruecke: &[String],
    unterbau: &[String],
    bau: gabbro_check::gatter::Bau,
    pruefbau: bool,
) -> Ergebnis {
    // **The fingerprint covers the content, the compiler line, the build mode -- and the
    // fingerprints of everything this unit rests on.**
    //
    // The last part is what the edge cost. A dependency's `.gabi` sits in the preamble and so
    // in the content, but *a change to a dependency's PRIVATE body does not move its
    // interface* -- and it does move its object file. Without the upstream fingerprints a
    // program would be reported current over a library it no longer contains.
    let mut teile: Vec<&[u8]> = Vec::new();
    for (d, q) in quellen {
        teile.push(d.as_bytes());
        teile.push(q.as_bytes());
    }
    let compilerzeile = manifest.compiler.join(" ");
    teile.push(compilerzeile.as_bytes());
    let modus: &[u8] = if pruefbau { b"testbuild" } else { b"shipping" };
    teile.push(modus);
    for a in unterabdruecke {
        teile.push(a.as_bytes());
    }
    let abdruck = abdruck64(&teile);
    let abdruck_text = format!("{abdruck:016x}");

    let c_pfad = PathBuf::from(&manifest.ausgabe).join(format!("{}.c", e.name));
    let gabi_pfad = PathBuf::from(&manifest.ausgabe).join(format!("{}.gabi", e.name));
    let objekt = PathBuf::from(&manifest.ausgabe).join(format!("{}.o", e.name));
    // **A `program` gets an object of its own too, and then a link.** Compiling and linking
    // in one `cc` call works for one unit and for no chain: the other objects have to stand
    // on the command line, and they are only known once the graph has been walked.
    let erzeugnis = match e.art {
        Art::Objekt => objekt.clone(),
        Art::Programm => PathBuf::from(&manifest.ausgabe).join(&e.name),
    };
    let marke = PathBuf::from(&manifest.ausgabe).join(format!("{}.abdruck", e.name));

    // **The artefact's PRESENCE is checked, not believed.** A deleted artefact with a valid
    // record is exactly the gap this whole section stands against -- and since a unit hands
    // its interface to its dependents, **the interface is an artefact of this build too**: a
    // deleted `.gabi` with a valid record would leave the next unit without its bridge.
    if let Ok(alt) = std::fs::read_to_string(&marke) {
        if alt.trim() == format!("{abdruck:016x}") && erzeugnis.exists() {
            if let Ok(gabi) = std::fs::read_to_string(&gabi_pfad) {
                return Ergebnis::Aktuell { gabi, abdruck: abdruck_text };
            }
        }
    }

    // **Checked, translated AND described as ONE unit**, out of `uebersetze_einheit` -- the
    // same function `gabbro emit --unit` runs. *Two renderings of one glued parse would be a
    // second register over the same thing*, and so would two parses of it.
    let (c, gabi) = match crate::uebersetze_einheit(vorspann, quellen, bau, crate::Strom::Aus) {
        crate::Einheitsbau::Fertig { c, gabi } => (c, gabi),
        crate::Einheitsbau::Abgesagt(n) => {
            return Ergebnis::Abgesagt(format!("{n} error(s) -- no C written"));
        }
    };
    if let Err(err) = std::fs::write(&c_pfad, &c) {
        return Ergebnis::Abgesagt(format!("{}: {err}", c_pfad.display()));
    }
    // The interface goes out before the compiler runs; **the record still goes out last.** A
    // `.gabi` on disk is not a claim that anything succeeded -- the record is the only claim.
    if let Err(err) = std::fs::write(&gabi_pfad, &gabi) {
        return Ergebnis::Abgesagt(format!("{}: {err}", gabi_pfad.display()));
    }

    let mut ruf = std::process::Command::new(&manifest.compiler[0]);
    ruf.args(&manifest.compiler[1..]);
    ruf.arg("-c").arg("-o").arg(&objekt).arg(&c_pfad);
    let aus = match ruf.output() {
        Ok(a) => a,
        Err(err) => return Ergebnis::Abgesagt(format!("{} did not run: {err}", manifest.compiler[0])),
    };
    if !aus.status.success() {
        eprint!("{}", String::from_utf8_lossy(&aus.stderr));
        return Ergebnis::Abgesagt(format!(
            "{} refused the generated C",
            manifest.compiler[0]
        ));
    }

    // **The link -- the only step that sees more than one unit at a time.**
    //
    // *`unit … program` had never run before 2026-09-01:* the branch existed, the example was
    // an `object`, and a program needs a `main`. What it needs besides is exactly the closure
    // computed by `geschlossene_grundlage` -- the objects of everything it rests on.
    if e.art == Art::Programm {
        let mut binde = std::process::Command::new(&manifest.compiler[0]);
        binde.args(&manifest.compiler[1..]);
        binde.arg("-o").arg(&erzeugnis).arg(&objekt);
        for u in unterbau {
            binde.arg(PathBuf::from(&manifest.ausgabe).join(format!("{u}.o")));
        }
        let aus = match binde.output() {
            Ok(a) => a,
            Err(err) => {
                return Ergebnis::Abgesagt(format!("{} did not run: {err}", manifest.compiler[0]))
            }
        };
        if !aus.status.success() {
            eprint!("{}", String::from_utf8_lossy(&aus.stderr));
            return Ergebnis::Abgesagt(format!(
                "the linker refused {} object(s) -- `{}` and the {} it rests on",
                unterbau.len() + 1,
                e.name,
                unterbau.len()
            ));
        }
    }

    // **The record is written LAST.** Written before the compiler ran, it would call a failed
    // build current on the next run.
    if let Err(err) = std::fs::write(&marke, format!("{abdruck_text}\n")) {
        return Ergebnis::Abgesagt(format!("{}: {err}", marke.display()));
    }
    Ergebnis::Gebaut { gabi, abdruck: abdruck_text }
}
