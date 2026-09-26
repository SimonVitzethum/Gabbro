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

/// Per-unit hosted driver generator (lane 246): one wrapper per root, one
/// thread per root, join all, idle root present, lock primitives defined.
/// Declared here (and not in `main.rs`) so the build owns it beside the
/// entry rule: the driver is a build artefact, not a language change.
#[path = "treiber.rs"]
mod treiber;

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

/// **The name the linker looks for, and this is the only place in the tree that spells it.**
///
/// It is **not a Gabbro word**: `emit.rs` does not mangle, so a `pub fn main` in a source IS
/// C's `main` in the artefact. *That is why the entry rule is a build rule and not a language
/// change* -- there is nothing to add to the vocabulary, only something to check.
const EINTRITT: &str = "main";

/// **What the sources declare under the entry name -- where it stands and what shape it has.**
///
/// All three fields are what a refusal has to say: *which* file, whether the linker can see
/// it, and whether C would accept the signature. A bare count would answer "how many" and
/// leave every other question to `cc`.
#[derive(Debug, Clone)]
struct Eintritt {
    datei: String,
    modul: String,
    oeffentlich: bool,
    parameter: usize,
}

/// **What a unit declares for the driver, and what the driver needs.**
///
/// One walk, like the entry: a second parse for the roots would be a second
/// reading of one text, and the two could drift the first time either walk
/// learned to nest differently.
#[derive(Debug, Clone)]
struct TreiberFund {
    /// The member path as written (`hauptA` or `modul::hauptA`).
    gab_pfand: String,
    /// The last segment (`hauptA`): the C name, since C has one namespace
    /// (the same reason the entry rule records the module and does not
    /// compare it).
    kurz: String,
    datei: String,
}

#[derive(Debug, Clone)]
struct TreiberSperre {
    name: String,
    geteilt: bool,
}

#[derive(Debug, Clone)]
struct FunktionsForm {
    parameter: usize,
    datei: String,
    modul: String,
}

/// The modules a unit declares and uses, **and every declaration of the entry name** -- all
/// three out of ONE parse of each file.
///
/// **This is the half the manifest must not carry.** `module` and `use` stand in the files;
/// asking them is a read, writing them down again is a second register (W7). *The entry is
/// the same kind of thing* -- it stands in a source, and the manifest says only whether the
/// unit that holds it is a `program`.
///
/// *A second parse for the entry would be a second reading of one text*, and the two could
/// drift apart the first time either walk learned to nest differently.
fn modulkarte(
    quellen: &[(String, String)],
) -> (
    BTreeSet<String>,
    BTreeSet<String>,
    Vec<Eintritt>,
    Vec<TreiberFund>,
    Vec<TreiberSperre>,
    BTreeMap<String, Vec<FunktionsForm>>,
) {
    let mut deklariert = BTreeSet::new();
    let mut benutzt = BTreeSet::new();
    let mut eintritte = Vec::new();
    let mut wurzeln = Vec::new();
    let mut sperren = Vec::new();
    let mut funktionen: BTreeMap<String, Vec<FunktionsForm>> = BTreeMap::new();
    for (datei, quelle) in quellen {
        let (baum, _) = gabbro_syntax::lies("<scan>", quelle);
        sammle(
            &baum.items,
            "",
            datei,
            &mut deklariert,
            &mut benutzt,
            &mut eintritte,
            &mut wurzeln,
            &mut sperren,
            &mut funktionen,
        );
    }
    (deklariert, benutzt, eintritte, wurzeln, sperren, funktionen)
}

fn sammle(
    items: &[gabbro_syntax::ast::Item],
    pfad: &str,
    datei: &str,
    deklariert: &mut BTreeSet<String>,
    benutzt: &mut BTreeSet<String>,
    eintritte: &mut Vec<Eintritt>,
    wurzeln: &mut Vec<TreiberFund>,
    sperren: &mut Vec<TreiberSperre>,
    funktionen: &mut BTreeMap<String, Vec<FunktionsForm>>,
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
                sammle(
                    &m.items,
                    &voll,
                    datei,
                    deklariert,
                    benutzt,
                    eintritte,
                    wurzeln,
                    sperren,
                    funktionen,
                );
            }
            ItemArt::Use(u) => {
                // `use a::b::C;` names the MODULE `a::b` -- the last part is the item.
                let t = u.pfad.text();
                if let Some(i) = t.rfind("::") {
                    benutzt.insert(t[..i].to_string());
                }
            }
            // **A function of the entry name, wherever it stands.** The module is recorded
            // and not compared: `main` is a C name, and C has one namespace -- a `main` deep
            // in a module is the same symbol as one at the top.
            ItemArt::Funktion(f) if f.name.text == EINTRITT => {
                eintritte.push(Eintritt {
                    datei: datei.to_string(),
                    modul: if pfad.is_empty() {
                        String::from("(top level)")
                    } else {
                        pfad.to_string()
                    },
                    oeffentlich: f.oeffentlich,
                    parameter: f.parameter.len(),
                });
                funktionen
                    .entry(f.name.text.clone())
                    .or_default()
                    .push(FunktionsForm {
                        parameter: f.parameter.len(),
                        datei: datei.to_string(),
                        modul: if pfad.is_empty() {
                            String::from("(top level)")
                        } else {
                            pfad.to_string()
                        },
                    });
            }
            // **Every other function, for the driver.** A `concurrent` member
            // resolves to one of these by short name (C has one namespace, as
            // above); the parameter count decides whether the driver can call
            // it at all.
            ItemArt::Funktion(f) => {
                funktionen
                    .entry(f.name.text.clone())
                    .or_default()
                    .push(FunktionsForm {
                        parameter: f.parameter.len(),
                        datei: datei.to_string(),
                        modul: if pfad.is_empty() {
                            String::from("(top level)")
                        } else {
                            pfad.to_string()
                        },
                    });
            }
            // **The declared starts.** The full path is kept for the refusal
            // text; the short name is what the driver spawns.
            ItemArt::Concurrent(c) => {
                for p in &c.koerper {
                    let kurz = p.teile.last().map(|s| s.text.clone()).unwrap_or_default();
                    wurzeln.push(TreiberFund {
                        gab_pfand: p.text(),
                        kurz,
                        datei: datei.to_string(),
                    });
                }
            }
            // **The locks the driver must define.** The emitter only declares
            // them; a shared (`geteilt`) lock additionally needs the
            // `_nimm_geteilt` / `_gib_geteilt` pair.
            ItemArt::Lock(l) => {
                sperren.push(TreiberSperre {
                    name: l.name.text.clone(),
                    geteilt: l.geteilte_haltezeit.is_some(),
                });
            }
            _ => {}
        }
    }
}

/// **The entry rule -- a `program` names exactly one entry, and an `object` names none.**
///
/// *Measured on 2026-09-01, and the finding is that most of "exactly one" already stood:*
///
/// | case | who refused it BEFORE this rule |
/// |---|---|
/// | one `pub fn main()` in a `program` | nobody -- it builds, links and runs |
/// | two `pub fn main` in one unit | **`N039`**, by name, in Gabbro |
/// | zero `main` in a `program` | `ld`, *"undefined reference to `main`"* |
/// | a private `fn main` | `cc -Werror=main`, *"normally a non-static function"* |
/// | a wrong return type or arity | `cc -Werror=main` |
///
/// **The three lower rows are the rule's whole reason.** They are refusals from foreign
/// tools, in the system's language, one and three tools downstream -- and the first of them
/// is the case a learner hits: *a `program` whose entry is simply not there.* `N039` covers
/// the duplicate only where BOTH are exported; a `pub` one beside a private one is two
/// entries and no `N039`.
///
/// **It costs no word.** `main` is an identifier, not a keyword; the vocabulary marks
/// (221 / 208 / 333) do not move, and `entry` is untouched -- that word declares an
/// *interrupt* stub entered by hardware, with a register footprint, a vector and a dispatch,
/// and it emits a prototype rather than a body. *A hosted entry is a different construct that
/// happens to share an English word.*
///
/// > **And it carries no identifier, which was measured and not assumed.** It read `B001` for
/// > one commit, until two guards said independently that the identifier space belongs to the
/// > CHECKER. `pruefe-kennungen.py` raised the count from 259 to 260 -- a number `TODO.md`
/// > and `README.md` both carry -- and `pruefe-saetze.py` raised the harder objection:
/// > its count of identifiers that owe a statement is a **ratchet** (`messung/PASSREGISTER.md`: 45, *may fall, not
/// > rise*), and `TODO.md` states the rule outright -- **no new refusal code without its
/// > statement.**
/// >
/// > **There is no statement to give it.** A `Satz` says what is true of a program that passed
/// > the checker without a refusal; this rule is about a MANIFEST, which no pass ever sees.
/// > Registering it would have meant a thirteenth pass, and `paesse.rs` holds that list at
/// > twelve against `SPRACHE.md` Teil III §6 -- *the twelve is a claim about the language, not
/// > a container with room in it.*
/// >
/// > So the refusal speaks in sentences, like the four this file already had: a module in two
/// > units, a cycle, an empty unit, a linker that said no. **The convention was already here;
/// > the identifier was the deviation.** *What it costs, named: no `-- erwartet: CODE` poison
/// > probe can name this rule -- and that convention does not reach here anyway, because it
/// > is for `.gab` files the checker reads and these probes are `.bau` manifests.*
fn eintrittsregel(art: Art, eintritte: &[Eintritt]) -> Option<String> {
    let ort = |e: &Eintritt| format!("`{}::{EINTRITT}` in {}", e.modul, e.datei);
    match art {
        Art::Programm => match eintritte.len() {
            0 => Some(format!(
                "this `program` declares no `{EINTRITT}` -- the hosted entry is a \
                 `pub fn {EINTRITT}()` and this unit has none\n\
                 \x20        = without this rule the refusal is `ld`'s (\"undefined \
                 reference to `{EINTRITT}`\"), three tools later and in the system's language"
            )),
            1 => {
                let e = &eintritte[0];
                if !e.oeffentlich {
                    return Some(format!(
                        "{} is not `pub` -- it lowers to a `static` function and the \
                         linker never sees it\n\
                         \x20        = the entry is an EXPORTED name; write `pub fn \
                         {EINTRITT}()`",
                        ort(e)
                    ));
                }
                if e.parameter != 0 {
                    return Some(format!(
                        "{} takes {} parameter(s) -- the hosted entry takes none\n\
                         \x20        = C allows `int {EINTRITT}(void)` and `int \
                         {EINTRITT}(int, char **)`; Gabbro writes the first, and it has no \
                         type for the second",
                        ort(e),
                        e.parameter
                    ));
                }
                None
            }
            n => Some(format!(
                "this `program` declares `{EINTRITT}` {n} times -- {}\n\
                 \x20        = a program has exactly one entry. `N039` catches the case \
                 where both are `pub`; this one also catches a `pub` beside a private",
                eintritte.iter().map(ort).collect::<Vec<_>>().join(", ")
            )),
        },
        // A library that defines the entry collides with the program that links it -- and it
        // collides at the LINKER, over two units, which is exactly the seam nothing else in
        // this build sees.
        Art::Objekt => eintritte.first().map(|e| {
            format!(
                "this `object` declares {} -- a library unit that defines the entry \
                 collides with the `program` that links it\n\
                 \x20        = `{EINTRITT}` belongs to the `program` unit; declare this unit \
                 `program`, or rename the function",
                ort(e)
            )
        }),
    }
}

/// **What the driver step carries per unit: the resolved roots and locks.**
///
/// `None` where the unit declares no `concurrent` set -- then no driver is
/// written at all. A unit whose locks exist but whose roots do not has
/// nothing to start, so it owns no driver either.
#[derive(Debug, Clone)]
struct TreiberPlan {
    wurzeln: Vec<treiber::Wurzel>,
    sperren: Vec<treiber::Sperre>,
}

/// **The driver rule -- every declared root must be exactly one nullary body.**
///
/// *Measured against the checker, and the finding is that almost all of it
/// already stands there:*
///
/// | case | who refused it BEFORE this rule |
/// |---|---|
/// | a member naming no body | **`W003`**, by name, in Gabbro (fail-closed) |
/// | the same body twice (`concurrent { f, f }`) | **`N304`**, by name, in Gabbro, when the routine is not pool-safe -- *a pool-safe routine (lane 245; idle ones too since fix lane F10 retired `N315`) is admitted and gets one thread per occurrence (fix lane F4), see below* |
/// | a member taking parameters | **nobody** -- the emitted root takes them and the driver passes none |
/// | two bodies sharing one C name | **nobody at the build** -- the checker sees modules, C sees one namespace |
///
/// **The last two rows are the rule's whole reason.** Both would otherwise
/// fail at `cc` (an implicit declaration, a duplicate symbol) or -- worse --
/// start the wrong thread. Like the entry rule this one speaks in sentences:
/// the identifier space belongs to the checker (`pruefe-kennungen.py`,
/// `pruefe-saetze.py`), and a manifest-level refusal has no `Satz` to give
/// it, so the reserved codes N441-N445 stay free.
///
/// Unlike the entry rule there is NO visibility check: the driver includes
/// the emitted C (`#include EINHEIT_INCLUDE`, like `laufzeit/start.c`), so a
/// `static` root is nameable -- inclusion, not linkage.
fn treiberregel(
    funde: &[TreiberFund],
    sperren: &[TreiberSperre],
    funktionen: &BTreeMap<String, Vec<FunktionsForm>>,
) -> Result<Option<TreiberPlan>, String> {
    if funde.is_empty() {
        return Ok(None);
    }
    let mut gesehen: BTreeSet<&str> = BTreeSet::new();
    let mut wurzeln = Vec::new();
    for f in funde {
        if !treiber::gueltiger_c_name(&f.kurz) {
            return Err(format!(
                "`concurrent` names `{}` in {} -- it has no C name, so the driver \
                 cannot spawn it (names that reach C are ASCII `[A-Za-z_][A-Za-z0-9_]*`)",
                f.gab_pfand, f.datei
            ));
        }
        // **One thread per OCCURRENCE, not per name** (fix lane F4, review G06
        // F5). A body named twice -- in one block (`concurrent { f, f }`) or
        // across two (`{a, b}` and `{a, c}`) -- is two declared starts: the
        // checker counts it so (`fusswache2::startet`, `N304`), the
        // exporter pushes every occurrence (`lean_g::check_starts`), and since
        // lane 245 a busy pool-safe routine named twice is ACCEPTED. Until this
        // lane the union here gave it ONE thread: the runtime ran fewer starts
        // than assumption (d) names, and the set pin could not see it. Each
        // occurrence is now its own root entry; the generator writes one
        // wrapper per NAME and one `pthread_create` per occurrence, and the pin
        // compares multisets. The validity checks below run once per name.
        if gesehen.insert(f.kurz.as_str()) {
            match funktionen.get(&f.kurz) {
                None => {
                    return Err(format!(
                        "`concurrent` names `{}`, which resolves to no body in this unit -- \
                         without the body the driver would not link (the checker refuses \
                         this first as `W003`; the build refuses it here so a stale driver \
                         is never generated over it)",
                        f.gab_pfand
                    ));
                }
                Some(formen) if formen.len() > 1 => {
                    let orte: Vec<String> =
                        formen.iter().map(|x| format!("{}::{} in {}", x.modul, f.kurz, x.datei)).collect();
                    return Err(format!(
                        "`concurrent` names `{}`, and two bodies share that C name -- {} -- \
                         C has one namespace and the driver could not say which thread runs which",
                        f.gab_pfand,
                        orte.join(", ")
                    ));
                }
                Some(formen) => {
                    let form = &formen[0];
                    if form.parameter != 0 {
                        return Err(format!(
                            "`concurrent` names `{}`, which takes {} parameter(s) -- the driver \
                             passes none (a declared start takes none; its `Env` travels in \
                             `E.starts`, not through `pthread_create`)",
                            f.gab_pfand, form.parameter
                        ));
                    }
                }
            }
        }
        wurzeln.push(treiber::Wurzel {
            c_name: f.kurz.clone(),
            gab_path: f.gab_pfand.clone(),
        });
    }
    // **Deduplicated by name, `geteilt` ORed.** Two `lock` items of one
    // name are legal input to the build (the build refuses nothing the
    // checker accepts); the primitives are per NAME (`<name>_nimm` /
    // `<name>_gib`), so one definition set serves both declarations, and the
    // OR honours every accepted declaration -- a shared pair asked for by
    // either declaration is defined. Contradictory `protects` sets stay the
    // checker's question, not the driver's: the driver defines symbols, it
    // decides no protection.
    let mut sperr_namen: BTreeMap<&str, bool> = BTreeMap::new();
    for s in sperren {
        if !treiber::gueltiger_c_name(&s.name) {
            return Err(format!(
                "lock `{}` has no C name -- its primitives `<name>_nimm` / `<name>_gib` \
                 would not be C functions",
                s.name
            ));
        }
        sperr_namen.entry(s.name.as_str()).and_modify(|g| *g |= s.geteilt).or_insert(s.geteilt);
    }
    let mut sperren_aus: Vec<treiber::Sperre> = sperr_namen
        .into_iter()
        .map(|(name, geteilt)| treiber::Sperre {
            name: name.to_string(),
            geteilt,
        })
        .collect();
    sperren_aus.sort_by(|a, b| a.name.cmp(&b.name));
    Ok(Some(TreiberPlan {
        wurzeln,
        sperren: sperren_aus,
    }))
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
    // **`gabbro build a.gab b.gab …` -- source files, not a manifest** (Opus F, OFFEN O28).
    // Without a manifest there is no compiler line and no output directory, so nothing is
    // compiled; but a program named as several units is not one program until they LINK, and
    // that check needs neither. It runs here, exactly as `gabbro link` runs it, and the line
    // below says what was NOT done.
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
        // Each file is checked against the interfaces of all the OTHERS (what `gabbro abi`
        // writes for them), in the order named -- the manifest build's preamble, with every
        // other file as a unit this one may rest on.
        let schnittstellen: Vec<String> = roh
            .iter()
            .enumerate()
            .map(|(i, q)| {
                let (baum, _) = gabbro_syntax::lies(&namen[i], q);
                gabbro_check::abi::schreibe(&baum, q)
            })
            .collect();
        let texte: Vec<(String, usize)> = roh
            .iter()
            .enumerate()
            .map(|(i, q)| {
                let mut v = String::new();
                for (j, s) in schnittstellen.iter().enumerate() {
                    if j != i {
                        v.push_str(s);
                        v.push('\n');
                    }
                }
                let ab = v.len();
                (format!("{v}{q}"), ab)
            })
            .collect();
        let gut = crate::verbinde_quellen("gabbro build (link)", &namen, &texte);
        println!(
            "gabbro build: {} source file(s), no manifest -- the link check ran; NOTHING was \
             compiled (name the units in a `gabbro.bau` for C)",
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

    // **The graph, computed and not read.** Module -> unit out of the sources; unit -> unit
    // out of the `use` lines through that map.
    let mut quellen_je_einheit: BTreeMap<String, Vec<(String, String)>> = BTreeMap::new();
    let mut modul_zu_einheit: BTreeMap<String, String> = BTreeMap::new();
    let mut benutzt_je_einheit: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    // **Every declaration of the entry name, per unit** -- the one question the manifest can
    // answer and a single file cannot: `object` or `program` (see `eintrittsregel`).
    let mut eintritte_je_einheit: BTreeMap<String, Vec<Eintritt>> = BTreeMap::new();
    // **Every declared start and lock, per unit** -- the driver half of the same
    // question: which threads the unit starts, and which primitives the driver
    // must define (see `treiberregel`).
    let mut treiber_funde_je_einheit: BTreeMap<String, Vec<TreiberFund>> = BTreeMap::new();
    let mut treiber_sperren_je_einheit: BTreeMap<String, Vec<TreiberSperre>> = BTreeMap::new();
    let mut funktionen_je_einheit: BTreeMap<String, BTreeMap<String, Vec<FunktionsForm>>> =
        BTreeMap::new();
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
        let (deklariert, benutzt, eintritte, wurzeln, sperren, funktionen) =
            modulkarte(&quellen);
        eintritte_je_einheit.insert(e.name.clone(), eintritte);
        treiber_funde_je_einheit.insert(e.name.clone(), wurzeln);
        treiber_sperren_je_einheit.insert(e.name.clone(), sperren);
        funktionen_je_einheit.insert(e.name.clone(), funktionen);
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
        // **The dry run carries the entry rule too, and that is the point of a dry run.** The entry
        // is read out of the sources this manifest names -- no C, no compiler, no linker --
        // so a plan that could not link is a plan that says so before anything is written.
        let mut befunde = 0usize;
        for name in &reihenfolge {
            let e = manifest.einheiten.iter().find(|x| &x.name == name).expect("named");
            println!("  unit {name} ({} file(s))", e.dateien.len());
            if let Some(befund) = eintrittsregel(e.art, &eintritte_je_einheit[name]) {
                befunde += 1;
                println!("  REFUSED  {name}: {befund}");
            }
            // **The dry run carries the driver rule too, for the same reason.**
            // The roots are read out of the sources this manifest names, so a
            // plan whose threads could not start says so before anything is
            // written.
            match treiberregel(
                &treiber_funde_je_einheit[name],
                &treiber_sperren_je_einheit[name],
                &funktionen_je_einheit[name],
            ) {
                Ok(None) => {}
                Ok(Some(plan)) => {
                    let wurzeln: Vec<&str> =
                        plan.wurzeln.iter().map(|w| w.c_name.as_str()).collect();
                    let sperren: Vec<&str> =
                        plan.sperren.iter().map(|s| s.name.as_str()).collect();
                    println!(
                        "  driver   {name}: roots [{}] locks [{}] -> {name}.treiber.c",
                        wurzeln.join(", "),
                        sperren.join(", ")
                    );
                }
                Err(befund) => {
                    befunde += 1;
                    println!("  REFUSED  {name} (driver): {befund}");
                }
            }
        }
        println!("  {} computed edge(s) between units", kanten.len());
        for (a, b) in &kanten {
            println!("    {a} -> {b}");
        }
        deckungszeile(&manifest, 0, 0, befunde);
        if befunde > 0 {
            return std::process::ExitCode::from(1);
        }
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
    // The preamble each unit was checked with -- the link below re-reads every unit with it.
    let mut vorspann_je_einheit: BTreeMap<String, String> = BTreeMap::new();
    let mut abdruck_je_einheit: BTreeMap<String, String> = BTreeMap::new();
    for name in &reihenfolge {
        let e = manifest.einheiten.iter().find(|x| &x.name == name).expect("named");
        let quellen = &quellen_je_einheit[name];
        // **The preamble is the interfaces of everything this unit rests on**, deepest first.
        // *That is the edge*: without it `use fach::lies` in another unit is `E009`, and the
        // costs clause on top of it is `K003`. A build that computed the graph and did not
        // carry it was a graph with nothing on it.
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
                // A unit this one rests on was refused. **It is not built on top of the
                // wreck** -- and it is not called "current" either.
                _ => fehlt = Some(u.clone()),
            }
        }
        vorspann_je_einheit.insert(name.clone(), unten.vorspann.clone());
        if let Some(u) = fehlt {
            abgesagt += 1;
            println!("REFUSED  {name}: the unit `{u}` it rests on was not built");
            continue;
        }
        // **The entry rule runs BEFORE the C is written.** A `program` without an entry translates
        // cleanly, compiles cleanly and dies at the linker -- so a rule that ran afterwards
        // would say the same thing `ld` says, only later.
        if let Some(befund) = eintrittsregel(e.art, &eintritte_je_einheit[name]) {
            abgesagt += 1;
            println!("REFUSED  {name}: {befund}");
            continue;
        }
        // **The driver rule runs beside it, for the same reason.** A unit whose
        // roots the driver cannot spawn would emit cleanly, compile cleanly and
        // die at the linker -- or start the wrong threads. No C is written for
        // a unit refused here, and no stale driver is left behind either.
        let treiber_plan = match treiberregel(
            &treiber_funde_je_einheit[name],
            &treiber_sperren_je_einheit[name],
            &funktionen_je_einheit[name],
        ) {
            Ok(plan) => plan,
            Err(befund) => {
                abgesagt += 1;
                println!("REFUSED  {name} (driver): {befund}");
                continue;
            }
        };
        match baue_einheit(&manifest, e, quellen, &unten, bau, pruefbau, treiber_plan.as_ref()) {
            Ergebnis::Gebaut { gabi, abdruck } => {
                gebaut += 1;
                gabi_je_einheit.insert(name.clone(), gabi);
                abdruck_je_einheit.insert(name.clone(), abdruck);
                // The driver travels in the same line: it was written beside
                // the `.c` above, so "built" covers it -- and a missing driver
                // on a concurrent unit would be a lie this line must not tell.
                if treiber_plan.as_ref().is_some_and(|p| !p.wurzeln.is_empty()) {
                    println!("built    {name} (+ {name}.treiber.c)");
                } else {
                    println!("built    {name}");
                }
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
    // alone above, against the interfaces below it -- and alone, a unit sees neither another
    // unit's threads nor a read hidden behind another unit's head. So a build of two or more
    // units is not done until the units LINK: the heads held against the bodies, and the
    // linked program checked whole (`verbund::verbinde_alle`, `gabbro link`). Its C is
    // already written; a refused link makes the build red and says so, and it runs again on
    // every build, "current" units included, because it is a property of the set.
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

/// **Everything a unit gets from the units below it, in one place.**
///
/// The three fields are three uses of one closure and must not drift apart: the interfaces go
/// in front of the source, the fingerprints go into the fingerprint, and the object files go
/// on the linker's command line. *Passing them as three loose arguments is how two of them
/// end up computed from different closures.*
struct Unterbau {
    /// The `.gabi` of everything below, deepest first.
    vorspann: String,
    /// Their fingerprints, in the same order.
    abdruecke: Vec<String>,
    /// Their names, in the same order -- the objects to link.
    namen: Vec<String>,
}

fn baue_einheit(
    manifest: &Manifest,
    e: &Einheit,
    quellen: &[(String, String)],
    unten: &Unterbau,
    bau: gabbro_check::gatter::Bau,
    pruefbau: bool,
    treiber_plan: Option<&TreiberPlan>,
) -> Ergebnis {
    // **The fingerprint covers the content, the compiler line, the build mode -- and the
    // fingerprints of everything this unit rests on.**
    //
    // The last part is what the edge cost. A dependency's `.gabi` sits in the preamble and so
    // in the content, but *a change to a dependency's PRIVATE body does not move its
    // interface* -- and it does move its object file. Without the upstream fingerprints a
    // program would be reported current over a library it no longer contains.
    //
    // The driver needs no fingerprint of its own -- except the generator's
    // version: it is rendered deterministically out of the same sources, so
    // any root added or dropped moves the content above, while a TEMPLATE
    // change with unchanged sources moves nothing. `GENERATOR_KENNUNG` closes
    // that hole: bump it, and every driver-owning unit rebuilds once.
    // A unit without roots owns no driver and carries no version either.
    let treiber_pfad = PathBuf::from(&manifest.ausgabe).join(format!("{}.treiber.c", e.name));
    let treiber_erwartet = treiber_plan.is_some_and(|p| !p.wurzeln.is_empty());
    let mut teile: Vec<&[u8]> = Vec::new();
    if treiber_erwartet {
        teile.push(treiber::GENERATOR_KENNUNG.as_bytes());
    }
    for (d, q) in quellen {
        teile.push(d.as_bytes());
        teile.push(q.as_bytes());
    }
    let compilerzeile = manifest.compiler.join(" ");
    teile.push(compilerzeile.as_bytes());
    let modus: &[u8] = if pruefbau { b"testbuild" } else { b"shipping" };
    teile.push(modus);
    for a in &unten.abdruecke {
        teile.push(a.as_bytes());
    }
    let abdruck = abdruck64(&teile);
    let abdruck_text = format!("{abdruck:016x}");

    let c_pfad = PathBuf::from(&manifest.ausgabe).join(format!("{}.c", e.name));
    let gabi_pfad = PathBuf::from(&manifest.ausgabe).join(format!("{}.gabi", e.name));
    let objekt = PathBuf::from(&manifest.ausgabe).join(format!("{}.o", e.name));
    // **The driver beside the emitted C.** A build artefact like the `.c`:
    // `<unit>.treiber.c` in the shape of `laufzeit/start.c`, generated from
    // the unit's `concurrent` sets -- never edited by hand.
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
    // The driver joins that list: a deleted `<unit>.treiber.c` with a valid
    // record would leave a stale-or-missing pin, so it is checked too.
    if let Ok(alt) = std::fs::read_to_string(&marke) {
        if alt.trim() == format!("{abdruck:016x}")
            && erzeugnis.exists()
            && (!treiber_erwartet || treiber_pfad.exists())
        {
            if let Ok(gabi) = std::fs::read_to_string(&gabi_pfad) {
                return Ergebnis::Aktuell { gabi, abdruck: abdruck_text };
            }
        }
    }

    // **Checked, translated AND described as ONE unit**, out of `uebersetze_einheit` -- the
    // same function `gabbro emit --unit` runs. *Two renderings of one glued parse would be a
    // second register over the same thing*, and so would two parses of it.
    let (c, gabi) = match crate::uebersetze_einheit(&unten.vorspann, quellen, bau, crate::Strom::Aus) {
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
    // **The driver goes out with the C, before the compiler runs.** It is
    // rendered, not checked: the rule above already refused what cannot be
    // spawned. A unit without roots owns no driver, and a driver is never
    // compiled or linked by this build -- it is the artefact the runtime half
    // is run from, beside the `.c` it includes.
    if let Some(plan) = treiber_plan {
        if !plan.wurzeln.is_empty() {
            let treiber_c = treiber::erzeuge(&e.name, &plan.wurzeln, &plan.sperren, None);
            // **The pin, held at the build itself** (fix lane F4): the rendered
            // file must start the declared occurrences, counted -- the writer
            // and the probe checked against each other on every build, not only
            // in the tests.
            let erwartet = treiber::vorkommen(plan.wurzeln.iter().map(|w| w.c_name.as_str()));
            if let Err(err) = treiber::pin_pruefe(&erwartet, &treiber_c) {
                return Ergebnis::Abgesagt(format!("{}: {err}", treiber_pfad.display()));
            }
            if let Err(err) = std::fs::write(&treiber_pfad, &treiber_c) {
                return Ergebnis::Abgesagt(format!("{}: {err}", treiber_pfad.display()));
            }
        }
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
        for u in &unten.namen {
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
                unten.namen.len() + 1,
                e.name,
                unten.namen.len()
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

#[cfg(test)]
mod treiberregel_tests {
    use super::{treiberregel, FunktionsForm, TreiberFund, TreiberSperre};
    use std::collections::BTreeMap;

    fn fund(pfad: &str) -> TreiberFund {
        TreiberFund {
            gab_pfand: pfad.to_string(),
            kurz: pfad.rsplit("::").next().unwrap_or("").to_string(),
            datei: "u.gab".to_string(),
        }
    }

    fn nullary() -> BTreeMap<String, Vec<FunktionsForm>> {
        let mut m = BTreeMap::new();
        for n in ["hauptA", "hauptB"] {
            m.insert(
                n.to_string(),
                vec![FunktionsForm {
                    parameter: 0,
                    datei: "u.gab".to_string(),
                    modul: "m".to_string(),
                }],
            );
        }
        m
    }

    /// **Roots count occurrences, across blocks too** (fix lane F4, review G06 F5).
    /// A member named in two `concurrent` sets is two declared starts -- the checker
    /// counts it so, and the driver must start what the checker judged.
    #[test]
    fn wurzeln_zaehlen_vorkommen() {
        let funde = vec![fund("hauptA"), fund("hauptB"), fund("hauptA")];
        let plan = treiberregel(&funde, &[], &nullary()).expect("occurrences hold").expect("roots");
        let namen: Vec<&str> = plan.wurzeln.iter().map(|w| w.c_name.as_str()).collect();
        assert_eq!(namen, vec!["hauptA", "hauptB", "hauptA"], "one root per occurrence, in order");
    }

    /// **A root with parameters is refused before any C is written.** The
    /// driver passes no arguments, so generating a call would be a wrong
    /// thread, not a loud one.
    #[test]
    fn wurzel_mit_parametern_wird_abgewiesen() {
        let mut f = nullary();
        f.get_mut("hauptB").expect("present")[0].parameter = 1;
        let befund = treiberregel(&[fund("hauptB")], &[], &f).expect_err("must refuse");
        assert!(befund.contains("1 parameter"), "the arity is named:\n{befund}");
    }

    /// **Duplicate lock declarations unite, like roots.** One primitive
    /// set per NAME serves every declaration of it; the OR honours each one.
    /// (`pub` duplicates collide earlier at the checker's `N039` -- "one C
    /// name, one binding" -- so this arm answers the non-`pub` remainder.)
    #[test]
    fn doppelte_sperre_vereinigt_geteilt() {
        let sperren = vec![
            TreiberSperre {
                name: "L".to_string(),
                geteilt: false,
            },
            TreiberSperre {
                name: "L".to_string(),
                geteilt: true,
            },
        ];
        let plan = treiberregel(&[fund("hauptA")], &sperren, &nullary())
            .expect("holds")
            .expect("roots");
        assert_eq!(plan.sperren.len(), 1, "one primitive set per name");
        assert!(plan.sperren[0].geteilt, "either declaration earns the shared pair");
    }

    /// **No roots, no driver.** A unit without a `concurrent` set owns no
    /// artefact and draws no refusal.
    #[test]
    fn ohne_wurzeln_kein_treiber() {
        assert!(treiberregel(&[], &[], &nullary()).expect("holds").is_none());
    }
}
