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
    /// `metal <dir>` (Opus agent J): the bare-metal runtime directory
    /// (`laufzeit/metall`). With it, every unit that owns a bare-metal driver is
    /// also LINKED into `<unit>.metall.elf` by the build.
    pub metall: Option<String>,
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
    let mut metall: Option<String> = None;
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
            "metal" => {
                if worte.len() != 2 {
                    return Err(format!(
                        "{}:{nr}: `metal` takes exactly one path (the bare-metal runtime, \
                         `laufzeit/metall`)",
                        pfad.display()
                    ));
                }
                metall = Some(worte[1].to_string());
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
                    "{}:{nr}: `{andere}` is no manifest word -- `compiler`, `out`, `metal`, \
                     `unit`, or an INDENTED file path",
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
    Ok(Manifest { compiler, ausgabe, einheiten, metall })
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
    /// `masks irqs` -- the bare-metal driver takes it with IF = 0 (Opus agent J).
    maskiert: bool,
}

#[derive(Debug, Clone)]
struct FunktionsForm {
    parameter: usize,
    datei: String,
    modul: String,
    /// `-> T` present: the C function returns a value (an entry's `regs out`).
    liefert: bool,
    /// A `spec fn` writes nothing into C -- no `_verteiler` can point at it.
    spec: bool,
}

/// **An `entry` as the bare-metal driver needs it** (Opus agent J): name,
/// constant vector, whether the LAPIC throws it, the register binding, the
/// dispatch's short name.
#[derive(Debug, Clone)]
struct EintrittFund {
    name: String,
    vektor: Option<u128>,
    via_idt: bool,
    arch: String,
    regs_in: Vec<String>,
    regs_out: Vec<String>,
    dispatch: String,
    datei: String,
}

/// What the bare-metal driver needs beyond roots and locks, out of the same walk.
#[derive(Debug, Clone, Default)]
struct MetallFunde {
    eintritte: Vec<EintrittFund>,
    rcus: Vec<String>,
    /// `accumulates A ... per cpu N`: the emitter's `A_zellen` arrays.
    zellen: Vec<String>,
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
    MetallFunde,
) {
    let mut deklariert = BTreeSet::new();
    let mut benutzt = BTreeSet::new();
    let mut eintritte = Vec::new();
    let mut wurzeln = Vec::new();
    let mut sperren = Vec::new();
    let mut funktionen: BTreeMap<String, Vec<FunktionsForm>> = BTreeMap::new();
    let mut metall = MetallFunde::default();
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
            &mut metall,
        );
    }
    (deklariert, benutzt, eintritte, wurzeln, sperren, funktionen, metall)
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
    metall: &mut MetallFunde,
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
                    metall,
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
                        liefert: f.ergebnis.is_some() && !matches!(f.ergebnis, Some(gabbro_syntax::ast::TypExpr::Never(_))),
                        spec: matches!(f.klasse, Some(gabbro_syntax::ast::FnKlasse::Spec)),
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
                        liefert: f.ergebnis.is_some() && !matches!(f.ergebnis, Some(gabbro_syntax::ast::TypExpr::Never(_))),
                        spec: matches!(f.klasse, Some(gabbro_syntax::ast::FnKlasse::Spec)),
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
                    maskiert: l.maskiert.is_some(),
                });
            }
            // **What the bare-metal driver needs besides** (Opus agent J): the
            // entries it installs in the IDT, the rcu read sides, and the per-cpu
            // cell arrays whose smallest count bounds the cores it brings up.
            ItemArt::Entry(x) => {
                metall.eintritte.push(EintrittFund {
                    name: x.name.text.clone(),
                    vektor: x.vektor.as_ref().and_then(|v| match &v.art {
                        gabbro_syntax::ast::ExprArt::Zahl(n) => Some(*n),
                        _ => None,
                    }),
                    via_idt: x.via.as_ref().is_some_and(|v| v.text == "idt"),
                    arch: x.arch.text.clone(),
                    regs_in: x.regs_in.iter().map(|(_, r)| r.text.clone()).collect(),
                    regs_out: x.regs_out.iter().map(|(_, r)| r.text.clone()).collect(),
                    dispatch: x.dispatch.teile.last().map(|i| i.text.clone()).unwrap_or_default(),
                    datei: datei.to_string(),
                });
            }
            ItemArt::Rcu(r) => metall.rcus.push(r.name.text.clone()),
            ItemArt::Accumulates(a) if a.pro_kern.is_some() => {
                metall.zellen.push(a.name.text.clone());
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
    /// Entries, rcu read sides and per-cpu cells for the bare-metal driver
    /// (Opus agent J). A unit with entries but no roots owns a bare-metal
    /// driver and no hosted one: the hosted side has no IDT to install into.
    zusatz: treiber::MetallZusatz,
}

impl TreiberPlan {
    /// The hosted driver starts threads; without roots there is nothing to start.
    fn hat_gehostet(&self) -> bool {
        !self.wurzeln.is_empty()
    }
    /// The bare-metal driver also installs entries.
    fn hat_metall(&self) -> bool {
        !self.wurzeln.is_empty() || !self.zusatz.eintritte.is_empty()
    }
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
    metall: &MetallFunde,
) -> Result<Option<TreiberPlan>, String> {
    if funde.is_empty() && metall.eintritte.is_empty() {
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
    // `maskiert` is ORed the same way: a mask asked for by either declaration
    // is kept -- the stronger lock, never the weaker.
    let mut sperr_namen: BTreeMap<&str, (bool, bool)> = BTreeMap::new();
    for s in sperren {
        if !treiber::gueltiger_c_name(&s.name) {
            return Err(format!(
                "lock `{}` has no C name -- its primitives `<name>_nimm` / `<name>_gib` \
                 would not be C functions",
                s.name
            ));
        }
        sperr_namen
            .entry(s.name.as_str())
            .and_modify(|(g, m)| {
                *g |= s.geteilt;
                *m |= s.maskiert;
            })
            .or_insert((s.geteilt, s.maskiert));
    }
    let mut sperren_aus: Vec<treiber::Sperre> = sperr_namen
        .into_iter()
        .map(|(name, (geteilt, maskiert))| treiber::Sperre {
            name: name.to_string(),
            geteilt,
            maskiert,
        })
        .collect();
    sperren_aus.sort_by(|a, b| a.name.cmp(&b.name));
    let zusatz = metallregel(metall, funktionen)?;
    Ok(Some(TreiberPlan {
        wurzeln,
        sperren: sperren_aus,
        zusatz,
    }))
}

/// **The bare-metal half of the driver rule** (Opus agent J, OFFEN O32 residue):
/// every `entry` of the unit becomes a stub in the metal IDT, and the rule
/// decides how the stub calls its dispatch -- or says why it cannot.
///
/// | case | answer |
/// |---|---|
/// | the vector is not a literal | REFUSED: the driver cannot name the IDT slot |
/// | an arch other than `x86_64` | REFUSED: the metal runtime is x86_64 only |
/// | the dispatch is not a function of this unit | the stub ends the machine if entered (the emitter wrote no `_verteiler` either) |
/// | `regs in` count != dispatch parameters, or `regs out` != (returns ? 1 : 0) | the stub ends the machine if entered: no honest binding exists (OFFEN O32; the checker does not hold the two against each other) |
/// | otherwise | `regs in` feed the parameters in order, the one `regs out` register receives the result |
///
/// Thrown (EOI) is `via idt` at a vector >= 32: a LAPIC-delivered interrupt.
/// An NMI or a CPU exception (< 32) and an entered entry take no EOI.
fn metallregel(
    metall: &MetallFunde,
    funktionen: &BTreeMap<String, Vec<FunktionsForm>>,
) -> Result<treiber::MetallZusatz, String> {
    let mut eintritte = Vec::new();
    for x in &metall.eintritte {
        if !treiber::gueltiger_c_name(&x.name) {
            return Err(format!("entry `{}` in {} has no C name", x.name, x.datei));
        }
        if x.arch != "x86_64" {
            return Err(format!(
                "entry `{}` in {} is `arch {}` -- the bare-metal runtime is x86_64 only",
                x.name, x.datei, x.arch
            ));
        }
        let Some(vektor) = x.vektor else {
            return Err(format!(
                "entry `{}` in {} has no literal vector -- the bare-metal driver cannot name \
                 its IDT slot (the emitter writes `gabbro_eintritt_{}_VEKTOR` only for a literal)",
                x.name, x.datei, x.name
            ));
        };
        // The runtime's own vectors (timer 0x40, wake 0x41, spurious 0xFF) are refused
        // by `metall_idt_setze` at boot; the build says it first, by name. The
        // exceptions that push a CPU error code (8, 10..14, 17, 21, 29, 30) take the
        // twin stub that drops it since Opus agent L (OFFEN O32 (9)).
        if matches!(vektor, 0x40 | 0x41 | 0xFF) || vektor > 0xFF {
            return Err(format!(
                "entry `{}` in {} sits on vector {vektor} -- the bare-metal runtime keeps \
                 0x40/0x41/0xFF for itself, and a vector is below 0x100",
                x.name, x.datei
            ));
        }
        let ruf = match funktionen.get(&x.dispatch).map(|v| v.as_slice()) {
            Some([f]) if !f.spec => {
                let aus_soll = usize::from(f.liefert);
                // An answer with no out register is dropped (`N561`, Opus agent L): the stub
                // guesses nothing, and the entry changes no register.
                if f.parameter == x.regs_in.len()
                    && (x.regs_out.len() == aus_soll || x.regs_out.is_empty())
                {
                    treiber::EintrittRuf::Bindung {
                        ein: x.regs_in.clone(),
                        aus: x.regs_out.first().cloned(),
                    }
                } else {
                    treiber::EintrittRuf::BindungFalsch
                }
            }
            _ => treiber::EintrittRuf::OhneZiel,
        };
        eintritte.push(treiber::Eintritt {
            name: x.name.clone(),
            vektor,
            geworfen: x.via_idt && vektor >= 32,
            ruf,
        });
    }
    let mut rcus = metall.rcus.clone();
    rcus.sort();
    rcus.dedup();
    let mut zellen = metall.zellen.clone();
    zellen.sort();
    zellen.dedup();
    Ok(treiber::MetallZusatz { eintritte, rcus, zellen })
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
    // **What the bare-metal driver installs besides** (Opus agent J): entries, rcu, cells.
    let mut metall_je_einheit: BTreeMap<String, MetallFunde> = BTreeMap::new();
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
        let (deklariert, benutzt, eintritte, wurzeln, sperren, funktionen, metall) =
            modulkarte(&quellen);
        metall_je_einheit.insert(e.name.clone(), metall);
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
                &metall_je_einheit[name],
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
            &metall_je_einheit[name],
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
                let mut beiwerk: Vec<String> = Vec::new();
                if treiber_plan.as_ref().is_some_and(|p| p.hat_gehostet()) {
                    beiwerk.push(format!("{name}.treiber.c"));
                }
                if treiber_plan.as_ref().is_some_and(|p| p.hat_metall()) {
                    beiwerk.push(format!("{name}.metall.c"));
                    if manifest.metall.is_some() {
                        beiwerk.push(format!("{name}.metall.elf"));
                    }
                }
                if beiwerk.is_empty() {
                    println!("built    {name}");
                } else {
                    println!("built    {name} (+ {})", beiwerk.join(", "));
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
    // The bare-metal twin (Opus agent I): `<unit>.metall.c` beside the hosted
    // driver, from the same plan, under the same generator version.
    let metall_pfad = PathBuf::from(&manifest.ausgabe).join(format!("{}.metall.c", e.name));
    let treiber_erwartet = treiber_plan.is_some_and(|p| p.hat_gehostet());
    let metall_erwartet = treiber_plan.is_some_and(|p| p.hat_metall());
    // **The linked bare-metal image** (Opus agent J): with a `metal <dir>` line the
    // build links `<unit>.metall.elf` itself -- the runtime sources are part of that
    // artefact, so their bytes go into the fingerprint (a changed `kern.c` rebuilds).
    let bild_pfad = PathBuf::from(&manifest.ausgabe).join(format!("{}.metall.elf", e.name));
    let bild_erwartet = metall_erwartet && manifest.metall.is_some();
    let laufzeit_bytes: Vec<Vec<u8>> = match (&manifest.metall, bild_erwartet) {
        (Some(dir), true) => METALL_QUELLEN
            .iter()
            .map(|f| std::fs::read(PathBuf::from(dir).join(f)).unwrap_or_default())
            .collect(),
        _ => Vec::new(),
    };
    let mut teile: Vec<&[u8]> = Vec::new();
    if treiber_erwartet || metall_erwartet {
        teile.push(treiber::GENERATOR_KENNUNG.as_bytes());
    }
    for b in &laufzeit_bytes {
        teile.push(b.as_slice());
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
            && (!metall_erwartet || metall_pfad.exists())
            && (!bild_erwartet || bild_pfad.exists())
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
        let erwartet = treiber::vorkommen(plan.wurzeln.iter().map(|w| w.c_name.as_str()));
        if plan.hat_gehostet() {
            let treiber_c = treiber::erzeuge(&e.name, &plan.wurzeln, &plan.sperren, None);
            // **The pin, held at the build itself** (fix lane F4): the rendered
            // file must start the declared occurrences, counted -- the writer
            // and the probe checked against each other on every build, not only
            // in the tests.
            if let Err(err) = treiber::pin_pruefe(&erwartet, &treiber_c) {
                return Ergebnis::Abgesagt(format!("{}: {err}", treiber_pfad.display()));
            }
            if let Err(err) = std::fs::write(&treiber_pfad, &treiber_c) {
                return Ergebnis::Abgesagt(format!("{}: {err}", treiber_pfad.display()));
            }
        }
        if plan.hat_metall() {
            // **The bare-metal driver, pinned the same way** (Opus agent I):
            // the freestanding twin starts the same multiset of roots through
            // `gabbro_faden_start` (`laufzeit/metall/`), and the build refuses
            // a rendering whose sites do not match the sources. Since Opus agent J
            // it also installs the unit's entries, masks the `masks irqs` locks,
            // defines the rcu read sides and bounds the cores by the per-cpu cells
            // -- and a unit with entries but no roots owns one too.
            let metall_c =
                treiber::erzeuge_metall_voll(&e.name, &plan.wurzeln, &plan.sperren, &plan.zusatz, None);
            if let Err(err) = treiber::metall_pin_pruefe(&erwartet, &metall_c) {
                return Ergebnis::Abgesagt(format!("{}: {err}", metall_pfad.display()));
            }
            if let Err(err) = std::fs::write(&metall_pfad, &metall_c) {
                return Ergebnis::Abgesagt(format!("{}: {err}", metall_pfad.display()));
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

    // **The bare-metal image, linked by the build itself** (Opus agent J, OFFEN O32 residue).
    // With a `metal <dir>` line the unit's `<unit>.metall.c` is compiled freestanding (no
    // hosted header: `-nostdinc` + the compiler's own headers + `<dir>/include`), linked
    // with the runtime (`start.S`, `kern.c`, `arena.c`) under `metall.ld` with NO C library,
    // and handed over as `<unit>.metall.elf` (ELF64) plus `<unit>.metall.boot.elf` (the
    // ELF32 copy a Multiboot1 loader such as `qemu -kernel` takes). An undefined symbol --
    // a foreign body the unit calls and nothing supplies -- is the linker's refusal, and the
    // build's.
    if bild_erwartet {
        if let Some(dir) = &manifest.metall {
            if let Err(grund) = metall_bild_binden(manifest, dir, &e.name) {
                return Ergebnis::Abgesagt(grund);
            }
        }
    }

    // **The record is written LAST.** Written before the compiler ran, it would call a failed
    // build current on the next run.
    if let Err(err) = std::fs::write(&marke, format!("{abdruck_text}\n")) {
        return Ergebnis::Abgesagt(format!("{}: {err}", marke.display()));
    }
    Ergebnis::Gebaut { gabi, abdruck: abdruck_text }
}

/// The runtime files a bare-metal image is linked from, relative to the `metal` directory.
/// Their bytes are part of the image's fingerprint.
const METALL_QUELLEN: [&str; 7] = [
    "start.S",
    "kern.c",
    "arena.c",
    "metall.h",
    "metall.ld",
    "include/math.h",
    "include/string.h",
];

/// The flag word of the bare-metal image -- the same as `instrumente/pruefe-metall.sh`'s:
/// freestanding, no red zone (the timer and the entries push onto the running stack), no
/// hosted header, `-Werror`.
const METALL_FLAGGEN: [&str; 16] = [
    "-std=c11",
    "-O2",
    "-ffreestanding",
    "-fno-builtin",
    "-nostdlib",
    "-nostdinc",
    "-fno-pic",
    "-fno-pie",
    "-mno-red-zone",
    "-mcmodel=small",
    "-fno-stack-protector",
    "-fno-asynchronous-unwind-tables",
    "-fno-tree-loop-distribute-patterns",
    "-Wall",
    "-Wextra",
    "-Werror",
];

/// Compile and link `<unit>.metall.elf` (Opus agent J). Every step is a named refusal.
fn metall_bild_binden(manifest: &Manifest, dir: &str, name: &str) -> Result<(), String> {
    let cc = &manifest.compiler[0];
    let aus = PathBuf::from(&manifest.ausgabe);
    let dir = PathBuf::from(dir);
    let lauf = |mut c: std::process::Command, was: &str| -> Result<(), String> {
        match c.output() {
            Ok(o) if o.status.success() => Ok(()),
            Ok(o) => {
                eprint!("{}", String::from_utf8_lossy(&o.stderr));
                Err(format!("bare-metal image: {was} refused (see above)"))
            }
            Err(err) => Err(format!("bare-metal image: {was} did not run: {err}")),
        }
    };
    // The compiler's OWN header directory: C11's freestanding headers, nothing of a libc.
    let gccinc = match std::process::Command::new(cc).arg("-print-file-name=include").output() {
        Ok(o) if o.status.success() => String::from_utf8_lossy(&o.stdout).trim().to_string(),
        _ => return Err(format!("bare-metal image: `{cc} -print-file-name=include` failed")),
    };
    let flaggen = |c: &mut std::process::Command| {
        c.args(METALL_FLAGGEN);
        c.arg("-isystem").arg(&gccinc);
        c.arg("-isystem").arg(dir.join("include"));
    };
    let obj = |teil: &str| aus.join(format!("{name}.metall.{teil}.o"));
    for (quelle, teil) in [("kern.c", "kern"), ("arena.c", "arena")] {
        let mut c = std::process::Command::new(cc);
        flaggen(&mut c);
        c.arg("-c").arg(dir.join(quelle)).arg("-o").arg(obj(teil));
        lauf(c, quelle)?;
    }
    let mut c = std::process::Command::new(cc);
    c.arg("-fno-pie").arg("-c").arg(dir.join("start.S")).arg("-o").arg(obj("start"));
    lauf(c, "start.S")?;
    let mut c = std::process::Command::new(cc);
    flaggen(&mut c);
    c.arg("-I").arg(&dir).arg("-I").arg(&aus);
    c.arg(format!("-DEINHEIT_INCLUDE=\"{name}.c\""));
    c.arg("-c").arg(aus.join(format!("{name}.metall.c"))).arg("-o").arg(obj("treiber"));
    lauf(c, &format!("{name}.metall.c"))?;
    let bild = aus.join(format!("{name}.metall.elf"));
    let mut c = std::process::Command::new("ld");
    c.args(["-nostdlib", "-static", "-no-pie", "-z", "max-page-size=0x1000", "-T"]);
    c.arg(dir.join("metall.ld")).arg("-o").arg(&bild);
    for teil in ["start", "kern", "arena", "treiber"] {
        c.arg(obj(teil));
    }
    lauf(c, "the link (`ld -nostdlib`: no C library)")?;
    let mut c = std::process::Command::new("objcopy");
    c.args(["-O", "elf32-i386"]).arg(&bild).arg(aus.join(format!("{name}.metall.boot.elf")));
    lauf(c, "objcopy to ELF32 (the Multiboot1 hand-over)")?;
    Ok(())
}

#[cfg(test)]
mod treiberregel_tests {
    use super::{treiberregel, EintrittFund, FunktionsForm, MetallFunde, TreiberFund, TreiberSperre};
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
                    liefert: false,
                    spec: false,
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
        let plan = treiberregel(&funde, &[], &nullary(), &MetallFunde::default()).expect("occurrences hold").expect("roots");
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
        let befund = treiberregel(&[fund("hauptB")], &[], &f, &MetallFunde::default()).expect_err("must refuse");
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
                maskiert: true,
            },
            TreiberSperre {
                name: "L".to_string(),
                geteilt: true,
                maskiert: false,
            },
        ];
        let plan = treiberregel(&[fund("hauptA")], &sperren, &nullary(), &MetallFunde::default())
            .expect("holds")
            .expect("roots");
        assert_eq!(plan.sperren.len(), 1, "one primitive set per name");
        assert!(plan.sperren[0].geteilt, "either declaration earns the shared pair");
        assert!(plan.sperren[0].maskiert, "either declaration earns the mask -- never the weaker lock");
    }

    fn eintritt(name: &str, vektor: Option<u128>, via_idt: bool, ein: &[&str], aus: &[&str], ziel: &str) -> EintrittFund {
        EintrittFund {
            name: name.to_string(),
            vektor,
            via_idt,
            arch: "x86_64".to_string(),
            regs_in: ein.iter().map(|s| s.to_string()).collect(),
            regs_out: aus.iter().map(|s| s.to_string()).collect(),
            dispatch: ziel.to_string(),
            datei: "u.gab".to_string(),
        }
    }

    /// **Entries: the binding, the EOI, and the three refusals** (Opus agent J).
    /// A matching binding feeds the registers in order; a mismatch becomes the
    /// loud stub, never a guessed binding; a missing target the other loud stub;
    /// an NMI takes no EOI; a non-literal vector, a runtime vector and an
    /// error-code exception are refused by name; an entry-only unit owns a
    /// bare-metal driver and no hosted one.
    #[test]
    fn eintritte_im_metalltreiber() {
        use super::treiber::EintrittRuf;
        let mut f = nullary();
        f.insert(
            "sys".to_string(),
            vec![FunktionsForm {
                parameter: 2,
                datei: "u.gab".to_string(),
                modul: "m".to_string(),
                liefert: true,
                spec: false,
            }],
        );
        let metall = MetallFunde {
            eintritte: vec![
                eintritt("syscall", Some(128), false, &["rax", "rdi"], &["rax"], "sys"),
                eintritt("falsch", Some(129), false, &["rax"], &["rax"], "hauptA"),
                eintritt("fremd", Some(130), false, &[], &[], "nirgends"),
                eintritt("nmi", Some(2), true, &[], &[], "hauptA"),
                eintritt("takt", Some(32), true, &[], &[], "hauptA"),
            ],
            rcus: vec![],
            zellen: vec![],
        };
        let plan = treiberregel(&[], &[], &f, &metall).expect("holds").expect("entries own a driver");
        assert!(!plan.hat_gehostet() && plan.hat_metall(), "entry-only: metal driver, no hosted one");
        let r: Vec<(&str, bool, &EintrittRuf)> =
            plan.zusatz.eintritte.iter().map(|e| (e.name.as_str(), e.geworfen, &e.ruf)).collect();
        assert_eq!(
            r[0],
            ("syscall", false, &EintrittRuf::Bindung {
                ein: vec!["rax".to_string(), "rdi".to_string()],
                aus: Some("rax".to_string())
            })
        );
        assert_eq!(r[1], ("falsch", false, &EintrittRuf::BindungFalsch));
        assert_eq!(r[2], ("fremd", false, &EintrittRuf::OhneZiel));
        assert_eq!(r[3].1, false, "an NMI is acknowledged by iretq, not by an EOI");
        assert_eq!(r[4].1, true, "a LAPIC-thrown entry writes the EOI");
        for (vektor, grund) in [(None, "literal"), (Some(0x40), "0x40"), (Some(0x100), "below 0x100")] {
            let m = MetallFunde {
                eintritte: vec![eintritt("x", vektor, true, &[], &[], "hauptA")],
                rcus: vec![],
                zellen: vec![],
            };
            let befund = treiberregel(&[], &[], &f, &m).expect_err("refused");
            assert!(befund.contains(grund), "named: {befund}");
        }
    }

    /// **No roots, no driver.** A unit without a `concurrent` set owns no
    /// artefact and draws no refusal.
    #[test]
    fn ohne_wurzeln_kein_treiber() {
        assert!(treiberregel(&[], &[], &nullary(), &MetallFunde::default()).expect("holds").is_none());
    }
}
