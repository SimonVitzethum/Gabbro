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

/// The arena runtime the hosted driver writes (`treiber::ARENA_LAUFZEIT`), for `gabbro runtime
/// arena`.
pub fn arena_laufzeit() -> &'static str {
    treiber::ARENA_LAUFZEIT
}

/// What a unit becomes. **`object` compiles, `program` links** -- and the difference is not a
/// language question, which is why it stands in the manifest.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Art {
    Objekt,
    Programm,
    /// `module <init> <exit>` (server lane, TODO section 0e K4): the unit becomes a
    /// LOADABLE LINUX KERNEL MODULE, built by `make -C <kernel build dir>` out of the
    /// emitted C, the module runtime (`laufzeit/kmodul/`) and the unit's own foreign C
    /// bodies. The two names are the unit's functions that `module_init` and
    /// `module_exit` call.
    ///
    /// **Why the MANIFEST names them and not the source.** A Linux module is entered by
    /// a call, not by a vector, so `entry … vector V` -- the interrupt form -- is the
    /// wrong word for it, and what the product IS has no representative in the source
    /// (`BAUSYSTEM.md` section 1). The unit stays a unit: the same `.gab` becomes an
    /// object, a program or a module depending on this line alone.
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
    /// For `Art::Modul`: the unit's load and unload functions, as the manifest named
    /// them. Empty for every other art.
    pub modul_init: String,
    pub modul_exit: String,
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
    /// `kmod <runtime dir> <kernel build dir>` (server lane, TODO section 0e K4):
    /// the module runtime (`laufzeit/kmodul`) and the kernel's own build tree
    /// (`/lib/modules/<release>/build`). **Both are named, neither is guessed** --
    /// a path baked into this tree would be a fact about one machine, and a kernel
    /// version baked in would be a fact about one kernel.
    pub kmod: Option<(String, String)>,
    /// `nolibc` (C-free lane, C1): the `program` units of this manifest are Linux x86_64
    /// processes WITHOUT a C library -- linked `-nostdlib -static`, entered by a generated
    /// `_start` that calls `main`, which is `-> never` and ends the process itself. Every operating-system
    /// call the program makes is then its own `syscall` item, and a name it leaves to libc is
    /// the linker's refusal.
    pub ohne_libc: bool,
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
    let mut kmod: Option<(String, String)> = None;
    let mut ohne_libc = false;
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
            "kmod" => {
                if worte.len() != 3 {
                    return Err(format!(
                        "{}:{nr}: `kmod` takes exactly two paths (the module runtime, \
                         `laufzeit/kmodul`, and the kernel build tree, \
                         `/lib/modules/<release>/build`)",
                        pfad.display()
                    ));
                }
                kmod = Some((worte[1].to_string(), worte[2].to_string()));
            }
            "nolibc" => {
                if worte.len() != 1 {
                    return Err(format!("{}:{nr}: `nolibc` takes no argument", pfad.display()));
                }
                ohne_libc = true;
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
                if worte.len() < 3 {
                    return Err(format!(
                        "{}:{nr}: `unit <name> <object|program|module <init> <exit>>` -- {} \
                         word(s) found",
                        pfad.display(),
                        worte.len()
                    ));
                }
                let Some(art) = Art::lies(worte[2]) else {
                    return Err(format!(
                        "{}:{nr}: `{}` is none of `object`, `program`, `module`",
                        pfad.display(),
                        worte[2]
                    ));
                };
                // **A module carries its two entry points on the same line.** Not in an
                // indented line: those are the unit's FILES, and one syntax per thing.
                let (init, exit) = match (art, worte.len()) {
                    (Art::Modul, 5) => (worte[3].to_string(), worte[4].to_string()),
                    (Art::Modul, n) => {
                        return Err(format!(
                            "{}:{nr}: `unit <name> module <init> <exit>` -- {n} word(s) \
                             found. A Linux module is entered by a call, so the two calls \
                             are named here",
                            pfad.display()
                        ))
                    }
                    (_, 3) => (String::new(), String::new()),
                    (_, n) => {
                        return Err(format!(
                            "{}:{nr}: `unit <name> {}` takes no further word, {n} found",
                            pfad.display(),
                            worte[2]
                        ))
                    }
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
                    modul_init: init,
                    modul_exit: exit,
                });
            }
            andere => {
                return Err(format!(
                    "{}:{nr}: `{andere}` is no manifest word -- `compiler`, `out`, `metal`, \
                     `kmod`, `nolibc`, `unit`, or an INDENTED file path",
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
    // **A `module` unit without a `kmod` line, and a `kmod` line without a module unit.**
    // Both halves, because both are a claim nobody keeps: the first asks for an artefact the
    // build cannot make, the second names two paths nothing reads.
    if einheiten.iter().any(|e| e.art == Art::Modul) && kmod.is_none() {
        return Err(format!(
            "{}: a `module` unit stands here and no `kmod <runtime dir> <kernel build dir>` \
             line -- the build has neither the module runtime nor a kernel to build against",
            pfad.display()
        ));
    }
    if kmod.is_some() && !einheiten.iter().any(|e| e.art == Art::Modul) {
        return Err(format!(
            "{}: a `kmod` line stands here and no `unit … module <init> <exit>` -- two paths \
             nothing reads",
            pfad.display()
        ));
    }
    // **`nolibc` is a statement about hosted programs**, and the flag that makes it true of
    // the emitted C is the manifest's own: without `-ffreestanding` the compiler may turn a
    // loop into `memset` or a `printf` into `puts`, and the linker's word would be a name
    // the program never wrote.
    if ohne_libc {
        if kmod.is_some() || metall.is_some() {
            return Err(format!(
                "{}: `nolibc` stands beside a `kmod` or `metal` line -- those products have no \
                 C library either way, and one manifest is one kind of product",
                pfad.display()
            ));
        }
        if !compiler.iter().any(|w| w == "-ffreestanding") {
            return Err(format!(
                "{}: `nolibc` needs `-ffreestanding` on the `compiler` line -- without it the \
                 compiler may call `memset`/`memcpy`/`puts` on its own",
                pfad.display()
            ));
        }
    }
    Ok(Manifest { compiler, ausgabe, einheiten, metall, kmod, ohne_libc })
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
    /// declared `-> never`
    nie: bool,
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
/// **An `atomic` declaration, as the module rule needs it** (server lane, 2026-09-28,
/// TODO section 0e): the name, the module it stands in, the file it stands in -- **and
/// whether its element type is a float** (K6).
///
/// The type entered this record on the day the blanket refusal went. While EVERY atomic was
/// refused, a place to point at was the whole of what the rule needed; now that all but one
/// shape is lowered (`laufzeit/kmodul/include/stdatomic.h`), the rule has to tell the shapes
/// apart, and the one it still refuses is the floating-point one.
#[derive(Debug, Clone)]
struct AtomarFund {
    name: String,
    modul: String,
    datei: String,
    /// `f32`/`f64`, directly or as the element type of an array of them.
    gleitkomma: bool,
}

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
    Vec<AtomarFund>,
    Vec<String>,
) {
    let mut deklariert = BTreeSet::new();
    let mut benutzt = BTreeSet::new();
    let mut eintritte = Vec::new();
    let mut wurzeln = Vec::new();
    let mut sperren = Vec::new();
    let mut funktionen: BTreeMap<String, Vec<FunktionsForm>> = BTreeMap::new();
    let mut metall = MetallFunde::default();
    let mut atomare: Vec<AtomarFund> = Vec::new();
    let mut arenen: Vec<String> = Vec::new();
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
            &mut atomare,
            &mut arenen,
        );
    }
    (deklariert, benutzt, eintritte, wurzeln, sperren, funktionen, metall, atomare, arenen)
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
    atomare: &mut Vec<AtomarFund>,
    arenen: &mut Vec<String>,
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
                    atomare,
                    arenen,
                );
            }
            // **Every `atomic` the unit declares**, for the module rule below. Since K6 that
            // rule refuses only the FLOATING-POINT ones, so the walk carries the element type
            // as the one bit the rule asks of it -- an array of floats is a float atomic, and
            // there is no deeper nesting to look through (`_Atomic` qualifies the element
            // type, `emit.rs::atom_c_deklarator`).
            ItemArt::Atomic(a) => {
                let gleit = |t: &gabbro_syntax::ast::TypExpr| {
                    matches!(t, gabbro_syntax::ast::TypExpr::Float(_))
                };
                atomare.push(AtomarFund {
                    name: a.name.text.clone(),
                    modul: if pfad.is_empty() {
                        String::from("(top level)")
                    } else {
                        pfad.to_string()
                    },
                    datei: datei.to_string(),
                    gleitkomma: match &a.typ {
                        gabbro_syntax::ast::TypExpr::Feld(f) => gleit(&f.element),
                        t => gleit(t),
                    },
                });
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
                    nie: matches!(f.ergebnis, Some(gabbro_syntax::ast::TypExpr::Never(_))),
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
            // **Every `arena` the unit declares** (server lane, 2026-09-28, TODO section 0e
            // K7): the binding rule below asks whether this unit needs the reservation
            // primitives at all, and an arena is the whole of what makes it need them. The
            // NAME is kept and not just a count, because that is what a refusal has to say.
            //
            // *It is not a second register over `GABBRO_ARENEN`*, which the EMITTER writes
            // out of the descriptors it emitted: this walk answers a question about the
            // manifest (does this unit bind what its runtime will call?) and is asked before
            // any C is written. The two would disagree only if the emitter dropped a
            // declared arena, and then the module reserves nothing for it -- a defect of the
            // emitter, which this rule is not the place to catch.
            ItemArt::Arena(a) => arenen.push(a.name.text.clone()),
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
fn eintrittsregel(art: Art, ohne_libc: bool, eintritte: &[Eintritt]) -> Option<String> {
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
                if ohne_libc && !e.nie {
                    return Some(format!(
                        "{} does not end in `-> never` -- under `nolibc` the generated `_start` \
                         only calls the entry and knows no way to end the process\n\
                         \x20        = the program ends itself through its own `-> never` \
                         `syscall` gate; declare `pub fn {EINTRITT}() -> never`",
                        ort(e)
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
        // **A module has no hosted entry either, and for a sharper reason than a library.**
        // `module_init` calls the function the manifest names; a `pub fn haupt()` in a
        // kernel module is a name the loader never calls and the kernel never links --
        // dead weight that looks like an entry point.
        Art::Modul => eintritte.first().map(|e| {
            format!(
                "this `module` declares {} -- a kernel module is entered by the calls the \
                 manifest names (`unit … module <init> <exit>`), never by the hosted entry\n\
                 \x20        = remove it, or declare this unit `program`",
                ort(e)
            )
        }),
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

/// **The module rule: the two calls the kernel makes must be callable** (server lane,
/// 2026-09-28, TODO section 0e K4).
///
/// `module_init` calls `GABBRO_KMOD_INIT()` and reads its answer as the load verdict;
/// `module_exit` calls `GABBRO_KMOD_EXIT()`. Both are ORDINARY functions of the unit, named
/// by the manifest -- so three things have to hold, and each one fails at a different, worse
/// place if it is not checked here:
///
/// | | without this rule |
/// |---|---|
/// | the name exists in the unit | the kernel build says *implicit declaration of function* |
/// | it takes no argument | the module passes nothing and the function reads a register nobody set |
/// | it answers a value | `module_init` has no verdict, and a refused load looks like a good one |
///
/// *The third is the one that matters most:* the load verdict is how a Gabbro module refuses
/// to be loaded (`laufzeit/kmodul/kmodul.c`), and a `void` init would make every load succeed.
///
/// **And one refusal that is not about the two calls at all** (server lane, session 3, and
/// NARROWED in session 5): a unit that declares a FLOATING-POINT `atomic` is no kernel module.
/// Session 3 refused every `atomic` here, because the lowering did not exist and a lowering
/// nobody had related to the goal theorem's atomic rely would have made the wall green and
/// the claim false. Session 5 built the lowering (K6,
/// `bibliothek/linux-kmod/stdatomic.h`, named assumption (M11) in `Zielsatz/Spec.lean`),
/// so what is left of the refusal is the one shape no barrier repairs.
///
/// **AND THE BINDING RULE** (server lane, session 6, TODO section 0e K7): a `module` unit
/// that uses a lock, an arena, a concurrent root or an `atomic` and BINDS NO PRIMITIVE for it
/// is refused here -- see [`bindungsregel`] below, which is where that half stands.
///
/// > **Why none of this carries an `N` code**, and the reason is [`eintrittsregel`]'s and not
/// > a new one: a `Satz` says what is true of a program the CHECKER passed, and every rule in
/// > this file is about a MANIFEST, which no pass ever sees. The refusals speak in sentences.
fn modulregel(
    e: &Einheit,
    funktionen: &BTreeMap<String, Vec<FunktionsForm>>,
    atomare: &[AtomarFund],
    arenen: &[String],
    sperren: &[TreiberSperre],
    wurzeln: &[TreiberFund],
) -> Option<String> {
    if e.art != Art::Modul {
        return None;
    }
    // **A FLOATING-POINT `atomic` has no kernel-module lowering, and this is where that is
    // said.** The other shapes do since K6: `laufzeit/kmodul/include/stdatomic.h` maps the
    // emitter's nine call forms onto `READ_ONCE`/`WRITE_ONCE`, `smp_load_acquire`/
    // `smp_store_release` and the `try_cmpxchg` family, each row at least as strong as the
    // C11 operation it replaces, and the relation between the two models is the named
    // assumption (M11) of `Zielsatz/Spec.lean`.
    //
    // A float is the one shape no barrier repairs: kernel code may not touch the FPU without
    // `kernel_fpu_begin`/`_end`, and nothing declares them -- a lowering that quietly used
    // SSE registers would corrupt whatever userspace task happened to be scheduled. The
    // header asserts the same thing (`GABBRO_KMOD_ATOMAR_TYP`, a `_Generic` that costs no
    // load), because that is what answers a hand-written `Kbuild`; here it arrives before a
    // byte of C is written and names the DECLARATION instead of a macro.
    if let Some(a) = atomare.iter().find(|a| a.gleitkomma) {
        return Some(format!(
            "this `module` declares the floating-point atomic `{}` ({} in {}) -- a \
             floating-point `atomic` has no kernel-module lowering\n\
             \x20        = kernel code may not use the FPU without `kernel_fpu_begin`/`_end`, \
             which nothing declares, and a lowering that used SSE registers would corrupt the \
             userspace task that happens to be scheduled\n\
             \x20        = the integer and `bool` shapes ARE lowered since 2026-09-28 \
             (`laufzeit/kmodul/include/stdatomic.h`, named assumption (M11) of \
             `Zielsatz/Spec.lean`); this is the remainder, not the rule\n\
             \x20        = without this rule the refusal is \
             `laufzeit/kmodul/include/stdatomic.h`'s, in a `make` log",
            a.name, a.modul, a.datei
        ));
    }
    for (rolle, name) in [("init", &e.modul_init), ("exit", &e.modul_exit)] {
        let Some(formen) = funktionen.get(name.as_str()) else {
            return Some(format!(
                "the manifest names `{name}` as this module's {rolle} function, and the unit \
                 declares no `{name}`\n\
                 \x20        = without this rule the refusal is the kernel build's, in a \
                 `make` log"
            ));
        };
        for f in formen {
            if f.parameter != 0 {
                return Some(format!(
                    "`{name}` ({rolle}) takes {} parameter(s) -- `module_{rolle}` passes none",
                    f.parameter
                ));
            }
            if !f.liefert {
                return Some(format!(
                    "`{name}` ({rolle}) answers nothing -- a module's {rolle} function \
                     carries the load verdict (0 loads, anything else refuses the load), and \
                     a `void` one would make every load succeed"
                ));
            }
        }
    }
    if e.modul_init == e.modul_exit {
        return Some(format!(
            "`{}` is named as BOTH the init and the exit function -- loading and unloading \
             are not the same call",
            e.modul_init
        ));
    }
    bindungsregel(e, funktionen, atomare, arenen, sperren, wurzeln)
}

/// **What a HOSTED unit must bind, per thing it uses** (server lane, 2026-09-28, TODO
/// section 0e K8).
///
/// The module rule's twin, and deliberately the same shape. Simon drew the line for the
/// runtimes on 2026-09-28: *"an die Hardware ist OK, OS nicht, das muss selbst gemacht
/// werden"* -- no operating-system call hard-wired in ANY runtime, hardware access on bare
/// metal allowed. `laufzeit/arena_dyn.c` was the first file to move
/// (`laufzeit/bindung.h` declares what it calls and defines nothing), so this is the first
/// thing a hosted unit has to bind.
///
/// | what the unit uses | what the hosted runtime will call | where |
/// |---|---|---|
/// | an `arena` | `gabbro_os_reserve` (answers a region), `gabbro_os_commit` (a region's page and a length), `gabbro_os_seitengroesse` | the arena runtime the generated driver writes (template `arena.dyn`; `laufzeit/arena_dyn.c` until 2026-09-30), at load and at every `grow` |
/// | a `concurrent` root | `gabbro_os_faden_start`, `_warte` | the generated driver's `main` |
/// | a `concurrent` root AND a `lock` | `gabbro_os_nachgeben` | the driver's ticket lock (template `sperre.ticket`), every 64 spins of a waiter |
/// | any of those | `gabbro_os_melden`, `gabbro_os_ende` | the fail-stops of both files |
///
/// **Why the lock row hangs off the ROOTS and not off the lock**, and it is the one shape
/// this rule got wrong on its first run: a unit with a `lock` and no declared start owns NO
/// hosted driver (`TreiberPlan::hat_gehostet`), so nothing in its build calls a lock
/// primitive at all -- the emitter DECLARES `L_nimm`/`L_gib` and whoever links the unit
/// supplies them. *Measured: `programmlogik/beispiel`, an `object` with one `lock` and no
/// `concurrent` set, was refused for a call nothing makes.* The demand follows the file that
/// is written, which is the driver.
///
/// **Why the report channel has no line of its own.** It belongs to everything the runtime
/// does, and a unit with neither an arena nor a driver has a runtime beside it that calls
/// nothing -- so demanding it there would be the same mistake one row up. *The demand grows
/// with the measurement* (`MARKE_OSSYM` in `instrumente/pruefe-os-bindung.sh`), which is the
/// only order in which a refusal and a number can stay the same statement. Until the driver
/// moved it stood under the `arena` row alone, because the arena was the only part of the
/// hosted runtime that had.
///
/// **A `geteilt` lock asks for nothing extra, and a `masks irqs` one neither.** The driver
/// defines `L_nimm_geteilt` over the same pair (the emitter asks for a second NAME, not a
/// second primitive), and hosted POSIX has no interrupts to mask -- the word is the
/// bare-metal driver's business (`treiber.rs::Sperre::maskiert`). The module rule has a
/// masked pair because a kernel module can keep that promise and must.
///
/// **Bare metal is exempt, and that is K8's own sentence.** A unit built for a `metal` target
/// gets `laufzeit/metall/arena.c`, whose reservation is a slice of one static region and
/// whose commit is a budget -- no operating system underneath, nothing to bind, and the
/// machine access it does have (port I/O, `hlt`, MSRs) is allowed.
///
/// A unit may of course write its own bodies instead of the library's -- the check is that
/// the DECLARATION stands, with its arity and its result, not that a particular file was
/// named.
fn bindungsregel_gehostet(
    e: &Einheit,
    metall_ziel: bool,
    funktionen: &BTreeMap<String, Vec<FunktionsForm>>,
    arenen: &[String],
    sperren: &[TreiberSperre],
    wurzeln: &[TreiberFund],
) -> Option<String> {
    if e.art == Art::Modul || metall_ziel {
        return None;
    }
    // **Does this unit own a hosted driver?** Exactly the question `TreiberPlan::hat_gehostet`
    // answers, and the same answer: a driver starts threads, so a unit without a declared
    // start has none written for it and nothing of it is linked.
    let treiber = !wurzeln.is_empty();
    if arenen.is_empty() && !treiber {
        return None;
    }
    // **The report channel, once, for whichever of the two brought us here.** Both files
    // that fail-stop say so through it, so the sentence names what the unit actually has
    // rather than a part of the runtime it may not link.
    let stopp = match (!arenen.is_empty(), treiber) {
        (true, true) => "this unit declares an `arena` and runs under the generated driver, \
                         and both fail-stop in words the program owns",
        (true, false) => "this unit declares an `arena`, and the runtime fail-stops a refused \
                          reservation in words the program owns",
        _ => "this unit runs under the generated driver, which reports a start or a join it \
              could not make in words the program owns",
    };
    let mut gefordert = vec![
        BindungsZeile { name: "gabbro_os_melden", parameter: 3, liefert: false, weil: stopp },
        BindungsZeile { name: "gabbro_os_ende", parameter: 1, liefert: false, weil: stopp },
    ];
    if !arenen.is_empty() {
        let weil = "this unit declares an `arena`, whose storage the runtime asks the program for";
        for (name, parameter, liefert) in [
            ("gabbro_os_reserve", 1, true),
            ("gabbro_os_commit", 2, true),
            ("gabbro_os_seitengroesse", 0, true),
        ] {
            gefordert.push(BindungsZeile { name, parameter, liefert, weil });
        }
    }
    if treiber && !sperren.is_empty() {
        // Since 2026-09-30 (C-free lane) the lock is the generated ticket lock (template
        // `sperre.ticket`); what it asks of the program is only the hand-over in its spin.
        let weil = "this unit declares a `lock` and a `concurrent` set, and the generated \
                    driver's ticket lock hands its core over while it waits";
        gefordert.push(BindungsZeile { name: "gabbro_os_nachgeben", parameter: 0, liefert: false, weil });
    }
    if treiber {
        let weil = "this unit declares a `concurrent` set, which the generated driver runs as \
                    threads";
        gefordert.push(BindungsZeile {
            name: "gabbro_os_faden_start",
            parameter: 2,
            liefert: true,
            weil,
        });
        gefordert.push(BindungsZeile {
            name: "gabbro_os_faden_warte",
            parameter: 1,
            liefert: true,
            weil,
        });
    }
    bindung_pruefe(&gefordert, funktionen, &GEHOSTET_ZIEL)
}

/// **One row of the binding: a name the module runtime calls, and what makes it call it**
/// (server lane, 2026-09-28, TODO section 0e K7).
///
/// The table below is held against `laufzeit/kmodul/bindung.h` by the comment in each row and
/// by the C compiler at every module build -- a name here that the runtime does not call
/// would be ceremony, and a call the runtime makes without a row here would be a kernel
/// function nobody declared, which is the whole thing K7 closes.
struct BindungsZeile {
    name: &'static str,
    parameter: usize,
    liefert: bool,
    /// What makes the unit need it, in the words of the refusal.
    weil: &'static str,
}

/// **What a `module` unit must bind, per thing it uses** (server lane, 2026-09-28, TODO
/// section 0e K7).
///
/// SIMON'S RULE: *"API calls are always user-made"* -- and until this rule existed the module
/// RUNTIME was the exception. `laufzeit/kmodul/` called twelve kernel functions no program had
/// declared (`dokumente/OFFEN.md` O35, measured by the stage `symbole_pruefe` of
/// `instrumente/pruefe-kernelmodul.sh`). They are declarations now
/// (`laufzeit/kmodul/bindung.h`) and the PROGRAM defines them --
/// `bibliothek/linux-kmod/linux-kmod.gab` plus its `.c` is the binding a program may take off
/// the shelf.
///
/// **A MEASUREMENT ALONE WOULD NOT HAVE CLOSED IT, and this rule is the other half.** The
/// symbol stage can say "the runtime pulls no kernel name" over a `.ko` that was BUILT; what
/// it cannot say is anything about the unit whose binding is missing, because that unit does
/// not link at all -- `modpost` says *"gabbro_kern_reserve undefined"*, in a `make` log, about
/// the runtime's name rather than about the program's omission. *A refusal that arrives as a
/// linker error over a name the user never wrote is a refusal the user cannot act on.*
///
/// | what the unit uses | what the runtime will call | where |
/// |---|---|---|
/// | anything (it is a module) | `gabbro_kern_melden` | every load refusal: printing is a kernel call |
/// | an `arena` | `gabbro_kern_reserve`, `_freigeben`, `_vorrat` | `arena.c` |
/// | any `lock` | `gabbro_kern_sperre_init`, `gabbro_kern_kernnummer` | `sperre.h`, at load and at every acquire |
/// | a PLAIN `lock` | `gabbro_kern_sperre_nimm`, `_gib` | `sperre.h` |
/// | a `masks irqs` `lock` | `gabbro_kern_sperre_nimm_maskiert`, `_gib_maskiert` | `sperre.h` |
/// | a `concurrent` root | `gabbro_kern_faden_start`, `_warte` | `kmodul.c` |
/// | an `atomic` | a `stdatomic.h` among the unit's files | the emitted prelude's `#include` |
///
/// **The last row is not a function and is here anyway**, because it is the same question one
/// step lower: the memory model of an `atomic` is macros (`READ_ONCE`, `smp_load_acquire`,
/// `try_cmpxchg`) and leaves no symbol, so the symbol stage cannot see it at all. The table
/// itself is the program's (`bibliothek/linux-kmod/stdatomic.h`); the runtime's own
/// `<stdatomic.h>` refuses `_Atomic` outright, so an unbound module fails to compile rather
/// than compiling into unordered accesses. *This rule is the door before that one.*
///
/// A unit may of course write its own bodies instead of the library's -- the check is that the
/// DECLARATION stands, with its arity and its result, not that a particular file was named.
/// **Where a binding rule points when it refuses** (server lane, 2026-09-28, TODO section 0e
/// K7 and K8).
///
/// Two targets carry the same rule today -- a Linux kernel module (K7) and a hosted program
/// (K8) -- and they differ in four words: which runtime calls the name, which header holds
/// the declaration, which library supplies the usual bodies, and whose error the user would
/// have got instead. **The rule itself is one function**, because a second copy of the shape
/// check is exactly the drift this folder writes its rules against (`W7`): a target whose
/// arity question was written twice would answer it twice, and one of the two would age.
struct BindungsZiel {
    /// How the refusal names the unit. A module is a `module` by its manifest word; the
    /// hosted rule holds for an `object` as much as for a `program` -- what it is about is
    /// the RUNTIME the unit will be linked against -- so it says "hosted unit" and not a
    /// manifest word it might contradict.
    art: &'static str,
    /// The runtime that calls these names, in the words of the refusal.
    laufzeit: &'static str,
    /// The header the declaration is held against.
    kopf: &'static str,
    /// The two manifest lines a program may take off the shelf instead of writing its own.
    bibliothek: &'static str,
    /// Whose message the user would have got without this rule -- and it is always about the
    /// RUNTIME's name, never about the program's omission.
    sonst: &'static str,
}

const MODUL_ZIEL: BindungsZiel = BindungsZiel {
    art: "`module`",
    laufzeit: "the module runtime",
    kopf: "laufzeit/kmodul/bindung.h",
    bibliothek: "`bibliothek/linux-kmod/linux-kmod.gab` and `bibliothek/linux-kmod/linux-kmod.c`",
    sonst: "`modpost`'s -- \"{} undefined\", in a `make` log",
};

const GEHOSTET_ZIEL: BindungsZiel = BindungsZiel {
    art: "hosted unit",
    laufzeit: "the hosted runtime",
    kopf: "laufzeit/bindung.h",
    bibliothek: "`bibliothek/linux/linux.gab` and `bibliothek/linux/linux.c`",
    sonst: "the linker's -- \"undefined reference to `{}`\"",
};

/// **Is every row of the binding declared, with its arity and its result?** (server lane,
/// 2026-09-28.)
///
/// **The SHAPE, not only the name.** C has no mangling, so a declaration of the right name and
/// the wrong arity links and then reads a register nobody set. The same three questions the
/// module's init/exit rule asks, for the same reason.
fn bindung_pruefe(
    gefordert: &[BindungsZeile],
    funktionen: &BTreeMap<String, Vec<FunktionsForm>>,
    ziel: &BindungsZiel,
) -> Option<String> {
    for z in gefordert {
        let Some(formen) = funktionen.get(z.name) else {
            return Some(format!(
                "this {} binds no `{}` -- {}\n\
                 \x20        = {} calls it (`{}`) and defines it nowhere: every operating-system \
                 call a Gabbro program makes is the PROGRAM's\n\
                 \x20        = the usual one is two lines in the manifest: {}\n\
                 \x20        = without this rule the refusal is {}, about a name the program \
                 never wrote",
                ziel.art,
                z.name,
                z.weil,
                ziel.laufzeit,
                ziel.kopf,
                ziel.bibliothek,
                ziel.sonst.replace("{}", z.name)
            ));
        };
        for f in formen {
            if f.parameter != z.parameter {
                return Some(format!(
                    "`{}` is bound with {} parameter(s) and the runtime calls it with {} \
                     ({} in {})\n\
                     \x20        = the declaration is held against `{}`; C has no mangling, so \
                     a wrong arity links and then reads a register nobody set",
                    z.name, f.parameter, z.parameter, f.modul, f.datei, ziel.kopf
                ));
            }
            if f.liefert != z.liefert {
                return Some(format!(
                    "`{}` is bound {} a result and the runtime {} one ({} in {})\n\
                     \x20        = see `{}` for the line it is held against",
                    z.name,
                    if f.liefert { "with" } else { "without" },
                    if z.liefert { "reads" } else { "reads none of" },
                    f.modul,
                    f.datei,
                    ziel.kopf
                ));
            }
        }
    }
    None
}

fn bindungsregel(
    e: &Einheit,
    funktionen: &BTreeMap<String, Vec<FunktionsForm>>,
    atomare: &[AtomarFund],
    arenen: &[String],
    sperren: &[TreiberSperre],
    wurzeln: &[TreiberFund],
) -> Option<String> {
    const MELDEN: BindungsZeile = BindungsZeile {
        name: "gabbro_kern_melden",
        parameter: 3,
        liefert: false,
        weil: "this is a `module`, and the runtime refuses a load in words the program owns",
    };
    let mut gefordert: Vec<BindungsZeile> = vec![MELDEN];
    if !arenen.is_empty() {
        let weil = "this unit declares an `arena`, whose storage the runtime asks the \
                    program for";
        for (name, parameter, liefert) in [
            ("gabbro_kern_reserve", 1, true),
            ("gabbro_kern_freigeben", 1, false),
            ("gabbro_kern_vorrat", 0, true),
        ] {
            gefordert.push(BindungsZeile { name, parameter, liefert, weil });
        }
    }
    if !sperren.is_empty() {
        let weil = "this unit declares a `lock`, whose primitive the emitter only declares";
        for (name, parameter, liefert) in [
            ("gabbro_kern_sperre_init", 1, false),
            ("gabbro_kern_kernnummer", 0, true),
        ] {
            gefordert.push(BindungsZeile { name, parameter, liefert, weil });
        }
        if sperren.iter().any(|s| !s.maskiert) {
            let weil = "this unit declares a `lock` without `masks irqs`";
            for name in ["gabbro_kern_sperre_nimm", "gabbro_kern_sperre_gib"] {
                gefordert.push(BindungsZeile { name, parameter: 1, liefert: false, weil });
            }
        }
        if sperren.iter().any(|s| s.maskiert) {
            let weil = "this unit declares a `masks irqs` `lock`, and the masking is the \
                        binding's (`kern_bindung_maskiert`)";
            for name in [
                "gabbro_kern_sperre_nimm_maskiert",
                "gabbro_kern_sperre_gib_maskiert",
            ] {
                gefordert.push(BindungsZeile { name, parameter: 1, liefert: false, weil });
            }
        }
    }
    if !wurzeln.is_empty() {
        let weil = "this unit declares a `concurrent` set, which the module runtime runs as \
                    kernel threads";
        gefordert.push(BindungsZeile {
            name: "gabbro_kern_faden_start",
            parameter: 2,
            liefert: true,
            weil,
        });
        gefordert.push(BindungsZeile {
            name: "gabbro_kern_faden_warte",
            parameter: 1,
            liefert: false,
            weil,
        });
    }
    if let Some(befund) = bindung_pruefe(&gefordert, funktionen, &MODUL_ZIEL) {
        return Some(befund);
    }
    // **The memory model of an `atomic`, which is a FILE and not a function.** See the table
    // in this function's own documentation for why it is checked here and not by the symbol
    // stage: macros leave no symbol.
    if let Some(a) = atomare.first() {
        if !e.dateien.iter().any(|d| {
            Path::new(d).file_name().is_some_and(|f| f == "stdatomic.h")
        }) {
            return Some(format!(
                "this `module` declares the atomic `{}` ({} in {}) and names no \
                 `stdatomic.h` -- the memory model of an `atomic` is the program's\n\
                 \x20        = the kernel has a memory model of its own and is built \
                 `-nostdinc`; `bibliothek/linux-kmod/stdatomic.h` maps the emitter's nine C11 \
                 call forms onto it (named assumption (M11) of `Zielsatz/Spec.lean`), and a \
                 different kernel gets a different table\n\
                 \x20        = add that file to this unit, or write your own\n\
                 \x20        = without this rule the refusal is the kernel build's, over an \
                 undefined `_Atomic` (`laufzeit/kmodul/include/stdatomic.h`)",
                a.name, a.modul, a.datei
            ));
        }
    }
    None
}

/// **What the driver step carries per unit: the resolved roots and locks.**
///
/// `None` where the unit declares no `concurrent` set -- then no driver is
/// written at all. A unit whose locks exist but whose roots do not has
/// nothing to start, so it owns no driver either.
#[derive(Debug, Clone)]
struct TreiberPlan {
    /// **The art decides WHICH driver the roots become** (server lane, 2026-09-28, TODO
    /// section 0e K6). A root is a root in all three worlds; what differs is who starts it
    /// -- a pthread in `laufzeit/start.c`, a core on bare metal, a `kthread` in
    /// `laufzeit/kmodul/kmodul.c`. Without this field a `module` unit with a `concurrent`
    /// set had a hosted pthread driver written beside its `.ko`: a file for a world it is
    /// not in.
    art: Art,
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
        self.art != Art::Modul && !self.wurzeln.is_empty()
    }
    /// The bare-metal driver also installs entries.
    fn hat_metall(&self) -> bool {
        self.art != Art::Modul && (!self.wurzeln.is_empty() || !self.zusatz.eintritte.is_empty())
    }
    /// **The module's roots become kernel threads**, and the list travels as a generated
    /// `wurzeln.h` beside `sperren.h` -- the driver `kmodul.c` is not generated, so what is
    /// unit-specific reaches it as a macro list out of THIS walk and no second one (`W7`).
    fn hat_kmod_faeden(&self) -> bool {
        self.art == Art::Modul && !self.wurzeln.is_empty()
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
///
/// **`art` decides whether the BARE-METAL half of the rule speaks** (server lane,
/// 2026-09-28, TODO section 0e K3). A `module` unit's artefact is a `.ko`: it has
/// no IDT, no boot stub and no metal driver, so [`metallregel`]'s refusals -- all
/// of which say *"the bare-metal driver cannot …"* -- are about an artefact this
/// unit never gets. *Measured that day:* a module unit declaring
/// `entry takt_uhr via irq` (a Linux hardirq callback, which owns no vector the
/// program could name) was REFUSED for having no literal IDT slot. **A refusal
/// whose reason names an artefact nobody asked for is a refusal in the wrong
/// place.** What still holds the declaration for a module unit is the checker
/// (`H102` over the dispatch's call graph, and the entry's own `N` codes); what
/// binds the stub to the kernel is the program's own C, and nothing in the build
/// can check that binding -- the module target has no twin of the metal `N561`
/// (OFFEN O19).
fn treiberregel(
    funde: &[TreiberFund],
    sperren: &[TreiberSperre],
    funktionen: &BTreeMap<String, Vec<FunktionsForm>>,
    metall: &MetallFunde,
    art: Art,
) -> Result<Option<TreiberPlan>, String> {
    let metall_gewollt = art != Art::Modul;
    // **A unit with LOCKS and no roots gets a plan too** (server lane, 2026-09-28, TODO
    // section 0e K3). It owns no driver -- `hat_gehostet`/`hat_metall` are both false and
    // nothing is written -- but a kernel module needs its lock list whether or not it starts
    // a thread, and the list is this function's. *Measured that day: the list came out empty
    // over a unit with one `masks irqs` lock, because the plan itself was `None`, and the
    // module did not link.*
    if funde.is_empty()
        && sperren.is_empty()
        && (!metall_gewollt || metall.eintritte.is_empty())
    {
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
    let zusatz = if metall_gewollt {
        metallregel(metall, funktionen)?
    } else {
        treiber::MetallZusatz::default()
    };
    Ok(Some(TreiberPlan {
        art,
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
    let trocken = argumente.iter().any(|a| a == "--dry-run" || a == "--trocken" || a == "--c-liste");
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
        // other file as a unit this one may rest on. `gabbro link` without `--with` runs the
        // SAME derivation, out of the same function.
        let texte = crate::vorspaenne_aus_einheiten(&namen, &roh);
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
    let mut atomare_je_einheit: BTreeMap<String, Vec<AtomarFund>> = BTreeMap::new();
    // **Every `arena` a unit declares** (server lane, TODO section 0e K7): the binding rule
    // asks whether the unit needs the reservation primitives of `laufzeit/kmodul/bindung.h`.
    let mut arenen_je_einheit: BTreeMap<String, Vec<String>> = BTreeMap::new();
    // **A unit's own C bodies** (server lane, TODO section 0e K4): the `.c` files a
    // `module` unit names beside its `.gab` sources. They are the bodies of the `extern fn`
    // items the PROGRAM declares -- the whole of its kernel API, written by whoever wrote
    // the declaration (`TODO.md` section -1). They are not Gabbro and are never parsed as
    // Gabbro; they are compiled into the module beside the emitted C.
    let mut fremde_je_einheit: BTreeMap<String, Vec<String>> = BTreeMap::new();
    // **A module unit's own HEADERS** (server lane, TODO section 0e K7): the `.h` files it
    // names, copied into the module's include directory in place of the runtime's shims.
    let mut koepfe_je_einheit: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for e in &manifest.einheiten {
        let mut quellen = Vec::new();
        let mut fremde: Vec<String> = Vec::new();
        let mut koepfe: Vec<String> = Vec::new();
        for d in &e.dateien {
            if d.ends_with(".c") {
                // **Until K8 only a `module` carried one**, and the refusal here said so
                // rather than compiling it into nothing: *"a hosted `program` with a foreign
                // body is a build-system gap of its own -- naming it here would be a promise
                // this build does not keep."*
                //
                // K8 is where the promise had to be kept (server lane, 2026-09-28). The
                // hosted runtime's operating-system calls became declarations the PROGRAM
                // defines (`laufzeit/bindung.h`), and the bodies that define them are an
                // ordinary `.c` file of the unit -- `bibliothek/linux/linux.c` for a program
                // that takes the usual POSIX ones off the shelf. A binding the build refused
                // to compile would have been a library nobody could use.
                //
                // So a non-module unit's `.c` files are compiled beside its own object with
                // the manifest's compiler line, and a `program` links them
                // (`baue_einheit`). *What is still refused is a `.h`* -- that is the module
                // include mechanism, and it has no hosted meaning.
                if !Path::new(d).is_file() {
                    eprintln!("gabbro build: {d}: no such file");
                    return std::process::ExitCode::from(2);
                }
                fremde.push(d.clone());
                continue;
            }
            // **A `.h` file of a module unit is a header the PROGRAM supplies** (server
            // lane, 2026-09-28, TODO section 0e K7). It is copied into the module's include
            // directory AFTER the runtime's own shims and therefore in place of one of the
            // same name -- which is the mechanism by which a program binds the memory model
            // of an `atomic`: `laufzeit/kmodul/include/stdatomic.h` refuses `_Atomic`, and
            // `bibliothek/linux-kmod/stdatomic.h` is the table that replaces it.
            //
            // *Why a file line and not a new manifest word.* The file list is already the
            // place a unit says which files are its own, and the `.c` branch above is the
            // same idea one file type over. A `kmodinclude <dir>` line would be a second
            // syntax for "this file belongs to this unit" (`W7`).
            if d.ends_with(".h") {
                if e.art != Art::Modul {
                    eprintln!(
                        "gabbro build: unit `{}` names the header `{d}` and is not a \
                         `module` -- a program-supplied header is carried into a kernel \
                         module today and nowhere else",
                        e.name
                    );
                    return std::process::ExitCode::from(1);
                }
                if !Path::new(d).is_file() {
                    eprintln!("gabbro build: {d}: no such file");
                    return std::process::ExitCode::from(2);
                }
                koepfe.push(d.clone());
                continue;
            }
            match std::fs::read_to_string(d) {
                Ok(q) => quellen.push((d.clone(), q)),
                Err(err) => {
                    eprintln!("gabbro build: {d}: {err}");
                    return std::process::ExitCode::from(2);
                }
            }
        }
        if quellen.is_empty() {
            eprintln!(
                "gabbro build: unit `{}` names no `.gab` file -- a unit of C alone is not a \
                 Gabbro unit",
                e.name
            );
            return std::process::ExitCode::from(1);
        }
        fremde_je_einheit.insert(e.name.clone(), fremde);
        koepfe_je_einheit.insert(e.name.clone(), koepfe);
        let (deklariert, benutzt, eintritte, wurzeln, sperren, funktionen, metall, atomare,
             arenen) = modulkarte(&quellen);
        atomare_je_einheit.insert(e.name.clone(), atomare);
        arenen_je_einheit.insert(e.name.clone(), arenen);
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
            if let Some(befund) = eintrittsregel(e.art, manifest.ohne_libc, &eintritte_je_einheit[name]) {
                befunde += 1;
                println!("  REFUSED  {name}: {befund}");
            }
            // **And the module rule, for the third time the same reason** (server lane):
            // the two calls a kernel module is entered by are read out of the sources this
            // manifest names, so a plan whose init the kernel could not call says so before
            // a `Kbuild` is written -- and before a kernel build tree is even needed.
            if let Some(befund) =
                modulregel(
                    e,
                    &funktionen_je_einheit[name],
                    &atomare_je_einheit[name],
                    &arenen_je_einheit[name],
                    &treiber_sperren_je_einheit[name],
                    &treiber_funde_je_einheit[name],
                )
            {
                befunde += 1;
                println!("  REFUSED  {name} (module): {befund}");
            }
            // **And its hosted twin** (server lane, TODO section 0e K8): a unit with an
            // `arena` that binds no memory primitive would emit cleanly and die at the
            // linker, over `gabbro_os_reserve` -- the runtime's name, not the program's.
            if let Some(befund) = bindungsregel_gehostet(
                e,
                manifest.metall.is_some(),
                &funktionen_je_einheit[name],
                &arenen_je_einheit[name],
                &treiber_sperren_je_einheit[name],
                &treiber_funde_je_einheit[name],
            ) {
                befunde += 1;
                println!("  REFUSED  {name} (hosted): {befund}");
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
                e.art,
            ) {
                Ok(None) => {}
                Ok(Some(plan)) => {
                    let wurzeln: Vec<&str> =
                        plan.wurzeln.iter().map(|w| w.c_name.as_str()).collect();
                    let sperren: Vec<&str> =
                        plan.sperren.iter().map(|s| s.name.as_str()).collect();
                    // A plan without roots writes no driver -- a line that named one anyway
                    // would promise a file the build does not make.
                    let ziel = if plan.hat_gehostet() {
                        format!("-> {name}.treiber.c")
                    } else if plan.hat_metall() {
                        format!("-> {name}.metall.c")
                    } else if plan.hat_kmod_faeden() {
                        "-> wurzeln.h (one kthread per root)".to_string()
                    } else {
                        "(no driver: nothing to start)".to_string()
                    };
                    println!(
                        "  driver   {name}: roots [{}] locks [{}] {ziel}",
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
        // **The handwritten C this plan puts into its products** (C-free lane, C0), one line
        // per file -- `c-file <unit> <origin> <lines> <path>`. It is read here, out of the
        // same lists the build compiles from (`fremde`, `koepfe`, `METALL_QUELLEN`,
        // `KMOD_QUELLEN`, the driver plan), so `instrumente/zaehle-c.py` counts what the
        // build uses and no second guess of it (`W7`).
        if argumente.iter().any(|a| a == "--c-liste") {
            for name in &reihenfolge {
                let e = manifest.einheiten.iter().find(|x| &x.name == name).expect("named");
                let plan = match treiberregel(
                    &treiber_funde_je_einheit[name],
                    &treiber_sperren_je_einheit[name],
                    &funktionen_je_einheit[name],
                    &metall_je_einheit[name],
                    e.art,
                ) {
                    Ok(p) => p,
                    Err(_) => None,
                };
                for (herkunft, pfad) in handgeschrieben(
                    &manifest,
                    e,
                    &fremde_je_einheit[name],
                    &koepfe_je_einheit[name],
                    plan.as_ref(),
                    &arenen_je_einheit[name],
                ) {
                    let zeilen = std::fs::read(&pfad)
                        .map(|b| b.iter().filter(|&&c| c == b'\n').count())
                        .unwrap_or(0);
                    println!("c-file {name} {herkunft} {zeilen} {}", pfad.display());
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
        if let Some(befund) = eintrittsregel(e.art, manifest.ohne_libc, &eintritte_je_einheit[name]) {
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
            e.art,
        ) {
            Ok(plan) => plan,
            Err(befund) => {
                abgesagt += 1;
                println!("REFUSED  {name} (driver): {befund}");
                continue;
            }
        };
        // **The module rule, beside the entry rule and the driver rule** (server lane).
        // It runs BEFORE any C is written, for the same reason as the other two: a module
        // whose init the kernel cannot call builds cleanly and fails at `insmod`.
        if let Some(befund) = modulregel(
            e,
            &funktionen_je_einheit[name],
            &atomare_je_einheit[name],
            &arenen_je_einheit[name],
            &treiber_sperren_je_einheit[name],
            &treiber_funde_je_einheit[name],
        ) {
            abgesagt += 1;
            println!("REFUSED  {name} (module): {befund}");
            continue;
        }
        // **And its hosted twin, before any C is written** (server lane, TODO section 0e
        // K8). Same reason as the three rules above it: without this, a unit with an
        // `arena` and no binding compiles cleanly and fails at the linker, over a name the
        // program never wrote.
        if let Some(befund) = bindungsregel_gehostet(
            e,
            manifest.metall.is_some(),
            &funktionen_je_einheit[name],
            &arenen_je_einheit[name],
            &treiber_sperren_je_einheit[name],
            &treiber_funde_je_einheit[name],
        ) {
            abgesagt += 1;
            println!("REFUSED  {name} (hosted): {befund}");
            continue;
        }
        match baue_einheit(
            &manifest,
            e,
            quellen,
            &fremde_je_einheit[name],
            &koepfe_je_einheit[name],
            &unten,
            bau,
            pruefbau,
            treiber_plan.as_ref(),
        ) {
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
    fremde: &[String],
    koepfe: &[String],
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
    let mut laufzeit_bytes: Vec<Vec<u8>> = match (&manifest.metall, bild_erwartet) {
        (Some(dir), true) => METALL_QUELLEN
            .iter()
            .map(|f| std::fs::read(PathBuf::from(dir).join(f)).unwrap_or_default())
            .collect(),
        _ => Vec::new(),
    };
    // **The same for the module runtime, and until 2026-09-28 it did nothing.**
    // `KMOD_QUELLEN` was written beside the metal list and read by nobody -- `cargo build`
    // said so (`constant KMOD_QUELLEN is never used`) and the effect was that a changed
    // `kmodul.c` left a stale `.ko` standing as up to date. The list gained `sperre.h`
    // with the lock primitives (K3), which made the hole load-bearing: a module whose
    // locks changed would not have been rebuilt.
    if e.art == Art::Modul {
        if let Some((dir, _)) = &manifest.kmod {
            for f in KMOD_QUELLEN {
                laufzeit_bytes.push(std::fs::read(PathBuf::from(dir).join(f)).unwrap_or_default());
            }
        }
    }
    // **And the unit's OWN foreign files** (server lane, session 6, TODO section 0e K7).
    // Until K7 neither the `.c` bodies nor -- there were none -- the headers entered the
    // fingerprint, so a program that changed its own kernel call kept a stale `.ko`
    // standing as up to date. *It never bit, because the harness builds in a fresh
    // directory every time;* with the binding library it would, since the twelve bodies a
    // module rests on are now exactly such files.
    let mut eigen_bytes: Vec<Vec<u8>> = Vec::new();
    for f in fremde.iter().chain(koepfe.iter()) {
        eigen_bytes.push(std::fs::read(f).unwrap_or_default());
    }
    let mut teile: Vec<&[u8]> = Vec::new();
    if treiber_erwartet || metall_erwartet {
        teile.push(treiber::GENERATOR_KENNUNG.as_bytes());
    }
    for b in &eigen_bytes {
        teile.push(b.as_slice());
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
        // The artefact of a module unit is the `.ko` the kernel's own build writes.
        Art::Modul => PathBuf::from(&manifest.ausgabe).join(format!("{}.ko", e.name)),
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

    // **The unit's OWN C bodies, for a unit that is not a module** (server lane,
    // 2026-09-28, TODO section 0e K8). A module's go to the kernel's build with the kernel's
    // flags (`kmod_modul_binden`); a hosted unit's are compiled right here, with the
    // manifest's own compiler line -- the same line the emitted C is compiled with, because
    // they are the same program.
    //
    // *Why the object names carry an index and not the file's stem:* two files of different
    // directories may share a stem, and an object silently overwritten by another would link
    // and then answer the wrong body. The index is the unit's file order, which is the
    // manifest's own.
    //
    // **The compiler line is the manifest's, with nothing added** -- and a body that
    // includes the runtime's interface (`laufzeit/bindung.h`, which is what holds a
    // binding's definitions against the declarations the runtime calls) says so with an
    // `-I` on that line, like any other library header. *An `-I` invented here would be a
    // path relative to whatever directory the build was started in* -- a flag that works
    // from the tree root and nowhere else is worse than none.
    let mut fremd_objekte: Vec<PathBuf> = Vec::new();
    if e.art != Art::Modul {
        for (i, f) in fremde.iter().enumerate() {
            let ziel = PathBuf::from(&manifest.ausgabe).join(format!("{}.fremd{i}.o", e.name));
            let mut ruf = std::process::Command::new(&manifest.compiler[0]);
            ruf.args(&manifest.compiler[1..]);
            ruf.arg("-c").arg("-o").arg(&ziel).arg(f);
            let aus = match ruf.output() {
                Ok(a) => a,
                Err(err) => {
                    return Ergebnis::Abgesagt(format!(
                        "{} did not run: {err}",
                        manifest.compiler[0]
                    ))
                }
            };
            if !aus.status.success() {
                eprint!("{}", String::from_utf8_lossy(&aus.stderr));
                return Ergebnis::Abgesagt(format!("{} refused the unit's own C body `{f}`",
                    manifest.compiler[0]));
            }
            fremd_objekte.push(ziel);
        }
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
        for o in &fremd_objekte {
            binde.arg(o);
        }
        // **`nolibc`: a process without a C library** (C-free lane, C1). The entry is a
        // generated `_start`, compiled with the manifest's own compiler line, and the link
        // takes no startup file, no library and nothing dynamic.
        if manifest.ohne_libc {
            let start_c = PathBuf::from(&manifest.ausgabe).join(format!("{}.start.c", e.name));
            let start_o = PathBuf::from(&manifest.ausgabe).join(format!("{}.start.o", e.name));
            if let Err(err) = std::fs::write(&start_c, prozess_start(EINTRITT)) {
                return Ergebnis::Abgesagt(format!("{}: {err}", start_c.display()));
            }
            let mut ruf = std::process::Command::new(&manifest.compiler[0]);
            ruf.args(&manifest.compiler[1..]);
            ruf.arg("-c").arg("-o").arg(&start_o).arg(&start_c);
            match ruf.output() {
                Ok(a) if a.status.success() => {}
                Ok(a) => {
                    eprint!("{}", String::from_utf8_lossy(&a.stderr));
                    return Ergebnis::Abgesagt(format!(
                        "{} refused the generated process entry",
                        manifest.compiler[0]
                    ));
                }
                Err(err) => {
                    return Ergebnis::Abgesagt(format!("{} did not run: {err}", manifest.compiler[0]))
                }
            }
            binde.arg(&start_o).arg("-nostdlib").arg("-static").arg("-Wl,-e,_start");
        }
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

    // **The kernel module, built by the KERNEL's own build system** (server lane,
    // TODO section 0e K4). Not by `cc` here: a module is compiled with the flags of the
    // kernel it is loaded into, and those flags belong to that kernel's `Kbuild`, not to this
    // tree. So the build writes the `Kbuild` and calls `make -C <kernel build dir>` --
    // exactly what `instrumente/pruefe-kernelmodul.sh` did in shell until today, and now in
    // ONE place (`W7`).
    if e.art == Art::Modul {
        if let Some((laufzeit, kernbau)) = &manifest.kmod {
            let sperren: &[treiber::Sperre] =
                treiber_plan.map_or(&[], |p| p.sperren.as_slice());
            let wurzeln: &[treiber::Wurzel] =
                treiber_plan.map_or(&[], |p| p.wurzeln.as_slice());
            if let Err(grund) =
                kmod_modul_binden(
                    manifest, laufzeit, kernbau, e, fremde, koepfe, sperren, wurzeln,
                )
            {
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

/// **Every handwritten file a unit's products contain** as `(origin, path)` (C-free lane,
/// C0): the unit's own foreign `.c`/`.h`, the module runtime a `kmod` line names, the
/// bare-metal runtime a `metal` line names when the unit owns a bare-metal driver, and the
/// hosted runtime the generated driver's header tells the user to link (`arena_dyn.c` for an
/// `arena`, `faden.c` for a `concurrent` set, `bindung.h` for either). `.ld` linker scripts
/// are not C and are left out; the emitted C and the generated drivers are Gabbro's own
/// output and are not listed.
fn handgeschrieben(
    manifest: &Manifest,
    e: &Einheit,
    fremde: &[String],
    koepfe: &[String],
    plan: Option<&TreiberPlan>,
    arenen: &[String],
) -> Vec<(&'static str, PathBuf)> {
    let mut aus: Vec<(&'static str, PathBuf)> = Vec::new();
    for f in fremde.iter().chain(koepfe.iter()) {
        aus.push(("unit", PathBuf::from(f)));
    }
    if e.art == Art::Modul {
        if let Some((dir, _)) = &manifest.kmod {
            for f in KMOD_QUELLEN {
                aus.push(("kmod-runtime", PathBuf::from(dir).join(f)));
            }
            // `kmod_modul_binden` copies the shared arena header beside them.
            aus.push(("kmod-runtime", PathBuf::from(dir).join("../arena_dyn.h")));
        }
    }
    if plan.is_some_and(|p| p.hat_metall()) {
        if let Some(dir) = &manifest.metall {
            for f in METALL_QUELLEN.iter().filter(|f| !f.ends_with(".ld")) {
                aus.push(("metal-runtime", PathBuf::from(dir).join(f)));
            }
        }
    }
    // A `metal` line makes the unit's product the bare-metal image, which links none of the
    // hosted runtime.
    if e.art != Art::Modul && manifest.metall.is_none() {
        let laufzeit = PathBuf::from("laufzeit");
        let mut dazu: Vec<&str> = Vec::new();
        if plan.is_some_and(|p| p.hat_gehostet()) {
            dazu.extend(["faden.c", "faden.h", "bindung.h"]);
        }
        // A dynamic arena brings no handwritten file any more: its runtime is the generated
        // driver's (`treiber::ARENA_LAUFZEIT`, template `arena.dyn`).
        if !arenen.is_empty() {
            dazu.extend(["bindung.h"]);
        }
        dazu.sort();
        dazu.dedup();
        for f in dazu {
            aus.push(("hosted-runtime", laufzeit.join(f)));
        }
    }
    aus
}

/// **The process entry of a `nolibc` program, written by the build** (C-free lane, C1).
///
/// The kernel starts an x86_64 process with `rsp` 16-aligned and pointing at `argc`, and
/// no return address under it. A C function expects `rsp + 8` to be 16-aligned at entry, so
/// the stub aligns and calls the program's `main` -- which the entry rule (`eintrittsregel`)
/// holds to be one public nullary function declared `-> never`. **The stub knows no system
/// call**: the program ends itself through its own `syscall` gate, so no operating system's
/// number is spelled in this tree.
fn prozess_start(eintritt: &str) -> String {
    format!(
        "/* Generated by the Gabbro build (`nolibc`) -- the process entry. Do not edit. */\n\
         extern void {eintritt}(void);\n\
         \n\
         __attribute__((naked, noreturn)) void _start(void)\n\
         {{\n\
         \x20   __asm__ volatile (\n\
         \x20       \"xor %ebp, %ebp\\n\"\n\
         \x20       \"and $-16, %rsp\\n\"\n\
         \x20       \"call {eintritt}\\n\"\n\
         \x20       \"ud2\\n\");\n\
         }}\n"
    )
}

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

/// The module runtime's files, relative to the `kmod` runtime directory. Their bytes are
/// part of the module's fingerprint -- a changed `kmodul.c` rebuilds the `.ko`.
///
/// **`sperre.h` joined the list on 2026-09-28** (the lock primitives, TODO section 0e K3), and
/// on the same day the list was READ for the first time: `cargo build` had been saying
/// `constant KMOD_QUELLEN is never used` since it was written, so a changed `kmodul.c` left a
/// stale `.ko` standing as up to date.
///
/// **`include/stdatomic.h` joined it the same week** (K6): it stopped being a refusal and
/// became the ATOMIC LOWERING, so a changed ordering row has to rebuild the module the same
/// way a changed lock primitive does. **It is a refusal again since K7** and the ordering
/// rows are the PROGRAM's (`bibliothek/linux-kmod/stdatomic.h`) -- so they travel in the
/// unit's own file bytes now, beside its `.c` bodies, and the entry here covers only the
/// door. `bindung.h` joined in the same step: it is the interface the runtime calls through,
/// and a changed declaration is a changed module.
const KMOD_QUELLEN: [&str; 7] = [
    "kmodul.c",
    "arena.c",
    "kmodul.h",
    "sperre.h",
    "bindung.h",
    "include/stdint.h",
    "include/stdatomic.h",
];

/// **The generated `sperren.h`: one `F(name, kind)` per `lock`, in name order.**
///
/// The list `laufzeit/kmodul/kmodul.c` expands to define the primitives the emitter only
/// declares. The four kinds are the four `METALL_SPERRE*` macros the bare-metal driver picks
/// between, out of the same [`treiber::Sperre`] list -- one register, three flavours.
///
/// Sorted by name and not by declaration order: the header is a build artefact compared for
/// staleness, and two orders over one list would rebuild the module for nothing. A driver
/// defines each primitive once, so the order is not a fact about the program.
fn sperrenliste(sperren: &[treiber::Sperre]) -> String {
    let mut aus = String::new();
    aus.push_str(
        "/* GENERATED by `gabbro build` -- the locks of this unit (server lane, TODO 0e K3).\n\
 * Do not edit. `laufzeit/kmodul/kmodul.c` expands it through `sperre.h`; the kind is the\n\
 * program's word, not the driver's: MASKED is `masks irqs`, which every runtime flavour\n\
 * keeps in its own way (here `raw_spin_lock_irqsave`). */\n",
    );
    if sperren.is_empty() {
        aus.push_str("/* This unit declares no `lock`, so no primitive is needed. */\n");
        return aus;
    }
    let mut sortiert: Vec<&treiber::Sperre> = sperren.iter().collect();
    sortiert.sort_by(|a, b| a.name.cmp(&b.name));
    let eintraege: Vec<String> = sortiert
        .iter()
        .map(|l| {
            let art = match (l.maskiert, l.geteilt) {
                (true, true) => "MASKED_SHARED",
                (true, false) => "MASKED",
                (false, true) => "SHARED",
                (false, false) => "PLAIN",
            };
            format!("F({}, {art})", l.name)
        })
        .collect();
    aus.push_str(&format!("#define GABBRO_SPERREN(F) {}\n", eintraege.join(" ")));
    aus
}

/// **The generated `wurzeln.h`: one `F(name)` per root of the `concurrent` set**
/// (server lane, 2026-09-28, TODO section 0e K6).
///
/// The module's twin of [`sperrenliste`], and it exists for the same reason: `kmodul.c` is
/// not generated, so what is unit-specific reaches it as a macro list out of the ONE walk the
/// other two driver flavours read (`W7`). The hosted driver starts these roots as pthreads
/// and the bare-metal one as cores; here they become `kthread`s, started after the unit's
/// load function answers 0 and joined before its unload function runs.
///
/// Sorted by name, and for the same reason the lock list is: the header is a build artefact
/// compared for staleness, and the start order of a `concurrent` set is not a fact about the
/// program (the roots are concurrent -- that is what the word says).
fn wurzelliste(wurzeln: &[treiber::Wurzel]) -> String {
    let mut aus = String::new();
    aus.push_str(
        "/* GENERATED by `gabbro build` -- the concurrent roots of this unit (server lane,\n\
 * TODO 0e K6). Do not edit. `laufzeit/kmodul/kmodul.c` expands it into one kthread per\n\
 * root: started when the load function has answered 0, joined before the unload function\n\
 * runs. A root that never returns therefore hangs `rmmod` -- the same contract the hosted\n\
 * driver's join has. */\n",
    );
    if wurzeln.is_empty() {
        aus.push_str("/* This unit declares no `concurrent` root, so no thread is started. */\n");
        return aus;
    }
    let mut namen: Vec<&str> = wurzeln.iter().map(|w| w.c_name.as_str()).collect();
    namen.sort_unstable();
    let eintraege: Vec<String> = namen.iter().map(|n| format!("F({n})")).collect();
    aus.push_str(&format!("#define GABBRO_WURZELN(F) {}\n", eintraege.join(" ")));
    aus
}

/// **Build `<unit>.ko` with the kernel's own build system** (server lane, TODO section 0e K4).
///
/// The recipe, and every step is a named refusal:
///
///  1. a build directory of its own under `out/` (`<unit>.kmod/`), because `make M=<dir>`
///     writes a dozen files beside the sources and none of them belong next to the emitted C;
///  2. the runtime, the emitted unit and the unit's own C bodies copied in FLAT -- the
///     includes are then flat too, which is why `arena.c`'s one `../arena_dyn.h` is rewritten;
///  3. a `Kbuild` naming the objects and the three `-D`s the runtime reads (the arenas are
///     NOT among them: the emitted unit carries `GABBRO_ARENEN` itself);
///  4. `make -C <kernel build dir> M=<dir> modules`;
///  5. the `.ko` moved beside the other artefacts as `<unit>.ko`.
///
/// **Nothing about Linux is decided here.** The module's name is the unit's, its init and exit
/// are the functions the manifest named, its kernel calls are the `extern fn` items the program
/// declared, and their bodies are the `.c` files the manifest named. A different kernel gets a
/// different `kmod` line and not a different Gabbro.
fn kmod_modul_binden(
    manifest: &Manifest,
    laufzeit: &str,
    kernbau: &str,
    e: &Einheit,
    fremde: &[String],
    koepfe: &[String],
    sperren: &[treiber::Sperre],
    wurzeln: &[treiber::Wurzel],
) -> Result<(), String> {
    let aus = PathBuf::from(&manifest.ausgabe);
    let bau = aus.join(format!("{}.kmod", e.name));
    let laufzeit = PathBuf::from(laufzeit);
    let kernbau = PathBuf::from(kernbau);
    if !kernbau.is_dir() {
        return Err(format!(
            "kernel module: `{}` is no directory -- the `kmod` line names the kernel build \
             tree (on a Debian-like system `/lib/modules/$(uname -r)/build`, from the \
             `linux-headers` package)",
            kernbau.display()
        ));
    }
    if !laufzeit.join("kmodul.c").is_file() {
        return Err(format!(
            "kernel module: `{}` holds no `kmodul.c` -- the `kmod` line names the module \
             runtime (`laufzeit/kmodul`)",
            laufzeit.display()
        ));
    }
    std::fs::create_dir_all(bau.join("inc"))
        .map_err(|err| format!("kernel module: {}: {err}", bau.display()))?;
    let kopiere = |von: PathBuf, nach: PathBuf| -> Result<(), String> {
        std::fs::copy(&von, &nach)
            .map(|_| ())
            .map_err(|err| format!("kernel module: {} -> {}: {err}", von.display(), nach.display()))
    };
    kopiere(laufzeit.join("kmodul.c"), bau.join("gabbro_kmodul.c"))?;
    kopiere(laufzeit.join("kmodul.h"), bau.join("kmodul.h"))?;
    // The lock primitives (server lane, TODO section 0e K3). Copied
    // unconditionally like `kmodul.h`: `kmodul.c` includes it only where the
    // unit wrote `GABBRO_SPERREN`, and a build that decided per unit which
    // headers to copy would be a second register over the same `#ifdef`.
    kopiere(laufzeit.join("sperre.h"), bau.join("sperre.h"))?;
    // **The interface between the runtime and the program's binding** (server lane,
    // 2026-09-28, TODO section 0e K7). Twelve declarations and no definition: the runtime
    // calls them, the PROGRAM defines them, and the kernel's own names stand in the
    // program's C alone. It is copied beside `kmodul.c` AND is what the program's own body
    // includes -- so the two halves of every one of the twelve meet in one directory, and
    // the C compiler holds them against each other.
    kopiere(laufzeit.join("bindung.h"), bau.join("bindung.h"))?;
    kopiere(laufzeit.join("../arena_dyn.h"), bau.join("arena_dyn.h"))?;
    // The runtime's arena half sits beside a header one level up in the tree and FLAT here.
    let arena = std::fs::read_to_string(laufzeit.join("arena.c"))
        .map_err(|err| format!("kernel module: {}/arena.c: {err}", laufzeit.display()))?;
    std::fs::write(bau.join("gabbro_arena.c"), arena.replace("\"../arena_dyn.h\"", "\"arena_dyn.h\""))
        .map_err(|err| format!("kernel module: {}: {err}", bau.display()))?;
    let inc = laufzeit.join("include");
    let eintraege = std::fs::read_dir(&inc)
        .map_err(|err| format!("kernel module: {}: {err}", inc.display()))?;
    for x in eintraege {
        let x = x.map_err(|err| format!("kernel module: {}: {err}", inc.display()))?;
        let ziel = bau.join("inc").join(x.file_name());
        kopiere(x.path(), ziel)?;
    }
    // **And the unit's OWN headers, after the runtime's and therefore in place of them**
    // (server lane, 2026-09-28, TODO section 0e K7). This is the whole mechanism by which a
    // program binds something that is not a function: `laufzeit/kmodul/include/stdatomic.h`
    // refuses `_Atomic` outright, and a unit that declares an `atomic` names
    // `bibliothek/linux-kmod/stdatomic.h` -- the table that maps the emitter's nine C11 call
    // forms onto the kernel's memory model -- which lands here and is what the module is
    // built from.
    //
    // *The overwrite is the point and not an accident*, so the order is fixed and stated:
    // the runtime's shims are the floor, the program's files are the answer. A `module` unit
    // with an `atomic` and no `stdatomic.h` is refused one door earlier
    // (`bindungsregel`), so the floor is never silently the answer.
    for k in koepfe {
        let name = Path::new(k)
            .file_name()
            .ok_or_else(|| format!("kernel module: `{k}` names no file"))?;
        kopiere(PathBuf::from(k), bau.join("inc").join(name))?;
    }
    kopiere(aus.join(format!("{}.c", e.name)), bau.join("einheit.c"))?;
    // **The unit's LOCKS, as the one line the module runtime expands** (server lane,
    // 2026-09-28, TODO section 0e K3).
    //
    // The emitter DECLARES `L_nimm`/`L_gib` per `lock` and defines neither: the primitive is
    // trust base, not product (`emit.rs`, `ItemArt::Lock`). Every driver flavour therefore
    // supplies them, and two of the three are GENERATED from exactly the list below -- the
    // hosted driver and the bare-metal one, both out of `treiber.rs` and both out of
    // `TreiberPlan::sperren`. `laufzeit/kmodul/kmodul.c` is NOT generated, so it needs the
    // list as text, and **this is the SAME register, not a second one** (`W7`): the three
    // facts (name, shared pair, `masks irqs`) come from the one `ItemArt::Lock` walk in
    // `sammle`. *Measured 2026-09-28: without this file a `module` unit with one `lock` did
    // not link at all --* `ERROR: modpost: "TAKT_nimm" ... undefined!`, over a unit the
    // checker had passed without a word.
    //
    // WHY NOT IN THE EMITTED C, where the arena list stands (`GABBRO_ARENEN`). Because the
    // emitted C is PINNED, byte for byte, in the translation-validation chain
    // (`grammatik/Grammatik/CText104.lean`), and the Lean `CParser` reads preprocessor lines
    // with a CLOSED grammar: `#include <x.h>` and an integer `#define`, nothing else. A
    // function-like `#define GABBRO_SPERREN(F) …` makes `parseC` answer `none`, and
    // `a2_104 : parseC ctext104 = some (kFuns zert104)` stops being `rfl`. *Measured the same
    // day, in that order: the list went into the emitter first, and the chain's own pin said
    // no.* Widening the parser to skip a directive it cannot evaluate would be the wrong
    // repair -- a macro the parser ignores may rename anything below it -- so the list stays
    // out of the artefact the chain reads. The arena list is a different case only by luck:
    // no chain-pinned unit declares an arena.
    std::fs::write(bau.join("sperren.h"), sperrenliste(sperren))
        .map_err(|err| format!("kernel module: {}/sperren.h: {err}", bau.display()))?;
    // **And the unit's ROOTS, the same way** (server lane, TODO section 0e K6): one
    // `F(name)` per member of the `concurrent` set, out of the same walk, expanded by
    // `kmodul.c` into one `kthread` each. Before this the roots of a `module` unit had a
    // hosted pthread driver written for them -- a file for a world the `.ko` is not in.
    std::fs::write(bau.join("wurzeln.h"), wurzelliste(wurzeln))
        .map_err(|err| format!("kernel module: {}/wurzeln.h: {err}", bau.display()))?;
    let mut objekte = vec!["gabbro_kmodul.o".to_string(), "gabbro_arena.o".to_string()];
    for (i, f) in fremde.iter().enumerate() {
        kopiere(PathBuf::from(f), bau.join(format!("gabbro_fremd{i}.c")))?;
        objekte.push(format!("gabbro_fremd{i}.o"));
    }
    let kbuild = format!(
        "obj-m := {name}.o\n\
         {name}-y := {objekte}\n\
         ccflags-y := -I$(src) -I$(src)/inc \\\n\
         \x20 -DGABBRO_EINHEIT_INCLUDE='\"einheit.c\"' \\\n\
         \x20 -DGABBRO_KMOD_INIT={init} -DGABBRO_KMOD_EXIT={exit} \\\n\
         \x20 -Wno-unused-function\n",
        name = e.name,
        objekte = objekte.join(" "),
        init = e.modul_init,
        exit = e.modul_exit,
    );
    std::fs::write(bau.join("Kbuild"), kbuild)
        .map_err(|err| format!("kernel module: {}/Kbuild: {err}", bau.display()))?;
    let bau_abs = std::fs::canonicalize(&bau)
        .map_err(|err| format!("kernel module: {}: {err}", bau.display()))?;
    let mut c = std::process::Command::new("make");
    c.arg("-C").arg(&kernbau).arg(format!("M={}", bau_abs.display())).arg("modules");
    match c.output() {
        Ok(o) if o.status.success() => {}
        Ok(o) => {
            eprint!("{}", String::from_utf8_lossy(&o.stderr));
            return Err(format!(
                "kernel module: `make -C {} M={} modules` refused (see above)",
                kernbau.display(),
                bau_abs.display()
            ));
        }
        Err(err) => return Err(format!("kernel module: `make` did not run: {err}")),
    }
    let ko = bau.join(format!("{}.ko", e.name));
    if !ko.is_file() {
        return Err(format!(
            "kernel module: `make` succeeded and wrote no {} -- nothing to load",
            ko.display()
        ));
    }
    kopiere(ko, aus.join(format!("{}.ko", e.name)))?;
    Ok(())
}

/// **The generated lock list of a kernel module** (server lane, TODO section 0e K3).
///
/// The whole of what a module driver reads to define the primitives the emitter declares, so
/// every kind has a probe: a dropped entry is an undefined reference at `modpost` and a wrong
/// kind is a `masks irqs` promise the C does not keep. The end-to-end run is
/// `instrumente/pruefe-kernelmodul.sh` probe `takt`.
#[cfg(test)]
mod sperrenliste_tests {
    use super::sperrenliste;
    use super::treiber::Sperre;

    fn s(name: &str, geteilt: bool, maskiert: bool) -> Sperre {
        Sperre { name: name.to_string(), geteilt, maskiert }
    }

    #[test]
    fn die_vier_arten_stehen_je_mit_ihrem_wort() {
        let aus = sperrenliste(&[
            s("A", false, false),
            s("B", true, false),
            s("C", false, true),
            s("D", true, true),
        ]);
        assert!(aus.contains("F(A, PLAIN)"), "{aus}");
        assert!(aus.contains("F(B, SHARED)"), "{aus}");
        assert!(aus.contains("F(C, MASKED)"), "{aus}");
        assert!(aus.contains("F(D, MASKED_SHARED)"), "{aus}");
    }

    /// One `#define`, one line: a `\\`-continuation would have to survive every tool that
    /// copies this header, and it buys nothing.
    #[test]
    fn die_liste_ist_eine_zeile_und_nach_namen_sortiert() {
        let aus = sperrenliste(&[s("ZWEI", false, true), s("EINS", false, false)]);
        let zeile = aus
            .lines()
            .find(|z| z.starts_with("#define GABBRO_SPERREN"))
            .expect("one define line");
        assert_eq!(zeile, "#define GABBRO_SPERREN(F) F(EINS, PLAIN) F(ZWEI, MASKED)", "{aus}");
        assert!(!aus.contains('\\'), "no continuation:\n{aus}");
    }

    /// **A unit without a lock defines NOTHING**, and that is load-bearing: `kmodul.c` decides
    /// on `#ifdef GABBRO_SPERREN` whether to pull in the kernel's spinlock headers at all.
    #[test]
    fn ohne_sperre_kein_define() {
        let aus = sperrenliste(&[]);
        assert!(!aus.contains("#define"), "a lockless unit got a macro:\n{aus}");
        assert!(aus.contains("no `lock`"), "and says why:\n{aus}");
    }
}

#[cfg(test)]
mod wurzelliste_tests {
    use super::treiber::Wurzel;
    use super::wurzelliste;

    fn w(name: &str) -> Wurzel {
        Wurzel { c_name: name.to_string(), gab_path: name.to_string() }
    }

    /// One line, name order, no continuation -- the same shape the lock list has, and for the
    /// same reason: the header is compared for staleness, so two orders over one list would
    /// rebuild the module for nothing.
    #[test]
    fn die_liste_ist_eine_zeile_und_nach_namen_sortiert() {
        let aus = wurzelliste(&[w("zweiter"), w("erster")]);
        let zeile = aus
            .lines()
            .find(|z| z.starts_with("#define GABBRO_WURZELN"))
            .expect("one define line");
        assert_eq!(zeile, "#define GABBRO_WURZELN(F) F(erster) F(zweiter)", "{aus}");
        assert!(!aus.contains('\\'), "no continuation:\n{aus}");
    }

    /// **A unit without a `concurrent` set defines NOTHING**, and that is load-bearing:
    /// `kmodul.c` decides on `#ifdef GABBRO_WURZELN` whether to pull in `linux/kthread.h`
    /// and whether its unload waits for anything at all.
    #[test]
    fn ohne_wurzel_kein_define() {
        let aus = wurzelliste(&[]);
        assert!(!aus.contains("#define"), "a rootless unit got a macro:\n{aus}");
        assert!(aus.contains("no `concurrent` root"), "and says why:\n{aus}");
    }
}

#[cfg(test)]
mod treiberregel_tests {
    use super::{treiberregel, Art, EintrittFund, FunktionsForm, MetallFunde, TreiberFund, TreiberSperre};
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

    /// **The art decides WHICH driver the same roots become** (server lane, 2026-09-28,
    /// TODO section 0e K6).
    ///
    /// One root list, three worlds: a `program` starts them as pthreads (and, since Opus
    /// agent I, as cores on bare metal), a `module` as `kthread`s out of the generated
    /// `wurzeln.h`. Before this the plan did not know the art, so a module with a
    /// `concurrent` set had a hosted pthread driver written beside its `.ko` -- a file for a
    /// world it is not in. *The three predicates are exclusive here, and that is the claim:*
    /// exactly one of them answers for any unit.
    #[test]
    fn die_art_entscheidet_welcher_treiber() {
        let funde = vec![fund("hauptA"), fund("hauptB")];
        let p = treiberregel(&funde, &[], &nullary(), &MetallFunde::default(), Art::Programm)
            .expect("holds")
            .expect("roots");
        assert!(p.hat_gehostet() && p.hat_metall() && !p.hat_kmod_faeden(), "a program");
        let m = treiberregel(&funde, &[], &nullary(), &MetallFunde::default(), Art::Modul)
            .expect("holds")
            .expect("roots");
        assert!(!m.hat_gehostet() && !m.hat_metall() && m.hat_kmod_faeden(), "a module");
        // And the roots themselves are the SAME list -- only the starter differs.
        let a: Vec<&str> = p.wurzeln.iter().map(|w| w.c_name.as_str()).collect();
        let b: Vec<&str> = m.wurzeln.iter().map(|w| w.c_name.as_str()).collect();
        assert_eq!(a, b, "one walk, one list");
    }

    /// **Roots count occurrences, across blocks too** (fix lane F4, review G06 F5).
    /// A member named in two `concurrent` sets is two declared starts -- the checker
    /// counts it so, and the driver must start what the checker judged.
    #[test]
    fn wurzeln_zaehlen_vorkommen() {
        let funde = vec![fund("hauptA"), fund("hauptB"), fund("hauptA")];
        let plan = treiberregel(&funde, &[], &nullary(), &MetallFunde::default(), Art::Programm).expect("occurrences hold").expect("roots");
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
        let befund = treiberregel(&[fund("hauptB")], &[], &f, &MetallFunde::default(), Art::Programm).expect_err("must refuse");
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
        let plan = treiberregel(&[fund("hauptA")], &sperren, &nullary(), &MetallFunde::default(), Art::Programm)
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
        let plan = treiberregel(&[], &[], &f, &metall, Art::Programm).expect("holds").expect("entries own a driver");
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
            let befund = treiberregel(&[], &[], &f, &m, Art::Programm).expect_err("refused");
            assert!(befund.contains(grund), "named: {befund}");
        }
    }

    /// **No roots, no driver.** A unit without a `concurrent` set owns no
    /// artefact and draws no refusal.
    #[test]
    fn ohne_wurzeln_kein_treiber() {
        assert!(treiberregel(&[], &[], &nullary(), &MetallFunde::default(), Art::Programm).expect("holds").is_none());
    }
}
