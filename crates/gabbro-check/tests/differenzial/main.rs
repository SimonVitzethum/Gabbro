//! **Differential harness: the Rust checker against the Lean model's `Akzeptiert`.**
//!
//! Programs are generated from the forms of the Lean model (`atome.rs`: one atom per
//! constructor family, with unsafe twins; `bau.rs`: the combination space, written down in its
//! header), and each is judged three times: by the Rust checker, by the exporter (does the
//! model have a form for it), and by the Lean Bool of the goal theorem's checker
//! (`akzeptiertX_pruefer.akzeptiert gE gFs gLs gCs`, evaluated by Lean in batches).
//!
//! Classes (the denominator is the model, never the corpus):
//!
//! * **(b)** the checker accepts, the model refuses: a CHECKER BUG, fixed at once;
//! * **(a)** the model accepts, the checker refuses: INCOMPLETENESS, the main target;
//! * **(c)** both refuse: expected;
//! * **(d)** the checker accepts and the exporter has no G form: the model is silent (named by
//!   its `LGxxx`), not a disagreement but the border of what Lean decides.
//!
//! `cargo test --test differenzial` runs a deterministic slice (all single-atom programs and a
//! stride over the pairs; the slice size is `GABBRO_DIFF_SLICE`, default 1800) and asserts the
//! classification against `erwartet.rs`. `-- --ignored vollraum` runs the whole space.

mod atome;
mod bau;
mod lauf;
mod sonder;

use std::collections::BTreeMap;

use atome::{katalog, Atom};
use bau::{bau, modi, Arr, Mode};
use lauf::{exportiere, lean_stapel, pur_stapel, rust_verdict, LeanV, PurV, RustV, Stueck};

pub struct Prog {
    pub n: usize,
    pub arr: Arr,
    pub mode: Mode,
    pub atoms: Vec<&'static str>,
    pub src: String,
}

impl Prog {
    fn name(&self) -> String {
        format!("{}/{}/{}", self.arr.name(), self.mode.name(), self.atoms.join("+"))
    }
}

/// Build the programs of one shape over a list of atoms (one per admissible mode).
fn erzeuge(arr: Arr, atoms: &[&Atom], out: &mut Vec<Prog>) {
    for mode in modi(atoms) {
        let n = out.len();
        if let Some(src) = bau(&format!("p{n}"), arr, mode, atoms) {
            out.push(Prog { n, arr, mode, atoms: atoms.iter().map(|a| a.id).collect(), src });
        }
    }
}

/// The whole combination space, in a fixed order: every atom alone (`One`, `Pool`), the written-out
/// units of `sonder.rs`, then every ordered pair of atoms under `Seq`, `Par` and `Call`.
pub fn raum() -> Vec<Prog> {
    let kat = katalog();
    let mut out: Vec<Prog> = Vec::new();
    for a in &kat {
        erzeuge(Arr::One, &[a], &mut out);
        erzeuge(Arr::Pool, &[a], &mut out);
    }
    for (id, src) in sonder::sonder() {
        let n = out.len();
        out.push(Prog { n, arr: Arr::One, mode: Mode::Free, atoms: vec![id], src: src.replace("gen::u", &format!("gen::p{n}")) });
    }
    for arr in [Arr::Seq, Arr::Par, Arr::Call] {
        for a in &kat {
            for b in &kat {
                erzeuge(arr, &[a, b], &mut out);
            }
        }
    }
    out
}

#[derive(Clone, Debug)]
pub struct Messung {
    pub n: usize,
    pub name: String,
    pub arr: Arr,
    pub mode: Mode,
    pub atoms: Vec<&'static str>,
    pub src: String,
    pub rust: RustV,
    pub lean: LeanV,
    /// The verdict of the pure-Lean path (no exporter).
    pub pur: PurV,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Klasse {
    /// Both accept.
    Beide,
    /// (b) the checker accepts, the model refuses.
    B,
    /// (d) the checker accepts, the exporter has no form.
    D,
    /// (a) the model accepts, the checker refuses.
    A,
    /// (c) both refuse (or the model has no form for a refused program).
    C,
    /// The reader refused: a generator defect.
    Syntax,
    /// Not measured by Lean (the run was switched off).
    Offen,
}

pub fn klasse(m: &Messung) -> Klasse {
    match (&m.rust, &m.lean) {
        (RustV::Syntax(_), _) => Klasse::Syntax,
        (_, LeanV::NotRun) | (_, LeanV::Defekt(_)) => Klasse::Offen,
        (RustV::Accept, LeanV::Accept) => Klasse::Beide,
        (RustV::Accept, LeanV::NoForm(_)) => Klasse::D,
        (RustV::Accept, _) => Klasse::B,
        (RustV::Refuse(_), LeanV::Accept) => Klasse::A,
        (RustV::Refuse(_), _) => Klasse::C,
    }
}

/// Measure programs: Rust verdict and export always, Lean in batches when `mit_lean`.
pub fn messe(progs: &[Prog], mit_lean: bool, dir: &std::path::Path) -> Vec<Messung> {
    let mut ms: Vec<Messung> = Vec::new();
    let mut stuecke: Vec<(usize, Stueck)> = Vec::new();
    for (i, p) in progs.iter().enumerate() {
        let name = format!("p{}.gab", p.n);
        let (rust, baum) = rust_verdict(&name, &p.src);
        let mut lean = LeanV::NotRun;
        if let Some(b) = &baum {
            if !matches!(rust, RustV::Syntax(_)) {
                match exportiere(&name, b, &format!("D{}", p.n)) {
                    Ok(s) => stuecke.push((i, s)),
                    Err((code, msg, modell)) => {
                        let t = format!("{code}: {}", msg.chars().take(160).collect::<String>().replace('\n', " "));
                        lean = if modell { LeanV::Verletzt(t) } else { LeanV::NoForm(t) };
                    }
                }
            }
        }
        ms.push(Messung { n: p.n, name: p.name(), arr: p.arr, mode: p.mode, atoms: p.atoms.clone(), src: p.src.clone(), rust, lean, pur: PurV::NotRun });
    }
    if mit_lean {
        std::fs::create_dir_all(dir).unwrap();
        for (k, chunk) in stuecke.chunks(150).enumerate() {
            let st: Vec<Stueck> = chunk.iter().map(|(_, s)| Stueck { ns: s.ns.clone(), text: s.text.clone() }).collect();
            let datei = dir.join(format!("batch{k}.lean"));
            let urteile = lean_stapel(&st, &datei).expect("the Lean run");
            for ((i, _), u) in chunk.iter().zip(urteile) {
                ms[*i].lean = u;
            }
        }
        // The pure-Lean path over every program the reader accepted: no exporter in the loop.
        if std::env::var("GABBRO_DIFF_OHNE_REIN").is_err() {
            let quellen: Vec<(usize, String)> =
                ms.iter().filter(|m| !matches!(m.rust, RustV::Syntax(_))).map(|m| (m.n, m.src.clone())).collect();
            let rein = pur_stapel(&quellen, &dir.join("quellen")).expect("the pure Lean run");
            for m in ms.iter_mut() {
                if let Some(v) = rein.get(&m.n) {
                    m.pur = v.clone();
                }
            }
        }
    }
    ms
}

pub fn zaehle(ms: &[Messung]) -> BTreeMap<Klasse, usize> {
    let mut z = BTreeMap::new();
    for m in ms {
        *z.entry(klasse(m)).or_insert(0) += 1;
    }
    z
}

fn kratz() -> std::path::PathBuf {
    lauf::wurzel().join(".claude/muse-arbeit/kratz/diff")
}

fn lean_lage(m: &Messung) -> String {
    match &m.lean {
        LeanV::Accept => "accept".into(),
        LeanV::Reject => "reject".into(),
        LeanV::Elab(e) => format!("elab({})", e),
        LeanV::Defekt(e) => format!("defekt({})", e),
        LeanV::NoForm(c) => format!("noform({c})"),
        LeanV::Verletzt(c) => format!("verletzt({c})"),
        LeanV::NotRun => "-".into(),
    }
}

/// One line per program, for reading by hand.
pub fn zeile(m: &Messung) -> String {
    let r = match &m.rust {
        RustV::Accept => "ACCEPT".to_string(),
        RustV::Refuse(c) => format!("refuse[{}]", c.join(",")),
        RustV::Syntax(c) => format!("SYNTAX[{}]", c.join(",")),
    };
    let pur = match &m.pur {
        PurV::Accept => "accept".to_string(),
        PurV::Reject => "reject".to_string(),
        PurV::KeinForm(e) => format!("noform({})", e.chars().take(60).collect::<String>()),
        PurV::NotRun => "-".to_string(),
    };
    format!("{:?}\t{}\trust={}\tlean={}\tp{}\tpur={}", klasse(m), m.name, r, lean_lage(m), m.n, pur)
}

fn auswahl(alle: Vec<Prog>, scheibe: usize) -> Vec<Prog> {
    let einzel: Vec<usize> = alle.iter().enumerate().filter(|(_, p)| p.atoms.len() == 1).map(|(i, _)| i).collect();
    let paare = alle.len() - einzel.len();
    let rest = scheibe.saturating_sub(einzel.len()).max(1);
    let schritt = (paare / rest).max(1);
    alle.into_iter()
        .enumerate()
        .filter(|(i, p)| p.atoms.len() == 1 || (i % schritt == 0))
        .map(|(_, p)| p)
        .collect()
}

fn umgebung(name: &str, vorgabe: usize) -> usize {
    std::env::var(name).ok().and_then(|s| s.parse().ok()).unwrap_or(vorgabe)
}

/// Print the source and the Rust diagnostics of every program whose name contains
/// `GABBRO_DIFF_SHOW` (for developing atoms; does nothing when unset).
#[test]
fn zeige_programme() {
    let Ok(f) = std::env::var("GABBRO_DIFF_SHOW") else { return };
    for p in raum().iter().filter(|p| p.name().contains(&f)) {
        eprintln!("=== {}\n{}\n{}", p.name(), p.src, lauf::rust_text("p.gab", &p.src));
    }
}

/// Write the Lean file of the programs whose name contains `GABBRO_DIFF_LEAN` to
/// `kratz/diff/eins.lean` (run it with `lake env lean`; for reading the full Lean error).
#[test]
fn schreibe_lean_datei() {
    let Ok(f) = std::env::var("GABBRO_DIFF_LEAN") else { return };
    let mut st = Vec::new();
    for p in raum().iter().filter(|p| p.name().contains(&f)) {
        let name = format!("p{}.gab", p.n);
        let (_, baum) = rust_verdict(&name, &p.src);
        if let Some(Ok(s)) = baum.as_ref().map(|b| exportiere(&name, b, &format!("D{}", p.n))) {
            st.push(s);
        }
    }
    let (text, _) = lauf::stapel_datei(&st);
    std::fs::create_dir_all(kratz()).unwrap();
    std::fs::write(kratz().join("eins.lean"), text).unwrap();
}

/// The whole space through the Rust checker and the exporter (no Lean): how many programs, how
/// the checker and the exporter split them. Prints the table; asserts nothing but readability.
#[test]
fn gesamtraum_rust_und_export() {
    if std::env::var("GABBRO_DIFF_GESAMT").is_err() {
        return;
    }
    let alle = raum();
    let ms = messe(&alle, false, &kratz());
    let mut z: BTreeMap<String, usize> = BTreeMap::new();
    for m in &ms {
        let r = match &m.rust {
            RustV::Accept => "accept",
            RustV::Refuse(_) => "refuse",
            RustV::Syntax(_) => "SYNTAX",
        };
        let e = match &m.lean {
            LeanV::NoForm(_) => "noform",
            LeanV::Verletzt(_) => "verletzt",
            _ => "exported",
        };
        *z.entry(format!("rust={r} export={e}")).or_insert(0) += 1;
    }
    eprintln!("space {}: {z:?}", alle.len());
    if std::env::var("GABBRO_DIFF_ZEILEN").is_ok() {
        for m in &ms {
            eprintln!("{}", zeile(m));
        }
    }
    assert_eq!(ms.iter().filter(|m| klasse(m) == Klasse::Syntax).count(), 0);
}

/// The report: the counts per class, per atom (every program the atom stands in), and the
/// classes of (a) and (b) with a minimal example (the shortest source) each.
pub fn bericht(ms: &[Messung]) -> String {
    let mut out = String::new();
    let z = zaehle(ms);
    out.push_str(&format!("programs {}, classes {z:?}\n\n", ms.len()));
    // counts per atom
    let mut je_atom: BTreeMap<&str, BTreeMap<Klasse, usize>> = BTreeMap::new();
    for m in ms {
        for a in &m.atoms {
            *je_atom.entry(a).or_default().entry(klasse(m)).or_insert(0) += 1;
        }
    }
    out.push_str("per atom (every program the atom stands in): Beide / (b) B / (d) D / (a) A / (c) C / open\n");
    for (a, c) in &je_atom {
        let g = |k: Klasse| c.get(&k).copied().unwrap_or(0);
        out.push_str(&format!(
            "  {a:<22} {:>5} {:>4} {:>5} {:>4} {:>5} {:>5}\n",
            g(Klasse::Beide), g(Klasse::B), g(Klasse::D), g(Klasse::A), g(Klasse::C), g(Klasse::Offen)
        ));
    }
    // classes of (a) and (b): grouped by the refusal codes (a) or by the model's reason (b)
    for (k, name) in [(Klasse::A, "(a)"), (Klasse::B, "(b)")] {
        let mut g: BTreeMap<String, Vec<&Messung>> = BTreeMap::new();
        for m in ms.iter().filter(|m| klasse(m) == k) {
            let schluessel = match (&m.rust, &m.lean) {
                (RustV::Refuse(c), _) => format!("checker refuses {}", c.join(",")),
                (_, l) => format!("model: {}", lean_lage(&Messung { lean: l.clone(), ..m.clone() }).chars().take(90).collect::<String>()),
            };
            g.entry(schluessel).or_default().push(m);
        }
        out.push_str(&format!("\nclass {name}: {} programs in {} groups\n", g.values().map(Vec::len).sum::<usize>(), g.len()));
        for (s, v) in &g {
            let kleinste = v.iter().min_by_key(|m| (m.atoms.len(), m.src.len())).unwrap();
            out.push_str(&format!("  {:>5}  {s}\n         minimal: {}\n", v.len(), kleinste.name));
        }
    }
    out
}

/// The pure-Lean path (`Parser/Cover/Differenz.lean`) against the Rust checker and against the
/// exporter route: how much of the measured space it decides, and where it agrees.
pub fn rein_bericht(ms: &[Messung]) -> String {
    let mut out = String::new();
    let gelaufen: Vec<&Messung> = ms.iter().filter(|m| m.pur != PurV::NotRun).collect();
    let entschieden: Vec<&&Messung> = gelaufen.iter().filter(|m| matches!(m.pur, PurV::Accept | PurV::Reject)).collect();
    out.push_str(&format!(
        "\npure-Lean path: {} programs sent, {} decided (accept/reject), {} outside the fragment of Track P\n",
        gelaufen.len(), entschieden.len(), gelaufen.len() - entschieden.len()
    ));
    // by the first refused stage
    let mut stufen: BTreeMap<String, usize> = BTreeMap::new();
    for m in &gelaufen {
        if let PurV::KeinForm(e) = &m.pur {
            let k = e.split(':').next().unwrap_or("").to_string();
            *stufen.entry(k).or_insert(0) += 1;
        }
    }
    out.push_str(&format!("  refused by stage: {stufen:?}\n"));
    let mut z: BTreeMap<String, usize> = BTreeMap::new();
    let mut beispiele: BTreeMap<String, &Messung> = BTreeMap::new();
    for m in &entschieden {
        let rust = match &m.rust { RustV::Accept => "rust-accept", _ => "rust-refuse" };
        let pur = if m.pur == PurV::Accept { "pure-accept" } else { "pure-reject" };
        let exp = match &m.lean {
            LeanV::Accept => "export-accept",
            LeanV::Reject => "export-reject",
            LeanV::Elab(_) | LeanV::Verletzt(_) => "export-model-refuses",
            _ => "export-none",
        };
        let k = format!("{rust} {pur} {exp}");
        *z.entry(k.clone()).or_insert(0) += 1;
        let better = beispiele.get(&k).is_none_or(|b| (m.atoms.len(), m.src.len()) < (b.atoms.len(), b.src.len()));
        if better {
            beispiele.insert(k, m);
        }
    }
    for (k, n) in &z {
        out.push_str(&format!("  {n:>6}  {k}   (minimal: {})\n", beispiele[k].name));
    }
    out
}

/// **The whole space, Lean included** (about ten minutes): `cargo test --test differenzial
/// vollraum -- --ignored --nocapture`. Writes `kratz/diff/bericht.txt`.
#[test]
#[ignore]
fn vollraum() {
    let alle = raum();
    let ms = messe(&alle, true, &kratz());
    let b = format!("{}{}", bericht(&ms), rein_bericht(&ms));
    std::fs::write(kratz().join("bericht.txt"), &b).unwrap();
    let mut tsv = String::new();
    for m in &ms {
        tsv.push_str(&zeile(m));
        tsv.push('\n');
    }
    std::fs::write(kratz().join("voll.tsv"), tsv).unwrap();
    eprintln!("{b}");
}

/// The slice of the space and its measurement; prints the table when `GABBRO_DIFF_ZEILEN` is set.
#[test]
fn schnitt_gegen_das_modell() {
    let alle = raum();
    let gesamt = alle.len();
    let progs = auswahl(alle, umgebung("GABBRO_DIFF_SLICE", 1800));
    let mit_lean = std::env::var("GABBRO_DIFF_OHNE_LEAN").is_err();
    let ms = messe(&progs, mit_lean, &kratz());
    let z = zaehle(&ms);
    eprintln!("space {gesamt}, slice {}, classes {z:?}{}", ms.len(), rein_bericht(&ms));
    if std::env::var("GABBRO_DIFF_ZEILEN").is_ok() {
        for m in &ms {
            eprintln!("{}", zeile(m));
        }
    }
    assert_eq!(z.get(&Klasse::Syntax), None, "a generated program does not read");
}
