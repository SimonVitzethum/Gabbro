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

use std::collections::BTreeMap;

use atome::{katalog, Atom};
use bau::{bau, modi, Arr, Mode};
use lauf::{exportiere, lean_stapel, rust_verdict, LeanV, RustV, Stueck};

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

/// The whole combination space, in a fixed order.
pub fn raum() -> Vec<Prog> {
    let kat = katalog();
    let mut out = Vec::new();
    let mut n = 0usize;
    let mut push = |arr: Arr, atoms: Vec<&Atom>, out: &mut Vec<Prog>| {
        for mode in modi(&atoms) {
            let name = format!("p{n}");
            if let Some(src) = bau(&name, arr, mode, &atoms) {
                out.push(Prog { n, arr, mode, atoms: atoms.iter().map(|a| a.id).collect(), src });
                n += 1;
            }
        }
    };
    for a in &kat {
        push(Arr::One, vec![a], &mut out);
        push(Arr::Pool, vec![a], &mut out);
    }
    for arr in [Arr::Seq, Arr::Par, Arr::Call] {
        for a in &kat {
            for b in &kat {
                push(arr, vec![a, b], &mut out);
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
}

pub fn klasse(m: &Messung) -> Klasse {
    match (&m.rust, &m.lean) {
        (RustV::Syntax(_), _) => Klasse::Syntax,
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
        ms.push(Messung { n: p.n, name: p.name(), arr: p.arr, mode: p.mode, atoms: p.atoms.clone(), src: p.src.clone(), rust, lean });
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
    format!("{:?}\t{}\trust={}\tlean={}\tp{}", klasse(m), m.name, r, lean_lage(m), m.n)
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

/// The slice of the space and its measurement; prints the table when `GABBRO_DIFF_ZEILEN` is set.
#[test]
fn schnitt_gegen_das_modell() {
    let alle = raum();
    let gesamt = alle.len();
    let progs = auswahl(alle, umgebung("GABBRO_DIFF_SLICE", 1800));
    let mit_lean = std::env::var("GABBRO_DIFF_OHNE_LEAN").is_err();
    let ms = messe(&progs, mit_lean, &kratz());
    let z = zaehle(&ms);
    eprintln!("space {gesamt}, slice {}, classes {z:?}", ms.len());
    if std::env::var("GABBRO_DIFF_ZEILEN").is_ok() {
        for m in &ms {
            eprintln!("{}", zeile(m));
        }
    }
    assert_eq!(z.get(&Klasse::Syntax), None, "a generated program does not read");
}
