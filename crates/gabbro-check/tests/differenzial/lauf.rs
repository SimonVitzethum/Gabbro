//! The three verdicts on one generated program, and the batch run of the Lean one.
//!
//! * **Rust**: `lies` + `pruefe`; the verdict is "no diagnostic of level error"
//!   (what `gabbro check` exits on).
//! * **Export**: `lean_g::export_ns`. A refusal (`LGxxx`) means the Lean model has no form
//!   for the program: the model gives no verdict.
//! * **Lean**: the exported unit is compiled with the other exports of its batch and the Bool
//!   `akzeptiertX_pruefer.akzeptiert gE gFs gLs gCs` -- the checker of the goal theorem
//!   `gabbro_ziel` -- is evaluated. A Lean elaboration error inside the export (a `by decide`
//!   side condition that fails, an ill-typed term) is the model refusing the program as a
//!   typed term; it is its own verdict, `Elab`.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::Command;

use gabbro_check::lean_g;
use gabbro_syntax::diag::Stufe;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RustV {
    Accept,
    Refuse(Vec<String>),
    /// The reader refused: a generator defect, never a verdict.
    Syntax(Vec<String>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LeanV {
    /// `Akzeptiert` evaluates to `true`.
    Accept,
    /// `Akzeptiert` evaluates to `false`.
    Reject,
    /// The export does not elaborate because a premise of the model fails (a `by decide` side
    /// condition that Lean PROVES false): the model refuses the typed term (first error line).
    Elab(String),
    /// The export does not elaborate for a reason that says nothing about the program (an
    /// unknown constant, a type mismatch of the export's own shape, a `decide` that does not
    /// evaluate): a defect of the exporter, no verdict (first error line).
    Defekt(String),
    /// The exporter has no G form for the program (`LGxxx`).
    NoForm(String),
    /// The export refuses because the program breaks a premise of the model (a guard not held,
    /// a rank not above everything held, a range that does not fit): the model refuses.
    Verletzt(String),
    /// Not run.
    NotRun,
}

/// The full diagnostics text of the Rust checker (for reading by hand).
pub fn rust_text(name: &str, src: &str) -> String {
    let (baum, mut absagen) = gabbro_syntax::lies(name, src);
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    absagen.zeige(src)
}

pub fn rust_verdict(name: &str, src: &str) -> (RustV, Option<gabbro_syntax::ast::Programm>) {
    let (baum, mut absagen) = gabbro_syntax::lies(name, src);
    let lese: Vec<String> = absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code.to_string())
        .collect();
    if !lese.is_empty() {
        return (RustV::Syntax(lese), None);
    }
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    let mut codes: Vec<String> = absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code.to_string())
        .collect();
    codes.sort();
    codes.dedup();
    if codes.is_empty() {
        (RustV::Accept, Some(baum))
    } else {
        (RustV::Refuse(codes), Some(baum))
    }
}

/// One program of a Lean batch: its namespace and its export text.
pub struct Stueck {
    pub ns: String,
    pub text: String,
}

/// Export one program; `Err((code, message))` where the exporter has no form.
pub fn exportiere(
    name: &str,
    baum: &gabbro_syntax::ast::Programm,
    ns: &str,
) -> Result<Stueck, (String, String, bool)> {
    match lean_g::export_ns(name, baum, ns) {
        Ok(text) => Ok(Stueck { ns: ns.to_string(), text }),
        Err(r) => Err((r.code.to_string(), r.message, r.modell)),
    }
}

const KOPF_IMPORTE: &[&str] = &[
    "Grammatik.Zielsatz.Kern.Akzeptiert",
    "Grammatik.Zielsatz.Kern.Beweis",
    "Grammatik.Zielsatz.Atomar.BeweisAtomar",
];

/// Merge exports into one Lean file: the union of the imports once on top, then each program in
/// its namespace followed by its verdict line `DIFF <ns> <Bool>`. Returns the file and, per
/// program, the first and last line it occupies (to attribute Lean errors).
pub fn stapel_datei(stuecke: &[Stueck]) -> (String, Vec<(usize, usize)>) {
    let mut importe: BTreeSet<String> = KOPF_IMPORTE.iter().map(|s| s.to_string()).collect();
    let mut rumpf = String::new();
    let mut bereiche = Vec::new();
    let mut zeile = 0usize;
    for s in stuecke {
        let anfang = zeile + 1;
        for l in s.text.lines() {
            if let Some(m) = l.strip_prefix("import ") {
                importe.insert(m.trim().to_string());
                continue;
            }
            rumpf.push_str(l);
            rumpf.push('\n');
            zeile += 1;
        }
        let q = format!("Gabbro.Grammatik.{}", s.ns);
        rumpf.push_str(&format!(
            "#eval IO.println s!\"DIFF {} {{Gabbro.Grammatik.Zielsatz.akzeptiertX_pruefer.akzeptiert {q}.gE {q}.gFs {q}.gLs {q}.gCs}}\"\n",
            s.ns
        ));
        zeile += 1;
        bereiche.push((anfang, zeile));
    }
    let mut kopf = String::new();
    for i in &importe {
        kopf.push_str(&format!("import {i}\n"));
    }
    let kopfzeilen = importe.len();
    let bereiche = bereiche.into_iter().map(|(a, b)| (a + kopfzeilen, b + kopfzeilen)).collect();
    (format!("{kopf}{rumpf}"), bereiche)
}

pub fn wurzel() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn lake() -> PathBuf {
    if let Ok(l) = std::env::var("LAKE") {
        return PathBuf::from(l);
    }
    let home = std::env::var("HOME").unwrap_or_default();
    let p = PathBuf::from(home).join(".elan/bin/lake");
    if p.is_file() { p } else { PathBuf::from("lake") }
}

/// Run Lean over one batch file; returns (stdout, stderr).
pub fn lean_lauf(datei: &Path) -> Result<(String, String), String> {
    let out = Command::new(lake())
        .current_dir(wurzel().join("grammatik"))
        .env_remove("ELAN_TOOLCHAIN")
        .args(["env", "lean", "-j2", "-M6144", "-DmaxErrors=100000"])
        .arg(datei)
        .output()
        .map_err(|e| format!("`lake env lean` could not run: {e}"))?;
    Ok((
        String::from_utf8_lossy(&out.stdout).into_owned(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
    ))
}

/// The verdict of the PURE-Lean path on one source text (`Parser/Cover/Differenz.lean`: lex, parse,
/// elaborate, lower, `AkzeptiertX`), with no Rust exporter in the loop.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PurV {
    Accept,
    Reject,
    /// A stage of the Lean pipeline refused BY A PREMISE OF THE MODEL (an access without its guard, a
    /// write without the right, a lock against a held lock of higher rank, a value outside its
    /// range): the model refuses the program, as `LeanV::Verletzt` does for the exporter route.
    Verletzt(String),
    /// A stage of the Lean pipeline refused (`parse-err`, `elab-err`, `lower-err`): the fragment of
    /// Track P does not cover the program; no verdict.
    KeinForm(String),
    NotRun,
}

/// The messages of the Lean elaboration and lowering that name a violated premise of the model (the
/// others say a form is missing).
const PUR_VERLETZT: &[&str] = &[
    "access without held guard",
    "write without right",
    "locks against a held lock",
    "value outside range",
    "value outside the annotated range",
    "write through a read pointer",
    "conversion outside target range",
    "index outside count",
];

/// Run the pure-Lean path over the given sources (written as `<n>.gab` under `dir`); the verdict of
/// each by its number.
pub fn pur_stapel(quellen: &[(usize, String)], dir: &Path) -> Result<std::collections::BTreeMap<usize, PurV>, String> {
    let _ = std::fs::remove_dir_all(dir);
    std::fs::create_dir_all(dir).map_err(|e| format!("cannot create {}: {e}", dir.display()))?;
    for (n, q) in quellen {
        std::fs::write(dir.join(format!("p{n}.gab")), q).map_err(|e| format!("write: {e}"))?;
    }
    // The library module must be built (the script imports its olean): cheap when up to date.
    let bau = Command::new(lake())
        .current_dir(wurzel().join("grammatik"))
        .env_remove("ELAN_TOOLCHAIN")
        .args(["build", "Grammatik.Parser.Cover.Differenz"])
        .output()
        .map_err(|e| format!("`lake build` could not run: {e}"))?;
    if !bau.status.success() {
        return Err(format!("`lake build Grammatik.Parser.Cover.Differenz` failed:\n{}", String::from_utf8_lossy(&bau.stdout)));
    }
    let out = Command::new(lake())
        .current_dir(wurzel().join("grammatik"))
        .env_remove("ELAN_TOOLCHAIN")
        .args(["env", "lean", "-j2", "-M6144", "--run", "Grammatik/Parser/Cover/DifferenzLauf.lean"])
        .arg(dir)
        .output()
        .map_err(|e| format!("`lake env lean --run` could not run: {e}"))?;
    let aus = String::from_utf8_lossy(&out.stdout).into_owned();
    let _ = std::fs::write(dir.with_extension("log"), format!("{aus}\n---\n{}", String::from_utf8_lossy(&out.stderr)));
    let mut m = std::collections::BTreeMap::new();
    for l in aus.lines() {
        let Some((name, v)) = l.split_once('\t') else { continue };
        let Some(n) = name.strip_prefix('p').and_then(|s| s.strip_suffix(".gab")).and_then(|s| s.parse::<usize>().ok())
        else {
            continue;
        };
        let v = match v {
            "accept" => PurV::Accept,
            "reject" => PurV::Reject,
            other if PUR_VERLETZT.iter().any(|p| other.contains(p)) => PurV::Verletzt(other.chars().take(120).collect()),
            other => PurV::KeinForm(other.chars().take(120).collect()),
        };
        m.insert(n, v);
    }
    Ok(m)
}

/// The Lean verdicts of one batch, in the order of `stuecke`.
pub fn lean_stapel(stuecke: &[Stueck], datei: &Path) -> Result<Vec<LeanV>, String> {
    let (text, bereiche) = stapel_datei(stuecke);
    std::fs::write(datei, &text).map_err(|e| format!("cannot write {}: {e}", datei.display()))?;
    let (aus, fehl) = lean_lauf(datei)?;
    let mut urteil: Vec<LeanV> = vec![LeanV::NotRun; stuecke.len()];
    for (i, s) in stuecke.iter().enumerate() {
        let marke = format!("DIFF {} ", s.ns);
        if let Some(l) = aus.lines().find(|l| l.starts_with(&marke)) {
            urteil[i] = if l.ends_with("true") { LeanV::Accept } else { LeanV::Reject };
        }
    }
    let _ = std::fs::write(datei.with_extension("log"), format!("{aus}\n---\n{fehl}"));
    // Errors are attributed by line. Lean prints them on stdout and stderr depending on the
    // version; read both.
    let alles = format!("{aus}\n{fehl}");
    let name = datei.file_name().and_then(|n| n.to_str()).unwrap_or("");
    let mut ersterfehler: Vec<Option<String>> = vec![None; stuecke.len()];
    for l in alles.lines() {
        if !l.contains(": error:") && !l.contains(": error(") {
            continue;
        }
        let Some(rest) = l.find(name).map(|p| &l[p + name.len()..]) else { continue };
        let Some(zeile) = rest.trim_start_matches(':').split(':').next().and_then(|n| n.parse::<usize>().ok())
        else {
            continue;
        };
        if let Some(i) = bereiche.iter().position(|(a, b)| zeile >= *a && zeile <= *b) {
            if ersterfehler[i].is_none() {
                let m = l.find(": error").map(|k| &l[k + 2..]).unwrap_or(l);
                ersterfehler[i] = Some(format!("L{}: {}", zeile - bereiche[i].0 + 1, m.chars().take(220).collect::<String>()));
            }
        }
    }
    for (i, e) in ersterfehler.into_iter().enumerate() {
        if let Some(e) = e {
            urteil[i] = if e.contains("proved that the proposition") {
                LeanV::Elab(e)
            } else {
                LeanV::Defekt(e)
            };
        } else if urteil[i] == LeanV::NotRun {
            urteil[i] = LeanV::Defekt("no verdict line and no error (Lean run aborted?)".to_string());
        }
    }
    Ok(urteil)
}
