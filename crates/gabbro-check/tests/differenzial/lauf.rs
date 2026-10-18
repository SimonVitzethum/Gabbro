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
    /// The export does not elaborate (first error line).
    Elab(String),
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
            urteil[i] = LeanV::Elab(e);
        } else if urteil[i] == LeanV::NotRun {
            urteil[i] = LeanV::Elab("no verdict line and no error (Lean run aborted?)".to_string());
        }
    }
    Ok(urteil)
}
