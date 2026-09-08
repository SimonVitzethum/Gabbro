//! **THE PERSON'S HALF, MEASURED -- `gabbro beweise`** (2026-09-07).
//!
//! `lean::module` writes a unit's duties as `_statement`s and proves each with
//! `gabbro_auto`, which closes what the model closes by computation and leaves a `sorry` on
//! what is the program's own logic. This file holds the OTHER half against it: a file
//! `Proofs/<Unit>.lean`, written by a person, with one theorem per statement -- and the
//! unit is GREEN only when every statement of the unit has a proof, and no proof uses a
//! `sorry`.
//!
//! ```text
//! unit.gab  ->  lean::module  ->  <model>/Duty/<Unit>.lean      (generated, never edited)
//!                                 <model>/Proofs/<Unit>.lean    (written by a person)
//!               lean Duty/<Unit>.lean ; lean Proofs/<Unit>.lean  ->  green
//! ```
//!
//! **Why this stands in the checker and not only in a shell script.** `gabbro emit
//! --mit-beweis` refuses to write C for a unit that still owes a proof, and a refusal the
//! emitter makes has to rest on a measurement the checker makes -- the same one, in the
//! same process, with the same words. The script `instrumente/pruefe-lean-pflichten.sh`
//! is the same measurement for a whole tree at once.
//!
//! What is run is `lean` itself (`$LEANBIN`, else `~/.elan/bin/lean`), against the model
//! built by `lake` in the model folder (`programmlogik/`, found by walking up from the
//! unit's file, or named with `--modell`). **Nothing here trusts a timestamp**: the model
//! is rebuilt by `lake` on every run, which is cheap when nothing changed, and the generated
//! half is compiled afresh every time.

use std::path::{Path, PathBuf};
use std::process::Command;

use gabbro_syntax::ast::Programm;

/// How a unit stands.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Stand {
    /// Every statement has a proof without a `sorry` -- by the generator, or by a person.
    Gruen,
    /// Statements are left to a person, and not all of them are proved.
    Geschuldet,
    /// The generated half or the person's half does not compile -- the TREE has to change.
    Rot,
    /// No Lean, no model, the model does not build -- the SETUP has to change, and nothing
    /// was measured.
    Aufbau,
}

/// The measurement of one unit.
#[derive(Debug, Clone)]
pub struct Befund {
    pub einheit: String,
    pub stand: Stand,
    /// Every `_statement` of the unit.
    pub statements: Vec<String>,
    /// The statements `gabbro_auto` closed by itself.
    pub geschlossen: Vec<String>,
    /// The statements a person has proved (in `Proofs/<Unit>.lean`, without `sorry`).
    pub bewiesen: Vec<String>,
    /// The statements still owed -- no theorem, or one with a `sorry`.
    pub geschuldet: Vec<String>,
    /// Where the person's file is expected.
    pub beweisdatei: PathBuf,
    /// What went wrong, where `stand` is `Rot` or `Aufbau` -- the first lines of it.
    pub meldung: String,
}

impl Befund {
    /// One line per unit, in the words every guardian of this tree uses.
    pub fn zeile(&self) -> String {
        match self.stand {
            Stand::Gruen if self.bewiesen.is_empty() => format!(
                "   GREEN  {} -- {} statement(s), all closed by the generator; nothing owed",
                self.einheit,
                self.statements.len()
            ),
            Stand::Gruen => format!(
                "   GREEN  {} -- {} statement(s), {} proved by a person, none owed",
                self.einheit,
                self.statements.len(),
                self.bewiesen.len()
            ),
            Stand::Geschuldet => format!(
                "   OWED   {} -- {} of {} statement(s) left to a person: {}\n          proofs go into {}",
                self.einheit,
                self.geschuldet.len(),
                self.statements.len(),
                self.geschuldet.join(", "),
                self.beweisdatei.display()
            ),
            Stand::Rot => format!("   RED    {}\n{}", self.einheit, indent(&self.meldung)),
            Stand::Aufbau => format!("   SETUP  {} -- {}", self.einheit, self.meldung),
        }
    }
}

fn indent(s: &str) -> String {
    s.lines().take(8).map(|l| format!("          {l}")).collect::<Vec<_>>().join("\n")
}

/// **The model folder for a unit**: `--modell` if given, else `programmlogik/` found by
/// walking up from the unit's file -- the folder that holds `Gabbro/Body.lean`.
pub fn modell_finden(datei: &str, genannt: Option<&str>) -> Option<PathBuf> {
    if let Some(m) = genannt {
        let p = PathBuf::from(m);
        return if p.join("Gabbro/Body.lean").is_file() { Some(p) } else { None };
    }
    let mut dir = Path::new(datei).canonicalize().ok()?;
    dir.pop();
    loop {
        let kandidat = dir.join("programmlogik");
        if kandidat.join("Gabbro/Body.lean").is_file() {
            return Some(kandidat);
        }
        if !dir.pop() {
            return None;
        }
    }
}

fn elan_bin(name: &str, env: &str) -> Option<PathBuf> {
    if let Ok(p) = std::env::var(env) {
        let p = PathBuf::from(p);
        return if p.is_file() { Some(p) } else { None };
    }
    let home = std::env::var("HOME").ok()?;
    let p = Path::new(&home).join(".elan/bin").join(name);
    if p.is_file() {
        Some(p)
    } else {
        None
    }
}

/// `$LEANBIN`, else `~/.elan/bin/lean`.
pub fn lean_binaer() -> Option<PathBuf> {
    elan_bin("lean", "LEANBIN")
}

/// `$LAKE`, else `~/.elan/bin/lake`.
pub fn lake_binaer() -> Option<PathBuf> {
    elan_bin("lake", "LAKE")
}

/// **The model, built.** `lake build Gabbro.Body` in the model folder -- cheap when nothing
/// changed, and the only way to know the `.olean` matches the source.
fn modell_bauen(modell: &Path) -> Result<(), String> {
    let lake = lake_binaer().ok_or("no `lake` (set $LAKE, or install elan)")?;
    let out = Command::new(&lake)
        .arg("build")
        .arg("Gabbro.Body")
        .current_dir(modell)
        .output()
        .map_err(|e| format!("`lake build Gabbro.Body` could not run: {e}"))?;
    if out.status.success() {
        Ok(())
    } else {
        let text = String::from_utf8_lossy(&out.stderr).to_string() + &String::from_utf8_lossy(&out.stdout);
        Err(format!("the MODEL does not build -- nothing measured:\n{}", text.lines().take(6).collect::<Vec<_>>().join("\n")))
    }
}

/// The lines of a Lean run that are errors -- `file:line:col: error: …` and the newer
/// `error(kind):` form alike.
fn fehlerzeilen(ausgabe: &str) -> Vec<String> {
    ausgabe
        .lines()
        .filter(|l| {
            let Some(rest) = l.splitn(4, ':').nth(3) else { return false };
            rest.trim_start().starts_with("error")
        })
        .map(|l| l.to_string())
        .collect()
}

/// The line numbers of the `declaration uses \`sorry\`` warnings.
fn sorry_zeilen(ausgabe: &str) -> Vec<usize> {
    ausgabe
        .lines()
        .filter(|l| l.contains("declaration uses `sorry`"))
        .filter_map(|l| l.split(':').nth(1).and_then(|n| n.parse().ok()))
        .collect()
}

/// The theorem declared at a line: `theorem NAME : …`.
fn theorem_bei(text: &str, zeile: usize) -> Option<String> {
    let l = text.lines().nth(zeile.checked_sub(1)?)?;
    let rest = l.strip_prefix("theorem ")?;
    Some(rest.split(|c: char| c == ' ' || c == ':').next()?.to_string())
}

/// Every `def NAME_statement : Prop :=` of a generated module.
fn statements_von(text: &str) -> Vec<String> {
    text.lines()
        .filter_map(|l| {
            let rest = l.strip_prefix("def ")?;
            let name = rest.split(' ').next()?;
            if name.ends_with("_statement") && rest.contains(": Prop :=") {
                Some(name.to_string())
            } else {
                None
            }
        })
        .collect()
}

fn lean_lauf(lean: &Path, lean_path: &str, datei: &Path, olean: Option<&Path>) -> Result<String, String> {
    let mut cmd = Command::new(lean);
    cmd.env("LEAN_PATH", lean_path);
    if let Some(o) = olean {
        cmd.arg("-o").arg(o);
    }
    cmd.arg(datei);
    let out = cmd.output().map_err(|e| format!("`lean` could not run: {e}"))?;
    Ok(String::from_utf8_lossy(&out.stdout).to_string() + &String::from_utf8_lossy(&out.stderr))
}

/// **The measurement of one unit.** `Err` only where the SETUP is wrong (no Lean, no
/// model); everything about the tree comes back as a `Befund`.
pub fn pruefe(baum: &Programm, datei: &str, modell: &Path) -> Result<Befund, String> {
    let lean = lean_binaer().ok_or("no `lean` (set $LEANBIN, or install elan)")?;
    modell_bauen(modell)?;
    let text = crate::lean::module(baum, datei);
    let name = crate::lean::module_name(datei);
    let duty_dir = modell.join("Duty");
    let proofs_dir = modell.join("Proofs");
    let out_dir = modell.join(".lake/build/duty");
    std::fs::create_dir_all(&duty_dir).map_err(|e| e.to_string())?;
    std::fs::create_dir_all(&proofs_dir).map_err(|e| e.to_string())?;
    std::fs::create_dir_all(out_dir.join("Duty")).map_err(|e| e.to_string())?;
    let duty = duty_dir.join(format!("{name}.lean"));
    std::fs::write(&duty, &text).map_err(|e| e.to_string())?;
    let lib = modell.join(".lake/build/lib/lean");
    let lib_s = lib.to_string_lossy().to_string();
    let beweisdatei = proofs_dir.join(format!("{name}.lean"));
    let statements = statements_von(&text);
    let mut befund = Befund {
        einheit: name.clone(),
        stand: Stand::Gruen,
        statements: statements.clone(),
        geschlossen: Vec::new(),
        bewiesen: Vec::new(),
        geschuldet: Vec::new(),
        beweisdatei: beweisdatei.clone(),
        meldung: String::new(),
    };
    // the generated half -- red here is the generator's fault, not the person's
    let olean = out_dir.join("Duty").join(format!("{name}.olean"));
    let ausgabe = lean_lauf(&lean, &lib_s, &duty, Some(&olean))?;
    let fehler = fehlerzeilen(&ausgabe);
    if !fehler.is_empty() {
        befund.stand = Stand::Rot;
        befund.meldung = format!("the GENERATED half does not compile ({}):\n{}", duty.display(), fehler.join("\n"));
        return Ok(befund);
    }
    let mut geschuldet: Vec<String> = sorry_zeilen(&ausgabe)
        .into_iter()
        .filter_map(|z| theorem_bei(&text, z))
        .map(|t| format!("{t}_statement"))
        .collect();
    geschuldet.sort();
    geschuldet.dedup();
    befund.geschlossen = statements.iter().filter(|s| !geschuldet.contains(s)).cloned().collect();
    if geschuldet.is_empty() {
        return Ok(befund);
    }
    if !beweisdatei.is_file() {
        befund.geschuldet = geschuldet;
        befund.stand = Stand::Geschuldet;
        return Ok(befund);
    }
    // the person's half
    let beweise = std::fs::read_to_string(&beweisdatei).map_err(|e| e.to_string())?;
    let lp = format!("{}:{}", lib_s, out_dir.to_string_lossy());
    let ausgabe = lean_lauf(&lean, &lp, &beweisdatei, None)?;
    let fehler = fehlerzeilen(&ausgabe);
    if !fehler.is_empty() {
        befund.stand = Stand::Rot;
        befund.meldung = format!("the PROOFS do not compile ({}):\n{}", beweisdatei.display(), fehler.join("\n"));
        return Ok(befund);
    }
    let mit_sorry: Vec<String> = sorry_zeilen(&ausgabe)
        .into_iter()
        .filter_map(|z| theorem_bei(&beweise, z))
        .collect();
    for st in geschuldet {
        // a theorem whose type is the statement, and none of the `sorry`-ed ones
        let bewiesen = beweise.lines().any(|l| {
            l.starts_with("theorem ")
                && l.contains(&format!(": {st}"))
                && !mit_sorry.iter().any(|t| l.starts_with(&format!("theorem {t} ")) || l.starts_with(&format!("theorem {t}:")))
        });
        if bewiesen {
            befund.bewiesen.push(st);
        } else {
            befund.geschuldet.push(st);
        }
    }
    if !befund.geschuldet.is_empty() {
        befund.stand = Stand::Geschuldet;
    }
    Ok(befund)
}

/// **A template for the person's file**: one theorem per statement, each with a `sorry`
/// to start from.
pub fn vorlage(baum: &Programm, datei: &str) -> String {
    let text = crate::lean::module(baum, datei);
    let name = crate::lean::module_name(datei);
    let mut s = String::new();
    s.push_str(&format!("import Duty.{name}\n"));
    s.push_str("set_option autoImplicit false\n");
    s.push_str(&format!("open Gabbro.Body GabbroDuty.{name}\n\n"));
    s.push_str("/-  Written from `gabbro beweise --vorlage`. Every statement below is the unit's own\n");
    s.push_str("    logic; the hypotheses a proof needs stand in the statement. `gabbro_auto?` shows\n");
    s.push_str("    what the model leaves after its own steps. -/\n\n");
    for st in statements_von(&text) {
        let th = st.trim_end_matches("_statement");
        s.push_str(&format!("theorem {th}_done : {st} := by\n"));
        // **The generated proof script, up to the automation** -- the openings the person
        // would otherwise write again -- and then the pipeline, which leaves exactly what
        // is theirs.
        let mut im_beweis = false;
        for l in text.lines() {
            if l.starts_with(&format!("theorem {th} ")) || l.starts_with(&format!("theorem {th}:")) {
                im_beweis = true;
                continue;
            }
            if !im_beweis {
                continue;
            }
            if l.trim().is_empty() {
                break;
            }
            if l.contains("gabbro_auto ") {
                let indent = &l[..l.len() - l.trim_start().len()];
                s.push_str(&l.replace("gabbro_auto ", "gabbro_pipeline "));
                s.push('\n');
                s.push_str(&format!("{indent}-- what is left here is the unit's own logic (`gabbro_auto?` shows it)\n"));
                s.push_str(&format!("{indent}all_goals sorry\n"));
                break;
            }
            s.push_str(l);
            s.push('\n');
        }
        s.push('\n');
    }
    s
}
