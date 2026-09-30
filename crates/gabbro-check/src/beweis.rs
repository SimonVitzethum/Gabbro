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
            ) + &if self.meldung.is_empty() { String::new() } else { format!("\n{}", indent(&self.meldung)) },
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

/// One Lean run: its whole output, and whether it EXITED successfully.
///
/// **It runs in the model folder**, because `~/.elan/bin/lean` is elan's proxy and picks the
/// toolchain from the `lean-toolchain` file of the directory it starts in. Started from
/// wherever `gabbro prove` was called, the proxy found no toolchain, printed
/// `error: no default toolchain configured` -- a line without `file:line:col:` -- and exited 1;
/// the parser below saw no error and no `sorry`, and the unit came out GREEN without a single
/// line of Lean having been checked (server lane, 2026-09-29, on `firewall/regeln.gab` of
/// `~/gabbro-netz`: GREEN in 3 s, where a real run takes 6 min and leaves nine duties owed).
/// The exit status is therefore part of the answer, not a detail.
fn lean_lauf(lean: &Path, lean_path: &str, datei: &Path, olean: Option<&Path>, ort: &Path) -> Result<(String, bool), String> {
    let mut cmd = Command::new(lean);
    cmd.env("LEAN_PATH", lean_path);
    cmd.current_dir(ort);
    if let Some(o) = olean {
        cmd.arg("-o").arg(o);
    }
    cmd.arg(datei);
    let out = cmd.output().map_err(|e| format!("`lean` could not run: {e}"))?;
    Ok((String::from_utf8_lossy(&out.stdout).to_string() + &String::from_utf8_lossy(&out.stderr), out.status.success()))
}

/// **A Lean run that failed without saying where** -- a non-zero exit and no error line with a
/// position. That is the SETUP failing (a toolchain, a path, a crash), and nothing about the
/// tree was measured: it may neither be GREEN nor be blamed on the tree.
fn ohne_ort(ausgabe: &str, erfolg: bool) -> Option<String> {
    if erfolg || !fehlerzeilen(ausgabe).is_empty() {
        return None;
    }
    let kopf: Vec<&str> = ausgabe.lines().filter(|l| !l.trim().is_empty()).take(4).collect();
    Some(format!("`lean` exited unsuccessfully and named no position -- nothing was measured:\n{}", kopf.join("\n")))
}

/// **The measurement of one unit.** `Err` only where the SETUP is wrong (no Lean, no
/// model); everything about the tree comes back as a `Befund`.
pub fn pruefe(baum: &Programm, datei: &str, modell: &Path) -> Result<Befund, String> {
    let lean = lean_binaer().ok_or("no `lean` (set $LEANBIN, or install elan)")?;
    // Absolute, because Lean runs INSIDE the model folder (`lean_lauf`) and every path handed
    // to it must mean the same thing there.
    let modell_abs = modell.canonicalize().map_err(|e| format!("the model folder {}: {e}", modell.display()))?;
    let modell: &Path = &modell_abs;
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
    // The `.olean` is the run's RECEIPT: removed first, it can only exist afterwards if this run
    // compiled the module. A run that exits cleanly and leaves none checked nothing.
    let _ = std::fs::remove_file(&olean);
    let (ausgabe, erfolg) = lean_lauf(&lean, &lib_s, &duty, Some(&olean), modell)?;
    if let Some(m) = ohne_ort(&ausgabe, erfolg) {
        befund.stand = Stand::Aufbau;
        befund.meldung = m;
        return Ok(befund);
    }
    let fehler = fehlerzeilen(&ausgabe);
    if !fehler.is_empty() {
        befund.stand = Stand::Rot;
        befund.meldung = format!("the GENERATED half does not compile ({}):\n{}", duty.display(), fehler.join("\n"));
        return Ok(befund);
    }
    if !olean.is_file() {
        befund.stand = Stand::Aufbau;
        befund.meldung = format!("`lean` reported success and wrote no `{}` -- nothing was measured", olean.display());
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
    // the person's half
    let lp = format!("{}:{}", lib_s, out_dir.to_string_lossy());
    let beweise_olean = out_dir.join("Proofs").join(format!("{name}.olean"));
    let _ = std::fs::remove_file(&beweise_olean);
    let hat_beweise = beweisdatei.is_file();
    if hat_beweise {
        std::fs::create_dir_all(out_dir.join("Proofs")).map_err(|e| e.to_string())?;
        let (ausgabe, erfolg) = lean_lauf(&lean, &lp, &beweisdatei, Some(&beweise_olean), modell)?;
        if let Some(m) = ohne_ort(&ausgabe, erfolg) {
            befund.stand = Stand::Aufbau;
            befund.meldung = m;
            return Ok(befund);
        }
        let fehler = fehlerzeilen(&ausgabe);
        if !fehler.is_empty() {
            befund.stand = Stand::Rot;
            befund.meldung = format!("the PROOFS do not compile ({}):\n{}", beweisdatei.display(), fehler.join("\n"));
            return Ok(befund);
        }
        if !beweise_olean.is_file() {
            befund.stand = Stand::Aufbau;
            befund.meldung = format!("`lean` reported success and wrote no `{}` -- nothing was measured", beweise_olean.display());
            return Ok(befund);
        }
    }
    // **The gate.** What is checked is not a line of text in the person's file but a GATE FILE
    // written here: one theorem per statement, whose TYPE is the generated statement, spelled
    // out in full, and whose proof is the generator's theorem or the person's `<th>_done` --
    // then `#print axioms` of each. A proof of another statement fails to elaborate; a `sorry`,
    // an `axiom` of the person's, `native_decide` (`Lean.ofReduceBool`) or any classical escape
    // shows up as an axiom outside the three standard ones. Nothing here reads a warning.
    let standard = ["propext", "Classical.choice", "Quot.sound"];
    let mut tor = String::new();
    tor.push_str(&format!("import Duty.{name}\n"));
    if hat_beweise {
        tor.push_str(&format!("import Proofs.{name}\n"));
    }
    tor.push_str("set_option autoImplicit false\n");
    let mut zeilen_von: Vec<(usize, usize)> = Vec::new(); // (Lean line, index of the statement)
    let mut zeile = tor.lines().count();
    for (k, st) in statements.iter().enumerate() {
        let th = st.trim_end_matches("_statement");
        let beweis = if geschuldet.contains(st) {
            if hat_beweise { format!("{th}_done") } else { "sorry".to_string() }
        } else {
            format!("GabbroDuty.{name}.{th}")
        };
        tor.push_str(&format!("theorem gate_{k} : GabbroDuty.{name}.{st} := {beweis}\n"));
        tor.push_str(&format!("#print axioms gate_{k}\n"));
        zeilen_von.push((zeile + 1, k));
        zeilen_von.push((zeile + 2, k));
        zeile += 2;
    }
    if text.contains("theorem unit_closed ") {
        tor.push_str(&format!("#print axioms GabbroDuty.{name}.unit_closed\n"));
    }
    let tor_datei = out_dir.join(format!("Gate{name}.lean"));
    std::fs::write(&tor_datei, &tor).map_err(|e| e.to_string())?;
    let (ausgabe, erfolg) = lean_lauf(&lean, &lp, &tor_datei, None, modell)?;
    if let Some(m) = ohne_ort(&ausgabe, erfolg) {
        befund.stand = Stand::Aufbau;
        befund.meldung = m;
        return Ok(befund);
    }
    // the statements whose gate theorem did not elaborate (no proof, or a proof of another statement)
    let mut ohne_beweis: Vec<usize> = Vec::new();
    let mut sonst_fehler: Vec<String> = Vec::new();
    for l in fehlerzeilen(&ausgabe) {
        let zl: Option<usize> = l.split(':').nth(1).and_then(|n| n.parse().ok());
        match zl.and_then(|z| zeilen_von.iter().find(|(lz, _)| *lz == z)) {
            Some((_, k)) => {
                if !ohne_beweis.contains(k) {
                    ohne_beweis.push(*k);
                }
            }
            None => sonst_fehler.push(l),
        }
    }
    // The axioms each `#print axioms gate_k` reported. **Fail-closed:** a theorem that elaborated
    // and has no report line means the run did not say what it depends on -- nothing measured.
    let mut schlecht_axiom: Vec<(usize, String)> = Vec::new();
    for (k, _) in statements.iter().enumerate() {
        if ohne_beweis.contains(&k) {
            continue;
        }
        let marke = format!("'gate_{k}'");
        let Some(i) = ausgabe.find(&marke) else {
            befund.stand = Stand::Aufbau;
            befund.meldung = format!("`lean` reported no axioms for `gate_{k}` -- nothing was measured");
            return Ok(befund);
        };
        let rest = &ausgabe[i + marke.len()..];
        let ende = rest.find("\n'").unwrap_or(rest.len());
        let stueck = &rest[..ende];
        if stueck.contains("does not depend on any axioms") {
            continue;
        }
        let Some(o) = stueck.find('[') else {
            befund.stand = Stand::Aufbau;
            befund.meldung = format!("the axiom report of `gate_{k}` is not in a form this gate reads -- nothing was measured");
            return Ok(befund);
        };
        let Some(c) = stueck.find(']') else {
            befund.stand = Stand::Aufbau;
            befund.meldung = format!("the axiom report of `gate_{k}` is not in a form this gate reads -- nothing was measured");
            return Ok(befund);
        };
        let fremd: Vec<&str> = stueck[o + 1..c]
            .split(',')
            .map(|a| a.trim())
            .filter(|a| !a.is_empty() && !standard.contains(a))
            .collect();
        if !fremd.is_empty() {
            schlecht_axiom.push((k, fremd.join(", ")));
        }
    }
    if let Some(i) = ausgabe.find("unit_closed' depends on axioms") {
        let stueck = &ausgabe[i..];
        if let (Some(o), Some(c)) = (stueck.find('['), stueck.find(']')) {
            let fremd: Vec<&str> = stueck[o + 1..c]
                .split(',')
                .map(|a| a.trim())
                .filter(|a| !a.is_empty() && !standard.contains(a))
                .collect();
            if !fremd.is_empty() {
                sonst_fehler.push(format!("`unit_closed` depends on axioms outside the standard three: {}", fremd.join(", ")));
            }
        }
    }
    // a GENERATED statement that fails the gate is the tree's fault; an owed one only stays owed
    let mut rot: Vec<String> = sonst_fehler;
    let mut grund_geschuldet: Vec<String> = Vec::new();
    for (k, st) in statements.iter().enumerate() {
        let owed = geschuldet.contains(st);
        let kaputt = ohne_beweis.contains(&k) || schlecht_axiom.iter().any(|(j, _)| *j == k);
        if owed {
            if kaputt || !hat_beweise {
                befund.geschuldet.push(st.clone());
                if !hat_beweise {
                } else if let Some((_, a)) = schlecht_axiom.iter().find(|(j, _)| *j == k) {
                    grund_geschuldet.push(format!("`{st}`: the proof depends on {a}"));
                } else if ohne_beweis.contains(&k) && hat_beweise {
                    grund_geschuldet.push(format!("`{st}`: no theorem `{}_done` of exactly this statement", st.trim_end_matches("_statement")));
                }
            } else {
                befund.bewiesen.push(st.clone());
            }
        } else if kaputt {
            let grund = schlecht_axiom.iter().find(|(j, _)| *j == k).map(|(_, a)| a.clone()).unwrap_or_else(|| "did not elaborate".into());
            rot.push(format!("the generated theorem of `{st}` fails the gate: {grund}"));
        }
    }
    befund.geschlossen = statements.iter().filter(|s| !geschuldet.contains(s)).cloned().collect();
    if !rot.is_empty() {
        befund.stand = Stand::Rot;
        befund.meldung = rot.join("\n");
        return Ok(befund);
    }
    if !befund.geschuldet.is_empty() {
        befund.stand = Stand::Geschuldet;
        befund.meldung = grund_geschuldet.join("\n");
    }
    Ok(befund)
}

/// **The bridge folder** (`bruecke/lakefile.toml`): `genannt` if given, else found by walking up
/// from the unit's file.
pub fn bruecke_finden(datei: &str, genannt: Option<&str>) -> Option<PathBuf> {
    if let Some(m) = genannt {
        let p = PathBuf::from(m);
        return if p.join("lakefile.toml").is_file() { Some(p) } else { None };
    }
    let mut dir = Path::new(datei).canonicalize().ok()?;
    dir.pop();
    loop {
        let kandidat = dir.join("bruecke");
        if kandidat.join("Bruecke/Vorlage.lean").is_file() {
            return Some(kandidat);
        }
        if !dir.pop() {
            return None;
        }
    }
}

/// A Lean string literal for `s`: quotes, backslashes and control characters escaped, everything
/// else (UTF-8 included) verbatim -- the text a person's file pins must be the file's bytes.
fn lean_literal(s: &str) -> String {
    let mut o = String::with_capacity(s.len() + 2);
    o.push('"');
    for c in s.chars() {
        match c {
            '"' => o.push_str("\\\""),
            '\\' => o.push_str("\\\\"),
            '\n' => o.push_str("\\n"),
            '\r' => o.push_str("\\r"),
            '\t' => o.push_str("\\t"),
            c if (c as u32) < 0x20 || c as u32 == 0x7f => o.push_str(&format!("\\x{:02x}", c as u32)),
            c => o.push(c),
        }
    }
    o.push('"');
    o
}

/// **The template pinned to the SOURCE TEXT** (`gabbro prove --template --source`): the file a
/// person starts from when the duties are to be stated by Lean and not by this program. Nothing
/// of the statement is written here -- `Bruecke/Vorlage.lean` (`vorlage`) runs the Lean front end
/// over the text and prints the pinned source, the stage hints and the computed duties; this
/// function only hands it the text and returns what it printed. A text the Lean front end
/// refuses comes back as a `-- REFUSED …` comment naming the stage, never as duties.
pub fn vorlage_quelle(quelle: &str, datei: &str, bruecke: Option<&str>) -> Result<String, String> {
    let b = bruecke_finden(datei, bruecke)
        .ok_or("no bridge folder (`bruecke/Bruecke/Vorlage.lean`) above the file -- name one with `--bridge <dir>`")?;
    let lake = lake_binaer().ok_or("no `lake` (set $LAKE, or install elan)")?;
    let gebaut = Command::new(&lake)
        .args(["build", "Bruecke.Vorlage"])
        .current_dir(&b)
        .output()
        .map_err(|e| format!("`lake build Bruecke.Vorlage` could not run: {e}"))?;
    if !gebaut.status.success() {
        let text = String::from_utf8_lossy(&gebaut.stderr).to_string() + &String::from_utf8_lossy(&gebaut.stdout);
        return Err(format!("the BRIDGE does not build -- nothing written:\n{}", text.lines().take(6).collect::<Vec<_>>().join("\n")));
    }
    let name = crate::lean::module_name(datei);
    let treiber = std::env::temp_dir().join(format!("gabbro-vorlage-{}.lean", std::process::id()));
    let inhalt = format!(
        "import Bruecke.Vorlage\n#eval IO.println (Gabbro.Bruecke.vorlage {} {})\n",
        lean_literal(&name),
        lean_literal(quelle)
    );
    std::fs::write(&treiber, inhalt).map_err(|e| format!("driver not writable: {e}"))?;
    let lauf = Command::new(&lake).args(["env", "lean"]).arg(&treiber).current_dir(&b).output();
    let _ = std::fs::remove_file(&treiber);
    let lauf = lauf.map_err(|e| format!("lean could not run: {e}"))?;
    if !lauf.status.success() {
        let text = String::from_utf8_lossy(&lauf.stdout).to_string() + &String::from_utf8_lossy(&lauf.stderr);
        return Err(format!("the template writer failed:\n{}", text.lines().take(8).collect::<Vec<_>>().join("\n")));
    }
    Ok(String::from_utf8_lossy(&lauf.stdout).to_string())
}

/// **A template for the person's file**: one theorem per statement, each with a `sorry`
/// to start from.
pub fn vorlage(baum: &Programm, datei: &str) -> String {
    let text = crate::lean::module(baum, datei);
    let name = crate::lean::module_name(datei);
    let mut s = String::new();
    s.push_str(&format!("import Duty.{name}\n"));
    // The pipeline's own budget (`PLAN.md` §3.3): the generated file carries it, and a proof file
    // that starts from the default 200 000 dies in `gabbro_pipeline` on the first call chain of any
    // size -- a message about the apparatus, not the unit (GabbroV lane, 2026-09-29).
    s.push_str("set_option autoImplicit false\nset_option maxHeartbeats 11300000\n");
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
            if l.contains("gabbro_auto2 ") {
                // `gabbro_auto2 [first] [second] using t`: the pipeline, and once more on what
                // it left -- spelled out, so the person sees the goals AFTER both passes
                // the lines after the pipeline stand at the block's own column (2), also when the
                // pipeline itself is the continuation `    <;> …` of a split
                let indent = "  ";
                let at = l.find("gabbro_auto2 ").unwrap_or(0);
                let (before, tail) = l.split_at(at);
                let (a, rest) = tail.trim_start_matches("gabbro_auto2 ").split_once("] [").unwrap_or((tail, ""));
                let (b, _) = rest.split_once("] using").unwrap_or((rest, ""));
                s.push_str(&format!("{before}gabbro_pipeline {}] using shapeOf\n", a.trim_end()));
                s.push_str(&format!("{indent}all_goals (try (gabbro_pipeline [{b}] using shapeOf))\n"));
                s.push_str(&format!("{indent}-- what is left here is the unit's own logic (`gabbro_auto?` shows it)\n"));
                s.push_str(&format!("{indent}all_goals sorry\n"));
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
