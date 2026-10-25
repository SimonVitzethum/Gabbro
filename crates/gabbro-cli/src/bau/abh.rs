//! **Dependencies: the project graph** (`dokumente/BUILD-SYSTEM.md` §7.3/§7.4).
//!
//! Every `dependency(...)` of a project resolves to a COPY: a project directory evaluated in a
//! scope of its own, with its own options (`options:` of the call, `-D<project>:<option>=<value>`)
//! and the program's `target` and `buildtype`. One project reached twice with the same source
//! and the same options is ONE copy; two versions of one project are two copies, each with its
//! own name space; the same version from two sources, or with two option sets, is refused (a
//! unit cannot know which one a path meant). A CYCLE of projects is refused: a project cannot be
//! configured before itself. Mutual calls are no cycle of projects -- they are callbacks.
//!
//! **`gabbro.lock`** (written by `setup` and `configure`, checked by every `compile`) records
//! per copy the path, version, options and a content fingerprint of every file it may bring;
//! a dependency that changed under the build is a refusal that names it, never a silent swap.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use super::einheit::abdruck64;
use super::sprache::{self, Projekt, Versionsbereich, Wert};

pub const LOCKDATEI: &str = "gabbro.lock";

/// One project in the build: the program (copy 0) or one copy of a dependency.
pub struct Kopie {
    /// The name space of the copy: the head every path into it starts with in the unit.
    pub ident: String,
    pub projekt: Projekt,
    pub werte: BTreeMap<String, Wert>,
    /// Per entry of `projekt.abhaengigkeiten`, the copy it resolved to.
    pub deps: Vec<usize>,
    /// The canonical build file.
    pub kanon: PathBuf,
    /// The project's own options as set (sorted): part of the copy's identity.
    pub optionen: Vec<(String, String)>,
}

pub struct Graph {
    pub kopien: Vec<Kopie>,
}

impl Graph {
    pub fn wurzel(&self) -> &Projekt {
        &self.kopien[0].projekt
    }
}

/// Splits `-D` settings into the program's own and those for a dependency (`<project>:<name>`).
pub fn trenne(gesetzt: &BTreeMap<String, String>) -> (BTreeMap<String, String>, BTreeMap<String, BTreeMap<String, String>>) {
    let mut eigen = BTreeMap::new();
    let mut fremd: BTreeMap<String, BTreeMap<String, String>> = BTreeMap::new();
    for (k, v) in gesetzt {
        match k.split_once(':') {
            Some((p, o)) => {
                fremd.entry(p.to_string()).or_default().insert(o.to_string(), v.clone());
            }
            None => {
                eigen.insert(k.clone(), v.clone());
            }
        }
    }
    (eigen, fremd)
}

/// **Resolves the project graph** below the program `wurzel`.
pub fn loese(
    wurzel: Projekt,
    werte: BTreeMap<String, Wert>,
    kanon: PathBuf,
    fremd: &BTreeMap<String, BTreeMap<String, String>>,
) -> Result<Graph, String> {
    let mut g = Graph {
        kopien: vec![Kopie {
            ident: String::new(),
            projekt: wurzel,
            werte,
            deps: Vec::new(),
            kanon: kanon.clone(),
            optionen: Vec::new(),
        }],
    };
    let mut stapel = vec![kanon];
    besuche(&mut g, 0, &mut stapel, fremd)?;
    for (p, _) in fremd {
        if !g.kopien.iter().skip(1).any(|k| &k.projekt.name == p) {
            return Err(format!("`-D{p}:…`: `{p}` is no dependency of this build"));
        }
    }
    vergib_namen(&mut g);
    Ok(g)
}

fn besuche(
    g: &mut Graph,
    idx: usize,
    stapel: &mut Vec<PathBuf>,
    fremd: &BTreeMap<String, BTreeMap<String, String>>,
) -> Result<(), String> {
    let abhs = g.kopien[idx].projekt.abhaengigkeiten.clone();
    let wurzel = g.kopien[idx].projekt.wurzel.clone();
    let (ziel, bautyp) = (g.kopien[0].werte["target"].clone(), g.kopien[0].werte["buildtype"].clone());
    for a in abhs {
        let dir = wurzel.join(&a.pfad);
        let datei = dir.join("gabbro.build");
        if !datei.is_file() {
            return Err(format!(
                "{}: dependency `{}`: `{}` holds no `gabbro.build` (give `path:`, or put the project into \
                 `subprojects/{}/`)",
                a.ort,
                a.name,
                dir.display(),
                a.name
            ));
        }
        let kanon = std::fs::canonicalize(&datei).map_err(|e| format!("{}: {e}", datei.display()))?;
        if let Some(i) = stapel.iter().position(|k| *k == kanon) {
            let kette: Vec<String> = stapel[i..]
                .iter()
                .map(|k| k.parent().unwrap_or(Path::new(".")).display().to_string())
                .chain(std::iter::once(dir.display().to_string()))
                .collect();
            return Err(format!(
                "{}: the projects form a cycle ({}) -- a project cannot be configured before itself; \
                 mutual calls go through function pointers or a third, shared project",
                a.ort,
                kette.join(" -> ")
            ));
        }
        // Its options: defaults, the program's `target`/`buildtype`, `options:`, then `-D<name>:…`.
        let alle = sprache::lies_optionen(&dir.join("gabbro.options"))?;
        let mut werte: BTreeMap<String, Wert> = alle.iter().map(|o| (o.name.clone(), o.vorgabe.clone())).collect();
        werte.insert("target".into(), ziel.clone());
        werte.insert("buildtype".into(), bautyp.clone());
        let mut gesetzt: BTreeMap<String, String> = a.optionen.iter().cloned().collect();
        if let Some(d) = fremd.get(&a.name) {
            gesetzt.extend(d.iter().map(|(k, v)| (k.clone(), v.clone())));
        }
        for (k, v) in &gesetzt {
            let Some(o) = alle.iter().find(|o| &o.name == k) else {
                return Err(format!("{}: `{k}` is no option of project `{}`", a.ort, a.name));
            };
            if o.eingebaut {
                return Err(format!(
                    "{}: `{k}` of `{}` -- the built-in options are the program's (`target` and `buildtype` \
                     are handed down)",
                    a.ort, a.name
                ));
            }
            werte.insert(k.clone(), sprache::lies_optionswert(o, v)?);
        }
        let projekt = sprache::werte_aus(&kanon, &werte)?;
        if projekt.name != a.name {
            return Err(format!(
                "{}: `{}` holds project `{}`, not `{}`",
                a.ort,
                dir.display(),
                projekt.name,
                a.name
            ));
        }
        if let Some(r) = &a.version {
            if projekt.version.is_empty() {
                return Err(format!(
                    "{}: `{}` requires version `{r}`, and project `{}` declares none (`project(..., version: '…')`)",
                    a.ort, a.name, a.name
                ));
            }
            let v = sprache::lies_version(&projekt.version)?;
            if !Versionsbereich::lies(r)?.erfuellt(&v) {
                return Err(format!(
                    "{}: `{}` requires version `{r}`, and `{}` is version {}",
                    a.ort,
                    a.name,
                    dir.display(),
                    projekt.version
                ));
            }
        }
        let optionen: Vec<(String, String)> = gesetzt.into_iter().collect();
        // One copy per source and option set; one version from two places is refused.
        let j = if let Some(j) = g.kopien.iter().position(|k| k.kanon == kanon) {
            if g.kopien[j].optionen != optionen {
                return Err(format!(
                    "{}: `{}` {} is reached twice with different options ({:?} and {:?}) -- one unit cannot \
                     know which copy a path meant",
                    a.ort, a.name, projekt.version, g.kopien[j].optionen, optionen
                ));
            }
            j
        } else {
            if let Some(k) = g
                .kopien
                .iter()
                .skip(1)
                .find(|k| k.projekt.name == projekt.name && k.projekt.version == projekt.version)
            {
                return Err(format!(
                    "{}: `{}` {} is reached from two places ({} and {}) -- one version is one source",
                    a.ort,
                    a.name,
                    projekt.version,
                    k.kanon.display(),
                    kanon.display()
                ));
            }
            g.kopien.push(Kopie {
                ident: String::new(),
                projekt,
                werte,
                deps: Vec::new(),
                kanon: kanon.clone(),
                optionen,
            });
            let j = g.kopien.len() - 1;
            stapel.push(kanon);
            besuche(g, j, stapel, fremd)?;
            stapel.pop();
            j
        };
        g.kopien[idx].deps.push(j);
    }
    Ok(())
}

/// The name spaces: a project's name, and its version beside it where two versions meet.
fn vergib_namen(g: &mut Graph) {
    let mut zahl: BTreeMap<String, usize> = BTreeMap::new();
    for k in &g.kopien {
        *zahl.entry(k.projekt.name.clone()).or_default() += 1;
    }
    let mut vergeben: Vec<String> = Vec::new();
    for i in 0..g.kopien.len() {
        let k = &g.kopien[i];
        let mut n = if zahl[&k.projekt.name] > 1 && i > 0 {
            let v: String = k.projekt.version.chars().map(|c| if c.is_ascii_alphanumeric() { c } else { '_' }).collect();
            format!("{}_v{v}", k.projekt.name)
        } else {
            k.projekt.name.clone()
        };
        let basis = n.clone();
        let mut z = 2;
        while vergeben.contains(&n) {
            n = format!("{basis}_{z}");
            z += 1;
        }
        vergeben.push(n.clone());
        g.kopien[i].ident = n;
    }
}

/// The content fingerprint of a copy: its build files, its options file, every source its
/// targets name.
fn fingerabdruck(k: &Kopie) -> Result<u64, String> {
    let mut namen: Vec<String> = k.projekt.baudateien.clone();
    namen.push("gabbro.options".into());
    for z in &k.projekt.ziele {
        namen.extend(z.dateien.iter().cloned());
    }
    namen.sort();
    namen.dedup();
    let mut teile: Vec<Vec<u8>> = Vec::new();
    for n in &namen {
        teile.push(n.as_bytes().to_vec());
        teile.push(std::fs::read(k.projekt.wurzel.join(n)).unwrap_or_default());
    }
    let refs: Vec<&[u8]> = teile.iter().map(|t| t.as_slice()).collect();
    Ok(abdruck64(&refs))
}

/// The lock text of a graph: one line per dependency copy.
pub fn lock_text(g: &Graph) -> Result<String, String> {
    let mut t = String::from(
        "# The dependencies of this build directory, written by `gabbro setup`/`configure`.\n\
         # `gabbro compile` refuses when a dependency no longer matches; `gabbro configure -C <dir>` accepts it.\n",
    );
    for k in g.kopien.iter().skip(1) {
        let opt: Vec<String> = k.optionen.iter().map(|(a, b)| format!("{a}={b}")).collect();
        t.push_str(&format!(
            "dependency {} project={} version={} path={} options={} content={:016x}\n",
            k.ident,
            k.projekt.name,
            k.projekt.version,
            k.kanon.parent().unwrap_or(Path::new(".")).display(),
            opt.join(";"),
            fingerabdruck(k)?
        ));
    }
    Ok(t)
}

pub fn schreibe_lock(verzeichnis: &Path, g: &Graph) -> Result<(), String> {
    let p = verzeichnis.join(LOCKDATEI);
    std::fs::write(&p, lock_text(g)?).map_err(|e| format!("{}: {e}", p.display()))
}

/// **Every compile checks the lock**: a dependency that changed is named, never swapped in silently.
pub fn pruefe_lock(verzeichnis: &Path, g: &Graph) -> Result<(), String> {
    let p = verzeichnis.join(LOCKDATEI);
    let jetzt = lock_text(g)?;
    let alt = match std::fs::read_to_string(&p) {
        Ok(t) => t,
        Err(_) if g.kopien.len() == 1 => return Ok(()),
        Err(_) => {
            return Err(format!(
                "`{}` has dependencies and no `{LOCKDATEI}` -- `gabbro configure -C {}` writes it",
                verzeichnis.display(),
                verzeichnis.display()
            ))
        }
    };
    if alt == jetzt {
        return Ok(());
    }
    let zeilen = |t: &str| -> Vec<String> { t.lines().filter(|z| z.starts_with("dependency ")).map(String::from).collect() };
    let (a, j) = (zeilen(&alt), zeilen(&jetzt));
    let mut was: Vec<String> = Vec::new();
    for z in &j {
        if !a.contains(z) {
            was.push(format!("now   {z}"));
        }
    }
    for z in &a {
        if !j.contains(z) {
            was.push(format!("was   {z}"));
        }
    }
    Err(format!(
        "the dependencies changed since this build directory was configured:\n  {}\n`gabbro configure -C {}` \
         accepts the change and writes `{LOCKDATEI}` anew",
        was.join("\n  "),
        verzeichnis.display()
    ))
}
