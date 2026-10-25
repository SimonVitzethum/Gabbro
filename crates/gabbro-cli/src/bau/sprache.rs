//! **The build language: `gabbro.build` and `gabbro.options`, after Meson.**
//!
//! A small declarative language, read and evaluated in one pass, never compiled to anything:
//!
//! ```text
//! project('hello', version: '0.1.0')
//! store = library('store', 'store.gab')          # a source library
//! app = program('app', files('app.gab'), install: true)
//! if get_option('trace')
//!   program('app-trace', 'app.gab', 'trace.gab')
//! endif
//! foreach n : ['a', 'b']
//!   test('runs-' + n, app, args: [n], stdout: n + '\n')
//! endforeach
//! subdir('werkzeuge')
//! ```
//!
//! Values are strings, integers, booleans, lists and target handles. Statements are an
//! assignment (`=`, `+=`), a call, `if`/`elif`/`else`/`endif` and `foreach`/`endforeach`.
//! `#` starts a comment. **Every refusal names its file and line**: a build that guesses what
//! a build file meant undoes every pass behind it.
//!
//! *What the language does NOT carry, and why* (`dokumente/BUILD-SYSTEM.md` §1): no
//! dependency list between targets -- the edges are COMPUTED from `module` and `use` in the
//! sources (W7); no compiler flags -- `arch`, `when TESTBUILD`, effects and costs stand in the
//! source; no custom commands -- a build that runs arbitrary programs checks nothing it runs.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

// ---------------------------------------------------------------- tokens

#[derive(Debug, Clone, PartialEq)]
enum Tok {
    Name(String),
    Text(String),
    Zahl(i64),
    Wahr,
    Falsch,
    Wort(&'static str),
    Zeichen(&'static str),
    Ende,
}

const WOERTER: &[&str] = &[
    "if", "elif", "else", "endif", "foreach", "endforeach", "and", "or", "not", "in",
];

struct Lexer<'a> {
    text: &'a [u8],
    pos: usize,
    zeile: usize,
    /// Depth of `(` and `[`: inside them a line break is no statement end.
    tiefe: usize,
}

fn lexe(datei: &str, text: &str) -> Result<Vec<(Tok, usize)>, String> {
    let mut l = Lexer { text: text.as_bytes(), pos: 0, zeile: 1, tiefe: 0 };
    let mut aus: Vec<(Tok, usize)> = Vec::new();
    while l.pos < l.text.len() {
        let c = l.text[l.pos];
        match c {
            b'#' => {
                while l.pos < l.text.len() && l.text[l.pos] != b'\n' {
                    l.pos += 1;
                }
            }
            b'\n' => {
                if l.tiefe == 0 && !matches!(aus.last(), Some((Tok::Ende, _)) | None) {
                    aus.push((Tok::Ende, l.zeile));
                }
                l.zeile += 1;
                l.pos += 1;
            }
            b' ' | b'\t' | b'\r' => l.pos += 1,
            b'\'' => {
                let start = l.zeile;
                l.pos += 1;
                let mut s = String::new();
                loop {
                    if l.pos >= l.text.len() || l.text[l.pos] == b'\n' {
                        return Err(format!("{datei}:{start}: a string is not closed on its line"));
                    }
                    let b = l.text[l.pos];
                    if b == b'\'' {
                        l.pos += 1;
                        break;
                    }
                    if b == b'\\' {
                        l.pos += 1;
                        let e = l.text.get(l.pos).copied().unwrap_or(b' ');
                        s.push(match e {
                            b'n' => '\n',
                            b't' => '\t',
                            b'\\' => '\\',
                            b'\'' => '\'',
                            andere => {
                                return Err(format!(
                                    "{datei}:{}: `\\{}` is no escape -- `\\n`, `\\t`, `\\\\`, `\\'`",
                                    l.zeile, andere as char
                                ))
                            }
                        });
                        l.pos += 1;
                        continue;
                    }
                    // Keep UTF-8 intact: copy the whole character.
                    let rest = std::str::from_utf8(&l.text[l.pos..]).map_err(|_| {
                        format!("{datei}:{}: the build file is not UTF-8", l.zeile)
                    })?;
                    let ch = rest.chars().next().expect("not at the end");
                    s.push(ch);
                    l.pos += ch.len_utf8();
                }
                aus.push((Tok::Text(s), start));
            }
            b'0'..=b'9' => {
                let a = l.pos;
                while l.pos < l.text.len() && l.text[l.pos].is_ascii_digit() {
                    l.pos += 1;
                }
                let s = std::str::from_utf8(&l.text[a..l.pos]).expect("digits");
                let n = s.parse::<i64>().map_err(|_| format!("{datei}:{}: `{s}` is too large", l.zeile))?;
                aus.push((Tok::Zahl(n), l.zeile));
            }
            b'a'..=b'z' | b'A'..=b'Z' | b'_' => {
                let a = l.pos;
                while l.pos < l.text.len()
                    && (l.text[l.pos].is_ascii_alphanumeric() || l.text[l.pos] == b'_')
                {
                    l.pos += 1;
                }
                let s = std::str::from_utf8(&l.text[a..l.pos]).expect("ascii");
                let t = match s {
                    "true" => Tok::Wahr,
                    "false" => Tok::Falsch,
                    _ => match WOERTER.iter().find(|w| **w == s) {
                        Some(w) => Tok::Wort(w),
                        None => Tok::Name(s.to_string()),
                    },
                };
                aus.push((t, l.zeile));
            }
            _ => {
                let zwei = l.text.get(l.pos..l.pos + 2).unwrap_or(b"");
                let z: &'static str = match zwei {
                    b"==" => "==",
                    b"!=" => "!=",
                    b"+=" => "+=",
                    _ => match c {
                        b'(' => "(",
                        b')' => ")",
                        b'[' => "[",
                        b']' => "]",
                        b',' => ",",
                        b':' => ":",
                        b'=' => "=",
                        b'+' => "+",
                        _ => {
                            return Err(format!(
                                "{datei}:{}: `{}` is no character of the build language",
                                l.zeile, c as char
                            ))
                        }
                    },
                };
                match z {
                    "(" | "[" => l.tiefe += 1,
                    ")" | "]" => l.tiefe = l.tiefe.saturating_sub(1),
                    _ => {}
                }
                l.pos += z.len();
                aus.push((Tok::Zeichen(z), l.zeile));
            }
        }
    }
    if l.tiefe > 0 {
        return Err(format!("{datei}:{}: a `(` or `[` is not closed", l.zeile));
    }
    aus.push((Tok::Ende, l.zeile));
    Ok(aus)
}

// ---------------------------------------------------------------- syntax tree

#[derive(Debug, Clone)]
enum Ausdruck {
    Text(String),
    Zahl(i64),
    Bool(bool),
    Liste(Vec<Ausdruck>),
    Name(String),
    Ruf {
        name: String,
        positionen: Vec<Ausdruck>,
        benannt: Vec<(String, Ausdruck)>,
    },
    Index(Box<Ausdruck>, Box<Ausdruck>),
    Nicht(Box<Ausdruck>),
    Zwei(&'static str, Box<Ausdruck>, Box<Ausdruck>),
}

#[derive(Debug, Clone)]
enum Satz {
    Zuweisung { name: String, plus: bool, wert: Ausdruck },
    Ausdruck(Ausdruck),
    Wenn { zweige: Vec<(Ausdruck, Vec<(Satz, usize)>)>, sonst: Vec<(Satz, usize)> },
    Fuer { name: String, liste: Ausdruck, rumpf: Vec<(Satz, usize)> },
}

struct Parser<'a> {
    datei: &'a str,
    toks: Vec<(Tok, usize)>,
    pos: usize,
}

impl Parser<'_> {
    fn sieh(&self) -> &Tok {
        &self.toks[self.pos].0
    }
    fn zeile(&self) -> usize {
        self.toks[self.pos].1
    }
    fn weiter(&mut self) -> Tok {
        let t = self.toks[self.pos].0.clone();
        if self.pos + 1 < self.toks.len() {
            self.pos += 1;
        }
        t
    }
    fn fehler<T>(&self, was: &str) -> Result<T, String> {
        Err(format!("{}:{}: {was}", self.datei, self.zeile()))
    }
    fn erwarte(&mut self, z: &'static str) -> Result<(), String> {
        if self.sieh() == &Tok::Zeichen(z) {
            self.weiter();
            Ok(())
        } else {
            self.fehler(&format!("`{z}` expected, {} found", zeige_tok(self.sieh())))
        }
    }
    fn ueberspringe_enden(&mut self) {
        while self.sieh() == &Tok::Ende && self.pos + 1 < self.toks.len() {
            self.pos += 1;
        }
    }

    /// Statements until one of the closing words (not consumed).
    fn block(&mut self, schluss: &[&str]) -> Result<Vec<(Satz, usize)>, String> {
        let mut aus = Vec::new();
        loop {
            self.ueberspringe_enden();
            match self.sieh() {
                Tok::Wort(w) if schluss.contains(w) => return Ok(aus),
                Tok::Ende => {
                    if schluss.is_empty() {
                        return Ok(aus);
                    }
                    return self.fehler(&format!("the file ends before `{}`", schluss.join("`/`")));
                }
                _ => {}
            }
            let z = self.zeile();
            let s = self.satz()?;
            aus.push((s, z));
            match self.sieh() {
                Tok::Ende => {
                    self.weiter();
                }
                t => return self.fehler(&format!("the statement goes on with {}", zeige_tok(t))),
            }
        }
    }

    fn satz(&mut self) -> Result<Satz, String> {
        match self.sieh().clone() {
            Tok::Wort("if") => {
                self.weiter();
                let mut zweige = Vec::new();
                let bed = self.ausdruck()?;
                let rumpf = self.block(&["elif", "else", "endif"])?;
                zweige.push((bed, rumpf));
                let mut sonst = Vec::new();
                loop {
                    match self.weiter() {
                        Tok::Wort("elif") => {
                            let b = self.ausdruck()?;
                            let r = self.block(&["elif", "else", "endif"])?;
                            zweige.push((b, r));
                        }
                        Tok::Wort("else") => {
                            sonst = self.block(&["endif"])?;
                        }
                        Tok::Wort("endif") => break,
                        t => return self.fehler(&format!("`endif` expected, {} found", zeige_tok(&t))),
                    }
                }
                Ok(Satz::Wenn { zweige, sonst })
            }
            Tok::Wort("foreach") => {
                self.weiter();
                let Tok::Name(name) = self.weiter() else {
                    return self.fehler("`foreach` takes a variable name");
                };
                self.erwarte(":")?;
                let liste = self.ausdruck()?;
                let rumpf = self.block(&["endforeach"])?;
                self.weiter();
                Ok(Satz::Fuer { name, liste, rumpf })
            }
            Tok::Name(n)
                if matches!(
                    self.toks.get(self.pos + 1).map(|t| &t.0),
                    Some(Tok::Zeichen("=")) | Some(Tok::Zeichen("+="))
                ) =>
            {
                self.weiter();
                let plus = self.weiter() == Tok::Zeichen("+=");
                let wert = self.ausdruck()?;
                Ok(Satz::Zuweisung { name: n, plus, wert })
            }
            _ => Ok(Satz::Ausdruck(self.ausdruck()?)),
        }
    }

    fn ausdruck(&mut self) -> Result<Ausdruck, String> {
        let mut l = self.und()?;
        while self.sieh() == &Tok::Wort("or") {
            self.weiter();
            let r = self.und()?;
            l = Ausdruck::Zwei("or", Box::new(l), Box::new(r));
        }
        Ok(l)
    }
    fn und(&mut self) -> Result<Ausdruck, String> {
        let mut l = self.nicht()?;
        while self.sieh() == &Tok::Wort("and") {
            self.weiter();
            let r = self.nicht()?;
            l = Ausdruck::Zwei("and", Box::new(l), Box::new(r));
        }
        Ok(l)
    }
    fn nicht(&mut self) -> Result<Ausdruck, String> {
        if self.sieh() == &Tok::Wort("not") {
            self.weiter();
            return Ok(Ausdruck::Nicht(Box::new(self.nicht()?)));
        }
        self.vergleich()
    }
    fn vergleich(&mut self) -> Result<Ausdruck, String> {
        let l = self.summe()?;
        let op = match self.sieh() {
            Tok::Zeichen("==") => "==",
            Tok::Zeichen("!=") => "!=",
            Tok::Wort("in") => "in",
            Tok::Wort("not")
                if self.toks.get(self.pos + 1).map(|t| &t.0) == Some(&Tok::Wort("in")) =>
            {
                self.weiter();
                "not in"
            }
            _ => return Ok(l),
        };
        self.weiter();
        let r = self.summe()?;
        Ok(Ausdruck::Zwei(op, Box::new(l), Box::new(r)))
    }
    fn summe(&mut self) -> Result<Ausdruck, String> {
        let mut l = self.nachsatz()?;
        while self.sieh() == &Tok::Zeichen("+") {
            self.weiter();
            let r = self.nachsatz()?;
            l = Ausdruck::Zwei("+", Box::new(l), Box::new(r));
        }
        Ok(l)
    }
    fn nachsatz(&mut self) -> Result<Ausdruck, String> {
        let mut a = self.grund()?;
        while self.sieh() == &Tok::Zeichen("[") {
            self.weiter();
            let i = self.ausdruck()?;
            self.erwarte("]")?;
            a = Ausdruck::Index(Box::new(a), Box::new(i));
        }
        Ok(a)
    }
    fn grund(&mut self) -> Result<Ausdruck, String> {
        match self.weiter() {
            Tok::Text(s) => Ok(Ausdruck::Text(s)),
            Tok::Zahl(n) => Ok(Ausdruck::Zahl(n)),
            Tok::Wahr => Ok(Ausdruck::Bool(true)),
            Tok::Falsch => Ok(Ausdruck::Bool(false)),
            Tok::Zeichen("(") => {
                let a = self.ausdruck()?;
                self.erwarte(")")?;
                Ok(a)
            }
            Tok::Zeichen("[") => {
                let mut teile = Vec::new();
                while self.sieh() != &Tok::Zeichen("]") {
                    teile.push(self.ausdruck()?);
                    if self.sieh() == &Tok::Zeichen(",") {
                        self.weiter();
                    } else {
                        break;
                    }
                }
                self.erwarte("]")?;
                Ok(Ausdruck::Liste(teile))
            }
            Tok::Name(n) => {
                if self.sieh() != &Tok::Zeichen("(") {
                    return Ok(Ausdruck::Name(n));
                }
                self.weiter();
                let mut positionen = Vec::new();
                let mut benannt: Vec<(String, Ausdruck)> = Vec::new();
                while self.sieh() != &Tok::Zeichen(")") {
                    if let (Tok::Name(k), Some(Tok::Zeichen(":"))) =
                        (self.sieh().clone(), self.toks.get(self.pos + 1).map(|t| t.0.clone()))
                    {
                        self.weiter();
                        self.weiter();
                        if benannt.iter().any(|(b, _)| b == &k) {
                            return self.fehler(&format!("`{k}:` is given twice"));
                        }
                        benannt.push((k, self.ausdruck()?));
                    } else {
                        if !benannt.is_empty() {
                            return self.fehler("a positional argument after a keyword argument");
                        }
                        positionen.push(self.ausdruck()?);
                    }
                    if self.sieh() == &Tok::Zeichen(",") {
                        self.weiter();
                    } else {
                        break;
                    }
                }
                self.erwarte(")")?;
                Ok(Ausdruck::Ruf { name: n, positionen, benannt })
            }
            t => self.fehler(&format!("an expression expected, {} found", zeige_tok(&t))),
        }
    }
}

fn zeige_tok(t: &Tok) -> String {
    match t {
        Tok::Name(n) => format!("`{n}`"),
        Tok::Text(s) => format!("'{s}'"),
        Tok::Zahl(n) => n.to_string(),
        Tok::Wahr => "`true`".into(),
        Tok::Falsch => "`false`".into(),
        Tok::Wort(w) | Tok::Zeichen(w) => format!("`{w}`"),
        Tok::Ende => "the end of the line".into(),
    }
}

fn parse(datei: &str, text: &str) -> Result<Vec<(Satz, usize)>, String> {
    let toks = lexe(datei, text)?;
    let mut p = Parser { datei, toks, pos: 0 };
    let saetze = p.block(&[])?;
    Ok(saetze)
}

// ---------------------------------------------------------------- values

#[derive(Debug, Clone, PartialEq)]
pub enum Wert {
    Text(String),
    Zahl(i64),
    Bool(bool),
    Liste(Vec<Wert>),
    /// A source path out of `files()`, already relative to the project root.
    Datei(String),
    /// A handle on a target, by index into `Projekt::ziele`.
    Ziel(usize),
    /// A handle on a dependency, by index into `Projekt::abhaengigkeiten`.
    Abh(usize),
    Nichts,
}

impl Wert {
    fn art(&self) -> &'static str {
        match self {
            Wert::Text(_) => "a string",
            Wert::Zahl(_) => "an integer",
            Wert::Bool(_) => "a boolean",
            Wert::Liste(_) => "a list",
            Wert::Datei(_) => "a file",
            Wert::Ziel(_) => "a target",
            Wert::Abh(_) => "a dependency",
            Wert::Nichts => "nothing",
        }
    }
}

// ---------------------------------------------------------------- options

#[derive(Debug, Clone, PartialEq)]
pub enum OptionsArt {
    Bool,
    Text,
    Zahl,
    Auswahl(Vec<String>),
}

#[derive(Debug, Clone)]
pub struct Option_ {
    pub name: String,
    pub art: OptionsArt,
    pub vorgabe: Wert,
    pub beschreibung: String,
    pub eingebaut: bool,
}

/// The options every project has. **`target` and `buildtype` replace the old `--target=` and
/// `--testbuild` of `gabbro build`**: a build directory is ONE configuration.
pub fn eingebaute_optionen() -> Vec<Option_> {
    vec![
        Option_ {
            name: "target".into(),
            art: OptionsArt::Auswahl(vec!["x86_64".into(), "aarch64".into()]),
            vorgabe: Wert::Text("x86_64".into()),
            beschreibung: "the target architecture (part of every fingerprint)".into(),
            eingebaut: true,
        },
        Option_ {
            name: "buildtype".into(),
            art: OptionsArt::Auswahl(vec!["shipping".into(), "testbuild".into()]),
            vorgabe: Wert::Text("shipping".into()),
            beschreibung: "`testbuild` opens the build gate `when TESTBUILD`".into(),
            eingebaut: true,
        },
        Option_ {
            name: "prefix".into(),
            art: OptionsArt::Text,
            vorgabe: Wert::Text("/usr/local".into()),
            beschreibung: "the install prefix".into(),
            eingebaut: true,
        },
        Option_ {
            name: "bindir".into(),
            art: OptionsArt::Text,
            vorgabe: Wert::Text("bin".into()),
            beschreibung: "programs are installed into <prefix>/<bindir>".into(),
            eingebaut: true,
        },
    ]
}

/// Reads `gabbro.options` (absent: no project options). Only `option(...)` calls stand there.
pub fn lies_optionen(pfad: &Path) -> Result<Vec<Option_>, String> {
    let mut alle = eingebaute_optionen();
    let Ok(text) = std::fs::read_to_string(pfad) else {
        return Ok(alle);
    };
    let datei = pfad.display().to_string();
    for (s, zeile) in parse(&datei, &text)? {
        let Satz::Ausdruck(Ausdruck::Ruf { name, positionen, benannt }) = s else {
            return Err(format!("{datei}:{zeile}: only `option(...)` stands in an options file"));
        };
        if name != "option" {
            return Err(format!("{datei}:{zeile}: `{name}` -- only `option(...)` stands in an options file"));
        }
        let mut leer = Auswerter::leer();
        let pos: Vec<Wert> = positionen
            .iter()
            .map(|a| leer.wert(a, &datei, zeile))
            .collect::<Result<_, _>>()?;
        let [Wert::Text(oname)] = pos.as_slice() else {
            return Err(format!("{datei}:{zeile}: `option('<name>', type: …)` takes exactly the name"));
        };
        if alle.iter().any(|o| &o.name == oname) {
            return Err(format!(
                "{datei}:{zeile}: option `{oname}` is declared twice (or names a built-in option)"
            ));
        }
        let mut kw: BTreeMap<String, Wert> = BTreeMap::new();
        for (k, a) in &benannt {
            kw.insert(k.clone(), leer.wert(a, &datei, zeile)?);
        }
        for k in kw.keys() {
            if !["type", "value", "choices", "description"].contains(&k.as_str()) {
                return Err(format!("{datei}:{zeile}: `{k}:` is no option keyword -- `type`, `value`, `choices`, `description`"));
            }
        }
        let typ = match kw.get("type") {
            Some(Wert::Text(t)) => t.clone(),
            _ => return Err(format!("{datei}:{zeile}: option `{oname}` needs `type:` -- 'boolean', 'string', 'integer' or 'combo'")),
        };
        let art = match typ.as_str() {
            "boolean" => OptionsArt::Bool,
            "string" => OptionsArt::Text,
            "integer" => OptionsArt::Zahl,
            "combo" => match kw.get("choices") {
                Some(Wert::Liste(l)) if !l.is_empty() => {
                    let mut c = Vec::new();
                    for w in l {
                        match w {
                            Wert::Text(t) => c.push(t.clone()),
                            andere => return Err(format!("{datei}:{zeile}: a choice is a string, {} found", andere.art())),
                        }
                    }
                    OptionsArt::Auswahl(c)
                }
                _ => return Err(format!("{datei}:{zeile}: a 'combo' option needs a non-empty `choices:` list")),
            },
            andere => return Err(format!("{datei}:{zeile}: `{andere}` is no option type -- 'boolean', 'string', 'integer', 'combo'")),
        };
        let vorgabe = match (kw.get("value"), &art) {
            (Some(w), _) => w.clone(),
            (None, OptionsArt::Bool) => Wert::Bool(false),
            (None, OptionsArt::Text) => Wert::Text(String::new()),
            (None, OptionsArt::Zahl) => Wert::Zahl(0),
            (None, OptionsArt::Auswahl(c)) => Wert::Text(c[0].clone()),
        };
        pruefe_wert(&art, &vorgabe).map_err(|e| format!("{datei}:{zeile}: option `{oname}`: {e}"))?;
        let beschreibung = match kw.get("description") {
            Some(Wert::Text(t)) => t.clone(),
            _ => String::new(),
        };
        alle.push(Option_ { name: oname.clone(), art, vorgabe, beschreibung, eingebaut: false });
    }
    Ok(alle)
}

fn pruefe_wert(art: &OptionsArt, w: &Wert) -> Result<(), String> {
    match (art, w) {
        (OptionsArt::Bool, Wert::Bool(_))
        | (OptionsArt::Text, Wert::Text(_))
        | (OptionsArt::Zahl, Wert::Zahl(_)) => Ok(()),
        (OptionsArt::Auswahl(c), Wert::Text(t)) if c.contains(t) => Ok(()),
        (OptionsArt::Auswahl(c), Wert::Text(t)) => {
            Err(format!("`{t}` is none of {}", c.iter().map(|x| format!("`{x}`")).collect::<Vec<_>>().join(", ")))
        }
        (a, w) => Err(format!("{} does not fit a {} option", w.art(), art_name(a))),
    }
}

fn art_name(a: &OptionsArt) -> &'static str {
    match a {
        OptionsArt::Bool => "boolean",
        OptionsArt::Text => "string",
        OptionsArt::Zahl => "integer",
        OptionsArt::Auswahl(_) => "combo",
    }
}

/// A `-Dname=value` text read against the option's type.
pub fn lies_optionswert(o: &Option_, text: &str) -> Result<Wert, String> {
    let w = match &o.art {
        OptionsArt::Bool => match text {
            "true" => Wert::Bool(true),
            "false" => Wert::Bool(false),
            _ => return Err(format!("`-D{}={text}`: a boolean option takes `true` or `false`", o.name)),
        },
        OptionsArt::Zahl => Wert::Zahl(text.parse().map_err(|_| {
            format!("`-D{}={text}`: an integer option takes an integer", o.name)
        })?),
        OptionsArt::Text | OptionsArt::Auswahl(_) => Wert::Text(text.to_string()),
    };
    pruefe_wert(&o.art, &w).map_err(|e| format!("`-D{}={text}`: {e}", o.name))?;
    Ok(w)
}

pub fn zeige_wert(w: &Wert) -> String {
    match w {
        Wert::Text(t) => t.clone(),
        Wert::Zahl(n) => n.to_string(),
        Wert::Bool(b) => b.to_string(),
        Wert::Liste(l) => format!("[{}]", l.iter().map(zeige_wert).collect::<Vec<_>>().join(", ")),
        Wert::Datei(d) => d.clone(),
        Wert::Ziel(i) => format!("<target {i}>"),
        Wert::Abh(i) => format!("<dependency {i}>"),
        Wert::Nichts => "nothing".into(),
    }
}

// ---------------------------------------------------------------- the project

/// What a target becomes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Art {
    /// Links to an executable; carries the entry `pub fn main`.
    Programm,
    /// Stops at `<name>.o`; carries no entry.
    Objekt,
    /// A source library: its files go into every unit whose `use` lines reach its modules.
    /// It is checked alone as well, so an error in it names it and not only its users.
    Bibliothek,
}

impl Art {
    pub fn wort(self) -> &'static str {
        match self {
            Art::Programm => "program",
            Art::Objekt => "object",
            Art::Bibliothek => "library",
        }
    }
}

#[derive(Debug, Clone)]
pub struct Ziel {
    pub name: String,
    pub art: Art,
    /// Paths relative to the project root, in the order written.
    pub dateien: Vec<String>,
    pub installieren: bool,
    /// `export: true` (a library): dependents may `use` its modules.
    pub export: bool,
    /// `dependencies: [...]`: the dependencies (indices into `Projekt::abhaengigkeiten`) this
    /// target may draw from. Which files enter its unit is still COMPUTED from `use`.
    pub abhaengigkeiten: Vec<usize>,
    /// `file:line` of the call that declared it.
    pub ort: String,
}

/// **A `dependency(...)` call**: another Gabbro project, from a local path (or
/// `subprojects/<name>/`), with a version requirement and options of its own.
#[derive(Debug, Clone, PartialEq)]
pub struct Abhaengigkeit {
    /// The project's name -- its `project('<name>')`, and the name its paths start with here.
    pub name: String,
    /// The project directory, relative to this project's root.
    pub pfad: String,
    /// The version requirement (`'>=1.2, <2'`), if any.
    pub version: Option<String>,
    /// `options: ['name=value', …]` for the dependency's own options.
    pub optionen: Vec<(String, String)>,
    pub ort: String,
}

#[derive(Debug, Clone)]
pub struct Test {
    pub name: String,
    pub ziel: usize,
    pub argumente: Vec<String>,
    pub ausgabe: Option<String>,
    pub austritt: i64,
    pub sekunden: u64,
    pub ort: String,
}

#[derive(Debug, Clone)]
pub struct Projekt {
    pub name: String,
    pub version: String,
    pub wurzel: PathBuf,
    pub ziele: Vec<Ziel>,
    pub tests: Vec<Test>,
    pub abhaengigkeiten: Vec<Abhaengigkeit>,
    /// Every build file read, relative to the root: what a reconfigure has to look at.
    pub baudateien: Vec<String>,
    pub meldungen: Vec<String>,
}

/// Evaluates the project whose build file is `baudatei`, with the options resolved.
pub fn werte_aus(
    baudatei: &Path,
    optionen: &BTreeMap<String, Wert>,
) -> Result<Projekt, String> {
    let wurzel = baudatei.parent().map(Path::to_path_buf).unwrap_or_else(|| PathBuf::from("."));
    let mut a = Auswerter {
        variablen: BTreeMap::new(),
        optionen: optionen.clone(),
        projekt: Projekt {
            name: String::new(),
            version: String::new(),
            wurzel: wurzel.clone(),
            ziele: Vec::new(),
            tests: Vec::new(),
            abhaengigkeiten: Vec::new(),
            baudateien: Vec::new(),
            meldungen: Vec::new(),
        },
        verzeichnis: String::new(),
        projekt_gesehen: false,
    };
    let name = baudatei.file_name().and_then(|s| s.to_str()).unwrap_or("gabbro.build").to_string();
    a.datei(&name)?;
    if !a.projekt_gesehen {
        return Err(format!("{}: no `project(...)` call", baudatei.display()));
    }
    Ok(a.projekt)
}

struct Auswerter {
    variablen: BTreeMap<String, Wert>,
    optionen: BTreeMap<String, Wert>,
    projekt: Projekt,
    /// The directory of the build file being read, relative to the root (`""` at the root).
    verzeichnis: String,
    projekt_gesehen: bool,
}

const ZIELWOERTER: &[&str] = &["install", "dependencies"];
const BIBLIOTHEKSWOERTER: &[&str] = &["export", "dependencies"];
const OBJEKTWOERTER: &[&str] = &["dependencies"];
const ABHWOERTER: &[&str] = &["path", "version", "options"];
const TESTWOERTER: &[&str] = &["args", "stdout", "exit", "timeout"];

impl Auswerter {
    fn leer() -> Auswerter {
        Auswerter {
            variablen: BTreeMap::new(),
            optionen: BTreeMap::new(),
            projekt: Projekt {
                name: String::new(),
                version: String::new(),
                wurzel: PathBuf::new(),
                ziele: Vec::new(),
                tests: Vec::new(),
                abhaengigkeiten: Vec::new(),
                baudateien: Vec::new(),
                meldungen: Vec::new(),
            },
            verzeichnis: String::new(),
            projekt_gesehen: true,
        }
    }

    fn relativ(&self, pfad: &str) -> String {
        if self.verzeichnis.is_empty() {
            pfad.to_string()
        } else {
            format!("{}/{pfad}", self.verzeichnis)
        }
    }

    /// Reads and runs one build file, relative to the root.
    fn datei(&mut self, relativ: &str) -> Result<(), String> {
        let pfad = self.projekt.wurzel.join(relativ);
        let text = std::fs::read_to_string(&pfad).map_err(|e| format!("{}: {e}", pfad.display()))?;
        self.projekt.baudateien.push(relativ.to_string());
        let saetze = parse(relativ, &text)?;
        self.saetze(&saetze, relativ)
    }

    fn saetze(&mut self, saetze: &[(Satz, usize)], datei: &str) -> Result<(), String> {
        for (s, zeile) in saetze {
            self.satz(s, datei, *zeile)?;
        }
        Ok(())
    }

    fn satz(&mut self, s: &Satz, datei: &str, zeile: usize) -> Result<(), String> {
        match s {
            Satz::Zuweisung { name, plus, wert } => {
                let w = self.wert(wert, datei, zeile)?;
                let neu = if *plus {
                    let Some(alt) = self.variablen.get(name).cloned() else {
                        return Err(format!("{datei}:{zeile}: `{name} +=` before `{name}` has a value"));
                    };
                    plus_werte(alt, w).map_err(|e| format!("{datei}:{zeile}: {e}"))?
                } else {
                    w
                };
                self.variablen.insert(name.clone(), neu);
            }
            Satz::Ausdruck(a) => {
                self.wert(a, datei, zeile)?;
            }
            Satz::Wenn { zweige, sonst } => {
                for (bed, rumpf) in zweige {
                    match self.wert(bed, datei, zeile)? {
                        Wert::Bool(true) => return self.saetze(rumpf, datei),
                        Wert::Bool(false) => {}
                        w => return Err(format!("{datei}:{zeile}: an `if` takes a boolean, {} found", w.art())),
                    }
                }
                self.saetze(sonst, datei)?;
            }
            Satz::Fuer { name, liste, rumpf } => {
                let Wert::Liste(l) = self.wert(liste, datei, zeile)? else {
                    return Err(format!("{datei}:{zeile}: `foreach` runs over a list"));
                };
                for w in l {
                    self.variablen.insert(name.clone(), w);
                    self.saetze(rumpf, datei)?;
                }
            }
        }
        Ok(())
    }

    fn wert(&mut self, a: &Ausdruck, datei: &str, zeile: usize) -> Result<Wert, String> {
        let f = |e: String| format!("{datei}:{zeile}: {e}");
        Ok(match a {
            Ausdruck::Text(s) => Wert::Text(s.clone()),
            Ausdruck::Zahl(n) => Wert::Zahl(*n),
            Ausdruck::Bool(b) => Wert::Bool(*b),
            Ausdruck::Liste(l) => Wert::Liste(
                l.iter().map(|x| self.wert(x, datei, zeile)).collect::<Result<_, _>>()?,
            ),
            Ausdruck::Name(n) => self
                .variablen
                .get(n)
                .cloned()
                .ok_or_else(|| f(format!("`{n}` has no value here")))?,
            Ausdruck::Index(l, i) => {
                let (lw, iw) = (self.wert(l, datei, zeile)?, self.wert(i, datei, zeile)?);
                match (lw, iw) {
                    (Wert::Liste(l), Wert::Zahl(i)) => {
                        let n = l.len() as i64;
                        let j = if i < 0 { n + i } else { i };
                        if j < 0 || j >= n {
                            return Err(f(format!("index {i} outside a list of {n}")));
                        }
                        l[j as usize].clone()
                    }
                    (l, i) => return Err(f(format!("{} cannot be indexed by {}", l.art(), i.art()))),
                }
            }
            Ausdruck::Nicht(x) => match self.wert(x, datei, zeile)? {
                Wert::Bool(b) => Wert::Bool(!b),
                w => return Err(f(format!("`not` takes a boolean, {} found", w.art()))),
            },
            Ausdruck::Zwei(op, l, r) => {
                let lw = self.wert(l, datei, zeile)?;
                // `and`/`or` stop early, as a reader expects.
                match (*op, &lw) {
                    ("and", Wert::Bool(false)) => return Ok(Wert::Bool(false)),
                    ("or", Wert::Bool(true)) => return Ok(Wert::Bool(true)),
                    _ => {}
                }
                let rw = self.wert(r, datei, zeile)?;
                match *op {
                    "and" | "or" => match (&lw, &rw) {
                        (Wert::Bool(_), Wert::Bool(b)) => Wert::Bool(*b),
                        _ => return Err(f(format!("`{op}` takes booleans"))),
                    },
                    "==" => Wert::Bool(lw == rw),
                    "!=" => Wert::Bool(lw != rw),
                    "in" | "not in" => {
                        let drin = match &rw {
                            Wert::Liste(l) => l.contains(&lw),
                            Wert::Text(t) => match &lw {
                                Wert::Text(s) => t.contains(s.as_str()),
                                _ => return Err(f("`in` a string takes a string".into())),
                            },
                            w => return Err(f(format!("`in` takes a list or a string, {} found", w.art()))),
                        };
                        Wert::Bool(if *op == "in" { drin } else { !drin })
                    }
                    "+" => plus_werte(lw, rw).map_err(f)?,
                    _ => unreachable!("the parser makes no other operator"),
                }
            }
            Ausdruck::Ruf { name, positionen, benannt } => {
                let pos: Vec<Wert> =
                    positionen.iter().map(|x| self.wert(x, datei, zeile)).collect::<Result<_, _>>()?;
                let mut kw: BTreeMap<String, Wert> = BTreeMap::new();
                for (k, x) in benannt {
                    kw.insert(k.clone(), self.wert(x, datei, zeile)?);
                }
                self.ruf(name, pos, kw, datei, zeile).map_err(f)?
            }
        })
    }

    fn ruf(
        &mut self,
        name: &str,
        pos: Vec<Wert>,
        kw: BTreeMap<String, Wert>,
        datei: &str,
        zeile: usize,
    ) -> Result<Wert, String> {
        let erlaube = |erlaubt: &[&str]| -> Result<(), String> {
            for k in kw.keys() {
                if !erlaubt.contains(&k.as_str()) {
                    return Err(format!(
                        "`{name}` takes no `{k}:`{}",
                        if erlaubt.is_empty() {
                            String::new()
                        } else {
                            format!(" -- {}", erlaubt.iter().map(|e| format!("`{e}:`")).collect::<Vec<_>>().join(", "))
                        }
                    ));
                }
            }
            Ok(())
        };
        if name != "project" && !self.projekt_gesehen {
            return Err(format!("`{name}` before `project(...)` -- the first call of the root build file is `project`"));
        }
        match name {
            "project" => {
                if self.projekt_gesehen {
                    return Err("`project` is called once, at the top of the root build file".into());
                }
                erlaube(&["version"])?;
                let [Wert::Text(n)] = pos.as_slice() else {
                    return Err("`project('<name>', version: …)`".into());
                };
                self.projekt.name = n.clone();
                self.projekt.version = match kw.get("version") {
                    Some(Wert::Text(v)) => v.clone(),
                    None => String::new(),
                    Some(w) => return Err(format!("`version:` is a string, {} found", w.art())),
                };
                self.projekt_gesehen = true;
                Ok(Wert::Nichts)
            }
            "files" => {
                erlaube(&[])?;
                Ok(Wert::Liste(
                    texte(&pos)?.into_iter().map(|t| Wert::Datei(self.relativ(&t))).collect(),
                ))
            }
            "program" | "object" | "library" => {
                erlaube(match name {
                    "program" => ZIELWOERTER,
                    "library" => BIBLIOTHEKSWOERTER,
                    _ => OBJEKTWOERTER,
                })?;
                let art = match name {
                    "program" => Art::Programm,
                    "object" => Art::Objekt,
                    _ => Art::Bibliothek,
                };
                let Some((Wert::Text(zname), quellen)) = pos.split_first() else {
                    return Err(format!("`{name}('<name>', <sources>…)`"));
                };
                pruefe_zielname(zname)?;
                if self.projekt.ziele.iter().any(|z| &z.name == zname) {
                    return Err(format!(
                        "`{zname}` is a second target of that name -- the artefacts would overwrite one another"
                    ));
                }
                let mut dateien = Vec::new();
                for p in self.quellpfade(quellen)? {
                    if !p.ends_with(".gab") {
                        return Err(format!(
                            "`{p}` is no `.gab` file -- a target's sources are Gabbro sources (this build compiles no C)"
                        ));
                    }
                    if dateien.contains(&p) {
                        return Err(format!("`{p}` is named twice in `{zname}`"));
                    }
                    dateien.push(p);
                }
                if dateien.is_empty() {
                    return Err(format!("`{zname}` names no source -- an empty target builds nothing and says it built"));
                }
                let installieren = match kw.get("install") {
                    None => false,
                    Some(Wert::Bool(b)) => *b,
                    Some(w) => return Err(format!("`install:` is a boolean, {} found", w.art())),
                };
                let export = match kw.get("export") {
                    None => false,
                    Some(Wert::Bool(b)) => *b,
                    Some(w) => return Err(format!("`export:` is a boolean, {} found", w.art())),
                };
                let mut abhaengigkeiten = Vec::new();
                match kw.get("dependencies") {
                    None => {}
                    Some(Wert::Liste(l)) => {
                        for w in l {
                            let Wert::Abh(i) = w else {
                                return Err(format!(
                                    "`dependencies:` lists handles of `dependency(...)`, {} found",
                                    w.art()
                                ));
                            };
                            if abhaengigkeiten.contains(i) {
                                return Err(format!(
                                    "`{}` stands twice in `dependencies:` of `{zname}`",
                                    self.projekt.abhaengigkeiten[*i].name
                                ));
                            }
                            abhaengigkeiten.push(*i);
                        }
                    }
                    Some(Wert::Abh(i)) => abhaengigkeiten.push(*i),
                    Some(w) => return Err(format!("`dependencies:` is a list of dependencies, {} found", w.art())),
                }
                self.projekt.ziele.push(Ziel {
                    name: zname.clone(),
                    art,
                    dateien,
                    installieren,
                    export,
                    abhaengigkeiten,
                    ort: format!("{datei}:{zeile}"),
                });
                Ok(Wert::Ziel(self.projekt.ziele.len() - 1))
            }
            "test" => {
                erlaube(TESTWOERTER)?;
                let [Wert::Text(tname), Wert::Ziel(z)] = pos.as_slice() else {
                    return Err("`test('<name>', <program>, args: […], stdout: '…', exit: 0, timeout: 30)`".into());
                };
                if self.projekt.ziele[*z].art != Art::Programm {
                    return Err(format!(
                        "`{}` is {} `{}`, and only a program runs",
                        self.projekt.ziele[*z].name,
                        match self.projekt.ziele[*z].art { Art::Objekt => "an", _ => "a" },
                        self.projekt.ziele[*z].art.wort()
                    ));
                }
                if self.projekt.tests.iter().any(|t| &t.name == tname) {
                    return Err(format!("`{tname}` is a second test of that name"));
                }
                let argumente = match kw.get("args") {
                    None => Vec::new(),
                    Some(Wert::Liste(l)) => texte(l)?,
                    Some(w) => return Err(format!("`args:` is a list of strings, {} found", w.art())),
                };
                let ausgabe = match kw.get("stdout") {
                    None => None,
                    Some(Wert::Text(t)) => Some(t.clone()),
                    Some(w) => return Err(format!("`stdout:` is a string, {} found", w.art())),
                };
                let austritt = match kw.get("exit") {
                    None => 0,
                    Some(Wert::Zahl(n)) if (0..=255).contains(n) => *n,
                    Some(w) => return Err(format!("`exit:` is an integer 0..255, {} found", zeige_wert(w))),
                };
                let sekunden = match kw.get("timeout") {
                    None => 30,
                    Some(Wert::Zahl(n)) if *n > 0 => *n as u64,
                    Some(w) => return Err(format!("`timeout:` is a positive integer, {} found", zeige_wert(w))),
                };
                self.projekt.tests.push(Test {
                    name: tname.clone(),
                    ziel: *z,
                    argumente,
                    ausgabe,
                    austritt,
                    sekunden,
                    ort: format!("{datei}:{zeile}"),
                });
                Ok(Wert::Nichts)
            }
            "dependency" => {
                erlaube(ABHWOERTER)?;
                let [Wert::Text(dname)] = pos.as_slice() else {
                    return Err("`dependency('<project>', path: '…', version: '…', options: […])`".into());
                };
                pruefe_projektname(dname)?;
                let pfad = match kw.get("path") {
                    None => format!("subprojects/{dname}"),
                    Some(Wert::Text(t)) if !t.is_empty() && !t.starts_with('/') => self.relativ(t),
                    Some(Wert::Text(t)) => {
                        return Err(format!("`path: '{t}'` -- a project directory relative to this build file"))
                    }
                    Some(w) => return Err(format!("`path:` is a string, {} found", w.art())),
                };
                let version = match kw.get("version") {
                    None => None,
                    Some(Wert::Text(t)) => {
                        Versionsbereich::lies(t)?;
                        Some(t.clone())
                    }
                    Some(w) => return Err(format!("`version:` is a string, {} found", w.art())),
                };
                let mut optionen = Vec::new();
                match kw.get("options") {
                    None => {}
                    Some(Wert::Liste(l)) => {
                        for t in texte(l)? {
                            let Some((k, v)) = t.split_once('=') else {
                                return Err(format!("`options:` holds `name=value` strings, `{t}` found"));
                            };
                            optionen.push((k.trim().to_string(), v.trim().to_string()));
                        }
                    }
                    Some(w) => return Err(format!("`options:` is a list of strings, {} found", w.art())),
                }
                let neu = Abhaengigkeit {
                    name: dname.clone(),
                    pfad,
                    version,
                    optionen,
                    ort: format!("{datei}:{zeile}"),
                };
                if let Some(i) = self.projekt.abhaengigkeiten.iter().position(|a| a.name == *dname) {
                    let alt = &self.projekt.abhaengigkeiten[i];
                    if (&alt.pfad, &alt.version, &alt.optionen) != (&neu.pfad, &neu.version, &neu.optionen) {
                        return Err(format!(
                            "`{dname}` is declared a second time ({}) with other arguments -- a project \
                             depends on one version of a project, so its name says which",
                            alt.ort
                        ));
                    }
                    return Ok(Wert::Abh(i));
                }
                self.projekt.abhaengigkeiten.push(neu);
                Ok(Wert::Abh(self.projekt.abhaengigkeiten.len() - 1))
            }
            "subdir" => {
                erlaube(&[])?;
                let [Wert::Text(d)] = pos.as_slice() else {
                    return Err("`subdir('<directory>')`".into());
                };
                if d.is_empty() || d.contains("..") || d.starts_with('/') {
                    return Err(format!("`subdir('{d}')` -- a subdirectory below this one, no `..`, no absolute path"));
                }
                let neu = self.relativ(d);
                let alt = std::mem::replace(&mut self.verzeichnis, neu.clone());
                let r = self.datei(&format!("{neu}/gabbro.build"));
                self.verzeichnis = alt;
                r.map(|_| Wert::Nichts)
            }
            "get_option" => {
                erlaube(&[])?;
                let [Wert::Text(o)] = pos.as_slice() else {
                    return Err("`get_option('<name>')`".into());
                };
                self.optionen.get(o).cloned().ok_or_else(|| {
                    format!("`{o}` is no option -- declare it in `gabbro.options`")
                })
            }
            "message" | "warning" | "error" => {
                erlaube(&[])?;
                let text = pos.iter().map(zeige_wert).collect::<Vec<_>>().join(" ");
                match name {
                    "error" => Err(format!("error: {text}")),
                    "warning" => {
                        self.projekt.meldungen.push(format!("{datei}:{zeile}: WARNING: {text}"));
                        Ok(Wert::Nichts)
                    }
                    _ => {
                        self.projekt.meldungen.push(format!("{datei}:{zeile}: {text}"));
                        Ok(Wert::Nichts)
                    }
                }
            }
            andere => Err(format!(
                "`{andere}` is no function of the build language -- project, files, program, \
                 library, object, dependency, test, subdir, get_option, message, warning, error"
            )),
        }
    }
}

impl Auswerter {
    /// Source paths relative to the root: a `files()` path as it is, a bare string relative to
    /// the directory of the build file that names it (in a `subdir` the two differ).
    fn quellpfade(&self, werte: &[Wert]) -> Result<Vec<String>, String> {
        let mut aus = Vec::new();
        for w in werte {
            match w {
                Wert::Text(t) => aus.push(self.relativ(t)),
                Wert::Datei(d) => aus.push(d.clone()),
                Wert::Liste(l) => aus.extend(self.quellpfade(l)?),
                andere => return Err(format!("a source is a string or a file, {} found", andere.art())),
            }
        }
        Ok(aus)
    }
}

fn texte(werte: &[Wert]) -> Result<Vec<String>, String> {
    let mut aus = Vec::new();
    for w in werte {
        match w {
            Wert::Text(t) => aus.push(t.clone()),
            Wert::Liste(l) => aus.extend(texte(l)?),
            andere => return Err(format!("a string or a list of strings expected, {} found", andere.art())),
        }
    }
    Ok(aus)
}

fn plus_werte(l: Wert, r: Wert) -> Result<Wert, String> {
    Ok(match (l, r) {
        (Wert::Text(a), Wert::Text(b)) => Wert::Text(a + &b),
        (Wert::Zahl(a), Wert::Zahl(b)) => Wert::Zahl(a.checked_add(b).ok_or("the sum overflows")?),
        (Wert::Liste(mut a), Wert::Liste(b)) => {
            a.extend(b);
            Wert::Liste(a)
        }
        (Wert::Liste(mut a), b) => {
            a.push(b);
            Wert::Liste(a)
        }
        (a, b) => return Err(format!("`+` does not join {} and {}", a.art(), b.art())),
    })
}

/// A project name is a path head in Gabbro source and a name space: an identifier.
pub fn pruefe_projektname(n: &str) -> Result<(), String> {
    if n.is_empty() || !n.starts_with(|c: char| c.is_ascii_alphabetic()) {
        return Err(format!("`{n}` -- a project name starts with an ASCII letter"));
    }
    if let Some(b) = n.chars().find(|c| !(c.is_ascii_alphanumeric() || *c == '_')) {
        return Err(format!(
            "`{n}` carries `{b}` -- a project name is an identifier (letters, digits, `_`): code reaches \
             it as the head of a path"
        ));
    }
    Ok(())
}

// ---------------------------------------------------------------- versions

/// A version: its numeric parts (`1.3.0` = [1, 3, 0]); a missing part is 0.
pub fn lies_version(t: &str) -> Result<Vec<u64>, String> {
    let t = t.trim();
    if t.is_empty() {
        return Err("an empty version".into());
    }
    t.split('.')
        .map(|x| x.parse::<u64>().map_err(|_| format!("`{t}` is no version (numbers separated by `.`)")))
        .collect()
}

fn vergleiche(a: &[u64], b: &[u64]) -> std::cmp::Ordering {
    let n = a.len().max(b.len());
    for i in 0..n {
        let (x, y) = (a.get(i).copied().unwrap_or(0), b.get(i).copied().unwrap_or(0));
        if x != y {
            return x.cmp(&y);
        }
    }
    std::cmp::Ordering::Equal
}

/// **A version requirement**: comparisons joined by `,`, all of which must hold
/// (`'>=1.2, <2'`); a bare version is `==`.
#[derive(Debug, Clone)]
pub struct Versionsbereich(Vec<(String, Vec<u64>)>);

impl Versionsbereich {
    pub fn lies(t: &str) -> Result<Versionsbereich, String> {
        let mut teile = Vec::new();
        for teil in t.split(',') {
            let teil = teil.trim();
            let (op, rest) = ["<=", ">=", "==", "!=", "<", ">", "="]
                .iter()
                .find_map(|op| teil.strip_prefix(op).map(|r| (*op, r)))
                .unwrap_or(("==", teil));
            let op = if op == "=" { "==" } else { op };
            teile.push((op.to_string(), lies_version(rest).map_err(|e| format!("`version: '{t}'`: {e}"))?));
        }
        Ok(Versionsbereich(teile))
    }

    pub fn erfuellt(&self, v: &[u64]) -> bool {
        use std::cmp::Ordering::*;
        self.0.iter().all(|(op, w)| {
            let o = vergleiche(v, w);
            match op.as_str() {
                "<" => o == Less,
                "<=" => o != Greater,
                ">" => o == Greater,
                ">=" => o != Less,
                "!=" => o != Equal,
                _ => o == Equal,
            }
        })
    }
}

/// The name is a file name in the build directory. **Refuse, never interpret.**
fn pruefe_zielname(n: &str) -> Result<(), String> {
    if n.is_empty() || !n.starts_with(|c: char| c.is_ascii_alphabetic()) {
        return Err(format!("`{n}` -- a target name starts with an ASCII letter"));
    }
    if let Some(b) = n.chars().find(|c| !(c.is_ascii_alphanumeric() || *c == '-' || *c == '_')) {
        return Err(format!("`{n}` carries `{b}` -- a target name holds letters, digits, `-` and `_`"));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn projekt(text: &str) -> Result<Projekt, String> {
        let d = std::env::temp_dir().join(format!("gabbro-sprache-{}-{}", std::process::id(), text.len()));
        std::fs::create_dir_all(&d).unwrap();
        std::fs::write(d.join("gabbro.build"), text).unwrap();
        let mut o = BTreeMap::new();
        for e in eingebaute_optionen() {
            o.insert(e.name.clone(), e.vorgabe.clone());
        }
        o.insert("trace".into(), Wert::Bool(true));
        let r = werte_aus(&d.join("gabbro.build"), &o);
        let _ = std::fs::remove_dir_all(&d);
        r
    }

    #[test]
    fn ein_projekt_mit_bedingung_und_schleife() {
        let p = projekt(
            "project('p', version: '1.0')\n\
             lib = library('lib', 'a.gab')\n\
             quellen = ['m.gab']\n\
             if get_option('trace') and get_option('target') == 'x86_64'\n  quellen += 't.gab'\nendif\n\
             haupt = program('haupt', quellen, install: true)\n\
             foreach n : ['x', 'y']\n  test('t-' + n, haupt, args: [n], stdout: n + '\\n')\nendforeach\n",
        )
        .unwrap();
        assert_eq!(p.name, "p");
        assert_eq!(p.ziele.len(), 2);
        assert_eq!(p.ziele[1].dateien, vec!["m.gab", "t.gab"]);
        assert!(p.ziele[1].installieren);
        assert_eq!(p.tests.len(), 2);
        assert_eq!(p.tests[1].ausgabe.as_deref(), Some("y\n"));
    }

    #[test]
    fn absagen_nennen_die_zeile() {
        let e = projekt("project('p')\nprogram('a', 'x.c')\n").unwrap_err();
        assert!(e.contains(":2:") && e.contains("no `.gab` file"), "{e}");
        let e = projekt("program('a', 'x.gab')\n").unwrap_err();
        assert!(e.contains("before `project"), "{e}");
        let e = projekt("project('p')\nprogram('a', 'x.gab', deps: [])\n").unwrap_err();
        assert!(e.contains("takes no `deps:`"), "{e}");
        let e = projekt("project('p')\nx = library('l', 'l.gab')\ntest('t', x)\n").unwrap_err();
        assert!(e.contains("only a program runs"), "{e}");
        let e = projekt("project('p')\nif true\nprogram('a', 'a.gab')\n").unwrap_err();
        assert!(e.contains("endif"), "{e}");
    }
}
