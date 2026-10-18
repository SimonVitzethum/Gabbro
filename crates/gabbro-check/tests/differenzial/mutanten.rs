//! **Mutants of the corpus.** The atoms (`atome.rs`) cover every form of the model one by one and in
//! pairs; the corpus programs carry the forms in the combinations people wrote. Every corpus example the
//! exporter certifies (the Lean model has a form for all of it) is mutated by small textual edits that
//! each remove or break one guarantee, and every mutant is judged like a generated program:
//!
//! * `unlock k`      -- the k-th `locks L { .. }` block is replaced by its statements;
//! * `drop-effect k` -- the k-th item of the k-th `effects { .. }` list disappears;
//! * `drop-held k`   -- the k-th `Held(..)` of a `requires` clause disappears;
//! * `swap-rank`     -- the first two `rank N` numbers of the lock declarations are exchanged;
//! * `drop-member k` / `dup-member k` -- a `concurrent` member disappears / is named twice;
//! * `widen k`       -- the k-th `in lo .. hi` range grows by one at the top;
//! * `drop-stmt k`   -- the k-th statement line of a body disappears;
//! * `drop-protect k` -- the k-th name of a `protects { .. }` list disappears.
//!
//! A mutant that does not read is no program and is dropped (`gen` rejects it by the reader).

use std::path::Path;

/// Strip `//` comments (the corpus has no block comments inside the units that export).
fn ohne_kommentare(s: &str) -> String {
    s.lines()
        .map(|l| match l.find("//") {
            Some(i) => &l[..i],
            None => l,
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// The index of the `}` matching the `{` at `open`.
fn passend(s: &str, open: usize) -> Option<usize> {
    let mut d = 0usize;
    for (i, c) in s.char_indices().skip_while(|(i, _)| *i < open) {
        match c {
            '{' => d += 1,
            '}' => {
                d -= 1;
                if d == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

/// Every start of `locks [shared] NAME {` with the index of its `{`.
fn sperrbloecke(s: &str) -> Vec<(usize, usize)> {
    let mut out = Vec::new();
    let mut von = 0;
    while let Some(p) = s[von..].find("locks ") {
        let a = von + p;
        von = a + 6;
        // a statement keyword, not the effect `locks L,` : the next `{` must come before any `;` and `,`
        let rest = &s[a..];
        let Some(b) = rest.find(['{', ';', ',', '}']) else { break };
        if rest.as_bytes()[b] == b'{' && !s[..a].trim_end().ends_with("effects {") {
            // not inside an `effects { .. }` list: such a list has `locks X` followed by `,` or `}`
            out.push((a, a + b));
        }
    }
    out
}

fn entsperrt(s: &str, k: usize) -> Option<String> {
    let (a, o) = *sperrbloecke(s).get(k)?;
    let e = passend(s, o)?;
    Some(format!("{}{}{}", &s[..a], &s[o + 1..e], &s[e + 1..]))
}

/// The `{ .. }` lists after the word `word` (`effects`, `protects`, `concurrent`): (open, close).
fn listen(s: &str, wort: &str) -> Vec<(usize, usize)> {
    let mut out = Vec::new();
    let mut von = 0;
    while let Some(p) = s[von..].find(wort) {
        let a = von + p;
        von = a + wort.len();
        let nach = s[von..].trim_start();
        if nach.starts_with('{') {
            let o = s.len() - nach.len();
            if let Some(e) = passend(s, o) {
                out.push((o, e));
            }
        }
    }
    out
}

fn eintrag_streichen(s: &str, wort: &str, liste: usize, k: usize) -> Option<String> {
    let (o, e) = *listen(s, wort).get(liste)?;
    let inner = &s[o + 1..e];
    let teile: Vec<&str> = inner.split(',').collect();
    if teile.len() < 2 || k >= teile.len() {
        return None;
    }
    let neu: Vec<&str> = teile.iter().enumerate().filter(|(i, _)| *i != k).map(|(_, t)| *t).collect();
    Some(format!("{}{{{}}}{}", &s[..o], neu.join(","), &s[e + 1..]))
}

fn mitglied_doppelt(s: &str, k: usize) -> Option<String> {
    let (o, e) = *listen(s, "concurrent").first()?;
    let inner = &s[o + 1..e];
    let teile: Vec<&str> = inner.split(',').map(str::trim).filter(|t| !t.is_empty()).collect();
    let t = teile.get(k)?;
    Some(format!("{}{{ {}, {} }}{}", &s[..o], inner.trim(), t, &s[e + 1..]))
}

fn held_streichen(s: &str, k: usize) -> Option<String> {
    let mut treffer = Vec::new();
    let mut von = 0;
    while let Some(p) = s[von..].find("Held(") {
        let a = von + p;
        let e = a + s[a..].find(')')? + 1;
        treffer.push((a, e));
        von = e;
    }
    let (a, e) = *treffer.get(k)?;
    // remove the item and a following or preceding comma
    let mut vor = s[..a].trim_end().len();
    let mut nach = e;
    if s[nach..].trim_start().starts_with(',') {
        nach += s[nach..].find(',')? + 1;
    } else if s[..vor].ends_with(',') {
        vor -= 1;
    } else if s[..vor].ends_with("requires") {
        vor -= "requires".len();
    }
    Some(format!("{}{}", &s[..vor], &s[nach..]))
}

fn raenge_tauschen(s: &str) -> Option<String> {
    let mut zahlen = Vec::new();
    let mut von = 0;
    while let Some(p) = s[von..].find("rank ") {
        let a = von + p + 5;
        let e = a + s[a..].find(|c: char| !c.is_ascii_digit())?;
        if e > a {
            zahlen.push((a, e));
        }
        von = e;
    }
    let ((a1, e1), (a2, e2)) = (*zahlen.first()?, *zahlen.get(1)?);
    let (x, y) = (&s[a1..e1], &s[a2..e2]);
    if x == y {
        return None;
    }
    Some(format!("{}{}{}{}{}", &s[..a1], y, &s[e1..a2], x, &s[e2..]))
}

fn bereich_weiten(s: &str, k: usize) -> Option<String> {
    let mut treffer = Vec::new();
    let mut von = 0;
    while let Some(p) = s[von..].find(" in ") {
        let a = von + p + 4;
        von = a;
        let rest = &s[a..];
        let lo_e = rest.find(|c: char| !(c.is_ascii_digit() || c == '-'))?;
        if lo_e == 0 || !rest[lo_e..].trim_start().starts_with("..") {
            continue;
        }
        let nach = &rest[lo_e..].trim_start()[2..];
        let nach = nach.strip_prefix('<').unwrap_or(nach).trim_start();
        let off = s.len() - nach.len();
        let hi_e = nach.find(|c: char| !c.is_ascii_digit())?;
        if hi_e > 0 {
            treffer.push((off, off + hi_e));
        }
    }
    let (a, e) = *treffer.get(k)?;
    let hi: i128 = s[a..e].parse().ok()?;
    Some(format!("{}{}{}", &s[..a], hi + 1, &s[e..]))
}

/// The k-th statement line: a line of a function body ending in `;` that is no declaration.
fn zeile_streichen(s: &str, k: usize) -> Option<String> {
    let zeilen: Vec<&str> = s.lines().collect();
    let mut n = 0;
    let mut tiefe = 0i32;
    for (i, l) in zeilen.iter().enumerate() {
        let t = l.trim();
        let vor = tiefe;
        tiefe += t.matches('{').count() as i32 - t.matches('}').count() as i32;
        let deklaration = t.starts_with("const ") || t.starts_with("type ") || t.starts_with("static ")
            || t.starts_with("lock ") || t.starts_with("atomic ") || t.starts_with("use ")
            || t.starts_with("concurrent") || t.starts_with("assume ") || t.starts_with("extern ")
            || t.starts_with("arena ") || t.starts_with("accumulates ");
        if vor >= 2 && t.ends_with(';') && !deklaration && !t.starts_with("return") {
            if n == k {
                let mut neu = zeilen.clone();
                neu.remove(i);
                return Some(neu.join("\n"));
            }
            n += 1;
        }
    }
    None
}

/// Every mutant of one source: (mutation id, text).
pub fn mutanten(quelle: &str) -> Vec<(String, String)> {
    let s = ohne_kommentare(quelle);
    let mut out: Vec<(String, String)> = Vec::new();
    let mut add = |id: String, m: Option<String>| {
        if let Some(m) = m {
            if m != s {
                out.push((id, m));
            }
        }
    };
    for k in 0..3 {
        add(format!("unlock{k}"), entsperrt(&s, k));
    }
    for liste in 0..3 {
        for k in 0..2 {
            add(format!("drop-effect{liste}.{k}"), eintrag_streichen(&s, "effects", liste, k));
        }
    }
    for k in 0..3 {
        add(format!("drop-held{k}"), held_streichen(&s, k));
        add(format!("drop-member{k}"), eintrag_streichen(&s, "concurrent", 0, k));
        add(format!("dup-member{k}"), mitglied_doppelt(&s, k));
        add(format!("widen{k}"), bereich_weiten(&s, k));
        add(format!("drop-stmt{k}"), zeile_streichen(&s, k));
        add(format!("drop-protect{k}"), eintrag_streichen(&s, "protects", 0, k));
    }
    add("swap-rank".to_string(), raenge_tauschen(&s));
    out
}

/// The corpus examples that export, with their mutants: (file stem, mutation id, source).
pub fn korpus_mutanten(dir: &Path, stems: &[&str]) -> Vec<(String, String, String)> {
    let mut out = Vec::new();
    for stem in stems {
        let Ok(q) = std::fs::read_to_string(dir.join(format!("{stem}.gab"))) else { continue };
        for (id, m) in mutanten(&q) {
            out.push((stem.to_string(), id, m));
        }
    }
    out
}
