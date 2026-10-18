//! The assembler: atoms to Gabbro source text.
//!
//! **Combination space (written down).** A program is
//!
//! ```text
//!   Arr x Mode x Atom^k      k = 1 for One and Pool, k = 2 for Seq, Par and Call
//! ```
//!
//! * `Arr`: `One` (one function), `Pool` (the function twice in `concurrent { f, f }`),
//!   `Seq` (two atoms in one body), `Par` (two atoms as two concurrent roots), `Call` (the first
//!   atom in a callee, called from the function that holds the second).
//! * `Mode`: how the guardable carriers of the atoms (`T`, `s`) are protected: `Free` (no lock
//!   declared), `Locks` (a `locks L { .. }` block around the atom), `Held` (`requires Held(L)`),
//!   `Bare` (the lock is declared and not taken: the poison twin of the other two).
//!   A program with no guardable carrier has only `Free`.
//! * An atom of `Seq`/`Par`/`Call` is admissible where the shape allows it: the first atom of a
//!   `Seq` and both of a `Par`/`Call` carry no result and (for `Par`/`Call`/`Pool`) no parameters.
//!   A recursive atom stands only in `One` (it calls `f`).

use crate::atome::{Atom, Wache};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Arr {
    One,
    Pool,
    Seq,
    Par,
    Call,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Mode {
    Free,
    Locks,
    Held,
    Bare,
    /// Only the first atom's carrier access is wrapped in `locks L`; the second one is bare.
    LocksErst,
    /// Only the second atom's carrier access is wrapped in `locks L`; the first one is bare.
    LocksZweit,
}

impl Arr {
    pub fn name(self) -> &'static str {
        match self {
            Arr::One => "One",
            Arr::Pool => "Pool",
            Arr::Seq => "Seq",
            Arr::Par => "Par",
            Arr::Call => "Call",
        }
    }
}

impl Mode {
    pub fn name(self) -> &'static str {
        match self {
            Mode::Free => "Free",
            Mode::Locks => "Locks",
            Mode::Held => "Held",
            Mode::Bare => "Bare",
            Mode::LocksErst => "LocksErst",
            Mode::LocksZweit => "LocksZweit",
        }
    }
}

fn slot(s: &str, i: usize) -> String {
    s.replace('@', &i.to_string())
}

fn kurz(a: &Atom) -> bool {
    a.params.is_empty() && a.ret.is_empty()
}

fn rekursiv(a: &Atom) -> bool {
    a.id.starts_with("c.rec")
}

/// Is the shape admissible for these atoms?
pub fn zulaessig(arr: Arr, atoms: &[&Atom]) -> bool {
    match arr {
        Arr::One => atoms.len() == 1,
        Arr::Pool => atoms.len() == 1 && kurz(atoms[0]) && !rekursiv(atoms[0]),
        Arr::Seq => {
            atoms.len() == 2
                && atoms[0].ret.is_empty()
                && !rekursiv(atoms[0])
                && !rekursiv(atoms[1])
        }
        Arr::Par | Arr::Call => atoms.len() == 2 && kurz(atoms[0]) && kurz(atoms[1]),
    }
}

/// The modes a set of atoms is built under.
pub fn modi(atoms: &[&Atom]) -> Vec<Mode> {
    if atoms.iter().any(|a| a.wache != Wache::Keine) {
        let mut m = vec![Mode::Free, Mode::Locks, Mode::Held, Mode::Bare];
        if atoms.len() == 2 {
            m.extend([Mode::LocksErst, Mode::LocksZweit]);
        }
        m
    } else {
        vec![Mode::Free]
    }
}

struct Teil {
    params: Vec<String>,
    eff: Vec<String>,
    body: String,
    ret: String,
    klausel: String,
    req: String,
    ohne_kosten: bool,
    ens: String,
    kosten_n: u32,
}

fn teil(a: &Atom, i: usize, mode: Mode) -> Teil {
    let guarded = a.wache != Wache::Keine
        && match mode {
            Mode::Locks | Mode::Held => true,
            Mode::LocksErst => i == 0,
            Mode::LocksZweit => i == 1,
            Mode::Free | Mode::Bare => false,
        };
    let mut eff: Vec<String> = a.eff.iter().map(|e| slot(e, i)).collect();
    if guarded {
        eff.push("locks L".to_string());
    }
    let mut body = slot(a.body, i);
    if guarded && mode != Mode::Held {
        let inner: String = body.lines().map(|l| format!("    {l}\n")).collect();
        body = format!("locks L {{\n{inner}    }}");
    }
    Teil {
        params: if a.params.is_empty() {
            vec![]
        } else {
            a.params.split(", ").map(|p| slot(p, i)).collect()
        },
        eff,
        body,
        ret: a.ret.to_string(),
        klausel: slot(a.klausel, i),
        req: slot(a.req, i),
        ohne_kosten: a.ohne_kosten,
        ens: slot(a.ens, i),
        kosten_n: a.kosten_n,
    }
}

fn effekte(teile: &[&Teil]) -> String {
    let mut e: Vec<String> = Vec::new();
    for t in teile {
        for x in &t.eff {
            if !e.contains(x) {
                e.push(x.clone());
            }
        }
    }
    if e.is_empty() {
        "pure".to_string()
    } else {
        e.join(", ")
    }
}

fn fn_text(name: &str, ts: &[&Teil], body: &str, mode: Mode, wache: bool, kosten_n: u32) -> String {
    let params: Vec<&str> = ts.iter().flat_map(|t| t.params.iter().map(|s| s.as_str())).collect();
    let ret = ts.iter().map(|t| t.ret.as_str()).find(|r| !r.is_empty()).unwrap_or("");
    let klausel = ts.iter().map(|t| t.klausel.as_str()).find(|r| !r.is_empty()).unwrap_or("");
    let mut reqs: Vec<&str> = ts.iter().map(|t| t.req.as_str()).filter(|r| !r.is_empty()).collect();
    if wache && mode == Mode::Held {
        reqs.push("Held(L)");
    }
    let req = if reqs.is_empty() { String::new() } else { format!("\n    requires {}", reqs.join(", ")) };
    let ens = ts.iter().map(|t| t.ens.as_str()).find(|e| !e.is_empty());
    let ens = ens.map(|e| format!("\n    ensures {e}")).unwrap_or_default();
    let kn = ts.iter().map(|t| t.kosten_n).find(|k| *k > 0).unwrap_or(kosten_n);
    let kosten = if ts.iter().any(|t| t.ohne_kosten) { String::new() } else { format!("\n    costs <= {kn} ops") };
    let kl = if klausel.is_empty() { String::new() } else { format!("\n    {klausel}") };
    format!(
        "impl fn {name}({}){ret}{req}{ens}\n    effects {{ {} }}{kosten}{kl}\n{{\n    {}\n}}\n",
        params.join(", "),
        effekte(ts),
        body.replace('\n', "\n    ")
    )
}

/// Build one unit. `None` where the shape is not admissible.
pub fn bau(name: &str, arr: Arr, mode: Mode, atoms: &[&Atom]) -> Option<String> {
    if !zulaessig(arr, atoms) {
        return None;
    }
    let ts: Vec<Teil> = atoms.iter().enumerate().map(|(i, a)| teil(a, i, mode)).collect();
    let wache_t = atoms.iter().any(|a| a.wache == Wache::T);
    let wache_s = atoms.iter().any(|a| a.wache == Wache::S);
    let wache = wache_t || wache_s;

    let mut decls: Vec<&str> = Vec::new();
    let mut items: Vec<&str> = Vec::new();
    for a in atoms {
        for d in a.decls {
            if !decls.contains(d) {
                decls.push(d);
            }
        }
        for d in a.items {
            if !items.contains(d) {
                items.push(d);
            }
        }
    }
    let mut out = format!("module gen::{name} {{\n");
    for d in &decls {
        out.push_str(d);
        out.push('\n');
    }
    if wache && mode != Mode::Free {
        let mut p = Vec::new();
        if wache_t {
            p.push("T");
        }
        if wache_s {
            p.push("s");
        }
        out.push_str(&format!("lock L protects {{ {} }} rank 0 held <= 100 ops;\n", p.join(", ")));
    }
    for i in &items {
        out.push_str(i);
        out.push('\n');
    }
    match arr {
        Arr::One | Arr::Pool => {
            out.push_str(&fn_text("f", &[&ts[0]], &ts[0].body, mode, wache, 40000));
            if arr == Arr::Pool {
                out.push_str("concurrent { f, f };\n");
            }
        }
        Arr::Seq => {
            let body = format!("{}\n    {}", ts[0].body, ts[1].body);
            out.push_str(&fn_text("f", &[&ts[0], &ts[1]], &body, mode, wache, 40000));
        }
        Arr::Par => {
            out.push_str(&fn_text("fa", &[&ts[0]], &ts[0].body, mode, atoms[0].wache != Wache::Keine, 40000));
            out.push_str(&fn_text("fb", &[&ts[1]], &ts[1].body, mode, atoms[1].wache != Wache::Keine, 40000));
            out.push_str("concurrent { fa, fb };\n");
        }
        Arr::Call => {
            out.push_str(&fn_text("ga", &[&ts[0]], &ts[0].body, mode, atoms[0].wache != Wache::Keine, 20000));
            let body = format!("ga();\n    {}", ts[1].body);
            let w = atoms[0].wache != Wache::Keine || atoms[1].wache != Wache::Keine;
            out.push_str(&fn_text("f", &[&ts[0], &ts[1]], &body, mode, w, 40000));
        }
    }
    out.push_str("}\n");
    Some(out)
}
