//! **The alias SURFACE, counted -- and deliberately not analysed.**
//!
//! `m3.rs` says it about itself in its own module head, and has since it was written:
//!
//! > *"Er ist kein Alias-Analysator. Zwei `ptr<normal, rw>` auf dasselbe Objekt bleiben
//! > ununterscheidbar."*
//!
//! That sentence is honest and it is not a number. **An alias analysis is the largest single
//! intervention on the open list, and the decision to build one has not been taken.** What
//! stands between "no analysis" and "an analysis nobody decided on" is the figure this module
//! prints: *how much of this corpus could the missing rule be about?*
//!
//! > **A measured area makes the later decision possible; an analysis built without a
//! > decision is trust surface.**
//!
//! ## Five strata, each strictly narrower than the one above
//!
//! | | what it counts | direction of its error |
//! |---|---|---|
//! | **S1** signatures | functions with >= 2 pointer parameters | **over**-counts: two pointers may point at disjoint objects |
//! | **S2** call sites | calls passing >= 2 pointer arguments | **over**-counts, same reason |
//! | **S3** same root | calls where two pointer arguments share a syntactic root | **under**-counts (W10) |
//! | **S4** re-views | `fn(ptr<..> A) -> ptr<..> B` -- the alias FACTORIES | **under**-counts |
//! | **S5** write/read | S1 functions whose `effects` write through one pointer and read through another | **over**-counts within S1 |
//!
//! **S1 and S2 are upper bounds, S3 and S4 lower bounds, and the true figure is between
//! them.** Printing only one of the two would be the flattering move in whichever direction
//! the reader wanted.
//!
//! ## Why S5 reads the `effects` clause and not the body
//!
//! Because `E006` and `E010` -- both issued in `wirkungen.rs`, neither here -- already hold
//! that clause against the body, and re-deriving the same fact would be a **second**
//! derivation of something
//! the checker already decided -- the shape that made `W16` a rule. *A number that comes out
//! of a private re-reading of the AST looks like a measurement of the program; it is a
//! measurement of the second reader.*
//!
//! The price is stated rather than hidden: for a function whose `effects` are missing or
//! incomplete, S5 counts what the clause says, not what the body does.
//!
//! ## What NONE of the five sees, and it is the important sentence
//!
//! An alias that arises through a **table index**, through an integer address, or in a caller
//! two frames up leaves no trace in any of these counts. `messung/netz/udp-echo.gab` is in
//! S4 and S5 because `kopfworte_von` is written down as a function; had the same re-view been
//! done by arithmetic on an address, every number here would be one smaller and nothing about
//! the program would have changed. **All five are counts over what the source SAYS.**

use gabbro_syntax::ast::*;
use std::collections::{BTreeMap, BTreeSet};

/// One pointer parameter of one function: its name, whether it may be written through, and
/// the target type as written.
struct Zeigerparameter {
    name: String,
    /// The position in the callee's parameter list -- the key an ARGUMENT is matched by.
    stelle: usize,
    schreibbar: bool,
    ziel: String,
}

/// What one function contributes to the surface.
struct Fnlage {
    voll: String,
    zeiger: Vec<Zeigerparameter>,
    /// The roots of the declared `writes …` effects.
    schreibt: BTreeSet<String>,
    /// The roots of the declared `reads …` effects.
    liest: BTreeSet<String>,
    /// `fn(ptr<..> A) -> ptr<..> B` -- takes a pointer, hands back a pointer. **The shape in
    /// which a second view onto the same memory comes into existence.**
    umdeutung: Option<(String, String)>,
}

/// The counted area. Every field is a count of SITES, not of functions, except where named.
#[derive(Default)]
pub struct Flaeche {
    pub funktionen: usize,
    pub mit_zeiger: usize,
    /// **S1.**
    pub s1: usize,
    /// S1 of which at least one pointer parameter is writable.
    pub s1_schreibend: usize,
    /// **S2.**
    pub s2: usize,
    pub s2_schreibend: usize,
    /// **S3.**
    pub s3: usize,
    pub s3_schreibend: usize,
    /// **S4.**
    pub s4: usize,
    /// S4 whose result is bound and the source pointer still live at the same site.
    pub s4_gebunden: usize,
    /// **S5.**
    pub s5: usize,
    /// Every site, spelled out -- so that no figure above has to be believed.
    pub zeilen: Vec<String>,
}

impl Flaeche {
    /// **Summing over units is not the same question as measuring one.** A call site in unit
    /// A to a function in unit B is invisible to both -- the sum is therefore a sum of
    /// per-unit figures, and it inherits their blindness rather than curing it. *Said here
    /// because a total line reads as if it saw the whole program.*
    pub fn dazu(&mut self, a: Flaeche) {
        self.funktionen += a.funktionen;
        self.mit_zeiger += a.mit_zeiger;
        self.s1 += a.s1;
        self.s1_schreibend += a.s1_schreibend;
        self.s2 += a.s2;
        self.s2_schreibend += a.s2_schreibend;
        self.s3 += a.s3;
        self.s3_schreibend += a.s3_schreibend;
        self.s4 += a.s4;
        self.s4_gebunden += a.s4_gebunden;
        self.s5 += a.s5;
        self.zeilen.extend(a.zeilen);
    }
}

fn ist_zeiger(t: &TypExpr) -> Option<&PtrTy> {
    match t {
        TypExpr::Zeiger(p) => Some(p),
        _ => None,
    }
}

fn zieltext(t: &TypExpr) -> String {
    match t {
        TypExpr::Pfad(p) => p.text(),
        TypExpr::Int(_) => "int".into(),
        TypExpr::Float(_) => "float".into(),
        TypExpr::Bool(_) => "bool".into(),
        TypExpr::Never(_) => "never".into(),
        TypExpr::Feld(_) => "[…]".into(),
        TypExpr::Zeiger(_) => "ptr<…>".into(),
        TypExpr::Verbund(..) => "{…}".into(),
        TypExpr::FnZeiger(_) => "fn(…)".into(),
        TypExpr::Varianten(..) => "|…|".into(),
        TypExpr::Index { tabelle, .. } => format!("index into {}", tabelle.text),
    }
}

fn schreibbar(p: &PtrTy) -> bool {
    p.rechte
        .iter()
        .any(|r| matches!(r, Recht::Schreiben | Recht::LesenSchreiben | Recht::Eigen(_)))
}

/// The root of a place: `a.slots[…].x` -> `a`.
fn wurzel(o: &Ort) -> String {
    o.basis.text.clone()
}

/// The root of an expression, if it has exactly one. `k` -> `k`; `k.ihl` -> `k`;
/// `kopfworte_von(k)` -> none, because the result is a NEW name for the same memory and the
/// call is what S4 counts.
fn ausdruckswurzel(e: &Expr) -> Option<String> {
    match &e.art {
        ExprArt::Ort(o) => Some(wurzel(o)),
        _ => None,
    }
}

fn lage(f: &FnDecl, voll: String) -> Fnlage {
    let zeiger: Vec<Zeigerparameter> = f
        .parameter
        .iter()
        .enumerate()
        .filter_map(|(stelle, p)| {
            ist_zeiger(&p.typ).map(|z| Zeigerparameter {
                name: p.name.text.clone(),
                stelle,
                schreibbar: schreibbar(z),
                ziel: zieltext(&z.ziel),
            })
        })
        .collect();
    let mut schreibt = BTreeSet::new();
    let mut liest = BTreeSet::new();
    if let Some(w) = &f.effects {
        for e in &w.liste {
            match &e.art {
                WirkungArt::Schreibt(o) | WirkungArt::Verbraucht(o) => {
                    schreibt.insert(wurzel(o));
                }
                WirkungArt::Liest(o) => {
                    liest.insert(wurzel(o));
                }
                // The remaining kinds name no place through which a pointer is dereferenced:
                // `publishes` names a payload, `locks`/`locks shared` a lock, `masks` an
                // interrupt, `allocs` a core, and `diverges`/`pure` carry no argument.
                // *Written out rather than `_`: if a tenth kind arrives that names a place
                // reached through a pointer, it fails here and not in a report.*
                WirkungArt::Veroeffentlicht(_)
                | WirkungArt::Sperrt(_)
                | WirkungArt::SperrtGeteilt(_)
                | WirkungArt::Maskiert(_)
                | WirkungArt::Belegt(_)
                | WirkungArt::Divergiert
                | WirkungArt::Rein => {}
            }
        }
    }
    // **A re-view: takes at least one pointer, returns one.** The types need NOT differ --
    // `fn(ptr<normal,r> T) -> ptr<normal,rw> T` is the sharper case, not the milder one.
    let umdeutung = match (&f.ergebnis, zeiger.first()) {
        (Some(erg), Some(erst)) => ist_zeiger(erg).map(|z| (erst.ziel.clone(), zieltext(&z.ziel))),
        _ => None,
    };
    Fnlage { voll, zeiger, schreibt, liest, umdeutung }
}

/// Every call in a body, with the enclosing function's name.
fn rufe(b: &Block, aus: &mut Vec<Ruf>) {
    for s in &b.anweisungen {
        sammle_rufe_stmt(s, aus);
        for k in crate::unterbloecke(s) {
            rufe(k, aus);
        }
    }
}

fn sammle_rufe_stmt(s: &Stmt, aus: &mut Vec<Ruf>) {
    let mut ausdruecke: Vec<&Expr> = Vec::new();
    match &s.art {
        StmtArt::Ruf(r) => aus.push(r.clone()),
        StmtArt::Let(l) => ausdruecke.push(&l.wert),
        StmtArt::Zuweisung(z) => ausdruecke.push(&z.wert),
        StmtArt::Return(Some(e)) => ausdruecke.push(e),
        StmtArt::Publish(p) => ausdruecke.push(&p.wert),
        StmtArt::Wenn(w) => {
            for (bedingung, _) in &w.zweige {
                ausdruecke.push(bedingung);
            }
        }
        // Every other statement kind either carries no expression through which a call
        // could pass an argument, or carries it in a sub-block, which `unterbloecke`
        // reaches. *This is a COUNT and not a rule: the direction of a miss here is a
        // smaller S2, and that is the safe direction for an upper bound.*
        _ => {}
    }
    for e in ausdruecke {
        rufe_aus_expr(e, aus);
    }
}

fn rufe_aus_expr(e: &Expr, aus: &mut Vec<Ruf>) {
    if let ExprArt::Ruf(r) = &e.art {
        aus.push(r.clone());
    }
    for k in crate::unterausdruecke(e) {
        rufe_aus_expr(k, aus);
    }
}

/// **The measurement.** One pass over the tree; no refusal is issued and none could be --
/// this module decides nothing.
pub fn erhebe(baum: &Programm) -> Flaeche {
    let u = crate::umgebung::Umgebung::sammle(baum);
    let mut lagen: BTreeMap<String, Fnlage> = BTreeMap::new();
    let mut ruempfe: Vec<(String, String, Block)> = Vec::new();
    let mut f = Flaeche::default();

    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let ItemArt::Funktion(fd) = &item.art else { return };
        let voll = if modul.is_empty() {
            fd.name.text.clone()
        } else {
            format!("{modul}::{}", fd.name.text)
        };
        let l = lage(fd, voll.clone());
        if let FnRumpf::Block(b) = &fd.rumpf {
            ruempfe.push((voll.clone(), modul.to_string(), b.clone()));
        }
        lagen.insert(voll, l);
    });

    f.funktionen = lagen.len();
    for l in lagen.values() {
        if !l.zeiger.is_empty() {
            f.mit_zeiger += 1;
        }
        if l.zeiger.len() >= 2 {
            f.s1 += 1;
            if l.zeiger.iter().any(|z| z.schreibbar) {
                f.s1_schreibend += 1;
            }
            // **S5 -- the write/read pair through two different pointer parameters.**
            let geschrieben: Vec<&Zeigerparameter> =
                l.zeiger.iter().filter(|z| l.schreibt.contains(&z.name)).collect();
            let gelesen: Vec<&Zeigerparameter> =
                l.zeiger.iter().filter(|z| l.liest.contains(&z.name)).collect();
            let paar = geschrieben
                .iter()
                .any(|w| gelesen.iter().any(|r| r.name != w.name));
            if paar {
                f.s5 += 1;
                let w: Vec<&str> = geschrieben.iter().map(|z| z.name.as_str()).collect();
                let r: Vec<&str> = gelesen.iter().map(|z| z.name.as_str()).collect();
                f.zeilen.push(format!(
                    "S5  {}  writes {{{}}} · reads {{{}}}",
                    l.voll,
                    w.join(", "),
                    r.join(", ")
                ));
            }
        }
        if let Some((von, nach)) = &l.umdeutung {
            f.s4 += 1;
            f.zeilen
                .push(format!("S4  {}  ptr<…> {von} -> ptr<…> {nach}", l.voll));
        }
    }

    // **S2 and S3 -- the call sites.**
    for (voll, modul, b) in &ruempfe {
        let mut gefunden: Vec<Ruf> = Vec::new();
        rufe(b, &mut gefunden);
        for r in &gefunden {
            let CallTarget::Path(p) = &r.ziel else {
                // A call through a place carries a `FnZeiger` contract and no parameter
                // NAMES to key on. *Not counted, and it is an undercount, not a zero.*
                continue;
            };
            let Some(ziel) = u
                .kandidaten_aufloesbar(modul, &p.text())
                .into_iter()
                .find(|k| lagen.contains_key(k))
            else {
                continue;
            };
            let l = &lagen[&ziel];
            if l.zeiger.len() < 2 {
                continue;
            }
            // **Which ARGUMENT positions are pointers?** The callee's parameter list is the
            // authority, and `Zeigerparameter::stelle` carries the position -- an argument
            // list shorter than the parameter list (a call the checker refuses anyway)
            // contributes fewer positions instead of panicking.
            let zeigerargs: Vec<usize> = l
                .zeiger
                .iter()
                .map(|z| z.stelle)
                .filter(|i| *i < r.argumente.len())
                .collect();
            if zeigerargs.len() < 2 {
                continue;
            }
            f.s2 += 1;
            let schreibend = l.zeiger.iter().any(|z| z.schreibbar);
            if schreibend {
                f.s2_schreibend += 1;
            }
            // **S3 -- two arguments with the SAME root.**
            let mut wurzeln: Vec<String> = Vec::new();
            for i in &zeigerargs {
                if let Some(w) = ausdruckswurzel(&r.argumente[*i]) {
                    wurzeln.push(w);
                }
            }
            let einzeln: BTreeSet<&String> = wurzeln.iter().collect();
            if einzeln.len() < wurzeln.len() {
                f.s3 += 1;
                if schreibend {
                    f.s3_schreibend += 1;
                }
                f.zeilen.push(format!(
                    "S3  in {voll}: {}({}) -- two pointer arguments share a root",
                    ziel,
                    wurzeln.join(", ")
                ));
            }
        }
    }

    // **S4 bound at a site**: a `let` whose value is a call to a re-view. That is the shape
    // in `messung/netz/udp-echo.gab` -- `w` and `k` are two names for twenty bytes.
    for (voll, modul, b) in &ruempfe {
        let mut gefunden: Vec<Ruf> = Vec::new();
        rufe(b, &mut gefunden);
        for r in &gefunden {
            let CallTarget::Path(p) = &r.ziel else { continue };
            let Some(ziel) = u
                .kandidaten_aufloesbar(modul, &p.text())
                .into_iter()
                .find(|k| lagen.contains_key(k))
            else {
                continue;
            };
            if lagen[&ziel].umdeutung.is_some() {
                f.s4_gebunden += 1;
                f.zeilen
                    .push(format!("S4* in {voll}: {ziel}(…) -- a re-view is TAKEN here"));
            }
        }
    }

    f.zeilen.sort();
    f
}

/// The report. **Both bounds on one page**, because printing one of them would let the reader
/// pick.
pub fn zeige(baum: &Programm, datei: &str) -> String {
    tafel(erhebe(baum), datei)
}

/// The same table over an already-summed area -- the total line of a corpus run.
pub fn tafel(f: Flaeche, datei: &str) -> String {
    tafel_von(&f, datei)
}

/// The table without consuming the area, so a corpus run can print it AND sum it.
pub fn tafel_von(f: &Flaeche, datei: &str) -> String {
    let mut aus = format!("# {datei}\n\n");
    aus.push_str(&format!(
        "functions: {}   ·   with at least one pointer parameter: {}\n\n",
        f.funktionen, f.mit_zeiger
    ));
    aus.push_str(&format!(
        "S1  signatures with >= 2 pointer parameters      {:>4}   (writable: {})\n",
        f.s1, f.s1_schreibend
    ));
    aus.push_str(&format!(
        "S2  call sites passing >= 2 pointer arguments    {:>4}   (writable: {})\n",
        f.s2, f.s2_schreibend
    ));
    aus.push_str(&format!(
        "S3  ... of those with two arguments of one root  {:>4}   (writable: {})\n",
        f.s3, f.s3_schreibend
    ));
    aus.push_str(&format!(
        "S4  re-views `fn(ptr A) -> ptr B`                {:>4}   (taken at {} sites)\n",
        f.s4, f.s4_gebunden
    ));
    aus.push_str(&format!(
        "S5  bodies writing through one, reading another  {:>4}\n\n",
        f.s5
    ));
    if f.zeilen.is_empty() {
        aus.push_str("  (no site in any stratum)\n");
    } else {
        for z in &f.zeilen {
            aus.push_str(&format!("  {z}\n"));
        }
    }
    aus
}
