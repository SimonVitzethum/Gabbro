//! The correspondence-certificate printer: `gabbro corr-lean <file.gab>` (T2 minimal).
//!
//! For each emitted function body this prints the correspondence certificate as a Lean
//! term: which Gabbro statement maps to which emitted C statement (a `CertRow` per
//! statement, in emission order), the local/parameter map (`vm`/`pp`/`ks`, the `EnvRel`
//! data) and the layout facts (`lay`). The vocabulary is exactly
//! `grammatik/Grammatik/Korrespondenz104.lean`: the four rows 104's emitted C uses
//! (`voidB`, `store100`, `callLies`, `retLoad`). Every other form is a NAMED refusal,
//! never a silent drop and never a truncation: a body is either certified whole or
//! refused by name, and without zero refusals no assembled `Cert104` literal is printed.
//!
//! What the printer proves and what it quotes:
//! - statement map, parameter positions and kinds, table counts and field layout come
//!   from the parsed tree (a `const` count is resolved through `KonstDecl`, a type
//!   alias through `TypDecl`; anything else is a refusal);
//! - the `ks` VALUES (the fixed index the model pins, `0` for 104) are model data, not
//!   source data: the printer proves the position and the kind and quotes the value
//!   with a `MODEL DATUM` comment. Lean still checks the value (`certOk` decides it).
//!
//! The checker runs before this (like `emit` and `zeugnis`): a certificate over a tree
//! the passes refused would certify a program Gabbro rejects.

use gabbro_syntax::ast::*;

/// A refused form: where it stands and what it is. Rendered as a `-- REFUSAL:` line.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Refusal {
    /// Which function body (or declaration) holds the form.
    pub wo: String,
    /// The form, named as precisely as the tree allows.
    pub was: String,
}

impl Refusal {
    fn zeige(&self) -> String {
        format!("-- REFUSAL: {}: {}\n", self.wo, self.was)
    }
}

/// How one C local (parameter order) maps back to Gabbro.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParamKind {
    /// A plain value parameter (`b : Betrag`): an `EnvRel` `vm` entry.
    Value,
    /// A table pointer parameter (`k : ptr<..> Konto`): an `EnvRel` `pp` entry.
    PtrTable(String),
    /// An index parameter (`i : index into Konto`): an `EnvRel` `ks` entry.
    IndexTable(String),
}

/// One certified function body: rows plus map plus layout notes for rendering.
#[derive(Debug, Clone)]
pub struct BodyCert {
    /// The Gabbro function name.
    pub name: String,
    /// Parameter names in C-local order.
    pub params: Vec<String>,
    /// Parameter kinds in C-local order.
    pub kinds: Vec<ParamKind>,
    /// The `CertRow` terms in emission order (`(void)` rows first).
    pub rows: Vec<String>,
    /// Layout facts used by a `store100`/`retLoad` row, if any.
    pub lay: Option<LayFacts>,
}

/// The layout facts behind one table field access.
#[derive(Debug, Clone)]
pub struct LayFacts {
    pub table: String,
    pub count_src: String,
    pub n: u128,
    pub field: String,
    pub field_ty: String,
    pub off: u32,
    pub ss: u32,
}

/// The whole unit: certified bodies plus every refusal.
#[derive(Debug, Clone, Default)]
pub struct UnitCert {
    pub bodies: Vec<BodyCert>,
    pub refusals: Vec<Refusal>,
}

impl UnitCert {
    fn refuse(&mut self, wo: &str, was: String) {
        self.refusals.push(Refusal {
            wo: wo.to_string(),
            was,
        });
    }
}

/// Name of a statement form for refusals.
fn stmt_name(art: &StmtArt) -> &'static str {
    match art {
        StmtArt::Let(_) => "let",
        StmtArt::LetSonst(_) => "let-else",
        StmtArt::Zuweisung(_) => "assignment",
        StmtArt::Wenn(_) => "if",
        StmtArt::Match(_) => "match",
        StmtArt::Schleife(_) => "loop",
        StmtArt::Bricht(_) => "breaking",
        StmtArt::Narrow(_) => "narrow",
        StmtArt::Sperrt(_) => "locks",
        StmtArt::Observiert(_) => "observes",
        StmtArt::Leave(_) => "leave",
        StmtArt::Next(_) => "next",
        StmtArt::Publish(_) => "publish",
        StmtArt::AwaitLoad(_) => "awaits",
        StmtArt::Exchange(_) => "exchange",
        StmtArt::Return(_) => "return",
        StmtArt::Ruf(_) => "call",
        StmtArt::LibraryCall(_) => "library call",
        StmtArt::Alloc(_) => "alloc",
        StmtArt::ResetArena(_) => "reset",
    }
}

/// Name of an expression form for refusals.
fn expr_name(e: &Expr) -> String {
    match &e.art {
        ExprArt::Zahl(v) => format!("literal {v}"),
        ExprArt::Gleitkomma { .. } => "float literal".to_string(),
        ExprArt::Wahr => "true".to_string(),
        ExprArt::Falsch => "false".to_string(),
        ExprArt::Ort(o) => format!("place `{}`", o.text()),
        ExprArt::FnWert(p) => format!("function value `{}`", p.text()),
        ExprArt::Ruf(r) => format!("call `{}`", r.ziel.text()),
        ExprArt::LibraryCall(_) => "library call".to_string(),
        ExprArt::Klammer(_) => "parenthesised".to_string(),
        ExprArt::Eingebaut(_) => "builtin".to_string(),
        ExprArt::Alt(o) => format!("old(`{}`)", o.text()),
        ExprArt::Ergebnis => "result".to_string(),
        ExprArt::Grund { grund, fall } => format!("reason {}::{}", grund.text, fall.text),
        ExprArt::Zaehle { .. } => "count".to_string(),
        ExprArt::Unaer(op, _) => format!("unary {op:?}"),
        ExprArt::Binaer(op, _, _) => format!("binary {op:?}"),
        ExprArt::ArrayLit(_) => "array literal".to_string(),
    }
}

/// A bare parameter variable: `i` with no suffix is C local `local`.
fn als_param(baum: &Expr, params: &[String]) -> Option<u32> {
    if let ExprArt::Ort(o) = &baum.art {
        if o.suffixe.is_empty() {
            return params.iter().position(|p| p == &o.basis.text).map(|i| i as u32);
        }
    }
    None
}

/// Byte size of an integer word.
fn wort_bytes(wort: &gabbro_syntax::kw::Kw) -> Option<u32> {
    use gabbro_syntax::kw::Kw;
    match wort {
        Kw::U8 | Kw::I8 => Option::Some(1),
        Kw::U16 | Kw::I16 => Option::Some(2),
        Kw::U32 | Kw::I32 => Option::Some(4),
        Kw::U64 | Kw::I64 => Option::Some(8),
        _ => Option::None,
    }
}

/// One pass over the unit's declarations: tables, literal consts, type aliases.
struct Umgebung<'a> {
    tabellen: Vec<&'a Tabelle>,
    konstanten: Vec<&'a KonstDecl>,
    typen: Vec<&'a TypDecl>,
}

impl<'a> Umgebung<'a> {
    fn sammle(baum: &'a Programm, um: &mut Umgebung<'a>) {
        for item in &baum.items {
            Self::item(item, um);
        }
    }

    fn item(item: &'a Item, um: &mut Umgebung<'a>) {
        match &item.art {
            ItemArt::Modul(m) => {
                for i in &m.items {
                    Self::item(i, um);
                }
            }
            ItemArt::Tabelle(t) => um.tabellen.push(t),
            ItemArt::Konst(k) => um.konstanten.push(k),
            ItemArt::Typ(t) => um.typen.push(t),
            _ => {}
        }
    }

    /// A translation-time count: a literal or a `const` holding one.
    fn anzahl(&self, e: &Expr) -> Option<(u128, String)> {
        match &e.art {
            ExprArt::Zahl(v) => Some((*v, format!("{v}"))),
            ExprArt::Ort(o) if o.suffixe.is_empty() => {
                for k in &self.konstanten {
                    if k.name.text == o.basis.text {
                        if let ExprArt::Zahl(v) = &k.wert.art {
                            return Some((*v, format!("{} = {v}", k.name.text)));
                        }
                    }
                }
                None
            }
            _ => None,
        }
    }

    /// Byte size of a slot field type: integers by word, `bool` by
    /// storage, aliases by resolution.
    fn feld_bytes(&self, t: &TypExpr, tiefe: u32) -> Option<u32> {
        if tiefe > 8 {
            return None;
        }
        match t {
            TypExpr::Int(i) => wort_bytes(&i.wort),
            TypExpr::Bool(_) => Some(1),
            TypExpr::Pfad(p) => {
                let name = p.einfach()?.text.clone();
                for td in &self.typen {
                    if td.name.text == name {
                        let rumpf = td.rumpf.as_ref()?;
                        return self.feld_bytes(rumpf, tiefe + 1);
                    }
                }
                // A bare path that is no alias has no size here.
                None
            }
            _ => None,
        }
    }

    /// Layout of field `feld` of table `tabelle`: count, offset, record size.
    fn layout(&self, tabelle: &str, feld: &str) -> Option<LayFacts> {
        let t = self.tabellen.iter().find(|t| t.name.text == tabelle)?;
        let cap = t.kapazitaet.as_ref()?;
        let (n, count_src) = self.anzahl(cap)?;
        let slot = t.slot.as_ref()?;
        let mut off: u32 = 0;
        for f in &slot.felder {
            let groesse = match &f.typ {
                SlotTyp::Typ(te) => self.feld_bytes(te, 0)?,
                SlotTyp::Wrapping(i) => wort_bytes(&i.wort)?,
            };
            if f.name.text == feld {
                let mut ss = 0;
                for g in &slot.felder {
                    ss += match &g.typ {
                        SlotTyp::Typ(te) => self.feld_bytes(te, 0)?,
                        SlotTyp::Wrapping(i) => wort_bytes(&i.wort)?,
                    };
                }
                let field_ty = match &f.typ {
                    SlotTyp::Typ(TypExpr::Int(i)) => format!("{i:?}"),
                    SlotTyp::Typ(TypExpr::Bool(_)) => "bool".to_string(),
                    SlotTyp::Typ(TypExpr::Pfad(p)) => p.text(),
                    SlotTyp::Typ(_) => "compound".to_string(),
                    SlotTyp::Wrapping(i) => format!("wrapping {i:?}"),
                };
                return Some(LayFacts {
                    table: tabelle.to_string(),
                    count_src,
                    n,
                    field: feld.to_string(),
                    field_ty,
                    off,
                    ss,
                });
            }
            off += groesse;
        }
        None
    }
}

/// `k.slots[i].stand`: pointer-param base `kp` over table `tab`, index-param `ip`,
/// field `feld`. The middle `.slots` word is the emitter's slot-array spelling.
fn als_slot(ort: &Ort, params: &[String], kinds: &[ParamKind]) -> Option<(u32, u32, String, String)> {
    let kp = params.iter().position(|p| p == &ort.basis.text)? as u32;
    let tab = match kinds.get(kp as usize)? {
        ParamKind::PtrTable(t) => t.clone(),
        _ => return None,
    };
    if let [OrtSuffix::Feld(_), OrtSuffix::Index(idx), OrtSuffix::Feld(feld)] = &ort.suffixe[..] {
        let ip = als_param(idx, params)?;
        if !matches!(kinds.get(ip as usize)?, ParamKind::IndexTable(_)) {
            return None;
        }
        return Some((kp, ip, tab, feld.text.clone()));
    }
    None
}

/// Certify one `impl fn` body. Only einzahlen/lies-shaped bodies have rows.
fn funktion(um: &Umgebung, f: &FnDecl, cert: &mut UnitCert) {
    let name = f.name.text.clone();
    if !matches!(f.klasse, Some(FnKlasse::Impl)) {
        cert.refuse(
            &format!("function `{name}`"),
            format!(
                "no emitted body ({}): only `impl fn` bodies have rows",
                match &f.klasse {
                    None => "no class".to_string(),
                    Some(k) => format!("`{}`", k.text()),
                }
            ),
        );
        return;
    }
    if name != "einzahlen" && name != "lies" {
        cert.refuse(
            &format!("function `{name}`"),
            "outside the 104 certificate: only `einzahlen` and `lies` have rows".to_string(),
        );
        return;
    }
    let block = match &f.rumpf {
        FnRumpf::Block(b) => b,
        _ => {
            cert.refuse(
                &format!("function `{name}`"),
                "body is not a block: only block bodies have rows".to_string(),
            );
            return;
        }
    };
    // Parameter map: C locals in parameter order.
    let params: Vec<String> = f.parameter.iter().map(|p| p.name.text.clone()).collect();
    let mut kinds: Vec<ParamKind> = Vec::new();
    for p in &f.parameter {
        kinds.push(match &p.typ {
            TypExpr::Zeiger(z) => match &z.ziel {
                TypExpr::Pfad(q) => ParamKind::PtrTable(q.text()),
                _ => ParamKind::Value,
            },
            TypExpr::Index { tabelle, .. } => ParamKind::IndexTable(tabelle.text.clone()),
            _ => ParamKind::Value,
        });
    }
    let mut rows: Vec<String> = Vec::new();
    let mut lay: Option<LayFacts> = None;
    let mut benutzt = vec![false; params.len()];
    let mut merke = |l: u32| {
        if let Some(b) = benutzt.get_mut(l as usize) {
            *b = true;
        }
    };
    let wo = format!("function `{name}`");
    // The end marker: `lies` returns its load (a row); `einzahlen` falls off
    // the end of its `void` body (no row, like the emitter's missing `return;`).
    let mut ende_ok = name == "einzahlen";
    for st in &block.anweisungen {
        match &st.art {
            StmtArt::Zuweisung(z) => {
                if z.op != ZuwOp::Setzt {
                    cert.refuse(&wo, format!("`{:?}` assignment: only `=` has a row", z.op));
                    return;
                }
                let Some((kp, ip, tab, feld)) = als_slot(&z.ziel, &params, &kinds) else {
                    cert.refuse(
                        &wo,
                        format!(
                            "slot store to `{}`: only `param.slots[param].field` has a row",
                            z.ziel.text()
                        ),
                    );
                    return;
                };
                if !matches!(z.wert.art, ExprArt::Zahl(100)) {
                    cert.refuse(
                        &wo,
                        format!("slot store of {}: only the constant 100 has a row", expr_name(&z.wert)),
                    );
                    return;
                }
                merke(kp);
                merke(ip);
                match um.layout(&tab, &feld) {
                    Some(l) => lay = Some(l),
                    None => {
                        cert.refuse(
                            &wo,
                            format!("slot store to `{tab}.{feld}`: layout has no byte size"),
                        );
                        return;
                    }
                }
                rows.push(format!("CertRow.store100 {kp} {ip}"));
            }
            StmtArt::Ruf(r) => {
                let ziel = r.ziel.text();
                if ziel != "lies" {
                    cert.refuse(&wo, format!("call to `{ziel}`: only `lies` has a callee relation"));
                    return;
                }
                if r.argumente.len() != 2 {
                    cert.refuse(
                        &wo,
                        format!("call to `lies` with {} arguments: only arity 2 has a row", r.argumente.len()),
                    );
                    return;
                }
                let (Some(a), Some(b)) = (als_param(&r.argumente[0], &params), als_param(&r.argumente[1], &params))
                else {
                    cert.refuse(&wo, "call to `lies`: only parameter arguments have a row".to_string());
                    return;
                };
                merke(a);
                merke(b);
                rows.push(format!("CertRow.callLies {a} {b}"));
            }
            StmtArt::Return(opt) => match opt {
                None => {
                    if f.ergebnis.is_some() {
                        cert.refuse(&wo, "`return;` with a declared result: no row".to_string());
                        return;
                    }
                    ende_ok = true;
                }
                Some(e) => {
                    let ExprArt::Ort(o) = &e.art else {
                        cert.refuse(&wo, format!("return of {}: only a slot load has a row", expr_name(e)));
                        return;
                    };
                    let Some((kp, ip, tab, feld)) = als_slot(o, &params, &kinds) else {
                        cert.refuse(&wo, format!("return of `{}`: only `param.slots[param].field` has a row", o.text()));
                        return;
                    };
                    merke(kp);
                    merke(ip);
                    match um.layout(&tab, &feld) {
                        Some(l) => lay = Some(l),
                        None => {
                            cert.refuse(&wo, format!("return of `{tab}.{feld}`: layout has no byte size"));
                            return;
                        }
                    }
                    rows.push(format!("CertRow.retLoad {kp} {ip}"));
                    ende_ok = true;
                }
            },
            _ => {
                cert.refuse(
                    &wo,
                    format!("statement `{}`: no correspondence row (104 uses assign, call, return only)", stmt_name(&st.art)),
                );
                return;
            }
        }
    }
    if !ende_ok {
        cert.refuse(&wo, "body ends without a row: only `return <slot>` ends a body".to_string());
        return;
    }
    // The emitter writes `(void)x;` for every unused parameter, first.
    let mut alle: Vec<String> = Vec::new();
    for (i, b) in benutzt.iter().enumerate() {
        if !b {
            alle.push(format!("CertRow.voidB {i}"));
        }
    }
    alle.append(&mut rows);
    cert.bodies.push(BodyCert {
        name,
        params,
        kinds,
        rows: alle,
        lay,
    });
}

/// Certify a whole unit: every `impl fn` body, refusals for the rest.
pub fn zertifiziere(baum: &Programm) -> UnitCert {
    let mut um = Umgebung {
        tabellen: Vec::new(),
        konstanten: Vec::new(),
        typen: Vec::new(),
    };
    Umgebung::sammle(baum, &mut um);
    let mut cert = UnitCert::default();
    fn gehe<'a>(um: &Umgebung<'a>, items: &'a [Item], cert: &mut UnitCert) {
        for item in items {
            match &item.art {
                ItemArt::Modul(m) => gehe(um, &m.items, cert),
                ItemArt::Funktion(f) => funktion(um, f, cert),
                _ => {}
            }
        }
    }
    gehe(&um, &baum.items, &mut cert);
    cert
}

fn art_text(k: &ParamKind) -> String {
    match k {
        ParamKind::Value => "value".to_string(),
        ParamKind::PtrTable(t) => format!("table {t}"),
        ParamKind::IndexTable(t) => format!("index {t}"),
    }
}

/// Render one body: rows, map (`vm`/`pp`/`ks`) and layout, as Lean comments.
fn zeige_body(b: &BodyCert) -> String {
    let mut aus = String::new();
    let params: Vec<String> = b
        .params
        .iter()
        .enumerate()
        .map(|(i, p)| format!("{p}:{i} ({})", art_text(&b.kinds[i])))
        .collect();
    aus.push_str(&format!("-- function `{}`: params {}\n", b.name, params.join(", ")));
    aus.push_str(&format!("--   rows := [{}]\n", b.rows.join(", ")));
    let vm: Vec<String> = b
        .kinds
        .iter()
        .enumerate()
        .filter(|(_, k)| **k == ParamKind::Value)
        .map(|(i, _)| format!("{i}"))
        .collect();
    let pp: Vec<String> = b
        .kinds
        .iter()
        .enumerate()
        .filter_map(|(i, k)| match k {
            ParamKind::PtrTable(_) => Some(format!("({i}, ())")),
            _ => None,
        })
        .collect();
    let ks: Vec<String> = b
        .kinds
        .iter()
        .enumerate()
        .filter_map(|(i, k)| match k {
            ParamKind::IndexTable(_) => Some(i),
            _ => None,
        })
        .map(|i| format!("({i}, 0)"))
        .collect();
    aus.push_str(&format!("--   vm := [{}]\n", vm.join(", ")));
    aus.push_str(&format!("--   pp := [{}]\n", pp.join(", ")));
    aus.push_str(&format!("--   ks := [{}]\n", ks.join(", ")));
    let index_note: Vec<String> = b
        .kinds
        .iter()
        .enumerate()
        .filter_map(|(i, k)| match k {
            ParamKind::IndexTable(t) => Some(format!("local {i} of index param over table `{t}`")),
            _ => None,
        })
        .collect();
    if !index_note.is_empty() {
        aus.push_str("--   -- MODEL DATUM: each ks value 0 is fixed by refD; the source proves ");
        aus.push_str(&index_note.join("; "));
        aus.push('\n');
    }
    match &b.lay {
        Some(l) => aus.push_str(&format!(
            "--   lay := <{}, {}, 0> -- table `{}`: count {}; field `{}`: {} at offset {}, record {} bytes\n",
            l.n, l.ss, l.table, l.count_src, l.field, l.field_ty, l.off, l.ss
        )),
        None => aus.push_str("--   lay: none (no slot access)\n"),
    }
    aus
}

/// Render the whole certificate: per-body fragments, then -- with zero refusals --
/// the assembled `Cert104` literal for `Korrespondenz104.lean`, then the
/// general `GRow` section for `Korrespondenz.lean`.
pub fn zeige(baum: &Programm, datei: &str) -> String {
    let cert = zertifiziere(baum);
    let mut aus = format!("-- corr-lean certificate for `{datei}`: T2 minimal, 104 forms only.\n");
    for b in &cert.bodies {
        aus.push_str(&zeige_body(b));
    }
    for r in &cert.refusals {
        aus.push_str(&r.zeige());
    }
    if cert.refusals.is_empty() {
        let ein = cert.bodies.iter().find(|b| b.name == "einzahlen");
        let lies = cert.bodies.iter().find(|b| b.name == "lies");
        match (ein, lies) {
            (Some(e), Some(l)) => {
                let felder = |b: &BodyCert| {
                    let vm: Vec<String> = b
                        .kinds
                        .iter()
                        .enumerate()
                        .filter(|(_, k)| **k == ParamKind::Value)
                        .map(|(i, _)| format!("{i}"))
                        .collect();
                    let pp: Vec<String> = b
                        .kinds
                        .iter()
                        .enumerate()
                        .filter_map(|(i, k)| match k {
                            ParamKind::PtrTable(_) => Some(format!("({i}, ())")),
                            _ => None,
                        })
                        .collect();
                    let ks: Vec<String> = b
                        .kinds
                        .iter()
                        .enumerate()
                        .filter_map(|(i, k)| match k {
                            ParamKind::IndexTable(_) => Some(format!("({i}, 0)")),
                            _ => None,
                        })
                        .collect();
                    (vm.join(", "), pp.join(", "), ks.join(", "))
                };
                let (evm, epp, eks) = felder(e);
                let (lvm, lpp, lks) = felder(l);
                let lay = e.lay.as_ref().or(l.lay.as_ref()).map(|l| format!("⟨{}, {}, {}⟩", l.n, l.ss, l.off));
                match lay {
                    Some(lay) => {
                        aus.push_str("-- The two bodies assemble to this Cert104 value (paste into Korrespondenz104.lean as printed104):\n");
                        aus.push_str(&format!("{{ einRows := [{}],\n", e.rows.join(", ")));
                        aus.push_str(&format!("  liesRows := [{}],\n", l.rows.join(", ")));
                        aus.push_str(&format!("  lay := {lay},\n"));
                        aus.push_str(&format!("  vmEin := [{evm}], ppEin := [{epp}], ksEin := [{eks}], -- ks values: MODEL DATUM, see above\n"));
                        aus.push_str(&format!("  vmLies := [{lvm}], ppLies := [{lpp}], ksLies := [{lks}] }} -- ks values: MODEL DATUM, see above\n"));
                    }
                    None => aus.push_str("-- REFUSAL: unit: no slot access, so no layout facts\n"),
                }
            }
            _ => aus.push_str("-- REFUSAL: unit: the assembled Cert104 needs `einzahlen` and `lies`\n"),
        }
    }
    aus.push_str(&gzeige(baum, datei));
    aus
}

#[cfg(test)]
mod tests {
    use super::*;

    const MINI: &str = r#"
module probe::mini {
const N : u32 = 2;
type Betrag = u32 in 0 .. 10;
table Konto count N {
    slot {
        stand : Betrag,
    }
}
impl fn einzahlen(k : ptr<normal, rw> Konto, i : index into Konto, b : Betrag)
{
    k.slots[i].stand = 100;
    lies(k, i);
}
impl fn lies(k : ptr<normal, r> Konto, i : index into Konto) -> Betrag
{
    return k.slots[i].stand;
}
}
"#;

    fn parse(quelle: &str) -> Programm {
        let (baum, absagen) = gabbro_syntax::lies("probe.gab", quelle);
        assert_eq!(absagen.fehler_zahl(), 0, "test source must parse");
        baum
    }

    #[test]
    fn druckt_104_zeilen_und_layout() {
        let cert = zertifiziere(&parse(MINI));
        assert!(cert.refusals.is_empty(), "unexpected refusals: {:?}", cert.refusals);
        assert_eq!(cert.bodies.len(), 2);
        let ein = cert.bodies.iter().find(|b| b.name == "einzahlen").expect("einzahlen");
        assert_eq!(ein.rows, vec!["CertRow.voidB 2", "CertRow.store100 0 1", "CertRow.callLies 0 1"]);
        let lies = cert.bodies.iter().find(|b| b.name == "lies").expect("lies");
        assert_eq!(lies.rows, vec!["CertRow.retLoad 0 1"]);
        let lay = ein.lay.as_ref().expect("layout");
        assert_eq!((lay.n, lay.ss, lay.off), (2, 4, 0));
        assert_eq!(lay.count_src, "N = 2");
        let text = zeige(&parse(MINI), "probe.gab");
        assert!(text.contains("{ einRows := [CertRow.voidB 2, CertRow.store100 0 1, CertRow.callLies 0 1],"));
        assert!(text.contains("liesRows := [CertRow.retLoad 0 1],"));
        assert!(text.contains("lay := ⟨2, 4, 0⟩,"));
        assert!(text.contains("vmEin := [2], ppEin := [(0, ())], ksEin := [(1, 0)]"));
        assert!(text.contains("vmLies := [], ppLies := [(0, ())], ksLies := [(1, 0)]"));
    }

    #[test]
    fn verweigert_let_mit_namen() {
        let src = MINI.replace("    lies(k, i);", "    let x = 1;\n    lies(k, i);");
        let cert = zertifiziere(&parse(&src));
        assert_eq!(cert.bodies.len(), 1, "only lies stays certified");
        assert_eq!(cert.refusals.len(), 1);
        assert!(cert.refusals[0].was.contains("`let`"), "refusal must name the form: {:?}", cert.refusals);
        assert!(!zeige(&parse(&src), "p.gab").contains("{ einRows"), "no assembled literal beside a refusal");
    }

    #[test]
    fn verweigert_wenn_mit_namen() {
        let src = MINI.replace("    lies(k, i);", "    if b == 1 { lies(k, i); }");
        let cert = zertifiziere(&parse(&src));
        assert!(cert.refusals.iter().any(|r| r.was.contains("`if`")), "if must be refused by name: {:?}", cert.refusals);
    }

    #[test]
    fn verweigert_fremden_ruf_mit_namen() {
        let src = MINI.replace("lies(k, i);", "fremd(k, i);");
        let cert = zertifiziere(&parse(&src));
        assert!(cert.refusals.iter().any(|r| r.was.contains("`fremd`")), "foreign callee must be refused by name: {:?}", cert.refusals);
    }

    #[test]
    fn verweigert_falsche_konstante_mit_wert() {
        let src = MINI.replace("k.slots[i].stand = 100;", "k.slots[i].stand = 99;");
        let cert = zertifiziere(&parse(&src));
        assert!(cert.refusals.iter().any(|r| r.was.contains("99")), "wrong constant must be refused with its value: {:?}", cert.refusals);
    }

    #[test]
    fn verweigert_dritte_funktion_mit_namen() {
        let src = MINI.replace(
            "impl fn lies",
            "impl fn extra(k : ptr<normal, r> Konto, i : index into Konto) -> Betrag\n{\n    return k.slots[i].stand;\n}\nimpl fn lies",
        );
        let cert = zertifiziere(&parse(&src));
        let text = zeige(&parse(&src), "p.gab");
        assert!(text.contains("-- REFUSAL: function `extra`"), "third function must be refused by name: {:?}", cert.refusals);
        assert!(!text.contains("liesRows :="), "no assembled literal beside a refusal");
    }

    #[test]
    fn verweigert_unbekannte_anzahl() {
        let src = MINI.replace("table Konto count N {", "table Konto count M {");
        let cert = zertifiziere(&parse(&src));
        assert!(cert.refusals.iter().any(|r| r.was.contains("layout")), "unknown count must fail the layout: {:?}", cert.refusals);
    }

    #[test]
    fn general_104_rows() {
        let cert = gzertifiziere(&parse(MINI));
        assert!(cert.refusals.is_empty(), "unexpected general refusals: {:?}", cert.refusals);
        let ein = cert.bodies.iter().find(|b| b.name == "einzahlen").expect("einzahlen");
        assert_eq!(
            ein.rows,
            vec![
                "GRow.void 2",
                "GRow.storeSlot 0 (.var 1) 2 4 0 (.int false .w32) (.lit 100)",
                "GRow.call 1 [.var 0, .var 1] none",
            ]
        );
        assert_eq!(ein.vm, vec!["2"]);
        assert_eq!(ein.pp, vec!["0"]);
        assert_eq!(ein.ks, vec!["(1, 0)"]);
        let lies = cert.bodies.iter().find(|b| b.name == "lies").expect("lies");
        assert_eq!(
            lies.rows,
            vec!["GRow.ret (some ((.int false .w32), (.ld (.slotA (.var 0) (.var 1) 2 4 0) (.int false .w32))))"]
        );
        assert!(lies.vm.is_empty());
        // The pasted Lean rows of Korrespondenz.lean match this output.
        let text = gzeige(&parse(MINI), "probe.gab");
        assert!(text.contains("GRow.storeSlot 0 (.var 1) 2 4 0 (.int false .w32) (.lit 100)"));
        assert!(text.contains("vm := [2], pp := [0], ks := [(1, 0)]"));
    }

    #[test]
    fn general_refuses_global_by_name() {
        let src = MINI.replace(
            "    k.slots[i].stand = 100;",
            "    k.slots[i].stand = 100;\n    g = 1;",
        );
        let cert = gzertifiziere(&parse(&src));
        assert!(
            cert.refusals.iter().any(|r| r.was.contains("`g`") || r.was.contains("globals")),
            "global store must be refused by name: {:?}",
            cert.refusals
        );
        assert!(cert.bodies.iter().all(|b| b.name != "einzahlen"), "refused body gets no rows");
        assert!(cert.bodies.iter().any(|b| b.name == "lies"), "clean body keeps its rows");
    }

    #[test]
    fn general_refuses_traverse_by_name() {
        let src = MINI.replace(
            "    lies(k, i);",
            "    traverse j over slots of k by unvisited\n        touches writes k.slots\n    {\n        lies(k, j);\n    }\n    lies(k, i);",
        );
        let parsed = parse(&src);
        let cert = gzertifiziere(&parsed);
        assert!(
            cert.refusals.iter().any(|r| r.was.contains("traverse") || r.was.contains("loop")),
            "traverse must be refused by name: {:?}",
            cert.refusals
        );
    }

    const IFMINI: &str = r#"
module probe::ifmini {
const N : u32 = 2;
type Betrag = u32 in 0 .. 10;
table Konto count N {
    slot {
        stand : Betrag,
    }
}
impl fn setzt(k : ptr<normal, rw> Konto, i : index into Konto, b : Betrag)
{
    if b == 1 { k.slots[i].stand = 5; } else { k.slots[i].stand = 6; }
}
}
"#;

    #[test]
    fn general_if_else_rows() {
        let cert = gzertifiziere(&parse(IFMINI));
        assert!(cert.refusals.is_empty(), "unexpected general refusals: {:?}", cert.refusals);
        let body = cert.bodies.iter().find(|b| b.name == "setzt").expect("setzt");
        assert_eq!(body.rows.len(), 1);
        assert!(
            body.rows[0].starts_with("GRow.ite (.cmp .eq"),
            "if/else must render one ite row: {:?}",
            body.rows
        );
        assert!(body.rows[0].contains("GRow.storeSlot 0 (.var 1) 2 4 0 (.int false .w32) (.lit 5)"));
        assert!(body.rows[0].contains("GRow.storeSlot 0 (.var 1) 2 4 0 (.int false .w32) (.lit 6)"));
    }

    const LITIDX: &str = r#"
module probe::litidx {
const N : u32 = 2;
type Betrag = u32 in 0 .. 10;
table Konto count N {
    slot {
        stand : Betrag,
    }
}
impl fn f(k : ptr<normal, rw> Konto)
{
    k.slots[0].stand = 30;
}
}
"#;

    #[test]
    fn general_literal_index_store() {
        let cert = gzertifiziere(&parse(LITIDX));
        assert!(cert.refusals.is_empty(), "unexpected general refusals: {:?}", cert.refusals);
        let body = cert.bodies.iter().find(|b| b.name == "f").expect("f");
        assert_eq!(
            body.rows,
            vec!["GRow.storeSlot 0 (.lit 0) 2 4 0 (.int false .w32) (.lit 30)"]
        );
    }

    const LETOP: &str = r#"
module probe::letop {
const N : u32 = 2;
type Betrag = u32 in 0 .. 10;
table Konto count N {
    slot {
        stand : Betrag,
    }
}
impl fn f(k : ptr<normal, rw> Konto, i : index into Konto, b : Betrag)
{
    let v : Betrag = b + 1;
    v += 2;
    k.slots[i].stand = v;
}
}
"#;

    #[test]
    fn general_let_and_setop_rows() {
        let cert = gzertifiziere(&parse(LETOP));
        assert!(cert.refusals.is_empty(), "unexpected general refusals: {:?}", cert.refusals);
        let body = cert.bodies.iter().find(|b| b.name == "f").expect("f");
        assert_eq!(body.rows.len(), 3);
        assert!(body.rows[0].starts_with("GRow.bindLet 3 ("), "let binds C local 3: {:?}", body.rows);
        assert!(body.rows[0].contains(".bin .add CIT.u32 (.var 2) (.lit 1)"), "add in u32: {:?}", body.rows);
        assert!(body.rows[1].starts_with("GRow.setOp 3 ("), "+= on the let local: {:?}", body.rows);
        assert!(body.rows[2].starts_with("GRow.storeSlot 0 (.var 1) 2 4 0"), "store of the local: {:?}", body.rows);
    }
}

/// Render an `if/else if/else` chain as a general `ite` row: the arms
/// are row lists of their own (arm `let`s do not escape, but the C
/// local counter threads on, monotonically).
fn gite(
    sc: &mut GScope,
    um: &Umgebung,
    impls: &[String],
    f: &FnDecl,
    w: &WennStmt,
    wo: &str,
    cert: &mut GUnitCert,
    lay: &mut Option<LayFacts>,
    benutzt: &mut [bool],
) -> Option<String> {
    fn arme(
        sc: &mut GScope,
        um: &Umgebung,
        impls: &[String],
        f: &FnDecl,
        zweige: &[(Expr, Block)],
        sonst: &Option<Block>,
        wo: &str,
        cert: &mut GUnitCert,
        lay: &mut Option<LayFacts>,
        benutzt: &mut [bool],
    ) -> Option<String> {
        let Some(((cond, then), rest)) = zweige.split_first() else {
            return None;
        };
        let cc = match gcx(sc, um, cond, &mut *benutzt) {
            Ok(c) => c,
            Err(was) => {
                cert.refuse(wo, format!("`if` condition of {was}"));
                return None;
            }
        };
        let mut arm = sc.clone();
        let mut then_rows = Vec::new();
        let mut ende = false;
        if !gblock(&mut arm, um, impls, f, then, wo, cert, &mut then_rows, lay, &mut ende, &mut *benutzt) {
            return None;
        }
        sc.next = sc.next.max(arm.next);
        let else_rows = if rest.is_empty() {
            match sonst {
                Some(b) => {
                    let mut arm = sc.clone();
                    let mut rows = Vec::new();
                    let mut ende = false;
                    if !gblock(&mut arm, um, impls, f, b, wo, cert, &mut rows, lay, &mut ende, &mut *benutzt) {
                        return None;
                    }
                    sc.next = sc.next.max(arm.next);
                    rows
                }
                None => Vec::new(),
            }
        } else {
            let mut arm = sc.clone();
            let nested = arme(&mut arm, um, impls, f, rest, sonst, wo, cert, lay, &mut *benutzt)?;
            sc.next = sc.next.max(arm.next);
            vec![nested]
        };
        Some(format!("GRow.ite ({cc}) [{}] [{}]", then_rows.join(", "), else_rows.join(", ")))
    }
    arme(sc, um, impls, f, &w.zweige, &w.sonst, wo, cert, lay, &mut *benutzt)
}

/// Certify one `impl fn` body in general syntax.
fn gfunktion(um: &Umgebung, impls: &[String], f: &FnDecl, cert: &mut GUnitCert) {
    let name = f.name.text.clone();
    if !matches!(f.klasse, Some(FnKlasse::Impl)) {
        cert.refuse(
            &format!("function `{name}`"),
            match &f.klasse {
                None => "no class: only `impl fn` bodies have rows".to_string(),
                Some(k) => format!("`{}`: only `impl fn` bodies have rows", k.text()),
            },
        );
        return;
    }
    let block = match &f.rumpf {
        FnRumpf::Block(b) => b,
        _ => {
            cert.refuse(
                &format!("function `{name}`"),
                "body is not a block: only block bodies have rows".to_string(),
            );
            return;
        }
    };
    let wo = format!("function `{name}`");
    let params: Vec<String> = f.parameter.iter().map(|p| p.name.text.clone()).collect();
    let mut sc = GScope {
        params: params.clone(),
        widths: Vec::new(),
        ptrs: Vec::new(),
        locals: Vec::new(),
        next: params.len() as u32,
    };
    let mut kinds: Vec<ParamKind> = Vec::new();
    for p in &f.parameter {
        kinds.push(match &p.typ {
            TypExpr::Zeiger(z) => match &z.ziel {
                TypExpr::Pfad(q) => {
                    sc.ptrs.push((p.name.text.clone(), q.text()));
                    ParamKind::PtrTable(q.text())
                }
                _ => ParamKind::Value,
            },
            TypExpr::Index { tabelle, .. } => ParamKind::IndexTable(tabelle.text.clone()),
            t => {
                if let Some(w) = width_of_typ(um, t) {
                    sc.widths.push((p.name.text.clone(), w));
                }
                ParamKind::Value
            }
        });
    }
    let mut benutzt = vec![false; params.len()];
    let mut rows: Vec<String> = Vec::new();
    let mut lay: Option<LayFacts> = None;
    let mut ende_ok = f.ergebnis.is_none();
    if !gblock(&mut sc, um, impls, f, block, &wo, cert, &mut rows, &mut lay, &mut ende_ok, &mut benutzt) {
        return;
    }
    if !ende_ok {
        cert.refuse(&wo, "body ends without a row: only `return <expr>` ends a valued body".to_string());
        return;
    }
    // The emitter writes `(void)x;` for every unused parameter, first.
    let mut alle: Vec<String> = Vec::new();
    for (i, used) in benutzt.iter().enumerate() {
        if !used {
            alle.push(format!("GRow.void {i}"));
        }
    }
    alle.append(&mut rows);
    let vm: Vec<String> = kinds
        .iter()
        .enumerate()
        .filter(|(_, k)| **k == ParamKind::Value)
        .map(|(i, _)| format!("{i}"))
        .collect();
    let pp: Vec<String> = kinds
        .iter()
        .enumerate()
        .filter_map(|(i, k)| match k {
            ParamKind::PtrTable(_) => Some(format!("{i}")),
            _ => None,
        })
        .collect();
    let ks: Vec<String> = kinds
        .iter()
        .enumerate()
        .filter_map(|(i, k)| match k {
            ParamKind::IndexTable(_) => Some(format!("({i}, 0)")),
            _ => None,
        })
        .collect();
    cert.bodies.push(GBodyCert {
        name,
        rows: alle,
        vm,
        pp,
        ks,
        lay,
    });
}

/// Certify a whole unit in general syntax: every `impl fn` body.
pub fn gzertifiziere(baum: &Programm) -> GUnitCert {
    let mut um = Umgebung {
        tabellen: Vec::new(),
        konstanten: Vec::new(),
        typen: Vec::new(),
    };
    Umgebung::sammle(baum, &mut um);
    let mut impls: Vec<String> = Vec::new();
    fn sammle_impl(items: &[Item], impls: &mut Vec<String>) {
        for item in items {
            match &item.art {
                ItemArt::Modul(m) => sammle_impl(&m.items, impls),
                ItemArt::Funktion(f) => {
                    if matches!(f.klasse, Some(FnKlasse::Impl)) {
                        impls.push(f.name.text.clone());
                    }
                }
                _ => {}
            }
        }
    }
    sammle_impl(&baum.items, &mut impls);
    let mut cert = GUnitCert::default();
    fn gehe<'a>(um: &Umgebung<'a>, impls: &[String], items: &'a [Item], cert: &mut GUnitCert) {
        for item in items {
            match &item.art {
                ItemArt::Modul(m) => gehe(um, impls, &m.items, cert),
                ItemArt::Funktion(f) => gfunktion(um, impls, f, cert),
                _ => {}
            }
        }
    }
    gehe(&um, &impls, &baum.items, &mut cert);
    cert
}

// ==================== general rows (T2 general) ====================
//
// Renders every `impl fn` body as general `GRow` data
// (`grammatik/Grammatik/Korrespondenz.lean`): `void`, `storeSlot`,
// `setVar`, `setOp`, `bindLet`, `ite`, `call`, `ret`. The expression
// renderer covers exactly the Lean `exprOk` families (literals,
// locals, `+`/`-`/`*`, `==`/`<`/`<=`/`>`, slot loads); everything else
// is a named `GREFUSAL`, never a silent drop. Bodies with a refusal
// get no literal. What the printer cannot know from the source it
// refuses: globals and named-table bases (no block numbers), `let`
// calls (no callee signature for the result type), `traverse` (no
// bound rendering yet -- the Lean row family exists).

/// An integer width for CIT/CTy rendering.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct IntW {
    sgn: bool,
    w: &'static str,
}

impl IntW {
    fn bits(&self) -> u32 {
        match self.w {
            "w8" => 8,
            "w16" => 16,
            "w32" => 32,
            _ => 64,
        }
    }

    fn cit(&self) -> String {
        let name = match (self.sgn, self.w) {
            (false, "w8") => "u8",
            (false, "w16") => "u16",
            (false, "w32") => "u32",
            (false, _) => "u64",
            (true, "w8") => "i8",
            (true, "w16") => "i16",
            (true, "w32") => "i32",
            (true, _) => "i64",
        };
        format!("CIT.{name}")
    }

    fn cty(&self) -> String {
        format!(".int {} .{}", self.sgn, self.w)
    }

    /// C11 6.3.1.1p2: narrower than `int` becomes `int`.
    fn promote(&self) -> IntW {
        if self.bits() < 32 {
            IntW { sgn: true, w: "w32" }
        } else {
            *self
        }
    }

    /// The usual arithmetic conversions (C11 6.3.1.8) on two widths.
    fn uac(a: IntW, b: IntW) -> IntW {
        let (pa, pb) = (a.promote(), b.promote());
        if pa.sgn == pb.sgn {
            if pa.bits() <= pb.bits() { pb } else { pa }
        } else {
            let (u, s) = if pa.sgn { (pb, pa) } else { (pa, pb) };
            if s.bits() <= u.bits() { u } else { s }
        }
    }
}

/// The local scope: parameters in C-local order, known integer widths,
/// table-pointer parameters, `let` locals with their C locals, and the
/// next free C local.
#[derive(Debug, Clone)]
struct GScope {
    params: Vec<String>,
    widths: Vec<(String, IntW)>,
    ptrs: Vec<(String, String)>,
    locals: Vec<(String, u32)>,
    next: u32,
}

impl GScope {
    fn local(&self, name: &str) -> Option<u32> {
        for (n, l) in self.locals.iter().rev() {
            if n == name {
                return Some(*l);
            }
        }
        self.params.iter().position(|p| p == name).map(|i| i as u32)
    }

    fn width(&self, name: &str) -> Option<IntW> {
        for (n, w) in self.widths.iter().rev() {
            if n == name {
                return Some(*w);
            }
        }
        None
    }

    fn ptable(&self, name: &str) -> Option<&str> {
        self.ptrs.iter().find(|(n, _)| n == name).map(|(_, t)| t.as_str())
    }
}

/// The storage word of an integer type expression, if it is one.
fn intw_of_wort(wort: &gabbro_syntax::kw::Kw) -> Option<IntW> {
    use gabbro_syntax::kw::Kw;
    let w = match wort {
        Kw::U8 | Kw::I8 => "w8",
        Kw::U16 | Kw::I16 => "w16",
        Kw::U32 | Kw::I32 => "w32",
        Kw::U64 | Kw::I64 => "w64",
        _ => return None,
    };
    let sgn = matches!(wort, Kw::I8 | Kw::I16 | Kw::I32 | Kw::I64);
    Some(IntW { sgn, w })
}

/// The integer width of a type expression: integers by word, `bool` by
/// storage, aliases by resolution. Anything else has no width here.
fn width_of_typ(um: &Umgebung, t: &TypExpr) -> Option<IntW> {
    match t {
        TypExpr::Int(i) => intw_of_wort(&i.wort),
        TypExpr::Bool(_) => Some(IntW { sgn: false, w: "w8" }),
        TypExpr::Pfad(p) => {
            let name = p.einfach()?.text.clone();
            for td in um.typen.iter() {
                if td.name.text == name {
                    return width_of_typ(um, td.rumpf.as_ref()?);
                }
            }
            None
        }
        _ => None,
    }
}

/// The integer width of a slot field type.
fn field_intw(um: &Umgebung, tabelle: &str, feld: &str) -> Option<IntW> {
    let t = um.tabellen.iter().find(|t| t.name.text == tabelle)?;
    let slot = t.slot.as_ref()?;
    let f = slot.felder.iter().find(|f| f.name.text == feld)?;
    match &f.typ {
        SlotTyp::Typ(te) => width_of_typ(um, te),
        SlotTyp::Wrapping(_) => None,
    }
}

/// The integer width of an expression, if it is one. Literals adapt to
/// their context (`None`); a bare local comes from the scope.
fn width_of_expr(sc: &GScope, um: &Umgebung, e: &Expr) -> Option<IntW> {
    match &e.art {
        ExprArt::Zahl(_) | ExprArt::Gleitkomma { .. } => None,
        ExprArt::Wahr | ExprArt::Falsch => Some(IntW { sgn: false, w: "w8" }),
        ExprArt::Ort(o) if o.suffixe.is_empty() => sc.width(&o.basis.text),
        ExprArt::Ort(o) => match gslot(o, sc) {
            Some((_, tab, _, feld)) => field_intw(um, &tab, &feld),
            None => None,
        },
        ExprArt::Binaer(op, a, b) => {
            use BinOp::*;
            match op {
                Plus | Minus | Mal => match (width_of_expr(sc, um, a), width_of_expr(sc, um, b)) {
                    (Some(x), Some(y)) => Some(IntW::uac(x, y)),
                    (Some(x), None) | (None, Some(x)) => Some(IntW::uac(x, x.promote())),
                    (None, None) => None,
                },
                Gleich | Ungleich | Kleiner | KleinerGleich | Groesser | GroesserGleich => {
                    Some(IntW { sgn: false, w: "w8" })
                }
                _ => None,
            }
        }
        ExprArt::Unaer(UnOp::Nicht, _) => Some(IntW { sgn: false, w: "w8" }),
        ExprArt::Klammer(e) => width_of_expr(sc, um, e),
        _ => None,
    }
}

/// The computation type of two operand widths: both known (usual
/// conversions), one known (a literal adapts), else a refusal.
fn cit_of_w(a: Option<IntW>, b: Option<IntW>) -> Result<String, String> {
    match (a, b) {
        (Some(x), Some(y)) => Ok(IntW::uac(x, y).cit()),
        (Some(x), None) | (None, Some(x)) => Ok(IntW::uac(x, x.promote()).cit()),
        (None, None) => Err("untyped operands: no computation type".to_string()),
    }
}

/// The computation type of `a op b`.
fn cit_of(sc: &GScope, um: &Umgebung, a: &Expr, b: &Expr) -> Result<String, String> {
    cit_of_w(width_of_expr(sc, um, a), width_of_expr(sc, um, b))
}

/// `k.slots[i].f` with `k` a table-pointer parameter: base local,
/// table, index expression, field name.
fn gslot<'o>(ort: &'o Ort, sc: &GScope) -> Option<(u32, String, &'o Expr, String)> {
    let kp = sc.params.iter().position(|p| p == &ort.basis.text)? as u32;
    let tab = sc.ptable(&ort.basis.text)?.to_string();
    if let [OrtSuffix::Feld(_), OrtSuffix::Index(idx), OrtSuffix::Feld(feld)] = &ort.suffixe[..] {
        return Some((kp, tab, idx, feld.text.clone()));
    }
    None
}

/// Mark a C local as used (for the emitter's `(void)` rows).
fn merke(benutzt: &mut [bool], l: u32) {
    if let Some(b) = benutzt.get_mut(l as usize) {
        *b = true;
    }
}

/// Render an expression as `CX`, in exactly the Lean `exprOk` families.
/// Returns the `CX` term or the refusal naming the form.
fn gcx(sc: &GScope, um: &Umgebung, e: &Expr, benutzt: &mut [bool]) -> Result<String, String> {
    match &e.art {
        ExprArt::Zahl(v) => Ok(format!(".lit {v}")),
        ExprArt::Wahr => Ok(".lit 1".to_string()),
        ExprArt::Falsch => Ok(".lit 0".to_string()),
        ExprArt::Klammer(inner) => gcx(sc, um, inner, &mut *benutzt),
        ExprArt::Ort(o) if o.suffixe.is_empty() => match sc.local(&o.basis.text) {
            Some(n) => {
                merke(&mut *benutzt, n);
                Ok(format!(".var {n}"))
            }
            None => Err(format!(
                "place `{}` is no parameter or local: globals and named tables have no block number",
                o.text()
            )),
        },
        ExprArt::Ort(o) => match gslot(o, sc) {
            Some((kp, tab, idx, feld)) => {
                let index = gcx(sc, um, idx, &mut *benutzt)?;
                match um.layout(&tab, &feld) {
                    Some(l) => match field_intw(um, &tab, &feld) {
                        Some(w) => {
                            merke(benutzt, kp);
                            Ok(format!(
                                ".ld (.slotA (.var {kp}) ({index}) {} {} {}) ({})",
                                l.n,
                                l.ss,
                                l.off,
                                w.cty()
                            ))
                        }
                        None => Err(format!("slot load `{}`: field `{tab}.{feld}` has no integer width", o.text())),
                    },
                    None => Err(format!("slot load `{}`: layout has no byte size", o.text())),
                }
            }
            None => Err(format!(
                "place `{}`: only bare locals and `param.slots[i].field` loads have rows",
                o.text()
            )),
        },
        ExprArt::Binaer(op, a, b) => {
            use BinOp::*;
            let (cop, cmp) = match op {
                Plus => (".add", false),
                Minus => (".sub", false),
                Mal => (".mul", false),
                Gleich => (".eq", true),
                Kleiner => (".lt", true),
                KleinerGleich => (".le", true),
                Groesser => (".gt", true),
                _ => {
                    return Err(format!(
                        "binary {op:?}: only +, -, * and ==, <, <=, > have rows"
                    ))
                }
            };
            let t = cit_of(sc, um, a, b)?;
            let (ca, cb) = (gcx(sc, um, a, &mut *benutzt)?, gcx(sc, um, b, &mut *benutzt)?);
            if cmp {
                Ok(format!(".cmp {cop} {t} ({ca}) ({cb})"))
            } else {
                Ok(format!(".bin {cop} {t} ({ca}) ({cb})"))
            }
        }
        _ => Err(format!("{}: no expression row (the Lean family is lit/var/+,-,*/cmp/slot)", expr_name(e))),
    }
}

/// One certified body in general syntax: rows plus map for `GBody`.
#[derive(Debug, Clone)]
pub struct GBodyCert {
    /// The Gabbro function name.
    pub name: String,
    /// The `GRow` terms in emission order (`(void)` rows first).
    pub rows: Vec<String>,
    /// Value-param C locals (`vm`).
    pub vm: Vec<String>,
    /// Pointer-param C locals (`pp`, raw numbers).
    pub pp: Vec<String>,
    /// Fixed index params (`ks`, values are model data).
    pub ks: Vec<String>,
    /// Layout facts used by a slot row, if any.
    pub lay: Option<LayFacts>,
}

/// The whole unit in general syntax: certified bodies plus refusals.
#[derive(Debug, Clone, Default)]
pub struct GUnitCert {
    pub bodies: Vec<GBodyCert>,
    pub refusals: Vec<Refusal>,
}

impl GUnitCert {
    fn refuse(&mut self, wo: &str, was: String) {
        self.refusals.push(Refusal {
            wo: wo.to_string(),
            was,
        });
    }
}

/// Render one block as general rows, or the first refusal. `out_unused`
/// collects `(void)` rows for unused parameters at the top level only.
fn gblock(
    sc: &mut GScope,
    um: &Umgebung,
    impls: &[String],
    f: &FnDecl,
    block: &Block,
    wo: &str,
    cert: &mut GUnitCert,
    rows: &mut Vec<String>,
    lay: &mut Option<LayFacts>,
    ende_ok: &mut bool,
    benutzt: &mut [bool],
) -> bool {
    for st in &block.anweisungen {
        match &st.art {
            StmtArt::Let(s) => {
                if matches!(s.wert.art, ExprArt::Ruf(_)) {
                    cert.refuse(wo, format!("`let {} =` call: result type needs the callee signature", s.name.text));
                    return false;
                }
                let ce = match gcx(sc, um, &s.wert, &mut *benutzt) {
                    Ok(c) => c,
                    Err(was) => {
                        cert.refuse(wo, format!("`let {}` of {was}", s.name.text));
                        return false;
                    }
                };
                let tc = match s.typ.as_ref().and_then(|t| width_of_typ(um, t)) {
                    Some(w) => w.cty(),
                    None => {
                        cert.refuse(wo, format!("`let {}` without a type annotation: no C type", s.name.text));
                        return false;
                    }
                };
                let x = sc.next;
                sc.next += 1;
                sc.locals.push((s.name.text.clone(), x));
                if let Some(t) = s.typ.as_ref().and_then(|t| width_of_typ(um, t)) {
                    sc.widths.push((s.name.text.clone(), t));
                }
                rows.push(format!("GRow.bindLet {x} ({tc}) ({ce})"));
            }
            StmtArt::Zuweisung(z) => {
                if z.op != ZuwOp::Setzt {
                    let target = z.ziel.text();
                    if !z.ziel.suffixe.is_empty() {
                        cert.refuse(wo, format!("`{target} {op:?}=`: no compound row outside locals (no T4 lemma for slot op)", op = z.op));
                        return false;
                    }
                    let Some(x) = sc.local(&z.ziel.basis.text) else {
                        cert.refuse(wo, format!("`{target} {op:?}=`: no compound row outside locals (no T4 lemma for slot op)", op = z.op));
                        return false;
                    };
                    let ce = match gcx(sc, um, &z.wert, &mut *benutzt) {
                        Ok(c) => c,
                        Err(was) => {
                            cert.refuse(wo, format!("`{target} {op:?}=` of {was}", op = z.op));
                            return false;
                        }
                    };
                    let wx = match sc.width(&z.ziel.basis.text) {
                        Some(w) => w,
                        None => {
                            cert.refuse(wo, format!("`{target} {op:?}=`: no integer width", op = z.op));
                            return false;
                        }
                    };
                    let wt = match cit_of_w(Some(wx), width_of_expr(sc, um, &z.wert)) {
                        Ok(t) => t,
                        Err(was) => {
                            cert.refuse(wo, format!("`{target} {op:?}=`: {was}", op = z.op));
                            return false;
                        }
                    };
                    let cop = match z.op {
                        ZuwOp::Plus => ".add",
                        ZuwOp::Minus => ".sub",
                        ZuwOp::Und => ".band",
                        ZuwOp::Oder => ".bor",
                        ZuwOp::Setzt => ".add",
                    };
                    merke(&mut *benutzt, x);
                    rows.push(format!("GRow.setOp {x} ({}) {cop} {wt} ({ce})", wx.cty()));
                    continue;
                }
                let target = z.ziel.text();
                if let Some((kp, tab, idx, feld)) = gslot(&z.ziel, sc) {
                    let index = match gcx(sc, um, idx, &mut *benutzt) {
                        Ok(c) => c,
                        Err(was) => {
                            cert.refuse(wo, format!("slot store to `{target}`: index {was}"));
                            return false;
                        }
                    };
                    let val = match gcx(sc, um, &z.wert, &mut *benutzt) {
                        Ok(c) => c,
                        Err(was) => {
                            cert.refuse(wo, format!("slot store to `{target}` of {was}"));
                            return false;
                        }
                    };
                    match um.layout(&tab, &feld) {
                        Some(l) => {
                            let tc = match field_intw(um, &tab, &feld) {
                                Some(w) => w.cty(),
                                None => {
                                    cert.refuse(wo, format!("slot store to `{tab}.{feld}`: no integer width"));
                                    return false;
                                }
                            };
                            merke(&mut *benutzt, kp);
                            rows.push(format!(
                                "GRow.storeSlot {kp} ({index}) {} {} {} ({tc}) ({val})",
                                l.n, l.ss, l.off
                            ));
                            *lay = Some(l);
                        }
                        None => {
                            cert.refuse(wo, format!("slot store to `{tab}.{feld}`: layout has no byte size"));
                            return false;
                        }
                    }
                } else if z.ziel.suffixe.is_empty() {
                    match sc.local(&z.ziel.basis.text) {
                        Some(x) => {
                            let ce = match gcx(sc, um, &z.wert, &mut *benutzt) {
                                Ok(c) => c,
                                Err(was) => {
                                    cert.refuse(wo, format!("assignment to `{target}` of {was}"));
                                    return false;
                                }
                            };
                            let tc = match sc.width(&z.ziel.basis.text) {
                                Some(w) => w.cty(),
                                None => {
                                    cert.refuse(wo, format!("assignment to `{target}`: no integer width"));
                                    return false;
                                }
                            };
                            merke(&mut *benutzt, x);
                            rows.push(format!("GRow.setVar {x} ({tc}) ({ce})"));
                        }
                        None => {
                            cert.refuse(wo, format!("assignment to `{target}`: globals and named tables have no block number"));
                            return false;
                        }
                    }
                } else {
                    cert.refuse(wo, format!("assignment to `{target}`: globals and named tables have no block number"));
                    return false;
                }
            }
            StmtArt::Wenn(w) => {
                match gite(sc, um, impls, f, w, wo, cert, lay, &mut *benutzt) {
                    Some(row) => rows.push(row),
                    None => return false,
                }
            }
            StmtArt::Ruf(r) => {
                let ziel = r.ziel.text();
                let Some(fc) = impls.iter().position(|n| *n == ziel) else {
                    cert.refuse(wo, format!("call to `{ziel}`: only unit functions have a callee relation"));
                    return false;
                };
                let mut args = Vec::new();
                for a in &r.argumente {
                    match gcx(sc, um, a, &mut *benutzt) {
                        Ok(c) => args.push(c),
                        Err(was) => {
                            cert.refuse(wo, format!("call to `{ziel}`: argument {was}"));
                            return false;
                        }
                    }
                }
                rows.push(format!("GRow.call {fc} [{}] none", args.join(", ")));
            }
            StmtArt::Return(opt) => match opt {
                None => {
                    if f.ergebnis.is_some() {
                        cert.refuse(wo, "`return;` with a declared result: no row".to_string());
                        return false;
                    }
                    *ende_ok = true;
                }
                Some(e) => {
                    let ce = match gcx(sc, um, e, &mut *benutzt) {
                        Ok(c) => c,
                        Err(was) => {
                            cert.refuse(wo, format!("return of {was}"));
                            return false;
                        }
                    };
                    let tc = match f.ergebnis.as_ref().and_then(|t| width_of_typ(um, t)) {
                        Some(w) => w.cty(),
                        None => {
                            cert.refuse(wo, "return of an untyped result: no C type".to_string());
                            return false;
                        }
                    };
                    rows.push(format!("GRow.ret (some (({tc}), ({ce})))"));
                    *ende_ok = true;
                }
            },
            _ => {
                cert.refuse(
                    wo,
                    format!("statement `{}`: no general row (void/store/set/let/if/call/return only)", stmt_name(&st.art)),
                );
                return false;
            }
        }
    }
    true
}

/// Render the whole general certificate: per-body fragments, then -- for
/// bodies without a refusal -- the pasteable `GBody` literal for
/// `Korrespondenz.lean`.
pub fn gzeige(baum: &Programm, datei: &str) -> String {
    let cert = gzertifiziere(baum);
    let mut aus = format!("-- general corr-lean certificate for `{datei}`: GRow form families.\n");
    for b in &cert.bodies {
        aus.push_str(&format!("-- function `{}`:\n", b.name));
        aus.push_str(&format!("--   rows := [{}]\n", b.rows.join(", ")));
        aus.push_str(&format!("--   vm := [{}]\n", b.vm.join(", ")));
        aus.push_str(&format!("--   pp := [{}]\n", b.pp.join(", ")));
        aus.push_str(&format!("--   ks := [{}] -- ks values: MODEL DATUM, fixed by the model\n", b.ks.join(", ")));
        match &b.lay {
            Some(l) => aus.push_str(&format!(
                "--   slot layout: table `{}` count {} field `{}` {} at offset {}, record {} bytes\n",
                l.table, l.count_src, l.field, l.field_ty, l.off, l.ss
            )),
            None => aus.push_str("--   slot layout: none (no slot access)\n"),
        }
        let hat_absage = cert.refusals.iter().any(|r| r.wo == format!("function `{}`", b.name));
        if !hat_absage {
            aus.push_str(&format!(
                "-- pasteable as GBody:\n{{ rows := [{}],\n  vm := [{}], pp := [{}], ks := [{}] }}\n",
                b.rows.join(", "),
                b.vm.join(", "),
                b.pp.join(", "),
                b.ks.join(", ")
            ));
        }
    }
    for r in &cert.refusals {
        aus.push_str(&format!("-- GREFUSAL: {}: {}\n", r.wo, r.was));
    }
    aus
}
