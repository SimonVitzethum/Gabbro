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

    /// Byte size of a slot field type: integers by word, aliases by resolution.
    fn feld_bytes(&self, t: &TypExpr, tiefe: u32) -> Option<u32> {
        if tiefe > 8 {
            return None;
        }
        match t {
            TypExpr::Int(i) => wort_bytes(&i.wort),
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
                let mut ss = off;
                for g in &slot.felder {
                    ss += match &g.typ {
                        SlotTyp::Typ(te) => self.feld_bytes(te, 0)?,
                        SlotTyp::Wrapping(i) => wort_bytes(&i.wort)?,
                    };
                }
                let field_ty = match &f.typ {
                    SlotTyp::Typ(TypExpr::Int(i)) => format!("{i:?}"),
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
/// the assembled `Cert104` literal for `Korrespondenz104.lean`.
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
}
