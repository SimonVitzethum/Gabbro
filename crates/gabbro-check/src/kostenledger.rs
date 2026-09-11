//! **The cost/deadline ledger -- a checkable sidecar beside the C, not inside it.**
//!
//! The checker PROMISES numbers (`costs`, `per_pass`, `bounded`, `deadline`) and the
//! emitter LOWERS primitives to C. Both facts leave the pipeline as prose today: the C
//! carries no record of which bound covered which function, and a recomputer that wants
//! to re-check the artefact has to re-derive the mapping from the sources. *A number
//! that only lives in the checking run is a number the artefact cannot defend.*
//!
//! This module is the RECORDING side of that gap. It owns a deterministic text format
//! (`render` / `parse`), a field-by-field comparison (`verify`) that the recomputer
//! consumes, and the per-unit row shape: ops counts (`costs` / `per_pass` / `bounded`
//! inputs), deadline clauses with falsifier names, and `absenkung` statement counts per
//! primitive. **It decides nothing**: every number arrives as a plain value from the
//! caller, and the passes in `kosten.rs` stay the only place that REFUSES.
//!
//! ## The ONE hook point (NOT wired here -- this file is standalone on purpose)
//!
//! The ledger is emitted beside the C, never inside it: generated C stays byte-identical.
//! The single call site is the end of `emit::emittiere_mit` in `emit.rs`, after the C
//! string is final:
//!
//! ```text
//!     aus.push_str(&rumpf);
//!     // HOOK (one line, no C touched):
//!     crate::kostenledger::ablegen(baum, &aus, zielpfad);
//!     aus
//! ```
//!
//! `ablegen` (specified in `messung/KOSTEN-LEDGER.md`, implemented at wiring time)
//! walks the tree with `crate::fuer_jedes_item_im_modul`, reads the already-computed
//! numbers (`Umgebung::konst_wert` for each bound, `kosten::durchgangskosten` for each
//! `retry` body, the statement counters below for each body), renders the [`Ledger`]
//! and writes it to [`sidecar_path`] -- `<stem>.kostenledger` next to the `.c` file.
//! The C string `aus` is only borrowed, never touched: *a sidecar that rewrites the
//! artefact is a second emitter wearing a ledger's clothes.*
//!
//! ## Caller-side extraction (three lines, at the hook -- not here)
//!
//! This module depends on nothing but `std`, so a single `rustc --test` checks it
//! without the crate graph. The two AST-shaped values therefore arrive pre-read:
//!
//! * falsifier name and class from `AnnahmeKlasse`: `Falsifizierbar(p)` gives
//!   `(p.text, true)`, `NichtFalsifizierbar(_)` gives `("(unfalsifiable)", false)`.
//! * bound inputs (the names a `per_pass` / `bounded` expression reads) from the
//!   expression walker the hook already owns.
//!
//! ## Format stability
//!
//! `render` is deterministic: rows in ledger order, keys in fixed order, integers in
//! decimal. `parse(render(x)) == x` and `render(parse(s)) == s` on well-formed input;
//! both directions are tested below. The recomputer compares with [`Ledger::verify`],
//! which reports every divergence as a line instead of stopping at the first -- *a
//! measurement that stops at the first hit answers "at least one", and the question
//! asked was "which ones"*.

use std::collections::BTreeMap;

/// Format version. Bumped only when `parse` stops reading an older rendering.
pub const VERSION: u32 = 1;

/// One bound the checker holds against a body: `costs`, one `per_pass`, one `bounded`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BoundClause {
    /// The bound as written (`64 + 12 * lenof(msg)`), escaped on render.
    pub source: String,
    /// Its constant value, if the checker could read one (`None` = symbolic/open).
    pub const_value: Option<i128>,
    /// The input names the expression reads (`lenof(msg)` reads `msg`).
    pub inputs: Vec<String>,
}

/// A `deadline <= N ops arch X falsifier p` clause, as recorded.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeadlineEntry {
    /// The date as written.
    pub cycles_source: String,
    /// Its constant value, if readable (`None` = unprobable shape, see `K011`).
    pub cycles: Option<i128>,
    /// The machine the date is promised on.
    pub arch: String,
    /// The probe that discharges it (or `"(unfalsifiable)"`).
    pub falsifier: String,
    /// Whether the probe can go red.
    pub falsifiable: bool,
}

/// How many statements of each primitive lower into this function -- the `absenkung`
/// census the lowering apex (`messung/ABSENKUNG-MESSUNG.md`) needs per unit.
///
/// The fields are the Gabbro primitives of `SPRACHE.md` §7 plus the lowering forms
/// `emit.rs` distinguishes. A new primitive is a new field, never a wider bucket:
/// *a bucket that grows silently is the `_` arm of a census.*
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct AbsenkungCounts {
    /// `let` / assignment / `publish` -- one store each.
    pub assign: u64,
    /// Arithmetic / comparison / alignment test -- one op each.
    pub arith: u64,
    /// Loads (`Ort` reads, `await` takes).
    pub load: u64,
    /// Calls, including indirect ones and conversions.
    pub call: u64,
    /// `if` / `match` / `narrow` -- the branch itself, not its arms.
    pub branch: u64,
    /// `traverse` loops (domain-finite by construction).
    pub traverse: u64,
    /// `retry` loops (world-dependent, hence `bounded`).
    pub retry: u64,
    /// `forever` loops (no total cost, hence `per_pass`).
    pub forever: u64,
    /// `locks` blocks.
    pub locks: u64,
    /// `observes` regions.
    pub observes: u64,
    /// `exchange` statements (both forms).
    pub exchange: u64,
    /// `count` predicates over a domain.
    pub count: u64,
}

impl AbsenkungCounts {
    /// The census total -- informational only, never a bound.
    pub fn total(&self) -> u64 {
        self.assign
            + self.arith
            + self.load
            + self.call
            + self.branch
            + self.traverse
            + self.retry
            + self.forever
            + self.locks
            + self.observes
            + self.exchange
            + self.count
    }

    /// Fixed field order for render/parse. One entry per field, in this order.
    fn fields(&self) -> [(&'static str, u64); 12] {
        [
            ("assign", self.assign),
            ("arith", self.arith),
            ("load", self.load),
            ("call", self.call),
            ("branch", self.branch),
            ("traverse", self.traverse),
            ("retry", self.retry),
            ("forever", self.forever),
            ("locks", self.locks),
            ("observes", self.observes),
            ("exchange", self.exchange),
            ("count", self.count),
        ]
    }

    fn set(&mut self, key: &str, value: u64) -> Result<(), String> {
        match key {
            "assign" => self.assign = value,
            "arith" => self.arith = value,
            "load" => self.load = value,
            "call" => self.call = value,
            "branch" => self.branch = value,
            "traverse" => self.traverse = value,
            "retry" => self.retry = value,
            "forever" => self.forever = value,
            "locks" => self.locks = value,
            "observes" => self.observes = value,
            "exchange" => self.exchange = value,
            "count" => self.count = value,
            other => return Err(format!("unknown absenkung primitive `{other}`")),
        }
        Ok(())
    }
}

/// One function of the unit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnitRow {
    /// Qualified name (`modul::funktion`), as the hook walks it.
    pub function: String,
    /// The `costs` promise, if the function carries one.
    pub costs: Option<BoundClause>,
    /// One entry per `forever` in the body, in source order.
    pub per_pass: Vec<BoundClause>,
    /// One entry per `retry` in the body, in source order.
    pub bounded: Vec<BoundClause>,
    /// The `deadline` clause, if the function carries one.
    pub deadline: Option<DeadlineEntry>,
    /// The computed body cost in ops, if the checker could compute one.
    pub body_ops: Option<i128>,
    /// The lowering census of the body.
    pub absenkung: AbsenkungCounts,
}

/// The ledger of one unit -- what the recomputer re-checks.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ledger {
    pub version: u32,
    /// The unit (file stem) the ledger was emitted beside.
    pub unit: String,
    pub rows: Vec<UnitRow>,
}

impl Ledger {
    /// Compare two ledgers field by field and report EVERY divergence.
    ///
    /// Empty output means the recomputed ledger matches the recorded one. The
    /// comparison is order-insensitive over functions (a walk order is not a
    /// promise) and order-sensitive within a row (`per_pass`/`bounded` follow
    /// source order, which IS a promise).
    pub fn verify(&self, actual: &Ledger) -> Vec<String> {
        let mut out = Vec::new();
        if self.version != actual.version {
            out.push(format!(
                "version: recorded v{}, recomputed v{}",
                self.version, actual.version
            ));
        }
        if self.unit != actual.unit {
            out.push(format!(
                "unit: recorded `{}`, recomputed `{}`",
                self.unit, actual.unit
            ));
        }
        let mut have: BTreeMap<&str, &UnitRow> = BTreeMap::new();
        for r in &actual.rows {
            have.insert(r.function.as_str(), r);
        }
        for want in &self.rows {
            match have.get(want.function.as_str()) {
                None => out.push(format!("function `{}`: missing in recomputed ledger", want.function)),
                Some(got) => {
                    if want.costs != got.costs {
                        out.push(format!(
                            "function `{}`: costs recorded {:?}, recomputed {:?}",
                            want.function, want.costs, got.costs
                        ));
                    }
                    if want.per_pass != got.per_pass {
                        out.push(format!(
                            "function `{}`: per_pass recorded {:?}, recomputed {:?}",
                            want.function, want.per_pass, got.per_pass
                        ));
                    }
                    if want.bounded != got.bounded {
                        out.push(format!(
                            "function `{}`: bounded recorded {:?}, recomputed {:?}",
                            want.function, want.bounded, got.bounded
                        ));
                    }
                    if want.deadline != got.deadline {
                        out.push(format!(
                            "function `{}`: deadline recorded {:?}, recomputed {:?}",
                            want.function, want.deadline, got.deadline
                        ));
                    }
                    if want.body_ops != got.body_ops {
                        out.push(format!(
                            "function `{}`: body_ops recorded {:?}, recomputed {:?}",
                            want.function, want.body_ops, got.body_ops
                        ));
                    }
                    if want.absenkung != got.absenkung {
                        out.push(format!(
                            "function `{}`: absenkung recorded {:?}, recomputed {:?}",
                            want.function, want.absenkung, got.absenkung
                        ));
                    }
                }
            }
        }
        for got in &actual.rows {
            if !self.rows.iter().any(|r| r.function == got.function) {
                out.push(format!(
                    "function `{}`: new in recomputed ledger, not recorded",
                    got.function
                ));
            }
        }
        out
    }
}

/// The sidecar path for a C output path: beside the C, stem kept, suffix swapped.
///
/// `out/foo.c` -> `out/foo.kostenledger`. No directories are created here; the
/// caller owns the output directory exactly like it owns the C file's.
pub fn sidecar_path(c_path: &str) -> String {
    match c_path.rsplit_once('.') {
        Some((stem, _)) if !stem.is_empty() => format!("{stem}.kostenledger"),
        _ => format!("{c_path}.kostenledger"),
    }
}

// --- escaping: `\` and newline in free text; `|` is the field separator ---------

fn escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '|' => out.push_str("\\p"),
            _ => out.push(c),
        }
    }
    out
}

fn unescape(s: &str) -> Result<String, String> {
    let mut out = String::with_capacity(s.len());
    let mut it = s.chars();
    while let Some(c) = it.next() {
        if c == '\\' {
            match it.next() {
                Some('\\') => out.push('\\'),
                Some('n') => out.push('\n'),
                Some('p') => out.push('|'),
                Some(x) => return Err(format!("bad escape `\\{x}` in `{s}`")),
                None => return Err(format!("trailing backslash in `{s}`")),
            }
        } else {
            out.push(c);
        }
    }
    Ok(out)
}

/// Split on unescaped `|`, keeping the escapes for `unescape`.
fn split_fields(s: &str) -> Vec<String> {
    let mut fields = Vec::new();
    let mut cur = String::new();
    let mut it = s.chars().peekable();
    while let Some(c) = it.next() {
        if c == '\\' {
            cur.push(c);
            if let Some(n) = it.next() {
                cur.push(n);
            }
        } else if c == '|' {
            fields.push(std::mem::take(&mut cur));
        } else {
            cur.push(c);
        }
    }
    fields.push(cur);
    fields
}

fn opt_num(s: &str) -> Result<Option<i128>, String> {
    if s == "?" {
        return Ok(None);
    }
    s.parse::<i128>()
        .map(Some)
        .map_err(|_| format!("not a number or `?`: `{s}`"))
}

fn fmt_opt(n: Option<i128>) -> String {
    n.map(|v| v.to_string()).unwrap_or_else(|| "?".to_string())
}

fn render_bound(b: &BoundClause) -> String {
    format!(
        "{}|{}|{}",
        escape(&b.source),
        fmt_opt(b.const_value),
        if b.inputs.is_empty() {
            "-".to_string()
        } else {
            b.inputs.join(",")
        }
    )
}

fn parse_bound(s: &str) -> Result<BoundClause, String> {
    let f = split_fields(s);
    if f.len() != 3 {
        return Err(format!("bound needs 3 fields, got {}: `{s}`", f.len()));
    }
    let inputs = if f[2] == "-" {
        Vec::new()
    } else {
        f[2].split(',').map(|x| x.to_string()).collect()
    };
    Ok(BoundClause {
        source: unescape(&f[0])?,
        const_value: opt_num(&f[1])?,
        inputs,
    })
}

/// Render the ledger deterministically. Byte-stable: same ledger, same bytes.
pub fn render(ledger: &Ledger) -> String {
    let mut out = String::new();
    out.push_str(&format!("kosten-ledger v{}\n", ledger.version));
    out.push_str(&format!("unit {}\n", escape(&ledger.unit)));
    for r in &ledger.rows {
        out.push_str(&format!("function {}\n", escape(&r.function)));
        match &r.costs {
            Some(b) => out.push_str(&format!("costs {}\n", render_bound(b))),
            None => out.push_str("costs -\n"),
        }
        for b in &r.per_pass {
            out.push_str(&format!("per_pass {}\n", render_bound(b)));
        }
        for b in &r.bounded {
            out.push_str(&format!("bounded {}\n", render_bound(b)));
        }
        match &r.deadline {
            Some(d) => out.push_str(&format!(
                "deadline {}|{}|{}|{}|{}\n",
                escape(&d.cycles_source),
                fmt_opt(d.cycles),
                escape(&d.arch),
                escape(&d.falsifier),
                if d.falsifiable { "falsifiable" } else { "assumed" }
            )),
            None => out.push_str("deadline -\n"),
        }
        out.push_str(&format!("body_ops {}\n", fmt_opt(r.body_ops)));
        let fields: Vec<String> = r
            .absenkung
            .fields()
            .iter()
            .map(|(k, v)| format!("{k}={v}"))
            .collect();
        out.push_str(&format!("absenkung {}\n", fields.join(" ")));
    }
    out
}

/// Parse a rendered ledger. Rejects unknown keys and malformed rows loudly --
/// *a sidecar the recomputer cannot read is a sidecar that does not exist, and
/// saying so is the reader's whole job.*
pub fn parse(text: &str) -> Result<Ledger, String> {
    let mut lines = text.lines();
    let head = lines.next().ok_or("empty ledger")?;
    let version: u32 = head
        .strip_prefix("kosten-ledger v")
        .ok_or(format!("bad header: `{head}`"))?
        .parse()
        .map_err(|_| format!("bad version in header: `{head}`"))?;
    let unit_line = lines.next().ok_or("ledger has a header but no unit")?;
    let unit = unescape(
        unit_line
            .strip_prefix("unit ")
            .ok_or(format!("bad unit line: `{unit_line}`"))?,
    )?;
    let mut rows: Vec<UnitRow> = Vec::new();
    let mut cur: Option<UnitRow> = None;
    let mut seen_body = false;
    let finish = |cur: &mut Option<UnitRow>, rows: &mut Vec<UnitRow>, seen_body: bool| -> Result<(), String> {
        match cur.take() {
            Some(r) => {
                if !seen_body {
                    return Err(format!("function `{}` has no body_ops line", r.function));
                }
                rows.push(r);
                Ok(())
            }
            None => Ok(()),
        }
    };
    for line in lines {
        if line.is_empty() {
            return Err("blank lines are not part of the format".to_string());
        }
        let (key, rest) = line.split_once(' ').unwrap_or((line, ""));
        match key {
            "function" => {
                finish(&mut cur, &mut rows, seen_body)?;
                seen_body = false;
                cur = Some(UnitRow {
                    function: unescape(rest)?,
                    costs: None,
                    per_pass: Vec::new(),
                    bounded: Vec::new(),
                    deadline: None,
                    body_ops: None,
                    absenkung: AbsenkungCounts::default(),
                });
            }
            "costs" => {
                let r = cur.as_mut().ok_or("costs line before any function")?;
                if rest != "-" {
                    r.costs = Some(parse_bound(rest)?);
                }
            }
            "per_pass" => {
                let r = cur.as_mut().ok_or("per_pass line before any function")?;
                r.per_pass.push(parse_bound(rest)?);
            }
            "bounded" => {
                let r = cur.as_mut().ok_or("bounded line before any function")?;
                r.bounded.push(parse_bound(rest)?);
            }
            "deadline" => {
                let r = cur.as_mut().ok_or("deadline line before any function")?;
                if rest != "-" {
                    let f = split_fields(rest);
                    if f.len() != 5 {
                        return Err(format!("deadline needs 5 fields, got {}: `{rest}`", f.len()));
                    }
                    r.deadline = Some(DeadlineEntry {
                        cycles_source: unescape(&f[0])?,
                        cycles: opt_num(&f[1])?,
                        arch: unescape(&f[2])?,
                        falsifier: unescape(&f[3])?,
                        falsifiable: match f[4].as_str() {
                            "falsifiable" => true,
                            "assumed" => false,
                            other => return Err(format!("deadline class is falsifiable|assumed, got `{other}`")),
                        },
                    });
                }
            }
            "body_ops" => {
                let r = cur.as_mut().ok_or("body_ops line before any function")?;
                r.body_ops = opt_num(rest)?;
                seen_body = true;
            }
            "absenkung" => {
                let r = cur.as_mut().ok_or("absenkung line before any function")?;
                if rest.trim().is_empty() {
                    return Err("absenkung line carries no primitives".to_string());
                }
                for cell in rest.split(' ') {
                    let (k, v) = cell
                        .split_once('=')
                        .ok_or(format!("absenkung cell without `=`: `{cell}`"))?;
                    let n: u64 = v
                        .parse()
                        .map_err(|_| format!("absenkung count not a number: `{cell}`"))?;
                    r.absenkung.set(k, n)?;
                }
            }
            other => return Err(format!("unknown ledger key `{other}` in `{line}`")),
        }
    }
    finish(&mut cur, &mut rows, seen_body)?;
    Ok(Ledger { version, unit, rows })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample() -> Ledger {
        Ledger {
            version: VERSION,
            unit: "beispiel".to_string(),
            rows: vec![
                UnitRow {
                    function: "kern::handler".to_string(),
                    costs: Some(BoundClause {
                        source: "64 + 12 * lenof(msg)".to_string(),
                        const_value: None,
                        inputs: vec!["msg".to_string()],
                    }),
                    per_pass: vec![BoundClause {
                        source: "40".to_string(),
                        const_value: Some(40),
                        inputs: Vec::new(),
                    }],
                    bounded: vec![],
                    deadline: Some(DeadlineEntry {
                        cycles_source: "1000".to_string(),
                        cycles: Some(1000),
                        arch: "x86_64".to_string(),
                        falsifier: "sonde_frist".to_string(),
                        falsifiable: true,
                    }),
                    body_ops: Some(37),
                    absenkung: AbsenkungCounts {
                        assign: 9,
                        arith: 4,
                        load: 6,
                        call: 2,
                        branch: 1,
                        traverse: 1,
                        ..Default::default()
                    },
                },
                UnitRow {
                    function: "kern::wartet".to_string(),
                    costs: None,
                    per_pass: Vec::new(),
                    bounded: vec![BoundClause {
                        source: "NCORES * 8".to_string(),
                        const_value: Some(64),
                        inputs: Vec::new(),
                    }],
                    deadline: None,
                    body_ops: None,
                    absenkung: AbsenkungCounts {
                        retry: 1,
                        exchange: 1,
                        ..Default::default()
                    },
                },
            ],
        }
    }

    #[test]
    fn runde_weg_ist_identitaet() {
        let l = sample();
        let zurueck = parse(&render(&l)).expect("sample renders and parses");
        assert_eq!(l, zurueck);
    }

    #[test]
    fn render_ist_bytestabil() {
        let l = sample();
        assert_eq!(render(&l), render(&parse(&render(&l)).unwrap()));
    }

    #[test]
    fn verify_schweigt_bei_gleichheit_meldet_jede_abweichung() {
        let l = sample();
        assert!(l.verify(&l.clone()).is_empty());
        let mut drift = l.clone();
        drift.rows[0].body_ops = Some(38);
        drift.rows[1].deadline = Some(DeadlineEntry {
            cycles_source: "5".to_string(),
            cycles: Some(5),
            arch: "x86_64".to_string(),
            falsifier: "(unfalsifiable)".to_string(),
            falsifiable: false,
        });
        drift.rows.push(UnitRow {
            function: "kern::neu".to_string(),
            costs: None,
            per_pass: Vec::new(),
            bounded: Vec::new(),
            deadline: None,
            body_ops: None,
            absenkung: AbsenkungCounts::default(),
        });
        // Every divergence is named: body_ops drift, deadline drift, added row.
        // Missing rows are reported the other way round.
        let meldungen = l.verify(&drift);
        assert_eq!(meldungen.len(), 3, "{meldungen:?}");
        let weg = Ledger { rows: vec![l.rows[0].clone()], ..l.clone() };
        let meldungen = l.verify(&weg);
        assert_eq!(meldungen.len(), 1, "{meldungen:?}");
        assert!(meldungen[0].contains("kern::wartet"));
    }

    #[test]
    fn verify_ist_reihenfolge_unabhaengig_ueber_funktionen() {
        let mut umgekehrt = sample();
        umgekehrt.rows.reverse();
        assert!(sample().verify(&umgekehrt).is_empty());
    }

    #[test]
    fn sonderzeichen_ueberleben_die_runde() {
        let mut l = sample();
        l.rows[0].costs.as_mut().unwrap().source = "a == b | c\\d".to_string();
        l.rows[0].deadline.as_mut().unwrap().falsifier = "sonde|x".to_string();
        let zurueck = parse(&render(&l)).expect("escapes round-trip");
        assert_eq!(l, zurueck);
    }

    #[test]
    fn leser_lehnt_laut_ab_statt_zu_raten() {
        assert!(parse("").is_err());
        assert!(parse("kosten-ledger v1\n").is_err());
        assert!(parse("kosten-ledger v1\nunit u\ncosts -\n").is_err());
        assert!(parse("kosten-ledger v1\nunit u\nfunction f\nkosten -\n").is_err());
        assert!(parse("kosten-ledger v1\nunit u\nfunction f\ncosts -\ndeadline -\nabsenkung assign=x\nbody_ops ?\n").is_err());
        // A row without body_ops is incomplete, not empty.
        assert!(parse("kosten-ledger v1\nunit u\nfunction f\ncosts -\ndeadline -\nabsenkung assign=1\n").is_err());
    }

    #[test]
    fn seitenwagen_liegt_neben_dem_c() {
        assert_eq!(sidecar_path("out/foo.c"), "out/foo.kostenledger");
        assert_eq!(sidecar_path("foo.c"), "foo.kostenledger");
        assert_eq!(sidecar_path("foo"), "foo.kostenledger");
    }

    #[test]
    fn absenkung_summe_zaehlt_alle_primitive() {
        let mut a = AbsenkungCounts::default();
        assert_eq!(a.total(), 0);
        a.assign = 2;
        a.call = 3;
        a.forever = 1;
        assert_eq!(a.total(), 6);
    }
}
