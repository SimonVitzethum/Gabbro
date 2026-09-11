//! Zeugnis-style derivation certificates for the int fragment -- the emitter half.
//!
//! This module prints derivation certificates per checked expression: a `CertExpr`
//! term plus the claimed range plus the side conditions, mirroring the shapes of
//! `CertExpr` and `certRange` in `grammatik/Grammatik/Zeugnis.lean` (read-only
//! reference; the Lean side is never edited from here).
//!
//! ## What the emitter covers
//!
//! The int fragment: `lit`, `add`, `div`, the bitwise family (`band`, `bor`,
//! `bxor`, `shl`, `shr`) with the `wide` narrowing the slot index needs, and the
//! three read forms (`var` against a de Bruijn context, `glob` against a global
//! carrier type plus its guard, `slot` against a table field plus the index shape
//! `0 .. count - 1` plus its guard).
//!
//! Every range below is recomputed from the same arms as `certRange`: `none`
//! means the print has no range at all, and a forged side condition lands there,
//! not in a diagnostic. The `claimed` field of a [`Certificate`] is exactly what
//! the table recomputes -- or `None`, printed as such.
//!
//! ## What the emitter does NOT do (booked, not forgotten)
//!
//! Validation stays future work: re-reading a printed certificate and running
//! `decide`-style acceptance over it (`GueltigAbleitung` on the Lean side) is a
//! second half with its own module, its own probes, and its own booking. This
//! file owns the print direction only -- valid-print-implies-judgment is proved
//! over in `Zeugnis.lean` (`zeugnis_sound`), and printer-prints-what-was-checked
//! is trust base there, exactly as booked.
//!
//! ## Arithmetic note
//!
//! Lean `Int` never overflows; Rust `i128` does. The range table below uses
//! checked arithmetic and answers `None` on overflow instead of wrapping: an
//! overflowed bound is no bound, and a certificate without a range is rejected
//! downstream -- loudly, by construction.
//!
//! Standalone on purpose: only `std`, no crate imports, so the file compiles on
//! its own (`rustc --test crates/gabbro-check/src/certemit.rs`). Registration in
//! the crate module tree belongs to the central integration, not to this lane.

/// A claimed or recomputed integer range, bounds written exactly as in `Expr`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Range {
    pub lo: i128,
    pub hi: i128,
}

impl Range {
    pub const fn new(lo: i128, hi: i128) -> Self {
        Range { lo, hi }
    }
}

/// The de Bruijn context the `var` arm reads through (`ctxTyp` on the Lean side).
///
/// Each slot holds the range of that variable, or `None` where the variable is
/// absent or not int-typed: a read of either lands on `none` -- booked, not faked.
#[derive(Debug, Clone, Default)]
pub struct Ctx {
    vars: Vec<Option<Range>>,
}

impl Ctx {
    /// Build a context from head (index 0) to tail.
    pub fn new(vars: Vec<Option<Range>>) -> Self {
        Ctx { vars }
    }

    /// The range of the `k`-th variable, `None` out of range or non-int.
    pub fn lookup(&self, k: usize) -> Option<Range> {
        self.vars.get(k).copied().flatten()
    }
}

/// One global: its carrier range (`intVonTyp` over `D.gtyp`) and whether its
/// guard holds (`gdarf`, recomputed -- never trusted from the print).
#[derive(Debug, Clone)]
pub struct Global {
    pub name: String,
    pub range: Option<Range>,
    pub guard: bool,
}

/// One table: its `count`, its fields with carrier ranges, and whether its guard
/// holds (`darf`, recomputed).
#[derive(Debug, Clone)]
pub struct Table {
    pub name: String,
    pub count: i128,
    pub fields: Vec<(String, Option<Range>)>,
    pub guard: bool,
}

impl Table {
    /// The carrier range of a field, `None` where the field is absent or non-int.
    pub fn field(&self, name: &str) -> Option<Range> {
        self.fields
            .iter()
            .find(|(n, _)| n == name)
            .and_then(|(_, r)| *r)
    }
}

/// The declared world the read arms consult: globals and tables.
#[derive(Debug, Clone, Default)]
pub struct World {
    pub globals: Vec<Global>,
    pub tables: Vec<Table>,
}

impl World {
    /// Find a global by name.
    pub fn global(&self, name: &str) -> Option<&Global> {
        self.globals.iter().find(|g| g.name == name)
    }

    /// Find a table by name.
    pub fn table(&self, name: &str) -> Option<&Table> {
        self.tables.iter().find(|t| t.name == name)
    }
}

/// A derivation term as plain data, mirroring `CertExpr` in `Zeugnis.lean`.
///
/// Hypothesis fields are absent by design: the claimed result range travels
/// beside the term (see [`Certificate`]), and every side condition is
/// recomputed by [`CertExpr::cert_range`], never trusted from the print.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CertExpr {
    /// `(.lit n)` -- exact `(n, n)`.
    Lit(i128),
    /// `(.add a b)` -- `(l1 + l2, h1 + h2)`.
    Add(Box<CertExpr>, Box<CertExpr>),
    /// `(.div a b)` -- `(0, h1)` under `0 <= l1` and `1 <= l2` (M102).
    Div(Box<CertExpr>, Box<CertExpr>),
    /// `(.band a b)` -- `(0, h1)` under `0 <= l1` and `0 <= l2` (M137).
    Band(Box<CertExpr>, Box<CertExpr>),
    /// `(.bor w a b)` -- `(0, 2^w - 1)` under nonnegativity plus `h < 2^w` (M137).
    Bor(u32, Box<CertExpr>, Box<CertExpr>),
    /// `(.bxor w a b)` -- same arm as `bor`.
    Bxor(u32, Box<CertExpr>, Box<CertExpr>),
    /// `(.shl a b)` -- `(0, h1 * 2^h2)` under nonnegativity (M137).
    Shl(Box<CertExpr>, Box<CertExpr>),
    /// `(.shr a b)` -- `(0, h1)` under nonnegativity (M137).
    Shr(Box<CertExpr>, Box<CertExpr>),
    /// `(.wide lo' hi' a)` -- `(lo', hi')` under `lo' <= l1` and `h1 <= hi'`.
    Wide(i128, i128, Box<CertExpr>),
    /// `(.var k)` -- de Bruijn index against the context (`ctxTyp`).
    Var(usize),
    /// `(.glob g)` -- carrier type from the declaration, guard recomputed.
    Glob(String),
    /// `(.slot t f i)` -- field type, under the index shape `0 .. count - 1`
    /// plus the guard, both recomputed.
    Slot(String, String, Box<CertExpr>),
}

/// `2^w`, or `None` where the width does not fit the emitter's arithmetic.
fn pow2(w: u32) -> Option<i128> {
    2i128.checked_pow(w)
}

impl CertExpr {
    /// Print the term in Lean `CertExpr` syntax: what the Rust printer writes.
    pub fn print(&self) -> String {
        match self {
            CertExpr::Lit(n) => format!("(.lit {n})"),
            CertExpr::Add(a, b) => format!("(.add {} {})", a.print(), b.print()),
            CertExpr::Div(a, b) => format!("(.div {} {})", a.print(), b.print()),
            CertExpr::Band(a, b) => format!("(.band {} {})", a.print(), b.print()),
            CertExpr::Bor(w, a, b) => format!("(.bor {w} {} {})", a.print(), b.print()),
            CertExpr::Bxor(w, a, b) => {
                format!("(.bxor {w} {} {})", a.print(), b.print())
            }
            CertExpr::Shl(a, b) => format!("(.shl {} {})", a.print(), b.print()),
            CertExpr::Shr(a, b) => format!("(.shr {} {})", a.print(), b.print()),
            CertExpr::Wide(lo, hi, a) => format!("(.wide {lo} {hi} {})", a.print()),
            CertExpr::Var(k) => format!("(.var {k})"),
            CertExpr::Glob(g) => format!("(.glob {g})"),
            CertExpr::Slot(t, f, i) => format!("(.slot {t} {f} {})", i.print()),
        }
    }

    /// The range table, recomputed: the `certRange` arms for the covered forms.
    ///
    /// `None` means the print has no range at all.
    pub fn cert_range(&self, ctx: &Ctx, world: &World) -> Option<Range> {
        match self {
            CertExpr::Lit(n) => Some(Range::new(*n, *n)),
            CertExpr::Add(a, b) => {
                let x = a.cert_range(ctx, world)?;
                let y = b.cert_range(ctx, world)?;
                Some(Range::new(x.lo.checked_add(y.lo)?, x.hi.checked_add(y.hi)?))
            }
            CertExpr::Div(a, b) => {
                let x = a.cert_range(ctx, world)?;
                let y = b.cert_range(ctx, world)?;
                if 0 <= x.lo && 1 <= y.lo {
                    Some(Range::new(0, x.hi))
                } else {
                    None
                }
            }
            CertExpr::Band(a, b) => {
                let x = a.cert_range(ctx, world)?;
                let y = b.cert_range(ctx, world)?;
                if 0 <= x.lo && 0 <= y.lo {
                    Some(Range::new(0, x.hi))
                } else {
                    None
                }
            }
            CertExpr::Bor(w, a, b) | CertExpr::Bxor(w, a, b) => {
                let x = a.cert_range(ctx, world)?;
                let y = b.cert_range(ctx, world)?;
                let bound = pow2(*w)?;
                if 0 <= x.lo && 0 <= y.lo && x.hi < bound && y.hi < bound {
                    Some(Range::new(0, bound.checked_sub(1)?))
                } else {
                    None
                }
            }
            CertExpr::Shl(a, b) => {
                let x = a.cert_range(ctx, world)?;
                let y = b.cert_range(ctx, world)?;
                if 0 <= x.lo && 0 <= y.lo {
                    let shift: u32 = y.hi.try_into().ok()?;
                    Some(Range::new(0, x.hi.checked_mul(pow2(shift)?)?))
                } else {
                    None
                }
            }
            CertExpr::Shr(a, b) => {
                let x = a.cert_range(ctx, world)?;
                let y = b.cert_range(ctx, world)?;
                if 0 <= x.lo && 0 <= y.lo {
                    Some(Range::new(0, x.hi))
                } else {
                    None
                }
            }
            CertExpr::Wide(lo, hi, a) => {
                let x = a.cert_range(ctx, world)?;
                if *lo <= x.lo && x.hi <= *hi {
                    Some(Range::new(*lo, *hi))
                } else {
                    None
                }
            }
            CertExpr::Var(k) => ctx.lookup(*k),
            CertExpr::Glob(g) => {
                let decl = world.global(g)?;
                let r = decl.range?;
                if decl.guard {
                    Some(r)
                } else {
                    None
                }
            }
            CertExpr::Slot(t, f, i) => {
                let tab = world.table(t)?;
                let idx = i.cert_range(ctx, world)?;
                let field = tab.field(f)?;
                if idx.lo == 0 && idx.hi == tab.count.checked_sub(1)? && tab.guard {
                    Some(field)
                } else {
                    None
                }
            }
        }
    }

    /// The side conditions, named with the values they were checked against.
    ///
    /// Children first, then the node's own line: reading top to bottom replays
    /// the derivation the term prints. A line ending in `HOLDS` records a check
    /// the table recomputed; a line ending in `FAILS` records the side condition
    /// that leaves the print without a range.
    pub fn side_conditions(&self, ctx: &Ctx, world: &World) -> Vec<String> {
        let mut out = Vec::new();
        self.sides_into(ctx, world, &mut out);
        out
    }

    fn sides_into(&self, ctx: &Ctx, world: &World, out: &mut Vec<String>) {
        match self {
            CertExpr::Lit(n) => out.push(format!("lit {n}: exact ({n}, {n}) -- HOLDS")),
            CertExpr::Add(a, b) => {
                a.sides_into(ctx, world, out);
                b.sides_into(ctx, world, out);
                match (a.cert_range(ctx, world), b.cert_range(ctx, world)) {
                    (Some(x), Some(y)) => match (
                        x.lo.checked_add(y.lo),
                        x.hi.checked_add(y.hi),
                    ) {
                        (Some(lo), Some(hi)) => out.push(format!(
                            "add: ({}, {}) + ({}, {}) = ({lo}, {hi}) -- HOLDS",
                            x.lo, x.hi, y.lo, y.hi
                        )),
                        _ => out.push("add: sum overflows -- FAILS".to_string()),
                    },
                    _ => out.push("add: a child has no range -- FAILS".to_string()),
                }
            }
            CertExpr::Div(a, b) => {
                a.sides_into(ctx, world, out);
                b.sides_into(ctx, world, out);
                match (a.cert_range(ctx, world), b.cert_range(ctx, world)) {
                    (Some(x), Some(y)) => {
                        let ok = 0 <= x.lo && 1 <= y.lo;
                        out.push(format!(
                            "div: needs 0 <= l1 and 1 <= l2; have l1 = {}, l2 = {} -- {}",
                            x.lo,
                            y.lo,
                            verdict(ok)
                        ));
                    }
                    _ => out.push("div: a child has no range -- FAILS".to_string()),
                }
            }
            CertExpr::Band(a, b) => {
                a.sides_into(ctx, world, out);
                b.sides_into(ctx, world, out);
                match (a.cert_range(ctx, world), b.cert_range(ctx, world)) {
                    (Some(x), Some(y)) => {
                        let ok = 0 <= x.lo && 0 <= y.lo;
                        out.push(format!(
                            "band: needs 0 <= l1 and 0 <= l2; have l1 = {}, l2 = {} -- {}",
                            x.lo,
                            y.lo,
                            verdict(ok)
                        ));
                    }
                    _ => out.push("band: a child has no range -- FAILS".to_string()),
                }
            }
            CertExpr::Bor(w, a, b) => {
                a.sides_into(ctx, world, out);
                b.sides_into(ctx, world, out);
                out.push(width_side("bor", *w, a, b, ctx, world));
            }
            CertExpr::Bxor(w, a, b) => {
                a.sides_into(ctx, world, out);
                b.sides_into(ctx, world, out);
                out.push(width_side("bxor", *w, a, b, ctx, world));
            }
            CertExpr::Shl(a, b) => {
                a.sides_into(ctx, world, out);
                b.sides_into(ctx, world, out);
                match (a.cert_range(ctx, world), b.cert_range(ctx, world)) {
                    (Some(x), Some(y)) => {
                        let ok = 0 <= x.lo && 0 <= y.lo;
                        out.push(format!(
                            "shl: needs 0 <= l1 and 0 <= l2; have l1 = {}, l2 = {} -- {}",
                            x.lo,
                            y.lo,
                            verdict(ok)
                        ));
                    }
                    _ => out.push("shl: a child has no range -- FAILS".to_string()),
                }
            }
            CertExpr::Shr(a, b) => {
                a.sides_into(ctx, world, out);
                b.sides_into(ctx, world, out);
                match (a.cert_range(ctx, world), b.cert_range(ctx, world)) {
                    (Some(x), Some(y)) => {
                        let ok = 0 <= x.lo && 0 <= y.lo;
                        out.push(format!(
                            "shr: needs 0 <= l1 and 0 <= l2; have l1 = {}, l2 = {} -- {}",
                            x.lo,
                            y.lo,
                            verdict(ok)
                        ));
                    }
                    _ => out.push("shr: a child has no range -- FAILS".to_string()),
                }
            }
            CertExpr::Wide(lo, hi, a) => {
                a.sides_into(ctx, world, out);
                match a.cert_range(ctx, world) {
                    Some(x) => {
                        let ok = *lo <= x.lo && x.hi <= *hi;
                        out.push(format!(
                            "wide [{lo}, {hi}]: needs lo' <= l1 and h1 <= hi'; \
                             have ({}, {}) -- {}",
                            x.lo,
                            x.hi,
                            verdict(ok)
                        ));
                    }
                    None => out.push("wide: the child has no range -- FAILS".to_string()),
                }
            }
            CertExpr::Var(k) => match ctx.lookup(*k) {
                Some(r) => out.push(format!(
                    "var {k}: context lookup = ({}, {}) -- HOLDS",
                    r.lo, r.hi
                )),
                None => out.push(format!(
                    "var {k}: context lookup is empty (out of range or non-int) -- FAILS"
                )),
            },
            CertExpr::Glob(g) => match world.global(g) {
                Some(decl) => match decl.range {
                    Some(r) => out.push(format!(
                        "glob {g}: carrier ({}, {}), guard gdarf = {} -- {}",
                        r.lo,
                        r.hi,
                        decl.guard,
                        verdict(decl.guard)
                    )),
                    None => out.push(format!(
                        "glob {g}: carrier is non-int, no range -- FAILS"
                    )),
                },
                None => out.push(format!("glob {g}: no such global -- FAILS")),
            },
            CertExpr::Slot(t, f, i) => {
                i.sides_into(ctx, world, out);
                match world.table(t) {
                    Some(tab) => {
                        let idx = i.cert_range(ctx, world);
                        let field = tab.field(f);
                        let want = tab.count.checked_sub(1);
                        let ok = idx.is_some_and(|r| {
                            want.is_some_and(|c| r.lo == 0 && r.hi == c)
                        }) && tab.guard
                            && field.is_some();
                        let have_idx = idx
                            .map(|r| format!("({}, {})", r.lo, r.hi))
                            .unwrap_or_else(|| "no range".to_string());
                        let have_field = field
                            .map(|r| format!("({}, {})", r.lo, r.hi))
                            .unwrap_or_else(|| "no range".to_string());
                        out.push(format!(
                            "slot {t}.{f}: index {have_idx} must be 0 .. count - 1 \
                             (count = {}), guard darf = {}, field type {have_field} -- {}",
                            tab.count,
                            tab.guard,
                            verdict(ok)
                        ));
                    }
                    None => out.push(format!("slot {t}.{f}: no such table -- FAILS")),
                }
            }
        }
    }
}

fn verdict(ok: bool) -> &'static str {
    if ok {
        "HOLDS"
    } else {
        "FAILS"
    }
}

/// The shared width side condition of `bor`/`bxor`: nonnegativity plus the
/// `h < 2^w` bound on both children.
fn width_side(
    name: &str,
    w: u32,
    a: &CertExpr,
    b: &CertExpr,
    ctx: &Ctx,
    world: &World,
) -> String {
    match (
        a.cert_range(ctx, world),
        b.cert_range(ctx, world),
        pow2(w),
    ) {
        (Some(x), Some(y), Some(bound)) => {
            let ok = 0 <= x.lo && 0 <= y.lo && x.hi < bound && y.hi < bound;
            format!(
                "{name} (w = {w}): needs 0 <= l1, 0 <= l2, h1 < 2^w and h2 < 2^w; \
                 have ({}, {}) and ({}, {}), 2^w = {bound} -- {}",
                x.lo,
                x.hi,
                y.lo,
                y.hi,
                verdict(ok)
            )
        }
        _ => format!("{name} (w = {w}): a child has no range or 2^w overflows -- FAILS"),
    }
}

/// The printed certificate: the term, the claimed range, the side conditions.
///
/// The claim is whatever the table recomputes -- `None` prints as `no range`,
/// which is what validation rejects. There is no third state.
#[derive(Debug, Clone)]
pub struct Certificate {
    pub term: String,
    pub claimed: Option<Range>,
    pub sides: Vec<String>,
}

impl Certificate {
    /// Render the certificate as stable, tool-free lines.
    pub fn render(&self) -> String {
        let mut out = String::new();
        out.push_str("== derivation certificate (int fragment, emitter half) ==\n");
        out.push_str(&format!("term: {}\n", self.term));
        match self.claimed {
            Some(r) => out.push_str(&format!("claimed range: ({}, {})\n", r.lo, r.hi)),
            None => out.push_str("claimed range: no range -- validation rejects\n"),
        }
        out.push_str("side conditions:\n");
        for s in &self.sides {
            out.push_str(&format!("  - {s}\n"));
        }
        out
    }

    /// Render the certificate as one JSON object — the machine-readable sidecar the
    /// call site writes beside the C. Hand-rolled on purpose, like
    /// `corrcert::CorrCert::to_json`: this file has no JSON dependency, and the shape
    /// is three fixed fields. `claimed` is `[lo, hi]` or `null`; `null` is what
    /// validation rejects, exactly as `render` prints `no range`.
    pub fn to_json(&self) -> String {
        let mut out = String::from("{\"term\":\"");
        out.push_str(&flucht(&self.term));
        out.push_str("\",\"claimed\":");
        match self.claimed {
            Some(r) => out.push_str(&format!("[{},{}]", r.lo, r.hi)),
            None => out.push_str("null"),
        }
        out.push_str(",\"sides\":[");
        for (i, s) in self.sides.iter().enumerate() {
            if i > 0 {
                out.push(',');
            }
            out.push('"');
            out.push_str(&flucht(s));
            out.push('"');
        }
        out.push_str("]}");
        out
    }
}

/// Escape a free-text field for [`Certificate::to_json`]: `\`, `"` and newline.
/// Names that reach here are identifiers today, but the sides carry rendered ranges
/// and punctuation — the escaper is total so a future word cannot break the sidecar.
fn flucht(s: &str) -> String {
    let mut aus = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '\\' => aus.push_str("\\\\"),
            '"' => aus.push_str("\\\""),
            '\n' => aus.push_str("\\n"),
            _ => aus.push(c),
        }
    }
    aus
}

/// Emit the certificate for one checked expression.
pub fn emit(expr: &CertExpr, ctx: &Ctx, world: &World) -> Certificate {
    Certificate {
        term: expr.print(),
        claimed: expr.cert_range(ctx, world),
        sides: expr.side_conditions(ctx, world),
    }
}

/// Emit the certificate for one checked expression, rendered as the sidecar object.
/// One call at the call site: build nothing twice, hold no intermediate. The emitter
/// half owns the print direction only (see the module head); this is its printable
/// form beside the C.
pub fn emit_json(expr: &CertExpr, ctx: &Ctx, world: &World) -> String {
    emit(expr, ctx, world).to_json()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn empty() -> (Ctx, World) {
        (Ctx::new(vec![]), World::default())
    }

    fn lit(n: i128) -> Box<CertExpr> {
        Box::new(CertExpr::Lit(n))
    }

    #[test]
    fn lit_prints_and_claims_exact() {
        let (ctx, world) = empty();
        let e = CertExpr::Lit(42);
        assert_eq!(e.print(), "(.lit 42)");
        assert_eq!(e.cert_range(&ctx, &world), Some(Range::new(42, 42)));
    }

    #[test]
    fn add_prints_and_sums_bounds() {
        let (ctx, world) = empty();
        let e = CertExpr::Add(lit(2), lit(3));
        assert_eq!(e.print(), "(.add (.lit 2) (.lit 3))");
        assert_eq!(e.cert_range(&ctx, &world), Some(Range::new(5, 5)));
    }

    #[test]
    fn add_overflow_has_no_range() {
        let (ctx, world) = empty();
        let e = CertExpr::Add(lit(i128::MAX), lit(1));
        assert_eq!(e.cert_range(&ctx, &world), None);
    }

    #[test]
    fn div_prints_and_claims_zero_to_hi() {
        let (ctx, world) = empty();
        let e = CertExpr::Div(lit(7), lit(2));
        assert_eq!(e.print(), "(.div (.lit 7) (.lit 2))");
        assert_eq!(e.cert_range(&ctx, &world), Some(Range::new(0, 7)));
    }

    #[test]
    fn div_by_zero_shaped_denominator_has_no_range() {
        // `1 <= l2` fails: the side condition lands on `none`, not in a message.
        let (ctx, world) = empty();
        let e = CertExpr::Div(lit(7), lit(0));
        assert_eq!(e.cert_range(&ctx, &world), None);
        let cert = emit(&e, &ctx, &world);
        assert!(cert.sides.iter().any(|s| s.ends_with("FAILS")));
        assert!(cert.render().contains("no range"));
    }

    #[test]
    fn div_negative_numerator_has_no_range() {
        // `0 <= l1` fails.
        let (ctx, world) = empty();
        let e = CertExpr::Div(
            Box::new(CertExpr::Add(lit(-5), lit(1))),
            lit(2),
        );
        assert_eq!(e.cert_range(&ctx, &world), None);
    }

    #[test]
    fn band_prints_and_claims() {
        let (ctx, world) = empty();
        let e = CertExpr::Band(lit(6), lit(3));
        assert_eq!(e.print(), "(.band (.lit 6) (.lit 3))");
        assert_eq!(e.cert_range(&ctx, &world), Some(Range::new(0, 6)));
    }

    #[test]
    fn band_negative_operand_has_no_range() {
        let (ctx, world) = empty();
        let e = CertExpr::Band(lit(-1), lit(3));
        assert_eq!(e.cert_range(&ctx, &world), None);
    }

    #[test]
    fn bor_prints_with_width_and_claims_full_width() {
        let (ctx, world) = empty();
        let e = CertExpr::Bor(3, lit(6), lit(3));
        assert_eq!(e.print(), "(.bor 3 (.lit 6) (.lit 3))");
        assert_eq!(e.cert_range(&ctx, &world), Some(Range::new(0, 7)));
    }

    #[test]
    fn bor_operand_past_the_width_has_no_range() {
        // `h < 2^w` fails for the first child (8 is not below 8).
        let (ctx, world) = empty();
        let e = CertExpr::Bor(3, lit(8), lit(3));
        assert_eq!(e.cert_range(&ctx, &world), None);
    }

    #[test]
    fn bxor_prints_with_width_and_claims_full_width() {
        let (ctx, world) = empty();
        let e = CertExpr::Bxor(3, lit(6), lit(3));
        assert_eq!(e.print(), "(.bxor 3 (.lit 6) (.lit 3))");
        assert_eq!(e.cert_range(&ctx, &world), Some(Range::new(0, 7)));
    }

    #[test]
    fn shl_prints_and_scales_by_shift() {
        let (ctx, world) = empty();
        let e = CertExpr::Shl(lit(3), lit(2));
        assert_eq!(e.print(), "(.shl (.lit 3) (.lit 2))");
        assert_eq!(e.cert_range(&ctx, &world), Some(Range::new(0, 12)));
    }

    #[test]
    fn shr_prints_and_claims() {
        let (ctx, world) = empty();
        let e = CertExpr::Shr(lit(12), lit(2));
        assert_eq!(e.print(), "(.shr (.lit 12) (.lit 2))");
        assert_eq!(e.cert_range(&ctx, &world), Some(Range::new(0, 12)));
    }

    #[test]
    fn wide_narrows_within_bounds() {
        let (ctx, world) = empty();
        let e = CertExpr::Wide(0, 7, lit(3));
        assert_eq!(e.print(), "(.wide 0 7 (.lit 3))");
        assert_eq!(e.cert_range(&ctx, &world), Some(Range::new(0, 7)));
    }

    #[test]
    fn wide_outside_bounds_has_no_range() {
        let (ctx, world) = empty();
        let e = CertExpr::Wide(0, 7, lit(9));
        assert_eq!(e.cert_range(&ctx, &world), None);
    }

    #[test]
    fn var_reads_the_context() {
        let ctx = Ctx::new(vec![Some(Range::new(3, 3))]);
        let world = World::default();
        let e = CertExpr::Var(0);
        assert_eq!(e.print(), "(.var 0)");
        assert_eq!(e.cert_range(&ctx, &world), Some(Range::new(3, 3)));
    }

    #[test]
    fn var_past_the_context_has_no_range() {
        let (ctx, world) = empty();
        let e = CertExpr::Var(0);
        assert_eq!(e.cert_range(&ctx, &world), None);
    }

    #[test]
    fn var_non_int_slot_has_no_range() {
        let ctx = Ctx::new(vec![None]);
        let world = World::default();
        let e = CertExpr::Var(0);
        assert_eq!(e.cert_range(&ctx, &world), None);
    }

    #[test]
    fn glob_reads_carrier_and_guard() {
        let (ctx, _) = empty();
        let world = World {
            globals: vec![Global {
                name: "G".to_string(),
                range: Some(Range::new(0, 255)),
                guard: true,
            }],
            tables: vec![],
        };
        let e = CertExpr::Glob("G".to_string());
        assert_eq!(e.print(), "(.glob G)");
        assert_eq!(e.cert_range(&ctx, &world), Some(Range::new(0, 255)));
    }

    #[test]
    fn glob_without_guard_has_no_range() {
        let (ctx, _) = empty();
        let world = World {
            globals: vec![Global {
                name: "G".to_string(),
                range: Some(Range::new(0, 255)),
                guard: false,
            }],
            tables: vec![],
        };
        let e = CertExpr::Glob("G".to_string());
        assert_eq!(e.cert_range(&ctx, &world), None);
    }

    #[test]
    fn slot_reads_field_under_exact_index_shape() {
        let (ctx, _) = empty();
        let world = World {
            globals: vec![],
            tables: vec![Table {
                name: "T".to_string(),
                count: 8,
                fields: vec![("f".to_string(), Some(Range::new(0, 100)))],
                guard: true,
            }],
        };
        let e = CertExpr::Slot(
            "T".to_string(),
            "f".to_string(),
            Box::new(CertExpr::Wide(0, 7, lit(3))),
        );
        assert_eq!(e.print(), "(.slot T f (.wide 0 7 (.lit 3)))");
        assert_eq!(e.cert_range(&ctx, &world), Some(Range::new(0, 100)));
    }

    #[test]
    fn slot_bare_literal_index_has_no_range() {
        // A bare literal is not an index until `wide` says so: `(3, 3)` is not
        // `(0, count - 1)`, so the arm lands on `none`.
        let (ctx, _) = empty();
        let world = World {
            globals: vec![],
            tables: vec![Table {
                name: "T".to_string(),
                count: 8,
                fields: vec![("f".to_string(), Some(Range::new(0, 100)))],
                guard: true,
            }],
        };
        let e = CertExpr::Slot("T".to_string(), "f".to_string(), lit(3));
        assert_eq!(e.cert_range(&ctx, &world), None);
    }

    #[test]
    fn slot_without_guard_has_no_range() {
        let (ctx, _) = empty();
        let world = World {
            globals: vec![],
            tables: vec![Table {
                name: "T".to_string(),
                count: 8,
                fields: vec![("f".to_string(), Some(Range::new(0, 100)))],
                guard: false,
            }],
        };
        let e = CertExpr::Slot(
            "T".to_string(),
            "f".to_string(),
            Box::new(CertExpr::Wide(0, 7, lit(3))),
        );
        assert_eq!(e.cert_range(&ctx, &world), None);
    }

    #[test]
    fn render_carries_term_claim_and_sides() {
        let (ctx, world) = empty();
        let cert = emit(&CertExpr::Add(lit(2), lit(3)), &ctx, &world);
        let text = cert.render();
        assert!(text.contains("term: (.add (.lit 2) (.lit 3))"));
        assert!(text.contains("claimed range: (5, 5)"));
        assert!(text.contains("side conditions:"));
        assert!(text.contains("HOLDS"));
    }

    #[test]
    fn json_carries_term_claim_and_sides() {
        let (ctx, world) = empty();
        let cert = emit(&CertExpr::Add(lit(2), lit(3)), &ctx, &world);
        let j = cert.to_json();
        assert!(j.starts_with("{\"term\":\"(.add (.lit 2) (.lit 3))\""));
        assert!(j.contains("\"claimed\":[5,5]"));
        assert!(j.contains("\"sides\":["));
        assert!(j.contains("HOLDS"));
        assert!(j.ends_with("]}"));
    }

    #[test]
    fn json_claim_without_range_is_null() {
        // The machine reading of what `render` prints as `no range`.
        let (ctx, world) = empty();
        let cert = emit(&CertExpr::Div(lit(7), lit(0)), &ctx, &world);
        assert_eq!(cert.claimed, None);
        let j = cert.to_json();
        assert!(j.contains("\"claimed\":null"));
        assert!(j.contains("FAILS"));
    }

    #[test]
    fn emit_json_is_emit_then_to_json() {
        let (ctx, world) = empty();
        let e = CertExpr::Bor(3, lit(6), lit(3));
        assert_eq!(emit_json(&e, &ctx, &world), emit(&e, &ctx, &world).to_json());
    }

    #[test]
    fn flucht_macht_seitenwagenfelder_ganz() {
        assert_eq!(flucht("a\\b\"c\nd"), "a\\\\b\\\"c\\nd");
        assert_eq!(flucht("(.lit 42)"), "(.lit 42)");
    }
}
