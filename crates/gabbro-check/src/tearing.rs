//! Post-emission check: shared-carrier sequence refusal (`T001`).
//!
//! The lane-47 inventory (`messung/TEARING-INVENTAR.md`) measured the emitted C
//! of three corpus units as assembler at `-O0`/`-O2` on x86_64, and the lane-70
//! ruling (`messung/TEARING-RULING.md`) sorted the eight measured forms into
//! five single-access admissions and three sequence refusals. This module is
//! the enforcement half of that ruling: it scans the emitted C of one unit,
//! line by line, for a multi-access sequence on a shared carrier, and refuses
//! it with a named code. Single-access rows pass silently; volatile register
//! traffic is recorded as open, never as admitted.
//!
//! ## Refusal logic
//!
//! | emitted C shape | verdict | guarantee named | lane-47 evidence |
//! |---|---|---|
//! | compound assign (`+=`, `-=`, `&=`, `\|=`) to a shared carrier | refuse `T001` | exclusive access; the atomic form is the upgrade path | slot `+=`: load/`leal`/store at -O0, one `addl` with no lock prefix at -O2 |
//! | guarded compound assign (same, under an `if`) | refuse `T001` | exclusive access; the guard sits beside the sequence | `movl`/`leal`/`movl` triple at -O0, load/`subl`/store at -O2 |
//! | relaxed load, local fold, relaxed store on a shared cell | refuse `T001` | single-writer-per-cell | `addl mem, reg` then store at -O2 |
//! | plain `=` store, atomic compare-exchange, release store / acquire load, lock take/release calls | pass | the atomicity price is in the ruling, not re-checked here | single `movb`/`movq`, `lock cmpxchgl`, plain moves, one `call` each |
//! | `volatile` access or `__volatile__` asm | open, no verdict | unmeasured: no device unit in the inventory | not measured at either level |
//!
//! Carrier sharing is NOT re-derived from the C text. The caller passes it in
//! from the declarations: table and `static mut` roots become `carriers`,
//! `accumulates` stems become `cells`. A compound assign to a name nobody
//! declared shared is a local fold and passes; the merge fold `z += v` passes
//! for the same reason, and only the load/fold/store triple on a declared
//! cell refuses.
//!
//! ## The one hook point (NOT wired here)
//!
//! This module is standalone on purpose: no `lib.rs` registration, no
//! `emit.rs` call. When it is wired, the call is a single post-emission scan
//! per unit — the C text is complete, `check` runs once over it:
//!
//! * site: `emit.rs`, function `anweisung`, the `StmtArt::Zuweisung` arm, the
//!   terminal push that lowers every plain and compound place assignment
//!   (`ort(&z.ziel, ..)`, `zuw_op(&z.op)`, the `=`/`+=`/`-=`/`&=`/`|=` text).
//!   That arm is the single funnel through which slot and global compound
//!   assign reaches the C text.
//! * the merge-add lowering (`accumulates` declaration emission, the
//!   `_melde`/`_lies` pair with `atomic_load_explicit` / fold /
//!   `atomic_store_explicit`) needs NO second hook: the same scan sees the
//!   load/fold/store triple after the fact, which is why one hook point is
//!   enough for both sequence shapes.
//! * `SharedCarriers` is built from the unit's declarations at the same site:
//!   tables and `static mut` globals name the carriers, `accumulates` names
//!   the cells.
//!
//! Wiring it as a hard gate today would red-flag the corpus's own disciplined
//! units: `01-tabelle` compounds under `KAPPEN` (exclusive access held at the
//! Gabbro level, invisible in the C text) and `05-nebenlaeufigkeit` merges
//! under single-writer-per-cell (a discipline over cores, not over lines).
//! The refusal names the guarantee; proving the guarantee is held belongs to
//! the lock passes, not to a text scan. Until that join exists, this module
//! ships as the refusal logic with its fixtures, not as a gate.
//!
//! ## Why text, not the tree
//!
//! The ruling is about the MACHINE shape of the emitted C, and the machine
//! shape depends on the C compiler and its level, not on the Gabbro AST. A
//! tree check would re-assert what the checker already knows; a text check
//! reads what is actually shipped. That is also why this module takes no
//! `gabbro_syntax` types and compiles on `std` alone.
//!
//! ## Open remainder
//!
//! Volatile register access (`*(volatile uintN_t *)(basis + off)`, port
//! `__asm__ __volatile__`) has no verdict in the inventory and gets none
//! here: `check` lists such lines under `open` and refuses nothing for them.
//! Measuring them needs the device unit, a fourth unit outside the
//! inventory's budget. They are counted openly rather than silently.

use std::collections::BTreeSet;

/// The one refusal code of this module. `T` is unused anywhere else in
/// `crates/` (checked against the kennungen guardian: one code, one file).
pub const CODE: &str = "T001";

/// Carrier sharing from the declarations, passed in by the caller.
///
/// * `carriers`: roots shared between contexts — table variables (`c`, `o`)
///   and `static mut` globals (`farbbericht`). A compound assign whose line
///   names one of these is a sequence on shared state.
/// * `cells`: `accumulates` stems (`z` for `z_zellen[k]`). Only the
///   load/fold/store triple on a declared cell refuses; the local fold alone
///   (`z += v`) is not shared traffic.
#[derive(Debug, Clone, Default)]
pub struct SharedCarriers {
    pub carriers: BTreeSet<String>,
    pub cells: BTreeSet<String>,
}

impl SharedCarriers {
    pub fn new(carriers: &[&str], cells: &[&str]) -> Self {
        Self {
            carriers: carriers.iter().map(|s| s.to_string()).collect(),
            cells: cells.iter().map(|s| s.to_string()).collect(),
        }
    }

    pub fn empty() -> Self {
        Self::default()
    }
}

/// Which sequence shape a refusal stands on. The shape decides the guarantee.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Kind {
    /// `+=`, `-=`, `&=` or `|=` to a shared carrier, guarded or not. The
    /// guard refines when the sequence runs without merging it into one
    /// access, so it changes nothing about the verdict.
    CompoundAssign { carrier: String, op: String },
    /// Relaxed load, local fold, relaxed store on a shared accumulates cell
    /// inside one function body.
    MergeAdd { cell: String },
}

impl Kind {
    /// The exact guarantee that redeems this refusal, in the ruling's words.
    pub fn guarantee(&self) -> &'static str {
        match self {
            Kind::CompoundAssign { .. } => "exclusive access",
            Kind::MergeAdd { .. } => "single-writer-per-cell",
        }
    }

    fn describe(&self) -> String {
        match self {
            Kind::CompoundAssign { carrier, op } => format!(
                "sequence `{op}=` on shared carrier `{carrier}` -- needs exclusive access; \
                 the atomic form is the upgrade path"
            ),
            Kind::MergeAdd { cell } => format!(
                "relaxed load-fold-store sequence on shared cell `{cell}_zellen` -- needs \
                 single-writer-per-cell: each core writes its own cell and the merge loop reads"
            ),
        }
    }
}

/// One refused line: the code, the 1-based line number, the line itself, and
/// the shape that fired.
#[derive(Debug, Clone)]
pub struct Refusal {
    pub code: &'static str,
    pub line_no: usize,
    pub line: String,
    pub kind: Kind,
}

impl Refusal {
    pub fn message(&self) -> String {
        format!("[{}] line {}: {}", self.code, self.line_no, self.kind.describe())
    }
}

/// One volatile line: seen, recorded, no verdict. The device unit that would
/// measure it is outside the inventory's budget, so these are counted openly
/// rather than admitted silently.
#[derive(Debug, Clone)]
pub struct OpenSite {
    pub line_no: usize,
    pub line: String,
}

#[derive(Debug, Clone, Default)]
pub struct Report {
    pub refusals: Vec<Refusal>,
    pub open: Vec<OpenSite>,
}

impl Report {
    pub fn is_clean(&self) -> bool {
        self.refusals.is_empty()
    }
}

/// Scan the emitted C of one unit. Every refusal is collected; the scan
/// never stops at the first hit — a measurement that aborts at the first
/// finding answers "at least one fires", not "which ones fire".
pub fn check(emitted: &str, shared: &SharedCarriers) -> Report {
    let mut report = Report::default();
    let blanked = blank_comments_and_strings(emitted);
    let lines: Vec<(usize, &str, &str)> = emitted
        .lines()
        .zip(blanked.lines())
        .enumerate()
        .map(|(i, (raw, clean))| (i + 1, raw, clean))
        .collect();
    let regions = regions(&lines);

    // The compound rule is per line; the merge rule needs the function body,
    // so merge candidates are gathered per region first.
    let mut loads: Vec<(usize, String, usize)> = Vec::new(); // (line idx, stem, region)
    let mut folds: Vec<(usize, usize)> = Vec::new();
    let mut stores: Vec<(usize, String, usize)> = Vec::new();

    for (idx, (no, raw, clean)) in lines.iter().enumerate() {
        if clean.contains("volatile") {
            // Covers `*(volatile uintN_t *)` AND port `__asm__ __volatile__`:
            // both are device-ordered traffic outside the measured inventory.
            report.open.push(OpenSite { line_no: *no, line: raw.to_string() });
            continue;
        }
        for op in ["+=", "-=", "&=", "|="] {
            if clean.contains(op) && shared.carriers.iter().any(|c| contains_word(clean, c)) {
                let carrier = shared
                    .carriers
                    .iter()
                    .find(|c| contains_word(clean, c))
                    .expect("checked above")
                    .clone();
                report.refusals.push(Refusal {
                    code: CODE,
                    line_no: *no,
                    line: raw.to_string(),
                    kind: Kind::CompoundAssign {
                        carrier,
                        op: op.trim_end_matches('=').to_string(),
                    },
                });
                break;
            }
        }
        // `++`/`--` are deliberately NOT compound shapes: the emitter uses
        // them only for locals and loop counters (`k++` in the merge loop),
        // never for shared-carrier traffic.
        let region = regions[idx];
        for stem in cell_stems(clean, "atomic_load_explicit") {
            if shared.cells.contains(&stem) {
                loads.push((idx, stem, region));
            }
        }
        if ["+=", "|=", "?"].iter().any(|t| clean.contains(t)) {
            folds.push((idx, region));
        }
        for stem in cell_stems(clean, "atomic_store_explicit") {
            if shared.cells.contains(&stem) {
                stores.push((idx, stem, region));
            }
        }
    }

    // One refusal per store that completes a load/fold/store triple on the
    // same cell in the same function body. The emitter always folds between
    // the two builtins (ternary for max/min, `+=` for add, `|=` for or/and),
    // so the pair with a fold between them IS the measured sequence.
    for (s_idx, stem, region) in &stores {
        let fired = loads.iter().any(|(l_idx, l_stem, l_region)| {
            l_stem == stem
                && l_region == region
                && *l_idx < *s_idx
                && folds.iter().any(|(f_idx, f_region)| {
                    f_region == region && *l_idx < *f_idx && *f_idx < *s_idx
                })
        });
        if fired {
            let (no, raw, _) = &lines[*s_idx];
            report.refusals.push(Refusal {
                code: CODE,
                line_no: *no,
                line: raw.to_string(),
                kind: Kind::MergeAdd { cell: stem.clone() },
            });
        }
    }

    report
}

/// Identifier-boundary match: `c` matches `c->slots` but not `cells` or
/// `_cx1`. Single-letter table roots make the boundary load-bearing.
fn contains_word(haystack: &str, needle: &str) -> bool {
    if needle.is_empty() {
        return false;
    }
    haystack
        .match_indices(needle)
        .any(|(i, _)| {
            let before = haystack[..i].chars().next_back();
            let after = haystack[i + needle.len()..].chars().next();
            let ident = |c: Option<char>| c.is_some_and(|c| c.is_alphanumeric() || c == '_');
            !ident(before) && !ident(after)
        })
}

/// Stems of `<stem>_zellen[k]` accessed through the named builtin on this
/// line: `z` for `atomic_load_explicit(&z_zellen[k], ...)`.
fn cell_stems(line: &str, builtin: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut rest = line;
    while let Some(i) = rest.find("_zellen[k]") {
        let stem: String = rest[..i]
            .chars()
            .rev()
            .take_while(|c| c.is_alphanumeric() || *c == '_')
            .collect::<String>()
            .chars()
            .rev()
            .collect();
        let call = format!("{builtin}(&{stem}_zellen[k]");
        if !stem.is_empty() && line.contains(&call) {
            out.push(stem);
        }
        rest = &rest[i + "_zellen[k]".len()..];
    }
    out
}

/// Region per line: each function body (plus the file-scope lines around it)
/// gets its own number, so a load in `_lies` never pairs with a store in
/// `_melde`. File-scope lines never carry cell builtins, so sharing a region
/// with the neighbour body is harmless.
fn regions(lines: &[(usize, &str, &str)]) -> Vec<usize> {
    let mut out = Vec::with_capacity(lines.len());
    let mut region = 0usize;
    let mut depth = 0i64;
    let mut above_zero = false;
    for (_, _, clean) in lines {
        out.push(region);
        depth += clean.chars().filter(|c| *c == '{').count() as i64;
        depth -= clean.chars().filter(|c| *c == '}').count() as i64;
        if depth > 0 {
            above_zero = true;
        }
        if above_zero && depth <= 0 {
            region += 1;
            above_zero = false;
        }
    }
    out
}

/// Blank block comments, line comments, and string/char literals (newlines
/// kept, so line numbers survive). A `+=` inside a comment or a literal is
/// not a sequence, and matching it would be a refusal about documentation.
fn blank_comments_and_strings(emitted: &str) -> String {
    #[derive(PartialEq)]
    enum State {
        Code,
        LineComment,
        BlockComment,
        Str,
        Char,
    }
    let mut state = State::Code;
    let mut out = String::with_capacity(emitted.len());
    let mut chars = emitted.chars().peekable();
    while let Some(c) = chars.next() {
        match state {
            State::Code => match c {
                '/' if chars.peek() == Some(&'*') => {
                    chars.next();
                    out.push_str("  ");
                    state = State::BlockComment;
                }
                '/' if chars.peek() == Some(&'/') => {
                    chars.next();
                    out.push_str("  ");
                    state = State::LineComment;
                }
                '"' => {
                    out.push(' ');
                    state = State::Str;
                }
                '\'' => {
                    out.push(' ');
                    state = State::Char;
                }
                _ => out.push(c),
            },
            State::LineComment => {
                if c == '\n' {
                    out.push('\n');
                    state = State::Code;
                } else {
                    out.push(' ');
                }
            }
            State::BlockComment => {
                if c == '*' && chars.peek() == Some(&'/') {
                    chars.next();
                    out.push_str("  ");
                    state = State::Code;
                } else if c == '\n' {
                    out.push('\n');
                } else {
                    out.push(' ');
                }
            }
            State::Str => {
                if c == '\\' {
                    out.push(' ');
                    if let Some(e) = chars.next() {
                        out.push(if e == '\n' { '\n' } else { ' ' });
                    }
                } else if c == '"' {
                    out.push(' ');
                    state = State::Code;
                } else if c == '\n' {
                    out.push('\n');
                } else {
                    out.push(' ');
                }
            }
            State::Char => {
                if c == '\\' {
                    out.push(' ');
                    if let Some(e) = chars.next() {
                        out.push(if e == '\n' { '\n' } else { ' ' });
                    }
                } else if c == '\'' {
                    out.push(' ');
                    state = State::Code;
                } else if c == '\n' {
                    out.push('\n');
                } else {
                    out.push(' ');
                }
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The thirteen assembler lines of the lane-47 evidence block
    /// (`messung/TEARING-INVENTAR.md`), verbatim. They are the ground truth
    /// this module enforces: every line is cited by at least one row of
    /// `ROWS`, and `all_evidence_lines_cited` proves it mechanically.
    const LANE47_ASM: [&str; 13] = [
        "addl    $1, 4(%rdi,%rax,8)          # slot += 1 at -O2, single RMW, no lock",
        "movl    (%rax), %eax                # guarded -= at -O0, the load half",
        "leal    -1(%rax), %edx              # guarded -= at -O0, the op half",
        "movl    %edx, (%rax)                # guarded -= at -O0, the store half",
        "lock cmpxchgl %edi, BESITZER(%rip)  # atomic exchange at -O2, single and atomic",
        "sete    %al                         # exchange result, flags to boolean",
        "movq    %rdi, farbbericht(%rip)     # shared global store at -O2, single mov",
        "movb    $1, FARBE_FERTIG(%rip)      # release store at -O2, single mov, no fence",
        "movzbl  FARBE_FERTIG(%rip), %eax    # acquire load at -O2, single mov, no fence",
        "addl    (%rdx,%rax,4), %ebx         # relaxed merge-add at -O2, load-op half",
        "movl    %ebx, (%rdx,%rax,4)         # relaxed merge-add at -O2, store half",
        "call    KAPPEN_nimm@PLT             # lock take, one call instruction",
        "jmp     KAPPEN_gib@PLT              # lock release at -O2, tail call",
    ];

    #[derive(Debug, PartialEq)]
    enum Verdict {
        Admit,
        Refuse(&'static str),
        Open,
    }

    struct Row {
        name: &'static str,
        c: &'static str,
        asm_o0: &'static str,
        asm_o2: &'static str,
        verdict: Verdict,
    }

    /// One row per measured form: the emitted C this module scans, the
    /// assembler both levels showed, and the verdict the ruling gave it.
    /// Rows that the evidence block describes only in table words cite those
    /// words (slot plain assign has no evidence-block line of its own).
    const ROWS: &[Row] = &[
        Row {
            name: "slot plain assign",
            c: "c->slots[s].benutzt = false;",
            asm_o0: "single `movb` store",
            asm_o2: "single `movb` store (folded into surrounding code)",
            verdict: Verdict::Admit,
        },
        Row {
            name: "shared global plain assign",
            c: "farbbericht = wert;",
            asm_o0: "single `movq` store",
            asm_o2: "movq    %rdi, farbbericht(%rip)     # shared global store at -O2, single mov",
            verdict: Verdict::Admit,
        },
        Row {
            name: "slot compound assign",
            c: "c->slots[s].marke += 1;",
            asm_o0: "sequence: load, `leal`, store",
            asm_o2: "addl    $1, 4(%rdi,%rax,8)          # slot += 1 at -O2, single RMW, no lock",
            verdict: Verdict::Refuse("exclusive access"),
        },
        Row {
            name: "guarded compound assign",
            c: "if (o->slots[obj].zaehler > 0) {\n    o->slots[obj].zaehler -= 1;\n}",
            asm_o0: "movl    (%rax), %eax                # guarded -= at -O0, the load half\n\
                     leal    -1(%rax), %edx              # guarded -= at -O0, the op half\n\
                     movl    %edx, (%rax)                # guarded -= at -O0, the store half",
            asm_o2: "sequence: load, `subl`, store, value reused by the following zero test",
            verdict: Verdict::Refuse("exclusive access"),
        },
        Row {
            name: "atomic compare-exchange",
            c: "ok = atomic_compare_exchange_strong_explicit(&BESITZER, &_erw, wert, \
                memory_order_release, memory_order_acquire);",
            asm_o0: "lock cmpxchgl %edi, BESITZER(%rip)  # atomic exchange at -O2, single and atomic",
            asm_o2: "lock cmpxchgl %edi, BESITZER(%rip)  # atomic exchange at -O2, single and atomic\n\
                     sete    %al                         # exchange result, flags to boolean",
            verdict: Verdict::Admit,
        },
        Row {
            name: "release store and acquire load",
            c: "atomic_store_explicit(&FARBE_FERTIG, 1, memory_order_release);\n\
                x = atomic_load_explicit(&FARBE_FERTIG, memory_order_acquire);",
            asm_o0: "single `movb` store and single `movzbl` load",
            asm_o2: "movb    $1, FARBE_FERTIG(%rip)      # release store at -O2, single mov, no fence\n\
                     movzbl  FARBE_FERTIG(%rip), %eax    # acquire load at -O2, single mov, no fence",
            verdict: Verdict::Admit,
        },
        Row {
            name: "relaxed merge-add",
            c: "static void z_melde(uint32_t roh) __attribute__((unused));\n\
                static void z_melde(uint32_t roh) {\n\
                \x20   uint32_t v = roh;\n\
                \x20   uint32_t k = gabbro_kern();\n\
                \x20   uint32_t z = atomic_load_explicit(&z_zellen[k], memory_order_relaxed);\n\
                \x20   z += v;\n\
                \x20   atomic_store_explicit(&z_zellen[k], z, memory_order_relaxed);\n\
                }",
            asm_o0: "sequence: load, add, store",
            asm_o2: "addl    (%rdx,%rax,4), %ebx         # relaxed merge-add at -O2, load-op half\n\
                     movl    %ebx, (%rdx,%rax,4)         # relaxed merge-add at -O2, store half",
            verdict: Verdict::Refuse("single-writer-per-cell"),
        },
        Row {
            name: "lock take and release",
            c: "KAPPEN_nimm();\nKAPPEN_gib();",
            asm_o0: "single `call` each",
            asm_o2: "call    KAPPEN_nimm@PLT             # lock take, one call instruction\n\
                     jmp     KAPPEN_gib@PLT              # lock release at -O2, tail call",
            verdict: Verdict::Admit,
        },
        Row {
            name: "volatile register access",
            c: "x = (*(volatile uint16_t *)(d->basis + 0xc));",
            asm_o0: "not measured -- no volatile site in the three units",
            asm_o2: "not measured -- no volatile site in the three units",
            verdict: Verdict::Open,
        },
    ];

    fn sharing() -> SharedCarriers {
        SharedCarriers::new(&["c", "o", "farbbericht"], &["z"])
    }

    #[test]
    fn rows_get_their_ruling_verdicts() {
        for row in ROWS {
            let report = check(row.c, &sharing());
            match row.verdict {
                Verdict::Admit => {
                    assert!(report.refusals.is_empty(), "{}: refused: {:?}", row.name, report.refusals);
                    assert!(report.open.is_empty(), "{}: open: {:?}", row.name, report.open);
                }
                Verdict::Refuse(guarantee) => {
                    assert_eq!(report.refusals.len(), 1, "{}: {:?}", row.name, report.refusals);
                    let r = &report.refusals[0];
                    assert_eq!(r.code, CODE);
                    assert_eq!(r.kind.guarantee(), guarantee, "{}", row.name);
                    assert!(report.open.is_empty(), "{}", row.name);
                }
                Verdict::Open => {
                    assert!(report.refusals.is_empty(), "{}: refused: {:?}", row.name, report.refusals);
                    assert_eq!(report.open.len(), 1, "{}", row.name);
                }
            }
        }
    }

    #[test]
    fn all_evidence_lines_cited() {
        // Every assembler line of the inventory's evidence block is cited by
        // at least one row, at a named level. A fixture nobody cites is
        // decoration; a line the table drops is a verdict without evidence.
        let cited: String = ROWS.iter().map(|r| format!("{}\n{}", r.asm_o0, r.asm_o2)).collect();
        for line in LANE47_ASM {
            assert!(cited.contains(line), "evidence line cited by no row: {line}");
        }
    }

    #[test]
    fn every_row_names_both_levels() {
        // The ruling's level binding: slot `+=` crosses the single/sequence
        // boundary between -O0 and -O2, so a row that names one level is an
        // incomplete fixture.
        for row in ROWS {
            assert!(!row.asm_o0.is_empty(), "{}", row.name);
            assert!(!row.asm_o2.is_empty(), "{}", row.name);
        }
    }

    #[test]
    fn refusal_points_at_the_sequence_line() {
        let c = "c->slots[s].benutzt = false;\nc->slots[s].marke += 1;\n";
        let report = check(c, &sharing());
        assert_eq!(report.refusals.len(), 1);
        assert_eq!(report.refusals[0].line_no, 2);
        assert_eq!(report.refusals[0].code, "T001");
        let msg = report.refusals[0].message();
        assert!(msg.contains("T001"), "{msg}");
        assert!(msg.contains("exclusive access"), "{msg}");
        assert!(msg.contains('c'), "{msg}");
    }

    #[test]
    fn merge_refusal_names_the_cell_and_its_discipline() {
        let row = &ROWS[6];
        let report = check(row.c, &sharing());
        assert_eq!(report.refusals.len(), 1);
        assert!(matches!(&report.refusals[0].kind, Kind::MergeAdd { cell } if cell == "z"));
        assert!(report.refusals[0].message().contains("single-writer-per-cell"));
    }

    #[test]
    fn merge_shape_on_an_undeclared_cell_passes() {
        // Sharing comes from the declarations. Without the cell in the set
        // there is no shared traffic, and the scan stays silent instead of
        // inventing a carrier.
        let row = &ROWS[6];
        let report = check(row.c, &SharedCarriers::empty());
        assert!(report.is_clean(), "{:?}", report.refusals);
    }

    #[test]
    fn read_only_merge_loop_passes() {
        // `_lies` loads every cell and stores none: reads without the
        // write-back are single accesses, not a sequence.
        let c = "static uint32_t z_lies(void) {\n\
                 \x20   uint32_t z = 0;\n\
                 \x20   for (uint32_t k = 0; k < (uint32_t)(4); k++) {\n\
                 \x20       uint32_t v = atomic_load_explicit(&z_zellen[k], memory_order_relaxed);\n\
                 \x20       z += v;\n\
                 \x20   }\n\
                 \x20   return z;\n\
                 }";
        let report = check(c, &sharing());
        assert!(report.is_clean(), "{:?}", report.refusals);
    }

    #[test]
    fn loads_and_stores_in_different_functions_never_pair() {
        // The load sits in one body, the store in another: no triple, no
        // refusal. Regions keep the two halves apart.
        let c = "static uint32_t z_a(void) {\n\
                 \x20   uint32_t z = atomic_load_explicit(&z_zellen[k], memory_order_relaxed);\n\
                 \x20   return z;\n\
                 }\n\
                 static void z_b(uint32_t z) {\n\
                 \x20   z += 1;\n\
                 \x20   atomic_store_explicit(&z_zellen[k], z, memory_order_relaxed);\n\
                 }";
        let report = check(c, &sharing());
        assert!(report.is_clean(), "{:?}", report.refusals);
    }

    #[test]
    fn compound_assign_to_a_local_passes() {
        // The merge fold `z += v` names no declared carrier: it is the local
        // half of the sequence, refused only together with its cell triple.
        let report = check("z += v;", &sharing());
        assert!(report.is_clean(), "{:?}", report.refusals);
    }

    #[test]
    fn compound_op_in_comment_or_string_is_not_a_sequence() {
        let c = "/* accumulates z merge add per cpu 4 -- one cell per core; fold: z += v */\n\
                 const char *s = \"a += b\";\n\
                 c->slots[s].benutzt = false;";
        let report = check(c, &sharing());
        assert!(report.is_clean(), "{:?}", report.refusals);
    }

    #[test]
    fn loop_counter_increment_is_not_a_sequence() {
        // `k++` is a local counter, and `++` is not one of the four compound
        // shapes anyway -- even a carrier named `k` would not fire here.
        let c = "for (uint32_t k = 0; k < (uint32_t)(4); k++) {\n\
                 \x20   sum += a[k];\n\
                 }";
        let report = check(c, &sharing());
        assert!(report.is_clean(), "{:?}", report.refusals);
    }

    #[test]
    fn port_asm_stays_open_like_volatile() {
        // `at port` lowers to `in`/`out` behind `__asm__ __volatile__`: device
        // traffic, unmeasured like every other volatile line.
        let c = "__asm__ __volatile__(\"inb %w[tor], %b[wert]\\n\"\n\
                 \x20   : [wert] \"=a\" (wert)\n\
                 \x20   : [tor] \"Nd\" (tor));";
        let report = check(c, &sharing());
        assert!(report.refusals.is_empty(), "{:?}", report.refusals);
        // Only the `__asm__` line itself carries the marker; the operand
        // lines are plain constraints, seen and passed over.
        assert_eq!(report.open.len(), 1);
        assert_eq!(report.open[0].line_no, 1);
    }

    #[test]
    fn scan_does_not_stop_at_the_first_hit() {
        let c = "c->slots[s].marke += 1;\no->slots[obj].zaehler -= 1;\n";
        let report = check(c, &sharing());
        assert_eq!(report.refusals.len(), 2);
        assert_eq!(report.refusals[0].line_no, 1);
        assert_eq!(report.refusals[1].line_no, 2);
    }

    #[test]
    fn single_letter_carrier_needs_word_boundaries() {
        // `c` must not match inside `cells`, `_cx1`, or `farbbericht`.
        let c = "cells = _cx1;\nfarbbericht = wert;";
        let report = check(c, &SharedCarriers::new(&["c"], &[]));
        assert!(report.is_clean(), "{:?}", report.refusals);
        let c = "c->slots[s].x |= mask;";
        let report = check(c, &SharedCarriers::new(&["c"], &[]));
        assert_eq!(report.refusals.len(), 1);
    }
}
