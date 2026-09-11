//! Per-primitive C statement budget enforcement.
//!
//! The lowering contract in `grammatik/Grammatik/Ziel.lean` carries the
//! assumption that every Gabbro primitive lowers to a BOUNDED list of C
//! forms:
//!
//! ```text
//! structure Absenkung where
//!   proPrimitiv : Nat
//!   begrenzt : proPrimitiv <= 18
//! def absenkung : Absenkung := ⟨17, by decide⟩
//! ```
//!
//! The bound `18` is the measured maximum `17` (`Schleife`, subform
//! `traverse over descendants of`, `emit.rs:8523-8560`) plus one headroom
//! (`messung/ABSENKUNG-MESSUNG.md`, decision
//! `messung/ABSENKUNG-SCHRANKEN-ENTSCHEID.md`). This module ENFORCES that
//! bound on the emitter side: it counts the C statements the emitter
//! produces for exactly one primitive and refuses the primitive — by name,
//! with the offending fragment beside the refusal — when the count exceeds
//! the bound.
//!
//! ## Deliberately crate-free
//!
//! This module imports NOTHING from the crate (`std` only). It is not
//! registered in `lib.rs` and it touches no pass list: the wiring is owned
//! centrally and lands in exactly ONE place (see below). A module that
//! cannot name `Stmt`, `Absagen` or `Span` cannot drift into a second
//! reader of the tree — and it compiles unchanged the day central
//! registers it with a single `pub mod absenkung;`.
//!
//! ## The ONE hook point (specified, not applied)
//!
//! `emit.rs`, `fn anweisung` (`emit.rs:6654-7755`):
//!
//! ```text
//! fn anweisung(
//!     s: &Stmt,            // carries `.art: StmtArt` and `.span: Span`
//!     aus: &mut String,    // the shared output buffer
//!     u: &Namen,
//!     absagen: &mut Absagen,
//!     tiefe: usize,
//!     austritt: &Austritt,
//! ) {
//! ```
//!
//! Central adds two lines, one at the top and one at the bottom of that
//! function, and one thin wrapper next to it:
//!
//! ```text
//! // top of `anweisung`, before the `match &s.art`:
//! let marke = aus.len();
//! // bottom of `anweisung`, after the `match &s.art`:
//! absenkung_anwenden(s, &aus[marke..], absagen);
//!
//! // beside `anweisung`, in `emit.rs`:
//! fn absenkung_anwenden(s: &Stmt, fragment: &str, absagen: &mut Absagen) {
//!     let name = match &s.art {
//!         StmtArt::Let(_) => "Let",               // ... one arm per variant,
//!         // ... 17 arms total, names from `absenkung::PRIMITIVES`
//!     };
//!     if let Err(zu_viel) = crate::absenkung::check_primitive(name, fragment) {
//!         weigere(absagen, s.span, &zu_viel.to_string());  // -> `C001`
//!     }
//! }
//! ```
//!
//! The refusal reuses the existing emitter refusal `weigere`
//! (`emit.rs:2542`), so an over-budget primitive reads `C001 "no
//! lowering: …"` like every other named refusal of the emitter. No new
//! refusal code, no new pass, no new register.
//!
//! ## Counting rules (the same lexer as the measurement)
//!
//! One `;` in emitted C text is one statement, with three exclusions taken
//! from `messung/ABSENKUNG-MESSUNG.md` section 1, plus a fourth the
//! measurement never needed but the enforcement cannot do without:
//!
//! 1. `for (...; ...; ...)` header separators are not statements.
//! 2. Comment text (`//…`, `/*…*/`) is not statements.
//! 3. Refusal strings never reach the output buffer — nothing to exclude.
//! 4. `;` inside string and character literals (`"a;b"`, `';'`) is not a
//!    statement. The static measurement read format strings out of the
//!    emitter source, where no literal carries a `;`; the enforcement
//!    reads emitted text, where one someday could. Excluding them is the
//!    direction that refuses LESS, and it is booked here rather than
//!    hidden in the lexer.
//!
//! Nested body statements are booked on the body, not on the row: the
//! hook slices the buffer (`&aus[marke..]`), so each primitive is held
//! against exactly the scaffold it emits itself.
//!
//! The count runs to the end of the fragment in every case: a counter
//! that stops at the first statement past the bound answers whether at
//! least one primitive is large, not how large this one is.

/// The bound beside the constant in `Ziel.lean`: `proPrimitiv <= 18`.
pub const STATEMENTS_PER_PRIMITIVE: usize = 18;

/// The measured maximum that fills `proPrimitiv`: `17`, at `Schleife` /
/// `traverse over descendants of` (`emit.rs:8523-8560`).
pub const MEASURED_MAXIMUM: usize = 17;

/// The seventeen statement kinds: one variant of `StmtArt`
/// (`gabbro-syntax/src/ast.rs`), each with exactly one lowering arm in
/// `emit.rs::anweisung`. The order follows the enum; the hook maps each
/// arm to its row name from this list.
pub const PRIMITIVES: [&str; 17] = [
    "Let",
    "LetSonst",
    "Zuweisung",
    "Wenn",
    "Match",
    "Schleife",
    "Bricht",
    "Narrow",
    "Sperrt",
    "Observiert",
    "Leave",
    "Next",
    "Publish",
    "AwaitLoad",
    "Exchange",
    "Return",
    "Ruf",
];

/// How many characters of the offending fragment a refusal carries.
/// Enough to recognise the scaffold, never the whole output: a refusal
/// names the code, it does not reprint the file.
pub const EXCERPT_LEN: usize = 512;

/// A primitive that lowered to more C statements than the bound allows.
/// Renders as the `was` text of the existing emitter refusal `weigere`
/// (`emit.rs:2542`), so central needs no new refusal code.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OverBudget {
    /// Row name from [`PRIMITIVES`], e.g. `"Schleife"`.
    pub primitive: String,
    /// Statements counted in the emitted fragment.
    pub counted: usize,
    /// The bound that was exceeded ([`STATEMENTS_PER_PRIMITIVE`]).
    pub bound: usize,
    /// First [`EXCERPT_LEN`] characters of the emitted fragment.
    pub excerpt: String,
}

impl std::fmt::Display for OverBudget {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "primitive `{}` lowers to {} C statements, over the budget of {} per primitive; \
             measured maximum is {} (traverse over descendants of); fragment: {}",
            self.primitive,
            self.counted,
            self.bound,
            MEASURED_MAXIMUM,
            self.excerpt,
        )
    }
}

/// Count the C statements in emitted text: one `;` is one statement,
/// minus `for`-header separators, comments, and `;` inside string or
/// character literals. Runs to the end of the text in every case.
pub fn count_c_statements(c: &str) -> usize {
    let b = c.as_bytes();
    let n = b.len();
    let mut i = 0;
    let mut count = 0;
    while i < n {
        match b[i] {
            b'/' if i + 1 < n && b[i + 1] == b'/' => {
                // Line comment: to the newline, terminator included.
                while i < n && b[i] != b'\n' {
                    i += 1;
                }
            }
            b'/' if i + 1 < n && b[i + 1] == b'*' => {
                // Block comment: to the closer. Unterminated still ends
                // the count — the C was already broken before we looked.
                i += 2;
                while i + 1 < n && !(b[i] == b'*' && b[i + 1] == b'/') {
                    i += 1;
                }
                i = (i + 2).min(n);
            }
            b'"' | b'\'' => {
                i = nach_literal(b, i);
            }
            b';' => {
                count += 1;
                i += 1;
            }
            b'f'
                if ist_wort_an(b, i, b"for")
                    && skip_for_kopf(b, &mut i) =>
            {
                // Handled inside: `i` stands past the closing paren.
            }
            _ => {
                i += 1;
            }
        }
    }
    count
}

/// Hold one primitive against the budget: count the statements in the
/// fragment the emitter produced for exactly that primitive and refuse
/// — by name, with the fragment beside the refusal — when the count
/// exceeds [`STATEMENTS_PER_PRIMITIVE`]. Returns the count on success.
pub fn check_primitive(primitive: &str, emitted: &str) -> Result<usize, OverBudget> {
    let counted = count_c_statements(emitted);
    if counted <= STATEMENTS_PER_PRIMITIVE {
        Ok(counted)
    } else {
        let excerpt: String = emitted.chars().take(EXCERPT_LEN).collect();
        Err(OverBudget {
            primitive: primitive.to_string(),
            counted,
            bound: STATEMENTS_PER_PRIMITIVE,
            excerpt,
        })
    }
}

/// Skip a string or character literal starting at the quote in `b[i]`;
/// returns the index past the closing quote. Backslash escapes hold
/// inside both literal kinds; an unterminated literal runs to the end.
fn nach_literal(b: &[u8], start: usize) -> usize {
    let quote = b[start];
    let mut i = start + 1;
    while i < b.len() {
        if b[i] == b'\\' {
            i += 2;
            continue;
        }
        if b[i] == quote {
            return i + 1;
        }
        // A line comment never starts inside a literal, but a literal
        // never crosses a newline either — except a continued one.
        if b[i] == b'\n' && quote != b'\\' {
            // C allows a newline only in a line-continued literal; either
            // way the literal ends here for counting purposes.
            return i;
        }
        i += 1;
    }
    i
}

/// True when `wort` stands at `b[i..]` as a whole word: preceded and
/// followed by no identifier character.
fn ist_wort_an(b: &[u8], i: usize, wort: &[u8]) -> bool {
    if !b[i..].starts_with(wort) {
        return false;
    }
    let davor_ok = i == 0 || !ist_ident(b[i - 1]);
    let danach = i + wort.len();
    let danach_ok = danach >= b.len() || !ist_ident(b[danach]);
    davor_ok && danach_ok
}

fn ist_ident(c: u8) -> bool {
    c.is_ascii_alphanumeric() || c == b'_'
}

/// Skip a `for (...)` header starting at the `f` in `b[i]`; returns true
/// and leaves `i` past the closing paren when a header follows, false
/// with `i` one past `f` otherwise. Nested parens, comments, strings
/// and character literals inside the header are honoured, so a `;`
/// inside any of them is not mistaken for the header end.
fn skip_for_kopf(b: &[u8], i: &mut usize) -> bool {
    let mut k = *i + 3;
    while k < b.len() && (b[k] == b' ' || b[k] == b'\t' || b[k] == b'\n' || b[k] == b'\r') {
        k += 1;
    }
    if k >= b.len() || b[k] != b'(' {
        *i += 1;
        return false;
    }
    let mut tiefe: usize = 0;
    let mut j = k;
    while j < b.len() {
        match b[j] {
            b'(' => {
                tiefe += 1;
                j += 1;
            }
            b')' => {
                tiefe -= 1;
                j += 1;
                if tiefe == 0 {
                    *i = j;
                    return true;
                }
            }
            b'/' if j + 1 < b.len() && b[j + 1] == b'/' => {
                while j < b.len() && b[j] != b'\n' {
                    j += 1;
                }
            }
            b'/' if j + 1 < b.len() && b[j + 1] == b'*' => {
                j += 2;
                while j + 1 < b.len() && !(b[j] == b'*' && b[j + 1] == b'/') {
                    j += 1;
                }
                j = (j + 2).min(b.len());
            }
            b'"' | b'\'' => {
                j = nach_literal(b, j);
            }
            _ => {
                j += 1;
            }
        }
    }
    // Unterminated header: consume to the end rather than counting its
    // separators as statements.
    *i = j;
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn leer_zaehlt_null() {
        assert_eq!(count_c_statements(""), 0);
        assert_eq!(count_c_statements("   \n  "), 0);
    }

    #[test]
    fn einfache_anweisungen_zaehlen() {
        assert_eq!(count_c_statements("int x = 1;"), 1);
        assert_eq!(count_c_statements("int x = 1;\nx = 2;\nreturn x;\n"), 3);
    }

    #[test]
    fn for_kopf_trennzeichen_zaehlen_nicht() {
        // The two header separators are excluded; the body counts.
        assert_eq!(count_c_statements("for (i = 0; i < n; i++) { x = 1; }"), 1);
        assert_eq!(count_c_statements("for (;;) { break; }"), 1);
    }

    #[test]
    fn for_als_wortteil_zaehlt_normal() {
        // `before` holds no loop: its `;` is a statement.
        assert_eq!(count_c_statements("before = 1;"), 1);
        assert_eq!(count_c_statements("int format = 1;"), 1);
    }

    #[test]
    fn for_kopf_mit_klammer_zaehlt_nicht() {
        assert_eq!(count_c_statements("for (i = 0; i < (n); i++) { x = 1; }"), 1);
    }

    #[test]
    fn kommentare_zaehlen_nicht() {
        assert_eq!(count_c_statements("// x = 1;\nint y = 2;"), 1);
        assert_eq!(count_c_statements("/* x = 1; y = 2; */ int z = 3;"), 1);
        assert_eq!(count_c_statements("int a = 1; /* ;;; */ int b = 2;"), 2);
    }

    #[test]
    fn literale_zaehlen_nicht() {
        assert_eq!(count_c_statements("char *s = \"a;b\";"), 1);
        assert_eq!(count_c_statements("char c = ';';"), 1);
        assert_eq!(count_c_statements("char *s = \"a\\\";b\";"), 1);
    }

    #[test]
    fn gemessenes_maximum_passt_noch() {
        // 17 counted is held; the bound is the maximum plus one headroom.
        assert_eq!(check_primitive("Schleife", &"x = 1;\n".repeat(17)), Ok(17));
        assert!(MEASURED_MAXIMUM < STATEMENTS_PER_PRIMITIVE);
        assert_eq!(STATEMENTS_PER_PRIMITIVE - MEASURED_MAXIMUM, 1);
    }

    #[test]
    fn schranke_ist_einschliessend() {
        // Exactly 18 passes; 19 is refused by name, with count and bound.
        assert_eq!(check_primitive("Exchange", &"x = 1;\n".repeat(18)), Ok(18));
        let err = check_primitive("Exchange", &"x = 1;\n".repeat(19)).unwrap_err();
        assert_eq!(err.primitive, "Exchange");
        assert_eq!(err.counted, 19);
        assert_eq!(err.bound, STATEMENTS_PER_PRIMITIVE);
        let text = err.to_string();
        assert!(text.contains("Exchange"), "refusal names the primitive");
        assert!(text.contains("19"), "refusal names the count");
        assert!(text.contains("18"), "refusal names the bound");
    }

    #[test]
    fn absage_traegt_fragmentausschnitt() {
        let lang = "x = 1;\n".repeat(30);
        let err = check_primitive("Schleife", &lang).unwrap_err();
        assert!(err.excerpt.chars().count() <= EXCERPT_LEN);
        assert!(err.excerpt.contains("x = 1;"), "excerpt shows the code");
    }

    #[test]
    fn siebzehn_primitive_wie_stmtart() {
        // One row per `StmtArt` variant; the hook maps each lowering arm
        // to exactly one of these names.
        assert_eq!(PRIMITIVES.len(), 17);
        for name in [
            "Let",
            "LetSonst",
            "Zuweisung",
            "Wenn",
            "Match",
            "Schleife",
            "Bricht",
            "Narrow",
            "Sperrt",
            "Observiert",
            "Leave",
            "Next",
            "Publish",
            "AwaitLoad",
            "Exchange",
            "Return",
            "Ruf",
        ] {
            assert!(PRIMITIVES.contains(&name), "row for `{name}` is booked");
        }
    }

    #[test]
    fn zaehlung_bricht_nie_ab() {
        // Statements past the bound are still counted: the maximum is
        // taken after the last statement, not at the first excess.
        let frag = "x = 1;\n".repeat(25);
        assert_eq!(count_c_statements(&frag), 25);
        assert_eq!(check_primitive("Schleife", &frag).unwrap_err().counted, 25);
    }
}
