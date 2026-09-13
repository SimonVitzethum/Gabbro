//! Statement certificates from Rust (T1 transfer printer, lane 153).
//!
//! The Lean side holds statement/block certificates with decidable validity
//! (`ZeugnisStmt.lean`: `CertStmt`/`CertSeq`/`CertEnd`, `ZeugnisStmt2.lean`:
//! `CertStmt2`/`CertSeq2`/`CertEnd2`). The Rust side printed only expression
//! certificates (`certemit.rs`). This module prints, per function body, a Lean
//! term of the `CertEnd`/`CertEnd2` shape for the forms both Lean files cover,
//! and REFUSES by name every body with a form outside them.
//!
//! ## Fragment boundary (measured, not hoped)
//!
//! Printable today: `return;`, `return <int-expr>;`, `let x : <range> = ...;`
//! (`CertEnd.bind`), direct table writes with literal indices, `if` with a
//! printable condition and falling branches. Everything else is a named
//! refusal, never a truncation:
//!
//! * `CS001` statement form with no `CertStmt`/`CertStmt2` form
//! * `CS002` expression with no `CertExpr`/cut-row form
//! * `CS003` index or variable with no recomputable range
//! * `CS004` call: `RufPasst` travels as proof (R-3), plain data cannot carry it
//! * `CS005` unresolvable name, count, rank or range for the claim
//!
//! ## Conventions of the printed term
//!
//! Table, field and function names print as written in surface syntax; the
//! contract prints as `V_<fn>`; every resource list prints as `[]` (the Lean
//! side recomputes validity over it, so a wrong flow fails `decide` loudly).
//! The printed term is linked to the checked body by construction of this
//! printer only; term identity (`print (elab x) = x`) is proved nowhere yet
//! (the `ZeugnisStmt2.lean` CUTS booking).

/// A named refusal: the code plus the exact surface form that caused it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Refusal {
    /// One of `CS001`..=`CS005` (see the module docs).
    pub code: &'static str,
    /// Names the function and the form, never truncated.
    pub grund: String,
}

/// The per-body print: a Lean term or a named refusal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BodyCert {
    /// A Lean `CertEnd2` term (as text) for this body.
    Gedruckt { lean: String },
    /// The body has a form outside the covered fragment.
    Abgewiesen { weigerung: Refusal },
}

/// Print the statement certificate for one function body (stub).
pub fn zeige_rumpf(funktion: &str) -> BodyCert {
    BodyCert::Abgewiesen {
        weigerung: Refusal {
            code: "CS001",
            grund: format!("function {funktion} not yet printed"),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stub_refuses_by_name() {
        let BodyCert::Abgewiesen { weigerung } = zeige_rumpf("f") else {
            panic!("stub must refuse");
        };
        assert_eq!(weigerung.code, "CS001");
        assert!(weigerung.grund.contains('f'));
    }
}
