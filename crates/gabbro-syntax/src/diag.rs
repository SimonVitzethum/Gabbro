//! Refusals. **Refuse, never interpret** (`SPRACHE.md`, rule 3): every refusal carries a
//! stable code, a site and a reason in plain words. The code is what a test harness counts;
//! the text is for the human beside it.

use crate::span::{Span, Zeilenindex};

/// How heavily a refusal weighs.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Stufe {
    /// Breaks compilation.
    Fehler,
    /// Does not break, but is a finding.
    Hinweis,
}

/// A single refusal.
#[derive(Debug, Clone)]
pub struct Absage {
    pub stufe: Stufe,
    /// Stable code, e.g. `L003` (lexis), `P017` (parser), `V002` (checking pass).
    pub code: &'static str,
    pub text: String,
    pub span: Span,
    /// Extra lines under the site -- rule, example, counter-proposal.
    pub notizen: Vec<String>,
    /// A machine-applicable repair, lane 187 (lever 4 of `dokumente/PLAN-EINFACHHEIT.md`).
    ///
    /// `Some` only where the correct edit is UNIQUE and mechanically determined -- the
    /// missing entry the hull names, the bound below the computed one, the expected token.
    /// Never a fix that weakens a contract, deletes a check, or silences a refusal: where
    /// two repairs are defensible, or the content is unknown, the field stays `None` and
    /// the human reads the notes. Adding the field changes no verdict -- passes neither
    /// read it nor branch on it.
    pub fix: Option<Fix>,
}

/// A machine-applicable edit: replace the byte range the span names in the checked
/// source with `replacement`. An empty span inserts, an empty `replacement` deletes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Fix {
    pub span: Span,
    pub replacement: String,
}

impl Fix {
    /// Replace `span` with `replacement`.
    pub fn new(span: Span, replacement: impl Into<String>) -> Fix {
        Fix { span, replacement: replacement.into() }
    }

    /// Insert `replacement` at byte offset `pos` (an empty span).
    pub fn insert(pos: u32, replacement: impl Into<String>) -> Fix {
        Fix { span: Span::neu(pos, pos), replacement: replacement.into() }
    }

    /// Delete `span` (an empty replacement).
    pub fn delete(span: Span) -> Fix {
        Fix { span, replacement: String::new() }
    }
}

impl Absage {
    pub fn fehler(code: &'static str, span: Span, text: impl Into<String>) -> Absage {
        Absage {
            stufe: Stufe::Fehler,
            code,
            text: text.into(),
            span,
            notizen: Vec::new(),
            fix: None,
        }
    }

    pub fn hinweis(code: &'static str, span: Span, text: impl Into<String>) -> Absage {
        Absage {
            stufe: Stufe::Hinweis,
            code,
            text: text.into(),
            span,
            notizen: Vec::new(),
            fix: None,
        }
    }

    pub fn mit_notiz(mut self, n: impl Into<String>) -> Absage {
        self.notizen.push(n.into());
        self
    }

    /// Attach the machine-applicable repair. Chainable like `mit_notiz`, set once: a
    /// second call keeps the first fix, so a site that qualifies twice does not silently
    /// re-point the edit.
    pub fn mit_fix(mut self, fix: Fix) -> Absage {
        if self.fix.is_none() {
            self.fix = Some(fix);
        }
        self
    }
}

/// All refusals of a run, together with the source they were measured against.
#[derive(Debug, Clone)]
pub struct Absagen {
    pub datei: String,
    pub absagen: Vec<Absage>,
}

impl Absagen {
    pub fn neu(datei: impl Into<String>) -> Absagen {
        Absagen {
            datei: datei.into(),
            absagen: Vec::new(),
        }
    }

    pub fn schiebe(&mut self, a: Absage) {
        self.absagen.push(a);
    }

    pub fn fehler_zahl(&self) -> usize {
        self.absagen
            .iter()
            .filter(|a| a.stufe == Stufe::Fehler)
            .count()
    }

    pub fn leer(&self) -> bool {
        self.absagen.is_empty()
    }

    /// For the human: site, line, caret, reason.
    pub fn zeige(&self, quelle: &str) -> String {
        let index = Zeilenindex::neu(quelle);
        let mut out = String::new();
        for a in &self.absagen {
            let stelle = index.stelle(quelle, a.span.von);
            let wort = match a.stufe {
                Stufe::Fehler => "error",
                Stufe::Hinweis => "hint",
            };
            out.push_str(&format!(
                "{}: [{}] {}:{}:{}: {}\n",
                wort, a.code, self.datei, stelle.zeile, stelle.spalte, a.text
            ));
            let zeile = index.zeilentext(quelle, a.span.von);
            let nr = format!("{:>5}", stelle.zeile);
            out.push_str(&format!("{} | {}\n", nr, zeile));
            let breite = (a.span.bis.saturating_sub(a.span.von)).max(1) as usize;
            let einzug = " ".repeat(stelle.spalte.saturating_sub(1) as usize);
            out.push_str(&format!(
                "{} | {}{}\n",
                " ".repeat(5),
                einzug,
                "^".repeat(breite.min(zeile.chars().count().max(1)))
            ));
            for n in &a.notizen {
                out.push_str(&format!("{} = {}\n", " ".repeat(5), n));
            }
            // Lane 187: the machine-applicable repair, if the refusing rule named one.
            // Rendered as `fix: <start>..<end> -> <replacement>`, byte offsets into the
            // checked source; `gabbro pruefe --fix` applies exactly these edits.
            if let Some(f) = &a.fix {
                out.push_str(&format!(
                    "{} fix: {}..{} -> {}\n",
                    " ".repeat(5),
                    f.span.von,
                    f.span.bis,
                    f.replacement
                ));
            }
        }
        out
    }
}
