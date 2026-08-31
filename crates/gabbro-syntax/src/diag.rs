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
}

impl Absage {
    pub fn fehler(code: &'static str, span: Span, text: impl Into<String>) -> Absage {
        Absage {
            stufe: Stufe::Fehler,
            code,
            text: text.into(),
            span,
            notizen: Vec::new(),
        }
    }

    pub fn hinweis(code: &'static str, span: Span, text: impl Into<String>) -> Absage {
        Absage {
            stufe: Stufe::Hinweis,
            code,
            text: text.into(),
            span,
            notizen: Vec::new(),
        }
    }

    pub fn mit_notiz(mut self, n: impl Into<String>) -> Absage {
        self.notizen.push(n.into());
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
        }
        out
    }
}
