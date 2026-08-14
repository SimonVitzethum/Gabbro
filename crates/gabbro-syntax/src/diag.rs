//! Absagen. **Abweisen, nie deuten** (`SPRACHE.md`, Regel 3): jede Absage traegt einen
//! stabilen Code, eine Fundstelle und einen Grund im Klartext. Der Code ist das, was ein
//! Pruefgeruest zaehlt; der Text ist fuer den Menschen daneben.

use crate::span::{Span, Zeilenindex};

/// Wie schwer eine Absage wiegt.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Stufe {
    /// Bricht die Uebersetzung.
    Fehler,
    /// Bricht nicht, ist aber ein Befund.
    Hinweis,
}

/// Eine einzelne Absage.
#[derive(Debug, Clone)]
pub struct Absage {
    pub stufe: Stufe,
    /// Stabiler Code, z. B. `L003` (Lexik), `P017` (Parser), `V002` (Pruefpass).
    pub code: &'static str,
    pub text: String,
    pub span: Span,
    /// Zusaetzliche Zeilen unter der Fundstelle -- Regel, Vorbild, Gegenvorschlag.
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

/// Alle Absagen eines Laufs, samt der Quelle, gegen die sie gemessen wurden.
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

    /// Fuer den Menschen: Fundstelle, Zeile, Zeiger, Grund.
    pub fn zeige(&self, quelle: &str) -> String {
        let index = Zeilenindex::neu(quelle);
        let mut out = String::new();
        for a in &self.absagen {
            let stelle = index.stelle(quelle, a.span.von);
            let wort = match a.stufe {
                Stufe::Fehler => "Fehler",
                Stufe::Hinweis => "Hinweis",
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
