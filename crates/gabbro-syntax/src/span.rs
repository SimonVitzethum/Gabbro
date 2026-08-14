//! Stellen in der Quelle. Byteversaetze, und ein Zeilenindex, der sie fuer den Menschen
//! uebersetzt. Eine Absage ohne Fundstelle ist eine Meinung.

/// Ein halboffener Byteabschnitt `[von, bis)` in einer Quelldatei.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    pub von: u32,
    pub bis: u32,
}

impl Span {
    pub const fn neu(von: u32, bis: u32) -> Span {
        Span { von, bis }
    }

    /// Der Abschnitt, der beide umschliesst.
    pub fn bis_zu(self, andere: Span) -> Span {
        Span {
            von: self.von.min(andere.von),
            bis: self.bis.max(andere.bis),
        }
    }

    pub fn leer(self) -> bool {
        self.von >= self.bis
    }
}

/// Zeilenanfaenge einer Quelle, einmal berechnet.
#[derive(Debug, Clone)]
pub struct Zeilenindex {
    anfaenge: Vec<u32>,
    laenge: u32,
}

/// Eine Stelle, wie ein Mensch sie liest: 1-basierte Zeile, 1-basierte Spalte in *Zeichen*.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Stelle {
    pub zeile: u32,
    pub spalte: u32,
}

impl Zeilenindex {
    pub fn neu(quelle: &str) -> Zeilenindex {
        let mut anfaenge = vec![0u32];
        for (i, b) in quelle.bytes().enumerate() {
            if b == b'\n' {
                anfaenge.push(i as u32 + 1);
            }
        }
        Zeilenindex {
            anfaenge,
            laenge: quelle.len() as u32,
        }
    }

    pub fn stelle(&self, quelle: &str, versatz: u32) -> Stelle {
        let versatz = versatz.min(self.laenge);
        let zeile = match self.anfaenge.binary_search(&versatz) {
            Ok(i) => i,
            Err(i) => i - 1,
        };
        let anfang = self.anfaenge[zeile] as usize;
        // Spalte in Zeichen, nicht in Bytes -- die Lexik laesst Umlaute in Bezeichnern zu.
        let spalte = quelle[anfang..versatz as usize].chars().count() as u32 + 1;
        Stelle {
            zeile: zeile as u32 + 1,
            spalte,
        }
    }

    /// Der Text der Zeile (ohne Zeilenende), zu der der Versatz gehoert.
    pub fn zeilentext<'a>(&self, quelle: &'a str, versatz: u32) -> &'a str {
        let versatz = versatz.min(self.laenge) as usize;
        let zeile = match self.anfaenge.binary_search(&(versatz as u32)) {
            Ok(i) => i,
            Err(i) => i - 1,
        };
        let anfang = self.anfaenge[zeile] as usize;
        let ende = self
            .anfaenge
            .get(zeile + 1)
            .map(|e| *e as usize)
            .unwrap_or(quelle.len());
        quelle[anfang..ende].trim_end_matches(['\n', '\r'])
    }
}
