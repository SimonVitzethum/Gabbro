//! Sites in the source. Byte offsets, and a line index that translates them for a human.
//! A refusal without a site is an opinion.

/// A half-open byte range `[von, bis)` in a source file.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    pub von: u32,
    pub bis: u32,
}

impl Span {
    pub const fn neu(von: u32, bis: u32) -> Span {
        Span { von, bis }
    }

    /// The range enclosing both.
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

/// Line starts of a source, computed once.
#[derive(Debug, Clone)]
pub struct Zeilenindex {
    anfaenge: Vec<u32>,
    laenge: u32,
}

/// A site as a human reads it: 1-based line, 1-based column in *characters*.
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
        // Column in characters, not bytes -- the lexis allows umlauts in identifiers.
        let spalte = quelle[anfang..versatz as usize].chars().count() as u32 + 1;
        Stelle {
            zeile: zeile as u32 + 1,
            spalte,
        }
    }

    /// The text of the line (without the line ending) the offset belongs to.
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
