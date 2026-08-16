//! **Der Korpus** -- die Gabbro-Bloecke aus den Markdown-Dateien des Ordners.
//!
//! Tor P2 lautet: *„100 % der Fragmente parsen; drei Gift-Fragmente scheitern mit benannter
//! Absage."* Die Fragmente liegen nicht als `.gab`-Dateien vor, sondern in ```gabbro-Bloecken;
//! also liest der Uebersetzer sie **an ihrer Stelle**.
//!
//! Die Zeilennummern bleiben die der Markdown-Datei: jeder Block wird mit so vielen Zeilenenden
//! aufgefuellt, wie vor ihm stehen. Eine Fundstelle, die man nicht anspringen kann, ist eine
//! Fundstelle in einem Bericht statt in einer Datei.

use gabbro_syntax::diag::Stufe;

pub struct Block {
    /// 1-basierte Zeile der ersten Codezeile in der Markdown-Datei.
    pub erste_zeile: usize,
    pub zeilen: usize,
    /// Der Blockinhalt, vorne mit Zeilenenden aufgefuellt.
    pub text: String,
}

/// Schneidet alle ```gabbro-Bloecke heraus.
pub fn schneide(md: &str) -> Vec<Block> {
    let mut out = Vec::new();
    let mut in_block = false;
    let mut anfang = 0usize;
    let mut inhalt = String::new();
    let mut zeilen = 0usize;
    for (nr, zeile) in md.lines().enumerate() {
        let nr = nr + 1;
        if !in_block {
            if zeile.trim_start().starts_with("```gabbro") {
                in_block = true;
                anfang = nr + 1;
                inhalt = "\n".repeat(nr);
                zeilen = 0;
            }
            continue;
        }
        if zeile.trim_start().starts_with("```") {
            in_block = false;
            out.push(Block {
                erste_zeile: anfang,
                zeilen,
                text: std::mem::take(&mut inhalt),
            });
            continue;
        }
        inhalt.push_str(zeile);
        inhalt.push('\n');
        zeilen += 1;
    }
    out
}

/// Faengt der Block mit einem Item an?
///
/// **Diese Unterscheidung entscheidet, was die Messung ueberhaupt bedeutet.** Die Fragmente
/// sind vollstaendige Uebersetzungseinheiten und zaehlen gegen Tor P2. Die Beispiele in
/// `SPRACHE.md` sind ueberwiegend **Ausschnitte** -- eine Anweisung, eine Klausel, ein Typ --
/// und ein Parser, der sie als Programm liest, meldet einen Fehler, den es nicht gibt.
/// Sie zusammenzuzaehlen waere derselbe Fehler wie eine Kennzahl ohne Nenner.
pub fn ist_uebersetzungseinheit(text: &str) -> bool {
    // **Ein Block mit `…` ist per Definition keiner.** Das Zeichen gehoert in keine Form der
    // Sprache (`L006`) -- es steht fuer *„hier waere noch mehr"*. Ein solcher Block als
    // Uebersetzungseinheit zu zaehlen heisst, eine Auslassung als Fehler zu melden, und das
    // ist derselbe Fehler wie eine Kennzahl ohne Nenner, nur andersherum.
    //
    // Gefunden 2026-08-16, als SYNTAX.md zum ersten Mal gegen sein eigenes Tor lief.
    //
    // **Und die erste Fassung war zu grob und ist sofort aufgeflogen:** sie suchte `…` im
    // ROHTEXT und warf damit fuenf der sechs Fragmente heraus, weil dort `…` in
    // KOMMENTAREN steht. Der Lexer trennt das -- er meldet `L006` nur fuer Zeichen im Code.
    // *Eine Vergroeberung, die in die falsche Richtung ging (W9): sie haette das Tor P2 von
    // 6 auf 1 Einheit geschrumpft und dabei wie ein Erfolg ausgesehen.*
    let mut verworfen = gabbro_syntax::Absagen::neu("<probe>");
    let tokens = gabbro_syntax::lex::zerlege(text, &mut verworfen);
    if !verworfen.leer() {
        return false; // der Lexer stolpert -- das ist kein Programm, sondern eine Skizze
    }
    let Some(erstes) = tokens.first() else {
        return false;
    };
    match erstes.art {
        gabbro_syntax::lex::Art::Wort(k) => gabbro_syntax::parse::faengt_item_an(k),
        _ => false,
    }
}

/// Das Ergebnis eines Blocks -- Codes statt Text, damit eine Messung vergleichbar bleibt.
pub struct Befund {
    pub bericht: crate::Bericht,
    pub erste_zeile: usize,
    pub zeilen: usize,
    /// Vollstaendige Uebersetzungseinheit (zaehlt gegen Tor P2) oder Ausschnitt.
    pub vollstaendig: bool,
    pub fehler: Vec<(&'static str, u32)>,
    pub hinweise: Vec<(&'static str, u32)>,
    /// Der gerenderte Text, fuer die Kommandozeile.
    pub text: String,
}

impl Befund {
    pub fn sauber(&self) -> bool {
        self.fehler.is_empty()
    }
}

/// Misst eine Markdown-Datei: je Block Fehler- und Hinweiscodes mit Zeile.
pub fn messe(datei: &str, md: &str) -> Vec<Befund> {
    schneide(md)
        .into_iter()
        .map(|b| {
            let name = format!("{datei}:{}", b.erste_zeile);
            let (baum, mut absagen) = gabbro_syntax::lies(&name, &b.text);
            let bericht = crate::pruefe(&baum, &mut absagen);
            let zeilen_index = gabbro_syntax::span::Zeilenindex::neu(&b.text);
            let mut fehler = Vec::new();
            let mut hinweise = Vec::new();
            for a in &absagen.absagen {
                let z = zeilen_index.stelle(&b.text, a.span.von).zeile;
                match a.stufe {
                    Stufe::Fehler => fehler.push((a.code, z)),
                    Stufe::Hinweis => hinweise.push((a.code, z)),
                }
            }
            Befund {
                bericht,
                erste_zeile: b.erste_zeile,
                zeilen: b.zeilen,
                vollstaendig: ist_uebersetzungseinheit(&b.text),
                text: absagen.zeige(&b.text),
                fehler,
                hinweise,
            }
        })
        .collect()
}
