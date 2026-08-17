//! The lexer -- `SYNTAX.md`, section "Lexik".
//!
//! No floating point, `--` to end of line as a comment, numbers with `_`, umlauts in
//! identifiers. Strings know **no escaping**: `char = any character except quote and newline`.
//! That is not an omission but the grammar -- an escape would be a new word.

use crate::diag::{Absage, Absagen};
use crate::kw::Kw;
use crate::span::Span;

/// A punctuation mark or operator.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Z {
    Kolon2,
    Kolon,
    Semi,
    Komma,
    Punkt,
    Bereich,
    BereichEx,
    Pfeil,
    Doppelpfeil,
    Gleich,
    GleichGleich,
    Ungleich,
    Kleiner,
    KleinerGleich,
    Groesser,
    GroesserGleich,
    SchiebLinks,
    SchiebRechts,
    Plus,
    PlusGleich,
    Minus,
    MinusGleich,
    Stern,
    Schraeg,
    Prozent,
    Und,
    UndUnd,
    UndGleich,
    Strich,
    StrichStrich,
    StrichGleich,
    Dach,
    Bang,
    At,
    RundAuf,
    RundZu,
    EckAuf,
    EckZu,
    GeschweiftAuf,
    GeschweiftZu,
}

impl Z {
    pub const fn text(self) -> &'static str {
        match self {
            Z::Kolon2 => "::",
            Z::Kolon => ":",
            Z::Semi => ";",
            Z::Komma => ",",
            Z::Punkt => ".",
            Z::Bereich => "..",
            Z::BereichEx => "..<",
            Z::Pfeil => "->",
            Z::Doppelpfeil => "=>",
            Z::Gleich => "=",
            Z::GleichGleich => "==",
            Z::Ungleich => "!=",
            Z::Kleiner => "<",
            Z::KleinerGleich => "<=",
            Z::Groesser => ">",
            Z::GroesserGleich => ">=",
            Z::SchiebLinks => "<<",
            Z::SchiebRechts => ">>",
            Z::Plus => "+",
            Z::PlusGleich => "+=",
            Z::Minus => "-",
            Z::MinusGleich => "-=",
            Z::Stern => "*",
            Z::Schraeg => "/",
            Z::Prozent => "%",
            Z::Und => "&",
            Z::UndUnd => "&&",
            Z::UndGleich => "&=",
            Z::Strich => "|",
            Z::StrichStrich => "||",
            Z::StrichGleich => "|=",
            Z::Dach => "^",
            Z::Bang => "!",
            Z::At => "@",
            Z::RundAuf => "(",
            Z::RundZu => ")",
            Z::EckAuf => "[",
            Z::EckZu => "]",
            Z::GeschweiftAuf => "{",
            Z::GeschweiftZu => "}",
        }
    }
}

/// What a token is.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Art {
    /// A free identifier.
    Ident,
    /// A word of the closed vocabulary.
    Wort(Kw),
    /// An integer. There is no floating point in the core.
    Zahl(u128),
    /// A string, without the quotes.
    Text,
    Zeichen(Z),
    Ende,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Token {
    pub art: Art,
    pub span: Span,
}

impl Token {
    /// The token's text in the source -- for `Text` without the quotes.
    pub fn text<'a>(&self, quelle: &'a str) -> &'a str {
        let (von, bis) = match self.art {
            Art::Text => (self.span.von as usize + 1, self.span.bis as usize - 1),
            _ => (self.span.von as usize, self.span.bis as usize),
        };
        quelle.get(von..bis).unwrap_or("")
    }

    /// How the token is named in a refusal.
    pub fn benennung(&self, quelle: &str) -> String {
        match self.art {
            Art::Ident => format!("Bezeichner `{}`", self.text(quelle)),
            Art::Wort(k) => format!("`{}`", k.text()),
            Art::Zahl(_) => format!("Zahl `{}`", self.text(quelle)),
            Art::Text => "Zeichenkette".to_string(),
            Art::Zeichen(z) => format!("`{}`", z.text()),
            Art::Ende => "Dateiende".to_string(),
        }
    }
}

fn ist_buchstabe(c: char) -> bool {
    c.is_ascii_alphabetic() || matches!(c, 'ä' | 'ö' | 'ü' | 'Ä' | 'Ö' | 'Ü' | 'ß')
}

fn ist_folgezeichen(c: char) -> bool {
    ist_buchstabe(c) || c.is_ascii_digit() || c == '_'
}

/// Splits the source. Refusals accumulate; the stream does not abort, so that one run shows
/// more than a single finding.
pub fn zerlege(quelle: &str, absagen: &mut Absagen) -> Vec<Token> {
    let b = quelle.as_bytes();
    let mut i = 0usize;
    let mut out = Vec::new();

    let schiebe = |out: &mut Vec<Token>, art: Art, von: usize, bis: usize| {
        out.push(Token {
            art,
            span: Span::neu(von as u32, bis as u32),
        });
    };

    while i < b.len() {
        let c = b[i];

        // Whitespace
        if c == b' ' || c == b'\t' || c == b'\r' || c == b'\n' {
            i += 1;
            continue;
        }

        // Comment `--` to end of line. Comes BEFORE any interpretation of `-`.
        if c == b'-' && i + 1 < b.len() && b[i + 1] == b'-' {
            while i < b.len() && b[i] != b'\n' {
                i += 1;
            }
            continue;
        }

        // String
        if c == b'"' {
            let von = i;
            i += 1;
            let mut geschlossen = false;
            while i < b.len() {
                if b[i] == b'"' {
                    i += 1;
                    geschlossen = true;
                    break;
                }
                if b[i] == b'\n' {
                    break;
                }
                i += 1;
            }
            if !geschlossen {
                absagen.schiebe(
                    Absage::fehler(
                        "L001",
                        Span::neu(von as u32, i as u32),
                        "Zeichenkette ohne schliessendes Anfuehrungszeichen",
                    )
                    .mit_notiz(
                        "`char = jedes Zeichen ausser quote und newline` -- eine Zeichenkette \
                         endet auf ihrer Zeile",
                    ),
                );
            }
            schiebe(&mut out, Art::Text, von, i);
            continue;
        }

        // Number
        if c.is_ascii_digit() {
            let von = i;
            let (basis, ziffernanfang) = if c == b'0' && i + 1 < b.len() && b[i + 1] == b'x' {
                i += 2;
                (16u32, i)
            } else if c == b'0' && i + 1 < b.len() && b[i + 1] == b'b' {
                i += 2;
                (2u32, i)
            } else {
                (10u32, i)
            };
            if c == b'0' && i + 1 < b.len() && (b[i + 1] == b'X' || b[i + 1] == b'B') {
                absagen.schiebe(
                    Absage::fehler(
                        "L004",
                        Span::neu(von as u32, von as u32 + 2),
                        "Grossbuchstabe im Zahlenpraefix",
                    )
                    .mit_notiz("the lexer knows `0x` and `0b`, not `0X`/`0B`"),
                );
            }
            let gueltig = |ch: u8, basis: u32| -> bool {
                match basis {
                    16 => ch.is_ascii_hexdigit(),
                    2 => ch == b'0' || ch == b'1',
                    _ => ch.is_ascii_digit(),
                }
            };
            let mut ziffern = String::new();
            while i < b.len() && (gueltig(b[i], basis) || b[i] == b'_') {
                if b[i] != b'_' {
                    ziffern.push(b[i] as char);
                }
                i += 1;
            }
            if ziffern.is_empty() {
                absagen.schiebe(Absage::fehler(
                    "L002",
                    Span::neu(von as u32, i as u32),
                    "number with no digits after the prefix",
                ));
                schiebe(&mut out, Art::Zahl(0), von, i);
                continue;
            }
            // A digit run adjoining a number is a trap: `0b12` would otherwise be `0b1`
            // followed by `2`. Refuse, never interpret.
            if i < b.len() && (ist_buchstabe(b[i] as char) || b[i].is_ascii_digit()) {
                let ende = {
                    let mut j = i;
                    while j < b.len() && ist_folgezeichen(b[j] as char) {
                        j += 1;
                    }
                    j
                };
                absagen.schiebe(
                    Absage::fehler(
                        "L003",
                        Span::neu(von as u32, ende as u32),
                        format!(
                            "digit or letter `{}` does not belong in this number",
                            &quelle[i..ende]
                        ),
                    )
                    .mit_notiz(
                        "Zahlen enden vor dem naechsten Buchstaben; ein Suffix gibt es nicht",
                    ),
                );
                i = ende;
                schiebe(&mut out, Art::Zahl(0), von, i);
                continue;
            }
            let ziffernanfang = ziffernanfang.min(i);
            let _ = ziffernanfang;
            match u128::from_str_radix(&ziffern, basis) {
                Ok(v) => schiebe(&mut out, Art::Zahl(v), von, i),
                Err(_) => {
                    absagen.schiebe(
                        Absage::fehler(
                            "L005",
                            Span::neu(von as u32, i as u32),
                            "number fits no integer type of the language",
                        )
                        .mit_notiz("the largest type is `u64`"),
                    );
                    schiebe(&mut out, Art::Zahl(0), von, i);
                }
            }
            continue;
        }

        // Identifier or word
        let ch = quelle[i..].chars().next().unwrap_or('\0');
        if ist_buchstabe(ch) || ch == '_' {
            let von = i;
            i += ch.len_utf8();
            while i < b.len() {
                let c2 = quelle[i..].chars().next().unwrap_or('\0');
                if ist_folgezeichen(c2) {
                    i += c2.len_utf8();
                } else {
                    break;
                }
            }
            let s = &quelle[von..i];
            let art = match Kw::suche(s) {
                Some(k) => Art::Wort(k),
                None => Art::Ident,
            };
            schiebe(&mut out, art, von, i);
            continue;
        }

        // Punctuation -- longest match first.
        let rest = &quelle[i..];
        const TABELLE: &[(&str, Z)] = &[
            ("..<", Z::BereichEx),
            ("::", Z::Kolon2),
            ("..", Z::Bereich),
            ("->", Z::Pfeil),
            ("=>", Z::Doppelpfeil),
            ("==", Z::GleichGleich),
            ("!=", Z::Ungleich),
            ("<=", Z::KleinerGleich),
            (">=", Z::GroesserGleich),
            ("<<", Z::SchiebLinks),
            (">>", Z::SchiebRechts),
            ("+=", Z::PlusGleich),
            ("-=", Z::MinusGleich),
            ("&&", Z::UndUnd),
            ("&=", Z::UndGleich),
            ("||", Z::StrichStrich),
            ("|=", Z::StrichGleich),
            (":", Z::Kolon),
            (";", Z::Semi),
            (",", Z::Komma),
            (".", Z::Punkt),
            ("=", Z::Gleich),
            ("<", Z::Kleiner),
            (">", Z::Groesser),
            ("+", Z::Plus),
            ("-", Z::Minus),
            ("*", Z::Stern),
            ("/", Z::Schraeg),
            ("%", Z::Prozent),
            ("&", Z::Und),
            ("|", Z::Strich),
            ("^", Z::Dach),
            ("!", Z::Bang),
            ("@", Z::At),
            ("(", Z::RundAuf),
            (")", Z::RundZu),
            ("[", Z::EckAuf),
            ("]", Z::EckZu),
            ("{", Z::GeschweiftAuf),
            ("}", Z::GeschweiftZu),
        ];
        let mut getroffen = false;
        for (t, z) in TABELLE {
            if rest.starts_with(t) {
                schiebe(&mut out, Art::Zeichen(*z), i, i + t.len());
                i += t.len();
                getroffen = true;
                break;
            }
        }
        if getroffen {
            continue;
        }

        let breite = ch.len_utf8();
        absagen.schiebe(Absage::fehler(
            "L006",
            Span::neu(i as u32, (i + breite) as u32),
            format!("character `{ch}` belongs to no form of the language"),
        ));
        i += breite;
    }

    schiebe(&mut out, Art::Ende, b.len(), b.len());
    out
}
