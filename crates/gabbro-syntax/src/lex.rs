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
    // PLAN-BITS section 4 (lane 88): the overflow operators. Each rides at the
    // precedence of its base operator; the lexer only cuts them.
    SchiebLinksProzent,
    Plus,
    PlusGleich,
    // Wrapping `+%`, saturating `+|`.
    PlusProzent,
    PlusStrich,
    Minus,
    MinusGleich,
    // Wrapping `-%`.
    MinusProzent,
    Stern,
    // Wrapping `*%`.
    SternProzent,
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
    Tilde,
    At,
    /// `#` -- the library call separator in `@library#function` (lane E1).
    /// A punctuation mark like `@`, not a vocabulary word: no `Kw` entry.
    Hash,
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
            Z::SchiebLinksProzent => "<<%",
            Z::Plus => "+",
            Z::PlusGleich => "+=",
            Z::PlusProzent => "+%",
            Z::PlusStrich => "+|",
            Z::Minus => "-",
            Z::MinusGleich => "-=",
            Z::MinusProzent => "-%",
            Z::Stern => "*",
            Z::SternProzent => "*%",
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
            Z::Tilde => "~",
            Z::At => "@",
            Z::Hash => "#",
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
    /// An integer.
    Zahl(u128),
    /// **«F»: eine Gleitkommazahl** -- die Bits einer `f64` und die Frage, ob der
    /// Dezimalbruch DYADISCH ist (`m/10^d` mit `5^d | m`).
    ///
    /// *Die Dyadizitaet steht hier, weil nur der Leser die Ziffern hat.* Ob der Wert im
    /// ZIELTYP exakt liegt, ist eine zweite Frage -- sie haengt an der Mantissenbreite und
    /// gehoert M1.
    Gleitkomma(u64, bool),
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
            Art::Ident => format!("identifier `{}`", self.text(quelle)),
            Art::Wort(k) => format!("`{}`", k.text()),
            Art::Zahl(_) => format!("number `{}`", self.text(quelle)),
            Art::Gleitkomma(..) => format!("floating point number `{}`", self.text(quelle)),
            Art::Text => "string".to_string(),
            Art::Zeichen(z) => format!("`{}`", z.text()),
            Art::Ende => "end of file".to_string(),
        }
    }
}

fn ist_buchstabe(c: char) -> bool {
    c.is_ascii_alphabetic() || matches!(c, 'ä' | 'ö' | 'ü' | 'Ä' | 'Ö' | 'Ü' | 'ß')
}

fn ist_folgezeichen(c: char) -> bool {
    ist_buchstabe(c) || c.is_ascii_digit() || c == '_'
}

/// **Lane 182 (source trust: homoglyphs and bidi).** Gabbro's promise is that a HUMAN
/// reads a body and proves its logic ("written by hand and read by a person"); a program
/// that reads differently to a human than to the parser breaks exactly that premise: a
/// Cyrillic `а` in an identifier, a bidi control character that reorders a line (Trojan
/// Source, CVE-2021-42574). The tree had zero hits for homoglyph/bidi/confusable, and
/// this gate keeps it that way.
///
/// The gate runs BEFORE the main loop and only ADDS refusals (`P060`-`P063`); it never
/// removes one. Measured over the corpus on 2026-09-14: 988 `.gab` files (3796 distinct
/// code identifiers, all ASCII) plus every `gabbro` block of `FRAGMENTE.md`, `SYNTAX.md`,
/// `SPRACHE.md`, `README.md`, `MEMO-GLEITKOMMA.md` and `TUTORIAL.md` -- zero new
/// refusals. The allowed identifier set stays what it was (ASCII letters, digits, `_`,
/// plus `ä ö ü ß Ä Ö Ü`): the corpus uses no non-ASCII identifier in code position at
/// all, so ASCII-only would also pass, but dropping the documented umlauts would narrow
/// the grammar for no measured reason. `P064` stays unissued (spare of the lane).

/// A Unicode bidi control/format character: it reorders the line for a human while the
/// parser reads bytes in order. Refused ANYWHERE in the source -- comments and strings
/// included, because the reordering happens in the editor, not in the token.
fn ist_bidi(c: char) -> bool {
    matches!(c as u32,
        0x202A..=0x202E | 0x2066..=0x2069 | 0x200E | 0x200F | 0x061C)
}

/// An invisible character: zero-width space and joiners anywhere, and the byte-order
/// mark anywhere except as the very first character of the file (a BOM at offset 0 is
/// an editor's signature, not a hiding place).
fn ist_unsichtbar(c: char) -> bool {
    matches!(c as u32, 0x200B..=0x200D | 0xFEFF)
}

/// The script of a letter, for mixed-script detection. An approximation of UTS#39, not
/// the table: what matters here is not the exact script name but whether ONE identifier
/// draws letters from TWO of them. `13` is "any other letter": one family, so it still
/// counts as "not mixed" (the Lean twin spells ASCII-neutral as `0`; the tables agree
/// on 1..12, which is all the run rule reads).
fn schrift(c: char) -> u8 {
    let n = c as u32;
    if c.is_ascii_alphabetic()
        || (0x00C0..=0x00FF).contains(&n)
        || (0x0100..=0x024F).contains(&n)
        || (0x1E00..=0x1EFF).contains(&n)
    {
        1 // Latin (covers `ä ö ü ß Ä Ö Ü`)
    } else if (0x0370..=0x03FF).contains(&n) || (0x1F00..=0x1FFF).contains(&n) {
        2 // Greek
    } else if (0x0400..=0x04FF).contains(&n)
        || (0x0500..=0x052F).contains(&n)
        || (0x2DE0..=0x2DFF).contains(&n)
        || (0xA640..=0xA69F).contains(&n)
    {
        3 // Cyrillic
    } else if (0x0530..=0x058F).contains(&n) {
        4 // Armenian
    } else if (0x0590..=0x05FF).contains(&n) {
        5 // Hebrew
    } else if (0x0600..=0x06FF).contains(&n) || (0x0750..=0x077F).contains(&n) {
        6 // Arabic
    } else if (0x0900..=0x097F).contains(&n) {
        7 // Devanagari
    } else if (0x0E00..=0x0E7F).contains(&n) {
        8 // Thai
    } else if (0x10A0..=0x10FF).contains(&n) {
        9 // Georgian
    } else if (0x1100..=0x11FF).contains(&n) || (0xAC00..=0xD7AF).contains(&n) {
        10 // Hangul
    } else if (0x3040..=0x309F).contains(&n) || (0x30A0..=0x30FF).contains(&n) {
        11 // Hiragana / Katakana
    } else if (0x3400..=0x4DBF).contains(&n) || (0x4E00..=0x9FFF).contains(&n) {
        12 // Han
    } else {
        13 // Any other letter: one family, so it still counts as "not mixed"
    }
}

/// A run character for the trust scan below: `_`, ASCII letters and digits, and
/// the twelve script families (the umlauts fall in Latin). This is deliberately
/// NARROWER than `is_alphanumeric`: an exotic number (`²`) or punctuation (`·`)
/// BREAKS a run here exactly as it does in `LexerVertrauen.lean`, so both
/// implementations cut the same runs -- and whatever they cut around still
/// falls under `L006` in the main loop. What starts a run stays wider
/// (`is_alphabetic`, see below): a run the main loop would cut anyway costs
/// nothing to open.
fn ist_laufzeichen(c: char) -> bool {
    c == '_' || c.is_ascii_alphanumeric() || (1..=12).contains(&schrift(c))
}

/// The source-trust gate itself: (1) bidi and invisible characters over the RAW source,
/// comments and strings included; (2) identifier-like runs over code only (strings and
/// `--` comments skipped, exactly as the main loop skips them), refused as `P061`
/// (outside the allowed set) or `P062` (two scripts in one run).
///
/// A run that directly adjoins a digit (`0䀀`, `123abc`) is left to the number rules
/// (`L003`/`L006` own that neighbourhood); flagging it here too would double-report a
/// site the lexer already refuses.
fn quelltext_pruefe(quelle: &str, absagen: &mut Absagen) {
    for (i, c) in quelle.char_indices() {
        if ist_bidi(c) {
            absagen.schiebe(
                Absage::fehler(
                    "P060",
                    Span::neu(i as u32, (i + c.len_utf8()) as u32),
                    format!(
                        "bidi control character U+{:04X} -- the line reads differently \
                         to a human than to the parser",
                        c as u32
                    ),
                )
                .mit_notiz(
                    "Trojan Source (CVE-2021-42574): reordering is done by the editor, \
                     never by the source -- delete the character",
                ),
            );
        } else if ist_unsichtbar(c) && !(c == '\u{FEFF}' && i == 0) {
            absagen.schiebe(
                Absage::fehler(
                    "P063",
                    Span::neu(i as u32, (i + c.len_utf8()) as u32),
                    format!(
                        "invisible character U+{:04X} -- what the human cannot see the \
                         parser must not read",
                        c as u32
                    ),
                )
                .mit_notiz(
                    "U+FEFF is allowed once, as the first character of the file (BOM); \
                     everywhere else it hides",
                ),
            );
        }
    }

    let mut it = quelle.char_indices().peekable();
    // The last code character seen (strings and comments skipped): a run that starts
    // right behind a digit belongs to the number neighbourhood (see above).
    let mut vorher_ziffer = false;
    while let Some((von, c)) = it.next() {
        if c == '"' {
            while let Some((_, d)) = it.next() {
                if d == '"' || d == '\n' {
                    break;
                }
            }
            vorher_ziffer = false;
            continue;
        }
        if c == '-' && it.peek().is_some_and(|(_, d)| *d == '-') {
            while let Some((_, d)) = it.next() {
                if d == '\n' {
                    break;
                }
            }
            vorher_ziffer = false;
            continue;
        }
        if c.is_alphabetic() || c == '_' {
            let angehaengt = vorher_ziffer;
            let mut bis = von + c.len_utf8();
            while let Some((j, d)) = it.peek() {
                if ist_laufzeichen(*d) {
                    bis = *j + d.len_utf8();
                    it.next();
                } else {
                    break;
                }
            }
            let lauf = &quelle[von..bis];
            let erlaubt = lauf.chars().all(ist_folgezeichen);
            if !erlaubt && !angehaengt {
                let mut arten = [false; 14];
                for d in lauf.chars() {
                    if d.is_alphabetic() {
                        arten[schrift(d) as usize] = true;
                    }
                }
                let gemischt = arten.iter().filter(|&&b| b).count() >= 2;
                if gemischt {
                    absagen.schiebe(
                        Absage::fehler(
                            "P062",
                            Span::neu(von as u32, bis as u32),
                            format!(
                                "identifier `{lauf}` mixes two scripts -- a homoglyph \
                                 reads as one name and parses as another"
                            ),
                        )
                        .mit_notiz(
                            "identifiers are ASCII letters, digits and `_`, plus \
                             ä ö ü ß Ä Ö Ü -- all one (Latin) script",
                        ),
                    );
                } else {
                    absagen.schiebe(
                        Absage::fehler(
                            "P061",
                            Span::neu(von as u32, bis as u32),
                            format!(
                                "identifier `{lauf}` holds a character outside the \
                                 allowed set"
                            ),
                        )
                        .mit_notiz(
                            "identifiers are ASCII letters, digits and `_`, plus \
                             ä ö ü ß Ä Ö Ü",
                        ),
                    );
                }
            }
            vorher_ziffer = false;
            continue;
        }
        vorher_ziffer = c.is_ascii_digit();
    }
}

/// **Das Zeichen an der Byte-Stelle `i` — als ZEICHEN, nicht als Byte.**
///
/// `quelle.as_bytes()[i] as char` deutet ein Byte als Latin-1-Codepunkt. Bei ASCII ist das
/// dasselbe, ab `0x80` etwas anderes — und mitten in einer Mehrbyte-Folge ist es nichts.
fn zeichen_bei(quelle: &str, i: usize) -> Option<char> {
    quelle.get(i..).and_then(|r| r.chars().next())
}

/// Splits the source. Refusals accumulate; the stream does not abort, so that one run shows
/// more than a single finding.
pub fn zerlege(quelle: &str, absagen: &mut Absagen) -> Vec<Token> {
    // Lane 182 first: the source-trust gate (bidi, invisible, homoglyph identifiers).
    // It only adds refusals; the stream below is unchanged.
    quelltext_pruefe(quelle, absagen);
    let b = quelle.as_bytes();
    let mut i = if quelle.starts_with('\u{FEFF}') {
        '\u{FEFF}'.len_utf8()
    } else {
        0
    };
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
                        "string literal with no closing quote",
                    )
                    .mit_notiz(
                        "`char = any character except quote and newline` -- a string \
                         literal ends on its own line",
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
                        "capital letter in the number prefix",
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
            // **«F»: eine Gleitkommazahl -- und der Punkt ist GEMESSEN mehrdeutig.**
            //
            // `0..100` ist heute gueltiger Bereich, also entscheidet maximal munch: `..`
            // frisst zuerst. Darum die Bedingung „Punkt UND dahinter eine Ziffer" -- damit
            // bleibt `1..5` ein Bereich und `1.5` eine Zahl. Ein Punkt ohne Ziffer dahinter
            // faellt in den gewoehnlichen Zweig und wird dort zum Zeichen `.`.
            if basis == 10 && i + 1 < b.len() && b[i] == b'.' && b[i + 1].is_ascii_digit() {
                i += 1;
                let mut nachkomma = String::new();
                while i < b.len() && (b[i].is_ascii_digit() || b[i] == b'_') {
                    if b[i] != b'_' {
                        nachkomma.push(b[i] as char);
                    }
                    i += 1;
                }
                // Exponent -- NUR kleines `e`. Der Leser lehnt `0X`/`0B` seit jeher ab
                // (`L004`); eine Schreibweise, nicht zwei.
                let mut exp: i64 = 0;
                let mut exptext = String::new();
                if i < b.len() && b[i] == b'e' {
                    let merk = i;
                    i += 1;
                    let mut vorzeichen = 1i64;
                    if i < b.len() && (b[i] == b'+' || b[i] == b'-') {
                        if b[i] == b'-' {
                            vorzeichen = -1;
                        }
                        exptext.push(b[i] as char);
                        i += 1;
                    }
                    let anfang = i;
                    while i < b.len() && b[i].is_ascii_digit() {
                        exptext.push(b[i] as char);
                        i += 1;
                    }
                    if i == anfang {
                        // `1.5e` ohne Ziffern -- kein Exponent, zurueck.
                        i = merk;
                        exptext.clear();
                    } else {
                        exp = vorzeichen
                            * exptext.trim_start_matches(['+', '-']).parse::<i64>().unwrap_or(0);
                    }
                }
                let text = if exptext.is_empty() {
                    format!("{ziffern}.{nachkomma}")
                } else {
                    format!("{ziffern}.{nachkomma}e{exptext}")
                };
                let wert: f64 = text.parse().unwrap_or(f64::NAN);
                if !wert.is_finite() {
                    absagen.schiebe(
                        Absage::fehler(
                            "L007",
                            Span::neu(von as u32, i as u32),
                            "floating point literal is out of range",
                        )
                        .mit_notiz("the largest type is `f64`"),
                    );
                    schiebe(&mut out, Art::Gleitkomma(0, true), von, i);
                    continue;
                }
                // **Dyadisch?** `m / 10^d` ist ein Dyadenbruch genau dann, wenn `5^d` die
                // Mantisse teilt. Ein positiver Exponent hilft: er multipliziert mit `5^e`,
                // und das bleibt ganzzahlig.
                let netto = nachkomma.len() as i64 - exp;
                let dyadisch = if netto <= 0 {
                    true
                } else {
                    let ganze = format!("{ziffern}{nachkomma}");
                    match ganze.parse::<u128>() {
                        Ok(m) => (0..netto).try_fold(m, |acc, _| {
                            if acc % 5 == 0 { Some(acc / 5) } else { None }
                        }).is_some(),
                        // Zu viele Ziffern, um es auszurechnen -- dann ist die Antwort NEIN,
                        // und das ist die sichere Richtung: sie verlangt `rounded`.
                        Err(_) => false,
                    }
                };
                schiebe(&mut out, Art::Gleitkomma(wert.to_bits(), dyadisch), von, i);
                continue;
            }

            // A digit run adjoining a number is a trap: `0b12` would otherwise be `0b1`
            // followed by `2`. Refuse, never interpret.
            //
            // **`b[i] as char` war hier ein Absturz** (behoben 2026-08-19). Ein Byte ist kein
            // Zeichen: bei `0` gefolgt von einem Mehrbytezeichen steht an `i` dessen ERSTES
            // Byte, und `0xE4 as char` ist `ae` -- ein Buchstabe. Der Lauf trat damit MITTEN
            // in die Folge, `ende` landete auf keiner Zeichengrenze, und `&quelle[i..ende]`
            // riss den Uebersetzer mit *"is not a char boundary"* um. *Ein Absturz ist keine
            // Absage: er hat keine Stelle, keinen Code und keinen Grund.*
            //
            // Derselbe Fehler machte die Umlaute in `ist_buchstabe` wirkungslos: sie sind in
            // UTF-8 ZWEI Bytes, und keines davon ist fuer sich ein Buchstabe. Die Zeile las
            // also nie das, was sie zu lesen glaubte.
            if zeichen_bei(quelle, i).is_some_and(|c| ist_buchstabe(c) || c.is_ascii_digit()) {
                let ende = {
                    let mut j = i;
                    while let Some(c) = zeichen_bei(quelle, j) {
                        if !ist_folgezeichen(c) {
                            break;
                        }
                        j += c.len_utf8();
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
                        "numbers end before the next letter; there is no suffix",
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
            ("<<%", Z::SchiebLinksProzent),
            ("<<", Z::SchiebLinks),
            (">>", Z::SchiebRechts),
            ("+=", Z::PlusGleich),
            ("+%", Z::PlusProzent),
            ("+|", Z::PlusStrich),
            ("-=", Z::MinusGleich),
            ("-%", Z::MinusProzent),
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
            ("*%", Z::SternProzent),
            ("+", Z::Plus),
            ("-", Z::Minus),
            ("*", Z::Stern),
            ("/", Z::Schraeg),
            ("%", Z::Prozent),
            ("&", Z::Und),
            ("|", Z::Strich),
            ("^", Z::Dach),
            ("!", Z::Bang),
            ("~", Z::Tilde),
            ("@", Z::At),
            ("#", Z::Hash),
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
