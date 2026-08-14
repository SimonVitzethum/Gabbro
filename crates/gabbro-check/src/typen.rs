//! **Das Typmodell -- M1.**
//!
//! *„Ganzzahlen tragen ihren **Wertebereich**, und jede Operation muss darin bleiben. Das ist
//! Adas Trick, und **genau er** hat S1a/S1b gefunden -- nicht ‚Ada ist sicherer'."*
//! ([`SPRACHE.md`](SPRACHE.md) §M1)
//!
//! Deshalb rechnet dieses Modul in `i128`: jeder Bereich der Sprache -- bis `u64` hinauf --
//! passt hinein, samt der Zwischenergebnisse, die ihn verlassen. **Genau diese
//! Zwischenergebnisse sind der Befund**, den M1 meldet.

/// Der Bereich einer Ganzzahl: Breite und Vorzeichen der Maschine, Untergrenze und
/// Obergrenze der Sprache.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IntBereich {
    pub breite: u8,
    pub vorzeichen: bool,
    pub min: i128,
    pub max: i128,
    /// **U10.** Ein Literal hat keine eigene Breite und nimmt die der Gegenseite an.
    /// Eine DEKLARIERTE Groesse hat eine, auch wenn ihr Bereich ein Punkt ist: ohne diese
    /// Unterscheidung entschied `u8 in 200 .. 200` gegen `u8 in 200 .. 201`, ob M1 rechnet
    /// oder schweigt -- und die weniger konservative Antwort zaehlte als Deckung.
    pub literal: bool,
}

impl IntBereich {
    pub fn voll(breite: u8, vorzeichen: bool) -> IntBereich {
        let (min, max) = grenzen(breite, vorzeichen);
        IntBereich {
            breite,
            vorzeichen,
            min,
            max,
            literal: false,
        }
    }

    pub fn genau(breite: u8, vorzeichen: bool, min: i128, max: i128) -> IntBereich {
        IntBereich {
            breite,
            vorzeichen,
            min,
            max,
            literal: false,
        }
    }

    /// Der Bereich einer Konstanten -- die kleinste Breite, in die sie passt.
    pub fn konstante(wert: i128) -> IntBereich {
        let vorzeichen = wert < 0;
        let breite = [8u8, 16, 32, 64]
            .into_iter()
            .find(|b| {
                let (lo, hi) = grenzen(*b, vorzeichen);
                wert >= lo && wert <= hi
            })
            .unwrap_or(64);
        IntBereich {
            breite,
            vorzeichen,
            min: wert,
            max: wert,
            literal: true,
        }
    }

    /// Passt jeder Wert dieses Bereichs in den anderen?
    pub fn passt_in(&self, ziel: &IntBereich) -> bool {
        self.min >= ziel.min && self.max <= ziel.max
    }

    /// Passt der Bereich noch in die Maschinenbreite, in der gerechnet wird?
    pub fn passt_in_die_breite(&self) -> bool {
        let (lo, hi) = grenzen(self.breite, self.vorzeichen);
        self.min >= lo && self.max <= hi
    }

    pub fn enthaelt_null(&self) -> bool {
        self.min <= 0 && self.max >= 0
    }

    pub fn text(&self) -> String {
        let wort = format!(
            "{}{}",
            if self.vorzeichen { "i" } else { "u" },
            self.breite
        );
        let (lo, hi) = grenzen(self.breite, self.vorzeichen);
        if self.min == lo && self.max == hi {
            wort
        } else {
            format!("{wort} in {} .. {}", self.min, self.max)
        }
    }
}

pub fn grenzen(breite: u8, vorzeichen: bool) -> (i128, i128) {
    let b = breite as u32;
    if vorzeichen {
        (-(1i128 << (b - 1)), (1i128 << (b - 1)) - 1)
    } else {
        (0, (1i128 << b) - 1)
    }
}

/// Die Breite, in der zwei Operanden gerechnet werden. Gabbro kennt **keine implizite
/// Umwandlung**; bei verschiedenen Breiten ist das Ergebnis unbekannt statt geraten.
fn gemeinsame_form(a: &IntBereich, b: &IntBereich) -> Option<(u8, bool)> {
    if a.breite == b.breite && a.vorzeichen == b.vorzeichen {
        return Some((a.breite, a.vorzeichen));
    }
    // Ein LITERAL nimmt die Form der anderen Seite an -- es hat keine eigene. Eine
    // deklarierte Groesse tut das nicht, auch wenn ihr Bereich ein Punkt ist (U10).
    if a.literal {
        return Some((b.breite, b.vorzeichen));
    }
    if b.literal {
        return Some((a.breite, a.vorzeichen));
    }
    None
}

/// Ein Typ, so weit dieser Pass ihn kennt.
#[derive(Debug, Clone, PartialEq)]
pub enum Typ {
    Ganzzahl(IntBereich),
    /// `u32 wrapping` an einem Slot: der Ueberlauf ist deklariert und damit kein Befund.
    Umlaufend(IntBereich),
    Wahrheit,
    Nie,
    Zeiger(Box<Typ>),
    /// Ein Neutyp. `undurchsichtig` heisst: keine Umwandlung in beide Richtungen (D1).
    Benannt {
        name: String,
        undurchsichtig: bool,
        unter: Box<Typ>,
    },
    Summe {
        name: String,
        varianten: Vec<(String, Option<Typ>)>,
    },
    Verbund(Vec<(String, Typ)>),
    Feld {
        element: Box<Typ>,
        laenge: Option<u128>,
    },
    /// Eine `table`; ihre Slots erreicht man ueber `.slots[i]`.
    Tabelle(String),
    /// Ein Geraeteregister: zugleich Zahl **und** Feldverbund. Genau diese Doppelnatur ist
    /// der Grund fuer `device` -- ein `u32`, dessen Bits Namen haben.
    Register {
        bereich: IntBereich,
        felder: Vec<(String, IntBereich)>,
    },
    /// Ein `format`-Kopf oder ein `device`-Block.
    Verbundname(String),
    /// **Der ehrliche Ausgang.** Was hier steht, prueft M1 nicht -- und der Lauf zaehlt es.
    Unbekannt,
}

impl Typ {
    /// Der Bereich, in dem gerechnet wird -- durch Neutypen hindurch.
    pub fn bereich(&self) -> Option<IntBereich> {
        match self {
            Typ::Ganzzahl(b) | Typ::Umlaufend(b) => Some(*b),
            Typ::Register { bereich, .. } => Some(*bereich),
            Typ::Benannt { unter, .. } => unter.bereich(),
            _ => None,
        }
    }

    pub fn laeuft_um(&self) -> bool {
        match self {
            Typ::Umlaufend(_) => true,
            Typ::Benannt { unter, .. } => unter.laeuft_um(),
            _ => false,
        }
    }

    pub fn ist_unbekannt(&self) -> bool {
        matches!(self, Typ::Unbekannt)
    }

    /// Der Typ hinter einem Zeiger und hinter Neutypen -- fuer Feldzugriffe.
    pub fn durchgreifen(&self) -> &Typ {
        match self {
            Typ::Zeiger(z) => z.durchgreifen(),
            Typ::Benannt { unter, .. } => unter.durchgreifen(),
            anderer => anderer,
        }
    }

    pub fn text(&self) -> String {
        match self {
            Typ::Ganzzahl(b) => b.text(),
            Typ::Umlaufend(b) => format!("{} wrapping", b.text()),
            Typ::Wahrheit => "bool".to_string(),
            Typ::Nie => "never".to_string(),
            Typ::Zeiger(z) => format!("ptr<…> {}", z.text()),
            Typ::Benannt { name, .. } => name.clone(),
            Typ::Summe { name, .. } => name.clone(),
            Typ::Verbund(_) => "{ … }".to_string(),
            Typ::Feld { element, laenge } => match laenge {
                Some(n) => format!("[{}; {n}]", element.text()),
                None => format!("[{}; ?]", element.text()),
            },
            Typ::Tabelle(n) | Typ::Verbundname(n) => n.clone(),
            Typ::Register { bereich, .. } => bereich.text(),
            Typ::Unbekannt => "?".to_string(),
        }
    }
}

/// Das Ergebnis einer Rechenoperation, samt der Frage, ob sie ihre Breite verlaesst.
pub struct Rechnung {
    pub bereich: Option<IntBereich>,
    /// Der Bereich verlaesst die Maschinenbreite -- **das ist der Ueberlauf**.
    pub laeuft_ueber: bool,
}

fn ergebnis(breite: u8, vorzeichen: bool, min: i128, max: i128) -> Rechnung {
    let b = IntBereich::genau(breite, vorzeichen, min, max);
    Rechnung {
        laeuft_ueber: !b.passt_in_die_breite(),
        bereich: Some(b),
    }
}

pub fn addiere(a: &IntBereich, b: &IntBereich) -> Rechnung {
    let Some((breite, vz)) = gemeinsame_form(a, b) else {
        return Rechnung {
            bereich: None,
            laeuft_ueber: false,
        };
    };
    ergebnis(breite, vz, a.min + b.min, a.max + b.max)
}

pub fn subtrahiere(a: &IntBereich, b: &IntBereich) -> Rechnung {
    let Some((breite, vz)) = gemeinsame_form(a, b) else {
        return Rechnung {
            bereich: None,
            laeuft_ueber: false,
        };
    };
    ergebnis(breite, vz, a.min - b.max, a.max - b.min)
}

pub fn multipliziere(a: &IntBereich, b: &IntBereich) -> Rechnung {
    let Some((breite, vz)) = gemeinsame_form(a, b) else {
        return Rechnung {
            bereich: None,
            laeuft_ueber: false,
        };
    };
    let ecken = [a.min * b.min, a.min * b.max, a.max * b.min, a.max * b.max];
    let min = ecken.iter().copied().min().unwrap_or(0);
    let max = ecken.iter().copied().max().unwrap_or(0);
    ergebnis(breite, vz, min, max)
}

/// Teilen und Rest verlangen einen Nenner, dessen Bereich die Null ausschliesst -- das
/// prueft der Aufrufer, hier steht nur der Ergebnisbereich.
pub fn teile(a: &IntBereich, b: &IntBereich) -> Rechnung {
    let Some((breite, vz)) = gemeinsame_form(a, b) else {
        return Rechnung {
            bereich: None,
            laeuft_ueber: false,
        };
    };
    if b.enthaelt_null() {
        return Rechnung {
            bereich: None,
            laeuft_ueber: false,
        };
    }
    if a.min >= 0 && b.min > 0 {
        return ergebnis(breite, vz, a.min / b.max, a.max / b.min);
    }
    // Vorzeichenbehaftet: die vier Ecken, konservativ.
    let ecken = [a.min / b.min, a.min / b.max, a.max / b.min, a.max / b.max];
    let min = ecken.iter().copied().min().unwrap_or(0);
    let max = ecken.iter().copied().max().unwrap_or(0);
    ergebnis(breite, vz, min, max)
}

pub fn rest(a: &IntBereich, b: &IntBereich) -> Rechnung {
    let Some((breite, vz)) = gemeinsame_form(a, b) else {
        return Rechnung {
            bereich: None,
            laeuft_ueber: false,
        };
    };
    if b.enthaelt_null() {
        return Rechnung {
            bereich: None,
            laeuft_ueber: false,
        };
    }
    if a.min >= 0 && b.min > 0 {
        // Der Rest ist kleiner als der Nenner -- und nie groesser als der Zaehler.
        return ergebnis(breite, vz, 0, (b.max - 1).min(a.max));
    }
    let schranke = b.min.abs().max(b.max.abs()) - 1;
    ergebnis(breite, vz, -schranke, schranke)
}

/// Bitweise Operationen: der Bereich faellt aus der **Bitbreite** der Operanden, nicht aus
/// ihren Grenzen. Konservativ, aber nie zu eng.
pub fn bitweise(a: &IntBereich, b: &IntBereich, op: BitOpArt) -> Rechnung {
    let Some((breite, vz)) = gemeinsame_form(a, b) else {
        return Rechnung {
            bereich: None,
            laeuft_ueber: false,
        };
    };
    if a.min < 0 || b.min < 0 {
        let (lo, hi) = grenzen(breite, vz);
        return ergebnis(breite, vz, lo, hi);
    }
    let max = match op {
        // `a & b` ist nie groesser als der kleinere Operand.
        BitOpArt::Und => a.max.min(b.max),
        // `a | b` und `a ^ b` bleiben in der gemeinsamen Bitmaske.
        BitOpArt::Oder | BitOpArt::Xor => maske(a.max.max(b.max)),
    };
    ergebnis(breite, vz, 0, max)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BitOpArt {
    Und,
    Oder,
    Xor,
}

/// Die kleinste Maske `2^k - 1`, die den Wert deckt.
fn maske(wert: i128) -> i128 {
    if wert <= 0 {
        return 0;
    }
    let bits = 128 - wert.leading_zeros();
    if bits >= 127 {
        i128::MAX
    } else {
        (1i128 << bits) - 1
    }
}

pub fn schiebe_links(a: &IntBereich, b: &IntBereich) -> Rechnung {
    // Eine Schiebeweite ausserhalb der Breite ist keine Rechnung, sondern ein Befund.
    if b.min < 0 || b.max >= a.breite as i128 {
        let (lo, hi) = grenzen(a.breite, a.vorzeichen);
        let mut r = ergebnis(a.breite, a.vorzeichen, lo, hi);
        r.laeuft_ueber = true;
        return r;
    }
    // **U8.** Frueher gab der Vorzeichenfall den vollen Bereich zurueck und loeschte damit
    // den Wertueberlauf: `i32 in -1 .. 1000000 << 20` kam durch. Die vier Ecken sind auch
    // mit Vorzeichen richtig -- links schieben ist monoton in beiden Argumenten.
    let ecken = [
        a.min << b.min,
        a.min << b.max,
        a.max << b.min,
        a.max << b.max,
    ];
    ergebnis(
        a.breite,
        a.vorzeichen,
        ecken.iter().copied().min().unwrap_or(0),
        ecken.iter().copied().max().unwrap_or(0),
    )
}

pub fn schiebe_rechts(a: &IntBereich, b: &IntBereich) -> Rechnung {
    if a.min < 0 || b.min < 0 || b.max >= a.breite as i128 {
        let (lo, hi) = grenzen(a.breite, a.vorzeichen);
        let mut r = ergebnis(a.breite, a.vorzeichen, lo, hi);
        r.laeuft_ueber = b.max >= a.breite as i128;
        return r;
    }
    ergebnis(a.breite, a.vorzeichen, a.min >> b.max, a.max >> b.min)
}

#[cfg(test)]
mod proben {
    use super::*;

    #[test]
    fn addition_weitet_den_bereich() {
        let a = IntBereich::genau(32, false, 0, 1000);
        let r = addiere(&a, &a);
        assert_eq!(r.bereich.expect("Bereich").max, 2000);
        assert!(!r.laeuft_ueber);
    }

    #[test]
    fn subtraktion_faellt_unter_null() {
        // Der gemessene Fall: `refcount -= 1` ohne Vorpruefung.
        let z = IntBereich::genau(32, false, 0, 65535);
        let eins = IntBereich::konstante(1);
        let r = subtrahiere(&z, &eins);
        assert_eq!(r.bereich.expect("Bereich").min, -1);
        assert!(r.laeuft_ueber, "unter Null ist Ueberlauf in u32");
    }

    #[test]
    fn multiplikation_verlaesst_die_breite() {
        let a = IntBereich::voll(32, false);
        let r = multipliziere(&a, &a);
        assert!(r.laeuft_ueber);
    }

    /// **U10.** Nur ein LITERAL nimmt die Breite der Gegenseite an. Eine deklarierte
    /// Groesse mit Punktbereich tut es nicht -- sonst entscheidet der Zufall einer
    /// Deklaration darueber, ob M1 rechnet oder schweigt.
    ///
    /// Diese Probe steht hier, weil die Mutationsprobe die Regel als **unbewacht** meldete:
    /// der Beispielkorpus konnte „`u8 in 200..200` nimmt fremde Breite" nicht von
    /// „nimmt sie nicht" unterscheiden.
    #[test]
    fn nur_ein_literal_hat_keine_eigene_breite() {
        let literal = IntBereich::konstante(200);
        let deklariert = IntBereich::genau(8, false, 200, 200);
        let breit = IntBereich::voll(32, false);
        assert!(literal.literal);
        assert!(!deklariert.literal);
        // Das Literal nimmt die Form der Gegenseite an -- `x + 1` muss rechnen.
        assert!(addiere(&breit, &literal).bereich.is_some());
        // Die deklarierte u8-Groesse nicht -- gemischte Breiten sind ehrlich unbekannt.
        // **Beide Seiten**: die Regel steht zweimal symmetrisch im Quelltext, und eine
        // Mutationsprobe, die nur eine Seite beschaedigt, ueberlebt sonst.
        assert!(
            addiere(&breit, &deklariert).bereich.is_none(),
            "eine deklarierte Groesse darf keine fremde Breite uebernehmen (rechts)"
        );
        assert!(
            addiere(&deklariert, &breit).bereich.is_none(),
            "eine deklarierte Groesse darf keine fremde Breite uebernehmen (links)"
        );
        assert!(addiere(&literal, &breit).bereich.is_some());
    }

    /// **U8.** Beide Ecken des Linksschiebens, nicht nur die obere.
    #[test]
    fn schieben_prueft_auch_die_untere_ecke() {
        let nur_unten = IntBereich::genau(32, true, -3000, 1);
        let zwanzig = IntBereich::konstante(20);
        assert!(
            schiebe_links(&nur_unten, &zwanzig).laeuft_ueber,
            "-3000 << 20 verlaesst i32 nach unten"
        );
    }

    #[test]
    fn teilen_durch_einen_bereich_mit_null_gibt_nichts() {
        let a = IntBereich::genau(32, false, 0, 100);
        let b = IntBereich::genau(32, false, 0, 10);
        assert!(teile(&a, &b).bereich.is_none());
        let c = IntBereich::genau(32, false, 1, 10);
        assert_eq!(teile(&a, &c).bereich.expect("Bereich").max, 100);
    }
}
