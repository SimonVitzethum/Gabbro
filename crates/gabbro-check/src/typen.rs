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

/// **«F»: die Gleitkommatatsache -- die Ganzzahltatsache PLUS ZWEI BITS.**
///
/// Ein Intervall ueber den reellen Zahlen, dazu `kann_nan` und `kann_unendlich`. *Das ist
/// kein Loeser*, sondern Intervallfortpflanzung -- dieselbe Bauart wie `IntBereich`, den M1
/// laengst traegt. Die Kante gilt unveraendert: geschlossene Form, keine freie Arithmetik.
///
/// **Warum die zwei Bits und nicht nur das Intervall:** ist ein Operand NaN, sind ALLE
/// Vergleiche falsch, und aus `!(x < y)` folgt `x >= y` nicht. Die Negation liefert ihre
/// Tatsache darum genau dann, wenn beide Seiten als nicht-NaN bekannt sind -- und das steht
/// hier.
///
/// *Ein deklarierter Wert kann alles sein; ein LITERAL ist bekannt endlich.* Deshalb ist die
/// Voreinstellung fuer eine Deklaration `true/true` und fuer ein Literal `false/false`.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct FBereich {
    /// 32 oder 64.
    pub breite: u8,
    pub lo: f64,
    pub hi: f64,
    pub kann_nan: bool,
    pub kann_unendlich: bool,
    /// Wie bei `IntBereich`: ein Literal hat keine eigene Breite.
    pub literal: bool,
}

impl FBereich {
    /// Der volle Bereich eines deklarierten Typs -- alles ist moeglich, NaN eingeschlossen.
    pub fn voll(breite: u8) -> Self {
        FBereich {
            breite,
            lo: f64::NEG_INFINITY,
            hi: f64::INFINITY,
            kann_nan: true,
            kann_unendlich: true,
            literal: false,
        }
    }

    /// Ein Literal: ein Punkt, endlich, kein NaN.
    pub fn punkt(wert: f64) -> Self {
        FBereich {
            breite: 64,
            lo: wert,
            hi: wert,
            kann_nan: false,
            kann_unendlich: false,
            literal: true,
        }
    }

    /// **Die Mantissenbreite -- daran haengt die Exaktheit eines Literals.**
    pub fn mantisse(self) -> u32 {
        if self.breite == 32 { 24 } else { 53 }
    }

    /// Endlich UND nicht NaN -- die Tatsache, die `narrow … to finite` herstellt.
    pub fn ist_sicher(self) -> bool {
        !self.kann_nan && !self.kann_unendlich
    }
}

/// Ein Typ, so weit dieser Pass ihn kennt.
#[derive(Debug, Clone, PartialEq)]
pub enum Typ {
    Ganzzahl(IntBereich),
    /// **«F»** -- siehe `FBereich`.
    Gleitkomma(FBereich),
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
        /// **«B32»:** `reg X : u16 wrapping @…` -- der Umlauf ist deklariert und damit
        /// kein Befund. Ohne dieses Feld konnte ein Hardwarezaehler seine Absicht nicht
        /// aussprechen, und M1 sagte an der richtigen Regel das falsche Programm ab.
        umlaufend: bool,
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
            // «B32»: ein Register darf seinen Umlauf ebenso aussprechen wie ein Slot.
            Typ::Register { umlaufend, .. } => *umlaufend,
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
            Typ::Gleitkomma(f) => {
                let art = if f.kann_nan {
                    " (kann NaN)"
                } else if f.kann_unendlich {
                    " (kann unendlich)"
                } else {
                    ""
                };
                if f.lo == f64::NEG_INFINITY && f.hi == f64::INFINITY {
                    format!("f{}{art}", f.breite)
                } else {
                    format!("f{} in {} .. {}{art}", f.breite, f.lo, f.hi)
                }
            }
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
        assert!(r.laeuft_ueber, "below zero is overflow in u32");
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
            "a declared quantity must not adopt a foreign width (right)"
        );
        assert!(
            addiere(&deklariert, &breit).bereich.is_none(),
            "a declared quantity must not adopt a foreign width (left)"
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

/// **Wertetabellen — Grenzen statt Klassen.**
///
/// Der erzeugte Mutationslauf vom 2026-08-15 fand **15 echte Regelluecken, 11 davon in
/// `typen.rs` und `umgebung.rs`** — der Bereichsarithmetik und der Konstantenauswertung.
/// Das Muster war lesbar und nicht zufaellig:
///
/// > **Der Pruefer ist dicht, wo er ABSAGEN ERZEUGT, und duenn, wo er RECHNET.**
///
/// Die 38 Handmutationen zielten auf Absagen, weil Absagen das sind, was man beim Schreiben
/// im Kopf hat. Und die Beispieldateien koennen es nicht auffangen: **ein Beispiel mit
/// `u8 in 0 .. 200` faellt bei jeder falschen Obergrenze zwischen 200 und 255 gleich aus.**
/// Es trifft eine KLASSE, keine GRENZE.
///
/// Diese Tabellen tun das Gegenteil: jede Zeile steht auf einer Kante, an der ein Fehler um
/// **eins** sichtbar wird.
#[cfg(test)]
mod wertetabellen {
    use super::*;

    fn u(breite: u8, min: i128, max: i128) -> IntBereich {
        IntBereich::genau(breite, false, min, max)
    }
    fn i(breite: u8, min: i128, max: i128) -> IntBereich {
        IntBereich::genau(breite, true, min, max)
    }
    fn b(r: &Rechnung) -> (i128, i128) {
        let x = r.bereich.expect("Bereich erwartet");
        (x.min, x.max)
    }

    #[test]
    fn multiplikation_nimmt_die_kleinste_und_groesste_ecke() {
        // Vier Ecken, und bei gemischten Vorzeichen liegt das Minimum NICHT bei min*min.
        // Ein `unwrap_or(0)` statt `min()` faellt hier, ein `max()` statt `min()` auch.
        let r = multipliziere(&i(32, -3, 2), &i(32, -5, 7));
        assert_eq!(b(&r), (-21, 15), "min = 2*-5 = -21, max = -3*-5 = 15");
        let r = multipliziere(&i(32, -3, -1), &i(32, -5, -2));
        assert_eq!(b(&r), (2, 15), "beide negativ: min = -1*-2, max = -3*-5");
        let r = multipliziere(&u(32, 0, 0), &u(32, 5, 9));
        assert_eq!(b(&r), (0, 0), "die Null frisst jede Ecke");
    }

    #[test]
    fn division_hat_zwei_wege_und_der_schnelle_gilt_nur_streng_positiv() {
        // `a.min >= 0 && b.min > 0` ist der schnelle Weg. Die Kante ist b.min == 1 gegen 0.
        let r = teile(&u(32, 10, 20), &u(32, 1, 4));
        assert_eq!(b(&r), (2, 20), "min = 10/4, max = 20/1");
        // b.min == 0 heisst: enthaelt die Null -- gar keine Rechnung.
        assert!(teile(&u(32, 10, 20), &u(32, 0, 4)).bereich.is_none());
        //
        // **AEQUIVALENTER MUTANT, nachgewiesen statt behauptet.** `b.min > 0` gegen
        // `b.min >= 0` an dieser Verzweigung ist NICHT unterscheidbar: die Pruefung
        // `b.enthaelt_null()` (`min <= 0 && max >= 0`) steht davor und faengt jedes `b` mit
        // `min == 0 && max >= 0` ab; ist `max < 0`, so ist auch `min < 0`, und beide
        // Bedingungen sind falsch. **Es gibt kein `b`, das die zwei Fassungen trennt.**
        //
        // Der erzeugte Mutationslauf zaehlt diese Stelle als „entkommen". Das ist richtig
        // gezaehlt und trotzdem kein Loch -- und der Unterschied gehoert aufgeschrieben,
        // sonst jagt jemand einer Probe hinterher, die es nicht geben kann.
        // a.min == 0 ist noch der schnelle Weg (>= 0), b.min == 1 auch.
        let r = teile(&u(32, 0, 20), &u(32, 1, 1));
        assert_eq!(b(&r), (0, 20));
        // Vorzeichenbehaftet muss ueber die vier Ecken gehen: -20/1 = -20 ist das Minimum.
        let r = teile(&i(32, -20, 10), &i(32, 1, 2));
        assert_eq!(b(&r), (-20, 10));
    }

    #[test]
    fn bitweise_faellt_bei_jedem_negativen_operanden_auf_die_volle_breite() {
        // Die Kante ist min == 0 gegen min == -1, auf BEIDEN Seiten.
        let r = bitweise(&u(8, 0, 3), &u(8, 0, 5), BitOpArt::Oder);
        assert_eq!(b(&r), (0, 7), "0..3 | 0..5 fits mask 7");
        let (lo, hi) = grenzen(8, true);
        let r = bitweise(&i(8, -1, 3), &i(8, 0, 5), BitOpArt::Oder);
        assert_eq!(b(&r), (lo, hi), "ein negativer Operand links -> volle Breite");
        let r = bitweise(&i(8, 0, 3), &i(8, -1, 5), BitOpArt::Oder);
        assert_eq!(b(&r), (lo, hi), "and the same on the right -- `||`, not `&&`");
    }

    #[test]
    fn die_maske_ist_die_naechste_zweierpotenz_minus_eins() {
        // Die Kanten sind die Zweierpotenzen selbst: 7 -> 7, 8 -> 15.
        assert_eq!(maske(0), 0);
        assert_eq!(maske(1), 1);
        assert_eq!(maske(7), 7, "7 needs 3 bits -> 2^3-1 = 7");
        assert_eq!(maske(8), 15, "8 needs 4 bits -> 2^4-1 = 15, NOT 8");
        assert_eq!(maske(255), 255);
        assert_eq!(maske(256), 511);
        // Und die Ueberlaufkante bei 127 Bit: `1 << 127` waere ein Ueberlauf in i128.
        assert_eq!(maske(i128::MAX), i128::MAX, "keine Verschiebung um 127 oder mehr");
    }

    #[test]
    fn linksschieben_ueber_die_breite_ist_ein_befund_kein_ergebnis() {
        // Die Kante: Schiebeweite == breite-1 rechnet, == breite laeuft ueber.
        let r = schiebe_links(&u(8, 1, 1), &u(8, 7, 7));
        assert!(!r.laeuft_ueber, "1 << 7 = 128 passt in u8");
        // **Der Wert muss PASSEN, damit nur die Weitenregel sprechen kann.** `1 << 8 = 256`
        // laeuft ohnehin ueber; die Probe haette dann zwei Gruende und misst keinen.
        // `0 << 8 = 0` passt in jedes u8 -- faellt es trotzdem, war es die Weite.
        let r = schiebe_links(&u(8, 0, 0), &u(8, 8, 8));
        assert!(
            r.laeuft_ueber,
            "0 << 8 FITS -- if it falls, it is because width == breadth, nothing else"
        );
        let r = schiebe_links(&u(8, 0, 0), &u(8, 7, 7));
        assert!(!r.laeuft_ueber, "width 7 < 8 is arithmetic, not a finding");
        let r = schiebe_links(&u(8, 1, 1), &i(8, -1, 2));
        assert!(r.laeuft_ueber, "a negative width is not arithmetic");
    }

    #[test]
    fn addition_erkennt_den_ueberlauf_an_der_kante_und_nicht_davor() {
        // u8: 255 + 0 passt, 255 + 1 nicht. Ein `>=` statt `>` faellt hier.
        assert!(!addiere(&u(8, 255, 255), &u(8, 0, 0)).laeuft_ueber);
        assert!(addiere(&u(8, 255, 255), &u(8, 1, 1)).laeuft_ueber);
        assert!(!addiere(&u(8, 0, 254), &u(8, 0, 1)).laeuft_ueber);
        assert!(addiere(&u(8, 0, 255), &u(8, 0, 1)).laeuft_ueber);
    }
}
