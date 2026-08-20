//! **Die Zusage eines FREMDEN Rumpfes ist eine Tatsache im Pruefer -- und sie entscheidet.**
//!
//! `m1::aus_ensures` verengt seit dem 2026-08-19 das Ergebnis eines Rufs aus dem `ensures`
//! des Gerufenen. Bei einem `impl fn` ist das eine Ableitung, die Gabbro einmal selbst
//! nachrechnen wird. **Bei einem `extern fn` ist es Glaube** -- und der Glaube wirkt bis ins
//! Erzeugnis, weil ein engerer Bereich andere Pruefungen bestehen laesst und andere
//! Absenkungen erlaubt.
//!
//! ```gabbro
//! extern fn melde_roh(t : ptr<…>) -> u32 ensures result <= 4096 …;
//! ...
//! let n = melde_roh(t);        -- `n` hat hier `u32 in 0 .. 4096`, weil eine Zeile es sagt
//! ```
//!
//! ## Warum das ein EIGENER Posten ist und nicht die allgemeine Annahmenflaeche
//!
//! Abschnitt E des Zeugnisses zaehlt die fremden Ruempfe samt Vertrag. Das ist die FLAECHE.
//! **Eine Verengung mit Wirkung im Erzeugnis ist etwas anderes als eine Zeile, die niemanden
//! bindet** -- und der Unterschied zwischen beiden ist genau der Gegenstand dieses Moduls:
//! `aus_ensures` gibt den Bereich unveraendert zurueck, wenn sich nichts bewegt hat.
//! *Gezaehlt wird die WIRKSAME Verengung, nicht die vorhandene Klausel.*
//!
//! ## EIN Leser, nicht zwei
//!
//! Dieses Projekt hat sich am 2026-08-20 daran verletzt: eine Tatsache hatte zwei Leser, und
//! nur einer las sie. **Die Frage „verengt diese `ensures`-Klausel, und wie?" wird hier
//! genau einmal beantwortet** -- `bereich_aus_ensures` liefert den verengten Typ UND die
//! Schritte, die dahin gefuehrt haben. M1 nimmt den Typ, das Zeugnis nimmt die Schritte;
//! *keiner von beiden rechnet die Antwort ein zweites Mal aus.*
//!
//! ## Was hier NICHT steht
//!
//! * **Die Verengung wird nicht abgeschaltet.** Ein Vertrag an einem fremden Rumpf SOLL
//!   wirken; das ist sein Zweck. Er wird sichtbar gemacht, nicht entfernt.
//! * **`M115` ist nicht dieselbe Klasse.** Es liest das `requires` des Fremden und WEIST AB.
//!   Eine falsche Vorbedingung an einer fremden Deklaration kann ein richtiges Programm
//!   abweisen -- sie kann kein falsches durchlassen. *Die Richtung ist der Unterschied:
//!   `ensures` laesst den Pruefer mehr glauben, `requires` weniger.* Der Befund steht in
//!   `messung/FREMDVERENGUNG.md`, damit die Entscheidung nachlesbar ist statt bloss gefallen.

use crate::typen::{IntBereich, Typ};
use gabbro_syntax::ast::*;
use gabbro_syntax::span::Span;

/// Der gespiegelte Vergleich -- `zahl < result` heisst `result > zahl`.
///
/// **Steht hier und nicht in `m1.rs`**, weil beide Richtungen desselben Vertrags ihn
/// brauchen (`aus_ensures` und `requires_pruefen`) und weil das Zeugnis die Klausel so
/// abdruckt, wie der Pruefer sie gelesen hat.
pub fn gespiegelt(op: BinOp) -> BinOp {
    match op {
        BinOp::Kleiner => BinOp::Groesser,
        BinOp::KleinerGleich => BinOp::GroesserGleich,
        BinOp::Groesser => BinOp::Kleiner,
        BinOp::GroesserGleich => BinOp::KleinerGleich,
        x => x,
    }
}

pub fn zeichen(op: BinOp) -> &'static str {
    match op {
        BinOp::Kleiner => "<",
        BinOp::KleinerGleich => "<=",
        BinOp::Groesser => ">",
        BinOp::GroesserGleich => ">=",
        BinOp::Gleich => "==",
        _ => "?",
    }
}

/// **Ein Schritt: eine Klausel, die eine Grenze BEWEGT hat.**
///
/// Eine Klausel, die keine bewegt, erzeugt keinen Schritt -- sie ist die Zeile, die niemanden
/// bindet.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Schritt {
    /// Die Klausel, so wie der Pruefer sie gelesen hat: `result <= 4096`.
    pub klausel: String,
    /// Der Bereich, bevor diese Klausel angewandt wurde.
    pub vorher: String,
    /// Der Bereich danach.
    pub nachher: String,
    /// **Hat sie eine Grenze BEWEGT?** *Das ist der ganze Gegenstand des Postens* -- eine
    /// Klausel, die nichts verengt, ist eine Zeile, die niemanden bindet.
    pub wirksam: bool,
}

/// Das Ergebnis der Frage: **welcher Typ, und was hat ihn verengt?**
#[derive(Debug, Clone)]
pub struct Verengung {
    /// Der Typ, mit dem der Rufer weiterrechnet.
    pub typ: Typ,
    /// Leer heisst: **keine Verengung.** Entweder gibt es keine Klausel dieser Form, oder
    /// keine bewegt eine Grenze, oder das Ergebnis waere leer gewesen.
    pub schritte: Vec<Schritt>,
}

/// **Der EINE Leser der Frage „verengt dieses `ensures` das Ergebnis, und wie?".**
///
/// *Punkt 4 vom 2026-08-19; bis dahin war ein Vertrag an einem fremden Rumpf in BEIDEN
/// Richtungen wirkungslos.*
///
/// ```gabbro
/// extern fn hole() -> u32 ensures result <= 100 …;
/// impl fn nutze() -> u32 in 0 .. 100 { let x = hole(); return x; }
/// --> M101: die Rueckgabe verlangt `u32 in 0 .. 100`, der Wert hat `u32`
/// ```
///
/// **48 fremde Ruempfe im Korpus, NULL sprachen ihre Pflicht aus** -- und der Grund war nicht
/// Nachlaessigkeit: *Hinschreiben kostete nichts und brachte nichts.* Eine Klausel, die
/// niemand liest, schreibt niemand.
///
/// > **Und die Richtung ist eine ANNAHME, keine Ableitung.** Bei einem `extern fn` glaubt
/// > Gabbro dem fremden Rumpf; das ist der Zweck eines Vertrags und trotzdem
/// > Vertrauensflaeche. *Deshalb zaehlt `gabbro pflichten` sie als `F`, das Zeugnis nennt die
/// > Flaeche in Abschnitt E und die WIRKSAMEN Stellen in Abschnitt F* -- wer nicht pruefen
/// > kann, EXPORTIERT.
///
/// Verengt wird nur aus Vergleichen `result <op> <Zahl>` -- die Form, die 14 der 17 Pflichten
/// des Beispielkorpus haben. Alles Uebrige (Quantoren, Weltzustand, `old`) bleibt liegen: es
/// waere eine Aussage ueber ORTE, und die Tatsachenmaschinerie haengt an Namen, die der Rufer
/// nicht kennt. Die relationale Form `result <op> <Ort>` liest `m1::beziehung_aus_ensures`.
///
/// **Ein leerer Bereich ist kein Fortschritt, sondern ein Widerspruch** -- und den meldet
/// nicht diese Funktion. *Sie verengt oder schweigt*, und wenn sie schweigt, ist die Liste
/// der Schritte leer. Damit gilt: `schritte.is_empty()` genau dann, wenn `typ` der
/// Eingabetyp ist.
pub fn bereich_aus_ensures(roh: &Typ, ensures: &[Pred]) -> Verengung {
    let stumm = Verengung {
        typ: roh.clone(),
        schritte: Vec::new(),
    };
    let Some(b) = roh.bereich() else { return stumm };
    let text = |lo: i128, hi: i128| IntBereich::genau(b.breite, b.vorzeichen, lo, hi).text();
    let (mut min, mut max) = (b.min, b.max);
    let mut schritte = Vec::new();
    for p in ensures {
        let Some((op, zahl)) = ergebnis_gegen_zahl(p) else { continue };
        let (vmin, vmax) = (min, max);
        match op {
            BinOp::Kleiner => max = max.min(zahl - 1),
            BinOp::KleinerGleich => max = max.min(zahl),
            BinOp::Groesser => min = min.max(zahl + 1),
            BinOp::GroesserGleich => min = min.max(zahl),
            BinOp::Gleich => {
                min = min.max(zahl);
                max = max.min(zahl);
            }
            _ => {}
        }
        schritte.push(Schritt {
            klausel: format!("result {} {zahl}", zeichen(op)),
            vorher: text(vmin, vmax),
            nachher: text(min, max),
            wirksam: (min, max) != (vmin, vmax),
        });
    }
    if min > max {
        // **Ein leerer Bereich ist kein Fortschritt, sondern ein Widerspruch** -- und den
        // meldet nicht diese Funktion. *Sie verengt oder schweigt.*
        return stumm;
    }
    // **Die EINE Zeile, die „wirksam" von „vorhanden" trennt.** Sie steht bewusst hier und
    // nicht in der Schleife: `schritte` ist danach genau dann leer, wenn keine Grenze sich
    // bewegt hat -- und das ist dieselbe Bedingung wie `(min, max) == (b.min, b.max)`, weil
    // beide Grenzen nur monoton wandern. *Eine Bedingung, zwei Leser waere genau der Fehler,
    // gegen den dieses Modul gebaut ist.*
    schritte.retain(|s| s.wirksam);
    if schritte.is_empty() {
        return stumm;
    }
    Verengung {
        typ: Typ::Ganzzahl(IntBereich::genau(b.breite, b.vorzeichen, min, max)),
        schritte,
    }
}

/// `result <op> <Zahl>` -- und die gespiegelte Form `<Zahl> <op> result`.
fn ergebnis_gegen_zahl(p: &Pred) -> Option<(BinOp, i128)> {
    let PredArt::Vergleich(e) = &p.art else { return None };
    let ExprArt::Binaer(op, a, c) = &e.art else { return None };
    match (&a.art, &c.art) {
        (ExprArt::Ergebnis, ExprArt::Zahl(n)) => Some((*op, *n as i128)),
        (ExprArt::Zahl(n), ExprArt::Ergebnis) => Some((gespiegelt(*op), *n as i128)),
        _ => None,
    }
}

/// **Was aus einer `ensures`-Klausel eines fremden Rumpfes im Rufer geworden ist.**
#[derive(Debug, Clone)]
pub enum Wirkung {
    /// Der Bereich des Ergebnisses ist enger geworden.
    Bereich { vorher: String, nachher: String },
    /// Eine Beziehung zweier Stellen wurde als Tatsache angelegt (`Fakt::Beziehung`).
    Beziehung,
}

impl Wirkung {
    pub fn marke(&self) -> &'static str {
        match self {
            Wirkung::Bereich { .. } => "range",
            Wirkung::Beziehung => "relation",
        }
    }
}

/// **Eine Stelle, an der der Vertrag eines fremden Rumpfes im Rufer GEWIRKT hat.**
///
/// Nicht: eine Stelle, an der eine Klausel steht. *Die Zeile, die niemanden bindet, steht
/// hier nicht* -- sie steht in Abschnitt E, bei der Flaeche.
#[derive(Debug, Clone)]
pub struct Stelle {
    /// Die Funktion, in deren Rumpf der Ruf steht.
    pub rufer: String,
    /// Der gerufene fremde Rumpf.
    pub gerufener: String,
    /// Der Ruf im Quelltext -- fuer die Zeilennummer.
    pub span: Span,
    /// Die Klausel, so wie der Pruefer sie gelesen hat.
    pub klausel: String,
    pub wirkung: Wirkung,
}

/// **Abschnitt F des Zeugnisses -- je Stelle eine Zeile, ohne Werkzeug lesbar.**
///
/// `quelle` ist der Quelltext derselben Einheit; ohne ihn gaebe es keine Zeilennummer, und
/// eine Fundstelle ohne Zeile ist eine Meinung.
pub fn zeige(stellen: &[Stelle], quelle: &str) -> String {
    let mut aus = String::new();
    if stellen.is_empty() {
        return aus;
    }
    let index = gabbro_syntax::span::Zeilenindex::neu(quelle);
    aus.push_str(
        "\nF  FOREIGN CONTRACTS THAT NARROWED -- a foreign `ensures` became a FACT here\n",
    );
    aus.push_str(
        "   Not the clauses that exist -- the ones that MOVED something. A contract on a\n\
        \x20  body Gabbro never sees is an assumption, and this is where it reaches the\n\
        \x20  product: a narrower range passes checks a wider one would not.\n",
    );
    for s in stellen {
        let stelle = index.stelle(quelle, s.span.von);
        aus.push_str(&format!(
            "     {:<6} {} -> {:<24} {:<9} {}\n",
            format!("{}:", stelle.zeile),
            s.rufer,
            s.gerufener,
            s.wirkung.marke(),
            s.klausel
        ));
        if let Wirkung::Bereich { vorher, nachher } = &s.wirkung {
            aus.push_str(&format!("            {vorher}  ->  {nachher}\n"));
        }
    }
    aus.push_str(
        "   What does NOT stand here: `M115` reads the callee's `requires` and REFUSES.\n\
        \x20  That is the other direction of the same contract and NOT the same class --\n\
        \x20  a wrong precondition can reject a correct program, never admit a wrong one.\n",
    );
    aus
}

#[cfg(test)]
mod proben {
    use super::*;

    fn lies_ensures(quelle: &str) -> Vec<Pred> {
        let (baum, absagen) = gabbro_syntax::lies("probe.gab", quelle);
        assert_eq!(absagen.fehler_zahl(), 0, "{}", absagen.zeige(quelle));
        let mut aus = Vec::new();
        crate::fuer_jedes_item(&baum, &mut |i| {
            if let ItemArt::Funktion(f) = &i.art {
                if !f.ensures.is_empty() {
                    aus = f.ensures.clone();
                }
            }
        });
        aus
    }

    /// **Eine Klausel, die nichts bewegt, ist kein Schritt.** Das ist der ganze Gegenstand
    /// des Postens: `u32 in 0 .. 100` mit `ensures result <= 100` steht da und bindet
    /// niemanden.
    #[test]
    fn eine_klausel_ohne_wirkung_zaehlt_nicht() {
        let e = lies_ensures(
            "extern fn hole() -> u32 in 0 .. 100\n    ensures result <= 100\n    effects { pure }\n    costs <= 1 ops;\n",
        );
        let roh = Typ::Ganzzahl(IntBereich::genau(32, false, 0, 100));
        let v = bereich_aus_ensures(&roh, &e);
        assert!(v.schritte.is_empty(), "{:?}", v.schritte);
        assert_eq!(v.typ.text(), roh.text());
    }

    /// Und die Gegenrichtung: dieselbe Klausel an einem WEITEREN Bereich bewegt etwas, und
    /// dann steht sie mit Vorher und Nachher da.
    #[test]
    fn eine_klausel_mit_wirkung_nennt_vorher_und_nachher() {
        let e = lies_ensures(
            "extern fn hole() -> u32\n    ensures result <= 100\n    effects { pure }\n    costs <= 1 ops;\n",
        );
        let roh = Typ::Ganzzahl(IntBereich::voll(32, false));
        let v = bereich_aus_ensures(&roh, &e);
        assert_eq!(v.schritte.len(), 1, "{:?}", v.schritte);
        assert_eq!(v.schritte[0].klausel, "result <= 100");
        assert_eq!(v.schritte[0].vorher, "u32");
        assert_eq!(v.schritte[0].nachher, "u32 in 0 .. 100");
        assert_eq!(v.typ.text(), "u32 in 0 .. 100");
    }

    /// **Ein leerer Bereich verengt NICHT** -- er ist ein Widerspruch, und den meldet diese
    /// Funktion nicht. *Wenn sie schweigt, muss auch die Zaehlung schweigen*, sonst zaehlt
    /// das Zeugnis eine Wirkung, die es nicht gab.
    #[test]
    fn ein_widerspruch_ist_keine_verengung() {
        let e = lies_ensures(
            "extern fn hole() -> u32 in 0 .. 10\n    ensures result >= 50\n    effects { pure }\n    costs <= 1 ops;\n",
        );
        let roh = Typ::Ganzzahl(IntBereich::genau(32, false, 0, 10));
        let v = bereich_aus_ensures(&roh, &e);
        assert!(v.schritte.is_empty(), "{:?}", v.schritte);
        assert_eq!(v.typ.text(), roh.text());
    }
}
