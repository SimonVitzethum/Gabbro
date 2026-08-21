//! **Das Pflichtenregister -- P6, die Messsonde (2026-08-19).**
//!
//! Die Kennzahl dieses Ordners ist am 2026-08-19 zurueckgezogen worden: sie war an
//! **Verus**-Zeilen gemessen, und Gabbro beweist in Isabelle/HOL. Die neue Buchung lautet
//! `unbekannt, > 0,5`. **Was zwischen den beiden Zustaenden liegt, ist nicht ein Ablesefehler,
//! sondern P6** -- die *erzeugte* Verfeinerungspflicht.
//!
//! ## Warum das der erste Schritt ist und nicht der letzte
//!
//! Ein Isabelle-verankertes `w` braucht **eine W-Pflicht, die ENTSTANDEN ist.** Ohne P6
//! muesste man sich eine ausdenken -- und was man erfindet, bevor man es misst, ist die
//! Bewegung, gegen die R7 und W3 stehen.
//!
//! **Dieses Modul loest keine Pflicht ein. Es ZAEHLT sie.** Und Zaehlen ist der Schritt, der
//! den Abstand zu 0,5 ueberhaupt sichtbar macht:
//!
//! ```text
//! E  Erhaltung     je `maintains I` an einem `impl fn`: I(vorher) und requires  =>  I(nachher)
//! N  Nachbedingung je `ensures P` an einem Rumpf, den Gabbro sieht
//! F  Fremdpflicht  je `ensures P` an einem Rumpf, den Gabbro NICHT sieht
//! ```
//!
//! ## Und die Grenze steht im selben Satz
//!
//! **Eine gezaehlte Pflicht ist keine bewiesene.** Das Register sagt, was ein Mensch schuldet,
//! nicht dass er es geleistet hat. *Es ist die Gegenrichtung zum Zeugnis:* jenes zaehlt auf,
//! worauf die Uebersetzung ruht, dieses, was der Programmierer noch schuldet.
//!
//! **Die K/A/W-Einordnung steht ausdruecklich NICHT hier.** Sie ist ein Urteil -- die
//! Kipp-Regeln verlangen je Pflicht einen Satz Begruendung, und ein Werkzeug, das raet, waere
//! genau die stille Antwort, gegen die dieser Ordner sonst schreibt. *Gezaehlt wird die ART,
//! geurteilt wird von Hand.*

use gabbro_syntax::ast::*;

pub struct Pflicht {
    pub art: Art,
    pub funktion: String,
    pub gegenstand: String,
    /// Hat Gabbro den Rumpf? *Ohne Rumpf ist die Pflicht eine ANNAHME ueber Fremdcode.*
    pub rumpf_da: bool,
}

#[derive(PartialEq, Eq, Clone, Copy)]
pub enum Art {
    Erhaltung,
    Nachbedingung,
    Fremdpflicht,
    /// **`V` -- die Vorbedingung am RUFORT, und sie fehlte in diesem Register (2026-08-20).**
    ///
    /// `M115` weist ab, wo der Bereich des Arguments die Vorbedingung **ausschliesst**, und
    /// schweigt sonst. *Eine untere Schranke, und sie steht als solche da.* **Was das
    /// Register bis heute verschwieg: die Gegenseite dieser Schranke ist keine leere Menge.**
    /// Jede Rufstelle einer Funktion mit `requires` traegt eine Bedingung, die der Rufer
    /// herstellen muesste und die niemand nachhaelt.
    ///
    /// > Die starke Fassung von `M115` -- *der Rufer BEWEIST die Vorbedingung* -- braucht eine
    /// > Entscheidungsprozedur, und M1 hat keine: er stellt Fakten HER, er entscheidet keine
    /// > Praedikate. **Solange sie fehlt, ist diese Zahl der Preis**, und ein Preis, der
    /// > nirgends steht, sieht aus wie null.
    ///
    /// *Sie steht bewusst NEBEN `E`/`N`/`F` und nicht in ihnen:* jene drei sind Pflichten,
    /// die eine Deklaration ERZEUGT, diese eine, die ein Ruf VERERBT. Die Zahl waechst mit
    /// den Rufstellen, nicht mit den Deklarationen.
    Vorbedingung,
}

impl Art {
    pub fn marke(self) -> &'static str {
        match self {
            Art::Erhaltung => "E",
            Art::Nachbedingung => "N",
            Art::Fremdpflicht => "F",
            Art::Vorbedingung => "V",
        }
    }
    pub fn name(self) -> &'static str {
        match self {
            Art::Erhaltung => "Preservation",
            Art::Nachbedingung => "Postcondition",
            Art::Fremdpflicht => "Foreign duty",
            Art::Vorbedingung => "Precondition at the call site",
        }
    }
}

pub fn sammle(baum: &Programm) -> Vec<Pflicht> {
    let mut aus = Vec::new();
    lauf(&baum.items, &mut aus);
    vorbedingungen(baum, &mut aus);
    aus
}

/// **Jede Rufstelle einer Funktion mit `requires` -- gezaehlt, nicht entschieden.**
///
/// Gemessen 2026-08-20, ausgeloest von der Buchung *„vorher zaehlen, an wie vielen Rufstellen
/// eine Vorbedingung heute unbewiesen bleibt"*. Die Zahl ist der Preis der schwachen Fassung
/// von `M115`: was dort schweigt, steht hier.
///
/// **Die Zahl ist eine OBERE Schranke der offenen Pflichten und eine UNTERE der Rufstellen.**
/// Obere, weil manche Vorbedingung am Rufort trivial gilt (`requires n < 8` mit `n : u32 in
/// 0 .. 7`) -- das entscheidet heute nichts, also zaehlt es mit. Untere, weil ein Ruf, dessen
/// Pfad sich nicht aufloest, gar nicht erst gefunden wird. *Beide Richtungen benannt, sonst
/// waere sie ein Urteil im Gewand einer Messung (W19).*
fn vorbedingungen(baum: &Programm, aus: &mut Vec<Pflicht>) {
    let u = crate::umgebung::Umgebung::sammle(baum);
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let ItemArt::Funktion(f) = &item.art else { return };
        if f.klasse == Some(FnKlasse::Spec) {
            return;
        }
        let FnRumpf::Block(b) = &f.rumpf else { return };
        let mut rufe = Vec::new();
        rufe_im_block(b, &mut rufe);
        for r in rufe {
            let Some(sig) = r.path().and_then(|p| u.funktion(modul, p)) else { continue };
            for (n, _) in sig.requires.iter().enumerate() {
                aus.push(Pflicht {
                    art: Art::Vorbedingung,
                    funktion: f.name.text.clone(),
                    gegenstand: format!("{} requires #{}", r.target_text(), n + 1),
                    rumpf_da: sig.rumpf_da,
                });
            }
        }
    });
}

/// Jeder Ruf eines Blocks, samt Unterbloecken und Unterausdruecken.
///
/// *Ohne `unterbloecke` faende die Zaehlung nur die oberste Ebene* -- und ein Ruf unter einer
/// Sperre oder in einem `observes`-Block ist derselbe Ruf. **Dieselbe Lehre wie `pruefe-
/// abstieg.py`, nur an einer Zaehlung statt an einem Pass.**
fn rufe_im_block<'a>(b: &'a Block, aus: &mut Vec<&'a Ruf>) {
    for s in &b.anweisungen {
        if let StmtArt::Ruf(r) = &s.art {
            aus.push(r);
        }
        for e in crate::eigene_ausdruecke(s) {
            for x in crate::alle_ausdruecke(e) {
                if let ExprArt::Ruf(r) = &x.art {
                    aus.push(r);
                }
            }
        }
        for k in crate::unterbloecke(s) {
            rufe_im_block(k, aus);
        }
    }
}

fn lauf(items: &[Item], aus: &mut Vec<Pflicht>) {
    for item in items {
        match &item.art {
            ItemArt::Modul(m) => lauf(&m.items, aus),
            ItemArt::Funktion(f) => {
                // Eine `spec fn` schuldet nichts -- sie IST die Aussage (`M113`).
                if f.klasse == Some(FnKlasse::Spec) {
                    continue;
                }
                let rumpf_da = matches!(f.rumpf, FnRumpf::Block(_));
                for i in &f.maintains {
                    aus.push(Pflicht {
                        art: Art::Erhaltung,
                        funktion: f.name.text.clone(),
                        gegenstand: i.text.clone(),
                        rumpf_da,
                    });
                }
                for (n, _) in f.ensures.iter().enumerate() {
                    aus.push(Pflicht {
                        art: if rumpf_da { Art::Nachbedingung } else { Art::Fremdpflicht },
                        funktion: f.name.text.clone(),
                        gegenstand: format!("ensures #{}", n + 1),
                        rumpf_da,
                    });
                }
            }
            _ => {}
        }
    }
}

pub fn zeige(baum: &Programm, datei: &str) -> String {
    let p = sammle(baum);
    let mut s = String::new();
    s.push_str(&format!("-- Obligation register: {datei}\n"));
    s.push_str("-- What a HUMAN still owes here. Counted, not discharged.\n\n");
    if p.is_empty() {
        s.push_str("   no generated proof obligation in this unit\n\n");
    }
    for art in [Art::Erhaltung, Art::Nachbedingung, Art::Fremdpflicht, Art::Vorbedingung] {
        let eigene: Vec<&Pflicht> = p.iter().filter(|x| x.art == art).collect();
        if eigene.is_empty() {
            continue;
        }
        s.push_str(&format!("{}  {} ({})\n", art.marke(), art.name(), eigene.len()));
        for x in &eigene {
            s.push_str(&format!("     {} :: {}\n", x.funktion, x.gegenstand));
        }
        s.push('\n');
    }
    let e = p.iter().filter(|x| x.art == Art::Erhaltung).count();
    let n = p.iter().filter(|x| x.art == Art::Nachbedingung).count();
    let f = p.iter().filter(|x| x.art == Art::Fremdpflicht).count();
    let v = p.iter().filter(|x| x.art == Art::Vorbedingung).count();
    s.push_str(&format!(
        "== {} obligations: {e} preservation, {n} postcondition, {f} foreign, \
         {v} precondition ==\n",
        p.len()
    ));
    s.push_str("   And what that does NOT mean: a counted obligation is not a proved one.\n");
    s.push_str("   The K/A/W classification is a JUDGEMENT and deliberately does not stand here --\n");
    s.push_str("   the tipping rules demand one sentence of reasoning per obligation.\n");
    if f > 0 {
        s.push_str(&format!(
            "   The {f} foreign ones sit at bodies Gabbro never sees: they are\n\x20\
                ASSUMPTIONS about foreign code and do not dissolve even under\n\x20  \"all \
                of Gabbro verified\".\n"
        ));
    }
    if v > 0 {
        s.push_str(&format!(
            "   The {v} preconditions are the price of the WEAK reading of `M115`: it\n   \
                refuses only where the range of the argument EXCLUDES the condition, and\n   \
                is silent otherwise. Silence is not confirmation -- these sites are\n   \
                counted, not settled.\n"
        ));
    }
    s
}

/// **Wie viele Rufe ruhen auf einem fremden Vertrag? -- Punkt 4, 2026-08-19.**
///
/// Seit heute verengt die Nachbedingung eines Gerufenen sein Ergebnis beim Rufer
/// (`m1::aus_ensures`). Bei einem `impl fn` ist das eine Ableitung, die Gabbro einmal selbst
/// nachrechnen wird; **bei einem `extern fn` ist es Glaube.**
///
/// > *Wer nicht pruefen kann, EXPORTIERT.* Dieselbe Konstruktion wie die `entrust`-Zeile in
/// > Abschnitt E des Zeugnisses -- eine Vertrauensflaeche, die gezaehlt dasteht statt
/// > stillschweigend zu wirken.
pub fn fremde_vertraege(baum: &Programm) -> Vec<String> {
    let mut aus = Vec::new();
    sammle_vertraege(&baum.items, &mut aus);
    aus
}

fn sammle_vertraege(items: &[Item], aus: &mut Vec<String>) {
    for item in items {
        match &item.art {
            ItemArt::Modul(m) => sammle_vertraege(&m.items, aus),
            ItemArt::Funktion(f) => {
                if matches!(f.rumpf, FnRumpf::Block(_)) || f.ensures.is_empty() {
                    continue;
                }
                aus.push(f.name.text.clone());
            }
            _ => {}
        }
    }
}
