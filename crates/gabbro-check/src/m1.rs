//! **Pass 3 -- M1 und die drei Flussregeln V1–V3.**
//!
//! > *„Jede Operation muss im Bereich ihres Ergebnistyps bleiben; passt `a + b` nicht ins
//! > Ziel, ist das ein **Uebersetzungsfehler, keine Laufzeitpruefung**. Division und Rest
//! > verlangen einen Nenner, dessen Bereich die Null ausschliesst."*
//! > ([`SPRACHE.md`](SPRACHE.md) §3)
//!
//! Und die Gegenmessung -- 255 Subtraktionen, 102 flusssensitiv -- hat gezeigt, dass *eine*
//! Regel nicht reicht und `narrow` allein zum Ritual wuerde. Es gibt genau **drei**:
//!
//! | | Regel |
//! |---|---|
//! | **V1** | eine geprüfte **Bereichsbedingung** verengt den Bereich der geprüften Stelle im Zweig danach |
//! | **V2** | eine geprüfte **Beziehung zweier Stellen** wird zum Zweigfakt: unter `a >= b` hat `a - b` den Typ `0 .. a.max − b.min` |
//! | **V3** | ein `match` auf einen `tagged`-Typ verengt im Zweig auf die Variante samt Nutzlast |
//!
//! **Syntaxgesteuert, ohne Fixpunkt, ohne Loeser.** Der Pass fuehrt je Block eine
//! Faktenmenge, die nur an den drei benannten Stellen waechst und bei **jedem Schreiben auf
//! eine beteiligte Stelle stirbt**. Schleifen tragen keine Fakten hinein.
//!
//! ## Was dieser Pass NICHT tut, und es steht hier statt in einer Fussnote
//!
//! * **Er prueft Rümpfe, keine Praedikate.** `requires`, `ensures` und `invariant` sind
//!   Geisterausdruecke ohne Laufzeitwirkung; sie gehoeren dem Beweiser, nicht M1.
//! * **Er kennt keine Aufrufwirkung auf lokale Werte** -- er braucht sie auch nicht: Gabbro
//!   hat keinen Adressoperator, also kann ein Gerufener eine lokale Groesse nicht aendern.
//!   Alles **Nichtlokale** verliert seine Fakten bei jedem Aufruf.
//! * **Er zaehlt, was er nicht weiss.** Jeder Ausdruck ohne Typ geht in die Zaehlung; ein
//!   Lauf ohne diese Zahl sieht aus wie Deckung.

use crate::typen::{self, IntBereich, Typ};
use crate::umgebung::Umgebung;
use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};
use gabbro_syntax::span::Span;
use std::collections::HashMap;

/// Was der Pass angesehen hat -- die Zahl steht neben dem Ergebnis.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Zaehlung {
    pub typisiert: usize,
    pub unbekannt: usize,
}

impl Zaehlung {
    pub fn gesamt(&self) -> usize {
        self.typisiert + self.unbekannt
    }

    pub fn deckung(&self) -> f64 {
        if self.gesamt() == 0 {
            return 0.0;
        }
        100.0 * self.typisiert as f64 / self.gesamt() as f64
    }
}

/// Ein Zweigfakt. Er lebt bis zum naechsten Schreiben auf eine beteiligte Stelle.
#[derive(Debug, Clone)]
enum Fakt {
    /// V1 -- die Stelle liegt in diesem Bereich.
    Bereich {
        schluessel: String,
        /// Die Namen, die in den Indizes des Schluessels stehen (U3).
        indizes: Vec<String>,
        min: i128,
        max: i128,
    },
    /// **«F»: die Stelle ist nicht NaN und/oder nicht unendlich.**
    ///
    /// **Keine Bereichsverfeinerung, und das ist der Punkt:** Endlichkeit ist im Gitter kein
    /// Intervall. NaN liegt in KEINEM Intervall, und dieselbe Aussage ist trotzdem nicht
    /// „der Bereich ist enger". Zwei Bits, die unabhaengig geloescht werden koennen.
    ///
    /// *Der Bedarfsbeleg ist eine Disjunktion* (`FRAGMENTE.md`, «F0»/FF1): der Fluchttest
    /// eines echten Renderers lautet `Zz2 < ER2 || isnan(de.x) || isinf(de.x) || …`, und im
    /// Nein-Zweig fallen beide Bits gleichzeitig.
    Endlich {
        schluessel: String,
        indizes: Vec<String>,
        nan: bool,
        unendlich: bool,
    },
    /// **«F»: die Stelle liegt in diesem Gleitkommaintervall.**
    ///
    /// Getrennt von `Bereich`, weil die Grenzen keine ganzen Zahlen sind -- und getrennt von
    /// `Endlich`, weil ein Intervall die zwei Bits nicht ersetzt: *mit NaN im Wertebereich
    /// ist der Vergleich keine totale Ordnung, und ohne totale Ordnung ist ein
    /// Intervallverband kein Verband.* Die zwei Bits sind die Voraussetzung dieser Zusage,
    /// nicht ihre kleinere Schwester.
    FIntervall {
        schluessel: String,
        indizes: Vec<String>,
        lo: f64,
        hi: f64,
    },
    /// V2 -- die Beziehung zweier Stellen, ausschliesslich als Vergleich.
    Beziehung {
        links: String,
        op: BinOp,
        rechts: String,
        indizes: Vec<String>,
    },
}

pub fn pass(baum: &Programm, absagen: &mut Absagen) -> Zaehlung {
    let umgebung = Umgebung::sammle(baum);
    let mut p = Pruefer {
        u: &umgebung,
        absagen,
        zaehlung: Zaehlung::default(),
        modul: String::new(),
    };
    p.programm(baum);
    p.zaehlung
}

struct Pruefer<'a> {
    u: &'a Umgebung,
    absagen: &'a mut Absagen,
    zaehlung: Zaehlung,
    /// Das Modul, in dem der gerade gepruefte Rumpf steht. **Ohne ihn loest der Pass Namen
    /// im Blindflug auf** -- und ein gleichnamiges `fn` in einem fremden Modul loescht eine
    /// Bereichspruefung, ohne dass jemand es sieht (Gegenpruefung 2026-08-14, U11/U12).
    modul: String,
}

/// Die Bindungen und Fakten eines Blocks. Ein Block erbt beide und gibt keins zurueck.
#[derive(Clone, Default)]
struct Lage {
    lokal: HashMap<String, Typ>,
    fakten: Vec<Fakt>,
}

impl<'a> Pruefer<'a> {
    fn programm(&mut self, baum: &Programm) {
        crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
            // **M1 sah bis 2026-08-18 NUR Funktionsruempfe.** Das fiel an «F» auf, und zwar
            // an der teuersten denkbaren Stelle: `F002` biss im Rumpf und schwieg in der
            // `const`-Deklaration -- *also genau dort, wo der Bedarfsbeleg herkam.*
            //
            // Die 53 inexakten Literale, die F0 an einem echten Renderer gemessen hat, sind
            // ln 2, 2 pi, Schwellwerte. **Die leben in Konstanten.** Eine Regel, die ueberall
            // beisst ausser am Hauptschauplatz, ist keine Stichprobe -- sie ist umgekehrt
            // gemessen.
            //
            // *Ein Initialisierer wird mit LEERER Lage geprueft: er hat keine Parameter und
            // keine Fakten, nur die Umgebung.*
            if let ItemArt::Konst(k) = &item.art {
                self.modul = modul.to_string();
                let ziel = self.u.typ_von_ausdruck_decl(modul, &k.typ);
                let mut lage = Lage::default();
                let quelle = self.ausdruck(&k.wert, &mut lage);
                self.passt(&quelle, &ziel, k.wert.span, "die Konstante");
            }
            // **`F004` -- und der Bedarfsbeleg steht im Korpus, nicht in einer Vorsorge.**
            //
            // «F0»/FF3 zeigt eine Gleitkommareduktion in echtem Code: `a += progress[i]`
            // ueber ein Feld. Genau die Form, fuer die `accumulates` da ist -- und ueber
            // Gleitkomma ist sie REIHENFOLGEABHAENGIG.
            //
            // `accumulates.monoid` ist BEWIESEN, unter der Praemisse, dass die Merge-Menge
            // ein kommutatives Monoid ist. Der Eintrag sagt, warum das mechanisch pruefbar
            // ist: der Wortschatz ist geschlossen. **Das ist die halbe Wahrheit** -- er
            // reicht nur, weil alle Zahlentypen ganzzahlig sind. Ueber `f64` ist `add` nicht
            // assoziativ und `max` mit NaN kein Verband, und
            // `faltung_ist_reihenfolgeunabhaengig` verlangt beides.
            //
            // *Der Satz bliebe wahr und seine Praemisse wuerde falsch.* Also weigert sich der
            // Pruefer, statt eine bewiesene Schablone ueber einen Fall zu spannen, den sie
            // nicht traegt.
            if let ItemArt::Accumulates(a) = &item.art {
                self.modul = modul.to_string();
                let t = self.u.typ_von_ausdruck_decl(modul, &a.typ);
                if matches!(t.durchgreifen(), Typ::Gleitkomma(_)) {
                    self.absagen.schiebe(
                        Absage::fehler(
                            "F004",
                            a.name.span,
                            format!(
                                "`accumulates {}` ueber einem Gleitkommatyp -- die Faltung \
                                 waere reihenfolgeabhaengig",
                                a.name.text
                            ),
                        )
                        .mit_notiz(
                            "die Absenkung faltet eine Zelle je Kern in einer Reihenfolge, \
                             die niemand festlegt; `add` ist ueber Gleitkomma nicht \
                             assoziativ und `max` mit NaN kein Verband",
                        )
                        .mit_notiz(
                            "`accumulates.monoid` ist BEWIESEN -- unter der Praemisse, dass \
                             die Merge-Menge ein kommutatives Monoid ist. Hier waere sie es \
                             nicht, und der Satz haette eine falsche Praemisse",
                        ),
                    );
                }
            }
            if let ItemArt::Statisch(st) = &item.art {
                self.modul = modul.to_string();
                let ziel = self.u.typ_von_ausdruck_decl(modul, &st.typ);
                let mut lage = Lage::default();
                let quelle = self.ausdruck(&st.wert, &mut lage);
                self.passt(&quelle, &ziel, st.wert.span, "der statische Wert");
            }
            if let ItemArt::Funktion(f) = &item.art {
                // Nur Ruempfe: Praedikate haben keine Laufzeitwirkung.
                if let FnRumpf::Block(b) = &f.rumpf {
                    self.modul = modul.to_string();
                    let mut lage = Lage::default();
                    for prm in &f.parameter {
                        let t = self.u.typ_von_ausdruck_decl(modul, &prm.typ);
                        lage.lokal.insert(prm.name.text.clone(), t);
                    }
                    let ergebnis = f
                        .ergebnis
                        .as_ref()
                        .map(|t| self.u.typ_von_ausdruck_decl(modul, t));
                    self.block(b, &mut lage, ergebnis.as_ref());
                }
            }
        });
    }

    // -- Anweisungen --------------------------------------------------------------------

    fn block(&mut self, b: &Block, lage: &mut Lage, ergebnis: Option<&Typ>) {
        for s in &b.anweisungen {
            self.anweisung(s, lage, ergebnis);
        }
    }

    /// **U1.** Ein Unterblock bekommt eine Kopie der Lage -- seine Schreibzugriffe muessen
    /// die Fakten des UMGEBENDEN Blocks trotzdem toeten. Sonst ueberlebt ein Fakt jedes
    /// Schreiben, das in einem `if`/`match`/Schleifen-/`locks`-Rumpf steht, und
    /// `SPRACHE.md` §3.2 -- *„stirbt bei jedem Schreiben auf eine beteiligte Stelle"* --
    /// ist an dieser Stelle falsch.
    fn unterblock(&mut self, b: &Block, aussen: &mut Lage, ergebnis: Option<&Typ>) {
        let mut innen = aussen.clone();
        self.block(b, &mut innen, ergebnis);
        self.geschriebenes_toeten(b, aussen);
    }

    fn geschriebenes_toeten(&mut self, b: &Block, aussen: &mut Lage) {
        let mut ziele = Vec::new();
        sammle_schreibziele(b, &mut ziele);
        for z in ziele {
            self.schreiben_toetet_fakten(&z, aussen);
        }
    }

    fn anweisung(&mut self, s: &Stmt, lage: &mut Lage, ergebnis: Option<&Typ>) {
        match &s.art {
            StmtArt::Let(l) => {
                let wert = self.ausdruck(&l.wert, lage);
                self.rufe_im_ausdruck(&l.wert, lage);
                let ziel = l.typ.as_ref().map(|t| self.u.typ_von_ausdruck_decl(&self.modul, t));
                if let Some(z) = &ziel {
                    self.passt(&wert, z, l.wert.span, "die Bindung");
                }
                // U2: die neue Bindung verdeckt die alte -- jeder Fakt ueber den Namen
                // stirbt, sonst erbt die Verdeckung die Verengung ihres Vorgaengers.
                lage.fakten
                    .retain(|f| !nennt_namen(f, &l.name.text));
                lage.lokal
                    .insert(l.name.text.clone(), ziel.unwrap_or(wert));
            }
            StmtArt::LetSonst(l) => {
                let t = match l.als_ruf() {
                    Some(r) => self.ruf(r, lage),
                    None => crate::typen::Typ::Unbekannt,
                };
                lage.fakten.retain(|f| !nennt_namen(f, &l.name.text));
                lage.lokal.insert(l.name.text.clone(), t);
                self.aufruf_toetet_fakten(lage);
                self.unterblock(&l.sonst, lage, ergebnis);
            }
            StmtArt::Zuweisung(z) => {
                // U9: M4 gilt auf BEIDEN Seiten. Ein Schreiben ausserhalb der Schranken ist
                // die gefaehrlichere Richtung, und sie lief hier am Index vorbei.
                self.index_pruefen(&z.ziel, lage);
                let ziel = self.u.typ_von_ort(&self.modul, &z.ziel, &lage.lokal);
                self.buche(&ziel);
                let quelle = self.ausdruck(&z.wert, lage);
                self.rufe_im_ausdruck(&z.wert, lage);
                let ergebnis_typ = match z.op {
                    ZuwOp::Setzt => quelle,
                    // `a += b` ist `a = a + b`. Das GELESENE `a` traegt seine Fakten (V1/V2),
                    // das geschriebene seinen deklarierten Bereich -- ohne diese Trennung
                    // sieht `if z >= 1 { z -= 1; }` aus wie `z -= 1`.
                    op => {
                        let gelesen = self.mit_fakt(&z.ziel, ziel.clone(), lage);
                        self.rechnung_zuweisung(&gelesen, &quelle, op, &z.ziel, z.wert.span)
                    }
                };
                // Ein `wrapping`-Slot hat seinen Ueberlauf DEKLARIERT; dort ist er kein Befund.
                if !ziel.laeuft_um() {
                    self.passt(&ergebnis_typ, &ziel, z.wert.span, "die Zuweisung");
                }
                self.schreiben_toetet_fakten(&z.ziel, lage);
            }
            StmtArt::Publish(p) => {
                self.index_pruefen(&p.ziel, lage);
                let ziel = self.u.typ_von_ort(&self.modul, &p.ziel, &lage.lokal);
                self.buche(&ziel);
                let quelle = self.ausdruck(&p.wert, lage);
                self.rufe_im_ausdruck(&p.wert, lage);
                self.passt(&quelle, &ziel, p.wert.span, "die Veroeffentlichung");
                self.schreiben_toetet_fakten(&p.ziel, lage);
            }
            StmtArt::Wenn(w) => {
                for (bedingung, rumpf) in &w.zweige {
                    let _ = self.ausdruck(bedingung, lage);
                    self.rufe_im_ausdruck(bedingung, lage);
                    let mut innen = lage.clone();
                    // V1 und V2: die geprueften Stellen sind im Zweig danach enger.
                    self.fakten_aus(bedingung, false, &mut innen);
                    self.block(rumpf, &mut innen, ergebnis);
                    self.geschriebenes_toeten(rumpf, lage);
                }
                if let Some(sonst) = &w.sonst {
                    let mut innen = lage.clone();
                    if let Some((bedingung, _)) = w.zweige.first() {
                        self.fakten_aus(bedingung, true, &mut innen);
                    }
                    self.block(sonst, &mut innen, ergebnis);
                    self.geschriebenes_toeten(sonst, lage);
                }
                // **V1 gilt auch fuer den Weg NACH einem Zweig, der immer verlaesst.**
                // `if a >= b { return a - b; }` -- was danach kommt, ist genau der Fall
                // `a < b`, und zwar syntaktisch, ohne Fixpunkt: der Zweig endet mit
                // `return`, `leave`, `next` oder einem Aufruf nach `never`. Ohne diese
                // Regel braucht der fruehe Rueckstieg ein `narrow`, und die Messlatte
                // („`narrow` <= 24 Fundstellen") faellt an einer Redewendung statt an der
                // Sprache.
                if w.sonst.is_none() && w.zweige.len() == 1 {
                    let (bedingung, rumpf) = &w.zweige[0];
                    if self.endet_immer(rumpf) {
                        self.fakten_aus(bedingung, true, lage);
                    }
                }
            }
            StmtArt::Match(m) => {
                let gegenstand = self.ausdruck(&m.gegenstand, lage);
                for zweig in &m.zweige {
                    let mut innen = lage.clone();
                    // V3: der Binder traegt die Nutzlast SEINER Variante.
                    if let (Some(binder), Typ::Summe { varianten, .. }) =
                        (&zweig.binder, gegenstand.durchgreifen())
                    {
                        let nutzlast = varianten
                            .iter()
                            .find(|(n, _)| *n == zweig.variante.text)
                            .and_then(|(_, t)| t.clone())
                            .unwrap_or(Typ::Unbekannt);
                        innen.lokal.insert(binder.text.clone(), nutzlast);
                    } else if let Some(binder) = &zweig.binder {
                        innen.lokal.insert(binder.text.clone(), Typ::Unbekannt);
                    }
                    self.block(&zweig.rumpf, &mut innen, ergebnis);
                    self.geschriebenes_toeten(&zweig.rumpf, lage);
                }
            }
            StmtArt::Narrow(n) => {
                let vorher = self.u.typ_von_ort(&self.modul, &n.ort, &lage.lokal);
                self.buche(&vorher);
                let mut innen = lage.clone();
                self.block(&n.sonst, &mut innen, ergebnis);
                self.geschriebenes_toeten(&n.sonst, lage);
                // U6: **der `else`-Zweig MUSS verlassen.** Ohne diese Pruefung installiert
                // ein leeres `else { }` denselben Bereich wie ein `else { return … }` --
                // und die Einengung gilt auf einem Weg, auf dem sie nie geprueft wurde.
                if !self.endet_immer(&n.sonst) {
                    self.absagen.schiebe(
                        Absage::fehler(
                            "M105",
                            n.sonst.span,
                            "the `else` branch of a `narrow` must return or diverge",
                        )
                        .mit_notiz(
                            "SYNTAX.md §7: `narrow place to range else { … }` ist eine \
                             Anweisung mit BENANNTEM Ausgang -- faellt der Zweig durch, \
                             gilt der eingeengte Bereich auf einem Weg, der ihn nie geprueft hat",
                        ),
                    );
                }
                // Der `else`-Zweig divergiert oder kehrt zurueck; danach gilt die Zusage.
                match &n.ziel {
                    NarrowZiel::Bereich(bereich) => {
                        // **«F»: dieselbe Anweisung, ein anderer Fakt.** Ist die Stelle ein
                        // Gleitkommawert, sind die Grenzen keine ganzen Zahlen -- und ein
                        // ganzzahliger Fakt darueber waere schlicht falsch.
                        let ist_gleit = matches!(
                            self.u
                                .typ_von_ort(&self.modul, &n.ort, &lage.lokal)
                                .durchgreifen(),
                            Typ::Gleitkomma(_)
                        );
                        if ist_gleit {
                            if let (Some(lo), Some(hi), Some((schluessel, indizes))) = (
                                self.u.gleitwert(&bereich.von),
                                self.u.gleitwert(&bereich.bis),
                                schluessel_und_indizes(&n.ort),
                            ) {
                                lage.fakten.push(Fakt::FIntervall {
                                    schluessel,
                                    indizes,
                                    lo,
                                    hi,
                                });
                            }
                            return;
                        }
                        let von = self.u.konst_wert(&self.modul, &bereich.von);
                        let bis = self.u.konst_wert(&self.modul, &bereich.bis);
                        if let (Some(lo), Some(hi), Some((schluessel, indizes))) =
                            (von, bis, schluessel_und_indizes(&n.ort))
                        {
                            let hi = if bereich.exklusiv { hi - 1 } else { hi };
                            lage.fakten.push(Fakt::Bereich {
                                schluessel,
                                indizes,
                                min: lo,
                                max: hi,
                            });
                        }
                    }
                    // **«F»: beide Bits auf einmal.** `finite` heisst nicht NaN UND nicht
                    // unendlich -- eine Pruefung, zwei Flanken. *Der `else`-Zweig ist der
                    // NaN-Weg, und damit steht in Gabbro als EINE Anweisung, was der Korpus
                    // von Hand als Disjunktion schreibt.*
                    NarrowZiel::Endlich(_) => {
                        if let Some((schluessel, indizes)) = schluessel_und_indizes(&n.ort) {
                            lage.fakten.push(Fakt::Endlich {
                                schluessel,
                                indizes,
                                nan: true,
                                unendlich: true,
                            });
                        }
                    }
                }
            }
            StmtArt::Bricht(b) => self.unterblock(&b.rumpf, lage, ergebnis),
            StmtArt::Sperrt(l) => self.unterblock(&l.rumpf, lage, ergebnis),
            StmtArt::Schleife(sch) => {
                // Schleifen tragen keine Fakten hinein -- die Invariante der Traversierung
                // tut das, und die gehoert dem Beweiser.
                let mut innen = Lage {
                    lokal: lage.lokal.clone(),
                    fakten: Vec::new(),
                };
                let rumpf = match sch.as_ref() {
                    Schleife::Traverse(t) => {
                        innen
                            .lokal
                            .insert(t.variable.text.clone(), Typ::Unbekannt);
                        if let Some(g) = &t.gegenstand {
                            let _ = self.ausdruck(g, lage);
                        }
                        &t.rumpf
                    }
                    Schleife::Retry(r) => {
                        let _ = self.ausdruck_opt(r.schranke.clone(), lage);
                        &r.rumpf
                    }
                    Schleife::Forever(f) => {
                        let _ = self.ausdruck_opt(f.je_durchgang.clone(), lage);
                        &f.rumpf
                    }
                };
                self.block(rumpf, &mut innen, ergebnis);
                self.geschriebenes_toeten(rumpf, lage);
            }
            StmtArt::Return(Some(e)) => {
                let t = self.ausdruck(e, lage);
                self.rufe_im_ausdruck(e, lage);
                if let Some(z) = ergebnis {
                    self.passt(&t, z, e.span, "die Rueckgabe");
                }
            }
            StmtArt::Ruf(r) => {
                let _ = self.ruf(r, lage);
                self.aufruf_toetet_fakten(lage);
            }
            StmtArt::AwaitLoad(a) => {
                let t = self.u.typ_von_ort(&self.modul, &a.quelle, &lage.lokal);
                self.buche(&t);
                lage.lokal.insert(a.name.text.clone(), t);
            }
            StmtArt::Exchange(e) => {
                let t = self.u.typ_von_ort(&self.modul, &e.ort, &lage.lokal);
                self.buche(&t);
                lage.lokal.insert(e.name.text.clone(), t.clone());
                if let XForm::Update { binder, rumpf } = &e.form {
                    let mut innen = lage.clone();
                    innen.lokal.insert(binder.text.clone(), t);
                    self.block(rumpf, &mut innen, ergebnis);
                }
                self.schreiben_toetet_fakten(&e.ort, lage);
            }
            StmtArt::Return(None) | StmtArt::Leave(_) | StmtArt::Next(_) => {}
        }
    }

    /// Verlaesst dieser Block seinen Weg immer? Rein syntaktisch, ohne Fixpunkt.
    fn endet_immer(&self, b: &Block) -> bool {
        let Some(letzte) = b.anweisungen.last() else {
            return false;
        };
        match &letzte.art {
            StmtArt::Return(_) | StmtArt::Leave(_) | StmtArt::Next(_) => true,
            // Ein Aufruf einer Funktion nach `never` kehrt nicht zurueck.
            StmtArt::Ruf(r) => {
                let name = r
                    .pfad
                    .teile
                    .last()
                    .map(|i| i.text.as_str())
                    .unwrap_or_default();
                matches!(
                    self.u.funktionen.get(name).and_then(|s| s.ergebnis.clone()),
                    Some(Typ::Nie)
                )
            }
            StmtArt::Wenn(w) => {
                w.sonst.as_ref().is_some_and(|s| self.endet_immer(s))
                    && w.zweige.iter().all(|(_, r)| self.endet_immer(r))
            }
            StmtArt::Match(m) => m.zweige.iter().all(|z| self.endet_immer(&z.rumpf)),
            _ => false,
        }
    }

    /// `a += b` rechnet im Bereich von `a` -- und genau dort faellt der Ueberlauf.
    fn rechnung_zuweisung(
        &mut self,
        ziel: &Typ,
        quelle: &Typ,
        op: ZuwOp,
        ort: &Ort,
        span: Span,
    ) -> Typ {
        let (Some(a), Some(b)) = (ziel.bereich(), quelle.bereich()) else {
            return Typ::Unbekannt;
        };
        let r = match op {
            ZuwOp::Plus => typen::addiere(&a, &b),
            ZuwOp::Minus => typen::subtrahiere(&a, &b),
            ZuwOp::Und => typen::bitweise(&a, &b, typen::BitOpArt::Und),
            ZuwOp::Oder => typen::bitweise(&a, &b, typen::BitOpArt::Oder),
            ZuwOp::Setzt => return quelle.clone(),
        };
        if r.laeuft_ueber && !ziel.laeuft_um() {
            self.ueberlauf(span, &a, &b, op_wort(op), ort);
        }
        match r.bereich {
            Some(b) => Typ::Ganzzahl(b),
            None => Typ::Unbekannt,
        }
    }

    // -- Ausdruecke ---------------------------------------------------------------------

    fn ausdruck_opt(&mut self, e: Expr, lage: &Lage) -> Typ {
        self.ausdruck(&e, lage)
    }

    fn ausdruck(&mut self, e: &Expr, lage: &Lage) -> Typ {
        let t = self.ausdruck_roh(e, lage);
        self.buche(&t);
        t
    }

    fn ausdruck_roh(&mut self, e: &Expr, lage: &Lage) -> Typ {
        match &e.art {
            ExprArt::Zahl(v) => match i128::try_from(*v) {
                Ok(w) => Typ::Ganzzahl(IntBereich::konstante(w)),
                Err(_) => Typ::Unbekannt,
            },
            // **«F»: ein Literal ist bekannt ENDLICH und nicht NaN.** Das ist der
            // Unterschied zu einem deklarierten Wert, und er ist der Grund, warum `narrow …
            // to finite` nur dort noetig ist, wo etwas GERECHNET oder UEBERGEBEN wurde.
            ExprArt::Gleitkomma {
                bits,
                dyadisch,
                gerundet,
            } => {
                // **`F002` -- und die Regel kam aus dem Korpus, nicht aus dem Entwurf.**
                //
                // Die geplante Fassung hiess „exakt darstellbar, sonst Absage". An 340
                // Literalen eines echten Renderers gemessen waeren damit 53 gefallen,
                // darunter ln 2 und 2 pi (`FRAGMENTE.md`, «F0»/FF4). Eine transzendente
                // Konstante ist in KEINER binaeren Breite exakt; ihre Dezimalform ist schon
                // eine Naeherung.
                //
                // *Verboten ist darum nicht das Inexakte, sondern das STILLSCHWEIGEND
                // Inexakte* -- genau der Satz, den `wrapping` ueber den Ueberlauf sagt.
                if !dyadisch && !gerundet {
                    self.absagen.schiebe(
                        Absage::fehler(
                            "F002",
                            e.span,
                            "this literal is not exactly representable in binary",
                        )
                        .mit_notiz(
                            "schreibe `rounded` dahinter, wenn die Rundung gemeint ist -- \
                             wie `wrapping` am Typ sagt sie: der Verlust ist ERKLAERT und \
                             darum kein Befund",
                        ),
                    );
                }
                let mut b = crate::typen::FBereich::punkt(f64::from_bits(*bits));
                b.gerundet = *gerundet;
                Typ::Gleitkomma(b)
            }
            ExprArt::Wahr | ExprArt::Falsch => Typ::Wahrheit,
            ExprArt::Ergebnis => Typ::Unbekannt,
            ExprArt::Klammer(i) => self.ausdruck_roh(i, lage),
            ExprArt::Ort(o) => {
                self.index_pruefen(o, lage);
                let grund = self.u.typ_von_ort(&self.modul, o, &lage.lokal);
                self.mit_fakt(o, grund, lage)
            }
            // `old(x)` ist ein Geisterausdruck: er steht in `ensures`, nicht im Rumpf.
            ExprArt::Alt(_) => Typ::Unbekannt,
            ExprArt::Ruf(r) => self.ruf_roh(r, lage),
            ExprArt::Eingebaut(_) => Typ::Unbekannt,
            ExprArt::Unaer(UnOp::Nicht, i) => {
                let _ = self.ausdruck(i, lage);
                Typ::Wahrheit
            }
            ExprArt::Unaer(UnOp::Negativ, i) => {
                let t = self.ausdruck(i, lage);
                match t.bereich() {
                    Some(b) => Typ::Ganzzahl(IntBereich::genau(
                        b.breite,
                        true,
                        -b.max,
                        -b.min,
                    )),
                    None => Typ::Unbekannt,
                }
            }
            ExprArt::Binaer(op, a, b) => self.binaer(*op, a, b, e.span, lage),
        }
    }

    fn binaer(&mut self, op: BinOp, a: &Expr, b: &Expr, span: Span, lage: &Lage) -> Typ {
        let ta = self.ausdruck(a, lage);
        let tb = self.ausdruck(b, lage);
        if op == BinOp::Und || op == BinOp::Oder {
            return Typ::Wahrheit;
        }
        // **«F»: Gleitkommaarithmetik antwortet heute mit dem VOLLEN Bereich.**
        //
        // Keine Fortpflanzung heisst nicht „keine Aussage", sondern die weiteste -- sonst
        // waere das Schweigen eine Zusage. `[0,1] + [0,1]` liegt in `[0,2]`, und ohne
        // Rechnung ist die einzige ehrliche Antwort: alles, NaN eingeschlossen.
        //
        // *Die Fortpflanzung muss NACH AUSSEN runden, wenn sie kommt* (`PLAN.md`, F3):
        // `[a,b] + [c,d]` ist `[RD(a+c), RU(b+d)]`. Mit Wirtsdoubles in RNE gerechnet waeren
        // die Schranken um bis zu ein Ulp zu ENG -- unsound in der Richtung, die nichts
        // meldet.
        if !op.ist_vergleich() {
            match (ta.durchgreifen().clone(), tb.durchgreifen().clone()) {
                (Typ::Gleitkomma(x), Typ::Gleitkomma(y)) => {
                    return match op {
                        BinOp::Plus => Typ::Gleitkomma(x.plus(y)),
                        BinOp::Minus => Typ::Gleitkomma(x.minus(y)),
                        BinOp::Mal => Typ::Gleitkomma(x.mal(y)),
                        BinOp::Geteilt => Typ::Gleitkomma(x.geteilt(y)),
                        // **`F005`: eine Verknuepfung, die es fuer Gleitkomma nicht gibt.**
                        // Sie stillschweigend mit dem vollen Bereich zu beantworten waere
                        // eine Erlaubnis -- dieselbe Bauart wie `opaque` vor `D003`.
                        _ => {
                            self.absagen.schiebe(
                                Absage::fehler(
                                    "F005",
                                    span,
                                    "diese Verknuepfung gibt es fuer Gleitkomma nicht",
                                )
                                .mit_notiz(
                                    "Bitverknuepfung, Schieben und Rest sind Aussagen ueber \
                                     ein Bitmuster; ein Gleitkommawert IST eines, aber seine \
                                     Bedeutung ist keine",
                                ),
                            );
                            Typ::Unbekannt
                        }
                    };
                }
                // **Breitenmischung mit einer Ganzzahl gibt es nicht ohne Umwandlung** -- und
                // eine Umwandlungsform steht noch nicht da.
                (Typ::Gleitkomma(x), _) | (_, Typ::Gleitkomma(x)) => {
                    let _ = x;
                    self.absagen.schiebe(
                        Absage::fehler(
                            "F005",
                            span,
                            "Gleitkomma und Ganzzahl in einer Verknuepfung",
                        )
                        .mit_notiz(
                            "es gibt keine Umwandlungsform; eine stillschweigende waere \
                             genau die Stelle, an der nicht dransteht, dass gerundet wurde",
                        ),
                    );
                    return Typ::Unbekannt;
                }
                _ => {}
            }
        }
        if op.ist_vergleich() {
            return Typ::Wahrheit;
        }
        // **`D003` -- ein undurchsichtiger Typ hat KEINE Rechnung seines Traegers.**
        //
        // Gemessen am 2026-08-18, und der Fund ist groesser als sein Anlass:
        //
        // ```gabbro
        // opaque type F32 = u32;
        // impl fn unsinn(a : F32, b : F32) -> F32 { return a & b; }
        // -> 3 Items, 0 Fehler, 0 Hinweise
        // ```
        //
        // Bitweises Und behaelt die Breite, also schwieg die Ueberlaufregel -- und der
        // undurchsichtige Typ wurde als sein TRAEGER gerechnet. **Dass `a + b` fiel, war
        // Zufall:** es fiel an `M104`, nicht an der Undurchsichtigkeit. *Wo die Breiten
        // aufgehen, ging der Unsinn durch.*
        //
        // > **Und es trifft nicht nur `F32`, sondern jeden Zeugen- und Neutyp der Sprache**:
        // > `Pa` gegen `Va`, zwei `index into` verschiedener Instanzen, einen Rang mit einer
        // > Zellenzahl. Dieselbe Klasse wie `protects`, das deklariert war und nie geprueft
        // > wurde.
        //
        // **VERGLEICHE bleiben zulaessig** (der `return` oben steht davor, mit Absicht): zwei
        // Adressen zu vergleichen deutet den Traeger nicht um, es ordnet Werte desselben
        // Typs. *Was verboten ist, ist das RECHNEN* -- eine Summe zweier Adressen ist keine
        // Adresse, und ein bitweises Und zweier Gleitkommazahlen ist gar nichts.
        for (t, e) in [(&ta, a), (&tb, b)] {
            if let Typ::Benannt { name, undurchsichtig: true, .. } = t {
                self.absagen.schiebe(
                    Absage::fehler(
                        "D003",
                        e.span,
                        format!("`{name}` ist undurchsichtig -- es hat die Rechnung seines Traegers nicht"),
                    )
                    .mit_notiz(
                        "ein `opaque type` sagt: dieser Typ IST nicht sein Traeger. Wer mit \
                         ihm rechnen will, wandelt ihn um -- und die Umwandlung steht dann da",
                    )
                    .mit_notiz(
                        "Vergleiche bleiben erlaubt: sie ordnen Werte desselben Typs, statt \
                         den Traeger umzudeuten",
                    ),
                );
                return Typ::Unbekannt;
            }
        }
        let (Some(ba), Some(bb)) = (ta.bereich(), tb.bereich()) else {
            return Typ::Unbekannt;
        };

        // V2: unter `a >= b` faengt `a - b` bei 0 an, unter `a > b` bei 1.
        if op == BinOp::Minus {
            if let (ExprArt::Ort(oa), ExprArt::Ort(ob)) = (&a.art, &b.art) {
                if let Some(untergrenze) = self.beziehung(oa, ob, lage) {
                    return Typ::Ganzzahl(IntBereich::genau(
                        ba.breite,
                        ba.vorzeichen,
                        untergrenze,
                        (ba.max - bb.min).max(untergrenze),
                    ));
                }
            }
        }

        let r = match op {
            BinOp::Plus => typen::addiere(&ba, &bb),
            BinOp::Minus => typen::subtrahiere(&ba, &bb),
            BinOp::Mal => typen::multipliziere(&ba, &bb),
            BinOp::Geteilt | BinOp::Rest => {
                if bb.enthaelt_null() {
                    self.absagen.schiebe(
                        Absage::fehler(
                            "M102",
                            b.span,
                            format!(
                                "the denominator has range `{}` and does not exclude zero",
                                bb.text()
                            ),
                        )
                        .mit_notiz(
                            "SPRACHE.md §3: Division und Rest verlangen einen Nenner, dessen \
                             Bereich die Null ausschliesst",
                        )
                        .mit_notiz(
                            "eine Pruefung `if n >= 1 { … }` verengt ihn (V1), sonst \
                             `narrow n to 1 .. … else { … }`",
                        ),
                    );
                    return Typ::Unbekannt;
                }
                if op == BinOp::Geteilt {
                    typen::teile(&ba, &bb)
                } else {
                    typen::rest(&ba, &bb)
                }
            }
            BinOp::BitUnd => typen::bitweise(&ba, &bb, typen::BitOpArt::Und),
            BinOp::BitOder => typen::bitweise(&ba, &bb, typen::BitOpArt::Oder),
            BinOp::BitXor => typen::bitweise(&ba, &bb, typen::BitOpArt::Xor),
            BinOp::SchiebLinks => typen::schiebe_links(&ba, &bb),
            BinOp::SchiebRechts => typen::schiebe_rechts(&ba, &bb),
            _ => return Typ::Unbekannt,
        };
        if r.laeuft_ueber && !ta.laeuft_um() {
            self.ueberlauf_ausdruck(span, &ba, &bb, op_zeichen(op));
        }
        match r.bereich {
            Some(x) => Typ::Ganzzahl(x),
            None => Typ::Unbekannt,
        }
    }

    fn ruf(&mut self, r: &Ruf, lage: &Lage) -> Typ {
        let t = self.ruf_roh(r, lage);
        self.buche(&t);
        t
    }

    fn ruf_roh(&mut self, r: &Ruf, lage: &Lage) -> Typ {
        // **Aufgeloest wird im Modul des Aufrufs**, nicht ueber den blanken Namen.
        let signatur = self.u.funktion(&self.modul, &r.pfad).cloned();
        let mut argtypen = Vec::new();
        for a in &r.argumente {
            argtypen.push((self.ausdruck(a, lage), a.span));
        }
        self.marken_pruefen(r);
        let Some(sig) = signatur else {
            return Typ::Unbekannt;
        };
        // Die Stelligkeit gehoert dem Namenspass; hier faellt nur der Bereich.
        for ((t, span), (pname, pt)) in argtypen.iter().zip(sig.parameter.iter()) {
            self.passt(t, pt, *span, &format!("das Argument `{pname}`"));
        }
        sig.ergebnis.clone().unwrap_or(Typ::Unbekannt)
    }

    /// **`M106` IST `deckt` aus `beweise/Verbund_Konstruktor.thy`, und `M107` ist die Frage,
    /// ob die Zuordnungsliste ueberhaupt eine ist.**
    ///
    /// Die Schablone `verbund.konstruktor` sagt: *„setzt jedes Feld genau einmal und laesst
    /// keins uninitialisiert."* Der Beweis fuehrt das auf eine Zeile zurueck --
    ///
    /// ```text
    /// deckt fs zs  ⟷  map fst zs = fs
    /// ```
    ///
    /// -- und die Zeile darunter ist genau dieser `!=`-Vergleich. *Beide Haelften der Zusage
    /// fallen zusammen, sobald die Deklaration wohlgeformt ist* (`deckt_setzt_jedes_genau_einmal`);
    /// deshalb steht hier **eine** Pruefung und nicht zwei.
    ///
    /// > Der Beweis fuehrt unter M-2 seine eigene Grenze: *nicht gezeigt ist, dass der
    /// > ERZEUGER `deckt` herstellt.* Das ist diese Funktion. Sie ist die Bruecke, und die
    /// > Mutation `verbundmarken-egal` ist ihre Sprechprobe.
    ///
    /// **Warum die REIHENFOLGE und nicht nur die Menge:** der Beweis waehlt `map fst zs = fs`
    /// bewusst gegen `set (map fst zs) = set fs` -- *eine Zuordnung, die nur die Menge trifft,
    /// sieht beim Leser aus wie die Deklaration und ist es nicht.*
    fn marken_pruefen(&mut self, r: &Ruf) {
        let gefunden = self.u.verbundfelder(&self.modul, &r.pfad).cloned();
        let felder = gefunden.clone().unwrap_or_default();
        match (gefunden.is_some(), r.ist_verbundwert()) {
            // Ein Verbund mit Marken: der Schluesselstrom gegen die Felderliste.
            (true, true) => {
                let gegeben: Vec<String> = r.marken.iter().map(|m| m.text.clone()).collect();
                if gegeben != felder {
                    self.absagen.schiebe(
                        Absage::fehler(
                            "M106",
                            r.span,
                            format!(
                                "`{}` hat die Felder ({}), der Konstruktor nennt ({})",
                                r.pfad.text(),
                                felder.join(", "),
                                gegeben.join(", ")
                            ),
                        )
                        .mit_notiz(
                            "die Marken muessen die Felderliste sein -- in der Reihenfolge der \
                             Deklaration, jedes Feld genau einmal, keins ausgelassen",
                        )
                        .mit_notiz(
                            "Schablone `verbund.konstruktor`, bewiesen: \
                             `deckt fs zs ⟷ map fst zs = fs`",
                        ),
                    );
                }
            }
            // **Ein Verbund ohne Marken ist der stille Fall, gegen den die Entscheidung
            // steht.** `Punkt(x, y)` mit zwei `u32` laesst sich vertauschen, ohne dass ein
            // Typ dagegen spricht -- und ein Feldname ist das einzige, was die beiden
            // unterscheidet.
            (true, false) => {
                self.absagen.schiebe(
                    Absage::fehler(
                        "M107",
                        r.span,
                        format!(
                            "`{}` ist ein Verbund; sein Konstruktor nennt seine Felder",
                            r.pfad.text()
                        ),
                    )
                    .mit_notiz(format!(
                        "`{}({})`",
                        r.pfad.text(),
                        felder
                            .iter()
                            .map(|f| format!("{f}: …"))
                            .collect::<Vec<_>>()
                            .join(", ")
                    ))
                    .mit_notiz(
                        "zwei gleichtypige Felder in Reihung sind vertauschbar, ohne dass ein \
                         Typ dagegen spricht -- der Name ist die einzige Unterscheidung",
                    ),
                );
            }
            // Marken an etwas, das kein Verbund ist. Eine Funktion hat Parameter, keine
            // Felder; eine Marke dort behauptet eine Zuordnung, die es nicht gibt.
            (false, true) => {
                self.absagen.schiebe(
                    Absage::fehler(
                        "M107",
                        r.span,
                        format!("`{}` ist kein Verbund; Marken gibt es nur am Konstruktor", r.pfad.text()),
                    )
                    .mit_notiz(
                        "die Reihenfolge der Parameter einer Funktion steht in ihrer \
                         Deklaration -- eine Marke am Aufruf waere eine zweite Wahrheit daneben",
                    ),
                );
            }
            (false, false) => {}
        }
    }

    // -- Fakten -------------------------------------------------------------------------

    /// V1/V2 aus einer geprueften Bedingung. `negiert` gilt fuer den `else`-Zweig.
    ///
    /// **VORBEDINGUNG, aufgeschrieben 2026-08-18 -- sie war immer da und stand nirgends:**
    /// der `negiert`-Zweig setzt voraus, dass die Negation einer Vergleichsbedingung selbst
    /// eine Vergleichsbedingung ist -- also eine **totale Ordnung ohne unvergleichbare
    /// Elemente**. Ueber ganzen Zahlen gibt `!(x < y)` das Faktum `x >= y`; das ist
    /// Trichotomie.
    ///
    /// > **Gleitkomma waere ihr erster Verletzer, nicht ihr einziger.** Ist ein Operand NaN,
    /// > sind ALLE Vergleiche falsch, und der `else`-Zweig gibt nichts -- vier Ausgaenge statt
    /// > drei. *Jeder partiell geordnete Traeger braeche dieselbe Maschinerie, und dies hier
    /// > ist die Stelle.*
    ///
    /// Heute traegt jeder Typ dieser Sprache eine totale Ordnung (`IntBereich`, `bool`), also
    /// gilt die Vorbedingung. **Sie steht hier, damit ein kuenftiger Traeger sie BRICHT statt
    /// sie stillschweigend zu unterlaufen** -- `SPRACHE.md` §3.2 fuehrt sie ausgeschrieben.
    fn fakten_aus(&mut self, bedingung: &Expr, negiert: bool, lage: &mut Lage) {
        match &bedingung.art {
            ExprArt::Klammer(i) => self.fakten_aus(i, negiert, lage),
            // `a && b` gibt im Ja-Zweig beide Fakten; im Nein-Zweig keinen (es reicht, dass
            // einer faellt, und welcher steht nicht fest).
            ExprArt::Binaer(BinOp::Und, a, b) if !negiert => {
                self.fakten_aus(a, false, lage);
                self.fakten_aus(b, false, lage);
            }
            ExprArt::Binaer(BinOp::Oder, a, b) if negiert => {
                self.fakten_aus(a, true, lage);
                self.fakten_aus(b, true, lage);
            }
            ExprArt::Binaer(op, a, b) if op.ist_vergleich() => {
                // **«F» -- das Herzstueck: die Negation ist BEDINGT, nicht abgeschaltet.**
                //
                // Ist ein Operand NaN, sind ALLE Vergleiche falsch, und aus `!(x < y)` folgt
                // `x >= y` nicht. Die Tatsache faellt darum genau dann an, wenn beide Seiten
                // als nicht-NaN bekannt sind -- und bekannt werden sie durch
                // `narrow … to finite` oder dadurch, dass sie Literale sind.
                //
                // *Damit ist Gleitkomma nicht faktenlos, sondern gewoehnlich: man wird NaN
                // einmal los und rechnet danach weiter.*
                if negiert && (self.nan_moeglich(a, lage) || self.nan_moeglich(b, lage)) {
                    return;
                }
                // **Ein GEGLUECKTER Vergleich impliziert Nicht-NaN auf BEIDEN Seiten.**
                //
                // Im Dann-Zweig von `if x < y` sind beide Operanden nan-frei, ohne jedes
                // `narrow` -- bei `<`, `<=`, `>`, `>=` und `==` gleichermassen. **Nur `!=`
                // gibt nichts her**, denn `NaN != NaN` ist wahr.
                //
                // *Genau darum waren zwei Bits richtig:* der Vergleich loescht EINS,
                // `narrow … to finite` loescht beide. Waere Endlichkeit ein Praedikat,
                // haette der Vergleich nichts beitragen koennen.
                //
                // Und `x == x` faellt damit von selbst in seine Rolle -- im Korpus die
                // Handschrift fuer `isnan`, hier ein Vergleich, dessen Dann-Zweig das
                // NaN-Bit loescht. **Er muss nicht als Idiom erkannt werden.**
                if !negiert && *op != BinOp::Ungleich {
                    for seite in [a, b] {
                        if let ExprArt::Ort(o) = &seite.art {
                            if matches!(
                                self.ausdruck(seite, lage).durchgreifen(),
                                Typ::Gleitkomma(_)
                            ) {
                                if let Some((schluessel, indizes)) = schluessel_und_indizes(o) {
                                    lage.fakten.push(Fakt::Endlich {
                                        schluessel,
                                        indizes,
                                        nan: true,
                                        unendlich: false,
                                    });
                                }
                            }
                        }
                    }
                }
                let op = if negiert { negiere(*op) } else { *op };
                self.vergleichsfakt(op, a, b, lage);
            }
            _ => {}
        }
    }

    /// **«F»: kann dieser Ausdruck NaN sein?**
    ///
    /// Nur Gleitkomma kann es. Ein Ganzzahlausdruck gibt `false`, und damit bleibt die
    /// Verengungsmaschinerie fuer den ganzen bisherigen Bestand unveraendert -- *die
    /// Erweiterung darf den gemessenen Pfad nicht anfassen* (Tor P-F1).
    fn nan_moeglich(&mut self, e: &Expr, lage: &Lage) -> bool {
        match self.ausdruck(e, lage) {
            Typ::Gleitkomma(f) => f.kann_nan,
            _ => false,
        }
    }

    fn vergleichsfakt(&mut self, op: BinOp, a: &Expr, b: &Expr, lage: &mut Lage) {
        // **«F»: derselbe Satz, andere Zahlen.** Bis 2026-08-18 lief hier nur `konst_wert`,
        // und das ist ganzzahlig -- ein Gleitkommavergleich loeschte das NaN-Bit und liess
        // die SCHRANKE offen. *Damit war `narrow … to <fbereich>` die einzige Quelle eines
        // Intervalls, und `if x < 1.0` sagte nichts ueber `x`.*
        if let (ExprArt::Ort(o), Some(w)) = (&a.art, self.u.gleitwert(b)) {
            if self.ist_gleitort(o, lage) {
                self.fintervallfakt(o, op, w, lage);
            }
        }
        if let (Some(w), ExprArt::Ort(o)) = (self.u.gleitwert(a), &b.art) {
            if self.ist_gleitort(o, lage) {
                self.fintervallfakt(o, spiegle(op), w, lage);
            }
        }
        // V1 -- Stelle gegen Konstante, in beiden Schreibrichtungen.
        if let (ExprArt::Ort(o), Some(wert)) = (&a.art, self.u.konst_wert(&self.modul, b)) {
            self.bereichsfakt(o, op, wert, lage);
        }
        if let (Some(wert), ExprArt::Ort(o)) = (self.u.konst_wert(&self.modul, a), &b.art) {
            self.bereichsfakt(o, spiegle(op), wert, lage);
        }
        // V2 -- Stelle gegen Stelle, ausschliesslich als Vergleichsfakt.
        if let (ExprArt::Ort(oa), ExprArt::Ort(ob)) = (&a.art, &b.art) {
            if let (Some((links, mut ia)), Some((rechts, ib))) =
                (schluessel_und_indizes(oa), schluessel_und_indizes(ob))
            {
                ia.extend(ib);
                lage.fakten.push(Fakt::Beziehung {
                    links,
                    op,
                    rechts,
                    indizes: ia,
                });
            }
        }
    }

    fn ist_gleitort(&self, o: &Ort, lage: &Lage) -> bool {
        matches!(
            self.u
                .typ_von_ort(&self.modul, o, &lage.lokal)
                .durchgreifen(),
            Typ::Gleitkomma(_)
        )
    }

    /// **Die Schranke aus einem Gleitkommavergleich.**
    ///
    /// `x < w` heisst `x <= vorheriger(w)` -- und *das* ist die Stelle, an der die
    /// Nachbarschaft der Gleitkommazahlen zaehlt: eine offene Schranke ist hier keine
    /// Naeherung, sondern ein benannter Nachbar.
    ///
    /// **Die Null bleibt die Ausnahme, die sie ist:** `nextDown(+0)` ist die groesste
    /// negative Zahl und nicht `-0.0`, denn `-0.0` ist nicht KLEINER als `+0.0`, sondern
    /// gleich. Damit faellt `x < 0.0` fuer `-0.0` zu Recht aus.
    fn fintervallfakt(&mut self, o: &Ort, op: BinOp, wert: f64, lage: &mut Lage) {
        let Some((schluessel, indizes)) = schluessel_und_indizes(o) else {
            return;
        };
        let (lo, hi) = match op {
            BinOp::GroesserGleich => (wert, f64::INFINITY),
            BinOp::Groesser => (wert.next_up(), f64::INFINITY),
            BinOp::KleinerGleich => (f64::NEG_INFINITY, wert),
            BinOp::Kleiner => (f64::NEG_INFINITY, wert.next_down()),
            BinOp::Gleich => (wert, wert),
            _ => return,
        };
        lage.fakten.push(Fakt::FIntervall {
            schluessel,
            indizes,
            lo,
            hi,
        });
    }

    fn bereichsfakt(&mut self, o: &Ort, op: BinOp, wert: i128, lage: &mut Lage) {
        let Some((schluessel, indizes)) = schluessel_und_indizes(o) else {
            return;
        };
        let (min, max) = match op {
            BinOp::GroesserGleich => (wert, i128::MAX),
            BinOp::Groesser => (wert + 1, i128::MAX),
            BinOp::KleinerGleich => (i128::MIN, wert),
            BinOp::Kleiner => (i128::MIN, wert - 1),
            BinOp::Gleich => (wert, wert),
            _ => return,
        };
        lage.fakten.push(Fakt::Bereich {
            schluessel,
            indizes,
            min,
            max,
        });
    }

    /// Der Typ eines Ortes, verengt durch die Fakten, die ueber ihn gelten.
    fn mit_fakt(&self, o: &Ort, grund: Typ, lage: &Lage) -> Typ {
        // **«F»: die zwei Bits zuerst** -- sie haengen an keinem Bereich, und ein
        // Gleitkommatyp hat gar keinen `bereich()` im Ganzzahlsinn.
        if let Typ::Gleitkomma(mut f) = grund {
            if let Some(schluessel) = schluessel_von(o) {
                for fk in &lage.fakten {
                    if let Fakt::Endlich {
                        schluessel: s,
                        nan,
                        unendlich,
                        ..
                    } = fk
                    {
                        if *s == schluessel {
                            if *nan {
                                f.kann_nan = false;
                            }
                            if *unendlich {
                                f.kann_unendlich = false;
                            }
                        }
                    }
                    if let Fakt::FIntervall {
                        schluessel: s,
                        lo,
                        hi,
                        ..
                    } = fk
                    {
                        if *s == schluessel {
                            f.lo = f.lo.max(*lo);
                            f.hi = f.hi.min(*hi);
                        }
                    }
                }
                // **Am SCHNITT, nicht je Fakt.** `x >= 0.0 && x <= 1.0` gibt zwei Fakten,
                // und jeder fuer sich ist halboffen -- erst zusammen sind sie endlich.
                // *Die erste Fassung pruefte je Fakt und liess die Bits stehen, obwohl das
                // Ergebnis sie ausschloss.*
                //
                // Und die Aussage ist scharf: **NaN liegt in KEINEM Intervall**, weil jeder
                // Vergleich mit ihm falsch ist, und unendlich liegt in keinem endlichen.
                if f.lo.is_finite() && f.hi.is_finite() {
                    f.kann_nan = false;
                    f.kann_unendlich = false;
                }
            }
            return Typ::Gleitkomma(f);
        }
        let Some(b) = grund.bereich() else {
            return grund;
        };
        let Some(schluessel) = schluessel_von(o) else {
            return grund;
        };
        let mut min = b.min;
        let mut max = b.max;
        for f in &lage.fakten {
            if let Fakt::Bereich {
                schluessel: s,
                min: lo,
                max: hi,
                ..
            } = f
            {
                if *s == schluessel {
                    min = min.max(*lo);
                    max = max.min(*hi);
                }
            }
        }
        if min == b.min && max == b.max {
            return grund;
        }
        Typ::Ganzzahl(IntBereich::genau(b.breite, b.vorzeichen, min, max))
    }

    /// V2 -- gibt die Untergrenze von `a - b`, wenn ein Vergleichsfakt sie traegt.
    fn beziehung(&self, a: &Ort, b: &Ort, lage: &Lage) -> Option<i128> {
        let (ka, kb) = (schluessel_von(a)?, schluessel_von(b)?);
        for f in &lage.fakten {
            if let Fakt::Beziehung {
                links, op, rechts, ..
            } = f
            {
                if *links == ka && *rechts == kb {
                    match op {
                        BinOp::GroesserGleich => return Some(0),
                        BinOp::Groesser => return Some(1),
                        _ => {}
                    }
                }
                if *links == kb && *rechts == ka {
                    match op {
                        BinOp::KleinerGleich => return Some(0),
                        BinOp::Kleiner => return Some(1),
                        _ => {}
                    }
                }
            }
        }
        None
    }

    /// *„bei jedem Schreiben auf eine beteiligte Stelle stirbt der Fakt"*.
    fn schreiben_toetet_fakten(&self, ziel: &Ort, lage: &mut Lage) {
        let Some(k) = schluessel_von(ziel) else {
            lage.fakten.clear();
            return;
        };
        lage.fakten.retain(|f| match f {
            // **«F»: dieselbe Regel wie fuer den Bereich.** Wird die Stelle beschrieben,
            // faellt auch die Endlichkeitszusage -- *ein Fakt ueber einen Wert ueberlebt
            // dessen Ueberschreiben nicht.*
            Fakt::Endlich {
                schluessel,
                indizes,
                ..
            }
            | Fakt::FIntervall {
                schluessel,
                indizes,
                ..
            }
            | Fakt::Bereich {
                schluessel,
                indizes,
                ..
            } => !beruehrt(schluessel, &k) && !indizes.iter().any(|i| *i == k),
            Fakt::Beziehung {
                links,
                rechts,
                indizes,
                ..
            } => {
                !beruehrt(links, &k)
                    && !beruehrt(rechts, &k)
                    && !indizes.iter().any(|i| *i == k)
            }
        });
        // Ein Schreiben durch einen Zeiger kann alles Nichtlokale treffen -- ohne M3 gibt es
        // keine Aliasaussage, also faellt hier alles Nichtlokale mit.
        if k.contains('.') || k.contains("->") || k.contains('[') {
            lage.fakten.retain(|f| match f {
                Fakt::Endlich { schluessel, .. }
            | Fakt::FIntervall { schluessel, .. }
            | Fakt::Bereich { schluessel, .. } => self.ist_lokal(schluessel),
                Fakt::Beziehung { links, rechts, .. } => {
                    self.ist_lokal(links) && self.ist_lokal(rechts)
                }
            });
        }
    }

    /// Ein Aufruf toetet die Fakten ueber alles **Nichtlokale**. Lokale Groessen kann er
    /// nicht aendern: Gabbro hat keinen Adressoperator.
    /// **U5.** Ein Aufruf steht selten allein: `let t = nuller(z);` ist derselbe Aufruf wie
    /// `nuller(z);`. Vorher toetete nur die zweite Form Fakten -- ein Zeichen Unterschied
    /// entschied ueber die Zusage.
    fn rufe_im_ausdruck(&self, e: &Expr, lage: &mut Lage) {
        if enthaelt_ruf(e) {
            self.aufruf_toetet_fakten(lage);
        }
    }

    fn aufruf_toetet_fakten(&self, lage: &mut Lage) {
        lage.fakten.retain(|f| match f {
            Fakt::Endlich { schluessel, .. }
            | Fakt::FIntervall { schluessel, .. }
            | Fakt::Bereich { schluessel, .. } => self.ist_lokal(schluessel),
            Fakt::Beziehung { links, rechts, .. } => {
                self.ist_lokal(links) && self.ist_lokal(rechts)
            }
        });
    }

    /// **U4.** Eine Stelle ist lokal, wenn sie weder Feld noch Index traegt **und kein
    /// globaler Name ist**. `static mut g` erfuellt die erste Haelfte -- ohne die zweite
    /// ueberlebt jeder Fakt ueber einen globalen Zaehler jeden Aufruf.
    fn ist_lokal(&self, schluessel: &str) -> bool {
        if schluessel.contains('.') || schluessel.contains('[') || schluessel.contains("->") {
            return false;
        }
        !self.u.globale.contains_key(schluessel)
    }

    // -- Absagen ------------------------------------------------------------------------

    fn buche(&mut self, t: &Typ) {
        if t.ist_unbekannt() {
            self.zaehlung.unbekannt += 1;
        } else {
            self.zaehlung.typisiert += 1;
        }
    }

    fn passt(&mut self, quelle: &Typ, ziel: &Typ, span: Span, was: &str) {
        // **«F»: die zwei Bits, und sie sind der Abnehmer der Faktenmaschine.**
        //
        // Ohne diese Zeilen waere `Fakt::Endlich` gebaut und von nichts gelesen -- genau die
        // Klasse, gegen die `pruefe-klauseln.py` steht. *Ein Typ mit einem GENANNTEN Bereich
        // schliesst NaN aus; ein blankes `f64` nicht.*
        // Neutypen durchgreifen: `type Anteil = f64 in 0.0 .. 1.0` traegt dieselbe Zusage
        // wie die ausgeschriebene Form. *Sonst haenge die Regel daran, ob jemand dem Typ
        // einen Namen gegeben hat.*
        if let (Typ::Gleitkomma(q), Typ::Gleitkomma(z)) =
            (quelle.durchgreifen(), ziel.durchgreifen())
        {
            let mut fehlt = Vec::new();
            if q.kann_nan && !z.kann_nan {
                fehlt.push("NaN");
            }
            if q.kann_unendlich && !z.kann_unendlich {
                fehlt.push("unendlich");
            }
            // **`F002` an der VERSCHMAELERUNG.** Ein Literal, das in `f64` exakt liegt,
            // muss es in `f32` nicht -- und `FBereich::mantisse()` stand dafuer da und wurde
            // von niemandem gelesen. *Dieselbe Klasse wie die siebzehn ZUSAGEN, in meinem
            // eigenen Code, einen Tag alt.*
            if q.literal
                && !q.gerundet
                && !crate::typen::FBereich::passt_in_mantisse(q.lo, z.breite)
            {
                self.absagen.schiebe(
                    Absage::fehler(
                        "F002",
                        span,
                        format!(
                            "das Literal liegt in `f{}` nicht exakt (in `f64` schon)",
                            z.breite
                        ),
                    )
                    .mit_notiz(
                        "`f32` traegt 24 Mantissenbits, `f64` traegt 53 -- schreibe \
                         `rounded` dahinter, wenn die Rundung gemeint ist",
                    ),
                );
            }
            // **Das INTERVALL, und ohne es waere der genannte Bereich eine Behauptung, die
            // nie eingeloest wird.** Schweigen ist unvollstaendig; eine ungepruefte Zusage
            // ist falsch -- und `2.5` ist endlich, liegt aber nicht in `0.0 .. 1.0`.
            if q.lo < z.lo || q.hi > z.hi {
                self.absagen.schiebe(
                    Absage::fehler(
                        "M101",
                        span,
                        format!(
                            "{was} requires `{}`, the value has `{}`",
                            Typ::Gleitkomma(*z).text(),
                            Typ::Gleitkomma(*q).text()
                        ),
                    )
                    .mit_notiz(
                        "`narrow <ort> to <von> .. <bis> else { … }` verengt den Bereich; \
                         `finite` allein loescht nur NaN und Unendlich",
                    ),
                );
            }
            if !fehlt.is_empty() {
                self.absagen.schiebe(
                    Absage::fehler(
                        "F001",
                        span,
                        format!(
                            "{was} vertraegt kein {}, der Wert kann es sein",
                            fehlt.join(" und kein ")
                        ),
                    )
                    .mit_notiz(
                        "`narrow <ort> to finite else { … }` stellt beides auf einmal her; \
                         der `else`-Zweig IST der NaN-Weg",
                    )
                    .mit_notiz(
                        "ohne die Tatsache liefert auch die Negation eines Vergleichs \
                         nichts: ist ein Operand NaN, sind alle Vergleiche falsch",
                    ),
                );
            }
            return;
        }
        let (Some(q), Some(z)) = (quelle.bereich(), ziel.bereich()) else {
            return;
        };
        if q.passt_in(&z) {
            return;
        }
        let mut a = Absage::fehler(
            "M101",
            span,
            format!(
                "{was} requires `{}`, the value has `{}`",
                z.text(),
                q.text()
            ),
        )
        .mit_notiz(
            "M1: jede Operation muss im Bereich ihres Ergebnistyps bleiben -- \
             das ist ein Uebersetzungsfehler, keine Laufzeitpruefung",
        );
        if q.min < z.min || q.max > z.max {
            a = a.mit_notiz(format!(
                "es fehlt der Nachweis, dass der Wert in {} .. {} liegt; \
                 eine Pruefung davor verengt ihn (V1/V2), sonst `narrow … to … else {{ … }}`",
                z.min, z.max
            ));
        }
        self.absagen.schiebe(a);
    }

    fn ueberlauf(&mut self, span: Span, a: &IntBereich, b: &IntBereich, wort: &str, ort: &Ort) {
        self.absagen.schiebe(
            Absage::fehler(
                "M104",
                span,
                format!(
                    "`{}` {wort} verlaesst den Bereich: `{}` gegen `{}`",
                    ort.text(),
                    a.text(),
                    b.text()
                ),
            )
            .mit_notiz(
                "der Ueberlauf ist ein Uebersetzungsfehler, keine Laufzeitpruefung -- \
                 wer ihn will, deklariert den Slot als `wrapping`",
            )
            .mit_notiz(
                "eine Pruefung davor verengt den Bereich (V1), eine Beziehung zweier \
                 Stellen ebenso (V2)",
            ),
        );
    }

    fn ueberlauf_ausdruck(&mut self, span: Span, a: &IntBereich, b: &IntBereich, zeichen: &str) {
        self.absagen.schiebe(
            Absage::fehler(
                "M104",
                span,
                format!(
                    "`{} {zeichen} {}` leaves the width of the result type",
                    a.text(),
                    b.text()
                ),
            )
            .mit_notiz(
                "SYNTAX.md §4: passt der Ergebnisbereich nicht, ist es ein \
                 Uebersetzungsfehler -- keine Laufzeitpruefung",
            ),
        );
    }

    /// M4 an der Stelle, an der M1 die Zahl hat: ein Index gegen die Laenge seines Feldes.
    fn index_pruefen(&mut self, o: &Ort, lage: &Lage) {
        // **`suche` und nicht `get`, und das war ein Loch in der ERSTEN getragenen Klasse.**
        //
        // Bis zum 2026-08-17 stand hier ein direktes `get(&o.basis.text)`. Die Schluessel in
        // `globale` sind QUALIFIZIERT (`beispiel::x::Kappenraum`), also traf der Blick auf
        // `"Kappenraum"` in jedem `module`-Block ins Leere -- der Traeger wurde `Unbekannt`,
        // und `M103` sagte nichts.
        //
        // ```gabbro
        // table W count 8 { slot { a : u32, } }
        // impl fn f(i : u32 in 0 .. 300) -> u32 { return W.slots[i].a; }   -- 0 Fehler
        // ```
        //
        // > **Die Regel war gebaut, gebucht und getragen -- und traf genau die Form nicht,
        // > fuer die sie da ist:** eine Tabelle, die ueber ihren globalen Namen adressiert
        // > wird. *Das ist die Bauart von `beispiele/09-ohne-zeiger.gab`, dessen ganzer Punkt
        // > es ist, dass Kernzustand keinen Zeiger braucht.*
        //
        // Gefunden beim Bauen von `const fn`, weil eine Giftprobe nicht fiel, die fallen
        // musste (R11). *`typ_von_ort` daneben hat immer `suche` benutzt -- die zwei Blicke
        // auf dieselbe Karte gingen auseinander, und nur einer davon hatte einen Test.*
        let mut traeger = lage
            .lokal
            .get(&o.basis.text)
            .cloned()
            .or_else(|| {
                self.u
                    .suche_global(&self.modul, &o.basis.text)
                    .cloned()
            })
            .unwrap_or(Typ::Unbekannt);
        for suffix in &o.suffixe {
            match suffix {
                OrtSuffix::Index(idx) => {
                    if let Typ::Feld {
                        element,
                        laenge: Some(n),
                    } = traeger.durchgreifen()
                    {
                        let n = *n as i128;
                        let it = self.ausdruck_roh(idx, lage);
                        if let Some(b) = it.bereich() {
                            if b.max >= n || b.min < 0 {
                                self.absagen.schiebe(
                                    Absage::fehler(
                                        "M103",
                                        idx.span,
                                        format!(
                                            "the index has `{}`, the array has {n} elements",
                                            b.text()
                                        ),
                                    )
                                    .mit_notiz(
                                        "M4: kein ungeprueftes Indizieren -- die Schranke \
                                         faellt aus dem Typ des Index, nicht aus einer Pruefung \
                                         zur Laufzeit",
                                    ),
                                );
                            }
                        }
                        traeger = (**element).clone();
                    } else {
                        traeger = match traeger.durchgreifen() {
                            Typ::Feld { element, .. } => (**element).clone(),
                            _ => Typ::Unbekannt,
                        };
                    }
                }
                OrtSuffix::Feld(f) | OrtSuffix::Ueber(f) => {
                    traeger = self.u.feld_von(&self.modul, &traeger, &f.text);
                }
            }
        }
    }
}

/// Der Schluessel eines Ortes -- `None`, wenn ein Index kein einfacher Ort und keine Zahl
/// ist. **Ohne Schluessel kein Fakt:** zwei verschiedene Indizes duerfen nicht denselben
/// Namen bekommen, sonst verengt eine Pruefung ueber `a[i]` auch `a[j]`.
fn schluessel_von(o: &Ort) -> Option<String> {
    schluessel_und_indizes(o).map(|(s, _)| s)
}

/// **U3.** Zum Schluessel gehoeren die Namen seiner Indizes. `buf[i]` bleibt sonst
/// derselbe Ort, waehrend `i` sich darunter wegbewegt -- ein Fakt ueber `buf[i]` ueberlebte
/// `i = 0` und verengte danach einen ganz anderen Platz.
fn schluessel_und_indizes(o: &Ort) -> Option<(String, Vec<String>)> {
    let mut s = o.basis.text.clone();
    let mut indizes = Vec::new();
    for suffix in &o.suffixe {
        match suffix {
            OrtSuffix::Feld(f) => {
                s.push('.');
                s.push_str(&f.text);
            }
            OrtSuffix::Ueber(f) => {
                s.push_str("->");
                s.push_str(&f.text);
            }
            OrtSuffix::Index(e) => match &e.art {
                ExprArt::Zahl(v) => s.push_str(&format!("[{v}]")),
                ExprArt::Ort(inner) if inner.suffixe.is_empty() => {
                    s.push_str(&format!("[{}]", inner.basis.text));
                    indizes.push(inner.basis.text.clone());
                }
                _ => return None,
            },
        }
    }
    Some((s, indizes))
}

/// Beruehren sich zwei Ortsschluessel? Ein Schreiben auf `c.slots` trifft auch
/// `c.slots[i].benutzt`, und umgekehrt.
fn beruehrt(a: &str, b: &str) -> bool {
    a == b
        || a.starts_with(b) && trennt(a.as_bytes().get(b.len()).copied())
        || b.starts_with(a) && trennt(b.as_bytes().get(a.len()).copied())
}

fn trennt(c: Option<u8>) -> bool {
    matches!(c, Some(b'.') | Some(b'[') | Some(b'-'))
}

/// Steht irgendwo in diesem Ausdruck ein Aufruf?
fn enthaelt_ruf(e: &Expr) -> bool {
    match &e.art {
        ExprArt::Ruf(_) => true,
        ExprArt::Klammer(i) | ExprArt::Unaer(_, i) => enthaelt_ruf(i),
        ExprArt::Binaer(_, a, b) => enthaelt_ruf(a) || enthaelt_ruf(b),
        ExprArt::Ort(o) => o.suffixe.iter().any(|sx| match sx {
            OrtSuffix::Index(i) => enthaelt_ruf(i),
            _ => false,
        }),
        ExprArt::Eingebaut(b) => match b.as_ref() {
            Eingebaut::Aligned(a, c) => enthaelt_ruf(a) || enthaelt_ruf(c),
            _ => false,
        },
        _ => false,
    }
}

/// Nennt der Fakt diesen Namen -- als Grundname oder in einem Index?
fn nennt_namen(f: &Fakt, name: &str) -> bool {
    let trifft = |s: &str| {
        s == name
            || s.starts_with(name) && trennt(s.as_bytes().get(name.len()).copied())
            || s.split(['[', ']', '.']).any(|t| t == name)
    };
    match f {
        Fakt::Endlich { schluessel, .. }
        | Fakt::FIntervall { schluessel, .. }
        | Fakt::Bereich { schluessel, .. } => trifft(schluessel),
        Fakt::Beziehung { links, rechts, .. } => trifft(links) || trifft(rechts),
    }
}

/// Sammelt jedes Ziel, auf das ein Block schreibt -- auch in seinen Unterbloecken.
fn sammle_schreibziele(b: &Block, out: &mut Vec<Ort>) {
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Zuweisung(z) => out.push(z.ziel.clone()),
            StmtArt::Publish(p) => out.push(p.ziel.clone()),
            StmtArt::Exchange(e) => out.push(e.ort.clone()),
            StmtArt::Wenn(w) => {
                for (_, r) in &w.zweige {
                    sammle_schreibziele(r, out);
                }
                if let Some(r) = &w.sonst {
                    sammle_schreibziele(r, out);
                }
            }
            StmtArt::Match(m) => {
                for z in &m.zweige {
                    sammle_schreibziele(&z.rumpf, out);
                }
            }
            StmtArt::Bricht(x) => sammle_schreibziele(&x.rumpf, out),
            StmtArt::Sperrt(x) => sammle_schreibziele(&x.rumpf, out),
            StmtArt::Narrow(x) => sammle_schreibziele(&x.sonst, out),
            StmtArt::LetSonst(x) => sammle_schreibziele(&x.sonst, out),
            StmtArt::Schleife(sch) => match sch.as_ref() {
                Schleife::Traverse(t) => sammle_schreibziele(&t.rumpf, out),
                Schleife::Retry(r) => sammle_schreibziele(&r.rumpf, out),
                Schleife::Forever(f) => sammle_schreibziele(&f.rumpf, out),
            },
            _ => {}
        }
    }
}

fn negiere(op: BinOp) -> BinOp {
    match op {
        BinOp::Gleich => BinOp::Ungleich,
        BinOp::Ungleich => BinOp::Gleich,
        BinOp::Kleiner => BinOp::GroesserGleich,
        BinOp::KleinerGleich => BinOp::Groesser,
        BinOp::Groesser => BinOp::KleinerGleich,
        BinOp::GroesserGleich => BinOp::Kleiner,
        anderer => anderer,
    }
}

/// `3 <= x` sagt dasselbe wie `x >= 3`.
fn spiegle(op: BinOp) -> BinOp {
    match op {
        BinOp::Kleiner => BinOp::Groesser,
        BinOp::KleinerGleich => BinOp::GroesserGleich,
        BinOp::Groesser => BinOp::Kleiner,
        BinOp::GroesserGleich => BinOp::KleinerGleich,
        anderer => anderer,
    }
}

fn op_wort(op: ZuwOp) -> &'static str {
    match op {
        ZuwOp::Plus => "+=",
        ZuwOp::Minus => "-=",
        ZuwOp::Und => "&=",
        ZuwOp::Oder => "|=",
        ZuwOp::Setzt => "=",
    }
}

fn op_zeichen(op: BinOp) -> &'static str {
    match op {
        BinOp::Plus => "+",
        BinOp::Minus => "-",
        BinOp::Mal => "*",
        BinOp::Geteilt => "/",
        BinOp::Rest => "%",
        BinOp::SchiebLinks => "<<",
        BinOp::SchiebRechts => ">>",
        BinOp::BitUnd => "&",
        BinOp::BitOder => "|",
        BinOp::BitXor => "^",
        _ => "?",
    }
}
