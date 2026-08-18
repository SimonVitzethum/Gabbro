//! **Die Umgebung** -- was ein Name bedeutet, und was ein Ort fuer einen Typ hat.
//!
//! Dazu gehoert die **Konstantenauswertung**: `type SlotIdx = u32 in 0 ..< NSLOTS` ist ohne
//! sie ein Bereich ohne Grenzen, und dann sagt M1 nichts. `constexpr` ist zur
//! Uebersetzungszeit auswertbar -- kein Praeprozessor, keine Textersetzung.
//!
//! **Was hier nicht aufgeloest wird, wird `Typ::Unbekannt`, und der Pass zaehlt es.** Ein
//! Pruefer, der einen unbekannten Typ als „passt schon" liest, meldet Gruen ueber Nichts.

use crate::typen::{grenzen, IntBereich, Typ};
use gabbro_syntax::ast::*;
use gabbro_syntax::kw::Kw;
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone)]
pub struct Signatur {
    pub parameter: Vec<(String, Typ)>,
    pub ergebnis: Option<Typ>,
    pub span: gabbro_syntax::span::Span,
}

/// **Die Traegerarten, erschoepfend.** Jede Deklaration, die einen Namen einfuehrt, den ein
/// Zeiger tragen kann, steht hier — und jede Aufloesungsstelle matcht **ohne `_`-Zweig**
/// darueber. Eine neue Art ist damit ein Uebersetzungsfehler an jeder Kette, die sie nicht
/// behandelt, statt eines stillen `Unbekannt`.
///
/// *Gefunden am MMU-Fragment 2026-08-16: `walk` fehlte, und die Schranke, die schon dastand,
/// griff trotzdem nicht.*
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Traegerart {
    Neutyp,
    Tabelle,
    Format,
    Geraet,
    Walk,
}

impl Traegerart {
    /// **Die Reihenfolge ist die Aufloesungsreihenfolge** — ein Neutyp verdeckt eine
    /// gleichnamige Tabelle, so wie bisher.
    pub const ALLE: [Traegerart; 5] = [
        Traegerart::Neutyp,
        Traegerart::Tabelle,
        Traegerart::Format,
        Traegerart::Geraet,
        Traegerart::Walk,
    ];
}

#[derive(Default)]
pub struct Umgebung {
    roh_typen: HashMap<String, TypDecl>,
    roh_konst: HashMap<String, Expr>,
    /// **`const fn` -- Name -> (Parameternamen, Rumpfausdruck).**
    ///
    /// Nur der einzeilige Fall: `{ return <expr>; }`. **Das ist keine Vorstufe, sondern die
    /// Entscheidung** -- ein `const fn` mit Verzweigung waere ein Auswerter im Pruefer, und
    /// ein Auswerter ist ein Erzeuger. *Comptime, das Werte rechnet, kostet keine Schablone;
    /// comptime, das rechnet WIE ein Programm, faengt an eine zu kosten.*
    konst_fn: HashMap<String, (Vec<String>, Expr)>,
    pub typen: HashMap<String, Typ>,
    pub konstanten: HashMap<String, i128>,
    /// Tabellenname -> Slotfelder.
    pub tabellen: HashMap<String, Vec<(String, Typ)>>,
    /// Tabellenname -> `count N`, wenn die Deklaration sie nennt.
    pub kapazitaeten: HashMap<String, u128>,
    /// **`walk`-Name -> `levels` x Knotenlaenge.** Die Schranke der Domaene `mappings of`
    /// steht in der Deklaration und nirgends sonst -- ohne sie kann der Kostenpass eine
    /// Seitentabellen-Traversierung nicht rechnen und sagt das (`K003`).
    pub walkschranken: HashMap<String, u128>,
    /// Uebergangsname -> seine festen Kosten (je `placeshift` ein Speichern).
    pub uebergangskosten: HashMap<String, i128>,
    pub formate: HashMap<String, Vec<(String, Typ)>>,
    pub geraete: HashMap<String, Vec<(String, Typ)>>,
    /// `static`, `atomic`, `accumulates` -- alles, was ohne Deklaration im Rumpf sichtbar ist.
    pub globale: HashMap<String, Typ>,
    pub funktionen: HashMap<String, Signatur>,
    /// **Die Namen, deren Signatur ein KONSTRUKTOR ist, kein Aufruf** («B7»).
    /// Wert ist die Felderliste in Deklarationsreihenfolge -- `fs` aus
    /// `beweise/Verbund_Konstruktor.thy`.
    pub verbundtypen: HashMap<String, Vec<String>>,
    /// Je Modulpfad die Pfade seiner `use`-Zeilen.
    verwendet: HashMap<String, Vec<String>>,
}

/// Das Modul, in dem ein qualifizierter Name steht.
pub fn modul_von(qualifiziert: &str) -> &str {
    match qualifiziert.rfind("::") {
        Some(i) => &qualifiziert[..i],
        None => "",
    }
}

/// Der letzte Abschnitt eines qualifizierten Namens.
pub fn kurzname(qualifiziert: &str) -> &str {
    qualifiziert.rsplit("::").next().unwrap_or(qualifiziert)
}

/// `""` + `x` = `x`; `a::b` + `x` = `a::b::x`.
fn qualifiziere(pfad: &str, name: &str) -> String {
    if pfad.is_empty() {
        name.to_string()
    } else {
        format!("{pfad}::{name}")
    }
}

impl Umgebung {
    pub fn sammle(baum: &Programm) -> Umgebung {
        let mut u = Umgebung::default();
        u.sammle_roh(&baum.items, "");
        // Konstanten zuerst: die Bereiche der Typen haengen an ihnen.
        let namen: Vec<String> = u.roh_konst.keys().cloned().collect();
        for n in namen {
            let mut unterwegs = HashSet::new();
            if let Some(w) = u.konst_aufloesen(modul_von(&n), kurzname(&n), &mut unterwegs) {
                u.konstanten.insert(n, w);
            }
        }
        let namen: Vec<String> = u.roh_typen.keys().cloned().collect();
        for n in namen {
            let mut unterwegs = HashSet::new();
            let t = u.typ_aufloesen(modul_von(&n), kurzname(&n), &mut unterwegs);
            u.typen.insert(n, t);
        }
        // **Die Kapazitaeten VOR den Traegern, und das ist ein Fund vom 2026-08-18.**
        //
        // `sammle_traeger` loest die Slotfelder einer Tabelle auf und traegt ihre Kapazitaet
        // DANACH ein. Ein `index into T` im Slot von T fand die Zahl also nie -- die Schranke
        // fiel auf blankes `u32` zurueck, und der naechste Zugriff wurde abgelehnt.
        //
        // **Damit war jede verkettete Struktur unschreibbar**: keine Freiliste, keine CDT,
        // kein Objektgraph -- genau die Form, die im Korpus steht (`FRAGMENTE.md`:158-161)
        // und ueber die `Table_Induktion.thy` seine Saetze fuehrt. *Der Beweis handelte von
        // einer Form, die der Pruefer nicht typisieren konnte.*
        //
        // Selbstbezueglichkeit war dabei nur der Fall, der IMMER faellt; ein VORWAERTSverweis
        // fiel genauso. Es ist die Reihenfolge, nicht die Bezueglichkeit.
        u.sammle_kapazitaeten(&baum.items, "");
        u.sammle_traeger(&baum.items, "");
        u
    }

    /// Nur die Kapazitaeten, und zwar zuerst -- siehe `sammle`.
    fn sammle_kapazitaeten(&mut self, items: &[Item], pfad: &str) {
        for i in items {
            match &i.art {
                ItemArt::Modul(m) => {
                    let innen = qualifiziere(pfad, &m.pfad.text());
                    self.sammle_kapazitaeten(&m.items, &innen);
                }
                ItemArt::Tabelle(t) => {
                    if let Some(n) = t
                        .kapazitaet
                        .as_ref()
                        .and_then(|e| self.konst_wert(pfad, e))
                        .filter(|n| *n > 0)
                    {
                        self.kapazitaeten
                            .insert(qualifiziere(pfad, &t.name.text), n as u128);
                    }
                }
                _ => {}
            }
        }
    }

    /// **Namensaufloesung.** Ein Name gilt zuerst im eigenen Modul, dann in den umgebenden,
    /// dann an der Wurzel, zuletzt ueber eine `use`-Zeile. *Ohne diese Ordnung verdeckt ein
    /// gleichnamiges `fn` in einem fremden Modul die Deklaration -- und mit ihr die
    /// Bereichspruefung, still.*
    pub fn kandidaten_oeffentlich(&self, von: &str, pfad: &str) -> Vec<String> {
        self.kandidaten(von, pfad)
    }

    fn kandidaten(&self, von: &str, pfad: &str) -> Vec<String> {
        let mut out = Vec::new();
        // Im eigenen Modul und in jedem umgebenden, von innen nach aussen.
        let mut umgebung = von.to_string();
        loop {
            out.push(if umgebung.is_empty() {
                pfad.to_string()
            } else {
                format!("{umgebung}::{pfad}")
            });
            match umgebung.rfind("::") {
                Some(i) => umgebung.truncate(i),
                None => {
                    if umgebung.is_empty() {
                        break;
                    }
                    umgebung.clear();
                }
            }
        }
        // Ueber eine `use`-Zeile des eigenen Moduls: `use a::b::Ding;` macht `Ding` sichtbar.
        let kurz = pfad.rsplit("::").next().unwrap_or(pfad);
        let mut modul = von.to_string();
        loop {
            if let Some(zeilen) = self.verwendet.get(&modul) {
                for z in zeilen {
                    if z.rsplit("::").next() == Some(kurz) {
                        out.push(z.clone());
                    }
                }
            }
            match modul.rfind("::") {
                Some(i) => modul.truncate(i),
                None => {
                    if modul.is_empty() {
                        break;
                    }
                    modul.clear();
                }
            }
        }
        out
    }

    fn suche<'a, T>(
        &self,
        karte: &'a HashMap<String, T>,
        von: &str,
        pfad: &str,
    ) -> Option<&'a T> {
        self.kandidaten(von, pfad)
            .into_iter()
            .find_map(|k| karte.get(&k))
    }

    pub fn funktion(&self, von: &str, pfad: &Pfad) -> Option<&Signatur> {
        self.suche(&self.funktionen, von, &pfad.text())
    }

    /// **Nennt dieser Pfad einen Verbundtyp?** («B7»)
    ///
    /// Die Frage steht neben `funktion` und nicht in ihr, weil beide Antworten gebraucht
    /// werden: der Konstruktor hat eine Signatur *wie* eine Funktion, und M1 muss trotzdem
    /// wissen, dass er eine ist -- sonst faellt `P(1, true)` (ohne Marken) still durch.
    /// Ein globaler Traeger, **modulbewusst** -- die Schluessel sind qualifiziert.
    ///
    /// *Die Karte direkt zu befragen war ein Loch in `M103`:* in einem `module`-Block traf
    /// `globale.get("Kappenraum")` nie, und die Indexschranke sagte nichts.
    pub fn suche_global(&self, von: &str, name: &str) -> Option<&Typ> {
        self.suche(&self.globale, von, name)
    }

    pub fn verbundfelder(&self, von: &str, pfad: &Pfad) -> Option<&Vec<String>> {
        self.suche(&self.verbundtypen, von, &pfad.text())
    }

    fn sammle_roh(&mut self, items: &[Item], pfad: &str) {
        for i in items {
            match &i.art {
                ItemArt::Modul(m) => {
                    let innen = qualifiziere(pfad, &m.pfad.text());
                    self.sammle_roh(&m.items, &innen);
                }
                ItemArt::Use(u) => {
                    self.verwendet
                        .entry(pfad.to_string())
                        .or_default()
                        .push(u.pfad.text());
                }
                ItemArt::Typ(t) => {
                    self.roh_typen
                        .insert(qualifiziere(pfad, &t.name.text), t.clone());
                }
                ItemArt::Konst(k) => {
                    self.roh_konst
                        .insert(qualifiziere(pfad, &k.name.text), k.wert.clone());
                }
                ItemArt::Funktion(f) if matches!(f.klasse, Some(FnKlasse::Konst)) => {
                    if let FnRumpf::Block(b) = &f.rumpf {
                        if let [Stmt { art: StmtArt::Return(Some(w)), .. }] = &b.anweisungen[..] {
                            self.konst_fn.insert(
                                qualifiziere(pfad, &f.name.text),
                                (
                                    f.parameter.iter().map(|p| p.name.text.clone()).collect(),
                                    w.clone(),
                                ),
                            );
                        }
                    }
                }
                ItemArt::Tabelle(t) => {
                    // Die Konstanten einer Tabelle gehoeren in ihren Modulpfad, nicht in
                    // den der Tabelle -- `table` ist kein Geltungsbereich der Grammatik.
                    for k in &t.konstanten {
                        self.roh_konst
                            .insert(qualifiziere(pfad, &k.name.text), k.wert.clone());
                    }
                }
                _ => {}
            }
        }
    }

    /// Traeger sind alles, was einen Typ hat, aber keinen erzeugt.
    fn sammle_traeger(&mut self, items: &[Item], pfad: &str) {
        for i in items {
            let q = |name: &str| qualifiziere(pfad, name);
            match &i.art {
                ItemArt::Modul(m) => {
                    let innen = qualifiziere(pfad, &m.pfad.text());
                    self.sammle_traeger(&m.items, &innen);
                }
                ItemArt::Konst(k) => {
                    let mut t = self.typ_von_ausdruck_decl(pfad, &k.typ);
                    // **«F»: eine Konstante ist so endlich wie ihr Initialisierer.**
                    //
                    // `const HALB : f64 = 0.5;` deklariert `f64` -- und `f64` kann NaN sein.
                    // Der WERT kann es nicht. Ohne diese Zeile waere der deklarierte Typ
                    // weiter als die Konstante, und jede Benutzung braeuchte eine Verengung
                    // gegen etwas, das schon feststeht.
                    //
                    // *Ein `const` mit bekannt endlichem Initialisierer ist der reinste Fall,
                    // den es gibt* -- und er faellt hier an, nicht in einem zweiten Pass.
                    if let (Typ::Gleitkomma(mut f), Some(w)) =
                        (t.clone(), self.gleitwert(&k.wert))
                    {
                        if w.is_finite() {
                            f.kann_nan = false;
                            f.kann_unendlich = false;
                            // **Und ihr WERT, nicht nur ihre zwei Bits.** Die erste Fassung
                            // loeschte nur NaN und Unendlich und liess das Intervall offen --
                            // dann war `const HALB : f64 = 0.5;` „endlich, sonst unbekannt",
                            // und `return HALB;` fiel gegen jeden genannten Bereich. *Eine
                            // Konstante ist ihr Wert.*
                            f.lo = w;
                            f.hi = w;
                            t = Typ::Gleitkomma(f);
                        }
                    }
                    self.globale.insert(q(&k.name.text), t);
                }
                ItemArt::Statisch(s) => {
                    let t = self.typ_von_ausdruck_decl(pfad, &s.typ);
                    self.globale.insert(q(&s.name.text), t);
                }
                ItemArt::Atomic(a) => {
                    let t = self.typ_von_ausdruck_decl(pfad, &a.typ);
                    self.globale.insert(q(&a.name.text), t);
                }
                ItemArt::Accumulates(a) => {
                    let t = self.typ_von_ausdruck_decl(pfad, &a.typ);
                    self.globale.insert(q(&a.name.text), t);
                }
                ItemArt::Tabelle(t) => {
                    let felder = t
                        .slot
                        .as_ref()
                        .map(|s| {
                            s.felder
                                .iter()
                                .map(|f| (f.name.text.clone(), self.typ_von_slottyp(pfad, &f.typ)))
                                .collect::<Vec<_>>()
                        })
                        .unwrap_or_default();
                    if let Some(n) = t
                        .kapazitaet
                        .as_ref()
                        .and_then(|e| self.konst_wert(pfad, e))
                        .filter(|n| *n > 0)
                    {
                        self.kapazitaeten.insert(q(&t.name.text), n as u128);
                    }
                    // (die Walk-Schranke steht weiter unten, bei `ItemArt::Walk`)
                    // **Eine `table` IST Speicher, nicht nur eine Form.** Damit ist ihr
                    // Name ein globaler Ort: `Kappenraum.slots[s]` hat einen Typ, und
                    // Kernzustand braucht keinen Zeiger, um erreichbar zu sein.
                    //
                    // Das loest den Ursprung der Eigentumskette dort, wo er wirklich sitzt:
                    // es gibt EINEN Kappenraum, kein Paar von Zeigern -- also auch kein
                    // Alias. Caprock hat es genauso (`CAPS.write().cspace`, eine Instanz
                    // hinter einer Sperre); die `&mut`-Parameter sind Rusts Leihform, nicht
                    // die Struktur der Sache.
                    self.globale
                        .insert(q(&t.name.text), Typ::Tabelle(q(&t.name.text)));
                    self.tabellen.insert(q(&t.name.text), felder);
                }
                ItemArt::Format(f) => {
                    let felder = f
                        .felder
                        .iter()
                        .map(|fd| (fd.name.text.clone(), self.typ_von_feld(pfad, fd)))
                        .collect();
                    self.formate.insert(q(&f.name.text), felder);
                }
                ItemArt::Device(d) => {
                    let mut felder = Vec::new();
                    for r in &d.register {
                        felder.push((r.name.text.clone(), self.typ_von_reg(pfad, r)));
                    }
                    for b in &d.baenke {
                        let inner: Vec<(String, Typ)> = b
                            .register
                            .iter()
                            .map(|r| (r.name.text.clone(), self.typ_von_reg(pfad, r)))
                            .collect();
                        felder.push((
                            b.name.text.clone(),
                            Typ::Feld {
                                element: Box::new(Typ::Verbund(inner)),
                                laenge: self.konst_wert(pfad, &b.anzahl).map(|v| v.max(0) as u128),
                            },
                        ));
                    }
                    // **Ein `transition` ist aufrufbar** (`wurzel_setzen(v);`), hat aber
                    // keine `costs`-Klausel in der Grammatik. Seine Kosten stehen fest: je
                    // `placeshift` ein Speichern, dazu die `requires`-Pruefung.
                    for t in &d.uebergaenge {
                        self.uebergangskosten
                            .insert(q(&t.name.text), t.schritte.len() as i128 + 1);
                        self.funktionen.insert(
                            q(&t.name.text),
                            Signatur {
                                parameter: Vec::new(),
                                ergebnis: None,
                                span: t.span,
                            },
                        );
                    }
                    // **Die Parameterliste eines `device` IST sein Konstruktor.**
                    // `device Vtd(basis : Pa) at mmio` sagt: aus einer `Pa` wird ein Vtd.
                    // Damit hat auch die zweite Klasse von Zustand ihren Ursprung -- und
                    // wieder ohne Zeiger, also ohne Aliasfrage.
                    // Der Konstruktor kostet nichts: die Adresse IST der Griff.
                    self.uebergangskosten.insert(q(&d.name.text), 0);
                    self.funktionen.insert(
                        q(&d.name.text),
                        Signatur {
                            parameter: d
                                .parameter
                                .iter()
                                .map(|prm| {
                                    (prm.name.text.clone(), self.typ_von_ausdruck_decl(pfad, &prm.typ))
                                })
                                .collect(),
                            ergebnis: Some(Typ::Verbundname(q(&d.name.text))),
                            span: d.span,
                        },
                    );
                    self.geraete.insert(q(&d.name.text), felder);
                }
                // **«B7»: die Felderliste eines `type` IST sein Konstruktor** -- genau die
                // Bauart, die `device` seit dem 2026-08-14 traegt (`Vtd(basis)`, oben).
                //
                // Damit bekommt `P(a: 1, b: true)` seine Signatur aus DERSELBEN Karte wie
                // jeder Aufruf, und die Paesse, die den Gerufenen nachschlagen (M1, Kosten,
                // `geteilt`, M2), finden ihn, statt ihn als unbekannt zu fuehren. *Ein
                // unbekannter Gerufener macht jede Huelle darueber zur unteren Schranke* --
                // dieser eine Eintrag ist der Unterschied zwischen einer Messung und einer.
                //
                // Nur ein VERBUND bekommt einen: `type Zaehler = u32 in 0 .. 9` ist ein
                // Bereichstyp, und `Zaehler(3)` waere eine Umwandlung, keine Herstellung.
                ItemArt::Typ(t) => {
                    // `durchgreifen`: ein benannter Typ ist `Benannt { unter }`, und der
                    // Verbund steht darunter. **Ohne diesen Griff war die Karte leer und
                    // jede Absage darunter unerreichbar** -- gefunden an der ersten Probe.
                    if let Typ::Verbund(felder) = self
                        .typen
                        .get(&q(&t.name.text))
                        .map(|x| x.durchgreifen())
                        .unwrap_or(&Typ::Unbekannt)
                    {
                        if !felder.is_empty() && !t.opaque {
                            let sig = Signatur {
                                parameter: felder.clone(),
                                ergebnis: Some(Typ::Verbund(felder.clone())),
                                span: t.span,
                            };
                            self.funktionen.insert(q(&t.name.text), sig);
                            self.verbundtypen.insert(
                                q(&t.name.text),
                                felder.iter().map(|(n, _)| n.clone()).collect(),
                            );
                        }
                    }
                }
                ItemArt::Funktion(f) => {
                    let sig = Signatur {
                        parameter: f
                            .parameter
                            .iter()
                            .map(|p| (p.name.text.clone(), self.typ_von_ausdruck_decl(pfad, &p.typ)))
                            .collect(),
                        ergebnis: f.ergebnis.as_ref().map(|t| self.typ_von_ausdruck_decl(pfad, t)),
                        span: f.span,
                    };
                    self.funktionen.insert(q(&f.name.text), sig);
                }
                ItemArt::Axiom(a) => {
                    let sig = Signatur {
                        parameter: a
                            .parameter
                            .iter()
                            .map(|p| (p.name.text.clone(), self.typ_von_ausdruck_decl(pfad, &p.typ)))
                            .collect(),
                        ergebnis: None,
                        span: a.span,
                    };
                    self.funktionen.insert(q(&a.name.text), sig);
                }
                // **`walk` traegt seine Schranke selbst:** `levels` mal Knotenlaenge.
                // Ohne sie hat die Domaene `mappings of` keine, und der Kostenpass sagt das
                // (`K003`) -- gefunden am MMU-Fragment 2026-08-16, dieselbe Klasse wie die
                // `queue`-Domaene: eine Schranke, die dasteht und die niemand las.
                ItemArt::Walk(w) => {
                    // **Ein `walk` ist auch ein TYP.** Ohne diese Zeile ist
                    // `ptr<normal, r> Seitenabstieg` dem Typsystem unbekannt, und die
                    // Domaenenschranke unten findet ihren Namen nicht -- gefunden am
                    // MMU-Fragment, nachdem die Schranke selbst schon dastand.
                    self.typen
                        .insert(q(&w.name.text), Typ::Verbundname(q(&w.name.text)));
                    let ebenen = self.konst_wert(pfad, &w.ebenen);
                    let laenge = self.konst_wert(pfad, &w.knoten.laenge);
                    if let (Some(e), Some(l)) = (ebenen, laenge) {
                        if e > 0 && l > 0 {
                            self.walkschranken
                                .insert(q(&w.name.text), (e as u128) * (l as u128));
                        }
                    }
                }
                _ => {}
            }
        }
    }

    // -- Konstanten ---------------------------------------------------------------------

    fn konst_aufloesen(
        &self,
        von: &str,
        pfad: &str,
        unterwegs: &mut HashSet<String>,
    ) -> Option<i128> {
        let voll = self
            .kandidaten(von, pfad)
            .into_iter()
            .find(|k| self.konstanten.contains_key(k) || self.roh_konst.contains_key(k))?;
        if let Some(w) = self.konstanten.get(&voll) {
            return Some(*w);
        }
        if !unterwegs.insert(voll.clone()) {
            return None; // Zyklus -- kein Wert, keine Behauptung.
        }
        let e = self.roh_konst.get(&voll)?.clone();
        self.auswerten(modul_von(&voll), &e, unterwegs)
    }

    /// Der Wert eines `constexpr`, wenn er zur Uebersetzungszeit feststeht.
    pub fn konst_wert(&self, von: &str, e: &Expr) -> Option<i128> {
        let mut unterwegs = HashSet::new();
        self.auswerten(von, e, &mut unterwegs)
    }

    /// Wie `auswerten`, aber mit gebundenen Parameternamen -- der Rumpf eines `const fn`.
    fn auswerten_mit(
        &self,
        von: &str,
        e: &Expr,
        werte: &HashMap<String, i128>,
        unterwegs: &mut HashSet<String>,
    ) -> Option<i128> {
        if let ExprArt::Ort(o) = &e.art {
            if o.suffixe.is_empty() {
                if let Some(v) = werte.get(&o.basis.text) {
                    return Some(*v);
                }
            }
        }
        match &e.art {
            ExprArt::Klammer(i) => self.auswerten_mit(von, i, werte, unterwegs),
            ExprArt::Unaer(UnOp::Negativ, i) => {
                self.auswerten_mit(von, i, werte, unterwegs).map(|v| -v)
            }
            ExprArt::Binaer(op, a, b) => {
                let x = self.auswerten_mit(von, a, werte, unterwegs)?;
                let y = self.auswerten_mit(von, b, werte, unterwegs)?;
                // Dieselbe Rechnung wie unten, ueber einem Ersatzbaum -- die Bruecke ist
                // schmal genug, dass zwei Zahlen sie tragen.
                let za = Expr { art: ExprArt::Zahl(u128::try_from(x).ok()?), span: a.span };
                let zb = Expr { art: ExprArt::Zahl(u128::try_from(y).ok()?), span: b.span };
                self.auswerten(
                    von,
                    &Expr {
                        art: ExprArt::Binaer(*op, Box::new(za), Box::new(zb)),
                        span: e.span,
                    },
                    unterwegs,
                )
            }
            _ => self.auswerten(von, e, unterwegs),
        }
    }

    fn auswerten(&self, von: &str, e: &Expr, unterwegs: &mut HashSet<String>) -> Option<i128> {
        match &e.art {
            ExprArt::Zahl(v) => i128::try_from(*v).ok(),
            ExprArt::Wahr => Some(1),
            ExprArt::Falsch => Some(0),
            ExprArt::Klammer(i) => self.auswerten(von, i, unterwegs),
            ExprArt::Unaer(UnOp::Negativ, i) => self.auswerten(von, i, unterwegs).map(|v| -v),
            ExprArt::Unaer(UnOp::Nicht, i) => {
                self.auswerten(von, i, unterwegs).map(|v| i128::from(v == 0))
            }
            ExprArt::Ort(o) => {
                // `u64::max` und `i32::min` -- die Grenzen einer Breite als Konstante.
                if o.suffixe.len() == 1 {
                    if let (Some(kw), OrtSuffix::Feld(f)) =
                        (Kw::suche(&o.basis.text), &o.suffixe[0])
                    {
                        if kw.ist_intty() {
                            let (breite, vz) = breite_von(kw);
                            let (lo, hi) = grenzen(breite, vz);
                            return match f.text.as_str() {
                                "max" => Some(hi),
                                "min" => Some(lo),
                                _ => None,
                            };
                        }
                    }
                }
                if !o.suffixe.is_empty() {
                    return None;
                }
                self.konst_aufloesen(von, &o.basis.text, unterwegs)
            }
            ExprArt::Binaer(op, a, b) => {
                let x = self.auswerten(von, a, unterwegs)?;
                let y = self.auswerten(von, b, unterwegs)?;
                Some(match op {
                    BinOp::Plus => x.checked_add(y)?,
                    BinOp::Minus => x.checked_sub(y)?,
                    BinOp::Mal => x.checked_mul(y)?,
                    BinOp::Geteilt => {
                        if y == 0 {
                            return None;
                        }
                        x / y
                    }
                    BinOp::Rest => {
                        if y == 0 {
                            return None;
                        }
                        x % y
                    }
                    BinOp::BitUnd => x & y,
                    BinOp::BitOder => x | y,
                    BinOp::BitXor => x ^ y,
                    BinOp::SchiebLinks => {
                        if !(0..127).contains(&y) {
                            return None;
                        }
                        x.checked_shl(y as u32)?
                    }
                    BinOp::SchiebRechts => {
                        if !(0..127).contains(&y) {
                            return None;
                        }
                        x >> y
                    }
                    BinOp::Gleich => i128::from(x == y),
                    BinOp::Ungleich => i128::from(x != y),
                    BinOp::Kleiner => i128::from(x < y),
                    BinOp::KleinerGleich => i128::from(x <= y),
                    BinOp::Groesser => i128::from(x > y),
                    BinOp::GroesserGleich => i128::from(x >= y),
                    BinOp::Und => i128::from(x != 0 && y != 0),
                    BinOp::Oder => i128::from(x != 0 || y != 0),
                })
            }
            // **Ein `const fn` wird HIER gerechnet, und nur hier.**
            //
            // Die Argumente werden zuerst ausgewertet -- schlaegt eines fehl, schlaegt der
            // Ruf fehl. *Ein `const fn` mit einem nicht-konstanten Argument ist kein
            // konstanter Ausdruck, und es waere die kleinere Luege, ihn zu raten.*
            //
            // `unterwegs` traegt den Rekursionsschutz: ein `const fn`, das sich selbst ruft,
            // liefert `None` statt zu haengen. **Das ist keine Nachsicht -- es ist dieselbe
            // Schranke, die die Sprache ihren Schleifen auferlegt.**
            ExprArt::Ruf(r) => {
                let name = self
                    .kandidaten(von, &r.pfad.text())
                    .into_iter()
                    .find(|k| self.konst_fn.contains_key(k))?;
                if !unterwegs.insert(format!("constfn:{name}")) {
                    return None;
                }
                let (params, rumpf) = self.konst_fn.get(&name)?.clone();
                if params.len() != r.argumente.len() {
                    return None;
                }
                let mut werte = HashMap::new();
                for (p, a) in params.iter().zip(r.argumente.iter()) {
                    werte.insert(p.clone(), self.auswerten(von, a, unterwegs)?);
                }
                let erg = self.auswerten_mit(modul_von(&name), &rumpf, &werte, unterwegs);
                unterwegs.remove(&format!("constfn:{name}"));
                erg
            }
            // `sizeof`/`lenof` brauchen das Layout; das entscheidet die Absenkung, nicht M1.
            _ => None,
        }
    }

    // -- Typen --------------------------------------------------------------------------

    fn typ_aufloesen(&self, von: &str, pfad: &str, unterwegs: &mut HashSet<String>) -> Typ {
        let Some(voll) = self
            .kandidaten(von, pfad)
            .into_iter()
            .find(|k| self.typen.contains_key(k) || self.roh_typen.contains_key(k))
        else {
            return Typ::Unbekannt;
        };
        let name = voll.as_str();
        if let Some(t) = self.typen.get(name) {
            return t.clone();
        }
        if !unterwegs.insert(name.to_string()) {
            return Typ::Unbekannt;
        }
        let Some(d) = self.roh_typen.get(name) else {
            return Typ::Unbekannt;
        };
        let d = d.clone();
        let von = modul_von(name).to_string();
        let von = von.as_str();
        let unter = match &d.rumpf {
            Some(r) => self.typexpr(von, r, unterwegs),
            // `linear type Parked;` -- ein Typ ohne Rumpf traegt nur seinen Namen.
            None => Typ::Unbekannt,
        };
        if d.tagged {
            if let Typ::Summe { varianten, .. } = unter {
                return Typ::Summe {
                    name: name.to_string(),
                    varianten,
                };
            }
        }
        Typ::Benannt {
            name: name.to_string(),
            undurchsichtig: d.opaque,
            unter: Box::new(unter),
        }
    }

    pub fn typ_von_ausdruck_decl(&self, von: &str, t: &TypExpr) -> Typ {
        let mut unterwegs = HashSet::new();
        self.typexpr(von, t, &mut unterwegs)
    }

    /// **«F»: der Wert einer Bereichsgrenze eines Gleitkommatyps.**
    ///
    /// Nimmt ein Gleitkommaliteral und eine Ganzzahl (`f64 in 0 .. 1` soll schreibbar sein).
    /// *Ein Ausdruck, der erst gerechnet werden muesste, gibt `None` -- und dann bleibt der
    /// volle Bereich stehen, was die sichere Richtung ist.*
    pub fn gleitwert(&self, e: &Expr) -> Option<f64> {
        match &e.art {
            ExprArt::Gleitkomma { bits, .. } => Some(f64::from_bits(*bits)),
            ExprArt::Zahl(v) => Some(*v as f64),
            ExprArt::Unaer(UnOp::Negativ, i) => self.gleitwert(i).map(|w| -w),
            ExprArt::Klammer(i) => self.gleitwert(i),
            _ => None,
        }
    }

    fn typexpr(&self, von: &str, t: &TypExpr, unterwegs: &mut HashSet<String>) -> Typ {
        match t {
            TypExpr::Int(i) => Typ::Ganzzahl(self.intbereich(von, i, unterwegs)),
            // **«F»:** ein deklarierter Gleitkommawert kann ALLES sein, NaN eingeschlossen.
            // *Der Bereich am Typ verengt das Intervall, nicht die zwei Bits* -- wer NaN
            // ausschliessen will, tut es mit `narrow … to finite`, und dort steht dann auch
            // die Laufzeitpruefung (W6).
            TypExpr::Float(f) => {
                let breite = if f.wort == gabbro_syntax::kw::Kw::F32 { 32 } else { 64 };
                let mut b = crate::typen::FBereich::voll(breite);
                if let Some(r) = &f.bereich {
                    if let (Some(lo), Some(hi)) = (self.gleitwert(&r.von), self.gleitwert(&r.bis)) {
                        b.lo = lo;
                        b.hi = hi;
                        b.kann_unendlich = lo.is_infinite() || hi.is_infinite();
                        // Ein GENANNTER Bereich schliesst NaN aus: NaN liegt in keinem
                        // Intervall, weil jeder Vergleich mit ihm falsch ist.
                        b.kann_nan = false;
                    }
                }
                Typ::Gleitkomma(b)
            }
            TypExpr::Bool(_) => Typ::Wahrheit,
            TypExpr::Never(_) => Typ::Nie,
            TypExpr::Pfad(p) => {
                let name = p
                    .teile
                    .last()
                    .map(|i| i.text.clone())
                    .unwrap_or_default();
                // Der Name wird HIER aufgeloest, im Modul des Gebrauchs -- ein
                // gleichnamiger Typ in einem fremden Modul verdeckt ihn damit nicht mehr.
                let kand = self.kandidaten(von, &name);
                // **Erschoepfend ueber die Traegerarten, ohne Auffangzweig.** Bis
                // 2026-08-16 war das eine `if-else`-Kette ueber Karten, und ein `walk`
                // fiel still durch: `ptr<normal, r> Seitenabstieg` war `Unbekannt`, die
                // Schranke der Domaene `mappings of` fand ihren Namen nie -- **obwohl die
                // Schranke selbst schon dastand.**
                //
                // *Eine gefuellte Karte ist kein Beleg fuer eine vollstaendige Karte.*
                // `Unbekannt` fiel nicht ab, es lief als leerer Eintrag mit.
                //
                // Der `match` unten hat **keinen `_`-Zweig**: eine neue Traegerart ist ab
                // jetzt ein UEBERSETZUNGSFEHLER an jeder Aufloesungsstelle, die sie nicht
                // behandelt. **Dieselbe D2-Medizin, die die Sprache ihren Nutzern
                // verschreibt, auf den Pruefer selbst angewandt.**
                Traegerart::ALLE
                    .iter()
                    .find_map(|art| {
                        let treffer = kand.iter().find(|k| match art {
                            Traegerart::Neutyp => self.roh_typen.contains_key(*k),
                            Traegerart::Tabelle => self.tabellen.contains_key(*k),
                            Traegerart::Format => self.formate.contains_key(*k),
                            Traegerart::Geraet => self.geraete.contains_key(*k),
                            Traegerart::Walk => self.walkschranken.contains_key(*k),
                        })?;
                        Some((*art, treffer.clone()))
                    })
                    .map_or(Typ::Unbekannt, |(art, k)| match art {
                        Traegerart::Neutyp => {
                            self.typ_aufloesen(modul_von(&k), kurzname(&k), unterwegs)
                        }
                        Traegerart::Tabelle => Typ::Tabelle(k),
                        Traegerart::Format | Traegerart::Geraet | Traegerart::Walk => {
                            Typ::Verbundname(k)
                        }
                    })
            }
            TypExpr::Feld(a) => Typ::Feld {
                element: Box::new(self.typexpr(von, &a.element, unterwegs)),
                laenge: self.konst_wert(von, &a.laenge).map(|v| v.max(0) as u128),
            },
            TypExpr::Zeiger(p) => Typ::Zeiger(Box::new(self.typexpr(von, &p.ziel, unterwegs))),
            TypExpr::Verbund(felder, _) => Typ::Verbund(
                felder
                    .iter()
                    .map(|f| (f.name.text.clone(), self.typ_von_feld(von, f)))
                    .collect(),
            ),
            TypExpr::FnZeiger(_) => Typ::Unbekannt,
            // **A3.** `index into T` erbt die Schranke aus `T`s `count`. Ohne `count` bleibt
            // sie offen -- und das ist dann eine Aussage der Deklaration, keine Konvention.
            TypExpr::Index { tabelle, .. } => {
                let bereich = self
                    .kandidaten(von, &tabelle.text)
                    .into_iter()
                    .find_map(|k| self.kapazitaeten.get(&k).copied())
                    .map(|n| IntBereich::genau(32, false, 0, n as i128 - 1))
                    .unwrap_or_else(|| IntBereich::voll(32, false));
                Typ::Benannt {
                    name: format!("index into {}", tabelle.text),
                    undurchsichtig: false,
                    unter: Box::new(Typ::Ganzzahl(bereich)),
                }
            }
            TypExpr::Varianten(v, _) => Typ::Summe {
                name: String::new(),
                varianten: v
                    .iter()
                    .map(|va| {
                        (
                            va.name.text.clone(),
                            va.nutzlast.as_ref().map(|n| self.typexpr(von, n, unterwegs)),
                        )
                    })
                    .collect(),
            },
        }
    }

    fn intbereich(&self, von: &str, i: &IntTy, unterwegs: &mut HashSet<String>) -> IntBereich {
        let (breite, vz) = breite_von(i.wort);
        let Some(b) = &i.bereich else {
            return IntBereich::voll(breite, vz);
        };
        let untere = self.auswerten(von, &b.von, &mut unterwegs.clone());
        let obere = self.auswerten(von, &b.bis, &mut unterwegs.clone());
        match (untere, obere) {
            (Some(lo), Some(hi)) => {
                let hi = if b.exklusiv { hi - 1 } else { hi };
                IntBereich::genau(breite, vz, lo, hi)
            }
            // Eine Grenze, die nicht feststeht, macht den Bereich NICHT enger.
            _ => IntBereich::voll(breite, vz),
        }
    }

    fn typ_von_feld(&self, von: &str, f: &FeldDecl) -> Typ {
        let mut unterwegs = HashSet::new();
        let grund = self.typexpr(von, &f.typ.typ, &mut unterwegs);
        match (&f.bitpos, grund.bereich()) {
            // Ein Bitfeld traegt den Bereich seiner Bits, nicht den seines Grundtyps.
            (Some(BitPos::Bit(_)), Some(b)) => {
                Typ::Ganzzahl(IntBereich::genau(b.breite, false, 0, 1))
            }
            (Some(BitPos::Bereich(h, t)), Some(b)) => {
                let breite_feld = (h.max(t) - h.min(t) + 1) as u32;
                let max = if breite_feld >= 127 {
                    b.max
                } else {
                    (1i128 << breite_feld) - 1
                };
                Typ::Ganzzahl(IntBereich::genau(b.breite, false, 0, max.min(b.max)))
            }
            _ => grund,
        }
    }

    fn typ_von_slottyp(&self, von: &str, s: &SlotTyp) -> Typ {
        let mut unterwegs = HashSet::new();
        match s {
            SlotTyp::Typ(t) => self.typexpr(von, t, &mut unterwegs),
            SlotTyp::Wrapping(i) => Typ::Umlaufend(self.intbereich(von, i, &mut unterwegs)),
        }
    }

    fn typ_von_reg(&self, von: &str, r: &RegDecl) -> Typ {
        let mut unterwegs = HashSet::new();
        let bereich = self.intbereich(von, &r.typ, &mut unterwegs);
        let felder = r
            .felder
            .iter()
            .map(|(name, bp)| {
                let b = match bp {
                    BitPos::Bit(_) => IntBereich::genau(bereich.breite, false, 0, 1),
                    BitPos::Bereich(h, t) => {
                        let w = (h.max(t) - h.min(t) + 1) as u32;
                        let max = if w >= 127 { bereich.max } else { (1i128 << w) - 1 };
                        IntBereich::genau(bereich.breite, false, 0, max)
                    }
                };
                (name.text.clone(), b)
            })
            .collect();
        Typ::Register {
            bereich,
            felder,
            umlaufend: r.umlaufend,
        }
    }

    /// Der Typ eines Ortes, gegeben die lokalen Bindungen.
    pub fn typ_von_ort(&self, von: &str, ort: &Ort, lokal: &HashMap<String, Typ>) -> Typ {
        let mut aktuell = lokal
            .get(&ort.basis.text)
            .cloned()
            .or_else(|| self.suche(&self.globale, von, &ort.basis.text).cloned())
            .unwrap_or(Typ::Unbekannt);

        for suffix in &ort.suffixe {
            aktuell = match suffix {
                OrtSuffix::Feld(f) | OrtSuffix::Ueber(f) => self.feld_von(von, &aktuell, &f.text),
                OrtSuffix::Index(_) => match aktuell.durchgreifen() {
                    Typ::Feld { element, .. } => (**element).clone(),
                    _ => Typ::Unbekannt,
                },
            };
            if aktuell.ist_unbekannt() {
                return Typ::Unbekannt;
            }
        }
        aktuell
    }

    pub fn feld_von(&self, _von: &str, traeger: &Typ, name: &str) -> Typ {
        match traeger.durchgreifen() {
            Typ::Tabelle(t) => {
                // `c.slots` ist das Slotfeld der Tabelle; jeder andere Name ist keiner.
                if name == "slots" {
                    let felder = self.tabellen.get(t).cloned().unwrap_or_default();
                    Typ::Feld {
                        element: Box::new(Typ::Verbund(felder)),
                        // **A3.** Mit `count N` bekommt M4 hier zum ersten Mal eine
                        // Schranke aus der Sprache statt aus einer Konvention.
                        laenge: self.kapazitaeten.get(t).copied(),
                    }
                } else {
                    Typ::Unbekannt
                }
            }
            Typ::Verbundname(n) => {
                let felder = self
                    .formate
                    .get(n)
                    .or_else(|| self.geraete.get(n))
                    .cloned()
                    .unwrap_or_default();
                felder
                    .iter()
                    .find(|(f, _)| f == name)
                    .map(|(_, t)| t.clone())
                    .unwrap_or(Typ::Unbekannt)
            }
            Typ::Verbund(felder) => felder
                .iter()
                .find(|(f, _)| f == name)
                .map(|(_, t)| t.clone())
                .unwrap_or(Typ::Unbekannt),
            Typ::Register { felder, .. } => felder
                .iter()
                .find(|(f, _)| f == name)
                .map(|(_, b)| Typ::Ganzzahl(*b))
                .unwrap_or(Typ::Unbekannt),
            _ => Typ::Unbekannt,
        }
    }
}

pub fn breite_von(k: Kw) -> (u8, bool) {
    match k {
        Kw::U8 => (8, false),
        Kw::U16 => (16, false),
        Kw::U32 => (32, false),
        Kw::U64 => (64, false),
        Kw::I8 => (8, true),
        Kw::I16 => (16, true),
        Kw::I32 => (32, true),
        Kw::I64 => (64, true),
        _ => (64, false),
    }
}

/// **Wertetabellen fuer die Konstantenauswertung — der zweite Fundort des Generatorlaufs.**
///
/// 5 der 15 echten Luecken vom 2026-08-15 lagen hier. Der Grund ist derselbe wie in
/// `typen.rs`: **eine Beispieldatei prueft, ob eine Absage faellt, nicht ob eine Zahl
/// stimmt.** Ein `const N : u32 = 100;` mit falscher Auswertung faellt in keinem Beispiel
/// auf, solange das Ergebnis irgendwo im gueltigen Bereich landet.
#[cfg(test)]
mod wertetabellen {
    use super::*;

    /// Wertet einen konstanten Ausdruck aus einer Quelle aus -- die kuerzeste Strecke von
    /// Text zu Zahl, damit die Probe die RECHNUNG misst und nicht den Aufbau.
    fn wert(ausdruck: &str) -> Option<i128> {
        let quelle = format!("module t {{ const K : u64 = {ausdruck}; }}");
        let (baum, _) = gabbro_syntax::lies("probe.gab", &quelle);
        let u = Umgebung::sammle(&baum);
        let mut aus = None;
        crate::fuer_jedes_item_im_modul(&baum, &mut |item, modul| {
            if let ItemArt::Konst(k) = &item.art {
                aus = u.konst_wert(modul, &k.wert);
            }
        });
        aus
    }

    #[test]
    fn die_logischen_verknuepfungen_sind_und_und_oder_und_nicht_umgekehrt() {
        // Die Kante: genau eine Seite wahr. `&&` und `||` sind dort unterscheidbar,
        // bei zwei wahren oder zwei falschen Seiten nicht.
        assert_eq!(wert("1 && 0"), Some(0), "one side false -> AND is false");
        assert_eq!(wert("1 || 0"), Some(1), "one side true -> OR is true");
        assert_eq!(wert("0 && 1"), Some(0));
        assert_eq!(wert("0 || 1"), Some(1));
        // Und die Null-Deutung: jeder Wert != 0 ist wahr, nicht nur 1.
        assert_eq!(wert("2 && 3"), Some(1), "!= 0 is true, not only == 1");
        assert_eq!(wert("0 || 0"), Some(0));
    }

    #[test]
    fn die_vergleiche_stehen_auf_ihrer_kante() {
        // Jeder Vergleich wird an der Stelle geprueft, an der er sich vom Nachbarn trennt.
        assert_eq!(wert("3 < 3"), Some(0));
        assert_eq!(wert("3 <= 3"), Some(1), "hier trennt sich < von <=");
        assert_eq!(wert("3 > 3"), Some(0));
        assert_eq!(wert("3 >= 3"), Some(1), "und hier > von >=");
        assert_eq!(wert("3 == 3"), Some(1));
        assert_eq!(wert("3 != 3"), Some(0));
    }

    #[test]
    fn die_verschiebungen_rechnen_und_raten_nicht() {
        assert_eq!(wert("1 << 0"), Some(1));
        assert_eq!(wert("1 << 10"), Some(1024));
        assert_eq!(wert("1024 >> 10"), Some(1));
        assert_eq!(wert("7 >> 1"), Some(3), "truncate, do not round");
    }

    #[test]
    fn grundrechenarten_an_ihren_kanten() {
        assert_eq!(wert("7 / 2"), Some(3), "ganzzahlig abgerundet");
        assert_eq!(wert("7 % 2"), Some(1));
        assert_eq!(wert("6 % 2"), Some(0));
        assert_eq!(wert("2 * 3 + 1"), Some(7), "Punkt vor Strich");
        assert_eq!(wert("1 + 2 * 3"), Some(7), "and in the other direction");
    }
}
