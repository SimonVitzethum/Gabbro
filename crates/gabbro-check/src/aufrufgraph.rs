//! **Der Aufrufgraph — Priorität null, weil er zum dritten Mal als Blocker auftauchte.**
//!
//! R17: *ein fehlendes Werkzeug, das zum dritten Mal blockiert, wandert an die Spitze.*
//! Der Aufrufgraph stand bei drei:
//!
//! 1. **`H005`** — die Zwischenregel am Aufrufrand (*„ein geteilter Block ruft **keine**
//!    Funktion mit `requires Held(…)`. Punkt."*) war absichtlich zu streng und hat die
//!    ersetzende Prüfung in ihrer eigenen Absage angekündigt. Hier ist sie.
//! 2. **Pass 8, Aufrufwirkungen** — ohne sie deckt eine `effects`-Liste nur die **erste
//!    Ebene**, und die Klempnerei-Klasse *Rahmen* hängt genau daran (`MESSUNGEN.md`,
//!    Neuerhebung: `N_neu = 5`).
//! 3. **Die Klasse *Phase*** — nur ein Aufrufgraph trennt „selten **ist**" von „selten
//!    **sichtbar**" (R18).
//!
//! ## Was er leistet und was nicht
//!
//! **Er löst Namen auf und schliesst Mengen transitiv.** Er ist *kein* Alias-Analysator und
//! bildet **keine Wirkungen auf Argumente ab** — `writes p.slots` beim Gerufenen wird beim
//! Rufer als `writes p.slots` gesehen, mit dem Parameternamen des **Gerufenen**. Das ist die
//! grobe Fassung, und sie ist **in die sichere Richtung grob**: sie sieht mehr Wirkungen als
//! da sind, nie weniger.
//!
//! **Zyklen enden, ohne zu raten.** Ein Zyklus wird erkannt und die Menge an dieser Kante
//! abgeschnitten; die betroffene Funktion wird als `unvollstaendig` geführt. *Eine
//! Wirkungsmenge, die aus einem Zyklus stammt, ist eine untere Schranke und heisst so*
//! (R16).

use gabbro_syntax::ast::*;
use std::collections::{BTreeMap, BTreeSet};

/// Was über eine Funktion im Graphen steht.
#[derive(Debug, Clone)]
pub struct Knoten {
    /// Die Wirkungen, die der Rumpf **selbst** nennt (aus der `effects`-Klausel).
    pub eigen: BTreeSet<String>,
    /// Die Pfade, die der Rumpf ruft — **wie im Quelltext geschrieben**, also `f` oder
    /// `a::f`. Aufgelöst wird erst beim Gehen, relativ zum Modul des Rufers.
    pub ruft: BTreeSet<String>,
    /// **Die Parameternamen, in Reihenfolge** — die Brücke über den Aufrufrand.
    pub parameter: Vec<String>,
    /// Je Rufkante: der aufgelöste Schlüssel und die **Ortsausdrücke der Argumente** —
    /// `None`, wo das Argument kein Ort ist. *`None` macht die Hülle an dieser Kante
    /// unvollständig, statt den Namen des Gerufenen stillschweigend zu erben.*
    pub rufe: Vec<(String, Vec<Option<String>>)>,
    /// **Das Modul, in dem die Funktion steht.** Ohne es ist `ruft` nicht auflösbar: zwei
    /// `hilf` in zwei Modulen sind zwei Funktionen, und der kurze Name nennt beide.
    pub modul: String,
    /// `requires Held(X)` — welche Sperren verlangt die Funktion, und geteilt oder exklusiv?
    pub verlangt: Vec<(String, bool)>,
    /// Hat sie überhaupt eine `effects`-Klausel? Ohne sie ist nichts ableitbar.
    pub hat_effects: bool,
    pub span: gabbro_syntax::span::Span,
}

#[derive(Debug, Default)]
pub struct Graph {
    pub knoten: BTreeMap<String, Knoten>,
}

/// Das Ergebnis einer transitiven Hülle.
#[derive(Debug, Clone)]
pub struct Huelle {
    pub wirkungen: BTreeSet<String>,
    /// **Untere Schranke statt Zahl** (R16): ein Zyklus oder ein unbekannter Gerufener.
    pub unvollstaendig: Option<String>,
}

use crate::umgebung::qualifiziere as schluessel;

/// Baut die Umgebung selbst. Wer schon eine hat, nimmt `erhebe_mit`.
pub fn erhebe(baum: &Programm) -> Graph {
    let u = crate::umgebung::Umgebung::sammle(baum);
    erhebe_mit(baum, &u)
}

/// **Modulbewusst seit 2026-08-19.** Bis dahin war der Schlüssel der KURZE Name, und zwei
/// gleichnamige Funktionen in zwei Modulen überschrieben einander -- die zweite gewann, und
/// welche das war, entschied die Reihenfolge im Quelltext. Gemessen: dieselbe Datei, nur die
/// Modulreihenfolge getauscht, ergab einmal **0 Fehler** für ein `pure`, das etwas
/// Schreibendes ruft, und einmal drei Fehler, davon einer an der **falschen** Funktion.
///
/// `lib.rs::fuer_jedes_item_im_modul` beschreibt genau diesen Fehler seit dem 2026-08-14 --
/// M1 wurde damals nachgezogen, die sechs anderen Pässe nicht.
pub fn erhebe_mit(baum: &Programm, u: &crate::umgebung::Umgebung) -> Graph {
    let mut g = Graph::default();
    // **Uebergaenge sind Gerufene mit erklaerten Wirkungen.** Ohne sie meldete der Graph
    // `uebersetzung_an ist unbekannt` und die Aufrufwirkungen von `scharfschalten` galten
    // als unentscheidbar -- eine Luecke im GRAPHEN, nicht im Programm. Gefunden am eigenen
    // Beispiel 02, eine Minute nachdem der dritte Zustand sichtbar wurde.
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        if let ItemArt::Device(d) = &item.art {
            for ue in &d.uebergaenge {
                let mut k = Knoten {
                    eigen: BTreeSet::new(),
                    ruft: BTreeSet::new(),
                    verlangt: Vec::new(),
                    hat_effects: ue.effects.is_some(),
                    parameter: Vec::new(),
                    rufe: Vec::new(),
                    modul: modul.to_string(),
                    span: ue.name.span,
                };
                if let Some(w) = &ue.effects {
                    for e in &w.liste {
                        k.eigen.insert(e.art.text());
                    }
                }
                g.knoten.insert(schluessel(modul, &ue.name.text), k);
            }
        }
    });
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let ItemArt::Funktion(f) = &item.art else {
            return;
        };
        let mut k = Knoten {
            eigen: BTreeSet::new(),
            ruft: BTreeSet::new(),
            verlangt: Vec::new(),
            hat_effects: f.effects.is_some(),
            parameter: f.parameter.iter().map(|p| p.name.text.clone()).collect(),
            rufe: Vec::new(),
            modul: modul.to_string(),
            span: f.name.span,
        };
        if let Some(w) = &f.effects {
            for e in &w.liste {
                k.eigen.insert(e.art.text());
            }
        }
        for p in &f.requires {
            held_aus_pred(p, &mut k.verlangt);
        }
        if let FnRumpf::Block(b) = &f.rumpf {
            sammle_rufe(b, &mut k.ruft);
            sammle_kanten(b, &mut k.rufe);
        }
        g.knoten.insert(schluessel(modul, &f.name.text), k);
    });
    // **Dritte Phase: die Kanten aufloesen.** Erst jetzt stehen alle Schluessel fest. Ein
    // Pfad wird relativ zum Modul des RUFERS gesucht, mit derselben Ordnung, die M1 seit
    // dem 2026-08-14 benutzt (eigenes Modul, umgebende, Wurzel, `use`-Zeile). Was sich nicht
    // aufloesen laesst, bleibt stehen wie geschrieben -- und macht die Huelle unvollstaendig,
    // statt still auf einen fremden Namen zu treffen.
    let schluessel_alle: BTreeSet<String> = g.knoten.keys().cloned().collect();
    for k in g.knoten.values_mut() {
        let modul = k.modul.clone();
        let aufloesen = |pfad: &str| {
            u.kandidaten_oeffentlich(&modul, pfad)
                .into_iter()
                .find(|kand| schluessel_alle.contains(kand))
                .unwrap_or_else(|| pfad.to_string())
        };
        k.ruft = k.ruft.iter().map(|p| aufloesen(p)).collect();
        k.rufe = k
            .rufe
            .iter()
            .map(|(p, args)| (aufloesen(p), args.clone()))
            .collect();
    }
    g
}

/// **Wie viele Knotenbesuche eine Hülle kosten darf, bevor der Pass sie ABSAGT.**
///
/// Mit `fertig` ist ein zyklenfreier Graph linear; in einer stark verzahnten Rekursion kann
/// derselbe Knoten aber auf mehreren Wegen neu gerechnet werden. Statt zu hoffen, dass das
/// nicht vorkommt, steht hier eine Zahl — und wird sie überschritten, heisst die Hülle
/// *unvollständig* **mit Grund** (R16). Der Korpus braucht weniger als hundert Schritte.
const SCHRITTE_MAX: usize = 100_000;

/// Der Zustand EINER Hüllenberechnung. Zwei Mengen, zwei verschiedene Fragen — siehe `gehe`.
#[derive(Default)]
struct Lauf {
    /// Wer liegt gerade unter mir? **Nur das ist ein Zyklus.**
    pfad: BTreeSet<String>,
    /// Wer ist zyklusfrei fertig gerechnet? Nur damit bleibt ein Diamant linear.
    fertig: BTreeMap<String, (BTreeSet<String>, Option<String>)>,
    schritte: usize,
}

impl Graph {
    /// **Die transitive Wirkungsmenge.** Eigene Wirkungen plus die aller Gerufenen.
    ///
    /// Der Weg endet an vier Stellen, und jede wird **benannt** statt geraten: an einem
    /// Zyklus, an einem Gerufenen ohne `effects`, an einem Namen, den der Graph nicht kennt
    /// (extern über Modulgrenzen hinweg, Konstruktoren, `Some`/`None`), und an einem Graphen,
    /// der größer ist als `SCHRITTE_MAX`.
    pub fn huelle(&self, start: &str) -> Huelle {
        let mut lauf = Lauf::default();
        let (menge, offen, _) = self.gehe(start, &mut lauf);
        Huelle {
            wirkungen: menge,
            unvollstaendig: offen,
        }
    }

    /// **Der Weg — mit einem PFAD, nicht mit einer Besuchsliste.**
    ///
    /// Bis zum 2026-08-19 stand hier *eine* Menge `gesehen`, die beim Rückweg nie geleert
    /// wurde und trotzdem als Zyklusmerkmal diente. Jeder ZWEITE Besuch desselben Knotens
    /// hiess damit „cycle over X", ganz gleich, ob er auf demselben Weg lag. Ein gewöhnlicher
    /// Diamant reicht:
    ///
    /// ```text
    /// f -> g -> k
    /// f -> h -> k      meldete «cycle over `m::k`»
    /// ```
    ///
    /// Die Folge war **kein falscher Alarm, sondern Schweigen**: eine Hülle mit `cycle` ist
    /// nur eine UNTERE Schranke, `E008` (*„promises `pure` but …"*) darf daraus nichts
    /// schliessen — und ein falsches `pure` kam durch. *Genau der Pass, dessen Modulkopf mit
    /// „effects ist NICHT fail-open" anfängt.* Dieselbe Klasse wie die 83 `_ => {}`-Zweige,
    /// nur diesmal in einer Tiefensuche, die eine Besuchsmenge für eine Stapelmenge hielt.
    ///
    /// Getrennt sind es zwei Mengen mit zwei Aufgaben:
    ///
    /// * **`pfad`** — wer gerade UNTER mir liegt. Nur das ist ein Zyklus.
    /// * **`fertig`** — wer schon fertig gerechnet ist. Nur damit bleibt der Diamant linear;
    ///   ein reiner Pfadschnitt allein wäre exponentiell, und diese Falle stand in derselben
    ///   Woche schon einmal (`m1::sammle_schreibziele`, 2ⁿ).
    ///
    /// Gemerkt wird **nur, was zyklusfrei zustande kam**: ein Ergebnis, das an einem
    /// Pfadschnitt hängt, gilt für diesen Weg und für keinen anderen.
    fn gehe(&self, name: &str, lauf: &mut Lauf) -> (BTreeSet<String>, Option<String>, bool) {
        if let Some((m, o)) = lauf.fertig.get(name) {
            return (m.clone(), o.clone(), false);
        }
        if lauf.pfad.contains(name) {
            // Ein Zyklus. Die Menge ist ab hier eine untere Schranke -- und sagt das.
            return (BTreeSet::new(), Some(format!("cycle over `{name}`")), true);
        }
        lauf.schritte += 1;
        if lauf.schritte > SCHRITTE_MAX {
            let o = format!(
                "the call graph around `{name}` needs more than {SCHRITTE_MAX} steps to expand"
            );
            return (BTreeSet::new(), Some(o), true);
        }
        let Some(k) = self.knoten.get(name) else {
            let o = Some(format!("`{name}` is unknown to the graph"));
            // Haengt nicht vom Weg ab: merkbar.
            lauf.fertig
                .insert(name.to_string(), (BTreeSet::new(), o.clone()));
            return (BTreeSet::new(), o, false);
        };
        lauf.pfad.insert(name.to_string());
        let mut menge: BTreeSet<String> = k.eigen.iter().cloned().collect();
        let mut offen = if k.hat_effects {
            None
        } else {
            Some(format!("`{name}` declares no `effects`"))
        };
        let mut zyklisch = false;
        let aufnehmen = |offen: &mut Option<String>, grund: Option<String>| {
            if offen.is_none() {
                *offen = grund;
            }
        };
        for (ziel, args) in &k.rufe {
            let (tiefer, grund, z) = self.gehe(ziel, lauf);
            zyklisch |= z;
            aufnehmen(&mut offen, grund);
            // **Die Bruecke ueber den Aufrufrand** (2026-08-19). Bis dahin sah der Rufer
            // `consumes p` mit dem PARAMETERNAMEN des Gerufenen und musste ihn woertlich in
            // seiner eigenen Liste fuehren, obwohl `p` bei ihm gar nicht existiert. Gemessen
            // an sauberem Code: `let y = erzeuge(); ende(y);` gab **`E008`: calls something
            // with `consumes p` but names no `consumes`**.
            //
            // *Ersetzt wird nur der GRUNDname:* `writes p.slots` beim Gerufenen wird
            // `writes q.slots` beim Rufer, wenn `q` das Argument war. Bleibt kein Argument
            // uebrig, bleibt der Name stehen -- **grob, und in die sichere Richtung grob.**
            let leer: Vec<String> = Vec::new();
            let ziel_par = self.knoten.get(ziel).map(|z| &z.parameter).unwrap_or(&leer);
            for w in tiefer {
                let (neu, unklar) = ersetze(&w, ziel_par, args);
                if unklar {
                    aufnehmen(
                        &mut offen,
                        Some(format!(
                            "an argument of the call to `{ziel}` is not a place, so `{w}` \
                             cannot be carried across"
                        )),
                    );
                }
                menge.insert(neu);
            }
        }
        // Kanten ohne Argumentwissen (`transition`-Uebergaenge) laufen weiter wie bisher.
        for g in k.ruft.iter().filter(|g| !k.rufe.iter().any(|(z, _)| &z == g)) {
            let (tiefer, grund, z) = self.gehe(g, lauf);
            zyklisch |= z;
            aufnehmen(&mut offen, grund);
            menge.extend(tiefer);
        }
        lauf.pfad.remove(name);
        if !zyklisch {
            lauf.fertig
                .insert(name.to_string(), (menge.clone(), offen.clone()));
        }
        (menge, offen, zyklisch)
    }

    /// **Steht diese Funktion in einem Rekursionszyklus?** Erreicht sie sich selbst?
    ///
    /// Die Frage, die «K5.4» stellt: bei einem Zyklus zählt der Kostenpass jede Kante einmal,
    /// und `costs` ist dort eine **Annahme**. Erst ein `decreases` macht daraus eine Aussage.
    pub fn im_zyklus(&self, start: &str) -> bool {
        let mut gesehen = BTreeSet::new();
        let mut offen: Vec<&str> = match self.knoten.get(start) {
            Some(k) => k.ruft.iter().map(String::as_str).collect(),
            None => return false,
        };
        while let Some(n) = offen.pop() {
            if n == start {
                return true;
            }
            if !gesehen.insert(n.to_string()) {
                continue;
            }
            if let Some(k) = self.knoten.get(n) {
                offen.extend(k.ruft.iter().map(String::as_str));
            }
        }
        false
    }

    /// Der qualifizierte Schlüssel einer Funktion — die Form, die `huelle` und `verlangt`
    /// erwarten. **Ein kurzer Name reicht dort nicht mehr** (2026-08-19).
    pub fn schluessel_von(&self, modul: &str, name: &str) -> String {
        schluessel(modul, name)
    }

    /// Löst einen Rufpfad auf, wie ihn der Rumpf schreibt, relativ zum rufenden Modul.
    pub fn aufloesen(&self, u: &crate::umgebung::Umgebung, von: &str, pfad: &str) -> Option<String> {
        u.kandidaten_oeffentlich(von, pfad)
            .into_iter()
            .find(|k| self.knoten.contains_key(k))
    }

    /// **Die Hülle OHNE die eigenen Wirkungen** — was allein aus den Gerufenen kommt.
    ///
    /// `huelle` schliesst die eigene `effects`-Liste ein, und für die Frage *„löst ein
    /// Gerufener diese Zusage ein?"* ist das genau die falsche Menge: die Zeile belegte
    /// sich selbst.
    pub fn huelle_der_gerufenen(&self, start: &str) -> Huelle {
        let Some(k) = self.knoten.get(start) else {
            return Huelle {
                wirkungen: BTreeSet::new(),
                unvollstaendig: Some(format!("`{start}` is unknown to the graph")),
            };
        };
        let mut lauf = Lauf::default();
        lauf.pfad.insert(start.to_string());
        let mut menge = BTreeSet::new();
        let mut offen = None;
        for g in &k.ruft {
            let (tiefer, grund, _) = self.gehe(g, &mut lauf);
            menge.extend(tiefer);
            if offen.is_none() {
                offen = grund;
            }
        }
        Huelle {
            wirkungen: menge,
            unvollstaendig: offen,
        }
    }

    /// Welche Sperren verlangt der Gerufene — und **geteilt oder exklusiv?**
    ///
    /// Das ist die Frage, die `H005` durch eine echte Pruefung ersetzt: ein geteilter Block
    /// darf `requires Held-shared` rufen, eine exklusive Forderung bleibt gesperrt.
    pub fn verlangt(&self, name: &str) -> &[(String, bool)] {
        self.knoten.get(name).map_or(&[], |k| &k.verlangt)
    }
}

/// **Einen Wirkungsnamen über den Aufrufrand tragen** («K5.5»).
///
/// `writes p.slots` mit `p` als erstem Parameter und `a.b` als erstem Argument wird
/// `writes a.b.slots` — **der ganze Ortsausdruck**, nicht nur seine Basis.
///
/// Das zweite Feld sagt, ob die Übersetzung **unklar** war: der Name gehört einem Parameter
/// des Gerufenen, und das Argument an dieser Stelle ist kein Ort (`f(g(x))`, ein Literal).
/// *Dann erbt der Rufer einen Namen, den es bei ihm nicht gibt* — und statt ihn
/// stillschweigend stehen zu lassen, macht das die Hülle unvollständig (`E009`).
fn ersetze(wirkung: &str, parameter: &[String], argumente: &[Option<String>]) -> (String, bool) {
    // `locks shared X` ist zweiwortig; der Ort ist immer das LETZTE Wort.
    let Some((kopf, ort)) = wirkung.rsplit_once(' ') else {
        return (wirkung.to_string(), false);
    };
    let (grund, rest) = match ort.find(['.', '[']) {
        Some(i) => (&ort[..i], &ort[i..]),
        None => (ort, ""),
    };
    match parameter.iter().position(|p| p == grund) {
        Some(i) if i < argumente.len() => match &argumente[i] {
            Some(a) => (format!("{kopf} {a}{rest}"), false),
            None => (wirkung.to_string(), true),
        },
        // Kein Parametername -- eine globale Stelle, sie heisst ueberall gleich.
        _ => (wirkung.to_string(), false),
    }
}

/// Je Rufstelle: der geschriebene Pfad und die Ortsausdrücke seiner Argumente.
pub fn kanten_von(b: &Block, aus: &mut Vec<(String, Vec<Option<String>>)>) {
    sammle_kanten(b, aus)
}

fn sammle_kanten(b: &Block, aus: &mut Vec<(String, Vec<Option<String>>)>) {
    fn nimm_ruf(r: &Ruf, aus: &mut Vec<(String, Vec<Option<String>>)>) {
        if let Some(n) = r.pfad.teile.last() {
            if n.text != "Some" && n.text != "None" && !r.ist_verbundwert() {
                let args = r
                    .argumente
                    .iter()
                    .map(|a| match &a.art {
                        // **Der ganze Ortsausdruck** («K5.5»), nicht nur seine Basis:
                        // `f(a.b)` traegt `a.b`, und `writes p.slots` wird `writes a.b.slots`.
                        ExprArt::Ort(o) => Some(o.text()),
                        _ => None,
                    })
                    .collect();
                aus.push((r.pfad.text(), args));
            }
        }
        for a in &r.argumente {
            if let ExprArt::Ruf(x) = &a.art {
                nimm_ruf(x, aus);
            }
        }
    }
    fn aus_expr(e: &Expr, aus: &mut Vec<(String, Vec<Option<String>>)>) {
        match &e.art {
            ExprArt::Ruf(r) => nimm_ruf(r, aus),
            ExprArt::Klammer(x) | ExprArt::Unaer(_, x) => aus_expr(x, aus),
            ExprArt::Binaer(_, a, b) => {
                aus_expr(a, aus);
                aus_expr(b, aus);
            }
            _ => {}
        }
    }
    for s in &b.anweisungen {
        for e in crate::eigene_ausdruecke(s) {
            aus_expr(e, aus);
        }
        match &s.art {
            StmtArt::Ruf(r) => nimm_ruf(r, aus),
            StmtArt::LetSonst(l) => {
                if let Some(r) = l.als_ruf() {
                    nimm_ruf(r, aus);
                }
            }
            _ => {}
        }
        for k in crate::unterbloecke(s) {
            sammle_kanten(k, aus);
        }
    }
}

/// `requires Held(X)` bzw. `Held(X, shared)` -- flach über den Prädikatbaum.
pub fn held_aus_pred(p: &Pred, aus: &mut Vec<(String, bool)>) {
    match &p.art {
        PredArt::Held { sperre, geteilt, .. } => aus.push((sperre.text.clone(), *geteilt)),
        PredArt::Vergleich(e) | PredArt::Element(e, _) => held_aus_expr(e, aus),
        PredArt::Klammer(x) | PredArt::Nicht(x) => held_aus_pred(x, aus),
        PredArt::Und(a, b) | PredArt::Oder(a, b) => {
            held_aus_pred(a, aus);
            held_aus_pred(b, aus);
        }
        _ => {}
    }
}

fn held_aus_expr(e: &Expr, aus: &mut Vec<(String, bool)>) {
    match &e.art {
        ExprArt::Ruf(r) if r.pfad.teile.last().is_some_and(|i| i.text == "Held") => {
            let name = match r.argumente.first().map(|a| &a.art) {
                Some(ExprArt::Ort(o)) => o.text(),
                _ => "…".to_string(),
            };
            // Ein zweites Argument `shared` macht die Forderung geteilt.
            let geteilt = r.argumente.len() > 1
                && matches!(&r.argumente[1].art, ExprArt::Ort(o) if o.text() == "shared");
            aus.push((name, geteilt));
        }
        ExprArt::Klammer(x) | ExprArt::Unaer(_, x) => held_aus_expr(x, aus),
        ExprArt::Binaer(_, a, b) => {
            held_aus_expr(a, aus);
            held_aus_expr(b, aus);
        }
        _ => {}
    }
}

/// **Der Abstieg geht über `crate::unterbloecke`** — erschöpfend über `StmtArt`.
///
/// Bis 2026-08-19 zählte dieser Weg seine Arme selbst auf und schloss mit `_ => {}`.
/// `observes` fehlte, und damit war **jeder Ruf in einem RCU-Leseblock für den Rahmenpass
/// unsichtbar**: gemessen verschwanden zwei `E008` (`masks IRQ`, `writes G`), sobald man
/// denselben Ruf eine Zeile tiefer schrieb.
fn sammle_rufe(b: &Block, aus: &mut BTreeSet<String>) {
    for s in &b.anweisungen {
        // Was die Anweisung selbst auswertet.
        for e in crate::eigene_ausdruecke(s) {
            aus_expr(e, aus);
        }
        // Die zwei Rufe, die in keinem `Expr` stehen.
        match &s.art {
            StmtArt::Ruf(r) => nimm(r, aus),
            // «B14b»: eine Quelle, die ein `place` ist, ruft nichts.
            StmtArt::LetSonst(l) => {
                if let Some(r) = l.als_ruf() {
                    nimm(r, aus);
                }
            }
            _ => {}
        }
        for k in crate::unterbloecke(s) {
            sammle_rufe(k, aus);
        }
    }
}

fn nimm(r: &Ruf, aus: &mut BTreeSet<String>) {
    // **Ein Konstruktor ruft nichts.** Dieselbe Aussage wie bei «B14b» und dieselbe wie
    // bei `Some`/`None` -- und sie ist hier die wichtigste von allen: eine Kante auf einen
    // Namen, hinter dem keine Funktion steht, macht den Gerufenen UNBEKANNT, und ueber
    // einem unbekannten Gerufenen ist jede Huelle nur noch eine untere Schranke (`E009`).
    //
    // > *Der Pass haette dann nicht falsch gerechnet, sondern aufgehoert zu rechnen -- und
    // > das Aufhoeren steht als Hinweis da, nicht als Fehler.*
    //
    // Der Unterscheider ist SYNTAKTISCH (`ist_verbundwert`, die Marken) und bleibt es: er
    // trennt Konstruktor von Aufruf, bevor irgendein Name aufgeloest wird. Die AUFLOESUNG
    // dagegen braucht die Umgebung und hat sie seit 2026-08-19 -- vorher gewann der zuletzt
    // eingetragene gleichnamige Knoten, still.
    if let Some(n) = r.pfad.teile.last() {
        // `Some`/`None` sind Konstruktoren, keine Aufrufe (s. «B35»).
        if n.text != "Some" && n.text != "None" && !r.ist_verbundwert() {
            // **Der ganze Pfad, nicht nur sein letztes Stueck.** `a::hilf()` und `b::hilf()`
            // waren bis 2026-08-19 derselbe Name; aufgeloest wird spaeter, in `erhebe_mit`.
            aus.insert(r.pfad.text());
        }
    }
    for a in &r.argumente {
        aus_expr(a, aus);
    }
}

fn aus_expr(e: &Expr, aus: &mut BTreeSet<String>) {
    match &e.art {
        ExprArt::Ruf(r) => nimm(r, aus),
        ExprArt::Klammer(x) | ExprArt::Unaer(_, x) => aus_expr(x, aus),
        ExprArt::Binaer(_, a, b) => {
            aus_expr(a, aus);
            aus_expr(b, aus);
        }
        _ => {}
    }
}
