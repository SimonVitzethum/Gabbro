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
        k.ruft = k
            .ruft
            .iter()
            .map(|pfad| {
                u.kandidaten_oeffentlich(&k.modul, pfad)
                    .into_iter()
                    .find(|kand| schluessel_alle.contains(kand))
                    .unwrap_or_else(|| pfad.clone())
            })
            .collect();
    }
    g
}

impl Graph {
    /// **Die transitive Wirkungsmenge.** Eigene Wirkungen plus die aller Gerufenen.
    ///
    /// Der Weg endet an drei Stellen, und jede wird **benannt** statt geraten: an einem
    /// Zyklus, an einem Gerufenen ohne `effects`, und an einem Namen, den der Graph nicht
    /// kennt (extern über Modulgrenzen hinweg, Konstruktoren, `Some`/`None`).
    pub fn huelle(&self, start: &str) -> Huelle {
        let mut gesehen = BTreeSet::new();
        let mut menge = BTreeSet::new();
        let mut offen = None;
        self.gehe(start, &mut gesehen, &mut menge, &mut offen);
        Huelle {
            wirkungen: menge,
            unvollstaendig: offen,
        }
    }

    fn gehe(
        &self,
        name: &str,
        gesehen: &mut BTreeSet<String>,
        menge: &mut BTreeSet<String>,
        offen: &mut Option<String>,
    ) {
        if !gesehen.insert(name.to_string()) {
            // Zyklus. Die Menge ist ab hier eine untere Schranke -- und sagt das.
            if offen.is_none() {
                *offen = Some(format!("cycle over `{name}`"));
            }
            return;
        }
        let Some(k) = self.knoten.get(name) else {
            if offen.is_none() {
                *offen = Some(format!("`{name}` is unknown to the graph"));
            }
            return;
        };
        if !k.hat_effects {
            if offen.is_none() {
                *offen = Some(format!("`{name}` declares no `effects`"));
            }
        }
        menge.extend(k.eigen.iter().cloned());
        for g in &k.ruft {
            self.gehe(g, gesehen, menge, offen);
        }
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

    /// Welche Sperren verlangt der Gerufene — und **geteilt oder exklusiv?**
    ///
    /// Das ist die Frage, die `H005` durch eine echte Pruefung ersetzt: ein geteilter Block
    /// darf `requires Held-shared` rufen, eine exklusive Forderung bleibt gesperrt.
    pub fn verlangt(&self, name: &str) -> &[(String, bool)] {
        self.knoten.get(name).map_or(&[], |k| &k.verlangt)
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
