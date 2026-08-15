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
    /// Die Namen, die der Rumpf ruft — kurz, wie im Quelltext.
    pub ruft: BTreeSet<String>,
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

pub fn erhebe(baum: &Programm) -> Graph {
    let mut g = Graph::default();
    crate::fuer_jedes_item(baum, &mut |item| {
        let ItemArt::Funktion(f) = &item.art else {
            return;
        };
        let mut k = Knoten {
            eigen: BTreeSet::new(),
            ruft: BTreeSet::new(),
            verlangt: Vec::new(),
            hat_effects: f.effects.is_some(),
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
        g.knoten.insert(f.name.text.clone(), k);
    });
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
                *offen = Some(format!("Zyklus ueber `{name}`"));
            }
            return;
        }
        let Some(k) = self.knoten.get(name) else {
            if offen.is_none() {
                *offen = Some(format!("`{name}` ist dem Graphen unbekannt"));
            }
            return;
        };
        if !k.hat_effects {
            if offen.is_none() {
                *offen = Some(format!("`{name}` nennt keine `effects`"));
            }
        }
        menge.extend(k.eigen.iter().cloned());
        for g in &k.ruft {
            self.gehe(g, gesehen, menge, offen);
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

/// `requires Held(X)` bzw. `Held(X, shared)` -- flach über den Prädikatbaum.
fn held_aus_pred(p: &Pred, aus: &mut Vec<(String, bool)>) {
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

fn sammle_rufe(b: &Block, aus: &mut BTreeSet<String>) {
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Ruf(r) => nimm(r, aus),
            StmtArt::Let(l) => aus_expr(&l.wert, aus),
            StmtArt::LetSonst(l) => {
                nimm(&l.ruf, aus);
                sammle_rufe(&l.sonst, aus);
            }
            StmtArt::Zuweisung(z) => aus_expr(&z.wert, aus),
            StmtArt::Return(Some(e)) => aus_expr(e, aus),
            StmtArt::Publish(p) => aus_expr(&p.wert, aus),
            StmtArt::Wenn(w) => {
                for (b1, r) in &w.zweige {
                    aus_expr(b1, aus);
                    sammle_rufe(r, aus);
                }
                if let Some(r) = &w.sonst {
                    sammle_rufe(r, aus);
                }
            }
            StmtArt::Match(m) => {
                for z in &m.zweige {
                    sammle_rufe(&z.rumpf, aus);
                }
            }
            StmtArt::Sperrt(x) => sammle_rufe(&x.rumpf, aus),
            StmtArt::Bricht(x) => sammle_rufe(&x.rumpf, aus),
            StmtArt::Narrow(x) => sammle_rufe(&x.sonst, aus),
            StmtArt::Exchange(e) => {
                if let XForm::Update { rumpf, .. } = &e.form {
                    sammle_rufe(rumpf, aus);
                }
            }
            StmtArt::Schleife(sch) => match sch.as_ref() {
                Schleife::Traverse(x) => sammle_rufe(&x.rumpf, aus),
                Schleife::Retry(x) => sammle_rufe(&x.rumpf, aus),
                Schleife::Forever(x) => sammle_rufe(&x.rumpf, aus),
            },
            _ => {}
        }
    }
}

fn nimm(r: &Ruf, aus: &mut BTreeSet<String>) {
    if let Some(n) = r.pfad.teile.last() {
        // `Some`/`None` sind Konstruktoren, keine Aufrufe (s. «B35»).
        if n.text != "Some" && n.text != "None" {
            aus.insert(n.text.clone());
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
