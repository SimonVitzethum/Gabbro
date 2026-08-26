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
    /// **The calls that go through a PLACE** («B8», 2026-08-21) — the callee is not
    /// statically known, and therefore does not appear in `ruft`.
    ///
    /// *Without this field there would be exactly the outcome this whole item stands
    /// against:* the call would vanish from the graph, the hull would still look complete,
    /// and `E008` would not see the callee's effects — **without a word being said anywhere.**
    pub indirect: Vec<IndirectCall>,
    /// **Das Modul, in dem die Funktion steht.** Ohne es ist `ruft` nicht auflösbar: zwei
    /// `hilf` in zwei Modulen sind zwei Funktionen, und der kurze Name nennt beide.
    pub modul: String,
    /// `requires Held(X)` — welche Sperren verlangt die Funktion, und geteilt oder exklusiv?
    pub verlangt: Vec<(String, bool)>,
    /// Hat sie überhaupt eine `effects`-Klausel? Ohne sie ist nichts ableitbar.
    pub hat_effects: bool,
    pub span: gabbro_syntax::span::Span,
}

/// **A call whose callee stands at a place.**
///
/// What saves the graph here is the **contract at the pointer type**: it says what the callee
/// may do without saying who it is. `effects` comes from the `effects` clause of the `fn(…)`
/// type; the parameter names beside it are the TYPE's, and `arguments` are the place
/// expressions at the call site — so `ersetze` carries the effect across the call boundary
/// **exactly as it does for a statically known callee.**
///
/// `has_contract == false` means: the type of the place is not a function pointer with
/// `effects`. The hull is then a **lower bound from here on, and says so** (R16) — the caller
/// gets `E009`, not silence.
#[derive(Debug, Clone)]
pub struct IndirectCall {
    /// The place as it stood in the source: `t->senden`, `TAB.bereit`.
    pub place: String,
    /// The effects from the pointer type's contract.
    pub effects: BTreeSet<String>,
    /// The parameter names **of the pointer type** — the bridge across the call boundary.
    ///
    /// **`None` where the pointer type named no parameter** (`fn(u8)`, the ordinary form
    /// since 2026-08-25). Such a slot can never be the target of a substitution, because no
    /// effect line can name it -- but it **keeps its position**, and that is the whole
    /// reason it is a `None` and not a gap in the list: `ersetze` indexes `arguments` by the
    /// parameter's position. *Dropping the unnamed ones would shift every later argument by
    /// one and translate `writes b.slots` into the wrong place.*
    pub parameters: Vec<Option<String>>,
    /// The place expressions of the arguments at the call site.
    pub arguments: Vec<Option<String>>,
    /// Does the type of the place carry an `effects` clause?
    pub has_contract: bool,
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
                    indirect: Vec::new(),
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
            // **Und das GERAET selbst ist ein Knoten -- weil `Vtd(basis)` kein Ruf ist**
            // (2026-08-20).
            //
            // *„Die Parameterliste der Deklaration IST der Konstruktor"* (`beispiele/09`):
            // aus einer `Pa` wird ein Griff, und dabei passiert nichts. Der Graph hielt es
            // fuer einen unbekannten Gerufenen und erklaerte daraufhin die Wirkungen JEDER
            // Funktion, die einen Griff bildet, fuer unentscheidbar -- `E009` an
            // `beispiele/09` und an `/39`.
            //
            // > **Dieselbe Luecke wie bei den Uebergaengen zwei Kommentare weiter oben, und
            // > derselbe Ort.** Sie stand darueber und ist beim Bauen uebersehen worden;
            // > gefunden hat sie `gabbro blindstellen`, als eine neue Datei einen Griff
            // > zurueckgab.
            let mut k = Knoten {
                eigen: BTreeSet::new(),
                ruft: BTreeSet::new(),
                verlangt: Vec::new(),
                hat_effects: true,
                parameter: Vec::new(),
                rufe: Vec::new(),
                indirect: Vec::new(),
                modul: modul.to_string(),
                span: d.name.span,
            };
            k.eigen.insert("pure".to_string());
            g.knoten.insert(schluessel(modul, &d.name.text), k);
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
            indirect: Vec::new(),
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
        // **Ein VERTRAG ruft auch** (2026-08-20). Bis heute wurden `requires`/`ensures`
        // nur nach `Held(…)` durchsucht; ein Ruf darin sah niemand.
        //
        // ```gabbro
        // impl fn f(t : ptr<normal, rw> T)
        //     requires forall s in slots of t : schreibt(t.slots[s].x)
        //     effects  { pure }                                    -- 0 Fehler
        // ```
        //
        // *Gefunden von einer Mutation, die UEBERLEBT hat* -- `PredArt::Quantor(_) => {}`
        // fiel durch keine Probe, und die Suche nach einer Probe fand statt ihrer das Loch.
        //
        // > Ein Vertrag, der etwas Wirkendes ruft, ist in beide Richtungen falsch: entweder
        // > luegt die Wirkungsliste, oder die Vorbedingung hat eine Wirkung. `E008` sagt
        // > beides.
        for p in f.requires.iter().chain(&f.ensures) {
            for e in crate::ausdruecke_im_praedikat(p) {
                for x in crate::alle_ausdruecke(e) {
                    if let ExprArt::Ruf(r) = &x.art {
                        nimm(r, &mut k.ruft);
                        // **A contract may not call through a place** (2026-08-21). The
                        // resolver here says "no contract" for every place, so an indirect
                        // call inside a `requires`/`ensures` makes the hull a lower bound and
                        // the caller gets `E009`. *A predicate is checked, not executed; a
                        // callee that is only known at run time cannot be part of one.*
                        nimm_ruf(r, &mut k.rufe, &mut k.indirect, &|_| None);
                    }
                }
            }
        }
        if let FnRumpf::Block(b) = &f.rumpf {
            sammle_rufe(b, &mut k.ruft);
            // **The local type picture an indirect call needs** (2026-08-21). A call through
            // a place can only be read if the type of that place is known -- the parameters
            // cover `t->senden`, the globals cover `TAB.bereit`, and the annotated `let`
            // bindings cover `let t : Treiber = …`.
            //
            // *The `let` scan is FLAT and knows nothing of shadowing.* Two bindings of one
            // name in two branches collapse into one entry here. That is coarse, and it is
            // coarse in the safe direction only as long as both are function pointers; where
            // they are not, `M1` is the pass that says so, not this one.
            let mut lokal: std::collections::HashMap<String, crate::typen::Typ> = f
                .parameter
                .iter()
                .map(|p| {
                    (
                        p.name.text.clone(),
                        u.typ_von_ausdruck_decl(modul, &p.typ),
                    )
                })
                .collect();
            sammle_lets(b, u, modul, &mut lokal);
            let vertrag = |o: &Ort| match u.typ_von_ort(modul, o, &lokal) {
                crate::typen::Typ::FnPtr(v) => Some(*v),
                _ => None,
            };
            sammle_kanten(b, &mut k.rufe, &mut k.indirect, &vertrag);
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
            u.kandidaten_aufloesbar(&modul, pfad)
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
            // A DECLARATION always names its parameters, so every entry is `Some`; the
            // `None` case exists only for a pointer type (`fn(u8)`). One allocation per call
            // edge, and the alternative was two readers for one substitution rule.
            let ziel_par: Vec<Option<String>> = self
                .knoten
                .get(ziel)
                .map(|z| z.parameter.iter().cloned().map(Some).collect())
                .unwrap_or_default();
            for w in tiefer {
                let (neu, unklar) = ersetze(&w, &ziel_par, args);
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
        // **The indirect calls -- the callee is not known, the contract is** (2026-08-21).
        //
        // There is nothing to descend into: a place carries no key. The effects come from
        // the pointer type's `effects` clause and are carried across the call boundary by
        // the same `ersetze` that serves a named callee -- the parameter names are the
        // TYPE's, the arguments are the call site's.
        //
        // **The other branch is the whole point of the item.** Without a contract the hull
        // does not quietly stay as it is; it becomes a lower bound WITH A REASON, and every
        // consumer of `unvollstaendig` (`E008`, `E009`, `H012`, the cost pass) sees it. *That
        // is the difference between a pass that stops computing and one that stops speaking.*
        for i in &k.indirect {
            if !i.has_contract {
                aufnehmen(
                    &mut offen,
                    Some(format!(
                        "the callee at `{}` is not statically known, and its type declares \
                         no `effects`",
                        i.place
                    )),
                );
                continue;
            }
            for w in &i.effects {
                let (neu, unklar) = ersetze(w, &i.parameters, &i.arguments);
                if unklar {
                    aufnehmen(
                        &mut offen,
                        Some(format!(
                            "an argument of the indirect call at `{}` is not a place, so \
                             `{w}` cannot be carried across",
                            i.place
                        )),
                    );
                }
                menge.insert(neu);
            }
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
        u.kandidaten_aufloesbar(von, pfad)
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
        // **The indirect calls belong to "what comes from the callees" too** (2026-08-21).
        // This is the set A4 uses to compute a caller's effect line instead of demanding it.
        // *Leaving the indirect calls out here would compute a line that is too short -- and
        // a short line is the one direction `effects` must never move.*
        for i in &k.indirect {
            if !i.has_contract {
                if offen.is_none() {
                    offen = Some(format!(
                        "the callee at `{}` is not statically known, and its type declares \
                         no `effects`",
                        i.place
                    ));
                }
                continue;
            }
            for w in &i.effects {
                let (neu, unklar) = ersetze(w, &i.parameters, &i.arguments);
                if unklar && offen.is_none() {
                    offen = Some(format!(
                        "an argument of the indirect call at `{}` is not a place, so `{w}` \
                         cannot be carried across",
                        i.place
                    ));
                }
                menge.insert(neu);
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
fn ersetze(
    wirkung: &str,
    parameter: &[Option<String>],
    argumente: &[Option<String>],
) -> (String, bool) {
    // `locks shared X` ist zweiwortig; der Ort ist immer das LETZTE Wort.
    let Some((kopf, ort)) = wirkung.rsplit_once(' ') else {
        return (wirkung.to_string(), false);
    };
    let (grund, rest) = match ort.find(['.', '[']) {
        Some(i) => (&ort[..i], &ort[i..]),
        None => (ort, ""),
    };
    // An UNNAMED slot of a pointer type (`fn(u8)`) matches nothing -- no effect line can
    // have named it. It still occupies its position; see `IndirectCall::parameters`.
    match parameter.iter().position(|p| p.as_deref() == Some(grund)) {
        Some(i) if i < argumente.len() => match &argumente[i] {
            Some(a) => (format!("{kopf} {a}{rest}"), false),
            None => (wirkung.to_string(), true),
        },
        // Kein Parametername -- eine globale Stelle, sie heisst ueberall gleich.
        _ => (wirkung.to_string(), false),
    }
}

/// **Every annotated `let` in a body, flat.** Feeds the local type picture that an indirect
/// call needs; see the comment at its one call site for what "flat" costs.
fn sammle_lets(
    b: &Block,
    u: &crate::umgebung::Umgebung,
    modul: &str,
    aus: &mut std::collections::HashMap<String, crate::typen::Typ>,
) {
    for s in &b.anweisungen {
        if let StmtArt::Let(l) = &s.art {
            if let Some(t) = &l.typ {
                aus.insert(l.name.text.clone(), u.typ_von_ausdruck_decl(modul, t));
            }
        }
        for k in crate::unterbloecke(s) {
            sammle_lets(k, u, modul, aus);
        }
    }
}

/// **How a call site learns the contract of a callee that stands at a place.**
///
/// Given the place (`t->senden`), it answers with the `fn(…)` contract of its type, or with
/// `None` -- and `None` is not silence: it becomes `has_contract: false`, which makes the
/// hull a lower bound that names itself (`E009`).
///
/// It is a closure and not a method because the two callers hold different amounts of
/// context: `erhebe_mit` knows the enclosing function's parameters, `kanten_von` (the
/// certificate path) knows nothing and must say so.
pub type ContractAt<'a> = &'a dyn Fn(&Ort) -> Option<crate::typen::FnPtrContract>;

/// Per call site: the written path and the place expressions of its arguments.
///
/// **The indirect calls come out separately** -- they have no name to be resolved against the
/// key table, and folding them into the same list would make them look like an edge to a
/// function called `t->senden`.
pub fn kanten_von(
    b: &Block,
    aus: &mut Vec<(String, Vec<Option<String>>)>,
    indirect: &mut Vec<IndirectCall>,
    vertrag: ContractAt<'_>,
) {
    sammle_kanten(b, aus, indirect, vertrag)
}

/// **Der Ort unter beliebig vielen Klammern.**
///
/// `f(q)` und `f((q))` sind derselbe Ruf mit demselben Argument; nur der Baum ist ein anderer.
/// Bis 2026-08-19 sah die Argumentabbildung im zweiten Fall **keinen Ort** und meldete
/// *„an argument … is not a place"* — ein `E009` an einer Stelle, an der gar nichts unklar
/// ist. **Eine Klammer ist keine Rechnung.**
///
/// Weiter geht es nicht, und das ist keine Lücke: ein Argument wie `f(g(x))` oder `f(a + 1)`
/// ist ein **Wert**, kein Ort — beim Rufer gibt es nichts, worauf `writes p.slots` abgebildet
/// werden könnte. *`E009` ist dort die Antwort, nicht ein Notbehelf.*
fn ort_unter_klammern(e: &Expr) -> Option<&Ort> {
    match &e.art {
        // **Der ganze Ortsausdruck** («K5.5»), nicht nur seine Basis:
        // `f(a.b)` traegt `a.b`, und `writes p.slots` wird `writes a.b.slots`.
        ExprArt::Ort(o) => Some(o),
        ExprArt::Klammer(i) => ort_unter_klammern(i),
        _ => None,
    }
}

/// Aus `sammle_kanten` herausgehoben (2026-08-20): auch ein VERTRAG ruft, und der
/// Vertragsleser steht eine Ebene hoeher.
fn nimm_ruf(
    r: &Ruf,
    aus: &mut Vec<(String, Vec<Option<String>>)>,
    indirect: &mut Vec<IndirectCall>,
    vertrag: ContractAt<'_>,
) {
    let args: Vec<Option<String>> = r
        .argumente
        .iter()
        .map(|a| ort_unter_klammern(a).map(|o| o.text()))
        .collect();
    match &r.ziel {
        CallTarget::Path(p) => {
            if let Some(n) = p.teile.last() {
                if n.text != "Some" && n.text != "None" && !r.ist_verbundwert() {
                    aus.push((p.text(), args));
                }
            }
        }
        // **The indirect call, and the one branch this whole item exists for.**
        //
        // The callee has no key in the graph, so there is nothing to walk to. What there is,
        // is the contract at the type of the place -- and `has_contract` decides which of the
        // two honest answers the hull gives: fold the promised effects in, or become a lower
        // bound that names itself. **There is no third branch, and in particular no silent
        // one.**
        CallTarget::Place(o) => {
            let v = vertrag(o);
            indirect.push(IndirectCall {
                place: o.text(),
                effects: v
                    .as_ref()
                    .map(|v| v.effects.iter().cloned().collect())
                    .unwrap_or_default(),
                parameters: v
                    .as_ref()
                    .map(|v| v.parameters.iter().map(|(n, _)| n.clone()).collect::<Vec<_>>())
                    .unwrap_or_default(),
                arguments: args,
                has_contract: v.as_ref().is_some_and(|v| v.has_effects),
                span: r.span,
            });
        }
    }
    for a in &r.argumente {
        if let ExprArt::Ruf(x) = &a.art {
            nimm_ruf(x, aus, indirect, vertrag);
        }
    }
}


fn sammle_kanten(
    b: &Block,
    aus: &mut Vec<(String, Vec<Option<String>>)>,
    indirect: &mut Vec<IndirectCall>,
    vertrag: ContractAt<'_>,
) {
    // **Ueber `alle_ausdruecke`, nicht von Hand** (2026-08-20). Der Handlaeufer hatte
    // `_ => {}` und sah damit weder einen Ruf in `t.slots[schreibt()]` noch einen in
    // `aligned(schreibt(), 4)`. *Sechzehn solcher Laeufer standen im Pruefer, fuenf davon
    // stiegen in einen Index ab.*
    fn aus_expr(
        e: &Expr,
        aus: &mut Vec<(String, Vec<Option<String>>)>,
        indirect: &mut Vec<IndirectCall>,
        vertrag: ContractAt<'_>,
    ) {
        for x in crate::alle_ausdruecke(e) {
            if let ExprArt::Ruf(r) = &x.art {
                nimm_ruf(r, aus, indirect, vertrag);
            }
        }
    }
    for s in &b.anweisungen {
        for e in crate::eigene_ausdruecke(s) {
            aus_expr(e, aus, indirect, vertrag);
        }
        for pr in crate::eigene_praedikate(s) {
            for e in crate::ausdruecke_im_praedikat(pr) {
                aus_expr(e, aus, indirect, vertrag);
            }
        }
        match &s.art {
            StmtArt::Ruf(r) => nimm_ruf(r, aus, indirect, vertrag),
            StmtArt::LetSonst(l) => {
                if let Some(r) = l.als_ruf() {
                    nimm_ruf(r, aus, indirect, vertrag);
                }
            }
            _ => {}
        }
        for k in crate::unterbloecke(s) {
            sammle_kanten(k, aus, indirect, vertrag);
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
        ExprArt::Ruf(r) if r.heisst("Held") => {
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
        // Was die Anweisung selbst auswertet -- Ausdruecke UND Praedikate. **Das `until`
        // einer `retry`-Schleife fehlte bis 2026-08-19**, und damit war `E008` dort
        // fail-open: `retry warten until tu() == 9` mit schreibendem `tu` kam unter
        // `effects { pure }` mit 0 Fehlern durch.
        for e in crate::eigene_ausdruecke(s) {
            aus_expr(e, aus);
        }
        for pr in crate::eigene_praedikate(s) {
            for e in crate::ausdruecke_im_praedikat(pr) {
                aus_expr(e, aus);
            }
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
    // **An indirect call enters NOTHING here** (2026-08-21). `ruft` is the set of NAMES, and
    // a call through a place has none. *It does not vanish because of that* -- it stands in
    // `Knoten::indirect` and is folded in by `gehe`, with its contract.
    // **This is exactly where the silent hole would have been:** a `_ => {}` at this site
    // would have dropped the callee's effects without replacement, and `E008` would again
    // have ended at the first call boundary.
    if let Some(p) = r.path() {
        if let Some(n) = p.teile.last() {
            // `Some`/`None` sind Konstruktoren, keine Aufrufe (s. «B35»).
            if n.text != "Some" && n.text != "None" && !r.ist_verbundwert() {
                // **Der ganze Pfad, nicht nur sein letztes Stueck.** `a::hilf()` und
                // `b::hilf()` waren bis 2026-08-19 derselbe Name; aufgeloest wird spaeter,
                // in `erhebe_mit`.
                aus.insert(p.text());
            }
        }
    }
    for a in &r.argumente {
        aus_expr(a, aus);
    }
}

/// Jeder Ruf in diesem Ausdruck -- ueber den erschoepfenden Laeufer, damit ein Ruf in
/// Indexposition nicht unsichtbar bleibt.
fn aus_expr(e: &Expr, aus: &mut BTreeSet<String>) {
    for x in crate::alle_ausdruecke(e) {
        if let ExprArt::Ruf(r) = &x.art {
            nimm(r, aus);
        }
    }
}
