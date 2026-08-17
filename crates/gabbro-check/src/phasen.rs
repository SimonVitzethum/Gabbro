//! **«B37» — die ORDNUNG auf einer linearen Geistmarke.**
//!
//! Das Bootfragment schreibt seinen eigenen Mangel hin (`FRAGMENTE.md`:1293–1299):
//!
//! > *„Die Marke traegt die Reihenfolge, aber sie traegt sie als **LINEARITAET**, nicht als
//! > **ORDNUNG**: `mmu_an` verbraucht die rohe Phase und gibt die gewoehnliche zurueck. Damit
//! > ist „vor der MMU" und „nach der MMU" unterscheidbar -- **aber „Cap-Tabellen vor dem
//! > ersten Cap" ist es nicht**, denn beide liegen in derselben Phase."*
//!
//! **Ein linearer Wert erzwingt eine KETTE, aber nicht WELCHE.** Bei sechs Bootschritten
//! typpruefen alle **720** Reihenfolgen; M2 sieht nur, dass jede Marke genau einmal
//! weitergereicht wird.
//!
//! ## Die Wahl, und das Fragment hatte beide genannt
//!
//! | | Preis |
//! |---|---|
//! | je Schritt eine eigene Marke | *„dann waechst der Wortschatz mit jedem Bootschritt"* |
//! | **eine Ordnung auf Marken** | **gewaehlt** -- zwei Woerter, einmal |
//!
//! ```gabbro
//! linear ghost type BootPhase order { roh, mmu, caps, eps, autoritaet, dienste };
//!
//! extern fn mmu_an(p : BootPhase) -> BootPhase
//!     advances roh -> mmu
//!     effects { consumes p, writes mmu } costs <= 4096 ops;
//! ```
//!
//! Die Stufen sind **Bezeichner in EINER Deklaration**. Der Wortschatz waechst um `order` und
//! `advances` -- einmal, nicht je Schritt.
//!
//! ## Was dieser Pass prueft, in drei Stufen
//!
//! 1. **Die Deklaration** (`O001`, `O002`): `advances a -> b` nennt Stufen, die es gibt, und
//!    geht **vorwaerts**. *Ohne die zweite Haelfte waere `order` eine Liste und keine Ordnung.*
//! 2. **Der Fluss** (`O003`): ein Schritt trifft eine Marke, die auf seiner Ausgangsstufe
//!    steht. **Das ist die Zeile, die `cap_tabellen` und `ipc_tabellen` unvertauschbar macht.**
//! 3. **Die Zusammensetzung** (`O004`): der Rumpf muss auf die Stufe kommen, die seine eigene
//!    `advances`-Zeile zusagt. *Eine Strecke, die unterwegs aufhoert, ist keine Strecke.*
//!
//! ## Und was er NICHT prueft, mit seinem Grund
//!
//! **Ein Phasenschritt innerhalb eines Zweiges oder einer Schleife wird gemeldet, nicht
//! entschieden** (`O005`, Hinweis). Zwei Zweige koennen die Marke auf verschiedene Stufen
//! bringen, und welche danach gilt, ist eine Fallunterscheidung -- *die gehoert dem Beweiser,
//! nicht dieser Buchhaltung.*
//!
//! > *Ein Pass, der bei Verzweigung stillschweigend durchlaesst, ist schlimmer als einer, der
//! > sagt, dass er hier nicht zustaendig ist.*

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};
use std::collections::BTreeMap;

/// Was eine Funktion auf einer Marke tut.
#[derive(Clone)]
struct Schritt {
    marke: String,
    von: String,
    nach: String,
}

pub fn pass(baum: &Programm, absagen: &mut Absagen) {
    // 1. Die Ordnungen. Typname -> Stufen in Reihenfolge.
    let mut ordnungen: BTreeMap<String, Vec<String>> = BTreeMap::new();
    crate::fuer_jedes_item(baum, &mut |i| {
        if let ItemArt::Typ(t) = &i.art {
            if let Some(o) = &t.ordnung {
                ordnungen.insert(
                    t.name.text.clone(),
                    o.iter().map(|s| s.text.clone()).collect(),
                );
            }
        }
    });

    // 2. Die Schritte, und dabei faellt Stufe 1.
    let mut schritte: BTreeMap<String, Schritt> = BTreeMap::new();
    crate::fuer_jedes_item(baum, &mut |i| {
        let ItemArt::Funktion(f) = &i.art else { return };
        let Some((von, nach)) = &f.advances else { return };
        // Welche Marke? Der erste Parameter, dessen Typ eine Ordnung hat.
        let marke = f.parameter.iter().find_map(|p| match &p.typ {
            TypExpr::Pfad(pf) => pf
                .teile
                .last()
                .map(|n| n.text.clone())
                .filter(|n| ordnungen.contains_key(n)),
            _ => None,
        });
        let Some(marke) = marke else {
            absagen.schiebe(
                Absage::fehler(
                    "O001",
                    f.name.span,
                    format!(
                        "`{}` sagt `advances` zu, hat aber keinen Parameter mit einer `order`",
                        f.name.text
                    ),
                )
                .mit_notiz(
                    "eine Stufe ist eine Stufe VON ETWAS -- `linear ghost type P \
                     order { … };`",
                ),
            );
            return;
        };
        let stufen = &ordnungen[&marke];
        let ix = |n: &Ident| stufen.iter().position(|s| *s == n.text);
        let (Some(a), Some(b)) = (ix(von), ix(nach)) else {
            for n in [von, nach] {
                if ix(n).is_none() {
                    absagen.schiebe(
                        Absage::fehler(
                            "O001",
                            n.span,
                            format!("`{}` hat keine Stufe `{}`", marke, n.text),
                        )
                        .mit_notiz(format!("die Stufen sind: {}", stufen.join(", "))),
                    );
                }
            }
            return;
        };
        // **`O002` ist die Zeile, die aus einer Liste eine ORDNUNG macht.**
        if a >= b {
            absagen.schiebe(
                Absage::fehler(
                    "O002",
                    f.name.span,
                    format!(
                        "`{}` geht von `{}` nach `{}` -- das ist kein Schritt vorwaerts",
                        f.name.text, von.text, nach.text
                    ),
                )
                .mit_notiz(format!("die Ordnung ist: {}", stufen.join(" -> ")))
                .mit_notiz(
                    "ohne diese Pruefung waere `order` eine Liste und keine Ordnung -- \
                     und genau das war «B37»",
                ),
            );
            return;
        }
        schritte.insert(
            f.name.text.clone(),
            Schritt {
                marke,
                von: von.text.clone(),
                nach: nach.text.clone(),
            },
        );
    });

    if schritte.is_empty() {
        return;
    }

    // 3. Der Fluss, je Rumpf.
    crate::fuer_jedes_item(baum, &mut |i| {
        let ItemArt::Funktion(f) = &i.art else { return };
        let FnRumpf::Block(rumpf) = &f.rumpf else { return };
        let Some(eigen) = schritte.get(&f.name.text) else {
            // Ein Rumpf ohne eigene `advances`-Zeile darf trotzdem Schritte tun -- dann ist
            // nur nichts zugesagt, was am Ende zu erreichen waere.
            let mut stand = BTreeMap::new();
            fluss(rumpf, &schritte, &mut stand, absagen, false);
            return;
        };
        let mut stand: BTreeMap<String, String> = BTreeMap::new();
        for p in &f.parameter {
            if let TypExpr::Pfad(pf) = &p.typ {
                if pf.teile.last().map(|n| n.text.as_str()) == Some(eigen.marke.as_str()) {
                    stand.insert(p.name.text.clone(), eigen.von.clone());
                }
            }
        }
        let erreicht = fluss(rumpf, &schritte, &mut stand, absagen, true);
        // **`O004`.** Eine Strecke, die unterwegs aufhoert, ist keine Strecke.
        if let Some(letzte) = erreicht {
            if letzte != eigen.nach {
                absagen.schiebe(
                    Absage::fehler(
                        "O004",
                        f.name.span,
                        format!(
                            "`{}` sagt `{} -> {}` zu, der Rumpf kommt bis `{}`",
                            f.name.text, eigen.von, eigen.nach, letzte
                        ),
                    )
                    .mit_notiz(
                        "die Schritte des Rumpfes muessen sich zu der Zusage zusammensetzen, \
                         die darueber steht",
                    ),
                );
            }
        }
    });
}

/// Verfolgt die Stufe je Marke durch einen Block. Gibt die zuletzt erreichte Stufe zurueck.
fn fluss(
    b: &Block,
    schritte: &BTreeMap<String, Schritt>,
    stand: &mut BTreeMap<String, String>,
    absagen: &mut Absagen,
    melden: bool,
) -> Option<String> {
    let mut zuletzt = None;
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Let(l) => {
                if let ExprArt::Ruf(r) = &l.wert.art {
                    if let Some(neu) = anwenden(r, schritte, stand, absagen) {
                        stand.insert(l.name.text.clone(), neu.clone());
                        zuletzt = Some(neu);
                    }
                }
            }
            StmtArt::Ruf(r) => {
                if let Some(neu) = anwenden(r, schritte, stand, absagen) {
                    zuletzt = Some(neu);
                }
            }
            // **`O005` -- gemeldet, nicht entschieden.**
            StmtArt::Wenn(_) | StmtArt::Match(_) | StmtArt::Schleife(_) | StmtArt::Sperrt(_) => {
                if melden && enthaelt_schritt(s, schritte) {
                    absagen.schiebe(
                        Absage::hinweis(
                            "O005",
                            s.span,
                            "ein Phasenschritt steht in einem Zweig oder einer Schleife",
                        )
                        .mit_notiz(
                            "zwei Zweige koennen die Marke auf verschiedene Stufen bringen; \
                             welche danach gilt, ist eine Fallunterscheidung",
                        )
                        .mit_notiz(
                            "dieser Pass entscheidet das NICHT -- er sagt es, statt \
                             stillschweigend durchzulassen",
                        ),
                    );
                }
            }
            _ => {}
        }
    }
    zuletzt
}

/// Wendet einen Ruf auf den Stand an. `None`, wenn er kein Schritt ist.
fn anwenden(
    r: &Ruf,
    schritte: &BTreeMap<String, Schritt>,
    stand: &mut BTreeMap<String, String>,
    absagen: &mut Absagen,
) -> Option<String> {
    let name = r.pfad.teile.last()?.text.clone();
    let sch = schritte.get(&name)?;
    // Welches Argument ist die Marke? Das erste, dessen Name einen Stand hat.
    let arg = r.argumente.iter().find_map(|a| match &a.art {
        ExprArt::Ort(o) if o.suffixe.is_empty() => stand
            .get(&o.basis.text)
            .map(|st| (o.basis.text.clone(), st.clone(), o.span)),
        _ => None,
    });
    let (marke, ist, span) = match arg {
        Some(x) => x,
        // Ohne bekannten Stand wird nichts behauptet -- das ist der Fall „die Marke kommt
        // von aussen und der Rufer sagt nichts zu".
        None => return Some(sch.nach.clone()),
    };
    // **`O003` -- die Zeile, die die 720 Reihenfolgen auf eine reduziert.**
    if ist != sch.von {
        absagen.schiebe(
            Absage::fehler(
                "O003",
                span,
                format!(
                    "`{name}` setzt `{}` voraus, `{marke}` steht auf `{ist}`",
                    sch.von
                ),
            )
            .mit_notiz(
                "ein linearer Wert erzwingt eine KETTE, aber nicht WELCHE -- diese Zeile \
                 sagt, welche",
            ),
        );
        return None;
    }
    stand.remove(&marke);
    Some(sch.nach.clone())
}

fn enthaelt_schritt(s: &Stmt, schritte: &BTreeMap<String, Schritt>) -> bool {
    let mut gefunden = false;
    let mut sieh = |r: &Ruf| {
        if let Some(n) = r.pfad.teile.last() {
            if schritte.contains_key(&n.text) {
                gefunden = true;
            }
        }
    };
    fn bloecke(s: &Stmt, f: &mut impl FnMut(&Block)) {
        match &s.art {
            StmtArt::Wenn(w) => {
                for (_, r) in &w.zweige {
                    f(r);
                }
                if let Some(r) = &w.sonst {
                    f(r);
                }
            }
            StmtArt::Match(m) => {
                for z in &m.zweige {
                    f(&z.rumpf);
                }
            }
            StmtArt::Sperrt(x) => f(&x.rumpf),
            StmtArt::Schleife(sch) => match sch.as_ref() {
                Schleife::Traverse(t) => f(&t.rumpf),
                Schleife::Retry(r) => f(&r.rumpf),
                Schleife::Forever(x) => f(&x.rumpf),
            },
            _ => {}
        }
    }
    bloecke(s, &mut |b| {
        for k in &b.anweisungen {
            match &k.art {
                StmtArt::Ruf(r) => sieh(r),
                StmtArt::Let(l) => {
                    if let ExprArt::Ruf(r) = &l.wert.art {
                        sieh(r)
                    }
                }
                _ => {}
            }
        }
    });
    gefunden
}
