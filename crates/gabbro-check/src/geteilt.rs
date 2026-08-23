//! **Pass — `locks shared`, die geteilte Sperrnahme.**
//!
//! Das Konstrukt kam nicht aus einem Entwurf, sondern aus einer **Messung**
//! ([`MESSUNGEN.md`](MESSUNGEN.md), Papiertest CapSpace/CDT vom 2026-08-14). Dort starb der
//! Kandidat `locks ordered` an null Prüffällen — und derselbe Test fand die Lücke, die auf
//! keiner Liste stand:
//!
//! > *Die heisseste Sperre des Baums ist ein **Reader-Writer**-Lock
//! > (`static CAPS: RwSpinLock<Caps>`), und der heisse Pfad ist die **geteilte** Seite:
//! > **33 `read()`-Stellen gegen 44 `write()`**. `lock`/`locks` und der `Held`-Zeuge waren
//! > exklusiv gedacht — der meistgelaufene Pfad des Kernels war nicht schreibbar.*
//!
//! ## Warum das ein Konstrukt sein darf und nicht bloss ein Kommentar
//!
//! Weil die Zusage **mechanisch prüfbar** ist, und zwar gegen etwas, das ohnehin dasteht:
//!
//! > **Geteilt halten heisst: die geschützten Plätze lesen, sie nicht schreiben.**
//!
//! `protects { … }` nennt die Plätze; der Rumpf nennt seine Schreibziele. Der Abgleich ist
//! derselbe Handgriff wie in `E006` — kein neuer Beweisbegriff, kein Vertrauen, keine
//! Annahme. **Das ist das Kriterium, an dem `abi { … }` und `locks ordered` gescheitert
//! sind, und dieses Konstrukt besteht es.**
//!
//! ## Die fuenf Absagen
//!
//! **Kennbuchstabe `H` (Halten), nicht `S`.** Beim Bau am 2026-08-14 habe ich `S001`–`S005`
//! vergeben, ohne den Kennungsraum zu pruefen — `schleifen.rs` fuehrt `S001`/`S002` seit
//! Pass 6 fuer die Schleifenmarke und den durchfallenden `else`-Zweig. Zusammen mit der
//! `K003`-Doppelbelegung war das **dreimal dieselbe Klasse an einem Tag**: eine Kennung
//! vergeben, ohne nachzusehen, wer sie schon hat. **Die Giftproben pruefen auf Kennungen** —
//! jede Doppelbelegung macht sie mehrdeutig.
//!
//! * **`H001`** — Schreiben auf einen geschützten Platz unter geteilter Nahme. *Die
//!   tragende Regel.*
//! * **`H002`** — geteilt genommen, aber die Sperre erklärt kein `shared held <= … ops`.
//!   Ohne die Zahl hat die Latenzaussage aus §9.3 für diese Sperre keinen Zweig
//!   (Nebenbefund **N3**: `held` war für **exklusive** Halter gedacht; auf der geteilten
//!   Seite ist die Rechengrösse die **Schreiberwartezeit unter Leserdruck**).
//! * **`H003`** — Hochstufung: exklusive Nahme derselben Sperre **innerhalb** einer
//!   geteilten. Auf einer Drehsperre ist das kein Stilfehler, sondern ein Deadlock.
//! * **`H004`** — `shared held` erklärt, aber die Sperre wird nirgends geteilt genommen.
//!   *Eine Zahl ohne Messstelle ist eine Behauptung; dieselbe Regel wie beim toten
//!   Kandidaten — kein Konstrukt ohne gemessenen Bedarf.*
//! * **`H005`** — **die Zwischenregel an der Aufrufgrenze.** Siehe unten.
//!
//! ## `H005` — **die Zwischenregel ist ERSETZT (2026-08-15), nicht gelockert**
//!
//! Die tragende Regel `H001` sieht nur, was der Block **selbst** schreibt. Ein Aufruf trägt
//! sie nicht mit: ruft ein geteilter Block eine Funktion mit `requires Held(N)`, so schreibt
//! **der Gerufene** exklusiv-berechtigt, während **der Rufer** nur geteilt hält. **Das ist
//! `H001` durch die Hintertür**, und bis Pass 8 steht, ist dieses Loch nicht bloss offen,
//! sondern **durchlässig**: der Zeuge existiert, seine Stärke wird nicht geprüft.
//!
//! Die grobe Fassung lautete: *„Ein geteilter Block ruft **keine** Funktion mit
//! `requires Held(…)`. Punkt."* — zu streng, denn sie verbot auch den harmlosen Aufruf über
//! eine **andere** Sperre. Der Preis stand in der Absage, und die ersetzende Prüfung war
//! dort **angekündigt**. *W5: eine Zwischenregel trägt die Ablösung in ihrer eigenen
//! Absage.* **Hier ist sie.**
//!
//! Die echte Regel, seit `aufrufgraph.rs` steht:
//!
//! > **Ein geteilter Block darf `requires Held(L, shared)` rufen. Eine exklusive
//! > Forderung — `requires Held(L)` — bleibt gesperrt, und zwar nur für die Sperre, die
//! > hier geteilt gehalten wird.**
//!
//! Die Asymmetrie steht damit eine Ebene höher noch einmal so, wie `E007` sie unten
//! schneidet: **wer mehr fordert, als der Rufer hält, fällt; wer weniger fordert, nicht.**
//!
//! *Was die Ablösung gekostet hat:* eine eigene Grammatikregel für den Zeugen
//! (`heldpred = "Held" "(" ident [ "," "shared" ] ")"`), weil `shared` ein Wort des
//! Wortschatzes ist und bleiben soll — **keine Aufweichung des Ausdrucks**.

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};
use gabbro_syntax::span::Span;
use std::collections::{BTreeMap, BTreeSet};

/// Nennt die `requires`-Klausel einen `Held(…)`-Zeugen? — der Prädikatbaum, flach gelesen.
/// Was über eine Sperre im Baum steht.
struct Sperre {
    schuetzt: Vec<String>,
    hat_geteilte_zeit: bool,
    /// Der `rank`. **`None`, wenn er nicht konstant auswertbar ist** -- dann sagt `H006`
    /// nichts, statt eine Ordnung zu erfinden (W9: die Grobheit hat eine Richtung, und die
    /// sichere ist hier Schweigen ueber eine unbekannte Zahl, nicht eine angenommene).
    rang: Option<i128>,
    span: Span,
}

/// **Was am Aufrufrand über den Gerufenen bekannt ist -- modulbewusst.**
///
/// Bis 2026-08-19 schlug `H005` den KURZEN Namen nach. In einem `module`-Block traf das
/// nie, und die Zwischenregel schwieg über jeden Aufruf ausserhalb der Wurzel.
struct Rufwissen<'a> {
    u: &'a crate::umgebung::Umgebung,
    g: &'a crate::aufrufgraph::Graph,
    verlangt: &'a BTreeMap<String, Vec<(String, bool)>>,
    modul: &'a str,
}

impl Rufwissen<'_> {
    /// **Welche Sperren nimmt der Gerufene — er selbst oder einer SEINER Gerufenen?**
    ///
    /// Die Frage, die `H006` bis 2026-08-19 nicht stellen konnte: sie prüfte die Rangordnung
    /// nur INNERPROZEDURAL. Gemessen: `locks L2 { … nimmt_l1(); }` mit `L1` auf Rang 1 und
    /// `L2` auf Rang 2 ging mit **null Fehlern** durch — *ein Zyklus über zwei Funktionen,
    /// und das ist genau die Form, in der ein Deadlock im echten Kernel steht.*
    fn nimmt(&self, pfad: &str) -> Vec<String> {
        let Some(voll) = self
            .u
            .kandidaten_aufloesbar(self.modul, pfad)
            .into_iter()
            .find(|k| self.g.knoten.contains_key(k))
        else {
            return Vec::new();
        };
        let h = self.g.huelle(&voll);
        // **Über einer unvollständigen Hülle wird nicht abgesagt** (R16).
        if h.unvollstaendig.is_some() {
            return Vec::new();
        }
        h.wirkungen
            .iter()
            .filter_map(|w| {
                w.strip_prefix("locks shared ")
                    .or_else(|| w.strip_prefix("locks "))
                    .map(str::to_string)
            })
            .collect()
    }

    fn forderungen(&self, pfad: &str) -> Option<&Vec<(String, bool)>> {
        self.u
            .kandidaten_aufloesbar(self.modul, pfad)
            .into_iter()
            .find_map(|k| self.verlangt.get(&k))
    }
}

pub fn pass(baum: &Programm, absagen: &mut Absagen) {
    let u = crate::umgebung::Umgebung::sammle(baum);
    let mut sperren: BTreeMap<String, Sperre> = BTreeMap::new();
    // **Der Modulpfad statt `""`** («K5.2», 2026-08-19). `rank NKERNE` in einem
    // `module`-Block loeste nie auf -- derselbe Fehler wie im Aufrufgraphen am Vormittag,
    // eine Ebene tiefer.
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        if let ItemArt::Lock(l) = &item.art {
            let rang = u.konst_wert(modul, &l.rang);
            // **`H014` -- ein Rang, den niemand ausrechnen kann, ist keine Ordnung.**
            //
            // `H006` und `H012` uebersprangen beide eine Sperre mit `rang: None`, jeder mit
            // einem stillen `continue`. Gemessen: `lock LA … rank woher()` neben
            // `lock LB … rank 1`, verschachtelt in der falschen Richtung -- **null Fehler.**
            //
            // *Der Rang IST die Ordnung; ohne ihn gibt es keine.* Dieselbe Klasse wie
            // `bounded` ohne Zahl -- und die Absage steht an der DEKLARATION, nicht an jedem
            // Zugriff: dort waere sie eine Meldung je Fundstelle fuer einen Fehler, der
            // einmal gemacht wurde.
            if rang.is_none() {
                absagen.schiebe(
                    Absage::fehler(
                        "H014",
                        l.rang.span,
                        format!("the `rank` of `{}` is not fixed at compile time", l.name.text),
                    )
                    .mit_notiz(
                        "the rank IS the lock order -- without it `H006` and `H012` have \
                         nothing to compare, and both stayed silent",
                    )
                    .mit_notiz(
                        "same class as a `bounded` without a number: a clause the grammar \
                         demands and nobody can read",
                    ),
                );
            }
            sperren.insert(
                l.name.text.clone(),
                Sperre {
                    schuetzt: l.schuetzt.iter().map(|o| o.text()).collect(),
                    hat_geteilte_zeit: l.geteilte_haltezeit.is_some(),
                    rang,
                    span: l.name.span,
                },
            );
        }
    });

    undeclared_locks(baum, &sperren, absagen);

    // Wer einen `Held(…)`-Zeugen verlangt, darf aus einem geteilten Block nicht gerufen
    // werden -- bis Pass 8 die Staerke des Zeugen wirklich prueft (S005).
    // **Aus dem Aufrufgraphen, nicht aus einem eigenen Durchgang.** Er traegt die Staerke
    // je Forderung -- genau das, was die Zwischenregel nicht hatte.
    let g = crate::aufrufgraph::erhebe_mit(baum, &u);
    let verlangt: BTreeMap<String, Vec<(String, bool)>> = g
        .knoten
        .iter()
        .filter(|(_, k)| !k.verlangt.is_empty())
        .map(|(n, k)| (n.clone(), k.verlangt.clone()))
        .collect();

    let mut geteilt_genommen: Vec<String> = Vec::new();
    let mut ueberhaupt_genommen: Vec<String> = Vec::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let ItemArt::Funktion(f) = &item.art else {
            return;
        };
        let FnRumpf::Block(b) = &f.rumpf else {
            return;
        };
        let rw = Rufwissen { u: &u, g: &g, verlangt: &verlangt, modul };
        block(b, &[], &[], &[], &sperren, &rw, &mut geteilt_genommen, absagen);
    });

    // **Die RCU-Domaenen -- vor H007 gesammelt, weil H007 sie BRAUCHT.**
    //
    // Ein Leser in `observes` darf die Schreibersperre nicht brauchen; sonst waere RCU eine
    // Sperre mit einem zweiten Namen.
    let mut rcu_domaenen: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut rueckgaben: BTreeMap<String, String> = BTreeMap::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Rcu(r) = &item.art {
            rcu_domaenen.insert(
                r.name.text.clone(),
                r.schuetzt.iter().map(|o| o.text()).collect(),
            );
            if let Some(g) = &r.gibt_zurueck {
                rueckgaben.insert(g.text(), r.name.text.clone());
            }
        }
    });

    undeclared_domains(baum, &rcu_domaenen, absagen);

    // **Welche RCU-Domaene traegt eine GNADENFRISTANNAHME?** (`H015`, 2026-08-21)
    //
    // Eine Annahme deckt eine Domaene, wenn ihr Satz die Domaene BEIM NAMEN nennt -- so, wie
    // `beispiele/31-rcu.gab` es seit jeher schreibt: *„Nach der Ruecknahme des Zeigers ist
    // kein Leser mehr in einem `observes BACCT`."*
    //
    // Der Abgleich laeuft ueber WORTGRENZEN und nicht ueber `contains`: ein Domaenenname ist
    // ein Bezeichner, und ein Teilstring waere ein Treffer, den niemand gemeint hat.
    let mut gnadenfrist: BTreeSet<String> = BTreeSet::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        let ItemArt::Assume(a) = &item.art else { return };
        for wort in a
            .text
            .text
            .split(|c: char| !(c.is_alphanumeric() || c == '_'))
        {
            if rcu_domaenen.contains_key(wort) {
                gnadenfrist.insert(wort.to_string());
            }
        }
    });

    // **H007 -- K11.2.1: `protects` beisst.**
    crate::fuer_jedes_item(baum, &mut |item| {
        let ItemArt::Funktion(f) = &item.art else { return };
        // **Ein `spec fn` fasst zur Laufzeit nichts an.** Es ist Beweisersache, und eine
        // Sperre dort zu verlangen hiesse, eine Laufzeitdisziplin auf einen Geistausdruck
        // anzuwenden. *Gefunden bei der Vorabmessung: beide gemeldeten Stellen des Korpus
        // waren dieselbe `spec fn`.*
        if matches!(f.klasse, Some(FnKlasse::Spec)) {
            return;
        }
        let FnRumpf::Block(b) = &f.rumpf else { return };
        let mut da: Vec<String> = Vec::new();
        sperrnahmen(b, &mut ueberhaupt_genommen);
        if let Some(w) = &f.effects {
            for e in &w.liste {
                // **Geteilt genommen zaehlt mit.** `H001` entscheidet danach, ob ein
                // SCHREIBEN unter geteilter Nahme zulaessig ist -- das ist die Staerke, und
                // sie ist eine andere Frage als die Nahme selbst.
                if let WirkungArt::Sperrt(o) | WirkungArt::SperrtGeteilt(o) = &e.art {
                    da.push(o.text());
                    if !ueberhaupt_genommen.contains(&o.text()) {
                        ueberhaupt_genommen.push(o.text());
                    }
                }
            }
        }
        for p in &f.requires {
            let mut h = Vec::new();
            crate::aufrufgraph::held_aus_pred(p, &mut h);
            da.extend(h.into_iter().map(|(n, _)| n));
        }
        schutz(b, &da, &sperren, &rcu_domaenen, &[], &f.name.text, absagen);
    });

    // **H009/H010 -- RCU, und es ist KEINE Sperre.**
    //
    // Aus «K2»: der zweite Korpus zeigte die Klasse, die der erste nie zeigte. Die Leseseite
    // nimmt gar nichts, die Schreibseite tauscht einen Zeiger und wartet auf eine
    // Gnadenfrist. Daraus zwei Regeln, und beide spiegeln `protects`/`H007`:
    //
    //   H009  ein LESEN einer rcu-geschuetzten Stelle steht in `observes`
    //   H010  ein SCHREIBEN steht zusaetzlich unter einer echten Sperre
    //
    // *Die zweite ist die, die man vergisst:* RCU serialisiert Leser gegen die
    // Rueckgewinnung und **nicht Schreiber gegeneinander**. Wer nur `observes` nimmt und
    // schreibt, hat zwei Schreiber nebeneinander.
    let domaenen = rcu_domaenen.clone();
    if !domaenen.is_empty() {
        crate::fuer_jedes_item(baum, &mut |item| {
            let ItemArt::Funktion(f) = &item.art else { return };
            if matches!(f.klasse, Some(FnKlasse::Spec)) {
                return;
            }
            let FnRumpf::Block(b) = &f.rumpf else { return };
            let mut aussen: Vec<String> = Vec::new();
            if let Some(w) = &f.effects {
                for x in &w.liste {
                    if let WirkungArt::Sperrt(o) | WirkungArt::SperrtGeteilt(o) = &x.art {
                        aussen.push(o.text());
                    }
                }
            }
            rcu_schutz(b, &[], &aussen, &domaenen, &rueckgaben, &sperren, &gnadenfrist, &f.name.text, absagen);
        });
    }

    // **H011 -- eine `locks`-Wirkung, die niemand einloest** (2026-08-19).
    //
    // Der Befund kam von aussen und ist die dritte Richtung derselben Frage. `H007` zaehlt
    // eine deklarierte `locks L`-Wirkung als GEHALTEN -- und das ist am Aufrufrand richtig
    // (dort ist die Zeile die Pflicht des Rufers) und im deklarierenden Rumpf falsch:
    //
    // ```gabbro
    // impl fn schreibt(i : index into T)
    //     effects { writes T.slots, locks L }   -- genommen wird sie NIRGENDS
    // { T.slots[i].x = 1; }
    // ```
    //
    // ging mit **null Fehlern** durch, und `H007` deckte jeden Zugriff mit einer Zeile, die
    // nichts tat. *Die Wirkungsliste war der Beleg fuer sich selbst.*
    //
    // **Eingeloest ist sie auf zwei Wegen**, und beide zaehlen: ein `locks L`-Block im
    // eigenen Rumpf, oder ein Gerufener, dessen Huelle `locks L` traegt (seit
    // 2026-08-15 schliesst eine Wirkungsliste die der Gerufenen ein, `E008`).
    //
    // **Und `requires Held(L)` nimmt aus**: wer die Sperre vom Rufer verlangt, nimmt sie
    // nicht -- `beispiele/09` schreibt genau so (`requires Held(KAPPEN)` neben
    // `locks KAPPEN`), und das ist die haeufigste richtige Form im Korpus.
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let ItemArt::Funktion(f) = &item.art else { return };
        let Some(w) = &f.effects else { return };
        let FnRumpf::Block(b) = &f.rumpf else { return };
        let mut eigene = Vec::new();
        sperrnahmen(b, &mut eigene);
        let mut verlangte = Vec::new();
        for p in &f.requires {
            crate::aufrufgraph::held_aus_pred(p, &mut verlangte);
        }
        // **Die Huelle der GERUFENEN, nicht die eigene.** `huelle(f)` enthaelt `f`s eigene
        // Wirkungsliste -- die Zeile haette sich damit selbst belegt, und der Waechter
        // schwieg beim ersten Lauf ueber genau das Gift, fuer das er gebaut wurde. *R11: eine
        // Probe, die auf Anhieb gruen ist, ist verdaechtig; hier war sie es zu Recht.*
        let huelle = g.huelle_der_gerufenen(&g.schluessel_von(modul, &f.name.text));
        for e in &w.liste {
            let (name, wort) = match &e.art {
                WirkungArt::Sperrt(o) => (o.text(), "locks"),
                WirkungArt::SperrtGeteilt(o) => (o.text(), "locks shared"),
                _ => continue,
            };
            if eigene.contains(&name) || verlangte.iter().any(|(n, _)| n == &name) {
                continue;
            }
            // Ein Gerufener, der sie nimmt, loest sie ebenso ein.
            if huelle
                .wirkungen
                .iter()
                .any(|x| x == &format!("locks {name}") || x == &format!("locks shared {name}"))
            {
                continue;
            }
            // **Ueber einer unvollstaendigen Huelle wird nicht abgesagt** (R16): ein Zyklus
            // oder ein Gerufener ohne `effects` macht die Menge zu einer unteren Schranke,
            // und eine Absage daraus waere eine Behauptung.
            if huelle.unvollstaendig.is_some() {
                continue;
            }
            absagen.schiebe(
                Absage::fehler(
                    "H011",
                    e.span,
                    format!(
                        "`{}` declares `{wort} {name}` but never takes it",
                        f.name.text
                    ),
                )
                .mit_notiz(
                    "`H007` counts a declared `locks` effect as HELD -- so this line covers \
                     every access to the protected places while nothing protects them",
                )
                .mit_notiz(
                    "redeemed by a `locks` block in this body, by a callee whose hull \
                     carries it, or by `requires Held(…)` -- the caller's duty",
                ),
            );
        }
    });

    // **H013 -- K11.2.2: die Ausfuehrungskontexte stehen im Ordner, seit es `entry` gibt.**
    //
    // `PLAN.md` fuehrt die Klasse *Rennen* seit dem 2026-08-16 als **nicht baubar**: *„wer
    // nebenlaeufig laeuft, sagt Gabbro nicht, und ohne das kann `jede Stelle, die zwei
    // Kontexte anfassen, ist gesperrt oder atomar` nicht ausgesprochen werden."*
    //
    // **Der Satz war ueberholt und niemand hat es gemerkt.** `entry … dispatch f` IST die
    // Aufzaehlung der Kontexte -- jeder Eintritt ist ein Weg, auf dem der Kern von aussen
    // betreten wird -- und seit heute traegt der Aufrufgraph die Wirkungen modulbewusst und
    // ueber `observes` hinweg. *Die Zutaten lagen nebeneinander; es fehlte die Zeile, die
    // sie zusammenbringt.*
    //
    // Gemessen vor dem Bau: zwei `entry`, beide auf eine Funktion, die denselben
    // ungeschuetzten `static mut` schreibt -- **null Fehler**.
    //
    // ## Was gilt als gedeckt
    //
    // Eine Sperre (`protects`), eine RCU-Domaene (`protects`), ein `atomic` und ein
    // `accumulates … per cpu` -- die vier Formen, in denen die Sprache geteilten Zustand
    // ueberhaupt ausspricht. **`boot` zaehlt NICHT als Kontext**: der Systemstart laeuft vor
    // den Eintritten, und dafuer stehen `order`/`advances` da, nicht eine Sperre.
    //
    // ## Und warum EIN Eintritt schon reicht
    //
    // Auf einer Maschine mit mehreren Kernen sind zwei Kerne im selben Syscall zwei
    // Kontexte. *Die Regel auf „zwei verschiedene Eintritte" zu beschraenken hiesse,
    // Einprozessorbetrieb anzunehmen -- und das ist genau die Annahme, die Caprocks D0
    // gekostet hat.*
    {
        let mut geschuetzt: Vec<String> = Vec::new();
        for sp in sperren.values() {
            geschuetzt.extend(sp.schuetzt.iter().cloned());
        }
        crate::fuer_jedes_item(baum, &mut |item| match &item.art {
            ItemArt::Rcu(r) => geschuetzt.extend(r.schuetzt.iter().map(|o| o.text())),
            ItemArt::Atomic(a) => geschuetzt.push(a.name.text.clone()),
            // `accumulates … per cpu` hat je Kern eine Zelle -- es gibt nichts zu teilen.
            ItemArt::Accumulates(a) => geschuetzt.push(a.name.text.clone()),
            _ => {}
        });
        // **Nur BEKANNTER, veraenderlicher Weltzustand** -- dieselbe Einschraenkung, die
        // `E010` am 2026-08-16 gelernt hat. Der erste Lauf meldete `beispiele/07` mit
        // `kernzustand`: ein Name, den nur die Wirkungsliste eines FREMDEN Rumpfes nennt und
        // den diese Uebersetzungseinheit gar nicht deklariert. *Eine Absage darueber waere
        // Laerm, der die echten zudeckt* -- und in einer vollstaendigen Einheit kostet die
        // Einschraenkung nichts, weil dort jeder Name aufloest.
        //
        // Ein `static` OHNE `mut` ist unveraenderlich: es gibt nichts zu teilen.
        let mut welt: Vec<String> = Vec::new();
        crate::fuer_jedes_item(baum, &mut |item| match &item.art {
            ItemArt::Statisch(x) if x.veraenderlich => welt.push(x.name.text.clone()),
            ItemArt::Tabelle(x) => welt.push(x.name.text.clone()),
            ItemArt::State(x) => welt.push(x.name.text.clone()),
            _ => {}
        });
        // **«K5.3» -- die Kontextmatrix statt „irgendein Eintritt".**
        //
        // Die Ausnahmen gelten NUR unter der Annahme `ein_kern`: auf mehr als einem Kern
        // schliesst `masks IRQ` gar nichts aus, ein zweiter Kern laeuft weiter. *Die Annahme
        // steht damit im Zeugnis und hat einen Falsifikator -- eine Probe, die auf zwei
        // Kernen bootet.* Ohne die Zeile wird nichts ausgenommen.
        let kontexte = crate::kontexte::erhebe(baum);
        let ein_kern = crate::annahmen(baum).contains_key("ein_kern");
        let mut gemeldet: Vec<String> = Vec::new();
        for k in &kontexte {
            let Some(voll) = g.aufloesen(&u, &k.modul, &k.wurzel) else {
                continue;
            };
            let (span, ziel) = (&k.span, &k.wurzel);
            let h = g.huelle(&voll);
            // Maskiert der Weg die Interrupts? Dann kann ihn auf EINEM Kern nichts
            // unterbrechen -- und nur dann.
            let maskiert = h.wirkungen.iter().any(|w| w.starts_with("masks "));
            if ein_kern && crate::kontexte::ein_kern_deckt(maskiert, k) {
                continue;
            }
            let _ = ziel;
            // **Ueber einer unvollstaendigen Huelle wird nicht abgesagt** (R16).
            if h.unvollstaendig.is_some() {
                continue;
            }
            for w in &h.wirkungen {
                let Some(ort) = w.strip_prefix("writes ") else { continue };
                let grund = ort.split(['.', '[']).next().unwrap_or(ort).to_string();
                if !welt.contains(&grund) {
                    continue;
                }
                if geschuetzt.iter().any(|p| beruehrt(p, &grund) || beruehrt(&grund, p)) {
                    continue;
                }
                if gemeldet.contains(&grund) {
                    continue;
                }
                gemeldet.push(grund.clone());
                absagen.schiebe(
                    Absage::fehler(
                        "H013",
                        *span,
                        format!(
                            "this entry writes `{grund}`, and nothing declares it shared"
                        ),
                    )
                    .mit_notiz(
                        "an `entry` is an execution context, and on more than one core two \
                         cores stand in the SAME one -- a place written there is touched \
                         concurrently",
                    )
                    .mit_notiz(
                        "declared shared by: a `lock … protects`, an `rcu … protects`, an \
                         `atomic`, or `accumulates … per cpu`",
                    ),
                );
            }
        }
    }

    // **H008 -- die Gegenrichtung von H007, und sie haette den Befund zuerst gefunden.**
    //
    // `lock BERICHT protects { farbbericht } rank 2 held <= 50 ops;` stand seit dem Bestehen
    // von `beispiele/05` im Ordner und wurde **nirgends genommen** -- der Platz ist ueber die
    // Paarung `publishes`/`awaits` synchronisiert, nicht ueber eine Sperre. *Zwei Mechanismen
    // fuer denselben Platz, und einer davon war Zierde.*
    //
    // > **Eine `protects`-Klausel, die niemand einhaelt, ist schlimmer als keine:** sie
    // > sieht aus wie eine Zusage und ist eine Behauptung. Dieselbe Bauart wie `S004`.
    for (name, sp) in &sperren {
        if !ueberhaupt_genommen.contains(name)
            && !verlangt.values().any(|v| v.iter().any(|(n, _)| n == name))
        {
            absagen.schiebe(
                Absage::hinweis(
                    "H008",
                    sp.span,
                    format!("`{name}` protects {:?} but is taken nowhere", sp.schuetzt),
                )
                .mit_notiz(
                    "neither a `locks` block nor an `effects { locks … }` nor a \
                     `requires Held(…)` names it",
                )
                .mit_notiz(
                    "if the place is synchronised some other way -- through \
                        `publishes`/`awaits` -- the lock does not belong here; otherwise the \
                        taking is missing",
                ),
            );
        }
    }

    // S004 -- eine Zahl ohne Messstelle. Kein Konstrukt ohne gemessenen Bedarf, und keine
    // Zusage ohne Ort, an dem sie faellt.
    for (name, s) in &sperren {
        if s.hat_geteilte_zeit && !geteilt_genommen.contains(name) {
            absagen.schiebe(
                Absage::hinweis(
                    "H004",
                    s.span,
                    format!("`{name}` declares `shared held` but is never taken shared"),
                )
                .mit_notiz(
                    "a promise with no site at which it can fail is a claim -- and \
                        `protects` is the promise that this place is only touched under this \
                        lock",
                ),
            );
        }
    }
}

/// `offen` ist der Stapel der geteilt gehaltenen Sperren — er trägt die Verschachtelung.
/// Alle Sperren, die ein Rumpf nimmt -- fuer `H008`.
fn sperrnahmen(b: &Block, aus: &mut Vec<String>) {
    for s in &b.anweisungen {
        if let StmtArt::Sperrt(l) = &s.art {
            let n = l.sperre.text();
            if !aus.contains(&n) {
                aus.push(n);
            }
        }
        for k in crate::unterbloecke(s) {
            sperrnahmen(k, aus);
        }
    }
}

/// **`H016` -- a lock name that no declaration explains.** The other direction of `H008`
/// (issued a few lines above), and the more expensive of the two.
///
/// `H008` says *"declared, but taken nowhere"* and is a hint. This rule says *"taken, but
/// declared nowhere"* and is an **error** -- because without a declaration there is no
/// `rank`, and without a rank the order rules compute nothing.
///
/// **Measured 2026-08-21 on a SINGLE unit** (`messung/abi-proben/unbekannte-sperre.gab`):
///
/// ```gabbro
/// pub impl fn f(i : index into T) -> bool effects { writes T.slots, locks NIEDA } costs <= 30 ops
/// { locks NIEDA { T.slots[i].a = 1; } return true; }
/// -> 4 Items, 0 Fehler, 0 Hinweise
/// ```
///
/// Both sites -- the effect list and the block -- name a lock that does not exist, and **no
/// pass looked**. The rank lookup in `rangprobe` above returns `None` and checks nothing; the
/// call-boundary rule in `rufprobe` does the same with a silent `continue`.
///
/// > **At a LIBRARY BOUNDARY this is not an edge case but the normal one:** there every name
/// > comes from elsewhere. A `.gabi` that carries `effects { locks SPEICHER }` and not
/// > `lock SPEICHER … rank 0` disarms the whole lock order -- silently.
///
/// *Measured on `messung/abi-proben/`: the mixer nests `SPEICHER` under `GERAET` AND `GERAET`
/// under `SPEICHER` -- a ring, hence a deadlock -- and passed with **0 errors, 0 hints**,
/// because both names came from `.gabi` files without a `lock` line.* The interface half is
/// answered in `abi.rs`; this rule is what makes the failure loud when it is not.
///
/// Same shape as `H014` (issued in this file, at the declaration): there the rank is present
/// but not computable, here the whole declaration is gone. Both end in the same silence, and
/// both now get a refusal.
fn undeclared_locks(baum: &Programm, sperren: &BTreeMap<String, Sperre>, absagen: &mut Absagen) {
    // **One refusal per NAME, not per site.** Naming `NIEDA` at five places is one mistake,
    // not five -- the same decision as at `H014`, whose refusal stands at the declaration and
    // not at every access.
    let mut reported: BTreeSet<String> = BTreeSet::new();
    let mut refuse = |name: String, span: Span, wo: &str, absagen: &mut Absagen| {
        if sperren.contains_key(&name) || !reported.insert(name.clone()) {
            return;
        }
        absagen.schiebe(
            Absage::fehler(
                "H016",
                span,
                format!("{wo} names `{name}`, and no `lock` declaration explains it"),
            )
            .mit_notiz(
                "the rank IS the lock order -- an undeclared lock has none, so the rank \
                 rules compare nothing and stay silent",
            )
            .mit_notiz(
                "across a library boundary this is the normal case: if the `.gabi` carries \
                 the `locks` effect but not the `lock … rank N` line, the whole lock order \
                 is disarmed without a word",
            ),
        );
    };
    crate::fuer_jedes_item(baum, &mut |item| {
        let ItemArt::Funktion(f) = &item.art else { return };
        // A `spec fn` touches nothing at run time -- the same exemption as at `H007`, which
        // is issued in this file and made for the same reason.
        if matches!(f.klasse, Some(FnKlasse::Spec)) {
            return;
        }
        if let Some(w) = &f.effects {
            for e in &w.liste {
                match &e.art {
                    WirkungArt::Sperrt(o) => {
                        refuse(o.text(), e.span, "this `locks` effect", absagen)
                    }
                    WirkungArt::SperrtGeteilt(o) => {
                        refuse(o.text(), e.span, "this `locks shared` effect", absagen)
                    }
                    // **Written out instead of `_`:** the remaining eight effect kinds name
                    // no lock. Reads, writes, `consumes` and `publishes` name PLACES,
                    // `masks` an interrupt, `allocs` a core, and `diverges`/`pure` carry no
                    // argument at all. *If a ninth is added that names a lock, it fails
                    // here and not in the field.*
                    WirkungArt::Liest(_)
                    | WirkungArt::Schreibt(_)
                    | WirkungArt::Verbraucht(_)
                    | WirkungArt::Veroeffentlicht(_)
                    | WirkungArt::Maskiert(_)
                    | WirkungArt::Belegt(_)
                    | WirkungArt::Divergiert
                    | WirkungArt::Rein => {}
                }
            }
        }
        // **`requires Held(…)` is NOT checked here, and the reason is a measurement.**
        //
        // The first version did check it, and `instrumente/pruefe-emission.sh` went red on
        // fragment F7: `extern fn melde_roh(…) requires Held(PHASE_ROH)`. `PHASE_ROH` is no
        // lock at all -- it is a BOOT PHASE, the witness of a `linear ghost type BootPhase`,
        // and the comment two lines above it in `dokumente/FRAGMENTE.md` says so: *"`roh`
        // means: before the MMU … and that is a PROPERTY OF THE PHASE, not of the device."*
        //
        // > **`Held(…)` carries two readings in this corpus, and nothing distinguishes
        // > them:** "this lock is held" and "we stand in this phase". A rule that refuses
        // > every name it cannot find among the locks would refuse the second reading as a
        // > typo -- *and it would be the rule that is wrong, not the fragment.*
        //
        // The two sites below are unambiguous: `locks X` in an effect list and `locks X { … }`
        // in a body are LOCK positions by grammar, not by convention. **They are also the
        // ones the library boundary needs** -- a `.gabi` carries effect lists, so nothing is
        // lost for the bridge. *Which of the two readings `Held` is meant to have is a
        // language question, and it is booked in `TODO.md` rather than guessed here.*
        if let FnRumpf::Block(b) = &f.rumpf {
            lock_blocks(b, &mut |name, span| {
                refuse(name, span, "this `locks` block", absagen)
            });
        }
    });
}

/// Every `locks` block of a body with its span -- for `H016`.
fn lock_blocks(b: &Block, f: &mut impl FnMut(String, Span)) {
    for s in &b.anweisungen {
        if let StmtArt::Sperrt(l) = &s.art {
            f(l.sperre.text(), l.sperre.span);
        }
        for k in crate::unterbloecke(s) {
            lock_blocks(k, f);
        }
    }
}

/// **`H017` -- an `observes` domain that no `rcu` declaration explains.** The RCU instance
/// of the shape `H016` closed for locks, and it was named as open on the same day
/// (`messung/ABI.md` §6.1: *"Dieselbe Stille steht noch bei der RCU-Domaene"*).
///
/// **Measured 2026-08-23 on `messung/abi-proben/unbekannte-domaene.gab`**, unchanged since
/// it was written for the ABI report:
///
/// ```gabbro
/// pub impl fn liest(i : index into T) -> u32 effects { reads T.slots } costs <= 30 ops
/// { let mut v : u32 = 0; observes NIEDADOM { v = T.slots[i].a; } return v; }
/// -> 4 Items, 0 Fehler, 0 Hinweise
/// ```
///
/// **Why the silence is total and not partial**, and this is the part that makes it worse
/// than the lock case: `rcu_schutz` -- the carrier of `H009`/`H010`/`H011`/`H012`/`H015` --
/// is called at all only `if !domaenen.is_empty()`. A unit that declares NO domain and
/// writes `observes X { … }` never enters the RCU walker; a unit that declares `BACCT` and
/// writes `observes TIPPFEHLER { … }` enters it, pushes the misspelt name onto `beobachtet`
/// and then matches it against nothing.
///
/// > **The second case is the dangerous one, because it INVERTS the rule it looks like it
/// > satisfies.** `H009` demands that a read of an RCU place stand inside `observes` of its
/// > domain. A misspelt domain name does not merely fail to help -- the reader looks
/// > protected to the eye and is unprotected to the pass, and `H009` then refuses at the
/// > read with a message about the wrong thing. *A name that no declaration explains is
/// > invisible to the pass that would use it.*
///
/// **One refusal per NAME, not per site** -- the same decision as at `H016` and `H014`.
/// Naming `NIEDADOM` at six places is one mistake.
///
/// *On the library boundary the rule costs nothing today and cannot: `abi.rs` carries no
/// `rcu` item into a `.gabi` at all (`messung/ABI.md` §5 lists `rcu` among the 14 unmeasured
/// item kinds). There is no way to import a domain, so there is no import to exempt.* **When
/// `rcu` does cross the boundary, this rule is where the exemption has to be written, and
/// `H016` shows the shape.**
fn undeclared_domains(
    baum: &Programm,
    domaenen: &BTreeMap<String, Vec<String>>,
    absagen: &mut Absagen,
) {
    let mut reported: BTreeSet<String> = BTreeSet::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        let ItemArt::Funktion(f) = &item.art else { return };
        // A `spec fn` touches nothing at run time -- the same exemption as at `H007` and
        // `H016`, both issued in this file and made for the same reason.
        if matches!(f.klasse, Some(FnKlasse::Spec)) {
            return;
        }
        let FnRumpf::Block(b) = &f.rumpf else { return };
        observes_blocks(b, &mut |name: String, span: Span| {
            if domaenen.contains_key(&name) || !reported.insert(name.clone()) {
                return;
            }
            absagen.schiebe(
                Absage::fehler(
                    "H017",
                    span,
                    format!("this `observes` names `{name}`, and no `rcu` declaration explains it"),
                )
                .mit_notiz(
                    "`observes D` is the read side of the domain `D` -- without the \
                     declaration there is no `protects` list, so the rules that would use \
                     it match nothing and stay silent",
                )
                .mit_notiz(
                    "worse than a missing rule: a misspelt domain looks protected and is \
                     not, and `H009` then refuses at the READ instead of here",
                ),
            );
        });
    });
}

/// Every `observes` block of a body with its domain name and span -- for `H017`.
fn observes_blocks(b: &Block, f: &mut impl FnMut(String, Span)) {
    for s in &b.anweisungen {
        if let StmtArt::Observiert(o) = &s.art {
            f(o.domaene.text.clone(), o.domaene.span);
        }
        for k in crate::unterbloecke(s) {
            observes_blocks(k, f);
        }
    }
}

/// **`H007` — jeder Zugriff auf einen geschuetzten Platz steht unter seiner Sperre.**
///
/// **Gemessen am 2026-08-17, und es war der Befund, mit dem K11.2 anfing:**
///
/// ```gabbro
/// lock KAPPEN protects { K } rank 3 held <= 40 ops;
/// impl fn schreib(i : index into K) -> bool effects { writes K } costs <= 4 ops
/// { K.slots[i].a = 1; return true; }          -- kein `locks KAPPEN`
/// → 4 Items, 0 Fehler, 0 Hinweise
/// ```
///
/// `H001`–`H006` pruefen die **Disziplin** einer genommenen Sperre — geteilt gegen exklusiv,
/// Rang, Haltezeit. **Sie pruefen nicht, dass sie genommen wird.**
///
/// > *Die Klasse Rennen hing damit nicht am Speichermodell — sie hing an einer Regel, die
/// > niemand gebaut hatte.*
///
/// **Als „genommen" gilt dreierlei**, und das ist keine Nachsicht, sondern die Bauart der
/// Sprache: ein umschliessender `locks`-Block, ein `effects { locks L }` (dann ist die Nahme
/// die Pflicht des Rufers, und `E006` haelt Rumpf gegen Klausel), und ein
/// `requires Held(L)` — der Zeuge IST die Aussage, dass sie gehalten wird.
fn schutz(
    b: &Block,
    da: &[String],
    sperren: &BTreeMap<String, Sperre>,
    rcu: &BTreeMap<String, Vec<String>>,
    beobachtet: &[String],
    wo: &str,
    absagen: &mut Absagen,
) {
    let deckt = |ort: &str| -> Option<String> {
        sperren
            .iter()
            .find(|(_, sp)| sp.schuetzt.iter().any(|p| beruehrt(p, ort)))
            .map(|(n, _)| n.clone())
    };
    // **Die RCU-Ausnahme, und sie ist die ganze Substanz des Konstrukts.**
    //
    // Steht eine Stelle in einer RCU-Domaene und stehen wir in deren `observes`, braucht ein
    // LESEN die Schreibersperre nicht. *Ohne diese Zeile kauft `observes` nichts* -- der
    // Leser muesste die Sperre trotzdem nehmen, und dann waere RCU eine Sperre mit einem
    // zweiten Namen.
    //
    // **Fuer ein SCHREIBEN gilt sie nicht** -- dafuer steht `H010` daneben.
    //
    // *Genauer:* `pruefe` unterscheidet Lesen und Schreiben nicht, also nimmt ein Schreiben
    // in `observes` die Ausnahme mit. **Das ist folgenlos, weil `H010` strenger ist** und die
    // bessere Meldung gibt -- „RCU serialisiert Schreiber nicht" statt „die Sperre fehlt".
    // Ein Schreiben unter der richtigen Sperre besteht beide, eines ohne faellt an `H010`.
    let rcu_deckt_lesen = |ort: &str| -> bool {
        rcu.iter().any(|(d, orte)| {
            beobachtet.iter().any(|b| b == d) && orte.iter().any(|p| beruehrt(p, ort))
        })
    };
    let pruefe = |o: &Ort, absagen: &mut Absagen| {
        let t = o.text();
        let Some(sperre) = deckt(&t) else { return };
        if da.iter().any(|d| d == &sperre) {
            return;
        }
        if rcu_deckt_lesen(&t) {
            return;
        }
        absagen.schiebe(
            Absage::fehler(
                "H007",
                o.span,
                format!("`{t}` is protected by `{sperre}`, and `{wo}` does not hold it"),
            )
            .mit_notiz(
                "held counts as: an enclosing `locks` block, an `effects { locks … }` (then taking it \
                 is the caller's duty), or a `requires Held(…)`",
            )
            .mit_notiz(
                "`protects` named the places all along; until K11.2.1 nobody checked that the lock \
                 is actually TAKEN",
            ),
        );
    };
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Sperrt(l) => {
                let mut innen = da.to_vec();
                innen.push(l.sperre.text());
                schutz(&l.rumpf, &innen, sperren, rcu, beobachtet, wo, absagen);
            }
            // **`observes` haelt NICHTS, und der Waechter muss trotzdem hineinsehen.**
            //
            // Beim Bauen von RCU stand hier zuerst nichts -- und damit war ein `observes`
            // ein blinder Fleck fuer `H007`: ein Schreiber haette sich darin verstecken und
            // die Sperre umgehen koennen. *Ein Bereich, den ein Waechter nicht betritt, ist
            // eine Einladung.* Die Domaene wandert AUSDRUECKLICH nicht in `da`.
            StmtArt::Observiert(o) => {
                let mut tiefer = beobachtet.to_vec();
                tiefer.push(o.domaene.text.clone());
                schutz(&o.rumpf, da, sperren, rcu, &tiefer, wo, absagen);
            }
            StmtArt::Zuweisung(z) => {
                pruefe(&z.ziel, absagen);
                orte_in(&z.wert, &mut |o| pruefe(o, absagen));
            }
            StmtArt::Publish(p) => {
                pruefe(&p.ziel, absagen);
                orte_in(&p.wert, &mut |o| pruefe(o, absagen));
            }
            StmtArt::Let(l) => orte_in(&l.wert, &mut |o| pruefe(o, absagen)),
            StmtArt::Return(Some(x)) => orte_in(x, &mut |o| pruefe(o, absagen)),
            StmtArt::Ruf(r) => {
                for a in &r.argumente {
                    orte_in(a, &mut |o| pruefe(o, absagen));
                }
            }
            StmtArt::Wenn(w) => {
                for (bed, _) in &w.zweige {
                    orte_in(bed, &mut |o| pruefe(o, absagen));
                }
            }
            _ => {}
        }
        // **Der Abstieg über `crate::unterbloecke`** — `locks` und `observes` haben ihn oben
        // schon getan, weil beide den mitgeführten Stand ändern.
        if !matches!(&s.art, StmtArt::Sperrt(_) | StmtArt::Observiert(_)) {
            for k in crate::unterbloecke(s) {
                schutz(k, da, sperren, rcu, beobachtet, wo, absagen);
            }
        }
    }
}

/// Die Orte eines Ausdrucks, **einschliesslich der Indizes** -- `c.slots[naechster]` liest
/// beides.
fn orte_in(e: &Expr, f: &mut impl FnMut(&Ort)) {
    match &e.art {
        ExprArt::Ort(o) => {
            f(o);
            for suf in &o.suffixe {
                if let OrtSuffix::Index(ix) = suf {
                    orte_in(ix, f);
                }
            }
        }
        ExprArt::Klammer(x) | ExprArt::Unaer(_, x) => orte_in(x, f),
        ExprArt::Binaer(_, a, b) => {
            orte_in(a, f);
            orte_in(b, f);
        }
        ExprArt::Ruf(r) => {
            for a in &r.argumente {
                orte_in(a, f);
            }
        }
        _ => {}
    }
}

fn block(
    b: &Block,
    offen: &[String],
    // **Alle** gehaltenen Sperren in Nahmereihenfolge, geteilt wie exklusiv -- die
    // Rangordnung gilt fuer beide Nahmearten gleich. `offen`/`exklusiv` trennen die
    // Staerke; `kette` traegt die REIHENFOLGE.
    kette: &[(String, Option<i128>)],
    // Exklusiv gehaltene Sperren -- eine Schreibstelle unter ihnen ist gedeckt, auch wenn
    // dieselbe Sperre aussen herum geteilt gehalten wird. **Diese Verschachtelung faellt
    // ohnehin mit `H003`; sie soll nicht ZWEIMAL fallen** -- eine Absage, die eine zweite
    // nach sich zieht, laesst den Leser den Fehler an der falschen Stelle suchen.
    exklusiv: &[String],
    sperren: &BTreeMap<String, Sperre>,
    rw: &Rufwissen,
    genommen: &mut Vec<String>,
    absagen: &mut Absagen,
) {
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Sperrt(l) => {
                let name = l.sperre.text();
                if l.geteilt {
                    if !genommen.contains(&name) {
                        genommen.push(name.clone());
                    }
                    match sperren.get(&name) {
                        Some(sp) if !sp.hat_geteilte_zeit => absagen.schiebe(
                            Absage::fehler(
                                "H002",
                                l.sperre.span,
                                format!(
                                    "`{name}` is taken shared but declares no \
                                     `shared held <= … ops`"
                                ),
                            )
                            .mit_notiz(
                                "`held` is meant for EXCLUSIVE holders; on the shared side the quantity that \
                                 counts is the writer's wait under reader pressure, not \
                                 how long one reader holds",
                            )
                            .mit_notiz(
                                "without that number the latency statement of SPRACHE.md §9.3 has no \
                                 branch for this lock",
                            ),
                        ),
                        _ => {}
                    }
                    let mut tiefer = offen.to_vec();
                    tiefer.push(name.clone());
                    let kette2 = rangprobe(&name, l.sperre.span, kette, sperren, absagen);
                    block(&l.rumpf, &tiefer, &kette2, exklusiv, sperren, rw, genommen, absagen);
                } else {
                    // S003 -- Hochstufung. Auf einer Drehsperre ist das kein Stilfehler.
                    if offen.contains(&name) {
                        absagen.schiebe(
                            Absage::fehler(
                                "H003",
                                l.sperre.span,
                                format!(
                                    "`{name}` is taken exclusively although it is already held \
                                     shared here"
                                ),
                            )
                            .mit_notiz(
                                "an upgrade from shared to exclusive waits on its own \
                                    read side -- that is a self-deadlock, not a race",
                            )
                            .mit_notiz(
                                "the honest form is hand-over with revalidation: release, \
                                    take exclusively, check the precondition again",
                            ),
                        );
                    }
                    let mut tiefer = exklusiv.to_vec();
                    tiefer.push(name.clone());
                    let kette2 = rangprobe(&name, l.sperre.span, kette, sperren, absagen);
                    block(&l.rumpf, offen, &kette2, &tiefer, sperren, rw, genommen, absagen);
                }
            }
            StmtArt::Zuweisung(z) => {
                schreibprobe(&z.ziel, s.span, offen, exklusiv, sperren, absagen);
                rufprobe_expr(&z.wert, s.span, offen, kette, sperren, rw, absagen);
            }
            StmtArt::Ruf(r) => rufprobe(r, s.span, offen, kette, sperren, rw, absagen),
            StmtArt::Let(l) => rufprobe_expr(&l.wert, s.span, offen, kette, sperren, rw, absagen),
            StmtArt::Return(Some(e)) => rufprobe_expr(e, s.span, offen, kette, sperren, rw, absagen),
            StmtArt::Publish(p) => schreibprobe(&p.ziel, s.span, offen, exklusiv, sperren, absagen),
            StmtArt::Exchange(e) => {
                schreibprobe(&e.ort, s.span, offen, exklusiv, sperren, absagen)
            }
            StmtArt::Wenn(w) => {
                for (b, _) in &w.zweige {
                    rufprobe_expr(b, s.span, offen, kette, sperren, rw, absagen);
                }
            }
            StmtArt::LetSonst(x) => {
                if let Some(r) = x.als_ruf() {
                    rufprobe(r, s.span, offen, kette, sperren, rw, absagen);
                }
            }
            _ => {}
        }
        // **Der Abstieg über `crate::unterbloecke`** — nur `locks` bleibt oben, weil es die
        // offene Sperrmenge ändert. Vorher fehlte `observes`: ein Aufruf mit
        // `requires Held(L)` aus einem RCU-Leseblock heraus wurde nicht geprüft.
        if !matches!(&s.art, StmtArt::Sperrt(_)) {
            for k in crate::unterbloecke(s) {
                block(k, offen, kette, exklusiv, sperren, rw, genommen, absagen);
            }
        }
    }
}

/// **S001 — die tragende Regel.** Ein Schreibziel unter geteilter Nahme, das die Sperre
/// schützt, ist ein Übersetzungsfehler. Der Abgleich ist derselbe wie in `E006`.
fn schreibprobe(
    ziel: &Ort,
    span: Span,
    offen: &[String],
    exklusiv: &[String],
    sperren: &BTreeMap<String, Sperre>,
    absagen: &mut Absagen,
) {
    let ort = ziel.text();
    for name in offen {
        if exklusiv.contains(name) {
            continue; // innen exklusiv genommen -- die Schreibstelle ist gedeckt (siehe S003)
        }
        let Some(sp) = sperren.get(name) else { continue };
        let Some(platz) = sp.schuetzt.iter().find(|p| beruehrt(p, &ort)) else {
            continue;
        };
        absagen.schiebe(
            Absage::fehler(
                "H001",
                span,
                format!("`{ort}` is written while `{name}` is held only shared"),
            )
            .mit_notiz(format!(
                "`{name}` protects `{platz}` -- holding it shared means: the place is \
                    only read"
            ))
            .mit_notiz(
                "exactly this match is what makes `locks shared` a construct instead of a \
                    comment",
            ),
        );
        return;
    }
}

/// Trifft das Schreibziel `getan` den geschützten Platz `platz`? Der Platz kann als
/// Grundname (`slots`) oder als Pfad (`c.slots`) stehen; das Ziel trägt seinen Zeiger vorn.
fn beruehrt(platz: &str, getan: &str) -> bool {
    let kern = platz.rsplit('.').next().unwrap_or(platz);
    getan.split(['.', '[']).any(|t| t == kern)
}

/// **S005 — die Zwischenregel.** Absichtlich grob: *jeder* `Held(…)`-Zeuge zählt, nicht nur
/// der der gerade geteilt gehaltenen Sperre. Der Preis ist benannt, die Richtung ist sicher.
/// **H005 — die ECHTE Prüfung, seit der Aufrufgraph steht (2026-08-15).**
///
/// Die Zwischenregel sperrte **jeden** `Held(…)`-Zeugen unter geteilter Nahme und nannte
/// ihren Preis in der eigenen Absage. Ersetzt, nicht gelockert:
///
/// > Ein geteilter Block darf `requires Held(L, shared)` rufen. Eine **exklusive** Forderung
/// > auf **der hier geteilt gehaltenen** Sperre fällt.
fn rufprobe(
    r: &Ruf,
    span: Span,
    offen: &[String],
    kette: &[(String, Option<i128>)],
    sperren: &BTreeMap<String, Sperre>,
    rw: &Rufwissen,
    absagen: &mut Absagen,
) {
    // **`H012` -- die Rangordnung ueber die Aufrufgrenze** (2026-08-19).
    //
    // `H006` rechnete die Ordnung im eigenen Rumpf nach und sah einen Ring ueber zwei
    // Funktionen nicht. Gemessen: `locks L2 { … nimmt_l1(); }` mit `L1` auf Rang 1 --
    // **null Fehler**, und das ist ein Deadlock, kein Stilfehler.
    //
    // Geprueft wird gegen die HUELLE des Gerufenen, also auch ueber mehrere Ebenen. Die
    // Meldung heisst `H012` und nicht `H006`, weil der Ort ein anderer ist: dort steht ein
    // `locks`-Block, hier ein Aufruf -- und die Abhilfe ist eine andere.
    // **An indirect call takes no lock and demands none -- and `N036` is what makes that a
    // statement rather than a silence** (2026-08-21).
    //
    // Both rules below key on the callee's NAME: `H012` looks its lock rank up in `rw.nimmt`,
    // `H005` its `requires Held(…)` in `rw.forderungen`. A place has no name, so neither can
    // be answered here. *The answer is therefore given one pass earlier and one level up:* a
    // `fn(…)` type may not promise `locks`, `locks shared` or `requires`, so a callee reached
    // through one cannot be holding or taking a lock in the first place.
    //
    // > **A program that would need the lock order to cross an indirect call is refused, not
    // > passed.** That is the difference between a named gap and a false green.
    let Some(pfad) = r.path() else {
        return;
    };
    if !kette.is_empty() {
        for genommen in rw.nimmt(&pfad.text()) {
            let Some(neu) = sperren.get(&genommen).and_then(|x| x.rang) else {
                continue;
            };
            for (aussen, alt) in kette {
                if aussen == &genommen {
                    continue;
                }
                let Some(alt) = alt else { continue };
                if *alt >= neu {
                    absagen.schiebe(
                        Absage::fehler(
                            "H012",
                            span,
                            format!(
                                "this call takes `{genommen}` (rank {neu}) while \
                                 `{aussen}` (rank {alt}) is held here"
                            ),
                        )
                        .mit_notiz(
                            "the lock order runs UPWARDS, and it runs THROUGH calls -- \
                             `H006` only ever recomputed it inside one body",
                        )
                        .mit_notiz(
                            "the callee's effect hull names the lock; the honest form is \
                             to release the outer lock first and re-check the carrying \
                             condition afterwards",
                        ),
                    );
                }
            }
        }
    }
    if offen.is_empty() {
        return;
    }
    let Some(name) = pfad.teile.last() else {
        return;
    };
    let Some(forderungen) = rw.forderungen(&pfad.text()) else {
        return;
    };
    for (sperre, geteilt) in forderungen {
        if *geteilt || !offen.iter().any(|o| o == sperre) {
            continue;
        }
        absagen.schiebe(
            Absage::fehler(
                "H005",
                span,
                format!(
                    "`{}` requires `Held({sperre})` exclusively but is called here while \
                        it is held shared",
                    name.text
                ),
            )
            .mit_notiz(
                "the callee writes with exclusive authority, the caller holds only a read \
                    right -- and nothing between the two says so",
            )
            .mit_notiz(
                "`requires Held(L, shared)` would be admissible here -- the strength \
                    belongs at the declaration, not at the call",
            ),
        );
    }
}

fn rufprobe_expr(
    e: &Expr,
    span: Span,
    offen: &[String],
    kette: &[(String, Option<i128>)],
    sperren: &BTreeMap<String, Sperre>,
    rw: &Rufwissen,
    absagen: &mut Absagen,
) {
    match &e.art {
        ExprArt::Ruf(r) => {
            rufprobe(r, span, offen, kette, sperren, rw, absagen);
            for a in &r.argumente {
                rufprobe_expr(a, span, offen, kette, sperren, rw, absagen);
            }
        }
        ExprArt::Klammer(x) | ExprArt::Unaer(_, x) => {
            rufprobe_expr(x, span, offen, kette, sperren, rw, absagen)
        }
        ExprArt::Binaer(_, a, b) => {
            rufprobe_expr(a, span, offen, kette, sperren, rw, absagen);
            rufprobe_expr(b, span, offen, kette, sperren, rw, absagen);
        }
        _ => {}
    }
}


/// **`H006` — die Sperrordnung wird geprueft, nicht nur deklariert.**
///
/// `lock … rank N` steht seit der ersten Fassung in der Grammatik, und der Ordner beruft sich
/// an mehreren Stellen darauf: die Deadlockfreiheit des Bestands ruht darauf, und die
/// Traegergruppe sagt seit dem 2026-08-16 ausdruecklich *„die Ordnung wird nicht an der Gruppe
/// deklariert, sie steht in den `rank`-Zahlen."*
///
/// **Bis zu dieser Funktion hat sie niemand nachgerechnet.** Ein `grep '.rang'` ueber dem
/// Pruefer lieferte genau eine Fundstelle, und die verglich auf *Gleichheit*. Eine Zusage, die
/// deklariert, nie geprueft und von einem zweiten Konstrukt als Grundlage benutzt wird, ist
/// schlechter als gar keine: sie sieht aus wie ein Beleg.
///
/// **Gleicher Rang faellt mit.** Zwei Sperren desselben Rangs haben keine Ordnung; wer sie
/// verschachtelt, kann es in zwei Richtungen tun, und genau daraus entsteht die Verklemmung.
/// *Dieselbe Sperre zweimal ist kein Rangfehler* -- das ist `H003`, und eine Absage, die eine
/// zweite nach sich zieht, laesst den Leser den Fehler an der falschen Stelle suchen.
fn rangprobe(
    name: &str,
    span: gabbro_syntax::span::Span,
    kette: &[(String, Option<i128>)],
    sperren: &BTreeMap<String, Sperre>,
    absagen: &mut Absagen,
) -> Vec<(String, Option<i128>)> {
    let rang = sperren.get(name).and_then(|s| s.rang);
    if let Some(neu) = rang {
        for (aussen, alt) in kette {
            if aussen == name {
                continue; // dieselbe Sperre -- das ist H003
            }
            let Some(alt) = alt else { continue };
            if *alt >= neu {
                absagen.schiebe(
                    Absage::fehler(
                        "H006",
                        span,
                        format!(
                            "`{name}` (rank {neu}) is taken under `{aussen}` (rank {alt})"
                        ),
                    )
                    .mit_notiz(
                        "the lock order runs UPWARDS: a lock is only taken while a \
                            strictly smaller rank is held",
                    )
                    .mit_notiz(if *alt == neu {
                        "gleicher Rang ist keine Ordnung: zwei Halter koennen sie in zwei \
                         Richtungen nehmen"
                    } else {
                        "die ehrliche Form ist, die aeussere Sperre vorher freizugeben und \
                         die tragende Bedingung danach ERNEUT zu pruefen"
                    }),
                );
            }
        }
    }
    let mut aus = kette.to_vec();
    aus.push((name.to_string(), rang));
    aus
}

/// **Der RCU-Waechter.** `beobachtet` sind die Domaenen, in deren `observes` wir stehen;
/// `gehalten` die Sperren, die der Rumpf haelt.
fn rcu_schutz(
    b: &Block,
    beobachtet: &[String],
    gehalten: &[String],
    domaenen: &BTreeMap<String, Vec<String>>,
    rueckgaben: &BTreeMap<String, String>,
    sperren: &BTreeMap<String, Sperre>,
    // Die RCU-Domaenen, die eine Gnadenfristannahme beim Namen nennt (`H015`).
    gnadenfrist: &BTreeSet<String>,
    wo: &str,
    absagen: &mut Absagen,
) {
    let deckt = |ort: &str| -> Option<String> {
        domaenen
            .iter()
            .find(|(_, orte)| orte.iter().any(|p| beruehrt(p, ort)))
            .map(|(n, _)| n.clone())
    };
    for s in &b.anweisungen {
        // Lesen: jeder Ort im Ausdruck; Schreiben: das Ziel.
        let mut gelesen: Vec<&Ort> = Vec::new();
        let mut geschrieben: Vec<&Ort> = Vec::new();
        match &s.art {
            StmtArt::Zuweisung(z) => geschrieben.push(&z.ziel),
            StmtArt::Let(l) => orte_aus_expr(&l.wert, &mut gelesen),
            StmtArt::Return(Some(e)) => orte_aus_expr(e, &mut gelesen),
            StmtArt::Observiert(o) => {
                let mut tiefer = beobachtet.to_vec();
                tiefer.push(o.domaene.text.clone());
                rcu_schutz(&o.rumpf, &tiefer, gehalten, domaenen, rueckgaben, sperren, gnadenfrist, wo, absagen);
            }
            StmtArt::Sperrt(l) => {
                let mut tiefer = gehalten.to_vec();
                tiefer.push(l.sperre.text());
                rcu_schutz(&l.rumpf, beobachtet, &tiefer, domaenen, rueckgaben, sperren, gnadenfrist, wo, absagen);
            }
            _ => {}
        }
        // **Der Abstieg über `crate::unterbloecke`** — `observes` und `locks` bleiben oben,
        // weil beide den mitgeführten Stand ändern. Vorher fehlte der `exchange`-Rumpf.
        if !matches!(&s.art, StmtArt::Observiert(_) | StmtArt::Sperrt(_)) {
            for k in crate::unterbloecke(s) {
                rcu_schutz(k, beobachtet, gehalten, domaenen, rueckgaben, sperren, gnadenfrist, wo, absagen);
            }
        }
        match &s.art {
            StmtArt::Publish(p) => geschrieben.push(&p.ziel),
            StmtArt::Ruf(r) => {
                for a in &r.argumente {
                    orte_aus_expr(a, &mut gelesen);
                }
            }
            _ => {}
        }
        for o in gelesen {
            let t = o.text();
            let Some(d) = deckt(&t) else { continue };
            if beobachtet.iter().any(|x| *x == d) {
                continue;
            }
            absagen.schiebe(
                Absage::fehler(
                    "H009",
                    o.span,
                    format!("`{t}` belongs to the RCU domain `{d}`, and `{wo}` does not stand in \
                        `observes`"),
                )
                .mit_notiz(
                    "the read side takes nothing -- but it must be NAMED, otherwise the \
                        grace period has no place it refers to",
                ),
            );
        }
        for o in geschrieben {
            let t = o.text();
            // **H011/H012 -- die Rueckgewinnung.**
            //
            // Die GNADENFRIST selbst ist keine Pruefung, sondern eine Annahme: dass kein Leser
            // das alte Objekt mehr sehen kann, stellt kein statischer Pass her. *Sie gehoert
            // dorthin, wo `progress` steht.* **Zwei Dinge sind aber pruefbar**, und beide sind
            // Fehler, die man wirklich macht.
            if let Some(d) = rueckgaben.get(&t) {
                if !beobachtet.is_empty() {
                    absagen.schiebe(
                        Absage::fehler(
                            "H011",
                            o.span,
                            format!("`{t}` reclaims while `{wo}` stands in `observes`"),
                        )
                        .mit_notiz(
                            "whoever reclaims is not a reader -- a reclaim inside one's \
                                own read region frees a place one still holds",
                        ),
                    );
                }
                let unter = gehalten.iter().any(|g| {
                    sperren.get(g).is_some_and(|sp| {
                        domaenen
                            .get(d)
                            .is_some_and(|orte| orte.iter().any(|p| sp.schuetzt.iter().any(|q| beruehrt(q, p))))
                    })
                });
                if !unter {
                    absagen.schiebe(
                        Absage::fehler(
                            "H012",
                            o.span,
                            format!("`{t}` reclaims without holding the writer lock of `{d}`"),
                        )
                        .mit_notiz(
                            "reclaiming is the write side -- and RCU serialises readers \
                                against it, not writers against each other",
                        ),
                    );
                }
                // **`H015` -- die GNADENFRIST wird VERLANGT** (2026-08-21).
                //
                // `H011` und `H012` halten die zwei PRUEFBAREN Haelften. Die dritte ist
                // keine Pruefung: dass kein Leser das alte Objekt mehr sieht, stellt kein
                // statischer Pass her. **Also wird sie verlangt statt hergestellt** --
                // dieselbe Regel wie `S003` an `progress`, an einem anderen Konstrukt.
                //
                // Gemessen am 2026-08-21, vor dem Bau: `beispiele/43-gegenprobe.gab`
                // deklariert `rcu BACCT … reclaims frei` und nannte keine Gnadenfrist --
                // *0 Fehler.* Der Posten im Ordner stimmte.
                //
                // **Was diese Regel NICHT prueft**, und es steht hier statt in einer
                // Fussnote: dass die Annahme WAHR ist, und dass ihr Satz wirklich von der
                // Gnadenfrist handelt. Sie prueft, dass eine benannte Annahme die Domaene
                // nennt -- *ein Satz, den jemand aufgeschrieben hat und der im Zeugnis
                // steht*, statt einer Unterstellung. Mehr kann eine Sprache hier nicht.
                if !gnadenfrist.contains(d) {
                    absagen.schiebe(
                        Absage::fehler(
                            "H015",
                            o.span,
                            format!("`{t}` reclaims, and no assumption names the grace period of `{d}`"),
                        )
                        .mit_notiz(
                            "no pass establishes that the last reader is gone -- the \
                                assumption names WHO GUARANTEES it, the way `progress` names \
                                who ends the loop",
                        )
                        .mit_notiz(
                            "write an `assume` whose sentence names the domain, e.g. \
                                `assume gnadenfrist_ist_abgelaufen \"… no reader is in an \
                                `observes <domain>` any more\" falsifier <probe>;`",
                        ),
                    );
                }
                continue;
            }
            let Some(d) = deckt(&t) else { continue };
            let unter_sperre = gehalten.iter().any(|g| {
                sperren
                    .get(g)
                    .is_some_and(|sp| sp.schuetzt.iter().any(|p| beruehrt(p, &t)))
            });
            if unter_sperre {
                continue;
            }
            absagen.schiebe(
                Absage::fehler(
                    "H010",
                    o.span,
                    format!("`{t}` is written in `{wo}` without a lock (RCU domain `{d}`)"),
                )
                .mit_notiz(
                    "RCU serialises readers against RECLAIM, not writers against each \
                        other -- the write side needs its own mutual exclusion",
                ),
            );
        }
    }
}

/// **Ueber `crate::alle_orte`, nicht von Hand** (2026-08-20).
///
/// Der Handlaeufer hatte `_ => {}` und stieg nicht in einen `OrtSuffix::Index` ab. `H007`
/// (*jeder Zugriff auf einen geschuetzten Platz steht unter seiner Sperre*) schwieg deshalb,
/// sobald der Zugriff in einer Indexposition, unter `narrow`, in einem `until` oder in der
/// Domaene eines `traverse` stand.
fn orte_aus_expr<'a>(e: &'a Expr, out: &mut Vec<&'a Ort>) {
    out.extend(crate::alle_orte(e));
}
