//! **Das Uebersetzungszeugnis — K100.4, Weg (b).**
//!
//! `PLAN.md` stellte zwei Wege zur Verfeinerung gegenueber:
//!
//! | | |
//! |---|---|
//! | **(a) verifizierter Erzeuger** | `emit.rs` selbst nach Isabelle. *Gross, einmalig — was CompCert getan hat* |
//! | **(b) Uebersetzungsvalidierung** | je Uebersetzung ein Zeugnis, dass **dieses** C **dieses** Gabbro erhaelt |
//!
//! Und er waehlte (b), mit einem Satz, der die Bauform vorgibt:
//!
//! > *„Die Differenztests sind bereits die schwache Fassung davon — sie messen **ein**
//! > Ergebnis statt aller. Der Weg von hier ist, aus `pruefe-emission.sh` ein ZEUGNIS zu
//! > machen, nicht eine laengere Liste von Beispielen."*
//!
//! ## Was dieses Zeugnis ist
//!
//! **Es beweist die Uebersetzung nicht. Es zaehlt auf, worauf sie ruht** — je Datei, nicht
//! global. Das ist der Unterschied zwischen *„der Erzeuger wird schon"* und einer Liste, die
//! man durchgehen kann:
//!
//! ```text
//! A  die Annahmen        — was die MASCHINE leisten muss (SYNTAX.md 12)
//! B  die Schablonen      — was der ERZEUGER herstellt, was niemand geschrieben hat
//! C  die direkte Absenkung — was 1:1 uebergeht
//! D  das Geloeschte      — was zur Laufzeit nicht existiert
//! ```
//!
//! **Der Programmierer bekommt damit je Programm die Liste dessen, was er vertraut.** Genau
//! das braucht der Satz *„unter der Annahme, dass ganz Gabbro verifiziert ist"*: er wird von
//! einer Redewendung zu einer Aufzaehlung mit Laenge.
//!
//! ## Warum es eine ZWEITE Lesung ist und keine Wiederholung
//!
//! Die Tabelle unten ist **nicht** die `match`-Kaskade des Erzeugers. Sie ist eine unabhaengig
//! gefuehrte Einordnung derselben Konstrukte — und beide muessen sich decken:
//!
//! * Senkt der Erzeuger etwas ab, das hier **nicht** eingeordnet ist, meldet das Zeugnis es
//!   als `UNZUGEORDNET`. *Das ist der Fall „der Erzeuger ist gewachsen und hat es niemandem
//!   gesagt".*
//! * Weigert sich der Erzeuger (`C001`), gibt es kein Zeugnis — die Weigerung steht schon da.
//!
//! > **Eine Vertrauensflaeche, die nur der Erzeuger kennt, ist keine gebuchte.** Dieselbe
//! > Bauart wie `schablonen.rs` gegenueber dem Erzeugercode und `manifest.rs` gegenueber den
//! > `assume`-Zeilen.
//!
//! ## Was es NICHT sagt, und das gehoert in dieselbe Ausgabe
//!
//! * **Es sagt nicht, dass die Schablone gilt** — es sagt, welche und ob sie bewiesen ist.
//! * **Es sagt nicht, dass die direkte Absenkung stimmt.** Sie ruht auf `emit.rs` und den
//!   Differenztests; das sind gemessene EINZELERGEBNISSE, keine Aussage ueber alle Eingaben.
//! * **Es sagt nichts ueber die Annahmen selbst** — nur, dass sie benannt sind.

use gabbro_syntax::ast::*;
use std::collections::BTreeMap;

/// Worauf ein Konstrukt in der Absenkung ruht.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Traegt {
    /// **1:1.** Die C-Form IST die Gabbro-Form; der Erzeuger stellt nichts her.
    /// Vertrauensbasis: `emit.rs` und die Differenztests.
    Direkt,
    /// **Erzeugt.** Der Erzeuger stellt Code her, den niemand geschrieben hat — der Name ist
    /// der Schabloneneintrag, unter dem die Beweispflicht steht.
    Schablone(&'static str),
    /// **Geloescht.** Existiert zur Laufzeit nicht: Geist, Spezifikation, Vertragsklausel.
    /// *Die Loeschung ist selbst eine Zusage und steht deshalb hier statt nirgends.*
    Geloescht,
    /// **Fremd.** Der Erzeuger schreibt den PROTOTYP und die Rufe; den Rumpf schreibt jemand
    /// anderes.
    ///
    /// **Diese Klasse fand das Zeugnis bei seinem ersten Lauf.** `lock KAPPEN protects …
    /// rank 3;` senkt zu vier Prototypen ab (`KAPPEN_nimm`, `_gib`, `_nimm_geteilt`,
    /// `_gib_geteilt`), und `beispiele/10` und `/13` uebersetzen damit sauber -- die Tabelle
    /// hier kannte die Form nicht, und genau das meldete sie als `UNZUGEORDNET`.
    ///
    /// > *Sie ist weder direkt noch erzeugt.* Direkt waere sie, wenn die C-Form die
    /// > Gabbro-Form WAERE; erzeugt, wenn ein Rumpf entstuende. **Hier entsteht ein
    /// > Versprechen an eine Funktion, die es in dieser Uebersetzungseinheit nicht gibt** --
    /// > und dass sie tut, was `lock` sagt, ist keine Aussage dieser Uebersetzung.
    Fremd,
}

/// Ein Konstrukt, wie es im Zeugnis erscheint.
pub struct Posten {
    pub konstrukt: &'static str,
    pub traegt: Traegt,
    /// Warum es dort steht, wo es steht. **Ein Eintrag ohne Grund ist ein Name.**
    pub grund: &'static str,
}

/// **Die Einordnung, unabhaengig vom Erzeuger gefuehrt.**
///
/// Wer hier einen Eintrag hinzufuegt, ohne dass der Erzeuger die Form kennt, bekommt eine
/// Zeile ohne Fundstelle — harmlos. **Wer im Erzeuger eine Form absenkt, ohne sie hier
/// einzutragen, bekommt `UNZUGEORDNET`** — und das ist der Fall, gegen den die Tabelle steht.
pub const EINORDNUNG: &[Posten] = &[
    // -- Deklarationen -----------------------------------------------------------------
    Posten {
        konstrukt: "const",
        traegt: Traegt::Direkt,
        grund: "`#define N u` — ein konstanter Wert, kein erzeugter Code",
    },
    Posten {
        konstrukt: "type (Bereich)",
        traegt: Traegt::Direkt,
        grund: "senkt zu seinem Traeger ab; die Schranke bleibt M1-Faktum (W6)",
    },
    Posten {
        konstrukt: "type (Verbund)",
        traegt: Traegt::Schablone("verbund.konstruktor"),
        grund: "`typedef struct` plus `(P){ .a = … }` — der Konstruktor ist ERZEUGT («B7»)",
    },
    Posten {
        konstrukt: "type (ghost)",
        traegt: Traegt::Geloescht,
        grund: "ein `linear ghost type` existiert zur Laufzeit nicht -- die Loeschung wirkt \
                an Signatur, Rufstelle und Bindung",
    },
    Posten {
        konstrukt: "table",
        traegt: Traegt::Schablone("table.absenkung"),
        grund: "Slotverbund plus festes Feld; `count N` ist der Grund, dass es fest ist",
    },
    Posten {
        konstrukt: "format",
        traegt: Traegt::Schablone("format.roundtrip"),
        grund: "KEIN C-Verbund, sondern Byteleser — ein Format ist eine Zusage ueber BYTES",
    },
    Posten {
        konstrukt: "device",
        traegt: Traegt::Schablone("device.konstruktor"),
        grund: "Griff auf `basis`; jeder Registerzugriff wird ein `volatile` an `basis + Versatz`",
    },
    Posten {
        konstrukt: "device (mirrors)",
        traegt: Traegt::Schablone("device.konstruktor"),
        grund: "Falle 4: `write(GCMD, (read(GSTS) & ~geaendert) | neu)` — eine Zeile je Geraet",
    },
    Posten {
        konstrukt: "lock",
        traegt: Traegt::Fremd,
        grund: "vier Prototypen (`_nimm`, `_gib`, `_nimm_geteilt`, `_gib_geteilt`); Rang und \
                Haltezeit bleiben im Pruefer (W6), der RUMPF kommt von aussen",
    },
    Posten {
        konstrukt: "static",
        traegt: Traegt::Direkt,
        grund: "ohne `mut` ein C-`const` -- ein Schreiben darauf ist dort ein Uebersetzungsfehler; \
                `section` wird ein Attribut, weil Platzierung eine Aussage ist",
    },
    Posten {
        konstrukt: "atomic",
        traegt: Traegt::Direkt,
        grund: "`_Atomic`, und die deklarierte Ordnung steht daneben -- unter A10, das die \
                Sichtbarkeitsaussage traegt und NICHT falsifizierbar ist",
    },
    Posten {
        konstrukt: "publishes",
        traegt: Traegt::Direkt,
        grund: "`atomic_store_explicit` mit der DEKLARIERTEN Ordnung -- ein `=` waere in C \
                `seq_cst`, also eine andere und teurere als die, die dasteht",
    },
    Posten {
        konstrukt: "awaits",
        traegt: Traegt::Direkt,
        grund: "`atomic_load_explicit` mit ACQUIRE -- die Deklaration nennt die Speicherseite, \
                und ein Laden mit `release` gibt es in C11 nicht",
    },
    Posten {
        konstrukt: "fn (impl/raw/prim/extern)",
        traegt: Traegt::Direkt,
        grund: "Prototyp und Rumpf; `-> never` wird `_Noreturn void`",
    },
    Posten {
        konstrukt: "fn (spec)",
        traegt: Traegt::Geloescht,
        grund: "eine Spezifikationsfunktion hat kein C — sie ist Beweisersache",
    },
    Posten {
        konstrukt: "assume / axiom",
        traegt: Traegt::Geloescht,
        grund: "steht als Annahme im Kopf des Erzeugnisses, nicht als Code (SYNTAX.md 12)",
    },
    // -- Anweisungen -------------------------------------------------------------------
    Posten {
        konstrukt: "let",
        traegt: Traegt::Direkt,
        grund: "eine Bindung; der Typ wird NICHT geraten (`C001`)",
    },
    Posten {
        konstrukt: "assignment",
        traegt: Traegt::Direkt,
        grund: "`=`, `+=`, `-=`, `&=`, `|=` — je eine C-Form",
    },
    Posten {
        konstrukt: "if",
        traegt: Traegt::Direkt,
        grund: "eine `else if`-Kette; der Austritt wird durchgereicht",
    },
    Posten {
        konstrukt: "return",
        traegt: Traegt::Direkt,
        grund: "vor jedem `return` werden gehaltene Sperren gegeben",
    },
    Posten {
        konstrukt: "call",
        traegt: Traegt::Direkt,
        grund: "Geistargumente fallen an der Rufstelle weg",
    },
    Posten {
        konstrukt: "match (option)",
        traegt: Traegt::Schablone("option.sonderwert"),
        grund: "ein Vergleich gegen den Sonderwert `N`; die Bindung des `Some`-Zweigs ist der Wert",
    },
    Posten {
        konstrukt: "locks",
        traegt: Traegt::Schablone("gruppe.sperrabdruck"),
        grund: "Nehmen und Geben, auf JEDEM Pfad; Rang und Haltezeit bleiben im Pruefer (W6)",
    },
    Posten {
        konstrukt: "narrow",
        traegt: Traegt::Direkt,
        grund: "die eine Stelle, an der eine Bereichspruefung im C BLEIBT — und sie steht da",
    },
    Posten {
        konstrukt: "traverse",
        traegt: Traegt::Schablone("table.induktion"),
        grund: "eine beschraenkte `for`-Schleife; die Schranke kommt aus `count N`",
    },
    Posten {
        konstrukt: "retry",
        traegt: Traegt::Schablone("table.induktion"),
        grund: "Budget geteilt durch Kosten je Durchgang — die Zahl steht im C, nicht im Kopf",
    },
];

/// Alles, was in dieser Datei vorkommt, mit Fundstellenzahl.
#[derive(Default)]
pub struct Erhebung {
    /// Konstrukt -> wie oft.
    pub posten: BTreeMap<&'static str, usize>,
    /// **Konstrukte, die vorkommen und die `EINORDNUNG` nicht kennt.**
    pub unzugeordnet: Vec<String>,
    /// **Die Ruempfe, die diese Uebersetzungseinheit NICHT schreibt** — mit dem Vertrag, den
    /// Gabbro ueber sie annimmt.
    ///
    /// Das ist die Liste, die uebrig bleibt, wenn man annimmt, dass *ganz Gabbro* verifiziert
    /// ist: **sie loest sich unter dieser Praemisse nicht auf.** Ein `extern fn`, ein
    /// `prim fn`, ein `lock` — Gabbro schreibt den Prototyp und rechnet mit `effects` und
    /// `costs`, die daneben stehen. **Wer sie schreibt, schuldet den Beweis**, und der ist
    /// weder Gabbros Klempnerei noch die Logik des Rufers.
    ///
    /// > *Ein Vertrag, auf den gerechnet wird und dessen Rumpf woanders steht, ist eine
    /// > Annahme — sie steht hier bei den anderen Annahmen und nicht im Kleingedruckten.*
    pub fremde: Vec<(String, String)>,
    /// **Wie viele davon AUSSPRECHEN, was ihr Rumpf herstellen muss** (`ensures`/`maintains`).
    ///
    /// Der Rest steht mit `effects` und `costs` da — und beides sind *Schranken*: ein Rumpf,
    /// der gar nichts tut, erfuellt sie. **Was der Rufer wirklich annimmt, steht dann
    /// nirgends.** Eine Sperre bringt keine mit; sie ist die Bauart selbst.
    pub fremde_mit_pflicht: usize,
}

fn zaehle(e: &mut Erhebung, was: &'static str) {
    if EINORDNUNG.iter().any(|p| p.konstrukt == was) {
        *e.posten.entry(was).or_insert(0) += 1;
    } else {
        e.unzugeordnet.push(was.to_string());
    }
}

/// Die zweite Lesung: was steht in dieser Datei?
pub fn erhebe(baum: &Programm) -> Erhebung {
    let mut e = Erhebung::default();
    let mut geister: Vec<String> = Vec::new();
    crate::fuer_jedes_item(baum, &mut |i| {
        if let ItemArt::Typ(t) = &i.art {
            if t.ghost {
                geister.push(t.name.text.clone());
            }
        }
    });
    crate::fuer_jedes_item(baum, &mut |i| match &i.art {
        ItemArt::Modul(_) | ItemArt::Use(_) => {}
        ItemArt::Konst(_) => zaehle(&mut e, "const"),
        ItemArt::Typ(t) => {
            if t.ghost {
                zaehle(&mut e, "type (ghost)")
            } else if matches!(&t.rumpf, Some(TypExpr::Verbund(f, _)) if !f.is_empty()) {
                zaehle(&mut e, "type (Verbund)")
            } else {
                zaehle(&mut e, "type (Bereich)")
            }
        }
        ItemArt::Tabelle(_) => zaehle(&mut e, "table"),
        ItemArt::Format(_) => zaehle(&mut e, "format"),
        ItemArt::Device(d) => {
            zaehle(&mut e, "device");
            if d.mirrors.is_some() {
                zaehle(&mut e, "device (mirrors)");
            }
        }
        ItemArt::Atomic(_) => zaehle(&mut e, "atomic"),
        ItemArt::Statisch(_) => zaehle(&mut e, "static"),
        ItemArt::Lock(l) => {
            zaehle(&mut e, "lock");
            e.fremde.push((
                format!("{}_nimm / _gib (+ geteilt)", l.name.text),
                "der Rumpf einer Sperre -- gegenseitiger Ausschluss, Fortschritt, und dass \
                 `rank` die Ordnung ist, die der Pruefer annimmt"
                    .into(),
            ));
        }
        ItemArt::Assume(_) | ItemArt::Axiom(_) => zaehle(&mut e, "assume / axiom"),
        ItemArt::Funktion(f) => {
            if matches!(f.klasse, Some(FnKlasse::Spec)) {
                zaehle(&mut e, "fn (spec)");
                return;
            }
            zaehle(&mut e, "fn (impl/raw/prim/extern)");
            match &f.rumpf {
                FnRumpf::Block(b) => block(b, &mut e, &geister),
                // **Kein Rumpf heisst: der Rumpf steht woanders.** Der Erzeuger schreibt
                // einen Prototyp, und die Paesse rechnen mit `effects` und `costs`, die hier
                // daneben stehen -- *als Vertrag, nicht als Messung.*
                FnRumpf::Keiner => {
                    if spricht_seine_pflicht_aus(f) {
                        e.fremde_mit_pflicht += 1;
                    }
                    e.fremde.push((f.name.text.clone(), vertrag(f)))
                }
                FnRumpf::Pred(_) => {}
            }
        }
        // **Kein Auffangzweig.** Ein Item, das hier nicht steht, ist keines, das der Erzeuger
        // stillschweigend mitnimmt — es faellt als `UNZUGEORDNET` auf.
        andere => e.unzugeordnet.push(format!("item `{}`", art_name(andere))),
    });
    e
}

/// **Sagt diese Deklaration, was ihr Rumpf HERSTELLEN muss?**
///
/// `effects` und `costs` sagen, was er anfassen und was er kosten darf — **beides sind
/// Schranken, keine Pflichten.** Ein `extern fn mmu_an(p) -> BootPhase effects { consumes p,
/// writes mmu } costs <= 4096 ops;` erlaubt einen Rumpf, der gar nichts tut: er fasst nichts
/// Verbotenes an und kostet null.
///
/// > *Was der Rufer wirklich annimmt — „danach ist die MMU an" — steht nirgends.*
///
/// **`ensures` an einer Deklaration ohne Rumpf ist genau diese Zeile**, und die Grammatik
/// kennt sie seit jeher. Am 2026-08-17 gemessen: **im ganzen Korpus null Stück.**
pub fn spricht_seine_pflicht_aus(f: &FnDecl) -> bool {
    !f.ensures.is_empty() || !f.maintains.is_empty()
}

/// Der Vertrag, mit dem der Pruefer ueber einen fremden Rumpf rechnet.
fn vertrag(f: &FnDecl) -> String {
    let w = f
        .effects
        .as_ref()
        .map(|e| {
            e.liste
                .iter()
                .map(|x| x.art.text())
                .collect::<Vec<_>>()
                .join(", ")
        })
        .unwrap_or_else(|| "KEINE `effects`-Klausel".into());
    let k = match &f.costs {
        Some(_) => "mit `costs`",
        None => "**ohne `costs`** -- jede Huelle darueber ist eine untere Schranke",
    };
    let pf = if spricht_seine_pflicht_aus(f) {
        format!(", ensures ({})", f.ensures.len() + f.maintains.len())
    } else {
        " -- OHNE `ensures`: was er HERSTELLEN muss, steht nirgends".into()
    };
    format!("effects {{ {w} }}, {k}{pf}")
}

fn art_name(a: &ItemArt) -> &'static str {
    match a {
        ItemArt::Modul(_) => "module",
        ItemArt::Use(_) => "use",
        ItemArt::Typ(_) => "type",
        ItemArt::Konst(_) => "const",
        ItemArt::Statisch(_) => "static",
        ItemArt::Funktion(_) => "fn",
        ItemArt::Format(_) => "format",
        ItemArt::Tabelle(_) => "table",
        ItemArt::Reason(_) => "reason",
        ItemArt::State(_) => "state",
        ItemArt::Device(_) => "device",
        ItemArt::Assume(_) => "assume",
        ItemArt::Axiom(_) => "axiom",
        ItemArt::Check(_) => "check",
        ItemArt::Atomic(_) => "atomic",
        ItemArt::Lock(_) => "lock",
        ItemArt::Gruppe(_) => "group",
        ItemArt::Accumulates(_) => "accumulates",
        ItemArt::Walk(_) => "walk",
        ItemArt::Entry(_) => "entry",
        ItemArt::Boot(_) => "boot",
    }
}

fn block(b: &Block, e: &mut Erhebung, geister: &[String]) {
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Let(_) => zaehle(e, "let"),
            StmtArt::Zuweisung(_) => zaehle(e, "assignment"),
            StmtArt::Return(_) => zaehle(e, "return"),
            StmtArt::Ruf(_) => zaehle(e, "call"),
            StmtArt::Wenn(w) => {
                zaehle(e, "if");
                for (_, r) in &w.zweige {
                    block(r, e, geister);
                }
                if let Some(r) = &w.sonst {
                    block(r, e, geister);
                }
            }
            StmtArt::Match(m) => {
                zaehle(e, "match (option)");
                for z in &m.zweige {
                    block(&z.rumpf, e, geister);
                }
            }
            StmtArt::Sperrt(x) => {
                zaehle(e, "locks");
                block(&x.rumpf, e, geister);
            }
            StmtArt::Narrow(x) => {
                zaehle(e, "narrow");
                block(&x.sonst, e, geister);
            }
            StmtArt::Schleife(sch) => match sch.as_ref() {
                Schleife::Traverse(t) => {
                    zaehle(e, "traverse");
                    block(&t.rumpf, e, geister);
                }
                Schleife::Retry(r) => {
                    zaehle(e, "retry");
                    block(&r.rumpf, e, geister);
                }
                Schleife::Forever(f) => {
                    e.unzugeordnet.push("forever".into());
                    block(&f.rumpf, e, geister);
                }
            },
            StmtArt::LetSonst(_) => e.unzugeordnet.push("let … else".into()),
            StmtArt::Bricht(_) => e.unzugeordnet.push("breaking".into()),
            StmtArt::Publish(_) => zaehle(e, "publishes"),
            StmtArt::AwaitLoad(_) => zaehle(e, "awaits"),
            StmtArt::Exchange(_) => e.unzugeordnet.push("exchange".into()),
            StmtArt::Leave(_) => e.unzugeordnet.push("leave".into()),
            StmtArt::Next(_) => e.unzugeordnet.push("next".into()),
        }
    }
}

/// **Das Zeugnis als Text.** Zeilenformat stabil, ohne Werkzeug lesbar.
pub fn zeige(baum: &Programm, datei: &str) -> String {
    let e = erhebe(baum);
    let mut aus = String::new();
    aus.push_str(&format!("== Uebersetzungszeugnis: {datei} ==\n"));
    aus.push_str(
        "-- Es beweist die Uebersetzung NICHT. Es zaehlt auf, worauf sie ruht.\n\n",
    );

    // -- A: die Annahmen ---------------------------------------------------------------
    let (annahmen, streit) = crate::manifest::vereinige(crate::manifest::sammle(baum));
    aus.push_str("A  DIE ANNAHMEN -- was die MASCHINE leisten muss\n");
    if annahmen.is_empty() {
        aus.push_str("     keine. Diese Einheit nimmt nichts ueber die Maschine an.\n");
    }
    for (n, a) in annahmen.iter().enumerate() {
        let wie = match &a.klasse {
            crate::manifest::Klasse::Falsifizierbar { sonde } => format!("Sonde {sonde}"),
            crate::manifest::Klasse::NichtFalsifizierbar { grund } => {
                format!("NICHT FALSIFIZIERBAR -- {grund}")
            }
        };
        aus.push_str(&format!("     A{}  {:<24} {}\n", n + 1, a.name, wie));
    }
    for s in &streit {
        aus.push_str(&format!("     WIDERSPRUCH: {s}\n"));
    }

    // -- B: die Schablonen -------------------------------------------------------------
    let mut benutzt: Vec<(&'static str, &'static str, usize)> = Vec::new();
    for (k, n) in &e.posten {
        if let Some(p) = EINORDNUNG.iter().find(|p| p.konstrukt == *k) {
            if let Traegt::Schablone(s) = p.traegt {
                benutzt.push((s, k, *n));
            }
        }
    }
    benutzt.sort();
    benutzt.dedup_by(|a, b| a.0 == b.0 && a.1 == b.1);
    aus.push_str("\nB  DIE SCHABLONEN -- was der ERZEUGER herstellt, was niemand geschrieben hat\n");
    if benutzt.is_empty() {
        aus.push_str("     keine. Diese Einheit senkt nur 1:1 ab.\n");
    }
    let mut offen = Vec::new();
    for (s, k, n) in &benutzt {
        let sch = crate::schablonen::SCHABLONEN.iter().find(|x| x.name == *s);
        let stand = sch.map(|x| x.stand.text()).unwrap_or("UNBEKANNT");
        aus.push_str(&format!("     {s:<24} {stand:<10} {n}x  {k}\n"));
        if sch.map(|x| x.stand) != Some(crate::schablonen::Stand::Bewiesen) {
            offen.push(*s);
        }
    }

    // -- C: die direkte Absenkung ------------------------------------------------------
    aus.push_str("\nC  DIE DIREKTE ABSENKUNG -- 1:1, kein erzeugter Code\n");
    for (k, n) in &e.posten {
        if let Some(p) = EINORDNUNG.iter().find(|p| p.konstrukt == *k) {
            if p.traegt == Traegt::Direkt {
                aus.push_str(&format!("     {:<28} {n}x  {}\n", k, p.grund));
            }
        }
    }

    // -- D: das Geloeschte -------------------------------------------------------------
    let geloescht: Vec<_> = e
        .posten
        .iter()
        .filter(|(k, _)| {
            EINORDNUNG
                .iter()
                .any(|p| p.konstrukt == **k && p.traegt == Traegt::Geloescht)
        })
        .collect();
    if !geloescht.is_empty() {
        aus.push_str("\nD  GELOESCHT -- existiert zur Laufzeit nicht\n");
        for (k, n) in geloescht {
            let grund = EINORDNUNG
                .iter()
                .find(|p| p.konstrukt == *k)
                .map(|p| p.grund)
                .unwrap_or("");
            aus.push_str(&format!("     {:<28} {n}x  {grund}\n", k));
        }
    }

    let fremd: Vec<_> = e
        .posten
        .iter()
        .filter(|(k, _)| {
            EINORDNUNG
                .iter()
                .any(|p| p.konstrukt == **k && p.traegt == Traegt::Fremd)
        })
        .collect();
    if !fremd.is_empty() || !e.fremde.is_empty() {
        aus.push_str(
            "\nE  FREMD -- der Erzeuger schreibt den Prototyp, den Rumpf schreibt jemand anderes\n",
        );
        for (k, n) in fremd {
            let grund = EINORDNUNG
                .iter()
                .find(|p| p.konstrukt == *k)
                .map(|p| p.grund)
                .unwrap_or("");
            aus.push_str(&format!("     {:<28} {n}x  {grund}\n", k));
        }
        // **Und hier stehen sie mit Namen.** Das ist die Liste, die uebrig bleibt, wenn man
        // annimmt, dass GANZ Gabbro verifiziert ist -- sie loest sich unter dieser Praemisse
        // nicht auf, weil sie nicht von Gabbro handelt.
        if !e.fremde.is_empty() {
            aus.push_str("\n     Die Ruempfe, die diese Einheit NICHT schreibt, und der Vertrag,\n");
            aus.push_str("     mit dem der Pruefer ueber sie rechnet:\n");
            for (n, v) in &e.fremde {
                aus.push_str(&format!("       {n:<26} {v}\n"));
            }
        }
    }

    // -- Der Befund --------------------------------------------------------------------
    aus.push_str("\n-- BEFUND\n");
    if !e.unzugeordnet.is_empty() {
        let mut u = e.unzugeordnet.clone();
        u.sort();
        u.dedup();
        aus.push_str(&format!(
            "     UNZUGEORDNET: {}\n",
            u.join(", ")
        ));
        aus.push_str(
            "     Diese Formen kommen in der Datei vor und stehen in KEINER Einordnung.\n\
             \x20    Entweder weigert sich der Erzeuger fuer sie (dann steht die Weigerung\n\
             \x20    schon da) -- oder er senkt sie ab, und niemand hat gebucht, worauf.\n",
        );
    }
    // **Eine Zeile traegt die Buchung.** Der Waechter vergleicht genau sie; eine zweite Zahl
    // daneben waere eine Gelegenheit, sich zu widersprechen.
    aus.push_str(&format!(
        "     {} Annahmen, {} Schablonen ({} davon UNBEWIESEN), {} direkte Formen, \
         {} fremde Ruempfe ({} sprechen ihre Pflicht aus)\n",
        annahmen.len(),
        benutzt.len(),
        offen.len(),
        e.posten
            .iter()
            .filter(|(k, _)| EINORDNUNG
                .iter()
                .any(|p| p.konstrukt == **k && p.traegt == Traegt::Direkt))
            .count(),
        e.fremde.len(),
        e.fremde_mit_pflicht
    ));
    if !e.fremde.is_empty() {
        aus.push_str(
            "     Ein fremder Rumpf loest sich auch dann nicht auf, wenn GANZ Gabbro\n\
             \x20    verifiziert ist -- sein Beweis faellt dem an, der ihn schreibt.\n",
        );
    }
    if !offen.is_empty() {
        offen.sort();
        offen.dedup();
        aus.push_str(&format!(
            "     DIE VERTRAUENSFLAECHE DIESER DATEI: {}\n",
            offen.join(", ")
        ));
    }
    aus.push_str(
        "\n-- Und was hier NICHT steht:\n\
         \x20  * dass eine Schablone GILT -- nur, welche und ob sie bewiesen ist\n\
         \x20  * dass die direkte Absenkung stimmt. Sie ruht auf `emit.rs` und den\n\
         \x20    Differenztests -- gemessene EINZELERGEBNISSE, keine Aussage ueber alle Eingaben\n\
         \x20  * dass die Annahmen zutreffen -- nur, dass sie benannt sind\n\
         \x20  * dass eine FREMDE Funktion tut, was ihre Deklaration sagt -- der Rumpf\n\
         \x20    steht nicht in dieser Uebersetzungseinheit\n",
    );
    aus
}

#[cfg(test)]
mod proben {
    use super::*;

    /// **Der `else`-Zweig von `zaehle` ist heute unerreichbar, und das ist Absicht.**
    ///
    /// Jeder Aufruf uebergibt einen Namen, der in `EINORDNUNG` steht — er MUSS, sonst faellt
    /// die Kreuzprobe. Der Zweig steht fuer den Tag, an dem jemand einen `zaehle`-Aufruf
    /// hinzufuegt und den Tabelleneintrag vergisst.
    ///
    /// > *Ein Wachposten ohne Probe ist eine Absicht.* Diese Zeile macht ihn zu einer Zusage.
    #[test]
    fn ein_name_ohne_einordnung_faellt_auf() {
        let mut e = Erhebung::default();
        zaehle(&mut e, "eine Form, die niemand eingetragen hat");
        assert_eq!(e.unzugeordnet.len(), 1, "{:?}", e.unzugeordnet);
        assert!(e.posten.is_empty(), "sie darf nicht ALS gezaehlt durchgehen");
    }

    /// Jede Schablone, auf die die Einordnung zeigt, muss es geben. *Eine Abhaengigkeit auf
    /// einen fehlenden Namen ist schlechter als keine — sie sieht aus wie eine gebuchte.*
    #[test]
    fn jede_genannte_schablone_gibt_es() {
        for p in EINORDNUNG {
            if let Traegt::Schablone(s) = p.traegt {
                assert!(
                    crate::schablonen::SCHABLONEN.iter().any(|x| x.name == s),
                    "`{}` zeigt auf die Schablone `{s}` -- die gibt es nicht",
                    p.konstrukt
                );
            }
        }
    }
}
