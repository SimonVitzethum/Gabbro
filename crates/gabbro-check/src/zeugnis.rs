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
        konstrukt: "type (tagged)",
        traegt: Traegt::Direkt,
        grund: "`struct { marke; union { … } }`, und die Marke ist ein `enum` — damit wird \
                `-Wswitch` ein ZWEITER Leser von `D005`. Dass die `union` das Typrecht nicht \
                verletzt, haelt derselbe Pass: gelesen wird nur, was die Marke nennt",
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
        konstrukt: "accumulates",
        traegt: Traegt::Schablone("accumulates.monoid"),
        grund: "eine Zelle je Kern, gefaltet beim Lesen -- kein CAS, keine unbeschraenkte \
                Schleife. Der aktuelle Kern kommt von aussen (`gabbro_kern`)",
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
        konstrukt: "reason",
        traegt: Traegt::Direkt,
        grund: "ein `enum` mit den DEKLARIERTEN Zahlen; der Text wandert als Kommentar mit. \
                Wie ein Fehler zurueckkommt, steht nirgends -- `let … else` bleibt `C001`",
    },
    Posten {
        konstrukt: "group",
        traegt: Traegt::Geloescht,
        grund: "eine Gruppe erzeugt NICHTS und darf nichts erzeugen: sie ist die \
                Verbindungsaussage ueber zwei Traegern, und ihr Sperrabdruck (`U001`-`U006`) \
                wird zur Uebersetzungszeit nachgerechnet (W6)",
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
        konstrukt: "match (tagged)",
        traegt: Traegt::Direkt,
        grund: "ein `switch` OHNE `default` — der fehlende Sammelzweig IST die Aussage, und \
                `-Wswitch` liest `D005` damit ein zweites Mal. Die Nutzlast kommt aus dem \
                Glied, das die Marke nennt, und nur daraus",
    },
    Posten {
        konstrukt: "rcu",
        traegt: Traegt::Fremd,
        grund: "zwei Prototypen (`_lese_start`, `_lese_ende`) und die Gnadenfrist -- der \
                RUMPF kommt von aussen. Dass nach der Ruecknahme des Zeigers kein Leser mehr \
                drin ist, ist eine Aussage ueber die UMGEBUNG und steht als `assume` daneben",
    },
    Posten {
        konstrukt: "observes",
        traegt: Traegt::Fremd,
        grund: "Betreten und Verlassen des Lesebereichs, auf JEDEM Pfad -- wie `locks`, nur \
                ohne Ausschluss. Wo zurueckgegeben werden darf, rechnet `H011`/`H012` zur \
                Uebersetzungszeit nach (W6)",
    },
    Posten {
        konstrukt: "exchange (compare)",
        traegt: Traegt::Direkt,
        grund: "`atomic_compare_exchange_strong_explicit` mit der DEKLARIERTEN Ordnung -- ein \
                `=` waere in C `seq_cst`, also eine andere und teurere als die, die dasteht. \
                Die `update`-Form bleibt `C001`: ihre Schranke braucht `NCORES`",
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
        konstrukt: "entrust",
        traegt: Traegt::Fremd,
        grund: "der Raum, dessen INHALT Gabbro nicht kennt -- keine Kosten, keine Wirkungen, \
                keine Terminierung. Was dasteht, ist der Vertrag am EINTRITT und die Annahme, \
                unter der er gilt",
    },
    // -- Die Maschinennaht -------------------------------------------------------------
    //
    // **Drei der vier tragen `Fremd`, und das ist die Aussage.** Der Eintrittspfad, die
    // Uebergabe an einen Gast und die Bootstrecke sind in C nicht ausdrueckbar (`iretq`,
    // Registerabdruck, Stapelwechsel); der Erzeuger schreibt den Prototyp und die gepruefte
    // Bezugnahme auf `dispatch`, den Rumpf schreibt jemand anderes. *Genau die Klasse, die
    // `lock` schon traegt.*
    Posten {
        konstrukt: "entry",
        traegt: Traegt::Fremd,
        grund: "Prototyp fuer den Stumpf, der Vektor als Zahl und `dispatch` als GEPRUEFTE \
                Bezugnahme; Registerabdruck, Stapelwechsel und `iretq` schreibt C nicht",
    },
    Posten {
        konstrukt: "boot",
        traegt: Traegt::Fremd,
        grund: "die Reihenfolge ist ein Tokenfluss und damit Uebersetzungszeit (W6); im C \
                stehen der Prototyp der Strecke und je eine gepruefte Bezugnahme auf einen \
                Schritt, der einen Rumpf hat -- die Modeschritte selbst sind `axiom`e",
    },
    Posten {
        konstrukt: "walk",
        traegt: Traegt::Direkt,
        grund: "Knotentyp, `down`/`leaf` als Praedikate ueber dem Eintrag und ein Abstieg, \
                dessen Schrittzahl aus `levels` kommt -- die Invarianten bleiben M1-Faktum (W6)",
    },
    Posten {
        konstrukt: "retry",
        traegt: Traegt::Schablone("table.induktion"),
        grund: "Budget geteilt durch Kosten je Durchgang — die Zahl steht im C, nicht im Kopf",
    },
    Posten {
        konstrukt: "forever",
        traegt: Traegt::Direkt,
        grund: "`for (;;)` — und `per_pass … ops` ist eine Aussage ueber EINEN Durchgang, die                 der Kostenpass zur Uebersetzungszeit haelt (W6). Zur Laufzeit gibt es nichts                 zu zaehlen, also bekommt `on_exceeded` KEINEN Zweig; es bekommt einen                 geprueften Bezug (`static void (*const …)(void) = <Wachhund>`), damit der                 C-Uebersetzer die Klausel ein zweites Mal liest",
    },
    Posten {
        konstrukt: "leave / next",
        traegt: Traegt::Direkt,
        grund: "ein `goto` auf eine benannte Marke und KEIN `break` — die Marke nennt eine                 Schleife, und `break` braeche in C immer die innerste. Die Sperren, die                 INNERHALB der Schleife genommen wurden, werden davor freigegeben",
    },
    Posten {
        konstrukt: "check",
        traegt: Traegt::Direkt,
        grund: "`bool pruefe_<name>(void)` -- der Rumpf ist der GESCHRIEBENE `can_fail`-Block \
                und keine Schablone; erzeugt wird nur seine Huelle. \
                `claim`, `gates` und `counterprobe` fahren als Kommentar mit: sie sind die \
                Erklaerung, die ein Leser des Erzeugnisses sonst nirgends findet. Die \
                Pflicht selbst (`linear ghost Duty`) ist geloescht -- dass sie verbraucht \
                wird, hat M2 entschieden",
    },
    Posten {
        konstrukt: "exchange (update)",
        traegt: Traegt::Schablone("table.induktion"),
        grund: "«C4b»: eine BESCHRAENKTE CAS-Schleife, und beschraenkt ist der Punkt -- eine \
                unbeschraenkte ist genau das, was diese Sprache verbietet. `bounded … ops \
                on_exceeded …` stehen in denselben Woertern wie an einem `retry`, weil es \
                dieselbe Schleife ist. Der Rumpf rechnet alt -> neu und ist REIN: darum darf \
                ein verlorener Wettlauf ihn folgenlos wiederholen",
    },
    Posten {
        konstrukt: "let … else",
        traegt: Traegt::Direkt,
        grund: "«C3a»: `bool f(T *_wert, R *_grund)`, und der `else`-Zweig haengt an dem \
                `bool`. Der Erfolg ist der Rueckgabewert und nicht ein Sonderwert im \
                Ergebnis (das taete `option index into T` schon -- W7), und der GRUND geht \
                durch einen eigenen Ausgang, weil `reason`-Werte vom Menschen vergeben sind \
                und kein Wort fuer „kein Fehler\" frei ist",
    },
    Posten {
        konstrukt: "traverse (Baum)",
        traegt: Traegt::Schablone("table.induktion"),
        grund: "`descendants of` laeuft OHNE Stapel an `tree { child, sibling, parent }` der                 Tabelle, in Nachordnung; `ancestors of` ist die Kette an `parent`. Dass                 beide ENDEN, ruht auf der Wohlfundiertheit -- einer HYPOTHESE der Tabelle,                 nicht einer Laufzeitpruefung, und darum steht es hier",
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
    /// **Die `asm`-Ruempfe, mit der Zahl ihrer Befehlszeilen** («OPT3», 2026-08-19).
    ///
    /// Ein Assemblerblock ist ein Loch in jedem der zwoelf Paesse — Gabbro liest den
    /// Befehlstext **nicht**. `arch`, `effects`, `costs` und `clobbers` daneben sind
    /// Annahmen, keine Messungen, und sie stehen deshalb hier bei den anderen Annahmen.
    ///
    /// > **Die Zahl ist die eigentliche Aussage:** *wie viele Zeilen Assembler traegt ein in
    /// > Gabbro geschriebener Kern?* Sie ist die Flaeche, ueber die dieser Ordner nichts sagt.
    pub asm: Vec<(String, usize)>,
    /// **«F»: rechnet diese Einheit mit Gleitkomma?**
    ///
    /// Sie steht im Zeugnis, weil sie **keine Aussage ueber Zahlen** ist: Gleitkomma aendert
    /// die Aufrufkonvention (dieselbe Funktion uebergibt in `xmm0` oder in `rdi`), und fuer
    /// einen Kernel aendert sie den Kontextwechsel -- FPU-Zustand ist Kontext, lazy switching
    /// hat eine eigene Leckklasse, und Preemption wird teurer.
    ///
    /// *Der Leser des Zeugnisses muss es sehen, ohne den Quelltext zu lesen.*
    pub gleitkomma: bool,
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
    // **Syntaktisch beantwortet, ueber die Typausdruecke** -- eine Frage an den Baum, keine
    // an den Pruefer. *Sie muss auch dann stimmen, wenn M1 geschwiegen hat.*
    fn im_typ(t: &TypExpr) -> bool {
        match t {
            TypExpr::Float(_) => true,
            TypExpr::Feld(a) => im_typ(&a.element),
            TypExpr::Zeiger(z) => im_typ(&z.ziel),
            TypExpr::Verbund(fs, _) => fs.iter().any(|f| im_typ(&f.typ.typ)),
            _ => false,
        }
    }
    crate::fuer_jedes_item(baum, &mut |i| match &i.art {
        ItemArt::Konst(k) => e.gleitkomma |= im_typ(&k.typ),
        ItemArt::Statisch(st) => e.gleitkomma |= im_typ(&st.typ),
        ItemArt::Typ(t) => {
            if let Some(r) = &t.rumpf {
                e.gleitkomma |= im_typ(r);
            }
        }
        ItemArt::Funktion(f) => {
            e.gleitkomma |= f.parameter.iter().any(|p| im_typ(&p.typ));
            e.gleitkomma |= f.ergebnis.as_ref().is_some_and(im_typ);
        }
        ItemArt::Accumulates(a) => e.gleitkomma |= im_typ(&a.typ),
        _ => {}
    });
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
            } else if t.tagged {
                zaehle(&mut e, "type (tagged)")
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
        ItemArt::Accumulates(_) => {
            zaehle(&mut e, "accumulates");
            e.fremde.push((
                "gabbro_kern".into(),
                "liefert die Nummer des laufenden Kerns, kleiner als `per cpu` -- eine \
                 MASCHINENFRAGE, und darum ein fremder Rumpf statt eines Ausdrucks"
                    .into(),
            ));
        }
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
        ItemArt::Reason(_) => zaehle(&mut e, "reason"),
        ItemArt::Rcu(r) => {
            zaehle(&mut e, "rcu");
            e.fremde.push((
                format!("{}_lese_start / _lese_ende", r.name.text),
                "der Rumpf eines RCU-Lesebereichs -- und die GNADENFRIST: dass nach der \
                 Ruecknahme des Zeigers kein Leser mehr drin ist, stellt kein statischer \
                 Pass her"
                    .into(),
            ));
        }
        ItemArt::Gruppe(_) => zaehle(&mut e, "group"),
        // **«entrust» -- die eine Zeile, um derentwillen das Wort existiert.**
        //
        // Sie nennt den ganzen Vertrag, nicht bloss den Namen: *wer das Zeugnis liest, muss
        // sehen, was der Gast beim Eintritt hat, und unter welcher Annahme.* Ein `entrust`
        // ohne diese Zeile waere ein Sprung ins Ungezeugte, den das Zeugnis verschweigt.
        ItemArt::Entrust(t) => {
            zaehle(&mut e, "entrust");
            let regs = t
                .regs_gast
                .iter()
                .map(|(r, ty)| format!("{}: {}", r.text, ty.text))
                .collect::<Vec<_>>()
                .join(", ");
            e.fremde.push((
                t.name.text.clone(),
                format!(
                    "GAST auf `{}`, Stapel `{}`, Register {{ {} }} -- \
                     Gabbro sagt ueber den Rumpf NICHTS; es gilt `assume {}`",
                    t.arch.text, t.stapel.text, regs, t.annahme.text
                ),
            ));
        }
        // **`walk` -- die einzige der vier, die etwas RECHNET.** Der Abstieg ist C, seine
        // Schrittzahl kommt aus `levels`; nichts daran ist ein fremder Rumpf.
        ItemArt::Walk(_) => zaehle(&mut e, "walk"),
        // **`entry` und `boot` nennen einen Stumpf, den diese Einheit nicht schreibt** -- und
        // die Zeile sagt, WAS er halten muss. *Ein Eintrittspfad ohne diese Zeile waere ein
        // fremder Rumpf, den das Zeugnis verschweigt.*
        ItemArt::Entry(x) => {
            zaehle(&mut e, "entry");
            let regs = |l: &[(gabbro_syntax::ast::Ident, gabbro_syntax::ast::Ident)]| {
                l.iter()
                    .map(|(a, r)| format!("{}: {}", a.text, r.text))
                    .collect::<Vec<_>>()
                    .join(", ")
            };
            e.fremde.push((
                format!("gabbro_eintritt_{}", x.name.text),
                format!(
                    "EINTRITTSPFAD auf `{}`, Stapel `{}`, regs in {{ {} }}, regs out {{ {} }} \
                     -- er haelt den Registerabdruck und kehrt mit `iretq` zurueck; C schreibt \
                     das nicht. Er verteilt an `{}`",
                    x.arch.text,
                    x.stack.text,
                    regs(&x.regs_in),
                    regs(&x.regs_out),
                    x.dispatch.text()
                ),
            ));
        }
        ItemArt::Boot(b) => {
            zaehle(&mut e, "boot");
            e.fremde.push((
                format!("gabbro_boot_{}", b.name.text),
                format!(
                    "BOOTSTRECKE auf `{}`, {} Schritte, dann `{}` -- sie setzt und liest \
                     Maschinenregister, und die Modeschritte sind `axiom`e. Die REIHENFOLGE \
                     haelt der Pruefer (Tokenfluss), nicht dieser Rumpf",
                    b.arch.text,
                    b.schritte.len(),
                    b.dispatch.text()
                ),
            ));
        }
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
                // **Ein `asm`-Rumpf ist BEIDES**: er steht hier in der Einheit, und trotzdem
                // ist alles an ihm eine Annahme. Er zaehlt deshalb als fremder Vertrag UND
                // wird eigens aufgefuehrt — *wer nicht pruefen kann, exportiert.*
                FnRumpf::Asm(a) => {
                    e.asm.push((f.name.text.clone(), a.zeilen.len()));
                    if spricht_seine_pflicht_aus(f) {
                        e.fremde_mit_pflicht += 1;
                    }
                    e.fremde.push((f.name.text.clone(), vertrag(f)));
                }
                FnRumpf::Pred(_) => {}
            }
        }
        // **Ein `check` ist eine Probe mit einem Rumpf** -- und der Rumpf muss mitgelesen
        // werden, sonst faellt jede Form darin durch (`beispiele/06`: das `let … else`).
        ItemArt::Check(c) => {
            zaehle(&mut e, "check");
            block(&c.can_fail, &mut e, &geister);
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
        ItemArt::Rcu(_) => "rcu",
        ItemArt::Gruppe(_) => "group",
        ItemArt::Accumulates(_) => "accumulates",
        ItemArt::Walk(_) => "walk",
        ItemArt::Entry(_) => "entry",
        ItemArt::Entrust(_) => "entrust",
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
                // **Zwei Absenkungen, zwei Buchungen** («C2»). Unterschieden wird
                // SYNTAKTISCH, an den Zweignamen -- diese Lesung wird ausdruecklich
                // unabhaengig vom Erzeuger gefuehrt, sonst deckt sie sich mit ihm, weil
                // sie ihn abschreibt.
                let option = m.zweige.len() == 2
                    && m.zweige.iter().any(|z| z.variante.text == "Some")
                    && m.zweige.iter().any(|z| z.variante.text == "None");
                zaehle(e, if option { "match (option)" } else { "match (tagged)" });
                for z in &m.zweige {
                    block(&z.rumpf, e, geister);
                }
            }
            StmtArt::Observiert(o) => {
                zaehle(e, "observes");
                block(&o.rumpf, e, geister);
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
                    // **Ein Baumdurchlauf traegt anderes als ein Feldlauf** («B41b»): dort
                    // steht die Schranke im Typ, hier ruht sie auf einer Invariante.
                    zaehle(
                        e,
                        match &t.domaene {
                            Domaene::NachfahrenVon(_) | Domaene::VorfahrenVon(_) => {
                                "traverse (Baum)"
                            }
                            _ => "traverse",
                        },
                    );
                    block(&t.rumpf, e, geister);
                }
                Schleife::Retry(r) => {
                    zaehle(e, "retry");
                    block(&r.rumpf, e, geister);
                }
                Schleife::Forever(f) => {
                    zaehle(e, "forever");
                    block(&f.rumpf, e, geister);
                }
            },
            StmtArt::LetSonst(l) => {
                zaehle(e, "let … else");
                block(&l.sonst, e, geister);
            }
            StmtArt::Bricht(_) => e.unzugeordnet.push("breaking".into()),
            StmtArt::Publish(_) => zaehle(e, "publishes"),
            StmtArt::AwaitLoad(_) => zaehle(e, "awaits"),
            // **«C4», 2026-08-19.** Nur die VERGLEICHSform senkt ab; `update` bleibt eine
            // Absage und darf darum auch keine Buchung bekommen -- sonst stuende im Zeugnis
            // eine Absenkung, die es nicht gibt.
            StmtArt::Exchange(x) => match &x.form {
                XForm::Vergleich { .. } => zaehle(e, "exchange (compare)"),
                XForm::Update { rumpf, .. } => {
                    zaehle(e, "exchange (update)");
                    block(rumpf, e, geister);
                }
            },
            StmtArt::Leave(_) | StmtArt::Next(_) => zaehle(e, "leave / next"),
        }
    }
}

/// **Das Zeugnis als Text.** Zeilenformat stabil, ohne Werkzeug lesbar.
///
/// `quelle` ist der Quelltext derselben Einheit. **Er kam am 2026-08-21 hinzu**, und zwar
/// nicht aus Bequemlichkeit: Abschnitt F nennt Fundstellen, und eine Fundstelle ohne
/// Zeilennummer ist eine Meinung. *Damit liest das Zeugnis nicht mehr nur den Baum, sondern
/// bekommt zusaetzlich, was der PASS gesehen hat* -- die Alternative waere ein zweiter Leser
/// derselben Frage gewesen.
pub fn zeige(baum: &Programm, datei: &str, quelle: &str) -> String {
    let e = erhebe(baum);
    let stellen = crate::fremdverengungen(baum);
    let mut aus = String::new();
    aus.push_str(&format!("== Uebersetzungszeugnis: {datei} ==\n"));
    aus.push_str(
        "-- It does NOT prove the translation. It lists what the translation RESTS ON.\n\n",
    );

    // -- A: die Annahmen ---------------------------------------------------------------
    let (annahmen, streit) = crate::manifest::vereinige(crate::manifest::sammle(baum));
    aus.push_str("A  THE ASSUMPTIONS -- what the MACHINE has to deliver\n");
    if annahmen.is_empty() {
        aus.push_str("     none. This unit assumes nothing about the machine.\n");
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
    aus.push_str("\nB  THE TEMPLATES -- what the GENERATOR produces, which nobody wrote\n");
    if benutzt.is_empty() {
        aus.push_str("     none. This unit lowers 1:1 only.\n");
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
    aus.push_str("\nC  THE DIRECT LOWERING -- 1:1, no generated code\n");
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
        aus.push_str("\nD  ERASED -- does not exist at run time\n");
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
            "\nE  FOREIGN -- the generator writes the prototype, somebody else the body\n",
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
            aus.push_str("\n     The bodies this unit does NOT write, and the contract\n");
            aus.push_str("     the checker uses to reason about them:\n");
            for (n, v) in &e.fremde {
                aus.push_str(&format!("       {n:<26} {v}\n"));
            }
        }
        // **Die `asm`-Ruempfe eigens** («OPT3»): sie stehen IN dieser Einheit, und trotzdem
        // ist alles an ihnen Annahme -- Gabbro liest den Befehlstext nicht. *Die Zahl ist die
        // eigentliche Aussage: wie viele Zeilen Assembler traegt dieser Kern?*
        if !e.asm.is_empty() {
            let zeilen: usize = e.asm.iter().map(|(_, n)| n).sum();
            aus.push_str(&format!(
                "\n     ASSEMBLY -- {} bodies, {zeilen} instruction lines. Gabbro does NOT read them:\n",
                e.asm.len()
            ));
            for (n, z) in &e.asm {
                aus.push_str(&format!("       {n:<26} {z} lines\n"));
            }
        }
    }

    // -- F: die fremden Vertraege, die GEWIRKT haben -----------------------------------
    //
    // **Getrennt von E, und der Unterschied ist der ganze Posten.** E ist die FLAECHE: jeder
    // fremde Rumpf mit seinem Vertrag. F sind die Stellen, an denen dieser Vertrag im Rufer
    // zu einer Tatsache geworden ist -- *eine Verengung mit Wirkung im Erzeugnis ist etwas
    // anderes als eine Zeile, die niemanden bindet.*
    aus.push_str(&crate::fremdverengung::zeige(&stellen, quelle));

    // -- Der Befund --------------------------------------------------------------------
    if e.gleitkomma {
        aus.push_str("\n-- FLOATING POINT -- and this is NOT a statement about numbers\n");
        aus.push_str(
            "     This unit computes with floating point. That changes the calling \
                convention\n     and the context size -- a statement about preemption, not \
                about digits.\n",
        );
        aus.push_str(
            "     What the generator demands for it: NO -ffast-math (it would break \
                every\n     interval), SSE2, and round-to-nearest-even pinned.\n",
        );
        aus.push_str(
            "     What does NOT stand here: numerical accuracy. The checker carries \
                ranges,\n     not error bounds.\n",
        );
    }
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
            "     These forms occur in the file and stand in NO classification.\n\x20\
                Either the generator refuses them (then the refusal already stands \
                there)\n\x20    -- or it lowers them, and nobody booked what on.\n",
        );
    }
    // **Eine Zeile traegt die Buchung.** Der Waechter vergleicht genau sie; eine zweite Zahl
    // daneben waere eine Gelegenheit, sich zu widersprechen. *Deshalb wuchs sie am
    // 2026-08-21 um ein Glied, statt eine zweite Zeile danebenzustellen.*
    aus.push_str(&format!(
        "     {} assumptions, {} templates ({} of them UNPROVED), {} direct forms, \
         {} foreign bodies ({} state their duty), {} narrowings from foreign contracts\n",
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
        e.fremde_mit_pflicht,
        stellen.len()
    ));
    if !e.fremde.is_empty() {
        aus.push_str(
            "     A foreign body does not dissolve even when all of Gabbro is verified \
                --\n\x20    it is the one class that stays.\n",
        );
    }
    if !stellen.is_empty() {
        aus.push_str(
            "     And a narrowing from a foreign contract is that same class REACHING \
                INTO\n\x20    this translation: the checker believes a range it did not \
                derive.\n",
        );
    }
    if !offen.is_empty() {
        offen.sort();
        offen.dedup();
        aus.push_str(&format!(
            "     THE TRUST SURFACE OF THIS FILE: {}\n",
            offen.join(", ")
        ));
    }
    aus.push_str(
        "\n-- And what does NOT stand here:\n\x20  it does not say that the C is correct. \
            It says what it rests on --\n\x20  and every line of that is a place somebody \
            can look at.\n",
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
