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
        grund: "`#define N u` — a constant value, no generated code",
    },
    Posten {
        konstrukt: "type (Bereich)",
        traegt: Traegt::Direkt,
        grund: "lowers to its carrier; the bound stays an M1 fact (W6)",
    },
    Posten {
        konstrukt: "type (Verbund)",
        traegt: Traegt::Schablone("verbund.konstruktor"),
        grund: "`typedef struct` plus `(P){ .a = … }` — the constructor is GENERATED («B7»)",
    },
    Posten {
        konstrukt: "type (tagged)",
        traegt: Traegt::Direkt,
        grund: "`struct { tag; union { … } }`, and the tag is an `enum` — which makes \
                `-Wswitch` a SECOND reader of `D005`. That the `union` does not violate the \
                type discipline is held by the same pass: only what the tag names is read",
    },
    Posten {
        konstrukt: "type (ghost)",
        traegt: Traegt::Geloescht,
        grund: "a `linear ghost type` does not exist at run time -- the erasure takes effect \
                at the signature, the call site and the binding",
    },
    Posten {
        konstrukt: "table",
        traegt: Traegt::Schablone("table.absenkung"),
        grund: "slot struct plus a fixed array; `count N` is the reason it is fixed",
    },
    Posten {
        konstrukt: "format",
        traegt: Traegt::Schablone("format.roundtrip"),
        grund: "NOT a C struct but byte readers — a format is a promise about BYTES",
    },
    Posten {
        konstrukt: "device",
        traegt: Traegt::Schablone("device.konstruktor"),
        grund: "a handle on `basis`; every register access becomes a `volatile` at `base + offset`",
    },
    Posten {
        konstrukt: "device (mirrors)",
        traegt: Traegt::Schablone("device.konstruktor"),
        grund: "trap 4: `write(GCMD, (read(GSTS) & ~changed) | new)` — one line per device",
    },
    Posten {
        konstrukt: "lock",
        traegt: Traegt::Fremd,
        grund: "four prototypes (`_nimm`, `_gib`, `_nimm_geteilt`, `_gib_geteilt`); rank and \
                hold time stay in the checker (W6), the BODY comes from outside",
    },
    Posten {
        konstrukt: "static",
        traegt: Traegt::Direkt,
        grund: "without `mut` a C `const` -- a write to it is a compile error there; `section` \
                becomes an attribute, because placement is a statement",
    },
    Posten {
        konstrukt: "accumulates",
        traegt: Traegt::Schablone("accumulates.monoid"),
        grund: "one cell per core, folded on reading -- no CAS, no unbounded loop. The current \
                core comes from outside (`gabbro_kern`)",
    },
    Posten {
        konstrukt: "atomic",
        traegt: Traegt::Direkt,
        grund: "`_Atomic`, and the declared ordering stands beside it -- under A10, which carries \
                the visibility statement and is NOT falsifiable",
    },
    Posten {
        konstrukt: "publishes",
        traegt: Traegt::Direkt,
        grund: "`atomic_store_explicit` with the DECLARED ordering -- an `=` would be `seq_cst` \
                in C, so a different and more expensive one than the one written there",
    },
    Posten {
        konstrukt: "awaits",
        traegt: Traegt::Direkt,
        grund: "`atomic_load_explicit` with ACQUIRE -- the declaration names the memory side, and \
                a load with `release` does not exist in C11",
    },
    Posten {
        konstrukt: "fn (impl/raw/prim/extern)",
        traegt: Traegt::Direkt,
        grund: "prototype and body; `-> never` becomes `_Noreturn void`",
    },
    Posten {
        konstrukt: "fn (spec)",
        traegt: Traegt::Geloescht,
        grund: "a specification function has no C — it is the prover's business",
    },
    Posten {
        konstrukt: "reason",
        traegt: Traegt::Direkt,
        grund: "an `enum` with the DECLARED numbers; the text travels along as a comment. How an \
                error comes back is written nowhere -- `let … else` stays `C001`",
    },
    Posten {
        konstrukt: "group",
        traegt: Traegt::Geloescht,
        grund: "a group generates NOTHING and may generate nothing: it is the connecting \
                statement over two carriers, and its lock footprint (`U001`-`U006`) is \
                recomputed at compile time (W6)",
    },
    Posten {
        konstrukt: "assume / axiom",
        traegt: Traegt::Geloescht,
        grund: "stands as an assumption in the head of the artefact, not as code (SYNTAX.md 12)",
    },
    // -- Anweisungen -------------------------------------------------------------------
    Posten {
        konstrukt: "let",
        traegt: Traegt::Direkt,
        grund: "a binding; the type is NOT guessed (`C001`)",
    },
    Posten {
        konstrukt: "assignment",
        traegt: Traegt::Direkt,
        grund: "`=`, `+=`, `-=`, `&=`, `|=` — one C form each",
    },
    Posten {
        konstrukt: "if",
        traegt: Traegt::Direkt,
        grund: "an `else if` chain; the exit is passed through",
    },
    Posten {
        konstrukt: "return",
        traegt: Traegt::Direkt,
        grund: "before every `return` held locks are released",
    },
    Posten {
        konstrukt: "call",
        traegt: Traegt::Direkt,
        grund: "ghost arguments drop out at the call site",
    },
    Posten {
        konstrukt: "match (option)",
        traegt: Traegt::Schablone("option.sonderwert"),
        grund: "a comparison against the special value `N`; the `Some` branch binds the value",
    },
    Posten {
        konstrukt: "match (tagged)",
        traegt: Traegt::Direkt,
        grund: "a `switch` WITHOUT `default` — the missing catch-all branch IS the statement, and \
                `-Wswitch` thereby reads `D005` a second time. The payload comes out of the \
                member the tag names, and out of that alone",
    },
    Posten {
        konstrukt: "rcu",
        traegt: Traegt::Fremd,
        grund: "two prototypes (`_lese_start`, `_lese_ende`) and the grace period -- the BODY \
                comes from outside. That no reader is left inside once the pointer has been \
                withdrawn is a statement about the ENVIRONMENT and stands beside it as an \
                `assume`",
    },
    Posten {
        konstrukt: "observes",
        traegt: Traegt::Fremd,
        grund: "entering and leaving the read section, on EVERY path -- like `locks`, only without \
                exclusion. Where a return is allowed, `H011`/`H012` recomputes at compile \
                time (W6)",
    },
    Posten {
        konstrukt: "exchange (compare)",
        traegt: Traegt::Direkt,
        grund: "`atomic_compare_exchange_strong_explicit` with the DECLARED ordering -- an `=` \
                would be `seq_cst` in C, so a different and more expensive one than the one \
                written there. The `update` form stays `C001`: its bound needs `NCORES`",
    },
    Posten {
        konstrukt: "locks",
        traegt: Traegt::Schablone("gruppe.sperrabdruck"),
        grund: "take and release, on EVERY path; rank and hold time stay in the checker (W6)",
    },
    Posten {
        konstrukt: "narrow",
        traegt: Traegt::Direkt,
        grund: "the one place where a range check REMAINS in the C — and there it stands",
    },
    Posten {
        konstrukt: "traverse",
        traegt: Traegt::Schablone("table.induktion"),
        grund: "a bounded `for` loop; the bound comes out of `count N`",
    },
    // **`breaking` lowers since 2026-08-31, so it stands here** -- until that day the
    // certificate booked it as `UNZUGEORDNET`, and rightly: the emitter refused it.
    Posten {
        konstrukt: "breaking",
        traegt: Traegt::Direkt,
        grund: "a C block, and nothing else -- at run time the region IS its statements. What is \
                generated is the comment carrying the suspended invariants; the restoration \
                stands as a preservation duty in `gabbro pflichten` and not in the C (W6)",
    },
    Posten {
        konstrukt: "entrust",
        traegt: Traegt::Fremd,
        grund: "the space whose CONTENT Gabbro does not know -- no costs, no effects, no \
                termination. What is written down is the contract at ENTRY and the assumption \
                under which it holds",
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
        grund: "a prototype for the stub, the vector as a number and `dispatch` as a CHECKED \
                reference; the register footprint, the stack switch and `iretq` C does not \
                write",
    },
    Posten {
        konstrukt: "boot",
        traegt: Traegt::Fremd,
        grund: "the order is a token flow and therefore compile time (W6); the C carries the \
                prototype of the sequence and one checked reference per step that has a body \
                -- the mode steps themselves are `axiom`s",
    },
    Posten {
        konstrukt: "walk",
        traegt: Traegt::Direkt,
        grund: "node type, `down`/`leaf` as predicates over the entry, and a descent whose step \
                count comes out of `levels` -- the invariants stay M1 facts (W6)",
    },
    Posten {
        konstrukt: "retry",
        traegt: Traegt::Schablone("table.induktion"),
        grund: "budget divided by the cost per pass — the number is in the C, not in the head",
    },
    Posten {
        konstrukt: "forever",
        traegt: Traegt::Direkt,
        grund: "`for (;;)` — and `per_pass … ops` is a statement about ONE pass, which the cost \
                pass holds at compile time (W6). At run time there is nothing to count, so \
                `on_exceeded` gets NO branch; it gets a checked reference \
                (`static void (*const …)(void) = <watchdog>`), so that the C compiler reads \
                the clause a second time",
    },
    Posten {
        konstrukt: "leave / next",
        traegt: Traegt::Direkt,
        grund: "a `goto` to a named label and NO `break` — the label names a loop, and in C \
                `break` would always break the innermost one. The locks taken INSIDE the loop \
                are released before it",
    },
    Posten {
        konstrukt: "check",
        traegt: Traegt::Direkt,
        grund: "`bool pruefe_<name>(void)` -- the body is the WRITTEN `can_fail` block and no \
                template; only its shell is generated. `claim`, `gates` and `counterprobe` \
                travel along as a comment: they are the explanation a reader of the artefact \
                finds nowhere else. The duty itself (`linear ghost Duty`) is erased -- that \
                it is consumed was decided by M2",
    },
    Posten {
        konstrukt: "exchange (update)",
        traegt: Traegt::Schablone("table.induktion"),
        grund: "«C4b»: a BOUNDED CAS loop, and bounded is the point -- an unbounded one is \
                exactly what this language forbids. `bounded … ops on_exceeded …` stand in \
                the same words as at a `retry`, because it is the same loop. The body \
                computes old -> new and is PURE: that is why a lost race may repeat it \
                without consequence",
    },
    Posten {
        konstrukt: "let … else",
        traegt: Traegt::Direkt,
        grund: "«C3a»: `bool f(T *_wert, R *_grund)`, and the `else` branch hangs on that \
                `bool`. Success is the return value and not a special value in the result \
                (`option index into T` already does that -- W7), and the REASON leaves \
                through an exit of its own, because `reason` values are handed out by people \
                and no word is free for „no error\"",
    },
    Posten {
        konstrukt: "traverse (Baum)",
        traegt: Traegt::Schablone("table.induktion"),
        grund: "`descendants of` runs WITHOUT a stack along the table's \
                `tree { child, sibling, parent }`, in post-order; `ancestors of` is the chain \
                along `parent`. That both TERMINATE rests on well-foundedness -- a HYPOTHESIS \
                of the table, not a run-time check, and that is why it stands here",
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
                "yields the number of the running core, smaller than `per cpu` -- a \
                 MACHINE QUESTION, and therefore a foreign body instead of an expression"
                    .into(),
            ));
        }
        ItemArt::Statisch(_) => zaehle(&mut e, "static"),
        ItemArt::Lock(l) => {
            zaehle(&mut e, "lock");
            e.fremde.push((
                format!("{}_nimm / _gib (+ geteilt)", l.name.text),
                "the body of a lock -- mutual exclusion, progress, and that `rank` is the \
                 order the checker assumes"
                    .into(),
            ));
        }
        ItemArt::Assume(_) | ItemArt::Axiom(_) => zaehle(&mut e, "assume / axiom"),
        ItemArt::Reason(_) => zaehle(&mut e, "reason"),
        ItemArt::Rcu(r) => {
            zaehle(&mut e, "rcu");
            e.fremde.push((
                format!("{}_lese_start / _lese_ende", r.name.text),
                "the body of an RCU read section -- and the GRACE PERIOD: that no reader \
                 is left inside once the pointer has been withdrawn is established by no \
                 static pass"
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
                    "GUEST on `{}`, stack `{}`, registers {{ {} }} -- \
                     Gabbro says NOTHING about the body; `assume {}` holds",
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
                    "ENTRY PATH on `{}`, stack `{}`, regs in {{ {} }}, regs out {{ {} }} \
                     -- it holds the register footprint and returns with `iretq`; C does not \
                     write that. It dispatches to `{}`",
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
                    "BOOT SEQUENCE on `{}`, {} steps, then `{}` -- it sets and reads \
                     machine registers, and the mode steps are `axiom`s. The ORDER is held by \
                     the checker (token flow), not by this body",
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
        .unwrap_or_else(|| "NO `effects` clause".into());
    let k = match &f.costs {
        Some(_) => "with `costs`",
        None => "**without `costs`** -- every envelope above it is a LOWER bound",
    };
    let pf = if spricht_seine_pflicht_aus(f) {
        format!(", ensures ({})", f.ensures.len() + f.maintains.len())
    } else {
        " -- WITHOUT `ensures`: what it must ESTABLISH is written nowhere".into()
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
            // **`breaking` is a booked construct since 2026-08-31.** It used to be pushed
            // straight onto `unzugeordnet` because the emitter refused it -- and the two
            // halves moved together: the lowering and its entry in `EINORDNUNG`.
            StmtArt::Bricht(b) => {
                zaehle(e, "breaking");
                block(&b.rumpf, e, geister);
            }
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
        // **A probe name stands here only where the probe stands as a PROGRAM** (2026-08-30).
        // The certificate is the artefact by which Gabbro carries its promise outward --
        // `Sonde <x>` for a name without a program read as coverage there, and was an
        // assurance about the absence of a refutation. *The assumption still stands; its
        // falsifiability does not.* See `crate::manifest::gedeckt`.
        let wie = match &a.klasse {
            crate::manifest::Klasse::Falsifizierbar { sonde }
                if crate::manifest::gedeckt(sonde) =>
            {
                format!("Sonde {sonde}")
            }
            crate::manifest::Klasse::Falsifizierbar { .. } => {
                "UNCOVERED -- no program for this probe".to_string()
            }
            crate::manifest::Klasse::NichtFalsifizierbar { grund } => {
                format!("NOT FALSIFIABLE -- {grund}")
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
            // **«B27», the register allocation at entry -- a NAMED delegation** (2026-08-30).
            //
            // `messung/EINTRITTSBELEGUNG.md` decided it and left one thing undone: the name.
            // A pass holding the constraint letters against a register table per `arch` is
            // not wrong, but it has **zero measured demand** -- the whole clean corpus holds
            // exactly ONE `prim fn` site with an `arch` and no allocation, and a table per
            // architecture is upkeep. *Rule A: no construct without measured demand.*
            //
            // So the allocation goes to `cc`, and it stands HERE, beside the other edge
            // items of section E -- not above them and not away. **A named delegation is the
            // honest booking; a silent one is none**, and this line is the difference.
            //
            // It buys nothing it does not say: swapping two letters still gives a program
            // that compiles and calls wrong. *That surface is moved, never checked* -- which
            // is exactly what «B27» wanted to shrink and what this line refuses to hide.
            aus.push_str(
                "\n     REGISTER ALLOCATION -- delegated to `cc`, NOT checked here («B27»).\n\x20\
                 \x20     The `in`/`out`/`clobbers` letters are C constraint letters and reach \
                 the\n\x20      compiler unread. Swapping two of them yields a program that \
                 compiles\n\x20      and calls wrong. A named delegation, not a missing form: \
                 no pass holds\n\x20      them against a register table, because the corpus \
                 shows no demand for\n\x20      one (messung/EINTRITTSBELEGUNG.md).\n",
            );
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
    // **Die Klasse der Annahme stand in der LISTE und nicht in der BUCHUNG** (2026-08-21).
    //
    // Jede `A`-Zeile trug seit jeher `Sonde <x>` oder `NICHT FALSIFIZIERBAR -- <grund>`;
    // die Zeile darunter warf beide in einen Topf. **Eine nicht falsifizierbare Annahme ist
    // eine andere Waehrung als eine mit benannter Sonde** -- gegen die erste kann keine
    // Sonde je etwas ausrichten, und `S004` weist genau deshalb eine unfalsifizierbare
    // Fortschrittsannahme ab.
    //
    // *Dieselbe Klasse wie die Fremdverengungen: eine Zahl, in der zwei Waehrungen stecken,
    // liest sich wie eine.* Die Nachbarn der Zeile fuehren ihre Untermenge laengst mit
    // (`(N of them UNPROVED)`, `(N state their duty)`); hier fehlte sie.
    let ohne_sonde = annahmen
        .iter()
        .filter(|a| matches!(a.klasse, crate::manifest::Klasse::NichtFalsifizierbar { .. }))
        .count();
    // **And the THIRD currency, since 2026-08-30: uncovered.**
    //
    // Until today the assumptions fell into two classes and this line carried both. But an
    // assumption naming a probe that no program redeems is neither: something COULD refute
    // it, only nobody does. *Counting it among the falsifiable ones was exactly the blend
    // this line healed for the other two on 2026-08-21* -- a figure holding two currencies
    // reads like one.
    let ungedeckt = annahmen
        .iter()
        .filter(|a| match &a.klasse {
            crate::manifest::Klasse::Falsifizierbar { sonde } => !crate::manifest::gedeckt(sonde),
            _ => false,
        })
        .count();
    aus.push_str(&format!(
        "     {} assumptions ({} of them NOT FALSIFIABLE, {} UNCOVERED -- named a probe that \
         does not exist as a program), {} templates ({} of them UNPROVED), \
         {} direct forms, \
         {} foreign bodies ({} state their duty), {} narrowings from foreign contracts\n",
        annahmen.len(),
        ohne_sonde,
        ungedeckt,
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
        zaehle(&mut e, "a form nobody has entered");
        assert_eq!(e.unzugeordnet.len(), 1, "{:?}", e.unzugeordnet);
        assert!(e.posten.is_empty(), "it must not pass as counted");
    }

    /// Jede Schablone, auf die die Einordnung zeigt, muss es geben. *Eine Abhaengigkeit auf
    /// einen fehlenden Namen ist schlechter als keine — sie sieht aus wie eine gebuchte.*
    #[test]
    fn jede_genannte_schablone_gibt_es() {
        for p in EINORDNUNG {
            if let Traegt::Schablone(s) = p.traegt {
                assert!(
                    crate::schablonen::SCHABLONEN.iter().any(|x| x.name == s),
                    "`{}` points at the template `{s}` -- there is no such template",
                    p.konstrukt
                );
            }
        }
    }
}
