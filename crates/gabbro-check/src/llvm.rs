//! **Gabbro → LLVM-IR (Text), für AArch64 und x86-64.**
//!
//! Der zweite Erzeuger neben dem C-Erzeuger (`emit.rs`): aus einem GEPRÜFTEN Baum schreibt
//! diese Datei LLVM-IR als Text (`.ll`), das reine LLVM-Werkzeuge (`opt`, `llc`) übersetzen
//! und `ld.lld` statisch bindet — ohne C an jeder Stelle (kein C-Quelltext, kein
//! C-Übersetzer, keine libc, keine verlinkte Laufzeit). Der Erzeuger ist UNVERTRAUT wie
//! der C-Erzeuger: der Prüfer läuft davor (der Aufrufer prüft zuerst mit `crate::pruefe`),
//! und was hier steht, ist keine verifizierte Übersetzung, sondern ein Kandidat für die
//! spätere Übersetzungsvalidierung (Quelle → Modell → fertige Bytes, in Lean geprüft).
//!
//! ## Was hier gilt (und was nicht)
//!
//! * **Der Prüfer ist zuerst dran.** `emittiere_llvm` selbst prüft nichts nach: Bereiche,
//!   Verträge, Kosten, Sperrdisziplin und das Zielprofil hat `crate::pruefe` schon
//!   gehalten. Was der Prüfer ablehnt, erreicht diese Datei nie als grünes Programm.
//! * **Verweigert wird mit Namen.** Jede Form ohne LLVM-Absenkung bekommt eine `Y`-Kennung
//!   (`Y101`–`Y104`, `Y106`) statt einer geratenen Absenkung — dieselbe Regel wie `C001`
//!   beim C-Erzeuger. Die `Y`-Kennung nennt die Form, nicht den Grund ihres Fehlens.
//!   `Y105` ist eingezogen (Fehlerkanal vollständig gesenkt).
//! * **Keine Abhängigkeit, kein `unsafe`.** Die Datei schreibt Text; `opt`/`llc`/`ld.lld`
//!   bauen ihn. Der Arbeitsbereich bleibt bei `std` allein (wie `emit.rs`).
//! * **Kein C-Erzeuger.** Diese Datei liest `emit.rs` nie, teilt keinen Code mit ihm und
//!   ruft ihn nie auf. Wo beide dasselbe senken (Ticket-Sperre, Freigaben, Bereiche),
//!   steht die Regel hier erneut mit eigenem Grund — ein Kommentar nennt die Herkunft,
//!   kein Aufruf die Datei. Nur Gabbro → LLVM → Binary.
//!
//! ## Optimierung — Invarianten als Treibstoff
//!
//! Die Datei senkt NAIV ab (jede `let`-Bindung ein `alloca`, jede Prüfung ein Zweig) und
//! legt dem Optimierer die geprüften Tatsachen bei — Invarianten-Optimierung ist der
//! große Punkt dieser Sprache, und er steht hier:
//!
//! * **Reichweiten als Speicher:** passt ein deklarierter Bereich in eine kleinere Breite,
//!   trägt die Zelle sie (`u32`, bewiesen unter 256 Werten, liegt als `i8` — Bytes gespart,
//!   bessere Vektorisierung). Gesund, weil der Prüfer jeden Speicher an den deklarierten
//!   Bereich hält; fremde ABI (`extern`, Tore) senkt breit.
//! * **`!range` an Ladungen/Speichern** aus deklarierten Bereichen (literale Schranken).
//! * **Flache skalare TBAA** (`i16/i32/i64/f32/f64/ptr` je ein Typ; `i8`/`i1` und Aggregate
//!   tragen nichts — kein Stempeln in dieser Sprache, darum gesund ohne Zeiger-Analyse).
//! * **`noalias` an `own`-Zeigerparametern** (exklusiv laut Deklaration).
//! * **`llvm.assume` hinter jeder bestandenen Prüfung** (`narrow`) **und aus Verträgen**
//!   (`requires` am Eintritt, `ensures` an der Antwort — was sich nicht senken lässt,
//!   fällt still unter den Tisch, nie die Einheit).
//! * **Pipeline:** `opt -O3` (Middle-End) plus `llc -O3` (Codegen); `llc` allein fährt die
//!   Middle-End-Pipeline nicht (gemessen langsamer als `-O0`).
//!
//! ## Coverage and runtime
//!
//! Coverage is classified against Lean constructors and declaration fields in
//! `dokumente/llvm-modelldeckung.tsv`, checked by
//! `instrumente/pruefe-llvm-modelldeckung.py`. Examples are execution witnesses,
//! never the coverage denominator. Unsupported forms still refuse by name.
//!
//! Every cyclic direct/compatible indirect call component is lowered to a loop
//! dispatcher with explicit continuation frames (`stackless.rs`). The existing
//! tail-cycle fast path uses jumps without suspended frames. Frames live in
//! checked, growable anonymous chunks, released on unwind; native call depth
//! does not grow with source recursion. Exhausted memory fail-stops explicitly.
//!
//! Thread groups are spawned before joining. A tiny ABI-specific trampoline is
//! necessary at the SP switch; the child never resumes a parent LLVM frame.
//! Each invocation owns a mapping with control word, guard and stack. Join waits
//! for kernel clear_child_tid (after exit), then releases the complete mapping.
//! This is still the Linux runtime profile, not an OS-neutral implementation.
//!
//! Arena free links live outside payloads. Empty payload chunks can be discarded
//! without losing LIFO reuse or changing the committed-prefix model. Physical
//! residency is distinct from reservation and virtual access rights.
//!
//! ## Die Stille-Invariante (Soundness)
//!
//! `None` OHNE Absage gilt nur, wo die Ursache schon steht: tote Namen entstehen
//! ausschließlich NEBEN einer Absage. Wer hier einen neuen stillen Pfad baut, beweist
//! erst, dass seine Ursache schon steht — sonst wird aus einer fehlenden Absenkung ein
//! fehlender Aufruf im Binary (still!).
//!
//! ## Determinismus
//!
//! Alle Register sind `BTreeMap`/`BTreeSet` (gleiche Quelle, gleiche Bytes, zweimal
//! hintereinander — Zertifikate vergleichen sonst Rauschen). `%arg{i}` gibt es nicht;
//! Namen laufen in Senkordnung.

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};
use gabbro_syntax::kw::Kw;
use gabbro_syntax::span::Span;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::Write as _;

mod stackless;
mod memory;
mod masken;
mod stapeltor;
mod eintritte;
mod publizieren;
mod leser_schreiber;
mod portraum;
mod assembler;
#[cfg(test)]
mod test_tools;

// ===================================================================================
// Ziele
// ===================================================================================

/// **Ein LLVM-Ziel: Triplett plus Datenlayout, als Daten.**
#[derive(Clone, Copy)]
pub struct Ziel {
    /// Das Wort, das `gabbro llvm --target=` versteht.
    pub name: &'static str,
    /// `target triple` der `.ll`-Datei.
    pub triple: &'static str,
    /// `target datalayout` der `.ll`-Datei (LP64 auf beiden Zielen).
    pub datalayout: &'static str,
}

/// **x86-64 (LP64).** Das Layout ist das von `clang --target=x86_64-unknown-linux-gnu`
/// gemeldete (keine Handvoll).
pub const ZIEL_X86_64: Ziel = Ziel {
    name: "x86_64",
    triple: "x86_64-unknown-linux-gnu",
    datalayout: "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128",
};

/// **AArch64 (LP64, little endian).** Das Layout ist das von
/// `clang --target=aarch64-unknown-linux-gnu` gemeldete.
pub const ZIEL_AARCH64: Ziel = Ziel {
    name: "aarch64",
    triple: "aarch64-unknown-linux-gnu",
    datalayout: "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128-Fn32",
};

/// **Das `--target`-Wort zum Ziel.** Versteht `x86_64`/`amd64` und `aarch64`/`arm64`,
/// je mit und ohne Schwanz. Alles andere ist `None` — der Aufrufer meldet es.
pub fn ziel_fuer(wunsch: &str) -> Option<&'static Ziel> {
    match wunsch.to_ascii_lowercase().as_str() {
        "x86_64" | "x86-64" | "amd64" | "x86_64-linux-gnu" | "x86_64-unknown-linux-gnu" => {
            Some(&ZIEL_X86_64)
        }
        "aarch64" | "arm64" | "aarch64-linux-gnu" | "aarch64-unknown-linux-gnu" => {
            Some(&ZIEL_AARCH64)
        }
        _ => None,
    }
}

// ===================================================================================
// Kennungen
// ===================================================================================

/// **Die Verweigerung ist ein Fehler mit Satznummer.** Wie `C001` beim C-Erzeuger: lieber
/// eine benannte Absage als eine geratene Absenkung.
fn weigere(s: &mut Senke, code: &'static str, span: Span, was: String) {
    s.absagen.schiebe(
        Absage::fehler(code, span, format!("no LLVM lowering: {was}")).mit_notiz(
            "the LLVM backend (llvm.rs) refuses by name instead of emitting something \
             plausible -- like emit.rs refuses with C001. The program stays checkable; \
             it is just not translated by THIS backend (Y101 type, Y102 item, Y103 \
             statement, Y104 expression, Y106 match).",
        ),
    );
}

// ===================================================================================
// LLVM-Typen und Werte
// ===================================================================================

/// **Ein LLVM-Typ, wie ihn diese Datei schreibt.** `Benannt` ist ein `%Name`-Struct.
#[derive(Clone, PartialEq, Eq)]
enum LlTyp {
    Int(u32),
    F32,
    F64,
    Void,
    Ptr,
    Feld(Box<LlTyp>, u64),
    Anon(Vec<LlTyp>),
    Benannt(String),
}

impl LlTyp {
    fn text(&self) -> String {
        match self {
            LlTyp::Int(w) => format!("i{w}"),
            LlTyp::F32 => "float".to_string(),
            LlTyp::F64 => "double".to_string(),
            LlTyp::Void => "void".to_string(),
            LlTyp::Ptr => "ptr".to_string(),
            LlTyp::Feld(e, n) => format!("[{n} x {}]", e.text()),
            LlTyp::Anon(fs) => {
                let innen: Vec<String> = fs.iter().map(|f| f.text()).collect();
                format!("{{ {} }}", innen.join(", "))
            }
            LlTyp::Benannt(n) => format!("%{n}"),
        }
    }

    fn ist_int(&self) -> bool {
        matches!(self, LlTyp::Int(_))
    }

    fn breite(&self) -> Option<u32> {
        match self {
            LlTyp::Int(w) => Some(*w),
            _ => None,
        }
    }
}

/// **Vorzeichen eines ganzzahligen Werts** (für `/`, `>>`, Vergleiche, Erweiterung).
#[derive(Clone, Copy, PartialEq, Eq)]
enum Zeichen {
    U,
    S,
    Egal,
}

/// **Ein gesenkter Wert: Typ, Vorzeichen, Operandentext, Herkunftsform.**
#[derive(Clone)]
struct Wert {
    typ: LlTyp,
    zeichen: Zeichen,
    text: String,
    form: Option<TypExpr>,
}

impl Wert {
    fn int(text: String, w: u32, z: Zeichen) -> Wert {
        Wert { typ: LlTyp::Int(w), zeichen: z, text, form: None }
    }
}

// ===================================================================================
// Sammlerzustand
// ===================================================================================

#[derive(Clone)]
struct FnSig {
    params: Vec<(LlTyp, Zeichen)>,
    ret: Option<(LlTyp, Zeichen)>,
    ret_form: Option<TypExpr>,
    extern_: bool,
    /// Geist-Parameter (je deklarierter Stelle): Argument fällt am Ruf weg.
    geist_param: Vec<bool>,
    /// Geist-Antwort: der Ruf trägt nichts.
    geist_rueck: bool,
    /// `own`-Parameter (je gesenkter Stelle): trägt `noalias`.
    eigen_param: Vec<bool>,
    /// Fehlerkanal (`-> T or R`): Antwort ist der Kanal-Struct.
    or_nutz: Option<OrKanal>,
    /// Vertrag für `assume` (geprüfte Zusagen als Optimierer-Fakten).
    vertrag_requires: Vec<Pred>,
    vertrag_ensures: Vec<Pred>,
}

/// **Ein gesenktes Tor: alles, was der Ruf braucht.**
#[derive(Clone)]
struct Tor {
    nummer: i64,
    /// (Register, Parameterplatz), in ABI-Ordnung.
    eingaben: Vec<(String, usize)>,
    param_typen: Vec<(LlTyp, Zeichen)>,
    ret: Option<(LlTyp, Zeichen)>,
    /// `-> never`: kein Ergebnis, kein Rücksprung.
    nie: bool,
    template: &'static str,
    clobbers: Vec<String>,
    /// Austrittsregister (Antwort).
    ret_reg: &'static str,
    /// `stack r`: das Tor startet einen Faden auf dem übergebenen Stapel (`llvm/stapeltor.rs`).
    stapel: Option<stapeltor::StapelTor>,
    /// Fehlerkanal des Tors plus errno-Dekodierung (Nummer, Grundwert).
    or_nutz: Option<OrKanal>,
    errors: Vec<(i64, i32)>,
}

/// Der Plan einer Funktion nach dem Sammeldurchgang.
#[derive(Clone)]
enum FnPlan {
    /// `impl`-Funktion mit Block-Rumpf (Namen/Formen nur der gesenkten Stellen).
    Impl { rumpf: Block, params: Vec<(LlTyp, Zeichen)>, namen: Vec<String>, formen: Vec<TypExpr>, modul: String },
    /// Fertig: `extern`, compilezeitlich oder verweigert.
    Fertig { modul: String },
}

/// Ruf auflösen: eigenes Modul zuerst, voller Pfad dann, kurz zuletzt.
fn loese_fn(s: &Senke, modul: &str, p: &Pfad) -> Option<(String, FnSig)> {
    let kurz = kurzname(p);
    let k = loese_schluessel(s, modul, p)?;
    let sig = s.fns.get(&k).cloned()?;
    let emit = s.emitnamen.get(&k).cloned().unwrap_or_else(|| kurz.clone());
    Some((emit, sig))
}

/// Schlüssel hinter einem Rufpfad (für Rufgraph und Schleifenentscheidung).
fn loese_schluessel(s: &Senke, modul: &str, p: &Pfad) -> Option<String> {
    let kurz = kurzname(p);
    let voll = p.text();
    let mut kandidaten = Vec::new();
    if p.teile.len() == 1 && !modul.is_empty() {
        kandidaten.push(format!("{modul}::{kurz}"));
    }
    kandidaten.push(voll.clone());
    kandidaten.push(kurz.clone());
    for k in kandidaten {
        if s.fns.contains_key(&k) {
            return Some(k);
        }
    }
    None
}

/// Tor auflösen (gleiche Ordnung wie Funktionen).
fn loese_tor(s: &Senke, modul: &str, p: &Pfad) -> Option<(String, Tor)> {
    let kurz = kurzname(p);
    let voll = p.text();
    let mut kandidaten = Vec::new();
    if p.teile.len() == 1 && !modul.is_empty() {
        kandidaten.push(format!("{modul}::{kurz}"));
    }
    kandidaten.push(voll.clone());
    kandidaten.push(kurz.clone());
    for k in kandidaten {
        if let Some(t) = s.tore.get(&k).cloned() {
            return Some((k, t));
        }
    }
    None
}

#[derive(Clone)]
struct Global {
    typ: LlTyp,
    zeichen: Zeichen,
    form: TypExpr,
    konstant: bool,
    init_text: Option<String>,
}

/// Eine monotone Region: Element mit Form und Größe, Schranken.
#[derive(Clone)]
struct ArenaInfo {
    elem: LlTyp,
    form: TypExpr,
    groesse: u64,
    lo: u64,
    hi: u64,
    max: u64,
    sample: Option<Sample>,
}

/// **The sampling behind `pb P blw B` (commit path, never alloc path).**
///
/// UNresolved stored (path plus arena module) and resolved at use --
/// at collection time the probe often stands behind the arena.
/// Resolution reads like a call from the arena's module (short name there,
/// full path everywhere). The threshold (`blw B`, bytes, due constant)
/// is set by the user -- e.g. `blw 1048576` (1 MiB).
#[derive(Clone)]
struct Sample {
    pfad: Pfad,
    modul: String,
    schwelle: u64,
}
/// **Die Abtastung rufen (ein Ruf je Commit-Stück).** Tor zuerst (wie
/// `senke_ruf`), dann Funktion — derselbe Pfad wie jeder Nutzer-Ruf (Dual-Arch,
/// Antwortdekodierung). Das Modul steht für die Auflösung kurz auf dem der
/// Arena und geht danach zurück.
fn call_sample(k: &mut Koerper, d: &Sample, span: Span) -> Option<Wert> {
    let heim = k.modul.clone();
    k.modul = d.modul.clone();
    let w = if loese_tor(k.s, &d.modul, &d.pfad).is_some() {
        let ruf = Ruf {
            ziel: CallTarget::Path(d.pfad.clone()),
            argumente: Vec::new(),
            marken: Vec::new(),
            span,
        };
        senke_tor_ruf(k, &d.pfad, &ruf, span)
    } else {
        match loese_fn(k.s, &d.modul, &d.pfad) {
            Some((ename, sig)) => {
                if !sig.params.is_empty() {
                    weigere(k.s, "Y103", span, format!("pressure probe {} takes arguments", d.pfad.text()));
                    k.modul = heim;
                    return None;
                }
                match sig.ret.clone() {
                    Some((rt, _)) if rt != LlTyp::Void => {
                        let t = k.tmp();
                        k.zeile(&format!("{t} = call {} {}()", rt.text(), gname(&ename)));
                        Some(Wert { typ: rt.clone(), zeichen: Zeichen::U, text: t, form: None })
                    }
                    _ => {
                        weigere(k.s, "Y103", span, format!("pressure probe {} answers nothing", d.pfad.text()));
                        None
                    }
                }
            }
            None => {
                weigere(k.s, "Y103", span, format!("pressure probe {} resolves nowhere", d.pfad.text()));
                None
            }
        }
    };
    k.modul = heim;
    w
}

/// Ein Tor im Beleg: Name, Nummer, Schablone, Bindungen, Austritt, Clobbers.
#[derive(Clone)]
struct TorBeleg {
    name: String,
    nummer: i64,
    schablone: String,
    bindungen: Vec<String>,
    austritt: String,
    clobbers: Vec<String>,
}

/// **Der Beleg: Gabbro → Binary, ohne LLVM darin.** Dieselbe Senkung wie das IR —
/// ein Lauf, zwei Ausgaben. Der Validator liest Daten, keinen IR-Text.
pub struct LLVMBeleg {
    /// Ziel-Triplett (als Datum, nicht als IR-Kopf).
    pub ziel: &'static str,
    /// (Name, Parameter-Layouts, Antwort-Layout, Klasse).
    pub funktionen: Vec<(String, Vec<String>, String, String)>,
    /// (Name, Layout).
    pub typen: Vec<(String, String)>,
    /// Gesenkte Tore beim Rufernamen.
    pub tore: Vec<TorBeleg>,
    /// Eintritt: (`main`-Name, Breite oder `None` bei `never`).
    pub eintritt: Option<(String, Option<u32>)>,
    /// Angenommene Tatsachen (`narrow`-Erfolge als `assume`, Vertrags-Vergleiche).
    pub annahmen: Vec<String>,
    /// (Name, Element-Layout, Reservierung, Schranke, Decke).
    pub arenen: Vec<(String, String, u64, u64, u64)>,
    /// Ticket-Wörter beim Namen.
    pub schloesser: Vec<String>,
    /// Wurzeln (Stapel/Wörter unter `gabbro_faden_N_*`).
    pub faeden: Vec<String>,
}

impl LLVMBeleg {
    /// **Der Beleg als Lean-Datei (Kern-Syntax, kein Import).** Trägt kein IR —
    /// kein `define`, keinen `target triple`-Kopf: Verfeinerung Gabbro→Binary.
    pub fn als_lean(&self, name: &str) -> String {
        let mut aus = String::new();
        let _ = writeln!(aus, "-- LLVM-Beleg zu {name} (Kandidat, kein Beweis).");
        let _ = writeln!(aus, "def llvmEinheit : String := \"{name}\"");
        let _ = writeln!(aus, "def llvmZiel : String := \"{}\"", self.ziel);
        let _ = writeln!(aus, "def llvmLayout : String := \"lp64\"");
        let _ = writeln!(aus, "def llvmFunktionen : List (String × List String × String × String) :=");
        for (n, _, _, _) in &self.funktionen {
            let _ = writeln!(aus, "-- name := \"{n}\"");
        }
        if self.funktionen.is_empty() {
            let _ = writeln!(aus, "  []");
        } else {
            let _ = writeln!(aus, "  [");
            for (i, (n, ps, r, k)) in self.funktionen.iter().enumerate() {
                let ps_text = ps.iter().map(|p| format!("\"{p}\"")).collect::<Vec<_>>().join(", ");
                let komma = if i + 1 < self.funktionen.len() { "," } else { "" };
                let _ = writeln!(aus, "    (\"{n}\", [{ps_text}], \"{r}\", \"{k}\"){komma}");
            }
            let _ = writeln!(aus, "  ]");
        }
        let _ = writeln!(aus, "def llvmTypen : List (String × String) :=");
        if self.typen.is_empty() {
            let _ = writeln!(aus, "  []");
        } else {
            let _ = writeln!(aus, "  [");
            for (i, (n, l)) in self.typen.iter().enumerate() {
                let komma = if i + 1 < self.typen.len() { "," } else { "" };
                let _ = writeln!(aus, "    (\"{n}\", \"{l}\"){komma}");
            }
            let _ = writeln!(aus, "  ]");
        }
        let _ = writeln!(aus, "def llvmTore : List (String × Nat × String × List String × String × List String) :=");
        if self.tore.is_empty() {
            let _ = writeln!(aus, "  []");
        } else {
            let _ = writeln!(aus, "  [");
            for (i, t) in self.tore.iter().enumerate() {
                let bs = t.bindungen.iter().map(|b| format!("\"{b}\"")).collect::<Vec<_>>().join(", ");
                let cs = t.clobbers.iter().map(|c| format!("\"{c}\"")).collect::<Vec<_>>().join(", ");
                let komma = if i + 1 < self.tore.len() { "," } else { "" };
                let _ = writeln!(
                    aus,
                    "    -- name := \"{}\", nummer := {}, schablone := \"{}\"",
                    t.name, t.nummer, t.schablone
                );
                let _ = writeln!(
                    aus,
                    "    (\"{}\", {}, \"{}\", [{bs}], \"{}\", [{cs}]){komma}",
                    t.name, t.nummer, t.schablone, t.austritt
                );
            }
            let _ = writeln!(aus, "  ]");
        }
        let _ = writeln!(aus, "def llvmEintritt : Option (String × Option Nat) :=");
        match &self.eintritt {
            Some((n, w)) => {
                let w_text = match w {
                    Some(b) => format!("some {b}"),
                    None => "none".to_string(),
                };
                let _ = writeln!(aus, "  some (\"{n}\", {w_text})");
                let _ = writeln!(aus, "def llvmEintrittArt : String := \"start\"");
                let _ = writeln!(aus, "-- art := \"start\"");
            }
            None => {
                let _ = writeln!(aus, "  none");
            }
        }
        let _ = writeln!(aus, "def llvmAnnahmen : List String :=");
        if self.annahmen.is_empty() {
            let _ = writeln!(aus, "  []");
        } else {
            let _ = writeln!(aus, "  [");
            for (i, a) in self.annahmen.iter().enumerate() {
                let komma = if i + 1 < self.annahmen.len() { "," } else { "" };
                let sicher = a.replace('"', "'");
                let _ = writeln!(aus, "    \"{sicher}\"{komma}");
            }
            let _ = writeln!(aus, "  ]");
        }
        let _ = writeln!(aus, "def llvmArenen : List (String × String × Nat × Nat × Nat) :=");
        if self.arenen.is_empty() {
            let _ = writeln!(aus, "  []");
        } else {
            let _ = writeln!(aus, "  [");
            for (i, (n, e, lo, hi, m)) in self.arenen.iter().enumerate() {
                let komma = if i + 1 < self.arenen.len() { "," } else { "" };
                let _ = writeln!(aus, "    (\"{n}\", \"{e}\", {lo}, {hi}, {m}){komma}");
            }
            let _ = writeln!(aus, "  ]");
        }
        let _ = writeln!(aus, "def llvmSchloesser : List String :=");
        if self.schloesser.is_empty() {
            let _ = writeln!(aus, "  []");
        } else {
            let sch = self.schloesser.iter().map(|s| format!("\"{s}\"")).collect::<Vec<_>>().join(", ");
            let _ = writeln!(aus, "  [{sch}]");
        }
        let _ = writeln!(aus, "def llvmFaeden : List String :=");
        if self.faeden.is_empty() {
            let _ = writeln!(aus, "  []");
        } else {
            let f = self.faeden.iter().map(|s| format!("\"{s}\"")).collect::<Vec<_>>().join(", ");
            let _ = writeln!(aus, "  [{f}]");
        }
        aus
    }
}

struct Senke<'a> {
    absagen: &'a mut Absagen,
    /// Gefaltete `const`-Werte des Prüfers — EIN Register (kein zweiter Rechner).
    umg: crate::umgebung::Umgebung,
    /// Modulpfad des Items (für modulbewusste Auflösung).
    modul: String,
    /// Deklarierte, aber nicht gesenkte Namen (Ursache steht am Item).
    tote_items: BTreeSet<String>,
    ziel: &'static Ziel,
    kopf: String,
    rumpf: String,
    /// Umrissene Helfer (eigene Funktionen).
    helfer: String,
    typedefs: BTreeSet<String>,
    fns: BTreeMap<String, FnSig>,
    /// Gesenkte Tore beim Rufernamen.
    tore: BTreeMap<String, Tor>,
    /// Tore für ein ANDERES Ziel (still übersprungen; der Ruf nennt sie).
    fremde_tore: BTreeSet<String>,
    /// Eintritt für `_start`: (Name, Breite oder `None` bei `never`).
    eintritt: Option<(String, Option<u32>)>,
    plaene: BTreeMap<String, FnPlan>,
    globale: BTreeMap<String, Global>,
    global_align: BTreeMap<String, u64>,
    aliase: BTreeMap<String, TypExpr>,
    rekorde: BTreeMap<String, Vec<(String, TypExpr)>>,
    varianten: BTreeMap<String, (String, Option<TypExpr>)>,
    variant_typen: BTreeMap<String, (Vec<(String, Option<TypExpr>)>, u64)>,
    gruende: BTreeMap<String, Vec<(String, i128)>>,
    schloesser: BTreeMap<String, bool>,
    /// Sperren mit `masks irqs` (`llvm/masken.rs`: Zustand sichern, maskieren, zurücknehmen).
    maskiert: BTreeSet<String>,
    /// Stapeltore und ausgelagerte Kindregionen (`llvm/stapeltor.rs`).
    kind: stapeltor::SenkeZustand,
    /// Aufgenommene `entry`-Deklarationen und ob welche geschrieben wurden (`llvm/eintritte.rs`).
    eintritte: Vec<eintritte::Plan>,
    mit_eintritt: bool,
    atomare: BTreeMap<String, (LlTyp, String)>,
    tabellen: BTreeMap<String, (u64, String)>,
    geister: BTreeSet<String>,
    /// Geräte (Register am Versatz) plus Transitionen (Name → Gerät, Schritte).
    geraete: BTreeMap<String, Vec<DevReg>>,
    transitionen: BTreeMap<String, (String, Vec<(String, String, i128, i128)>)>,
    /// Gleitkomma-Konstanten (Name → Bits, `true` = f32).
    gkonst: BTreeMap<String, (u64, bool)>,
    arenen: BTreeMap<String, ArenaInfo>,
    braucht_assume: bool,
    /// The loud trap of `falle` is the generic `llvm.trap` intrinsic (no ISA instruction).
    braucht_trap: bool,
    braucht_fabs: bool,
    beleg_typen: Vec<(String, String)>,
    beleg_annahmen: Vec<String>,
    beleg_tore: Vec<TorBeleg>,
    beleg_funktionen: Vec<(String, Vec<String>, String, String)>,
    nebenlaeufig: Vec<String>,
    start_wurzeln: BTreeSet<String>,
    /// Rufer-Name je Vollname (Kollision → `m_f`, sonst kurz).
    emitnamen: BTreeMap<String, String>,
    /// Schleifenplan je Zyklus-Mitglied (Vollname → Info).
    rek: BTreeMap<String, RekInfo>,
    /// Slot-Felder je Tabelle (für Layout und Zugriffe).
    tab_slots: BTreeMap<String, Vec<(String, TypExpr)>>,
    /// Baumkanten je Tabelle (Vater, Kind, Geschwister — `tree { … }`).
    tab_baeume: BTreeMap<String, (Option<String>, Option<String>, Option<String>)>,
    /// Formate (gepackte Verbunde — keine Füllbytes zwischen Feldern).
    formate: BTreeSet<String>,
    /// Tabellen mit `ops`: (Belegungsfeld, Elternfeld, erzeugte Wörter).
    tab_ops: BTreeMap<String, (String, Option<String>, Vec<String>)>,
    /// Bereich, den eine `forall`-Invariante einem Tabellenfeld gibt: (Tabelle, Feld) → (lo, hi) inklusiv.
    inv_range: BTreeMap<(String, String), (i128, i128)>,
    /// Struct-Pfad-TBAA: (Struct, Feld) → Knotennummer.
    tbaa_pfad: BTreeMap<(String, String), u32>,
    /// Struct-Knoten je Structname.
    tbaa_struct: BTreeMap<String, u32>,
    /// Zugriffs-Tags je Typknoten (`!{!td, !td, i64 0}`).
    tbaa_tags: BTreeMap<String, u32>,
    meta_knoten: BTreeMap<u32, String>,
    meta_nr: u32,
    /// Verengungs-Modus: `true` senkt Speicher nach bewiesener Reichweite
    /// (`verenge_form`); fremd (`extern`, Tore) senkt breit (fremde ABI).
    eng_modus: bool,
    /// Qualified names of the functions whose WRITABLE pointer parameters carry `noalias`
    /// beyond `own` (`noalias_innen`).
    noalias_innen: BTreeSet<String>,
    /// Facts handed to LLVM, counted per kind (`nuw`, `nsw`, `inbounds`, `nounwind`, ...).
    /// Written as `; gabbro-fact KIND N` lines at the end of the IR.
    fakten: BTreeMap<&'static str, u64>,
    /// `asm`-Rümpfe (Vollname → fertige Funktion, `llvm/assembler.rs`).
    asm_defs: BTreeMap<String, assembler::Def>,
    /// `asm`-Rümpfe für die andere Maschine (Vollname → Kurzname, Maschine, Stelle).
    fremde_asm: BTreeMap<String, (String, String, Span)>,
}

impl Senke<'_> {
    /// Book one fact handed to LLVM (kind counted, see `fakten`).
    fn fakt(&mut self, art: &'static str) {
        *self.fakten.entry(art).or_insert(0) += 1;
    }
}

fn gname(n: &str) -> String {
    format!("@\"{}\"", n.replace('"', ""))
}


/// Global-Teil (`M` + `bereit` → `@"M.bereit"` — Punkt IN den Anführungen).
fn gteil(n: &str, teil: &str) -> String {
    gname(&format!("{n}.{teil}"))
}

/// Kurzer Rufname: letztes Pfadsegment (`m::f` → `f`).
fn kurzname(p: &Pfad) -> String {
    p.teile.last().map(|i| i.text.clone()).unwrap_or_else(|| p.text())
}

/// **Wort → (Breite, Vorzeichen).**
fn int_wort(w: Kw) -> Option<(u32, Zeichen)> {
    match w.text() {
        "u8" => Some((8, Zeichen::U)),
        "u16" => Some((16, Zeichen::U)),
        "u32" => Some((32, Zeichen::U)),
        "u64" => Some((64, Zeichen::U)),
        "i8" => Some((8, Zeichen::S)),
        "i16" => Some((16, Zeichen::S)),
        "i32" => Some((32, Zeichen::S)),
        "i64" => Some((64, Zeichen::S)),
        _ => None,
    }
}

/// **Umwandlungsname (`u32(x)` …) → Ziel.**
fn wandel_wort(n: &str) -> Option<(LlTyp, Zeichen)> {
    match n {
        "u8" => Some((LlTyp::Int(8), Zeichen::U)),
        "u16" => Some((LlTyp::Int(16), Zeichen::U)),
        "u32" => Some((LlTyp::Int(32), Zeichen::U)),
        "u64" => Some((LlTyp::Int(64), Zeichen::U)),
        "i8" => Some((LlTyp::Int(8), Zeichen::S)),
        "i16" => Some((LlTyp::Int(16), Zeichen::S)),
        "i32" => Some((LlTyp::Int(32), Zeichen::S)),
        "i64" => Some((LlTyp::Int(64), Zeichen::S)),
        "bool" => Some((LlTyp::Int(1), Zeichen::Egal)),
        "f32" => Some((LlTyp::F32, Zeichen::Egal)),
        "f64" => Some((LlTyp::F64, Zeichen::Egal)),
        _ => None,
    }
}

/// Umwandlungsname mit Zucker (`u13` → Speicherwort `u16`).
fn wandel_mit_zucker(n: &str) -> Option<(LlTyp, Zeichen)> {
    if let Some(x) = wandel_wort(n) {
        return Some(x);
    }
    let speicher = gabbro_syntax::parse::zucker_speicher(n)?;
    int_wort(speicher).map(|(w, z)| (LlTyp::Int(w), z))
}

/// Die deklarierte Form hinter einem Umwandlungsnamen.
fn wandel_form(n: &str) -> Option<TypExpr> {
    let nix = Span::neu(0, 0);
    let wort = match n {
        "u8" => Kw::U8,
        "u16" => Kw::U16,
        "u32" => Kw::U32,
        "u64" => Kw::U64,
        "i8" => Kw::I8,
        "i16" => Kw::I16,
        "i32" => Kw::I32,
        "i64" => Kw::I64,
        "f32" => return Some(TypExpr::Float(FloatTy { wort: Kw::F32, bereich: None, span: nix })),
        "f64" => return Some(TypExpr::Float(FloatTy { wort: Kw::F64, bereich: None, span: nix })),
        "bool" => return Some(TypExpr::Bool(nix)),
        _ => return None,
    };
    Some(TypExpr::Int(IntTy { wort, zucker: None, bereich: None, span: nix }))
}

/// Alias-auflösende Grundform (Geister vererben nicht — hier nur Namen).
fn grundform(s: &Senke, t: &TypExpr) -> TypExpr {
    match t {
        TypExpr::Pfad(p) => {
            if let Some(einfach) = p.einfach() {
                if let Some(seite) = s.aliase.get(&einfach.text).cloned() {
                    return grundform(s, &seite);
                }
            }
            t.clone()
        }
        _ => t.clone(),
    }
}

/// Literale Bereichsschranken (modulunabhängig — nur Zahlen, keine Namen).
fn bereich_literal(b: &Bereich) -> Option<(i128, i128, bool)> {
    fn zahl(e: &Expr) -> Option<i128> {
        match &e.art {
            ExprArt::Zahl(v) => i128::try_from(*v).ok(),
            ExprArt::Klammer(x) => zahl(x),
            ExprArt::Unaer(UnOp::Negativ, x) => zahl(x).map(|v| -v),
            _ => None,
        }
    }
    Some((zahl(&b.von)?, zahl(&b.bis)?, b.exklusiv))
}

/// Bereichsschranken mit Konstanten (benannte Schranken faltet der Prüfer-Register).
fn bereich_grenzen(s: &Senke, b: &Bereich) -> Option<(i128, i128, bool)> {
    fn zahl(s: &Senke, e: &Expr) -> Option<i128> {
        match &e.art {
            ExprArt::Zahl(v) => i128::try_from(*v).ok(),
            ExprArt::Klammer(x) => zahl(s, x),
            ExprArt::Unaer(UnOp::Negativ, x) => zahl(s, x).map(|v| -v),
            ExprArt::Ort(o) if o.suffixe.is_empty() => s.umg.konst_wert(&s.modul, e),
            _ => None,
        }
    }
    Some((zahl(s, &b.von)?, zahl(s, &b.bis)?, b.exklusiv))
}

/// Faltungs-Konstante als `u64` (Längen, Nummern, Schranken — EIN Register).
fn konst_u64(s: &Senke, e: &Expr) -> Option<u64> {
    let v = s.umg.konst_wert(&s.modul, e)?;
    u64::try_from(v).ok()
}

/// Byte-Größe eines gesenkten Typs (Varianten-Polster, Arenenzellen).
fn groesse_von_typ(s: &mut Senke, t: &TypExpr) -> Option<u64> {
    let (ll, _) = senke_typ(s, t)?;
    groesse_von_ll(s, &ll)
}

fn groesse_von_ll(s: &Senke, ll: &LlTyp) -> Option<u64> {
    stackless::layout(&ll.text(), &s.beleg_typen).map(|(size, _)| size)
}

/// Statische Größe ohne Layout-Rückgriff (keine Rekursion in `sorge_*`).
fn groesse_statisch(s: &Senke, t: &TypExpr, eng: bool) -> Option<u64> {
    let t2 = if eng { verenge_form(s, t) } else { t.clone() };
    match grundform(s, &t2) {
        TypExpr::Int(i) => Some(int_wort(i.wort)?.0 as u64 / 8),
        TypExpr::Float(_) => Some(8),
        TypExpr::Bool(_) => Some(1),
        TypExpr::Never(_) => Some(0),
        TypExpr::Zeiger(_) => Some(8),
        TypExpr::FnZeiger(_) => Some(8),
        TypExpr::Index { optional, .. } => Some(if optional { 12 } else { 4 }),
        TypExpr::Feld(a) => {
            let n = s.umg.konst_wert(&s.modul, &a.laenge).and_then(|v| u64::try_from(v).ok())?;
            Some(groesse_statisch(s, &a.element, eng)?.checked_mul(n)?)
        }
        TypExpr::Verbund(fs, _) => {
            let mut sum = 0u64;
            for f in &fs {
                sum = sum.checked_add(groesse_statisch(s, &f.typ.typ, eng)?)?;
            }
            Some(sum)
        }
        TypExpr::Zeichenkette { max, .. } => Some(4 + u64::try_from(max).ok()?),
        TypExpr::Pfad(p) => {
            if let Some(einfach) = p.einfach() {
                let n = &einfach.text;
                if s.tabellen.contains_key(n) {
                    return Some(8);
                }
                // Rekorde/Varianten: Namen auflösen, Rekursion abbrechen.
                if let Some(felder) = s.rekorde.get(n).cloned() {
                    let mut sum = 0u64;
                    for (_, ft) in &felder {
                        sum = sum.checked_add(groesse_statisch(s, ft, eng)?)?;
                    }
                    return Some(sum);
                }
                if let Some((faelle, _)) = s.variant_typen.get(n).cloned() {
                    let mut groesste = 0u64;
                    for (_, nt) in &faelle {
                        if let Some(nt) = nt {
                            groesste = groesste.max(groesse_statisch(s, nt, eng)?);
                        }
                    }
                    return Some(4 + groesste);
                }
            }
            None
        }
        TypExpr::Varianten(_, _) => None,
    }
}

// ===================================================================================
// Typabsenkung (mit Reichweiten-Verengung)
// ===================================================================================

/// Reichweiten-verengte Form: passt der deklarierte Bereich in eine kleinere Breite,
/// trägt die Form sie (Beispiel: `u32`, bewiesen unter 256 Werten, liegt als `i8`).
/// Gesund, weil der Prüfer jeden Speicher an den DEKLARIERTEN Bereich hält und die
/// verengte Breite ihn ganz deckt. Nur literale Schranken; Vorzeichen bleibt.
fn verenge_form(s: &Senke, t: &TypExpr) -> TypExpr {
    let t = grundform(s, t);
    match &t {
        TypExpr::Int(i) => {
            let (w0, z) = match int_wort(i.wort) {
                Some(x) => x,
                None => return t.clone(),
            };
            let (lo, hi, exklusiv) = match i.bereich.as_ref().and_then(|b| bereich_grenzen(s, b)) {
                Some(x) => x,
                None => return t.clone(),
            };
            let hi_inkl = if exklusiv { hi - 1 } else { hi };
            let neu = match z {
                Zeichen::U => {
                    if lo < 0 {
                        None
                    } else if hi_inkl <= 255 {
                        Some(Kw::U8)
                    } else if hi_inkl <= 65535 {
                        Some(Kw::U16)
                    } else if hi_inkl <= 4294967295 {
                        Some(Kw::U32)
                    } else {
                        None
                    }
                }
                _ => {
                    if lo >= -128 && hi_inkl <= 127 {
                        Some(Kw::I8)
                    } else if lo >= -32768 && hi_inkl <= 32767 {
                        Some(Kw::I16)
                    } else if lo >= -2147483648 && hi_inkl <= 2147483647 {
                        Some(Kw::I32)
                    } else {
                        None
                    }
                }
            };
            match neu {
                Some(wort) if int_wort(wort).is_some_and(|(w, _)| w < w0) => TypExpr::Int(IntTy {
                    wort,
                    zucker: None,
                    bereich: i.bereich.clone(),
                    span: i.span,
                }),
                _ => t.clone(),
            }
        }
        TypExpr::Feld(_) => t.clone(),
        TypExpr::Verbund(_, _) => t.clone(),
        _ => t.clone(),
    }
}

/// Layout-Name je Modus: eng wie erklärt, breit mit `$breit`-Schwanz (fremde ABI).
fn layout_name(n: &str, eng: bool) -> String {
    if eng {
        n.to_string()
    } else {
        format!("{n}$breit")
    }
}

fn senke_typ(s: &mut Senke, t: &TypExpr) -> Option<(LlTyp, Zeichen)> {
    let t = if s.eng_modus { verenge_form(s, t) } else { t.clone() };
    senke_typ_roh(s, &t)
}

/// Gerätezeiger hinter einer Form (flüchtiger Zugriff — kein Optimierer-Cache).
fn ist_fluechtig(s: &Senke, form: &Option<TypExpr>) -> bool {
    match form.clone().map(|f| grundform(s, &f)) {
        Some(TypExpr::Zeiger(z)) => !matches!(z.raum, Raum::Normal),
        _ => false,
    }
}

/// Options-Layout (`{i32 Tag, [8 x i8]}` — einmal je Einheit).
fn sorge_gabopt(s: &mut Senke) {
    if s.typedefs.insert("gabopt".to_string()) {
        let layout = "{ i32, [8 x i8] }".to_string();
        let _ = writeln!(s.kopf, "%gabopt = type {layout}");
        s.beleg_typen.push(("gabopt".to_string(), layout));
    }
}

/// `own`-Zeiger hinter einer Form (exklusiv laut Deklaration).
fn ist_eigen(s: &Senke, t: &TypExpr) -> bool {
    match grundform(s, t) {
        TypExpr::Zeiger(z) => z.rechte.iter().any(|r| matches!(r, Recht::Eigen(_))),
        _ => false,
    }
}

fn senke_typ_roh(s: &mut Senke, t: &TypExpr) -> Option<(LlTyp, Zeichen)> {
    match t {
        TypExpr::Int(i) => int_wort(i.wort).map(|(w, z)| (LlTyp::Int(w), z)),
        TypExpr::Float(f) => match f.wort.text() {
            "f32" => Some((LlTyp::F32, Zeichen::Egal)),
            "f64" => Some((LlTyp::F64, Zeichen::Egal)),
            _ => {
                weigere(s, "Y101", f.span, format!("float word {}", f.wort.text()));
                None
            }
        },
        TypExpr::Bool(_) => Some((LlTyp::Int(1), Zeichen::Egal)),
        TypExpr::Never(_) => Some((LlTyp::Void, Zeichen::Egal)),
        TypExpr::Zeiger(_) => Some((LlTyp::Ptr, Zeichen::Egal)),
        TypExpr::Index { optional, .. } => {
            if *optional {
                sorge_gabopt(s);
                Some((LlTyp::Benannt("gabopt".to_string()), Zeichen::Egal))
            } else {
                Some((LlTyp::Int(32), Zeichen::U))
            }
        }
        TypExpr::Pfad(p) => {
            if let Some(einfach) = p.einfach() {
                let n = einfach.text.clone();
                if let Some(seite) = s.aliase.get(&n).cloned() {
                    return senke_typ_roh(s, &seite);
                }
                if s.geister.contains(&n) {
                    // Geister löschen sich (kein Laufzeitwert).
                    return Some((LlTyp::Int(8), Zeichen::Egal));
                }
                if s.rekorde.contains_key(&n) {
                    // Layouts immer breit (Verengung nur für skalare Zellen —
                    // sonst trüge jeder Ruf eine Wandlung).
                    sorge_typdef(s, &n, false);
                    let lname = layout_name(&n, false);
                    if !s.typedefs.contains(&lname) {
                        weigere(s, "Y101", p.span, format!("record {n} without layout"));
                        return None;
                    }
                    return Some((LlTyp::Benannt(lname), Zeichen::Egal));
                }
                if s.variant_typen.contains_key(&n) {
                    sorge_variante(s, &n, false);
                    let lname = layout_name(&n, false);
                    if !s.typedefs.contains(&lname) {
                        weigere(s, "Y101", p.span, format!("variant {n} without layout"));
                        return None;
                    }
                    return Some((LlTyp::Benannt(lname), Zeichen::Egal));
                }
                if s.tabellen.contains_key(&n) {
                    // Tabelle als Wert: ihre Adresse.
                    return Some((LlTyp::Ptr, Zeichen::Egal));
                }
                if s.gruende.contains_key(&n) {
                    // Grundwerte fließen als i32 (Fallwerte aus der Deklaration).
                    return Some((LlTyp::Int(32), Zeichen::S));
                }
                if s.geraete.contains_key(&n) {
                    // Ein Gerät als WERT ist sein Griff (Basisadresse als Zahl).
                    return Some((LlTyp::Int(64), Zeichen::U));
                }
                if s.arenen.contains_key(&n) {
                    return Some((LlTyp::Ptr, Zeichen::Egal));
                }
            }
            weigere(s, "Y101", p.span, format!("named type {}", p.text()));
            None
        }
        TypExpr::Feld(a) => {
            let n = konst_u64(s, &a.laenge)?;
            let (e, _) = senke_typ_roh(s, &a.element)?;
            match e {
                LlTyp::Int(_) | LlTyp::F32 | LlTyp::F64 | LlTyp::Ptr | LlTyp::Benannt(_)
                | LlTyp::Anon(_) | LlTyp::Feld(_, _) => {
                    Some((LlTyp::Feld(Box::new(e), n), Zeichen::Egal))
                }
                LlTyp::Void => {
                    weigere(s, "Y101", a.span, "array of void".to_string());
                    None
                }
            }
        }
        TypExpr::Verbund(fs, _) => {
            let mut out = Vec::new();
            for f in fs {
                if f.bitpos.is_some()
                    || f.bedingung.is_some()
                    || f.typ.embeds.is_some()
                    || f.typ.scale.is_some()
                {
                    weigere(
                        s,
                        "Y101",
                        f.span,
                        format!("record field {} with bit position, condition or scaling", f.name.text),
                    );
                    return None;
                }
                let (t, _) = senke_typ_roh(s, &f.typ.typ)?;
                out.push(t);
            }
            Some((LlTyp::Anon(out), Zeichen::Egal))
        }
        TypExpr::Varianten(_, span) => {
            weigere(s, "Y101", *span, "anonymous variant type".to_string());
            None
        }
        TypExpr::Zeichenkette { max, .. } => {
            let n = match u64::try_from(*max) {
                Ok(v) => v,
                Err(_) => {
                    weigere(s, "Y101", t.span(), "string of this length".to_string());
                    return None;
                }
            };
            let name = format!("gabstr{n}");
            if s.typedefs.insert(name.clone()) {
                let layout = format!("{{ i32, [{n} x i8] }}");
                let _ = writeln!(s.kopf, "%{name} = type {layout}");
                s.beleg_typen.push((name.clone(), layout));
            }
            Some((LlTyp::Benannt(name), Zeichen::Egal))
        }
        TypExpr::FnZeiger(_) => Some((LlTyp::Ptr, Zeichen::Egal)),
    }
}

/// `%Name = type { … }` einmal je Modus in den Kopf.
fn sorge_typdef(s: &mut Senke, name: &str, eng: bool) {
    let lname = layout_name(name, eng);
    if s.typedefs.contains(&lname) {
        return;
    }
    let felder = match s.rekorde.get(name).cloned() {
        Some(f) => f,
        None => return,
    };
    s.typedefs.insert(lname.clone());
    let alt = s.eng_modus;
    s.eng_modus = eng;
    let mut teile = Vec::new();
    let mut ok = true;
    for (_, ft) in &felder {
        match senke_typ(s, ft) {
            Some((t, _)) => teile.push(t.text()),
            None => {
                ok = false;
                break;
            }
        }
    }
    s.eng_modus = alt;
    if !ok {
        return;
    }
    // Formate liegen gepackt (Versätze aus der Deklaration, keine Füllbytes).
    let layout = if s.formate.contains(name) {
        format!("<{{ {} }}>", teile.join(", "))
    } else {
        format!("{{ {} }}", teile.join(", "))
    };
    let _ = writeln!(s.kopf, "%{lname} = type {layout}");
    s.beleg_typen.push((lname, layout));
}

/// Varianten-Layout faul je Modus (`{i32 Marke, [P x i8]}` oder `{i32}`).
fn sorge_variante(s: &mut Senke, tname: &str, eng: bool) {
    let lname = layout_name(tname, eng);
    if s.typedefs.contains(&lname) {
        return;
    }
    let (faelle, _) = match s.variant_typen.get(tname).cloned() {
        Some(x) => x,
        None => return,
    };
    s.typedefs.insert(lname.clone());
    let alt = s.eng_modus;
    s.eng_modus = eng;
    let mut groesste = 0u64;
    let mut ok = true;
    for (_, nl) in &faelle {
        if let Some(nt) = nl {
            match groesse_von_typ(s, nt) {
                Some(n) => groesste = groesste.max(n),
                None => {
                    ok = false;
                    break;
                }
            }
        }
    }
    s.eng_modus = alt;
    if !ok {
        return;
    }
    if let Some(e) = s.variant_typen.get_mut(tname) {
        e.1 = groesste;
    }
    let layout = if groesste == 0 {
        "{ i32 }".to_string()
    } else {
        format!("{{ i32, [{groesste} x i8] }}")
    };
    let _ = writeln!(s.kopf, "%{lname} = type {layout}");
    s.beleg_typen.push((lname, layout));
}

// ===================================================================================
// Metadaten (Optimierungstreibstoff aus geprüften Tatsachen)
// ===================================================================================

/// Die darstellbaren Grenzen einer `iN`-Zelle als `[lo, hi)`.
fn typ_grenzen(w: u32, z: Zeichen) -> (i128, i128) {
    let voll: i128 = 1i128 << w.min(126);
    match z {
        Zeichen::S => (-(voll / 2), voll / 2),
        _ => (0, voll),
    }
}

/// Bereichs-Knoten (`!range`): `[lo, hi)` als iN-Paar, Nummer bei Erstgebrauch.
/// Volle Breite oder leer heißt: keine Information (kein Knoten).
fn range_knoten(s: &mut Senke, breite: u32, lo: i128, hi_exklusiv: i128) -> Option<u32> {
    if breite == 1 || breite > 64 {
        return None;
    }
    let voll: i128 = 1i128 << breite;
    let lo_n = lo.rem_euclid(voll);
    let hi_n = hi_exklusiv.rem_euclid(voll + 1);
    if lo_n == 0 && hi_n >= voll {
        return None;
    }
    if lo_n >= hi_n {
        return None;
    }
    let def = format!("!{{i{breite} {lo_n}, i{breite} {hi_n}}}");
    for (nr, d) in s.meta_knoten.iter() {
        if d == &def {
            return Some(*nr);
        }
    }
    let nr = s.meta_nr;
    s.meta_nr += 1;
    s.meta_knoten.insert(nr, def);
    Some(nr)
}

/// TBAA-Knoten (flache Skalar-Hierarchie — gesund ohne Zeiger-Analyse).
/// `i8`/`i1` und Aggregate tragen NICHTS.
fn tbaa_knoten(s: &mut Senke, t: &LlTyp) -> Option<u32> {
    let name: &str = match t {
        LlTyp::Int(8) | LlTyp::Int(1) => return None,
        LlTyp::Int(16) => "gabbro-i16",
        LlTyp::Int(32) => "gabbro-i32",
        LlTyp::Int(64) => "gabbro-i64",
        LlTyp::F32 => "gabbro-f32",
        LlTyp::F64 => "gabbro-f64",
        LlTyp::Ptr => "gabbro-ptr",
        _ => return None,
    };
    let wurzel_nr = tbaa_wurzel(s);
    // „omnipotent char" dazwischen: ungestempelte Bytes dürfen alles überlagern.
    let omni_def = format!("!{{!\"omnipotent char\", !{wurzel_nr}, i64 0}}");
    let omni_nr = match s.meta_knoten.iter().find(|(_, d)| **d == omni_def) {
        Some((nr, _)) => *nr,
        None => {
            let nr = s.meta_nr;
            s.meta_nr += 1;
            s.meta_knoten.insert(nr, omni_def.clone());
            nr
        }
    };
    let def = format!("!{{!\"{name}\", !{omni_nr}, i64 0}}");
    for (nr, d) in s.meta_knoten.iter() {
        if d == &def {
            return Some(*nr);
        }
    }
    let nr = s.meta_nr;
    s.meta_nr += 1;
    s.meta_knoten.insert(nr, def);
    Some(nr)
}

/// Zugriffs-Metadaten: `!range` (nur Ladungen — Speicher tragen keins) aus dem
/// deklarierten Bereich, `!tbaa` für Skalare. Beides gesund, beides belegt.
fn zugriff_meta(
    k: &mut Koerper,
    ll: &LlTyp,
    form: &Option<TypExpr>,
    ladung: bool,
    slot: &Option<(String, String)>,
    rekord: &Option<(String, String)>,
    zeichen: Zeichen,
) -> String {
    let mut meta = String::new();
    if ladung {
        if let LlTyp::Int(w) = ll {
            // Der engere der beiden Bereiche: erklärter Typ und `forall`-Invariante.
            let mut grenzen: Option<(i128, i128)> = None;
            if let Some(f) = form {
                if let TypExpr::Int(i) = grundform(k.s, f) {
                    if let Some(b) = &i.bereich {
                        if let Some((lo, hi, exklusiv)) = bereich_literal(b) {
                            let hi_ex = if exklusiv { hi } else { hi + 1 };
                            grenzen = Some((lo, hi_ex));
                        }
                    }
                }
            }
            if let Some(sf) = slot {
                if let Some((lo, hi)) = k.s.inv_range.get(sf).copied() {
                    // Offene Schranken an die Typgrenzen legen (`MIN`/`MAX` sind keine Werte).
                    let (typ_lo, typ_hi_ex) = typ_grenzen(*w, zeichen);
                    let lo = lo.max(typ_lo);
                    let hi_ex = if hi == i128::MAX { typ_hi_ex } else { (hi + 1).min(typ_hi_ex) };
                    if lo < hi_ex {
                        grenzen = Some(match grenzen {
                            Some((l, h)) => (l.max(lo), h.min(hi_ex)),
                            None => (lo, hi_ex),
                        });
                    }
                }
            }
            if let Some((lo, hi_ex)) = grenzen {
                if let Some(nr) = range_knoten(k.s, *w, lo, hi_ex) {
                    meta.push_str(&format!(", !range !{nr}"));
                }
            }
        }
    }
    // Struct-Pfad-TBAA, wo das Feld bekannt ist (sonst flach-skalar).
    let mut gesetzt = false;
    if let Some((struktur, feld)) = slot.as_ref().map(|(t, f)| (format!("{t}$slot"), f.clone())).or_else(|| rekord.clone()) {
        if let Some(off) = feld_versatz(k.s, &struktur, &feld, false) {
            if let Some(tag) = tbaa_feld_tag(k.s, &struktur, &feld, ll, off) {
                meta.push_str(&format!(", !tbaa !{tag}"));
                gesetzt = true;
            }
        }
    }
    if !gesetzt {
        if let Some(td) = tbaa_knoten(k.s, ll) {
            let tag = tbaa_tag(k.s, td);
            meta.push_str(&format!(", !tbaa !{tag}"));
        }
    }
    meta
}

// ===================================================================================
// Funktionskörper: Zähler, Bereiche, Zeilen
// ===================================================================================

/// Eine Bindung: Adresse plus Zugriffstyp (Ladung/Speicher wandeln an der Grenze).
#[derive(Clone)]
struct Bindung {
    ptr: String,
    ll: LlTyp,
    zeichen: Zeichen,
    form: Option<TypExpr>,
    fluechtig: bool,
}

/// Schleifenkontext für `leave`/`next` (Marke: Binder oder Schleifenname).
#[derive(Clone)]
struct SchleifenKontext {
    weiter: String,
    danach: String,
    marke: Option<String>,
    /// Locks held when the loop was entered: `leave`/`next` release only those taken inside.
    sperr_tiefe: usize,
}

/// Passende Marke von innen suchen (`leave i` trifft den Binder).
fn schleife_fuer(schleifen: &[SchleifenKontext], name: &str) -> Option<SchleifenKontext> {
    schleifen.iter().rev().find(|c| c.marke.as_deref() == Some(name)).cloned()
}

struct Koerper<'s, 'a> {
    s: &'s mut Senke<'a>,
    text: String,
    allocas: String,
    zaehler: u32,
    bloecke: u32,
    bereiche: Vec<HashMap<String, Bindung>>,
    funktionsname: String,
    gegenwart: String,
    rueck: Option<(LlTyp, Zeichen)>,
    beendet: bool,
    schleifen: Vec<SchleifenKontext>,
    sperren: Vec<String>,
    /// Stapelzellen der gesicherten Unterbrechungsmaske je maskierender Sperre (`llvm/masken.rs`).
    maske_zellen: BTreeMap<String, String>,
    /// Paarung Rufstelle/`child`-Region dieser Funktion (`llvm/stapeltor.rs`).
    kind: stapeltor::Zustand,
    alt_wert: Option<Wert>,
    ergebnis_wert: Option<Wert>,
    /// Fehlerkanal der laufenden Funktion (Rückgaben wickeln ein).
    or_nutz: Option<OrKanal>,
    /// Modul der laufenden Funktion (Rufe lösen modulnah auf).
    modul: String,
    /// Geist-Antwort der laufenden Funktion (`return x` kehrt leer zurück).
    geist_rueck: bool,
    /// Tausch-Rumpf: `return` liefert neu (Speicher, Typ, Fortsetzung).
    tausch_rueck: Option<(String, LlTyp, String)>,
    /// Schleife der laufenden Funktion (Schwanzrufe springen statt zu rufen).
    rek: Option<RekKontext>,
    /// Tiefe der `locks`-Stapelung (Freigabe an jedem Ausgang).
    sperrtiefe: u32,
}

impl<'s, 'a> Koerper<'s, 'a> {
    fn tmp(&mut self) -> String {
        let n = self.zaehler;
        self.zaehler += 1;
        format!("%t{n}")
    }

    fn block(&mut self, stamm: &str) -> String {
        let n = self.bloecke;
        self.bloecke += 1;
        format!("{stamm}_{n}")
    }

    fn zeile(&mut self, z: &str) {
        if !self.beendet {
            let _ = writeln!(self.text, "  {z}");
        }
    }

    fn alloca(&mut self, t: &str) -> String {
        let n = self.zaehler;
        self.zaehler += 1;
        let p = format!("%a{n}");
        let _ = writeln!(self.allocas, "  {p} = alloca {t}, align 8");
        p
    }

    fn suche(&self, name: &str) -> Option<Bindung> {
        for b in self.bereiche.iter().rev() {
            if let Some(x) = b.get(name) {
                return Some(x.clone());
            }
        }
        None
    }

    fn lege_an(&mut self, name: String, b: Bindung) {
        if let Some(top) = self.bereiche.last_mut() {
            top.insert(name, b);
        }
    }

    fn oeffne(&mut self) {
        self.bereiche.push(HashMap::new());
    }

    fn schliesse(&mut self) {
        self.bereiche.pop();
    }
}

/// Natürliche Ausrichung eines Zugriffstyps.
fn nat_align(ll: &LlTyp) -> u32 {
    match ll {
        LlTyp::Int(w) => (*w / 8).clamp(1, 8),
        LlTyp::F32 => 4,
        LlTyp::F64 => 8,
        LlTyp::Ptr => 8,
        LlTyp::Void => 1,
        LlTyp::Feld(e, _) => nat_align(e),
        LlTyp::Anon(fs) => fs.iter().map(nat_align).max().unwrap_or(1),
        // Named layouts include packed formats and 4-aligned options/records.
        // The access type alone cannot promise eight-byte address alignment.
        LlTyp::Benannt(_) => 1,
    }
}

/// Ganzzahl in Zielbreite falten (Zweierkomplement wie die Maschine).
fn falte_int(v: i128, breite: u32) -> String {
    if breite >= 128 {
        return format!("{v}");
    }
    let voll: i128 = 1i128 << breite;
    let n = v.rem_euclid(voll);
    // LLVM will das vorzeichenbehaftete Literal: über die Hälfte → negativ.
    if n >= (1i128 << (breite - 1)) { format!("{}", n - voll) } else { format!("{n}") }
}

/// Wert an Zieltyp angleichen (erweitern/verengen/wandeln — gesund, da der Prüfer
/// die Bereiche hält; schneidet nie still ab, was nicht passt).
fn angleiche(k: &mut Koerper, v: Wert, ziel: &LlTyp, zziel: Zeichen) -> Option<Wert> {
    if &v.typ == ziel {
        return Some(v);
    }
    match (&v.typ, ziel) {
        (LlTyp::Int(wq), LlTyp::Int(wz)) => {
            let t = k.tmp();
            let op = if wz > wq {
                match v.zeichen {
                    Zeichen::S => "sext",
                    _ => "zext",
                }
            } else {
                "trunc"
            };
            k.zeile(&format!("{t} = {op} {} {} to {}", v.typ.text(), v.text, ziel.text()));
            Some(Wert { typ: ziel.clone(), zeichen: zziel, text: t, form: v.form })
        }
        (LlTyp::Int(1), LlTyp::F32 | LlTyp::F64) => {
            let t = k.tmp();
            k.zeile(&format!("{t} = uitofp i1 {} to {}", v.text, ziel.text()));
            Some(Wert { typ: ziel.clone(), zeichen: Zeichen::Egal, text: t, form: v.form })
        }
        (LlTyp::Int(_), LlTyp::F32 | LlTyp::F64) => {
            let t = k.tmp();
            let op = if v.zeichen == Zeichen::S { "sitofp" } else { "uitofp" };
            k.zeile(&format!("{t} = {op} {} {} to {}", v.typ.text(), v.text, ziel.text()));
            Some(Wert { typ: ziel.clone(), zeichen: Zeichen::Egal, text: t, form: v.form })
        }
        (LlTyp::F32 | LlTyp::F64, LlTyp::Int(_)) => {
            let t = k.tmp();
            let op = if zziel == Zeichen::S { "fptosi" } else { "fptoui" };
            k.zeile(&format!("{t} = {op} {} {} to {}", v.typ.text(), v.text, ziel.text()));
            Some(Wert { typ: ziel.clone(), zeichen: zziel, text: t, form: v.form })
        }
        (LlTyp::F32, LlTyp::F64) => {
            let t = k.tmp();
            k.zeile(&format!("{t} = fpext float {} to double", v.text));
            Some(Wert { typ: ziel.clone(), zeichen: Zeichen::Egal, text: t, form: v.form })
        }
        (LlTyp::F64, LlTyp::F32) => {
            let t = k.tmp();
            k.zeile(&format!("{t} = fptrunc double {} to float", v.text));
            Some(Wert { typ: ziel.clone(), zeichen: Zeichen::Egal, text: t, form: v.form })
        }
        (LlTyp::Ptr, LlTyp::Int(wz)) => {
            let t = k.tmp();
            k.zeile(&format!("{t} = ptrtoint ptr {} to i{wz}", v.text));
            Some(Wert { typ: ziel.clone(), zeichen: Zeichen::U, text: t, form: v.form })
        }
        (LlTyp::Benannt(a), LlTyp::Benannt(b)) => {
            // String-Wandlung (`max 8` → `max 16`): Länge plus Bytes, geprüft.
            match (gabstr_max(&LlTyp::Benannt(a.clone())), gabstr_max(&LlTyp::Benannt(b.clone()))) {
                (Some(ma), Some(mb)) => string_wandeln(k, v, ma, mb, b),
                _ => None,
            }
        }
        _ => None,
    }
}

/// String in breiteren/schmaleren Struct (`max`-Wechsel zur Laufzeitlänge).
fn string_wandeln(k: &mut Koerper, v: Wert, ma: u64, mb: u64, zielname: &str) -> Option<Wert> {
    let (len, bytes, _) = string_teile(k, &v)?;
    let st = LlTyp::Benannt(zielname.to_string());
    let slot = k.alloca(&st.text());
    // Passt die Laufzeitlänge? (Der Prüfer hält die Kopie — hierher kein Überlauf.)
    let len64 = k.tmp();
    k.zeile(&format!("{len64} = zext i32 {len} to i64"));
    let passt = k.tmp();
    k.zeile(&format!("{passt} = icmp ule i64 {len64}, {mb}"));
    let ok = k.block("strw_ok");
    let falle = k.block("strw_falle");
    k.zeile(&format!("br i1 {passt}, label %{ok}, label %{falle}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{falle}:");
    k.beendet = false;
    k.zeile("unreachable");
    k.beendet = true;
    let _ = writeln!(k.text, "{ok}:");
    k.beendet = false;
    let lp = k.tmp();
    k.zeile(&format!("{lp} = getelementptr %{zielname}, ptr {slot}, i32 0, i32 0"));
    k.zeile(&format!("store i32 {len}, ptr {lp}, align 4"));
    // Bytes bis Laufzeitlänge (nicht bis Max — der Rest bleibt undefiniert).
    let kopf = k.block("strw_kopf");
    let rumpf = k.block("strw_rumpf");
    let danach = k.block("strw_ende");
    let zaehler = k.alloca("i64");
    k.zeile(&format!("store i64 0, ptr {zaehler}, align 8"));
    k.zeile(&format!("br label %{kopf}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{kopf}:");
    k.beendet = false;
    let iv = k.tmp();
    k.zeile(&format!("{iv} = load i64, ptr {zaehler}, align 8"));
    let cond = k.tmp();
    k.zeile(&format!("{cond} = icmp ult i64 {iv}, {len64}"));
    k.zeile(&format!("br i1 {cond}, label %{rumpf}, label %{danach}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{rumpf}:");
    k.beendet = false;
    let qp = k.tmp();
    k.zeile(&format!("{qp} = getelementptr i8, ptr {bytes}, i64 {iv}"));
    let qb = k.tmp();
    k.zeile(&format!("{qb} = load i8, ptr {qp}, align 1"));
    let zp = k.tmp();
    k.zeile(&format!("{zp} = getelementptr %{zielname}, ptr {slot}, i32 0, i32 1, i64 {iv}"));
    k.zeile(&format!("store i8 {qb}, ptr {zp}, align 1"));
    let nv = k.tmp();
    k.zeile(&format!("{nv} = add i64 {iv}, 1"));
    k.zeile(&format!("store i64 {nv}, ptr {zaehler}, align 8"));
    k.zeile(&format!("br label %{kopf}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{danach}:");
    k.beendet = false;
    let t = k.tmp();
    k.zeile(&format!("{t} = load %{zielname}, ptr {slot}, align 8"));
    let _ = ma;
    Some(Wert { typ: st, zeichen: Zeichen::Egal, text: t, form: None })
}

/// **Versuchsweise senken (Annahmen fällen keine Einheit).** Was sich nicht senken
/// lässt, fällt lautlos unter den Tisch (Text, Zähler UND Absagen rollen zurück).
fn versuch(k: &mut Koerper, f: impl FnOnce(&mut Koerper) -> Option<String>) -> Option<String> {
    let n_abs = k.s.absagen.absagen.len();
    let text = std::mem::take(&mut k.text);
    let allocas = std::mem::take(&mut k.allocas);
    let (z, b) = (k.zaehler, k.bloecke);
    let r = f(k);
    match r {
        Some(x) => {
            // Erfolg behält BEIDES: Vortext (Bindungen!) plus Annahme.
            let mut t = text;
            t.push_str(&k.text);
            k.text = t;
            let mut a = allocas;
            a.push_str(&k.allocas);
            k.allocas = a;
            Some(x)
        }
        None => {
            k.text = text;
            k.allocas = allocas;
            k.zaehler = z;
            k.bloecke = b;
            k.s.absagen.absagen.truncate(n_abs);
            None
        }
    }
}

/// Eine Vergleichs-Annahme senken und als `llvm.assume` legen.
fn nehme_an(k: &mut Koerper, pred: &Pred, herkunft: &str) {
    if !matches!(pred.art, PredArt::Vergleich(_)) {
        return;
    }
    let cond = versuch(k, |kk| senke_predikat(kk, pred));
    if let Some(c) = cond {
        k.s.braucht_assume = true;
        k.zeile(&format!("call void @llvm.assume(i1 {c})"));
        let mut annahme = format!("{herkunft}: Vertrags-Vergleich");
        annahme.truncate(200);
        k.s.beleg_annahmen.push(annahme);
    }
}

/// Ein Vertragsprädikat als i1 — heute nur der Vergleich (die Form, die `bis` trägt).
fn senke_predikat(k: &mut Koerper, pred: &Pred) -> Option<String> {
    match &pred.art {
        PredArt::Vergleich(e) => {
            let v = senke_expr(k, e)?;
            match &v.typ {
                LlTyp::Int(1) => Some(v.text),
                LlTyp::Int(w) => {
                    let t = k.tmp();
                    k.zeile(&format!("{t} = icmp ne i{w} {}, 0", v.text));
                    Some(t)
                }
                _ => None,
            }
        }
        PredArt::Klammer(p) => senke_predikat(k, p),
        PredArt::Nicht(p) => {
            let c = senke_predikat(k, p)?;
            let t = k.tmp();
            k.zeile(&format!("{t} = xor i1 {c}, true"));
            Some(t)
        }
        PredArt::Und(a, b) => {
            let x = senke_predikat(k, a)?;
            let y = senke_predikat(k, b)?;
            let t = k.tmp();
            k.zeile(&format!("{t} = and i1 {x}, {y}"));
            Some(t)
        }
        PredArt::Oder(a, b) => {
            let x = senke_predikat(k, a)?;
            let y = senke_predikat(k, b)?;
            let t = k.tmp();
            k.zeile(&format!("{t} = or i1 {x}, {y}"));
            Some(t)
        }
        _ => None,
    }
}

// ===================================================================================
// Ausdrücke
// ===================================================================================

/// Eine Adresse plus Zugriffstyp und Form (Ladung/Speicher wandeln an der Grenze).
struct Adresse {
    addr: String,
    ll: LlTyp,
    zeichen: Zeichen,
    form: Option<TypExpr>,
    atomar: Option<&'static str>,
    fluechtig: bool,
    /// Bitfeld (Tiefstbit, Breite) — Ladung extrahiert, Speicher liest-modifiziert-schreibt.
    bit: Option<(u32, u32)>,
    /// Tabellenfeld hinter dieser Adresse (Tabelle, Feld) — für Invarianten-Bereiche.
    slot: Option<(String, String)>,
    /// Rekordfeld hinter dieser Adresse (Rekordname, Feld) — für Struct-Pfad-TBAA.
    rekord: Option<(String, String)>,
    /// Portraum (`device … at port`): `addr` ist eine `i16`-PORTNUMMER, kein Zeiger; Zugriff
    /// nur über `in`/`out` (`llvm/portraum.rs`). Jede andere Verwendung wird beim Namen verweigert.
    port: bool,
}

fn atomar_ordnung(o: &Ordnung) -> &'static str {
    match o {
        Ordnung::Acquire => "acquire",
        Ordnung::Release => "release",
        Ordnung::Seq => "seq_cst",
        // LLVM kennt kein `relaxed`-IR? Doch — `monotonic` ist es.
        Ordnung::Relaxed => "monotonic",
    }
}

fn senke_expr(k: &mut Koerper, e: &Expr) -> Option<Wert> {
    senke_expr_mit(k, e, None)
}

/// Ausdruck mit erwartetem Typ (Ruf-Argumente, Initialisierer — spart Wandlungen).
fn senke_expr_mit(k: &mut Koerper, e: &Expr, _erwartet: Option<(&LlTyp, Zeichen)>) -> Option<Wert> {
    // Zucker-Grenzwort (`u13::max` — Pfad über der Zucker-Schreibweise).
    if let ExprArt::Ort(o) = &e.art {
        if o.suffixe.len() == 1 {
            if let OrtSuffix::Feld(f) = &o.suffixe[0] {
                if (f.text == "max" || f.text == "min") && k.suche(&o.basis.text).is_none() && !k.s.globale.contains_key(&o.basis.text) {
                    if let Some((lo, hi)) = gabbro_syntax::parse::zucker_bereich(&o.basis.text) {
                        let v = if f.text == "max" { hi } else { lo };
                        if let Some((w, z)) = gabbro_syntax::parse::zucker_speicher(&o.basis.text).and_then(int_wort) {
                            return Some(Wert { typ: LlTyp::Int(w), zeichen: z, text: format!("{v}"), form: None });
                        }
                    }
                }
            }
        }
    }
    match &e.art {
        ExprArt::Zahl(v) => {
            // Breite aus dem Kontext raten wir nicht — i64, Angleichung am Gebrauch.
            // Kleine Literale passen überall; `falte_int` schneidet am Gebrauch zu.
            let t = format!("{}", v);
            Some(Wert { typ: LlTyp::Int(64), zeichen: Zeichen::U, text: t, form: None })
        }
        ExprArt::Gleitkomma { bits, .. } => {
            Some(Wert { typ: LlTyp::F64, zeichen: Zeichen::Egal, text: hexfloat(*bits, false), form: None })
        }
        ExprArt::Wahr => Some(Wert::int("true".to_string(), 1, Zeichen::Egal)),
        ExprArt::Falsch => Some(Wert::int("false".to_string(), 1, Zeichen::Egal)),
        ExprArt::Ort(o) => {
            if o.suffixe.is_empty() {
                if let Some((tname, fall_nr, nutz)) = varianten_fall(k.s, &o.basis.text) {
                    if nutz.is_none() {
                        sorge_variante(k.s, &tname, false);
                        let lname = layout_name(&tname, false);
                        let groesste = k.s.variant_typen.get(&tname).map(|(_, g)| *g).unwrap_or(0);
                        let t = k.tmp();
                        if groesste == 0 {
                            k.zeile(&format!("{t} = insertvalue %{lname} undef, i32 {fall_nr}, 0"));
                        } else {
                            let slot = k.alloca(&format!("%{lname}"));
                            let pp = k.tmp();
                            k.zeile(&format!("{pp} = getelementptr %{lname}, ptr {slot}, i32 0, i32 1"));
                            k.zeile(&format!("store [{groesste} x i8] zeroinitializer, ptr {pp}, align 1"));
                            let t0 = k.tmp();
                            k.zeile(&format!("{t0} = load %{lname}, ptr {slot}, align 8"));
                            k.zeile(&format!("{t} = insertvalue %{lname} {t0}, i32 {fall_nr}, 0"));
                        }
                        return Some(Wert { typ: LlTyp::Benannt(lname), zeichen: Zeichen::Egal, text: t, form: None });
                    }
                }
                if let Some((bits, f32)) = k.s.gkonst.get(&o.basis.text).cloned() {
                    let (typ, text) = if f32 {
                        (LlTyp::F32, hexfloat(bits, true))
                    } else {
                        (LlTyp::F64, hexfloat(bits, false))
                    };
                    return Some(Wert { typ, zeichen: Zeichen::Egal, text, form: None });
                }
            }
            let p = adresse_von_ort_mit(k, o, true)?;
            if let Some((lo, breite)) = p.bit {
                let al = nat_align(&p.ll);
                let w = if p.port {
                    portraum::lesen(k, &p.addr, &p.ll)
                } else {
                    let w = k.tmp();
                    k.zeile(&format!("{w} = load volatile {}, ptr {}, align {al}", p.ll.text(), p.addr));
                    w
                };
                let bw = p.ll.breite().unwrap_or(32);
                // Verschieben, schneiden (nur bei echter Verengung), auf i32 heben.
                let s1 = if lo == 0 {
                    w.clone()
                } else {
                    let s = k.tmp();
                    k.zeile(&format!("{s} = lshr i{bw} {w}, {lo}"));
                    s
                };
                let klein = if breite.max(1) < bw {
                    let t = k.tmp();
                    k.zeile(&format!("{t} = trunc i{bw} {s1} to i{}", breite.max(1)));
                    t
                } else {
                    s1
                };
                let t32 = if breite.max(1) < 32 {
                    let t = k.tmp();
                    k.zeile(&format!("{t} = zext i{} {klein} to i32", breite.max(1)));
                    t
                } else {
                    klein
                };
                return Some(Wert { typ: LlTyp::Int(32), zeichen: Zeichen::U, text: t32, form: None });
            }
            if p.port {
                let t = portraum::lesen(k, &p.addr, &p.ll);
                return Some(Wert { typ: p.ll, zeichen: p.zeichen, text: t, form: p.form });
            }
            let t = k.tmp();
            let al = nat_align(&p.ll);
            let meta = if p.fluechtig { String::new() } else { zugriff_meta(k, &p.ll, &p.form, true, &p.slot, &p.rekord, p.zeichen) };
            let vol = if p.fluechtig { " volatile" } else { "" };
            match &p.atomar {
                Some(ordnung) => {
                    k.zeile(&format!(
                        "{t} = load atomic{vol} {} , ptr {} {ordnung}, align {al}{meta}",
                        p.ll.text(),
                        p.addr
                    ));
                }
                None => {
                    k.zeile(&format!("{t} = load{vol} {}, ptr {}, align {al}{meta}", p.ll.text(), p.addr));
                }
            }
            // `bool`-Zelle als Byte: an der Grenze wandeln (trunc an jedem Zugriff).
            Some(Wert { typ: p.ll, zeichen: p.zeichen, text: t, form: p.form })
        }
        ExprArt::FnWert(p) => {
            let n = kurzname(p);
            let voll = p.text();
            let emit = k.s.emitnamen.get(&voll).cloned().unwrap_or(n.clone());
            if !k.s.fns.contains_key(&n) && !k.s.fns.contains_key(&voll) && !k.s.tore.contains_key(&n) {
                weigere(k.s, "Y104", e.span, format!("function value of unknown {n}"));
                return None;
            }
            Some(Wert { typ: LlTyp::Ptr, zeichen: Zeichen::Egal, text: format!("{}", gname(&emit)), form: None })
        }
        ExprArt::Ruf(r) => senke_ruf(k, r, e.span),
        ExprArt::LibraryCall(_) => {
            weigere(k.s, "Y104", e.span, "library call".to_string());
            None
        }
        ExprArt::Klammer(x) => senke_expr(k, x),
        ExprArt::Eingebaut(b) => senke_eingebaut(k, b, e.span),
        ExprArt::Alt(o) => match k.alt_wert.clone() {
            Some(v) => {
                // `old(X)` ist die eben geladene Antwort (nur im Vergleich).
                let _ = o;
                Some(v)
            }
            None => {
                weigere(k.s, "Y104", e.span, "contract-only expression in a body".to_string());
                None
            }
        },
        ExprArt::Ergebnis => match k.ergebnis_wert.clone() {
            Some(v) => Some(v),
            None => {
                weigere(k.s, "Y104", e.span, "contract-only expression in a body".to_string());
                None
            }
        },
        ExprArt::Grund { grund, fall } => {
            let faelle = k.s.gruende.get(&grund.text).cloned();
            match faelle {
                Some(fs) => match fs.iter().find(|(f, _)| f == &fall.text) {
                    Some((_, w)) => Some(Wert::int(format!("{w}"), 32, Zeichen::S)),
                    None => {
                        weigere(k.s, "Y104", e.span, format!("unknown case {} of reason {}", fall.text, grund.text));
                        None
                    }
                },
                None => {
                    weigere(k.s, "Y104", e.span, format!("unknown reason {}", grund.text));
                    None
                }
            }
        }
        ExprArt::Zaehle { variable, domaene, rumpf } => senke_zaehle(k, variable, domaene, rumpf, e.span),
        ExprArt::Unaer(op, x) => {
            let v = senke_expr(k, x)?;
            senke_unaer(k, *op, v, e.span)
        }
        ExprArt::Binaer(op, a, b) => {
            senke_binaer(k, *op, a, b, e.span, _erwartet)
        }
        ExprArt::ArrayLit(_) => {
            weigere(k.s, "Y104", e.span, "array literal in a body".to_string());
            None
        }
        ExprArt::Kette(bytes) => senke_kette(k, bytes, _erwartet, e.span),
    }
}

fn senke_unaer(k: &mut Koerper, op: UnOp, v: Wert, span: Span) -> Option<Wert> {
    match op {
        UnOp::Nicht => {
            let c = als_bool(k, v)?;
            let t = k.tmp();
            k.zeile(&format!("{t} = xor i1 {c}, true"));
            Some(Wert::int(t, 1, Zeichen::Egal))
        }
        UnOp::Negativ => match v.typ {
            LlTyp::Int(w) => {
                let t = k.tmp();
                k.zeile(&format!("{t} = sub i{w} 0, {}", v.text));
                Some(Wert { typ: LlTyp::Int(w), zeichen: Zeichen::S, text: t, form: v.form })
            }
            LlTyp::F32 => {
                let t = k.tmp();
                k.zeile(&format!("{t} = fneg float {}", v.text));
                Some(Wert { typ: LlTyp::F32, zeichen: Zeichen::Egal, text: t, form: v.form })
            }
            LlTyp::F64 => {
                let t = k.tmp();
                k.zeile(&format!("{t} = fneg double {}", v.text));
                Some(Wert { typ: LlTyp::F64, zeichen: Zeichen::Egal, text: t, form: v.form })
            }
            _ => {
                weigere(k.s, "Y104", span, "negation of this type".to_string());
                None
            }
        },
        UnOp::BitNicht => match v.typ {
            LlTyp::Int(w) => {
                let t = k.tmp();
                k.zeile(&format!("{t} = xor i{w} {}, -1", v.text));
                Some(Wert { typ: LlTyp::Int(w), zeichen: v.zeichen, text: t, form: v.form })
            }
            _ => {
                weigere(k.s, "Y104", span, "bitwise complement of this type".to_string());
                None
            }
        },
    }
}

/// Als i1 lesen (Vergleiche tragen ihn schon; Zahlen sind ungleich Null).
fn als_bool(k: &mut Koerper, v: Wert) -> Option<String> {
    match &v.typ {
        LlTyp::Int(1) => Some(v.text),
        LlTyp::Int(w) => {
            let t = k.tmp();
            k.zeile(&format!("{t} = icmp ne i{w} {}, 0", v.text));
            Some(t)
        }
        _ => None,
    }
}

/// Gemeinsame Ganzzahl-Breite zweier Operanden (der breitere gewinnt).
fn gemein_int(a: &Wert, b: &Wert) -> Option<(u32, Zeichen)> {
    match (&a.typ, &b.typ) {
        (LlTyp::Int(wa), LlTyp::Int(wb)) => {
            let w = (*wa).max(*wb);
            let z = if a.zeichen == Zeichen::S || b.zeichen == Zeichen::S {
                Zeichen::S
            } else {
                Zeichen::U
            };
            Some((w, z))
        }
        _ => None,
    }
}

/// Which no-wrap flag the operands justify: `nuw` when both known signs are unsigned, `nsw`
/// when both are signed, none when the two differ or neither sign is known.
fn nowrap_flag(a: Zeichen, b: Zeichen) -> Option<&'static str> {
    match (a, b) {
        (Zeichen::U, Zeichen::U) | (Zeichen::U, Zeichen::Egal) | (Zeichen::Egal, Zeichen::U) => Some("nuw"),
        (Zeichen::S, Zeichen::S) | (Zeichen::S, Zeichen::Egal) | (Zeichen::Egal, Zeichen::S) => Some("nsw"),
        _ => None,
    }
}

fn senke_binaer(
    k: &mut Koerper,
    op: BinOp,
    a: &Expr,
    b: &Expr,
    span: Span,
    erwartet: Option<(&LlTyp, Zeichen)>,
) -> Option<Wert> {
    // Kurzschluss für die logischen (RHS läuft nur bei Bedarf — Seiteneffekte!).
    if matches!(op, BinOp::Und | BinOp::Oder) {
        let x = senke_expr(k, a)?;
        let xc = als_bool(k, x)?;
        let ein = k.block("und_ein");
        let aus = k.block("und_aus");
        let rechts = k.block("und_rechts");
        if matches!(op, BinOp::Und) {
            k.zeile(&format!("br i1 {xc}, label %{rechts}, label %{ein}"));
        } else {
            k.zeile(&format!("br i1 {xc}, label %{ein}, label %{rechts}"));
        }
        k.beendet = true;
        let _ = writeln!(k.text, "{rechts}:");
        k.beendet = false;
        let y = senke_expr(k, b)?;
        let yc = als_bool(k, y)?;
        k.zeile(&format!("br label %{aus}"));
        k.beendet = true;
        let _ = writeln!(k.text, "{ein}:");
        k.beendet = false;
        k.zeile(&format!("br label %{aus}"));
        k.beendet = true;
        let _ = writeln!(k.text, "{aus}:");
        k.beendet = false;
        let t = k.tmp();
        let (lx, ly) = if matches!(op, BinOp::Und) {
            (format!("false"), yc)
        } else {
            (format!("true"), yc)
        };
        let _ = lx;
        // Wahrheitswert je Pfad: links entschied schon, rechts trägt y.
        k.zeile(&format!("{t} = phi i1 [ {xc}, %{ein} ], [ {ly}, %{rechts} ]"));
        return Some(Wert::int(t, 1, Zeichen::Egal));
    }
    // Zeichenketten laufen über Länge plus Bytes (lexikografisch, verkettet).
    if matches!(
        op,
        BinOp::Plus | BinOp::Gleich | BinOp::Ungleich | BinOp::Kleiner | BinOp::KleinerGleich | BinOp::Groesser | BinOp::GroesserGleich
    ) && (erwartet.is_some_and(|(t, _)| gabstr_max(t).is_some()) || ist_string_expr(k, a) || ist_string_expr(k, b))
    {
        return senke_string_binop(k, op, a, b, span, erwartet);
    }
    let va = senke_expr(k, a)?;
    let vb = senke_expr(k, b)?;
    // Gleitkomma, wenn eine Seite es ist.
    let float = matches!(va.typ, LlTyp::F32 | LlTyp::F64) || matches!(vb.typ, LlTyp::F32 | LlTyp::F64);
    if float {
        let (ta, tb) = (va.typ.clone(), vb.typ.clone());
        let ziel = if matches!(ta, LlTyp::F64) || matches!(tb, LlTyp::F64) {
            LlTyp::F64
        } else {
            LlTyp::F32
        };
        let xa = angleiche(k, va, &ziel, Zeichen::Egal)?;
        let xb = angleiche(k, vb, &ziel, Zeichen::Egal)?;
        let t = k.tmp();
        let mnemonic = match op {
            BinOp::Plus | BinOp::PlusWrap | BinOp::PlusSat => "fadd",
            BinOp::Minus | BinOp::MinusWrap => "fsub",
            BinOp::Mal | BinOp::MalWrap => "fmul",
            BinOp::Geteilt => "fdiv",
            BinOp::Rest => "frem",
            BinOp::Gleich => {
                k.zeile(&format!("{t} = fcmp oeq {} {}, {}", ziel.text(), xa.text, xb.text));
                return Some(Wert::int(t, 1, Zeichen::Egal));
            }
            BinOp::Ungleich => {
                k.zeile(&format!("{t} = fcmp une {} {}, {}", ziel.text(), xa.text, xb.text));
                return Some(Wert::int(t, 1, Zeichen::Egal));
            }
            BinOp::Kleiner => {
                k.zeile(&format!("{t} = fcmp olt {} {}, {}", ziel.text(), xa.text, xb.text));
                return Some(Wert::int(t, 1, Zeichen::Egal));
            }
            BinOp::KleinerGleich => {
                k.zeile(&format!("{t} = fcmp ole {} {}, {}", ziel.text(), xa.text, xb.text));
                return Some(Wert::int(t, 1, Zeichen::Egal));
            }
            BinOp::Groesser => {
                k.zeile(&format!("{t} = fcmp ogt {} {}, {}", ziel.text(), xa.text, xb.text));
                return Some(Wert::int(t, 1, Zeichen::Egal));
            }
            BinOp::GroesserGleich => {
                k.zeile(&format!("{t} = fcmp oge {} {}, {}", ziel.text(), xa.text, xb.text));
                return Some(Wert::int(t, 1, Zeichen::Egal));
            }
            _ => {
                weigere(k.s, "Y104", span, "bitwise operation on floats".to_string());
                return None;
            }
        };
        // Sättigung kennt kein float (Prüfer hält das — hier nie gesenkt).
        if matches!(op, BinOp::PlusSat) {
            weigere(k.s, "Y104", span, "saturating addition on floats".to_string());
            return None;
        }
        k.zeile(&format!("{t} = {mnemonic} {} {}, {}", ziel.text(), xa.text, xb.text));
        return Some(Wert { typ: ziel, zeichen: Zeichen::Egal, text: t, form: None });
    }
    let (w, z) = match gemein_int(&va, &vb) {
        Some(x) => x,
        None => {
            weigere(k.s, "Y104", span, "mixed integer and non-integer operands".to_string());
            return None;
        }
    };
    let flag = nowrap_flag(va.zeichen, vb.zeichen);
    let xa = angleiche(k, va, &LlTyp::Int(w), z)?;
    let xb = angleiche(k, vb, &LlTyp::Int(w), z)?;
    let t = k.tmp();
    let signed = z == Zeichen::S;
    // Plain `+ - *` carry `nuw`/`nsw`: the checker (M104) refuses every sum, difference or
    // product that could leave the operands' width, so no value of such an operation wraps.
    // The wrapping forms (`+% -% *%`) carry no flag.
    let mit = |k: &mut Koerper, wrap: bool| -> &'static str {
        match (wrap, flag) {
            (false, Some("nuw")) => {
                k.s.fakt("nuw");
                " nuw"
            }
            (false, Some(_)) => {
                k.s.fakt("nsw");
                " nsw"
            }
            _ => "",
        }
    };
    match op {
        BinOp::Plus | BinOp::PlusWrap => {
            let f = mit(k, matches!(op, BinOp::PlusWrap));
            k.zeile(&format!("{t} = add{f} i{w} {}, {}", xa.text, xb.text));
        }
        BinOp::Minus | BinOp::MinusWrap => {
            let f = mit(k, matches!(op, BinOp::MinusWrap));
            k.zeile(&format!("{t} = sub{f} i{w} {}, {}", xa.text, xb.text));
        }
        BinOp::Mal | BinOp::MalWrap => {
            let f = mit(k, matches!(op, BinOp::MalWrap));
            k.zeile(&format!("{t} = mul{f} i{w} {}, {}", xa.text, xb.text));
        }
        BinOp::Geteilt => {
            let m = if signed { "sdiv" } else { "udiv" };
            k.zeile(&format!("{t} = {m} i{w} {}, {}", xa.text, xb.text));
        }
        BinOp::Rest => {
            let m = if signed { "srem" } else { "urem" };
            k.zeile(&format!("{t} = {m} i{w} {}, {}", xa.text, xb.text));
        }
        BinOp::SchiebLinks | BinOp::SchiebLinksWrap => {
            k.zeile(&format!("{t} = shl i{w} {}, {}", xa.text, xb.text));
        }
        BinOp::SchiebRechts => {
            let m = if signed { "ashr" } else { "lshr" };
            k.zeile(&format!("{t} = {m} i{w} {}, {}", xa.text, xb.text));
        }
        BinOp::BitUnd => {
            k.zeile(&format!("{t} = and i{w} {}, {}", xa.text, xb.text));
        }
        BinOp::BitOder => {
            k.zeile(&format!("{t} = or i{w} {}, {}", xa.text, xb.text));
        }
        BinOp::BitXor => {
            k.zeile(&format!("{t} = xor i{w} {}, {}", xa.text, xb.text));
        }
        BinOp::Gleich => {
            k.zeile(&format!("{t} = icmp eq i{w} {}, {}", xa.text, xb.text));
            return Some(Wert::int(t, 1, Zeichen::Egal));
        }
        BinOp::Ungleich => {
            k.zeile(&format!("{t} = icmp ne i{w} {}, {}", xa.text, xb.text));
            return Some(Wert::int(t, 1, Zeichen::Egal));
        }
        BinOp::Kleiner => {
            let m = if signed { "slt" } else { "ult" };
            k.zeile(&format!("{t} = icmp {m} i{w} {}, {}", xa.text, xb.text));
            return Some(Wert::int(t, 1, Zeichen::Egal));
        }
        BinOp::KleinerGleich => {
            let m = if signed { "sle" } else { "ule" };
            k.zeile(&format!("{t} = icmp {m} i{w} {}, {}", xa.text, xb.text));
            return Some(Wert::int(t, 1, Zeichen::Egal));
        }
        BinOp::Groesser => {
            let m = if signed { "sgt" } else { "ugt" };
            k.zeile(&format!("{t} = icmp {m} i{w} {}, {}", xa.text, xb.text));
            return Some(Wert::int(t, 1, Zeichen::Egal));
        }
        BinOp::GroesserGleich => {
            let m = if signed { "sge" } else { "uge" };
            k.zeile(&format!("{t} = icmp {m} i{w} {}, {}", xa.text, xb.text));
            return Some(Wert::int(t, 1, Zeichen::Egal));
        }
        BinOp::PlusSat => {
            // Sättigung von Hand (kein Intrinsic nötig): Summe in +1 Bit gibt es
            // nicht — darum über Vergleich und Auswahl.
            let sum = k.tmp();
            k.zeile(&format!("{sum} = add i{w} {}, {}", xa.text, xb.text));
            let voll: u128 = if w >= 128 { u128::MAX } else { (1u128 << w) - 1 };
            let max_text = if signed {
                format!("{}", (voll >> 1) as i128)
            } else {
                format!("{voll}")
            };
            let ueber = k.tmp();
            if signed {
                k.zeile(&format!("{ueber} = icmp slt i{w} {sum}, {}", xa.text));
                // Negative Überläufe unterschlagen wir nie: zweiter Vergleich.
                let _ = ueber;
            } else {
                k.zeile(&format!("{ueber} = icmp ult i{w} {sum}, {}", xa.text));
            }
            k.zeile(&format!("{t} = select i1 {ueber}, i{w} {max_text}, i{w} {sum}"));
            return Some(Wert { typ: LlTyp::Int(w), zeichen: z, text: t, form: None });
        }
        BinOp::Und | BinOp::Oder => unreachable!("kurzgeschlossen"),
    }
    Some(Wert { typ: LlTyp::Int(w), zeichen: z, text: t, form: None })
}

fn senke_eingebaut(k: &mut Koerper, b: &Eingebaut, span: Span) -> Option<Wert> {
    match b {
        Eingebaut::Sizeof(t) => senke_sizeof(k, t, span),
        Eingebaut::Lenof(t) => senke_lenof(k, t, span),
        Eingebaut::Aligned(_, _) => {
            weigere(k.s, "Y104", span, "alignment probe".to_string());
            None
        }
    }
}

// ===================================================================================
// Adressen (Orte → Zeiger)
// ===================================================================================

/// Basis auflösen: lokale Bindung, Globales, Arena, Atomic, Tabelle.
fn basis_adresse(
    k: &mut Koerper,
    name: &str,
    span: Span,
) -> Option<(String, LlTyp, Zeichen, Option<TypExpr>, Option<&'static str>, bool)> {
    if let Some(b) = k.suche(name) {
        return Some((b.ptr, b.ll, b.zeichen, b.form, None, b.fluechtig));
    }
    if let Some(g) = k.s.globale.get(name).cloned() {
        let fl = ist_fluechtig(k.s, &Some(g.form.clone()));
        return Some((format!("{}", gname(&name)), g.typ, g.zeichen, Some(g.form), None, fl));
    }
    if let Some(ai) = k.s.arenen.get(name).cloned() {
        // Nur mit Index zu gebrauchen (unten) — nackt weist der Prüfer ab.
        let gtext = gteil(name, "basis");
        return Some((gtext, LlTyp::Feld(Box::new(ai.elem.clone()), ai.max), Zeichen::Egal, Some(ai.form), None, false));
    }
    if let Some((ll, ord)) = k.s.atomare.get(name).cloned() {
        let ord_static: &'static str = match ord.as_str() {
            "acquire" => "acquire",
            "release" => "release",
            "seq_cst" => "seq_cst",
            _ => "monotonic",
        };
        return Some((format!("{}", gname(&name)), ll, Zeichen::U, None, Some(ord_static), false));
    }
    if k.s.tabellen.contains_key(name) {
        // Tabellenname als Wert: Adresse des Träger-Globals (`%Tab`, Form: Pfad).
        let form = TypExpr::Pfad(Pfad {
            teile: vec![Ident { text: name.to_string(), span }],
            span,
        });
        return Some((format!("{}", gname(name)), LlTyp::Benannt(name.to_string()), Zeichen::Egal, Some(form), None, false));
    }
    weigere(k.s, "Y104", span, format!("unknown place {name}"));
    None
}

/// Feldnummer im Rekord (hinter Alias her) — Slots über `tab_slots`.
fn feld_nummer(s: &Senke, rekord: &str, feld: &str) -> Option<(usize, TypExpr)> {
    if let Some(fs) = s.rekorde.get(rekord) {
        return fs.iter().position(|(n, _)| n == feld).map(|i| (i, fs[i].1.clone()));
    }
    let basis = rekord.strip_suffix("$slot").unwrap_or(rekord);
    if let Some(fs) = s.tab_slots.get(basis).or_else(|| s.tab_slots.get(rekord)) {
        return fs.iter().position(|(n, _)| n == feld).map(|i| (i, fs[i].1.clone()));
    }
    None
}

fn adresse_von_ort(k: &mut Koerper, ort: &Ort) -> Option<Adresse> {
    adresse_von_ort_mit(k, ort, false)
}

/// `port_ok`: der Aufrufer liest oder schreibt den Ort selbst (`portraum.rs`); jeder andere
/// Gebrauch eines Portregisters (Adresse nehmen, `+=`, Atomar, Zeiger) wird verweigert.
fn adresse_von_ort_mit(k: &mut Koerper, ort: &Ort, port_ok: bool) -> Option<Adresse> {
    let mut port = false;
    let (mut ptr, mut ll, mut z, mut form, mut atomar, fluechtig) = basis_adresse(k, &ort.basis.text, ort.span)?;
    let fluechtig = fluechtig || ist_fluechtig(k.s, &form);
    // Arena-Basis (Elemente liegen hinter der Laufzeit-Basis, nicht im Global).
    // Nackt ist sie kein Ort — der Prüfer weist das ab; Schweigen wäre ein Loch.
    if k.s.arenen.contains_key(&ort.basis.text) && ort.suffixe.is_empty() {
        weigere(k.s, "Y103", ort.span, format!("bare arena {} is not a place", ort.basis.text));
        return None;
    }
    let arena_tisch: Option<String> = if k.s.arenen.contains_key(&ort.basis.text) {
        Some(ort.basis.text.clone())
    } else {
        None
    };
    // Geräteregister hinter dem Feld (Name, Tiefstbit, Breite merken).
    let mut dev_reg: Option<(String, String)> = None;
    let mut bit: Option<(u32, u32)> = None;
    // Tabellenfeld (für Invarianten-Bereiche aus `forall`-Klauseln).
    let mut slot_feld: Option<(String, String)> = None;
    // Rekordfeld (für Struct-Pfad-TBAA).
    let mut rekord_feld: Option<(String, String)> = None;
    let mut tab_aktuell: Option<String> = None;
    // Tabellenname als Basis: Adresse des Globals (bereit für `.slots`).
    let mut geladen: Option<String> = None;
    for suffix in &ort.suffixe {
        match suffix {
            OrtSuffix::Feld(f) => {
                // `.slots` an einer Tabelle: in den Träger steigen (Feld 0 von `%Tab`).
                // Form ist Tabellen-Pfad oder Zeiger darauf (`w : ptr<…> Werte`).
                if f.text == "slots" {
                    let tab_opt = form.clone().map(|ff| grundform(k.s, &ff)).and_then(|tf| match tf {
                        TypExpr::Pfad(p) => p.einfach().map(|e| e.text.clone()),
                        TypExpr::Zeiger(zz) => match grundform(k.s, &zz.ziel) {
                            TypExpr::Pfad(p) => p.einfach().map(|e| e.text.clone()),
                            _ => None,
                        },
                        _ => None,
                    }).filter(|tn| k.s.tabellen.contains_key(tn));
                    if let Some(tn) = tab_opt {
                        let cur = geladen.clone().unwrap_or_else(|| ptr.clone());
                        let base = match &ll {
                            LlTyp::Ptr => {
                                let t = k.tmp();
                                k.zeile(&format!("{t} = load ptr, ptr {cur}, align 8"));
                                t
                            }
                            _ => cur,
                        };
                        geladen = Some(base.clone());
                        let (len, slot) = k.s.tabellen.get(&tn).cloned()?;
                        let arr = LlTyp::Feld(Box::new(LlTyp::Benannt(slot)), len);
                        let t = k.tmp();
                        k.zeile(&format!("{t} = getelementptr %{tn}, ptr {base}, i32 0, i32 0"));
                        ptr = t.clone();
                        geladen = Some(t.clone());
                        ll = arr;
                        form = None;
                        atomar = None;
                        tab_aktuell = Some(tn.clone());
                        continue;
                    }
                }
                // Geräteregister: Form nennt das Gerät (Zeiger oder Wert vom Konstruktor).
                if let Some(dev) = geraet_hinter(k.s, &form) {
                    match k.s.geraete.get(&dev).and_then(|rs| rs.iter().find(|r| r.name == f.text).cloned()) {
                        Some(reg) if reg.port => {
                            if !port_ok {
                                weigere(
                                    k.s,
                                    "Y102",
                                    suffix_span(suffix),
                                    format!("port register {}.{} used as an address: a port is reached by `in`/`out` only", dev, reg.name),
                                );
                                return None;
                            }
                            let cur = geladen.clone().unwrap_or_else(|| ptr.clone());
                            let nr = portraum::portnummer(k, &ll, &cur, reg.versatz, suffix_span(suffix))?;
                            ptr = nr.clone();
                            geladen = Some(nr);
                            ll = reg.ll.clone();
                            z = reg.zeichen;
                            form = None;
                            atomar = None;
                            port = true;
                            dev_reg = Some((dev, reg.name.clone()));
                            continue;
                        }
                        Some(reg) => {
                            let cur = geladen.clone().unwrap_or_else(|| ptr.clone());
                            // Griff laden (Zeiger) oder wandeln (Basisadresse als Zahl —
                            // die EINE `inttoptr`-Stelle: abstrakte Register haben
                            // keine Adresse, Basis+Versatz ist die Treiberabbildung).
                            let roh = match &ll {
                                LlTyp::Ptr => {
                                    let t = k.tmp();
                                    k.zeile(&format!("{t} = load ptr, ptr {cur}, align 8"));
                                    t
                                }
                                LlTyp::Int(_) => {
                                    let geladen_wert = k.tmp();
                                    k.zeile(&format!("{geladen_wert} = load i64, ptr {cur}, align 8"));
                                    let t = k.tmp();
                                    k.zeile(&format!("{t} = inttoptr i64 {geladen_wert} to ptr"));
                                    t
                                }
                                _ => {
                                    weigere(k.s, "Y104", suffix_span(suffix), format!("device handle of odd type"));
                                    return None;
                                }
                            };
                            let off = k.tmp();
                            k.zeile(&format!("{off} = getelementptr i8, ptr {roh}, i64 {}", reg.versatz));
                            let bc = k.tmp();
                            k.zeile(&format!("{bc} = getelementptr i8, ptr {off}, i64 0"));
                            ptr = bc.clone();
                            geladen = Some(bc.clone());
                            ll = reg.ll.clone();
                            z = reg.zeichen;
                            form = None;
                            atomar = None;
                            dev_reg = Some((dev, reg.name.clone()));
                            continue;
                        }
                        None => {
                            // Kein Register — vielleicht ein Bitfeld (unten)?
                            // Fällt durch auf die Bitfeld-Prüfung hinter dem Register.
                        }
                    }
                }
                // Bitfeld hinter einem Geräteregister (Adresse bleibt Wortadresse).
                if let Some((dev, reg)) = dev_reg.clone() {
                    if let Some((_, lo, breite)) = bitfeld(k.s, &dev, &reg, &f.text) {
                        bit = Some((lo, breite));
                        continue;
                    }
                    weigere(k.s, "Y104", suffix_span(suffix), format!("unknown bit field {}", f.text));
                    return None;
                }
                // Feld eines Tabellen-Slots: Identität merken (Invarianten-Bereich).
                if let Some(tn) = tab_aktuell.clone() {
                    if k.s.tab_slots.get(&tn).is_some_and(|fs| fs.iter().any(|(n, _)| n == &f.text)) {
                        slot_feld = Some((tn, f.text.clone()));
                    }
                }
                // Gewöhnliches Rekordfeld (ggf. durch Zeiger hindurch).
                let cur = geladen.clone().unwrap_or_else(|| ptr.clone());
                let ( need_load, struct_typ, rec_name ) = match &ll {
                    LlTyp::Ptr => {
                        // Zeiger auf Rekord: Form hinter dem Zeiger suchen.
                        match form.clone().map(|f| grundform(k.s, &f)) {
                            Some(TypExpr::Zeiger(zz)) => {
                                let inner = grundform(k.s, &zz.ziel);
                                match &inner {
                                    TypExpr::Pfad(p) if p.einfach().is_some_and(|e| k.s.rekorde.contains_key(&e.text)) => {
                                        let rn = p.einfach().unwrap().text.clone();
                                        sorge_typdef(k.s, &rn, false);
                                        (true, LlTyp::Benannt(layout_name(&rn, false)), Some(rn))
                                    }
                                    TypExpr::Verbund(_, _) => (true, LlTyp::Anon(vec![]), None),
                                    _ => {
                                        weigere(k.s, "Y104", suffix_span(suffix), format!("field {} of non-record pointer", f.text));
                                        return None;
                                    }
                                }
                            }
                            _ => {
                                weigere(k.s, "Y104", suffix_span(suffix), format!("field {} of pointer without record form", f.text));
                                return None;
                            }
                        }
                    }
                    LlTyp::Benannt(n) => {
                        let rn = n.strip_suffix("$breit").unwrap_or(n).to_string();
                        (false, ll.clone(), Some(rn))
                    }
                    LlTyp::Anon(_) => (false, ll.clone(), None),
                    _ => {
                        weigere(k.s, "Y104", suffix_span(suffix), format!("field {} of non-record", f.text));
                        return None;
                    }
                };
                let base = if need_load {
                    let t = k.tmp();
                    k.zeile(&format!("{t} = load ptr, ptr {cur}, align 8"));
                    t
                } else {
                    cur
                };
                geladen = Some(base.clone());
                // Feldnummer bestimmen.
                let (nr, ftyp) = match rec_name.clone() {
                    Some(rn) => feld_nummer(k.s, &rn, &f.text)?,
                    None => {
                        weigere(k.s, "Y104", suffix_span(suffix), format!("field {} of anonymous record", f.text));
                        return None;
                    }
                };
                if let Some(rn) = rec_name.clone() {
                    // Tabellen-Slot trägt seinen eigenen Struct-Namen (`T$slot`).
                    let struktur = if rn.ends_with("$slot") { rn.clone() } else { rn.clone() };
                    rekord_feld = Some((struktur, f.text.clone()));
                }
                let (fll, fz) = senke_typ(k.s, &ftyp)?;
                let t = k.tmp();
                k.zeile(&format!(
                    "{t} = getelementptr {}, ptr {base}, i32 0, i32 {nr}",
                    struct_typ.text()
                ));
                ptr = t.clone();
                // The ADDRESS of the access is the field pointer. It stood as `base` (the
                // record's own address) until 2026-10-17 -- every field behind the first one
                // read and wrote the first field's word (found by messung/llvm/leserschreiber.gab:
                // `paar.b` aliased `paar.a`, both targets, deterministic).
                geladen = Some(t.clone());
                ll = fll;
                z = fz;
                form = Some(ftyp);
                atomar = None;
            }
            OrtSuffix::Index(idx) => {
                let iv = senke_expr(k, idx)?;
                let ii = angleiche(k, iv, &LlTyp::Int(64), Zeichen::U)?;
                let cur = geladen.clone().unwrap_or_else(|| ptr.clone());
                // Elementtyp + GEP-Operanden je Träger.
                match ll.clone() {
                    LlTyp::Feld(e, _) => {
                        // Arena-Element (Basis aus der Laufzeit — DRITTE sanktionierte
                        // `inttoptr`-Stelle: die Basis kommt aus eigenem `mmap`).
                        if let Some(tisch) = arena_tisch.clone() {
                            let ai = k.s.arenen.get(&tisch).cloned()?;
                            let b = k.tmp();
                            k.zeile(&format!("{b} = load i64, ptr {}, align 8", gteil(&tisch, "basis")));
                            let bp = k.tmp();
                            k.zeile(&format!("{bp} = inttoptr i64 {b} to ptr"));
                            let t = k.tmp();
                            k.zeile(&format!(
                                "{t} = getelementptr {}, ptr {bp}, {} {}",
                                ai.elem.text(),
                                ii.typ.text(),
                                ii.text
                            ));
                            ptr = t.clone();
                            geladen = Some(t.clone());
                            form = Some(ai.form.clone());
                            ll = ai.elem.clone();
                            continue;
                        }
                        let t = k.tmp();
                        // M4 (M103): the index of a fixed array is proven below its length.
                        k.s.fakt("inbounds");
                        k.zeile(&format!(
                            "{t} = getelementptr inbounds {}, ptr {cur}, i32 0, {} {}",
                            ll.text(),
                            ii.typ.text(),
                            ii.text
                        ));
                        ptr = t.clone();
                        geladen = Some(t.clone());
                        let ef = match form.clone().map(|f| grundform(k.s, &f)) {
                            Some(TypExpr::Feld(a)) => Some(a.element.clone()),
                            _ => None,
                        };
                        form = ef;
                        ll = (*e).clone();
                        // Element eines Atom-Felds: Zugriff ordnen (ein Wort je Element).
                        if let Some((_, ord)) = k.s.atomare.get(&ort.basis.text).cloned() {
                            let ord_static: &'static str = match ord.as_str() {
                                "acquire" => "acquire",
                                "release" => "release",
                                "seq_cst" => "seq_cst",
                                _ => "monotonic",
                            };
                            atomar = Some(ord_static);
                        }
                    }
                    LlTyp::Ptr => {
                        // Zeiger-Index: Ziel aus der Form (Feld/Arena/Tabellen-Slot).
                        let (elem_ll, elem_form, gep_typ) = match form.clone().map(|f| grundform(k.s, &f)) {
                            Some(TypExpr::Zeiger(zz)) => {
                                let inner = grundform(k.s, &zz.ziel);
                                let (ell, _) = senke_typ(k.s, &inner)?;
                                (ell.clone(), Some(inner), ell.text())
                            }
                            _ => {
                                weigere(k.s, "Y104", suffix_span(suffix), "index into pointer without element form".to_string());
                                return None;
                            }
                        };
                        let base = {
                            let t = k.tmp();
                            k.zeile(&format!("{t} = load ptr, ptr {cur}, align 8"));
                            t
                        };
                        let t = k.tmp();
                        k.zeile(&format!(
                            "{t} = getelementptr {gep_typ}, ptr {base}, {} {}",
                            ii.typ.text(),
                            ii.text
                        ));
                        ptr = t.clone();
                        geladen = Some(t.clone());
                        ll = elem_ll;
                        form = elem_form;
                    }
                    LlTyp::Benannt(n) if n.starts_with("gabstr") => {
                        let t = k.tmp();
                        k.zeile(&format!(
                            "{t} = getelementptr %{n}, ptr {cur}, i32 0, i32 1, {} {}",
                            ii.typ.text(),
                            ii.text
                        ));
                        ptr = t.clone();
                        geladen = Some(t.clone());
                        ll = LlTyp::Int(8);
                        z = Zeichen::U;
                        form = None;
                    }
                    LlTyp::Benannt(n) => {
                        // Tabellen-Träger: `[N x Slot]` hinter `%Tab`.
                        let stroh = n.strip_suffix("$breit").unwrap_or(&n).to_string();
                        if k.s.tabellen.contains_key(&stroh) {
                            let (len, slot) = k.s.tabellen.get(&stroh).cloned()?;
                            let slot_ll = LlTyp::Benannt(slot.clone());
                            // Erst in `.slots` (Feld 0), dann Element.
                            let t0 = k.tmp();
                            let cur2 = geladen.clone().unwrap_or_else(|| ptr.clone());
                            // Falls Zeiger auf Tabelle: laden.
                            let base = if matches!(ll, LlTyp::Benannt(_)) && geladen.is_none() && cur_is_global_or_alloca(k, &cur2) {
                                cur2
                            } else {
                                let t = k.tmp();
                                k.zeile(&format!("{t} = load ptr, ptr {cur2}, align 8"));
                                t
                            };
                            let _ = len;
                            let t = k.tmp();
                            k.zeile(&format!(
                                "{t} = getelementptr %{stroh}, ptr {base}, i32 0, i32 0, {} {}",
                                ii.typ.text(),
                                ii.text
                            ));
                            let _ = t0;
                            ptr = t.clone();
                            geladen = Some(t.clone());
                            ll = slot_ll;
                            form = None;
                        } else {
                            weigere(k.s, "Y104", suffix_span(suffix), format!("index into {n}"));
                            return None;
                        }
                    }
                    _ => {
                        weigere(k.s, "Y104", suffix_span(suffix), "index into scalar".to_string());
                        return None;
                    }
                }
                z = Zeichen::Egal;
                atomar = None;
            }
            OrtSuffix::Ueber(f) => {
                // `->feld`: Zeiger laden, dann Feld.
                let cur = geladen.clone().unwrap_or_else(|| ptr.clone());
                let base = {
                    let t = k.tmp();
                    k.zeile(&format!("{t} = load ptr, ptr {cur}, align 8"));
                    t
                };
                let (struct_typ, rec_name) = match form.clone().map(|ff| grundform(k.s, &ff)) {
                    Some(TypExpr::Zeiger(zz)) => match grundform(k.s, &zz.ziel) {
                        TypExpr::Pfad(p) if p.einfach().is_some_and(|e| k.s.rekorde.contains_key(&e.text)) => {
                            let rn = p.einfach().unwrap().text.clone();
                            sorge_typdef(k.s, &rn, false);
                            (LlTyp::Benannt(layout_name(&rn, false)), rn)
                        }
                        _ => {
                            weigere(k.s, "Y104", suffix_span(suffix), format!("`{}` of non-record pointer", f.text));
                            return None;
                        }
                    },
                    _ => {
                        weigere(k.s, "Y104", suffix_span(suffix), format!("`{}` without pointer form", f.text));
                        return None;
                    }
                };
                let (nr, ftyp) = feld_nummer(k.s, &rec_name, &f.text)?;
                let (fll, fz) = senke_typ(k.s, &ftyp)?;
                let t = k.tmp();
                k.zeile(&format!(
                    "{t} = getelementptr {}, ptr {base}, i32 0, i32 {nr}",
                    struct_typ.text()
                ));
                ptr = t.clone();
                geladen = Some(t.clone());
                ll = fll;
                z = fz;
                form = Some(ftyp);
                atomar = None;
            }
        }
    }
    Some(Adresse { addr: geladen.unwrap_or(ptr), ll, zeichen: z, form, atomar, fluechtig, bit, slot: slot_feld, rekord: rekord_feld, port })
}

fn suffix_span(s: &OrtSuffix) -> Span {
    match s {
        OrtSuffix::Feld(i) => i.span,
        OrtSuffix::Index(e) => e.span,
        OrtSuffix::Ueber(i) => i.span,
    }
}

/// Heuristik: Text ist Alloca/Lokal oder Global (kein geladener Zeiger).
fn cur_is_global_or_alloca(_k: &Koerper, cur: &str) -> bool {
    cur.starts_with("%a") || cur.starts_with("@\"")
}

// ===================================================================================
// Rufe (Funktionen, Tore, Umwandlungen, Konstruktoren)
// ===================================================================================

/// Ruf senken: Umwandlung, Verbundwert, Variante, Tor, Funktion — in der Ordnung.
fn senke_ruf(k: &mut Koerper, r: &Ruf, span: Span) -> Option<Wert> {
    // Verbundwert: markierter Ruf (`Completion(id: k, len: n)`).
    if r.ist_verbundwert() {
        return senke_verbundwert(k, r, span);
    }
    let pfad = match r.path() {
        Some(p) => p.clone(),
        None => {
            // Indirekter Ruf: Vertrag steht am Zeigertyp (Modell `callInd`).
            return senke_ruf_indirekt(k, r, span);
        }
    };
    let name = kurzname(&pfad);
    // Umwandlung (`u32(x)`, `bool(x)` …, Zucker `u13(x)`): ein Argument.
    if let Some((zll, zz)) = wandel_mit_zucker(&name) {
        if r.argumente.len() != 1 {
            weigere(k.s, "Y104", span, format!("conversion {name} with {} arguments", r.argumente.len()));
            return None;
        }
        let v = senke_expr(k, &r.argumente[0])?;
        let w = angleiche(k, v, &zll, zz)?;
        let mut w2 = w;
        w2.form = wandel_form(&name);
        return Some(w2);
    }
    // Erzeugte Tabellen-Operation (`Verzeichnis::insert(v, i)`).
    if pfad.teile.len() == 2 {
        let tab = pfad.teile[0].text.clone();
        let wort = pfad.teile[1].text.clone();
        if k.s.tab_ops.contains_key(&tab) && ["insert", "remove", "relabel"].contains(&wort.as_str()) {
            return senke_ops_ruf(k, &tab, &wort, r, span);
        }
    }
    // Geräte-Konstruktor (`Vtd(basis)`): die Basis IST die Adresse.
    if k.s.geraete.contains_key(&name) {
        if r.argumente.len() != 1 {
            weigere(k.s, "Y104", span, format!("device construction of {name} takes one base address"));
            return None;
        }
        let v = senke_expr(k, &r.argumente[0])?;
        let w = angleiche(k, v, &LlTyp::Int(64), Zeichen::U)?;
        let form = TypExpr::Pfad(pfad.clone());
        let mut w = w;
        w.form = Some(form);
        return Some(w);
    }
    // Transition (`wurzel_setzen(v)`): Bit-Schritte am Gerät (RMW, flüchtig).
    if let Some((dev, schritte)) = k.s.transitionen.get(&name).cloned() {
        return senke_transition(k, &dev, &schritte, r, span);
    }
    // Varianten-Konstruktor (`Fall(x)` / `Fall`): Tag plus Nutzlast-Bytes.
    if let Some((tname, fall_nr, nutz_opt)) = varianten_fall(k.s, &name) {
        return senke_varianten_wert(k, &tname, fall_nr, nutz_opt, r, span);
    }
    // `Some(x)` / `None`: Options-Wert als `{i32 Tag, [P x i8]}`.
    if name == "Some" || name == "None" {
        return senke_option_wert(k, &name, r, span);
    }
    // Tor-Ruf (direktes Tor für dieses Ziel — eigenes Modul zuerst).
    if let Some(pfad) = r.path() {
        if loese_tor(k.s, &k.modul.clone(), pfad).is_some() {
            return senke_tor_ruf(k, pfad, r, span);
        }
    }
    if k.s.fremde_tore.contains(&name) {
        weigere(k.s, "Y102", span, format!("gate {name} has no body for target {}", k.s.ziel.name));
        return None;
    }
    // Gewöhnliche Funktion (eigenes Modul zuerst, voller Pfad dann, kurz zuletzt).
    let voll = pfad.text();
    let (ename, sig) = match loese_fn(k.s, &k.modul.clone(), &pfad) {
        Some(x) => x,
        None => {
            // Tote Items (verweigerte Funktionen) tragen ihre Ursache schon.
            if k.s.tote_items.contains(&name) || k.s.tote_items.contains(&voll) {
                return None;
            }
            weigere(k.s, "Y104", span, format!("call of unknown function {name}"));
            return None;
        }
    };
    // Geister fallen am Ruf weg (je deklarierter Stelle — Stelle verbraucht).
    let mut args = Vec::new();
    let mut ai = 0usize;
    for (pi, ghost) in sig.geist_param.iter().enumerate() {
        let ae = match r.argumente.get(ai) {
            Some(e) => e,
            None => {
                weigere(k.s, "Y104", span, format!("missing argument {} for {name} (parameter {pi})", ai + 1));
                return None;
            }
        };
        ai += 1;
        if *ghost {
            continue;
        }
        let (pt, _pz) = match sig.params.get(args.len()) {
            Some(x) => x.clone(),
            None => {
                weigere(k.s, "Y104", span, format!("too many arguments for {name}"));
                return None;
            }
        };
        // Feld als Adresse an Zeiger-Parameter: verfallen (erstes Element).
        let v2 = verfall_arg(k, ae, &pt, span)?;
        args.push(v2.text);
    }
    let ret_text = match &sig.ret {
        Some((rt, _)) if *rt != LlTyp::Void => rt.text(),
        Some(_) => "void".to_string(),
        None => "void".to_string(),
    };
    let _ptexts: Vec<String> = sig.params.iter().map(|(t, _)| t.text()).collect();
    match &sig.ret {
        Some((rt, _)) if *rt != LlTyp::Void => {
            let t = k.tmp();
            let argtexte: Vec<String> = sig.params.iter().zip(args.iter()).map(|((t, _), a)| format!("{} {a}", t.text())).collect();
            k.zeile(&format!(
                "{t} = call {} {}({})",
                ret_text,
                gname(&ename),
                argtexte.join(", ")
            ));
            Some(Wert { typ: rt.clone(), zeichen: Zeichen::Egal, text: t, form: sig.ret_form.clone() })
        }
        _ => {
            let argtexte: Vec<String> = sig.params.iter().zip(args.iter()).map(|((t, _), a)| format!("{} {a}", t.text())).collect();
            k.zeile(&format!("call void {}({})", gname(&ename), argtexte.join(", ")));
            None
        }
    }
}

/// Argument an Parameter: Zeiger-Parameter verfallen (Adresse direkt — nie erst
/// laden: ein geladenes Feld ist ein WERT, kein Zeiger mehr).
fn verfall_arg(k: &mut Koerper, ae: &Expr, pt: &LlTyp, span: Span) -> Option<Wert> {
    if *pt == LlTyp::Ptr {
        if let ExprArt::Ort(o) = &ae.art {
            let p = adresse_von_ort(k, o)?;
            match &p.ll {
                LlTyp::Feld(_, _) => {
                    let t = k.tmp();
                    k.zeile(&format!(
                        "{t} = getelementptr {}, ptr {}, i32 0, i32 0",
                        p.ll.text(),
                        p.addr
                    ));
                    return Some(Wert { typ: LlTyp::Ptr, zeichen: Zeichen::Egal, text: t, form: p.form });
                }
                LlTyp::Benannt(n) if n.starts_with("gabstr") => {
                    let t = k.tmp();
                    k.zeile(&format!("{t} = getelementptr %{n}, ptr {}, i32 0, i32 1, i32 0", p.addr));
                    return Some(Wert { typ: LlTyp::Ptr, zeichen: Zeichen::Egal, text: t, form: p.form });
                }
                LlTyp::Ptr => {
                    let t = k.tmp();
                    k.zeile(&format!("{t} = load ptr, ptr {}, align 8", p.addr));
                    return Some(Wert { typ: LlTyp::Ptr, zeichen: Zeichen::Egal, text: t, form: p.form });
                }
                _ => {
                    weigere(k.s, "Y104", span, "scalar at pointer parameter".to_string());
                    return None;
                }
            }
        }
        let v = senke_expr(k, ae)?;
        if v.typ == LlTyp::Ptr {
            return Some(v);
        }
        weigere(k.s, "Y104", span, "non-pointer at pointer parameter".to_string());
        return None;
    }
    let v = senke_expr_mit(k, ae, Some((pt, Zeichen::Egal)))?;
    angleiche_mit_weigere(k, v, pt, span)
}

/// (Typname, Fallnummer, Nutzlast-Typ) hinter einem Konstruktornamen.
fn varianten_fall(s: &Senke, name: &str) -> Option<(String, u32, Option<TypExpr>)> {
    for (tname, (faelle, _)) in &s.variant_typen {
        for (i, (fname, nutz)) in faelle.iter().enumerate() {
            if fname == name {
                return Some((tname.clone(), i as u32, nutz.clone()));
            }
        }
    }
    None
}

/// Verbundwert (`Name(feld: wert, …)`): `insertvalue`-Kette aus `undef`.
fn senke_verbundwert(k: &mut Koerper, r: &Ruf, span: Span) -> Option<Wert> {
    let pfad = r.path()?.clone();
    let name = kurzname(&pfad);
    // Rekordname hinter Alias her.
    let rec_name = {
        let mut n = name.clone();
        if let Some(seite) = k.s.aliase.get(&n).cloned() {
            if let TypExpr::Pfad(p) = grundform(k.s, &seite) {
                if let Some(e) = p.einfach() {
                    n = e.text.clone();
                }
            }
        }
        n
    };
    let felder = match k.s.rekorde.get(&rec_name).cloned() {
        Some(f) => f,
        None => {
            weigere(k.s, "Y104", span, format!("record construction of unknown {name}"));
            return None;
        }
    };
    if r.marken.len() != r.argumente.len() {
        weigere(k.s, "Y104", span, "record construction with unnamed arguments".to_string());
        return None;
    }
    // Marke → Wert, in Deklarationsordnung.
    let mut gegeben: HashMap<String, Expr> = HashMap::new();
    for (m, a) in r.marken.iter().zip(r.argumente.iter()) {
        gegeben.insert(m.text.clone(), a.clone());
    }
    // Verbundwerte immer breit (Layouts sind einig — siehe `verenge_form`).
    sorge_typdef(k.s, &rec_name, false);
    let lname = layout_name(&rec_name, false);
    // Feldtypen in Ordnung (für insertvalue-Typen) — breit wie das Layout.
    let alt_eng = k.s.eng_modus;
    k.s.eng_modus = false;
    let mut fts = Vec::new();
    for (fname, ftyp) in &felder {
        let (fll, _) = senke_typ(k.s, ftyp)?;
        let _ = fname;
        fts.push(fll);
    }
    k.s.eng_modus = alt_eng;
    let mut cur = "undef".to_string();
    for (i, (fname, _)) in felder.iter().enumerate() {
        let ae = match gegeben.get(fname) {
            Some(e) => e.clone(),
            None => {
                weigere(k.s, "Y104", span, format!("record construction of {name} without field {fname}"));
                return None;
            }
        };
        let v = senke_expr(k, &ae)?;
        let fll = fts[i].clone();
        let w = angleiche(k, v, &fll, Zeichen::Egal)?;
        let t = k.tmp();
        k.zeile(&format!("{t} = insertvalue %{lname} {cur}, {} {}, {i}", fll.text(), w.text));
        cur = t;
    }
    Some(Wert { typ: LlTyp::Benannt(lname), zeichen: Zeichen::Egal, text: cur, form: Some(TypExpr::Pfad(pfad)) })
}

/// Varianten-Wert: `{i32 Tag, [P x i8]}` — Tag plus Nutzlast in die Bytes.
fn senke_varianten_wert(
    k: &mut Koerper,
    tname: &str,
    fall_nr: u32,
    nutz_opt: Option<TypExpr>,
    r: &Ruf,
    span: Span,
) -> Option<Wert> {
    sorge_variante(k.s, tname, false);
    let lname = layout_name(tname, false);
    let groesste = k.s.variant_typen.get(tname).map(|(_, g)| *g).unwrap_or(0);
    let mut cur = "undef".to_string();
    let t0 = k.tmp();
    k.zeile(&format!("{t0} = insertvalue %{lname} {cur}, i32 {fall_nr}, 0"));
    cur = t0;
    if let Some(nt) = nutz_opt {
        if r.argumente.len() != 1 {
            weigere(k.s, "Y104", span, "variant case with payload needs one argument".to_string());
            return None;
        }
        let v = senke_expr(k, &r.argumente[0])?;
        let (nll, _) = senke_typ(k.s, &nt)?;
        let w = angleiche(k, v, &nll, Zeichen::Egal)?;
        // Nutzlast in die Bytes: über Speicher und Ladung (Größe trägt der Typ).
        let slot = k.alloca(&LlTyp::Benannt(lname.clone()).text());
        k.zeile(&format!("store %{lname} {cur}, ptr {slot}, align 8"));
        let pp = k.tmp();
        k.zeile(&format!("{pp} = getelementptr %{lname}, ptr {slot}, i32 0, i32 1"));
        let pc = k.tmp();
        k.zeile(&format!("{pc} = getelementptr i8, ptr {pp}, i64 0"));
        k.zeile(&format!("store {} {}, ptr {pc}, align 1", nll.text(), w.text));
        let t1 = k.tmp();
        k.zeile(&format!("{t1} = load %{lname}, ptr {slot}, align 8"));
        cur = t1;
        let _ = groesste;
    } else if !r.argumente.is_empty() {
        weigere(k.s, "Y104", span, "variant case without payload takes no argument".to_string());
        return None;
    }
    Some(Wert { typ: LlTyp::Benannt(lname), zeichen: Zeichen::Egal, text: cur, form: None })
}

/// `Some(x)` / `None` als `%gabopt` (Tag 1/0, Index in den Bytes).
fn senke_option_wert(k: &mut Koerper, name: &str, r: &Ruf, span: Span) -> Option<Wert> {
    // Die Hülle bestimmt P — hier: Zeigerbreite (8). Der Prüfer hält die Form;
    // das Layout trägt jede Nutzlast bis 8 Bytes (größere fallen benannt).
    sorge_gabopt(k.s);
    let gabopt = LlTyp::Benannt("gabopt".to_string());
    if name == "None" {
        if !r.argumente.is_empty() {
            weigere(k.s, "Y104", span, "None takes no argument".to_string());
            return None;
        }
        let t = k.tmp();
        k.zeile(&format!("{t} = insertvalue %gabopt undef, i32 0, 0"));
        return Some(Wert { typ: gabopt, zeichen: Zeichen::Egal, text: t, form: None });
    }
    if r.argumente.len() != 1 {
        weigere(k.s, "Y104", span, "Some needs one argument".to_string());
        return None;
    }
    let v = senke_expr(k, &r.argumente[0])?;
    let groesse = match groesse_von_ll(k.s, &v.typ) {
        Some(g) if g <= 8 => g,
        _ => {
            weigere(k.s, "Y104", span, "Some payload larger than 8 bytes".to_string());
            return None;
        }
    };
    let t0 = k.tmp();
    k.zeile(&format!("{t0} = insertvalue %gabopt undef, i32 1, 0"));
    let slot = k.alloca("%gabopt");
    k.zeile(&format!("store %gabopt {t0}, ptr {slot}, align 8"));
    let pp = k.tmp();
    k.zeile(&format!("{pp} = getelementptr %gabopt, ptr {slot}, i32 0, i32 1"));
    let pc = k.tmp();
    k.zeile(&format!("{pc} = getelementptr i8, ptr {pp}, i64 0"));
    k.zeile(&format!("store {} {}, ptr {pc}, align 1", v.typ.text(), v.text));
    let t1 = k.tmp();
    k.zeile(&format!("{t1} = load %gabopt, ptr {slot}, align 8"));
    let _ = groesse;
    Some(Wert { typ: gabopt, zeichen: Zeichen::Egal, text: t1, form: None })
}

/// Tor-Ruf: Nummer plus Argumente als `asm sideeffect` (Ziel wählt die Schablone).
fn senke_tor_ruf(k: &mut Koerper, pfad: &Pfad, r: &Ruf, span: Span) -> Option<Wert> {
    let name = kurzname(pfad);
    let tor = match loese_tor(k.s, &k.modul.clone(), pfad) {
        Some((_, t)) => t,
        None => {
            weigere(k.s, "Y102", span, format!("gate {name} has no body for target {}", k.s.ziel.name));
            return None;
        }
    };
    if r.argumente.len() != tor.param_typen.len() {
        weigere(k.s, "Y104", span, format!("gate {name} takes {} arguments, got {}", tor.param_typen.len(), r.argumente.len()));
        return None;
    }
    // Grenzen: Nummer falten, Argumente angleichen.
    let mut ops: Vec<String> = vec![format!("i64 {}", tor.nummer)];
    for (ae, (pt, _)) in r.argumente.iter().zip(tor.param_typen.iter()) {
        // Zeiger-Argument: verfallen (erstes Element hinter dem Zeiger).
        let w = verfall_arg(k, ae, pt, span)?;
        let ww = angleiche_mit_weigere(k, w, &LlTyp::Int(64), span)?;
        ops.push(format!("i64 {}", ww.text));
    }
    // Bindung: `={ret},{num-reg},{in-regs}…` plus Clobbers plus Speicher.
    let mut bind: Vec<String> = Vec::new();
    bind.push(format!("={{{}}}", tor.ret_reg));
    // Nummer-Register: erstes Eingaberegister der ABI-Ordnung ist die Nummer?
    // Nein — die Nummer reist als ERSTER Operand im Nummernregister.
    let num_reg = if k.s.ziel.name == "x86_64" { "rax" } else { "x8" };
    bind.push(format!("{{{num_reg}}}"));
    for (reg, _) in &tor.eingaben {
        bind.push(format!("{{{reg}}}"));
    }
    for c in &tor.clobbers {
        bind.push(format!("~{{{c}}}"));
    }
    bind.push("~{memory}".to_string());
    let constraint = bind.join(",");
    // Stapeltor: im Kind springt die Befehlsfolge in die ausgelagerte Region (`llvm/stapeltor.rs`).
    let template: String = match &tor.stapel {
        Some(st) => stapeltor::vorbereiten(k, &tor, st, r, span)?,
        None => tor.template.to_string(),
    };
    if tor.nie {
        // Ein Aufruf ohne Antwort (`void`) trägt keinen Ausgang: `={rax}` an `void` ist ein
        // `llc`-Fehler ("could not allocate output register").
        let ohne_ausgang = constraint.split_once(',').map(|(_, r)| r.to_string()).unwrap_or_default();
        k.zeile(&format!(
            "call void asm sideeffect \"{template}\", \"{ohne_ausgang}\"({})",
            ops.join(", ")
        ));
        k.zeile("unreachable");
        k.beendet = true;
        return None;
    }
    match &tor.ret {
        Some((rt, _)) if *rt != LlTyp::Void => {
            // Die Anweisung antwortet immer i64 (Antwortregister); Dekodierung danach.
            let raw = k.tmp();
            k.zeile(&format!(
                "{raw} = call i64 asm sideeffect \"{template}\", \"{constraint}\"({})",
                ops.join(", ")
            ));
            match tor.or_nutz.clone() {
                Some(or) => tor_antwort_dekodieren(k, &tor, &or, &raw, span),
                None => {
                    // i64-Antwort an schmälere Deklaration: trunc am Gebrauch.
                    let w = angleiche(
                        k,
                        Wert { typ: LlTyp::Int(64), zeichen: Zeichen::U, text: raw, form: None },
                        rt,
                        Zeichen::U,
                    )?;
                    Some(w)
                }
            }
        }
        _ => {
            k.zeile(&format!(
                "call void asm sideeffect \"{template}\", \"{constraint}\"({})",
                ops.join(", ")
            ));
            None
        }
    }
}

/// Rohe Tor-Antwort in den Kanalwert: errno-Arme zuerst, sonst Ok.
fn tor_antwort_dekodieren(k: &mut Koerper, tor: &Tor, or: &OrKanal, raw: &str, span: Span) -> Option<Wert> {
    let st = or_struct(or.p);
    if tor.errors.is_empty() {
        // Kein errno-Blatt: roh ist der Wert (Kanal ohne Dekodierung gibt es nicht —
        // ohne `errors` wäre der Kanal nie gefallen; hierher kommt nur der volle).
        let v = Wert { typ: LlTyp::Int(64), zeichen: Zeichen::U, text: raw.to_string(), form: None };
        return or_ok_wert(k, or, v);
    }
    let ende = k.block("tor_ende");
    let ok_arm = k.block("tor_ok");
    // Kette: jeder errno-Arm prüft `raw == -num`.
    let mut naechste: Option<String> = None;
    let mut err_werte: Vec<(String, String)> = Vec::new();
    for (num, rval) in &tor.errors {
        if let Some(lbl) = naechste.take() {
            let _ = writeln!(k.text, "{lbl}:");
            k.beendet = false;
        }
        let neg = -num;
        let trifft = k.tmp();
        k.zeile(&format!("{trifft} = icmp eq i64 {raw}, {neg}"));
        let arm = k.block("tor_err");
        let weiter = k.block("tor_weiter");
        k.zeile(&format!("br i1 {trifft}, label %{arm}, label %{weiter}"));
        k.beendet = true;
        let _ = writeln!(k.text, "{arm}:");
        k.beendet = false;
        let ev = or_err_wert(k, or, &format!("{rval}"));
        k.zeile(&format!("br label %{ende}"));
        err_werte.push((arm.clone(), ev.text));
        k.beendet = true;
        naechste = Some(weiter);
    }
    if let Some(lbl) = naechste.take() {
        let _ = writeln!(k.text, "{lbl}:");
        k.beendet = false;
    }
    k.zeile(&format!("br label %{ok_arm}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{ok_arm}:");
    k.beendet = false;
    let v = Wert { typ: LlTyp::Int(64), zeichen: Zeichen::U, text: raw.to_string(), form: None };
    let okv = or_ok_wert(k, or, v)?;
    k.zeile(&format!("br label %{ende}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{ende}:");
    k.beendet = false;
    // Zusammenfluss: ein Phi über alle Arme.
    let mut arme: Vec<String> = err_werte.iter().map(|(l, t)| format!("[ {t}, %{l} ]")).collect();
    arme.push(format!("[ {}, %{ok_arm} ]", okv.text));
    let t = k.tmp();
    k.zeile(&format!("{t} = phi {} {}", st.text(), arme.join(", ")));
    let _ = span;
    Some(Wert { typ: st, zeichen: Zeichen::Egal, text: t, form: or.tform.clone() })
}

// ===================================================================================
// Anweisungen
// ===================================================================================

fn senke_block(k: &mut Koerper, b: &Block) {
    k.oeffne();
    for st in &b.anweisungen {
        if k.beendet {
            break;
        }
        senke_stmt(k, st);
    }
    k.schliesse();
}

/// Sperren am Ausgang freigeben (jeder Ausgang — Ticket: `bereit += 1`).
///
/// **Der Stapel bleibt stehen.** Die Freigabe schreibt Text für EINEN Pfad (den, der hier
/// endet); der andere Pfad hinter einem `if … { return }` hält die Sperre weiter und gibt
/// sie am Blockende selbst frei. Früher leerte dieser Aufruf den Stapel, und der Pfad ohne
/// `return` ließ die Sperre für immer genommen (gemessen 2026-10-17, ein zweiter Ruf
/// hing). Innen vor außen: bei maskierenden Sperren ist die Reihenfolge Pflicht.
fn sperren_freigeben(k: &mut Koerper) {
    sperren_freigeben_ab(k, 0);
}

/// Wie `sperren_freigeben`, aber nur die Sperren über `tiefe` (`leave`/`next`).
fn sperren_freigeben_ab(k: &mut Koerper, tiefe: usize) {
    let halten: Vec<String> = k.sperren.iter().skip(tiefe).cloned().collect();
    for name in halten.iter().rev() {
        ticket_freigabe(k, name);
    }
}

/// `return` senken (die Sperren gibt der Aufrufer VOR dem Abschluss frei, `return_freigabe`).
fn senke_return(k: &mut Koerper, e: &Option<Expr>, span: Span) {
    match e {
        Some(x) => {
            // Schwanzruf: springen statt rufen (kein Rahmen, kein Überlauf).
            if schwanz_ruf(k, x, span).is_some() {
                return;
            }
            // Geist-Antwort: der Wert ist beweisführend — Rückkehr leer.
            if k.geist_rueck {
                k.zeile("ret void");
                k.beendet = true;
                return;
            }
            // Tausch-Rumpf: `return` ist das neue Wort (kein Ausgang).
            if let Some((neu_slot, nll, weiter)) = k.tausch_rueck.clone() {
                let v = match senke_expr(k, x) {
                    Some(v) => v,
                    None => return,
                };
                let w = match angleiche_mit_weigere(k, v, &nll, span) {
                    Some(w) => w,
                    None => return,
                };
                k.zeile(&format!("store {} {}, ptr {neu_slot}, align {}", nll.text(), w.text, nat_align(&nll)));
                k.zeile(&format!("br label %{weiter}"));
                k.beendet = true;
                return;
            }
            if let Some((rt, _)) = k.rueck.clone() {
                if rt == LlTyp::Void {
                    weigere(k.s, "Y104", span, "return of a value from a void function".to_string());
                    return;
                }
                // Kanalfunktion: Grund → Fehler, Wert → Ok.
                if let Some(or) = k.or_nutz.clone() {
                    senke_return_kanal(k, x, &or, &rt, span);
                    k.beendet = true;
                    return;
                }
                let v = match senke_expr_mit(k, x, Some((&rt, Zeichen::Egal))) {
                    Some(v) => v,
                    None => return,
                };
                let w = match angleiche_mit_weigere(k, v, &rt, span) {
                    Some(w) => w,
                    None => return,
                };
                // `ensures`-Annahmen über der Antwort (was sich senken lässt).
                if let Some(annahmen) = k.s.fns.get(&k.funktionsname).map(|f| f.vertrag_ensures.clone()) {
                    let alt = k.ergebnis_wert.clone();
                    k.ergebnis_wert = Some(w.clone());
                    for pred in &annahmen {
                        nehme_an(k, pred, "ensures");
                    }
                    k.ergebnis_wert = alt;
                }
                k.zeile(&format!("ret {} {}", rt.text(), w.text));
            } else {
                weigere(k.s, "Y104", span, "return of a value".to_string());
                return;
            }
        }
        None => {
            k.zeile("ret void");
        }
    }
    k.beendet = true;

}

/// Sperrfreigabe unmittelbar vor der letzten Zeile (dem Abschluss) des eben gesenkten
/// `return`: `ret`, oder `br` beim Tausch-Rumpf und beim Schwanzruf.
fn return_freigabe(k: &mut Koerper, von: usize) {
    if !k.beendet || k.sperren.is_empty() || k.text.len() <= von {
        return;
    }
    let ohne_ende = k.text.trim_end_matches('\n').len();
    let Some(zeilenanfang) = k.text[..ohne_ende].rfind('\n').map(|i| i + 1) else {
        return;
    };
    if zeilenanfang < von {
        return;
    }
    let abschluss = k.text.split_off(zeilenanfang);
    k.beendet = false;
    sperren_freigeben(k);
    k.beendet = true;
    k.text.push_str(&abschluss);
}

fn senke_stmt(k: &mut Koerper, st: &Stmt) {
    k.kind.stmt = Some(st.span);
    match &st.art {
        StmtArt::Let(l) => senke_let(k, l, st.span),
        StmtArt::LetSonst(l) => senke_let_sonst(k, l, st.span),
        StmtArt::Zuweisung(z) => senke_zuweisung(k, z, st.span),
        StmtArt::Wenn(w) => senke_wenn(k, w),
        StmtArt::Match(m) => senke_match(k, m, st.span),
        StmtArt::Schleife(s) => senke_schleife(k, s, st.span),
        StmtArt::Bricht(b) => {
            // `breaking`: Nachweis-Buchhaltung — der Rumpf läuft.
            senke_block(k, &b.rumpf);
        }
        StmtArt::Narrow(n) => senke_narrow(k, n, st.span),
        StmtArt::Sperrt(s) => senke_sperrt(k, s, st.span),
        StmtArt::Observiert(o) => {
            // RCU-Leseseite: Zaun plus Rumpf (kein Ausschluss, keine Nahme).
            k.zeile("fence acquire");
            senke_block(k, &o.rumpf);
            k.zeile("fence acquire");
        }
        StmtArt::Leave(mark) => {
            let ctx = match schleife_fuer(&k.schleifen, &mark.text) {
                Some(c) => c,
                None => {
                    weigere(k.s, "Y103", st.span, format!("leave outside a loop ({})", mark.text));
                    return;
                }
            };
            // Durch `traverse` hindurch (keine Marke dort) — Sperren freigeben.
            sperren_freigeben_ab(k, ctx.sperr_tiefe);
            k.zeile(&format!("br label %{}", ctx.danach));
            k.beendet = true;
        }
        StmtArt::Next(mark) => {
            let ctx = match schleife_fuer(&k.schleifen, &mark.text) {
                Some(c) => c,
                None => {
                    weigere(k.s, "Y103", st.span, format!("next outside a loop ({})", mark.text));
                    return;
                }
            };
            sperren_freigeben_ab(k, ctx.sperr_tiefe);
            k.zeile(&format!("br label %{}", ctx.weiter));
            k.beendet = true;
        }
        StmtArt::Publish(p) => senke_publish(k, p, st.span),
        StmtArt::AwaitLoad(a) => senke_await(k, a, st.span),
        StmtArt::Exchange(e) => senke_exchange(k, e, st.span),
        StmtArt::Return(e) => {
            // **Zuerst der Wert, dann die Freigabe.** Ein `return Z` unter `locks` liest `Z`
            // noch unter der Sperre; die Freigabe steht darum unmittelbar VOR dem Abschluss
            // dieses Pfades und nicht davor (bei maskierenden Sperren stünde sonst die Lesung
            // mit freien Unterbrechungen).
            let von = k.text.len();
            senke_return(k, e, st.span);
            return_freigabe(k, von);
        }
        StmtArt::Ruf(r) => {
            let _ = senke_ruf(k, r, st.span);
        }
        StmtArt::LibraryCall(_) => {
            weigere(k.s, "Y104", st.span, "library call".to_string());
        }
        StmtArt::Alloc(a) => senke_alloc(k, a, st.span),
        StmtArt::ResetArena(name) => {
            if k.s.arenen.contains_key(&name.text) {
                memory::reset(k, &name.text, st.span);
            } else {
                weigere(k.s, "Y103", st.span, format!("reset of unknown arena {}", name.text));
            }
        }
        StmtArt::ResetSlot(r) => memory::reset_range(k, r, st.span),
        StmtArt::Grow(g) => senke_grow(k, g, st.span),
        // **TODO §1-B:** the slot release (intrusive free list).
        StmtArt::Frei(f) => senke_frei(k, f, st.span),
        StmtArt::Child(b) => stapeltor::kind_stmt(k, b),
        StmtArt::Start(s) => senke_start(k, s, st.span),
    }
}

/// Angleichen oder benannt verweigern (kein stilles `None` an Rufstellen).
fn angleiche_mit_weigere(k: &mut Koerper, v: Wert, ziel: &LlTyp, span: Span) -> Option<Wert> {
    match angleiche(k, v, ziel, Zeichen::Egal) {
        Some(w) => Some(w),
        None => {
            weigere(k.s, "Y104", span, "value of this type at this place".to_string());
            None
        }
    }
}

fn senke_let(k: &mut Koerper, l: &LetStmt, span: Span) {
    // Geist-Bindung: Dummy-Byte (Marken sind beweisführend — kein Laufzeitwert).
    if l.typ.as_ref().is_some_and(|t| ist_geist(k.s, t)) {
        let p = k.alloca("i8");
        k.zeile(&format!("store i8 0, ptr {p}, align 1"));
        k.lege_an(
            l.name.text.clone(),
            Bindung { ptr: p, ll: LlTyp::Int(8), zeichen: Zeichen::Egal, form: l.typ.clone(), fluechtig: false },
        );
        return;
    }
    // Erklärte Form zuerst (Kettenliterale bauen danach ihren Struct).
    let vorab: Option<(LlTyp, Zeichen)> = match &l.typ {
        Some(t) => match senke_typ(k.s, t) {
            Some(x) => Some(x),
            None => return,
        },
        None => None,
    };
    let v = match match &vorab {
        Some((ll, z)) => senke_expr_mit(k, &l.wert, Some((ll, *z))),
        None => senke_expr(k, &l.wert),
    } {
        Some(v) => v,
        None => return,
    };
    // Erklärte Form schlägt den Wert (Annotation bindet).
    let (ll, z, form) = match (&l.typ, vorab) {
        (Some(t), Some((ll, z))) => (ll, z, Some(t.clone())),
        _ => (v.typ.clone(), v.zeichen, v.form.clone()),
    };
    let w = match angleiche_mit_weigere(k, v, &ll, span) {
        Some(w) => w,
        None => return,
    };
    let p = k.alloca(&ll.text());
    k.zeile(&format!("store {} {}, ptr {p}, align {}", ll.text(), w.text, nat_align(&ll)));
    let fl = ist_fluechtig(k.s, &form);
    k.lege_an(l.name.text.clone(), Bindung { ptr: p, ll, zeichen: z, form , fluechtig: fl });
    let _ = l.veraenderlich;
}

fn senke_let_sonst(k: &mut Koerper, l: &LetSonst, span: Span) {
    // `let x = f() else (e) { … }`: Ruf mit Fehlerkanal — der Kanal ist `Y102`.
    // Orts-Quelle (Option auspacken): Tag prüfen, Nutzlast binden.
    match &l.quelle {
        LetQuelle::Ruf(r) => {
            senke_let_sonst_ruf(k, l, r, span);
        }
        LetQuelle::Ort(o) => {
            let p = match adresse_von_ort(k, o) {
                Some(p) => p,
                None => return,
            };
            // Tag laden (Feld 0), gegen 0 halten, Nutzlast (Feld 1) binden.
            let t = k.tmp();
            k.zeile(&format!("{t} = load i32, ptr {}, align 4", p.addr));
            let ok = k.tmp();
            k.zeile(&format!("{ok} = icmp ne i32 {t}, 0"));
            let weiter = k.block("sonst_weiter");
            let sonst = k.block("sonst_else");
            k.zeile(&format!("br i1 {ok}, label %{weiter}, label %{sonst}"));
            k.beendet = true;
            let _ = writeln!(k.text, "{sonst}:");
            k.beendet = false;
            senke_block(k, &l.sonst);
            if !k.beendet {
                k.zeile(&format!("br label %{weiter}"));
            }
            k.beendet = true;
            let _ = writeln!(k.text, "{weiter}:");
            k.beendet = false;
            // Nutzlast-Zeiger binden (Byte 4 …): der Name trägt die Adresse.
            let pp = k.tmp();
            k.zeile(&format!("{pp} = getelementptr {{ i32, [8 x i8] }}, ptr {}, i32 0, i32 1", p.addr));
            // Typ aus der Annotation (oder Byte).
            let (ell, ez, eform) = match &l.typ {
                Some(t) => match senke_typ(k.s, t) {
                    Some((ll, z)) => (ll, z, Some(t.clone())),
                    None => return,
                },
                None => (LlTyp::Int(8), Zeichen::U, None),
            };
            let pc = k.tmp();
            k.zeile(&format!("{pc} = getelementptr i8, ptr {pp}, i64 0"));
            let lv = k.tmp();
            k.zeile(&format!("{lv} = load {}, ptr {pc}, align 1", ell.text()));
            let slot = k.alloca(&ell.text());
            k.zeile(&format!("store {} {lv}, ptr {slot}, align {}", ell.text(), nat_align(&ell)));
            k.lege_an(l.name.text.clone(), Bindung { ptr: slot, ll: ell, zeichen: ez, form: eform , fluechtig: false });
            let _ = l.fehlername;
        }
    }
}

fn senke_zuweisung(k: &mut Koerper, z: &Zuweisung, span: Span) {
    let p = match adresse_von_ort_mit(k, &z.ziel, true) {
        Some(p) => p,
        None => return,
    };
    if p.port && !matches!(z.op, ZuwOp::Setzt) {
        // `in` und `out` sind zwei Befehle ohne etwas dazwischen, das ein Ort sein könnte
        // (LANGUAGE.md; `gift/654` im Prüfer): die Verbundzuweisung hat hier keine Form.
        weigere(k.s, "Y103", span, "compound assignment at a port register: `in` and `out` are two instructions".to_string());
        return;
    }
    match z.op {
        ZuwOp::Setzt => {
            // Bitfeld-Speicher: lesen-modifizieren-schreiben (flüchtig beidseitig).
            if let Some((lo, breite)) = p.bit {
                let v = match senke_expr(k, &z.wert) {
                    Some(v) => v,
                    None => return,
                };
                let bw = p.ll.breite().unwrap_or(32);
                let al = nat_align(&p.ll);
                let w = if p.port {
                    portraum::lesen(k, &p.addr, &p.ll)
                } else {
                    let w = k.tmp();
                    k.zeile(&format!("{w} = load volatile {}, ptr {}, align {al}", p.ll.text(), p.addr));
                    w
                };
                let maske: u128 = if breite >= 128 { u128::MAX } else { (1u128 << breite) - 1 };
                let geloeschte_maske = !(maske << lo) & ((1u128 << bw) - 1);
                let vv = match angleiche(k, v, &LlTyp::Int(bw), Zeichen::U) {
                    Some(w) => w,
                    None => {
                        weigere(k.s, "Y104", span, "bit field value".to_string());
                        return;
                    }
                };
                let beschnitten = k.tmp();
                k.zeile(&format!("{beschnitten} = and i{bw} {}, {maske}", vv.text));
                let verschoben = k.tmp();
                k.zeile(&format!("{verschoben} = shl i{bw} {beschnitten}, {lo}"));
                let behalten = k.tmp();
                k.zeile(&format!("{behalten} = and i{bw} {w}, {geloeschte_maske}"));
                let neu = k.tmp();
                k.zeile(&format!("{neu} = or i{bw} {behalten}, {verschoben}"));
                if p.port {
                    portraum::schreiben(k, &p.addr, &p.ll, &neu);
                } else {
                    k.zeile(&format!("store volatile {} {neu}, ptr {}, align {al}", p.ll.text(), p.addr));
                }
                return;
            }
            let v = match senke_expr_mit(k, &z.wert, Some((&p.ll, p.zeichen))) {
                Some(v) => v,
                None => return,
            };
            if p.port {
                let w = match angleiche_mit_weigere(k, v, &p.ll, span) {
                    Some(w) => w,
                    None => return,
                };
                portraum::schreiben(k, &p.addr, &p.ll, &w.text);
                return;
            }
            // `bool`-Zelle als Byte: `zext` an der Grenze (trunc beim Laden).
            let (text, zugriff) = if p.ll == LlTyp::Int(8) && matches!(p.form.clone().map(|f| grundform(k.s, &f)), Some(TypExpr::Bool(_))) {
                let w = angleiche(k, v, &LlTyp::Int(1), Zeichen::Egal).and_then(|w| {
                    let t = k.tmp();
                    k.zeile(&format!("{t} = zext i1 {} to i8", w.text));
                    Some(t)
                });
                match w {
                    Some(t) => (t, LlTyp::Int(8)),
                    None => return,
                }
            } else {
                let w = match angleiche_mit_weigere(k, v, &p.ll, span) {
                    Some(w) => w,
                    None => return,
                };
                (w.text, p.ll.clone())
            };
            let al = nat_align(&p.ll);
            let meta = if p.fluechtig { String::new() } else { zugriff_meta(k, &p.ll, &p.form, false, &p.slot, &p.rekord, p.zeichen) };
            let vol = if p.fluechtig { " volatile" } else { "" };
            match &p.atomar {
                Some(ordnung) => {
                    k.zeile(&format!(
                        "store atomic{vol} {} {text}, ptr {} {ordnung}, align {al}{meta}",
                        zugriff.text(),
                        p.addr
                    ));
                }
                None => {
                    k.zeile(&format!("store{vol} {} {text}, ptr {}, align {al}{meta}", zugriff.text(), p.addr));
                }
            }
        }
        ZuwOp::Plus | ZuwOp::Minus => {
            // `+=` / `-=`: laden, rechnen, speichern (atomar: `atomicrmw`).
            let plus = matches!(z.op, ZuwOp::Plus);
            let v = match senke_expr(k, &z.wert) {
                Some(v) => v,
                None => return,
            };
            let w = match angleiche_mit_weigere(k, v, &p.ll, span) {
                Some(w) => w,
                None => return,
            };
            let al = nat_align(&p.ll);
            match (&p.atomar, &p.ll) {
                (Some(ordnung), LlTyp::Int(b)) => {
                    k.zeile(&format!(
                        "atomicrmw {} ptr {}, {} {} {ordnung}, align {al}",
                        if plus { "add" } else { "sub" },
                        p.addr,
                        p.ll.text(),
                        w.text
                    ));
                    let _ = b;
                }
                _ => {
                    let t = k.tmp();
                    k.zeile(&format!("{t} = load {}, ptr {}, align {al}", p.ll.text(), p.addr));
                    let r = k.tmp();
                    k.zeile(&format!(
                        "{r} = {} {} {t}, {}",
                        if plus { "add" } else { "sub" },
                        p.ll.text(),
                        w.text
                    ));
                    let meta = zugriff_meta(k, &p.ll, &p.form, false, &p.slot, &p.rekord, p.zeichen);
                    k.zeile(&format!("store {} {r}, ptr {}, align {al}{meta}", p.ll.text(), p.addr));
                }
            }
        }
        ZuwOp::Und | ZuwOp::Oder => {
            weigere(k.s, "Y103", span, "bitwise assignment".to_string());
        }
    }
}

fn senke_wenn(k: &mut Koerper, w: &WennStmt) {
    let danach = k.block("wenn_ende");
    let mut naechste_pruefung: Option<String> = None;
    for (i, (cond, body)) in w.zweige.iter().enumerate() {
        if let Some(lbl) = naechste_pruefung.take() {
            let _ = writeln!(k.text, "{lbl}:");
            k.beendet = false;
        }
        let v = match senke_expr(k, cond) {
            Some(v) => v,
            None => return,
        };
        let c = match als_bool(k, v) {
            Some(c) => c,
            None => {
                weigere(k.s, "Y104", cond.span, "non-boolean condition".to_string());
                return;
            }
        };
        let dann = k.block("wenn_dann");
        let sonst = if i + 1 < w.zweige.len() || w.sonst.is_some() {
            k.block("wenn_sonst")
        } else {
            danach.clone()
        };
        k.zeile(&format!("br i1 {c}, label %{dann}, label %{sonst}"));
        k.beendet = true;
        let _ = writeln!(k.text, "{dann}:");
        k.beendet = false;
        senke_block(k, body);
        if !k.beendet {
            k.zeile(&format!("br label %{danach}"));
        }
        k.beendet = true;
        if sonst != danach {
            naechste_pruefung = Some(sonst);
        }
    }
    if let Some(sonst) = w.sonst.clone() {
        if let Some(lbl) = naechste_pruefung.take() {
            let _ = writeln!(k.text, "{lbl}:");
            k.beendet = false;
        }
        senke_block(k, &sonst);
        if !k.beendet {
            k.zeile(&format!("br label %{danach}"));
        }
        k.beendet = true;
    }
    let _ = writeln!(k.text, "{danach}:");
    k.beendet = false;
}

fn senke_match(k: &mut Koerper, m: &MatchStmt, span: Span) {
    // Ganzzahlig (alle Arme `intpat`): Kette aus Vergleichen — Abdeckung hält der
    // Prüfer (`N411`–`N414`), darum endet die Kette in `unreachable`.
    let ganzzahlig = !m.zweige.is_empty() && m.zweige.iter().all(|z| z.intpat.is_some());
    if ganzzahlig {
        let v = match senke_expr(k, &m.gegenstand) {
            Some(v) => v,
            None => return,
        };
        let (w, _) = match gemein_int(&v, &Wert::int("0".to_string(), 64, Zeichen::U)) {
            Some(x) => x,
            None => {
                weigere(k.s, "Y106", span, "integer match over non-integer".to_string());
                return;
            }
        };
        let vv = match angleiche(k, v, &LlTyp::Int(w), Zeichen::Egal) {
            Some(v) => v,
            None => return,
        };
        let ende = k.block("match_ende");
        let mut naechste: Option<String> = None;
        for zweig in &m.zweige {
            if let Some(lbl) = naechste.take() {
                let _ = writeln!(k.text, "{lbl}:");
                k.beendet = false;
            }
            let pat = zweig.intpat.clone().expect("ganzzahlig geprüft");
            let trifft = match pat {
                IntPat::Exact(b) => {
                    let val = if b.negative {
                        format!("-{}", b.value)
                    } else {
                        format!("{}", b.value)
                    };
                    let t = k.tmp();
                    k.zeile(&format!("{t} = icmp eq i{w} {}, {val}", vv.text));
                    t
                }
                IntPat::Range { lo, hi, exclusive } => {
                    let lo_v = if lo.negative { format!("-{}", lo.value) } else { format!("{}", lo.value) };
                    let hi_v = if hi.negative { format!("-{}", hi.value) } else { format!("{}", hi.value) };
                    let t1 = k.tmp();
                    k.zeile(&format!("{t1} = icmp sle i{w} {lo_v}, {}", vv.text));
                    let t2 = k.tmp();
                    let cmp = if exclusive { "slt" } else { "sle" };
                    k.zeile(&format!("{t2} = icmp {cmp} i{w} {}, {hi_v}", vv.text));
                    let t = k.tmp();
                    k.zeile(&format!("{t} = and i1 {t1}, {t2}"));
                    t
                }
            };
            let arm = k.block("match_arm");
            let weiter = k.block("match_weiter");
            k.zeile(&format!("br i1 {trifft}, label %{arm}, label %{weiter}"));
            k.beendet = true;
            let _ = writeln!(k.text, "{arm}:");
            k.beendet = false;
            senke_block(k, &zweig.rumpf);
            if !k.beendet {
                k.zeile(&format!("br label %{ende}"));
            }
            k.beendet = true;
            naechste = Some(weiter);
        }
        if let Some(lbl) = naechste.take() {
            let _ = writeln!(k.text, "{lbl}:");
            k.beendet = false;
        }
        // Abdeckung hält der Prüfer — hierher kommt kein Lauf.
        k.zeile("unreachable");
        k.beendet = true;
        let _ = writeln!(k.text, "{ende}:");
        k.beendet = false;
        return;
    }
    // Variante/Grund/Option: Marke laden, Arme vergleichen.
    let v = match senke_expr(k, &m.gegenstand) {
        Some(v) => v,
        None => return,
    };
    if v.typ == LlTyp::Benannt("gabopt".to_string()) {
        senke_match_option(k, m, &v, span);
        return;
    }
    // Tag als i32 lesen (Wert oder Zeiger auf Variante).
    let tag = match &v.typ {
        LlTyp::Benannt(_) | LlTyp::Anon(_) => {
            // Strukturwert: Marke ist Feld 0.
            let t = k.tmp();
            let slot = k.alloca(&v.typ.text());
            k.zeile(&format!("store {} {}, ptr {slot}, align 8", v.typ.text(), v.text));
            let pp = k.tmp();
            k.zeile(&format!("{pp} = getelementptr {}, ptr {slot}, i32 0, i32 0", v.typ.text()));
            k.zeile(&format!("{t} = load i32, ptr {pp}, align 4"));
            t
        }
        LlTyp::Int(32) => v.text.clone(),
        _ => {
            weigere(k.s, "Y106", span, "match over this form".to_string());
            return;
        }
    };
    // Typnamen bestimmen: Variante oder Grund.
    let faelle: Vec<(String, Option<TypExpr>)> = find_variant_fuer_tag(k.s, &v)
        .map(|(_, f, _)| f)
        .unwrap_or_default();
    let grund_faelle: Vec<(String, i128)> = find_grund_fuer_wert(k.s, &v).unwrap_or_default();
    if faelle.is_empty() && grund_faelle.is_empty() {
        weigere(k.s, "Y106", span, "match over this form".to_string());
        return;
    }
    let ende = k.block("match_ende");
    let mut naechste: Option<String> = None;
    for zweig in &m.zweige {
        if let Some(lbl) = naechste.take() {
            let _ = writeln!(k.text, "{lbl}:");
            k.beendet = false;
        }
        let nr: Option<i128> = faelle
            .iter()
            .position(|(n, _)| n == &zweig.variante.text)
            .map(|i| i as i128)
            .or_else(|| grund_faelle.iter().find(|(n, _)| n == &zweig.variante.text).map(|(_, w)| *w));
        let nr = match nr {
            Some(n) => n,
            None => {
                weigere(k.s, "Y106", zweig.span, format!("unknown case {}", zweig.variante.text));
                return;
            }
        };
        let trifft = k.tmp();
        k.zeile(&format!("{trifft} = icmp eq i32 {tag}, {nr}"));
        let arm = k.block("match_arm");
        let weiter = k.block("match_weiter");
        k.zeile(&format!("br i1 {trifft}, label %{arm}, label %{weiter}"));
        k.beendet = true;
        let _ = writeln!(k.text, "{arm}:");
        k.beendet = false;
        k.oeffne();
        // Binder: Nutzlast laden (Varianten mit Nutzlast).
        if let Some(binder) = &zweig.binder {
            if let Some((_, nutz)) = faelle.iter().find(|(n, _)| n == &zweig.variante.text).and_then(|(_, n)| Some((0, n.clone()))) {
                if let Some(nt) = nutz {
                    let (nll, nz) = match senke_typ(k.s, &nt) {
                        Some(x) => x,
                        None => return,
                    };
                    let slot = k.alloca(&v.typ.text());
                    k.zeile(&format!("store {} {}, ptr {slot}, align 8", v.typ.text(), v.text));
                    let pp = k.tmp();
                    k.zeile(&format!("{pp} = getelementptr {}, ptr {slot}, i32 0, i32 1", v.typ.text()));
                    let pc = k.tmp();
                    k.zeile(&format!("{pc} = getelementptr i8, ptr {pp}, i64 0"));
                    let lv = k.tmp();
                    k.zeile(&format!("{lv} = load {}, ptr {pc}, align 1", nll.text()));
                    let bslot = k.alloca(&nll.text());
                    k.zeile(&format!("store {} {lv}, ptr {bslot}, align {}", nll.text(), nat_align(&nll)));
                    k.lege_an(binder.text.clone(), Bindung { ptr: bslot, ll: nll, zeichen: nz, form: Some(nt) , fluechtig: false });
                }
            }
        }
        for st in &zweig.rumpf.anweisungen {
            if k.beendet {
                break;
            }
            senke_stmt(k, st);
        }
        k.schliesse();
        if !k.beendet {
            k.zeile(&format!("br label %{ende}"));
        }
        k.beendet = true;
        naechste = Some(weiter);
    }
    if let Some(lbl) = naechste.take() {
        let _ = writeln!(k.text, "{lbl}:");
        k.beendet = false;
    }
    k.zeile("unreachable");
    k.beendet = true;
    let _ = writeln!(k.text, "{ende}:");
    k.beendet = false;
}

/// Variantenfälle zum Wert (Form nennt die Variante).
fn find_variant_fuer_tag(s: &Senke, v: &Wert) -> Option<(String, Vec<(String, Option<TypExpr>)>, u64)> {
    let f = v.form.clone().map(|x| grundform(s, &x))?;
    match f {
        TypExpr::Pfad(p) => {
            let e = p.einfach()?;
            let (faelle, g) = s.variant_typen.get(&e.text)?.clone();
            Some((e.text.clone(), faelle, g))
        }
        _ => None,
    }
}

/// Grundfälle zum Wert (Form nennt den Grund — Fallwerte aus der Deklaration).
fn find_grund_fuer_wert(s: &Senke, v: &Wert) -> Option<Vec<(String, i128)>> {
    let f = v.form.clone().map(|x| grundform(s, &x))?;
    match f {
        TypExpr::Pfad(p) => {
            let e = p.einfach()?;
            s.gruende.get(&e.text).cloned()
        }
        _ => None,
    }
}

fn senke_narrow(k: &mut Koerper, n: &NarrowStmt, span: Span) {
    match &n.ziel {
        NarrowZiel::Endlich(_) => {
            senke_narrow_endlich(k, n, span);
            return;
        }
        NarrowZiel::Bereich(b) => {
            let p = match adresse_von_ort(k, &n.ort) {
                Some(p) => p,
                None => return,
            };
            // Gleitkomma läuft über `fcmp` (Modell `gleitNarrow`).
            if matches!(p.ll, LlTyp::F32 | LlTyp::F64) {
                senke_narrow_gleit(k, n, &p, b, span);
                return;
            }
            let w = match &p.ll {
                LlTyp::Int(bw) => *bw,
                _ => {
                    weigere(k.s, "Y104", span, "narrowing of non-integer".to_string());
                    return;
                }
            };
            // Schranke konstant oder zur Laufzeit (beides prüft derselbe Zweig).
            let (lo_t, hi_t) = match bereich_grenzen(k.s, b) {
                Some((lo, hi, exklusiv)) => {
                    let hi_inkl = if exklusiv { hi - 1 } else { hi };
                    (falte_int(lo, w), falte_int(hi_inkl, w))
                }
                None => match (senke_expr(k, &b.von), senke_expr(k, &b.bis)) {
                    (Some(vlo), Some(vhi)) => match (angleiche(k, vlo, &LlTyp::Int(w), Zeichen::U), angleiche(k, vhi, &LlTyp::Int(w), Zeichen::U)) {
                        (Some(wl), Some(wh)) => {
                            let mut wh = wh;
                            if b.exklusiv {
                                let e = k.tmp();
                                k.zeile(&format!("{e} = sub i{w} {}, 1", wh.text));
                                wh = Wert { typ: LlTyp::Int(w), zeichen: Zeichen::U, text: e, form: None };
                            }
                            (wl.text, wh.text)
                        }
                        _ => {
                            weigere(k.s, "Y104", b.span, "unlowerable narrowing bound".to_string());
                            return;
                        }
                    },
                    _ => {
                        weigere(k.s, "Y104", b.span, "unlowerable narrowing bound".to_string());
                        return;
                    }
                },
            };
            // Aktuellen Wert laden, halten, prüfen.
            let t = k.tmp();
            let al = nat_align(&p.ll);
            k.zeile(&format!("{t} = load {}, ptr {}, align {al}", p.ll.text(), p.addr));
            // Vorzeichen aus der Zelle (nicht aus dem Namen — Wand 9).
            let (cmp_lo, cmp_hi) = if p.zeichen == Zeichen::S {
                ("sge", "sle")
            } else {
                ("uge", "ule")
            };
            let ok1 = k.tmp();
            k.zeile(&format!("{ok1} = icmp {cmp_lo} i{w} {t}, {lo_t}"));
            let ok2 = k.tmp();
            k.zeile(&format!("{ok2} = icmp {cmp_hi} i{w} {t}, {hi_t}"));
            let ok = k.tmp();
            k.zeile(&format!("{ok} = and i1 {ok1}, {ok2}"));
            let weiter = k.block("narrow_weiter");
            let sonst = k.block("narrow_sonst");
            k.zeile(&format!("br i1 {ok}, label %{weiter}, label %{sonst}"));
            k.beendet = true;
            let _ = writeln!(k.text, "{sonst}:");
            k.beendet = false;
            senke_block(k, &n.sonst);
            if !k.beendet {
                k.zeile(&format!("br label %{weiter}"));
            }
            k.beendet = true;
            let _ = writeln!(k.text, "{weiter}:");
            k.beendet = false;
            // Bestandene Prüfung als Tatsache (`assume` — Optimierer UND Validator).
            k.s.braucht_assume = true;
            k.zeile(&format!("call void @llvm.assume(i1 {ok})"));
            k.s.beleg_annahmen.push(format!("narrow: {} in range holding at {}", n.ort.text(), span_zeile(span)));
        }
    }
}

fn span_zeile(span: Span) -> String {
    format!("{:?}", span)
}

fn senke_schleife(k: &mut Koerper, s: &Schleife, span: Span) {
    match s {
        Schleife::Traverse(t) => senke_traverse(k, t, span),
        Schleife::Retry(r) => senke_retry(k, r, span),
        Schleife::Forever(f) => senke_forever(k, f, span),
    }
}

/// Zählschleife über `elems of` (Felder) oder `slots of` (Tabellen).
fn senke_traverse(k: &mut Koerper, t: &Traverse, span: Span) {
    // Grenze je Domäne — alles andere ist `Y103` (exotische Domäne).
    enum Grenze {
        Feld { len: u64 },
        Schlitz { len: u64 },
    }
    let grenze = match &t.domaene {
        Domaene::ElementeVon(o) => {
            let p = match adresse_von_ort(k, o) {
                Some(p) => p,
                None => return,
            };
            match &p.ll {
                LlTyp::Feld(_, n) => Grenze::Feld { len: *n },
                _ => {
                    weigere(k.s, "Y103", span, "traversal over non-array".to_string());
                    return;
                }
            }
        }
        Domaene::NachfahrenVon(o) => {
            senke_traverse_nachfahren(k, t, o, span);
            return;
        }
        Domaene::VorfahrenVon(o) => {
            senke_traverse_ahnen(k, t, o, span);
            return;
        }
        // `queue T` ist `slots of T` (Zucker.lean) — gleiche Laufform.
        Domaene::Schlange(o) => {
            let tab = o.basis.text.clone();
            match k.s.tabellen.get(&tab).map(|(n, _)| *n) {
                Some(n) => Grenze::Schlitz { len: n },
                None => {
                    weigere(k.s, "Y103", span, "traversal over unknown queue".to_string());
                    return;
                }
            }
        }
        Domaene::SlotsVon(o) => {
            // `slots of w`: Tabellenname direkt oder hinter dem Zeiger
            // (Parameter `w : ptr<…> Werte` trägt die Form).
            let mut tab = o.basis.text.clone();
            if !k.s.tabellen.contains_key(&tab) {
                if let Some(b) = k.suche(&tab) {
                    if let Some(TypExpr::Zeiger(zz)) = b.form.clone().map(|f| grundform(k.s, &f)) {
                        if let TypExpr::Pfad(p) = grundform(k.s, &zz.ziel) {
                            if let Some(e) = p.einfach() {
                                tab = e.text.clone();
                            }
                        }
                    }
                }
            }
            match k.s.tabellen.get(&tab).map(|(n, _)| *n) {
                Some(n) => Grenze::Schlitz { len: n },
                None => {
                    weigere(k.s, "Y103", span, "traversal over unknown table".to_string());
                    return;
                }
            }
        }
        _ => {
            weigere(k.s, "Y103", span, "traversal over this domain".to_string());
            return;
        }
    };
    let _ = t.gegenstand;
    let n = match grenze {
        Grenze::Feld { len } => len,
        Grenze::Schlitz { len } => len,
    };
    // Verbrauchend oder unbesucht — der Lauf ist derselbe Zähler.
    let _ = &t.abstieg;
    let kopf = k.block("trav_kopf");
    let rumpf = k.block("trav_rumpf");
    let weiter = k.block("trav_weiter");
    let danach = k.block("trav_ende");
    let slot = k.alloca("i64");
    k.zeile(&format!("store i64 0, ptr {slot}, align 8"));
    k.zeile(&format!("br label %{kopf}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{kopf}:");
    k.beendet = false;
    let iv = k.tmp();
    k.zeile(&format!("{iv} = load i64, ptr {slot}, align 8"));
    let cond = k.tmp();
    k.zeile(&format!("{cond} = icmp ult i64 {iv}, {n}"));
    k.zeile(&format!("br i1 {cond}, label %{rumpf}, label %{danach}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{rumpf}:");
    k.beendet = false;
    k.oeffne();
    let islot = k.alloca("i32");
    let trunc = k.tmp();
    k.zeile(&format!("{trunc} = trunc i64 {iv} to i32"));
    k.zeile(&format!("store i32 {trunc}, ptr {islot}, align 4"));
    // Schleifeninvariante als Annahme (was sich senken lässt — der Rest fällt still).
    if let Some(inv) = &t.invariante {
        nehme_an(k, inv, "invariant");
    }
    k.lege_an(
        t.variable.text.clone(),
        Bindung { ptr: islot, ll: LlTyp::Int(32), zeichen: Zeichen::U, form: None , fluechtig: false },
    );
    // Marke ist der Binder (`leave i` verlässt den Durchlauf).
    k.schleifen.push(SchleifenKontext {
        weiter: weiter.clone(),
        danach: danach.clone(),
        marke: Some(t.variable.text.clone()),
        sperr_tiefe: k.sperren.len(),
    });
    for st in &t.rumpf.anweisungen {
        if k.beendet {
            break;
        }
        senke_stmt(k, st);
    }
    k.schleifen.pop();
    k.schliesse();
    if !k.beendet {
        k.zeile(&format!("br label %{weiter}"));
    }
    k.beendet = true;
    let _ = writeln!(k.text, "{weiter}:");
    k.beendet = false;
    let nv = k.tmp();
    k.zeile(&format!("{nv} = load i64, ptr {slot}, align 8"));
    let nn = k.tmp();
    k.zeile(&format!("{nn} = add i64 {nv}, 1"));
    k.zeile(&format!("store i64 {nn}, ptr {slot}, align 8"));
    k.zeile(&format!("br label %{kopf}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{danach}:");
    k.beendet = false;
}

fn senke_retry(k: &mut Koerper, r: &Retry, span: Span) {
    // `retry … until … bounded N`: Zähler plus Bedingung — `bis` trägt die Form.
    let schranke = match konst_u64(k.s, &r.schranke) {
        Some(n) => n,
        None => {
            weigere(k.s, "Y103", span, "retry with non-constant bound".to_string());
            return;
        }
    };
    let kopf = k.block("retry_kopf");
    let rumpf = k.block("retry_rumpf");
    let weiter = k.block("retry_weiter");
    let danach = k.block("retry_ende");
    let ueber = k.block("retry_ueber");
    let slot = k.alloca("i64");
    k.zeile(&format!("store i64 0, ptr {slot}, align 8"));
    k.zeile(&format!("br label %{kopf}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{kopf}:");
    k.beendet = false;
    if let Some(bis) = &r.bis {
        let c = match senke_predikat(k, bis) {
            Some(c) => c,
            None => {
                weigere(k.s, "Y103", span, "retry with unlowerable condition".to_string());
                return;
            }
        };
        // Bedingung wahr → fertig (Ziel erreicht).
        k.zeile(&format!("br i1 {c}, label %{danach}, label %{rumpf}"));
    } else {
        k.zeile(&format!("br label %{rumpf}"));
    }
    k.beendet = true;
    let _ = writeln!(k.text, "{rumpf}:");
    k.beendet = false;
    let nv = k.tmp();
    k.zeile(&format!("{nv} = load i64, ptr {slot}, align 8"));
    let voll = k.tmp();
    k.zeile(&format!("{voll} = icmp uge i64 {nv}, {schranke}"));
    k.zeile(&format!("br i1 {voll}, label %{ueber}, label %{weiter}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{ueber}:");
    k.beendet = false;
    // Überschreitung: benannter Austritt (Funktion ohne Argumente).
    let hname = r.bei_ueberschreitung.text.clone();
    k.zeile(&format!("call void {}()", gname(&hname)));
    k.zeile("unreachable");
    k.beendet = true;
    let _ = writeln!(k.text, "{weiter}:");
    k.beendet = false;
    if let Some(inv) = &r.invariante {
        nehme_an(k, inv, "invariant");
    }
    k.schleifen.push(SchleifenKontext { weiter: weiter.clone(), danach: danach.clone(), marke: r.marke.clone().map(|m| m.text), sperr_tiefe: k.sperren.len() });
    senke_block(k, &r.rumpf);
    k.schleifen.pop();
    if !k.beendet {
        let nv2 = k.tmp();
        k.zeile(&format!("{nv2} = load i64, ptr {slot}, align 8"));
        let nn = k.tmp();
        k.zeile(&format!("{nn} = add i64 {nv2}, 1"));
        k.zeile(&format!("store i64 {nn}, ptr {slot}, align 8"));
        k.zeile(&format!("br label %{kopf}"));
    }
    k.beendet = true;
    let _ = writeln!(k.text, "{danach}:");
    k.beendet = false;
    let _ = r.marke;
    let _ = r.fortschritt;
    let _ = r.effects;
}

fn senke_forever(k: &mut Koerper, f: &Forever, span: Span) {
    // `forever`: Rumpf bis `leave` — Schranke zählt nur den Wachhund.
    let _ = konst_u64(k.s, &f.je_durchgang);
    let kopf = k.block("for_kopf");
    let danach = k.block("for_ende");
    k.zeile(&format!("br label %{kopf}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{kopf}:");
    k.beendet = false;
    if let Some(inv) = &f.invariante {
        nehme_an(k, inv, "invariant");
    }
    k.schleifen.push(SchleifenKontext { weiter: kopf.clone(), danach: danach.clone(), marke: f.marke.clone().map(|m| m.text), sperr_tiefe: k.sperren.len() });
    senke_block(k, &f.rumpf);
    k.schleifen.pop();
    if !k.beendet {
        k.zeile(&format!("br label %{kopf}"));
    }
    k.beendet = true;
    let _ = writeln!(k.text, "{danach}:");
    k.beendet = false;
    let _ = span;
    let _ = &f.je_durchgang;
    let _ = &f.bei_ueberschreitung;
    let _ = &f.effects;
    let _ = &f.marke;
    let _ = &f.fortschritt;
    let _ = &f.verlaesst;
}

/// Ticket-Sperre nehmen: `nummer = tausch(nächst); warte bis bereit == nummer`.
fn ticket_nehmen(k: &mut Koerper, name: &str) {
    ticket_nehmen_roh(k, name);
    // A lock with a `shared held` side also waits for its readers to leave.
    leser_schreiber::schreiber_wartet_auf_leser(k, name);
}

/// The ticket gate alone (a reader passes through it, `leser_schreiber.rs`).
fn ticket_nehmen_roh(k: &mut Koerper, name: &str) {
    let naechst = gteil(name, "naechst");
    let bereit = gteil(name, "bereit");
    let ticket = k.tmp();
    k.zeile(&format!("{ticket} = atomicrmw add ptr {naechst}, i32 1 seq_cst, align 4"));
    let warte = k.block("lock_warte");
    let drin = k.block("lock_drin");
    k.zeile(&format!("br label %{warte}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{warte}:");
    k.beendet = false;
    let b = k.tmp();
    k.zeile(&format!("{b} = load atomic i32, ptr {bereit} seq_cst, align 4"));
    let eq = k.tmp();
    k.zeile(&format!("{eq} = icmp eq i32 {b}, {ticket}"));
    k.zeile(&format!("br i1 {eq}, label %{drin}, label %{warte}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{drin}:");
    k.beendet = false;
}

/// Ticket-Sperre geben: `bereit += 1` (der Nächste ist dran).
fn ticket_freigabe(k: &mut Koerper, name: &str) {
    let basis = match leser_schreiber::als_leser(name) {
        Some(leser) => {
            leser_schreiber::leser_freigabe(k, leser);
            leser
        }
        None => {
            ticket_freigabe_roh(k, name);
            name
        }
    };
    // Maskierende Sperre: der Zustand von vorher kehrt zurück (nie ein bedingungsloses `sti`).
    // Erst nach der Freigabe -- auch der Leserseite --, und nicht beim Weiterreichen des
    // Tickets mitten in der Leseraufnahme (`ticket_freigabe_roh`).
    if k.s.maskiert.contains(basis) {
        masken::wiederherstellen(k, basis);
    }
}

/// Das Ticket allein weitergeben: `bereit += 1`.
fn ticket_freigabe_roh(k: &mut Koerper, name: &str) {
    let bereit = gteil(name, "bereit");
    k.zeile(&format!("atomicrmw add ptr {bereit}, i32 1 seq_cst, align 4"));
}

fn senke_sperrt(k: &mut Koerper, s: &SperrtStmt, span: Span) {
    // Sperrname aus dem Ort (Basis — `locks L` / `locks m.L`).
    let name = s.sperre.basis.text.clone();
    if !k.s.schloesser.contains_key(&name) {
        weigere(k.s, "Y103", span, format!("unknown lock {name}"));
        return;
    }
    // Maskierende Sperre: erst Zustand sichern und Unterbrechungen sperren (auch für die
    // Leserseite), dann erst die Sperre selbst.
    if k.s.maskiert.contains(&name) {
        masken::maskieren(k, &name);
    }
    // A shared acquisition is held under the marked name (`leser_schreiber.rs`).
    let gehalten = if s.geteilt { leser_schreiber::leser_nehmen(k, &name) } else { ticket_nehmen(k, &name); name.clone() };
    k.sperren.push(gehalten.clone());
    senke_block(k, &s.rumpf);
    // Freigabe am Blockende, wenn der Pfad bis hier läuft (ein Rumpf, der in jedem Zweig
    // zurückkehrt, hat an jedem Ausgang freigegeben).
    k.sperren.pop();
    if !k.beendet {
        ticket_freigabe(k, &gehalten);
    }
}

/// **Zelle hinter der Laufzeit-Basis (TODO §1-B).** Die dritte sanktionierte
/// `inttoptr`-Stelle, geteilt von Hochwasser-Pfad, Freilisten-Pop und `free`.
fn arena_zelle(k: &mut Koerper, tisch: &str, idx: &str) -> Option<String> {
    let ai = k.s.arenen.get(tisch).cloned()?;
    let b = k.tmp();
    k.zeile(&format!("{b} = load i64, ptr {}, align 8", gteil(tisch, "basis")));
    let bp = k.tmp();
    k.zeile(&format!("{bp} = inttoptr i64 {b} to ptr"));
    let zelle = k.tmp();
    k.zeile(&format!(
        "{zelle} = getelementptr {}, ptr {bp}, i64 {idx}",
        ai.elem.text()
    ));
    Some(zelle)
}

/// **`free A[i];` senken (TODO §1-B, intrusive Freiliste).**
///
/// Der Slot trägt danach das Kettenglied (alter Kopf als `i64`), der Kopf
/// zeigt auf ihn. Der Prüfer (`N586`) hält Einfach-Freigabe und Tod; hier
/// steht kein Zweig -- ein lebender Slot ist immer verlinkbar. Elemente
/// unter 8 Bytes tragen kein Glied (`Y103` -- der Prüfer kennt keine Größen,
/// also steht die Schranke hier, benannt statt schweigend).
fn senke_frei(k: &mut Koerper, f: &FreiStmt, span: Span) {
    let tisch = f.ort.basis.text.clone();
    let _ai = match k.s.arenen.get(&tisch).cloned() {
        Some(x) => x,
        None => {
            weigere(k.s, "Y103", span, format!("release from unknown arena {tisch}"));
            return;
        }
    };
    let ix = match f.ort.suffixe.as_slice() {
        [OrtSuffix::Index(e)] => e,
        _ => {
            weigere(k.s, "Y103", span, format!("release of `{}` is no single slot", f.ort.text()));
            return;
        }
    };
    let v = match senke_expr(k, ix) {
        Some(v) => v,
        None => return,
    };
    let idx = match angleiche_mit_weigere(k, v, &LlTyp::Int(64), span) {
        Some(w) => w.text,
        None => return,
    };
    let zelle = memory::meta_cell(k, &tisch, &idx, false);
    let frei_g = gteil(&tisch, "frei");
    let kopf = k.tmp();
    k.zeile(&format!("{kopf} = load i64, ptr {frei_g}, align 8"));
    k.zeile(&format!("store i64 {kopf}, ptr {zelle}, align 8"));
    k.zeile(&format!("store i64 {idx}, ptr {frei_g}, align 8"));
    memory::live_change(k, &tisch, &idx, false, span);
}

fn senke_alloc(k: &mut Koerper, a: &AllocStmt, span: Span) {
    let ai = match k.s.arenen.get(&a.tisch.text).cloned() {
        Some(x) => x,
        None => {
            weigere(k.s, "Y103", span, format!("allocation from unknown arena {}", a.tisch.text));
            return;
        }
    };
    let v = match senke_expr(k, &a.wert) {
        Some(v) => v,
        None => return,
    };
    let w = match angleiche_mit_weigere(k, v, &ai.elem, span) {
        Some(w) => w,
        None => return,
    };
    let gname_tisch = a.tisch.text.clone();
    let weiter = k.block("alloc_weiter");
    let voll = k.block("alloc_voll");
    // Both predecessor paths must initialise the SAME binding. Separate
    // allocas here let the free-list path read an uninitialised index at -O0.
    let islot = k.alloca("i32");
    k.lege_an(a.name.text.clone(), Bindung {
        ptr: islot.clone(), ll: LlTyp::Int(32), zeichen: Zeichen::U,
        form: None, fluechtig: false,
    });
    // Freiliste zuerst (TODO §1-B): wiederverwendete Slots brauchen weder
    // Commit noch Abtastung -- der Speicher steht bereit. Der Pfad mündet
    // in `fertig`, nicht in `weiter`: `weiter` liest den Hochwasser-Zähler,
    // den dieser Pfad nie lädt (SSA-Dominanz).
    let fertig = k.block("alloc_fertig");
    let frei_g = gteil(&gname_tisch, "frei");
    let kopf = k.tmp();
    k.zeile(&format!("{kopf} = load i64, ptr {frei_g}, align 8"));
    let leer = k.tmp();
    k.zeile(&format!("{leer} = icmp eq i64 {kopf}, -1"));
    let hochwasser = k.block("alloc_hochwasser");
    let freiliste = k.block("alloc_freiliste");
    k.zeile(&format!("br i1 {leer}, label %{hochwasser}, label %{freiliste}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{freiliste}:");
    k.beendet = false;
    // Pop: Index ist der Kopf, Kopf ist das Glied im Slot; belegt rührt
    // nicht (der Slot steht unter der Hochwassermarke).
    let zelle_f = match arena_zelle(k, &gname_tisch, &kopf) {
        Some(z) => z,
        None => return,
    };
    if let Some(sample) = ai.sample.clone() {
        let p = memory::meta_cell(k, &gname_tisch, &kopf, true);
        let live = k.tmp(); k.zeile(&format!("{live} = load i64, ptr {p}, align 8"));
        let empty = k.tmp(); k.zeile(&format!("{empty} = icmp eq i64 {live}, 0"));
        let probe = k.block("arena_reuse_probe"); let ready = k.block("arena_reuse_ready");
        k.zeile(&format!("br i1 {empty}, label %{probe}, label %{ready}")); k.beendet = true;
        let _ = writeln!(k.text, "{probe}:"); k.beendet = false;
        let Some(value) = call_sample(k, &sample, span).and_then(|v| angleiche(k, v, &LlTyp::Int(64), Zeichen::U)) else { return; };
        let low = k.tmp(); k.zeile(&format!("{low} = icmp ult i64 {}, {}", value.text, sample.schwelle));
        k.zeile(&format!("br i1 {low}, label %{voll}, label %{ready}")); k.beendet = true;
        let _ = writeln!(k.text, "{ready}:"); k.beendet = false;
    }
    let link = memory::meta_cell(k, &gname_tisch, &kopf, false);
    let nach = k.tmp();
    k.zeile(&format!("{nach} = load i64, ptr {link}, align 8"));
    k.zeile(&format!("store i64 {nach}, ptr {frei_g}, align 8"));
    k.zeile(&format!("store {} {}, ptr {zelle_f}, align {}", ai.elem.text(), w.text, nat_align(&ai.elem)));
    memory::live_change(k, &gname_tisch, &kopf, true, span);
    // Index binden (schmal -- der Zähler passt immer). Derselbe Schwanz wie
    // unten, wiederholt statt über einen Join: zwei Pfade, kein Phi.
    let trunc_f = k.tmp();
    k.zeile(&format!("{trunc_f} = trunc i64 {kopf} to i32"));
    k.zeile(&format!("store i32 {trunc_f}, ptr {islot}, align 4"));
    k.zeile(&format!("br label %{fertig}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{hochwasser}:");
    k.beendet = false;
    let belegt = gteil(&gname_tisch, "belegt");
    let idx = k.tmp();
    k.zeile(&format!("{idx} = load i64, ptr {belegt}, align 8"));
    // Volle Arena (Zähler an der Schranke): `else` oder Falle — ohne einen
    // einzigen Systemruf (die Schranke steht, RAM steht nicht dahinter).
    let ok = k.tmp();
    k.zeile(&format!("{ok} = icmp ult i64 {idx}, {}", ai.hi));
    k.zeile(&format!("br i1 {ok}, label %{weiter}, label %{voll}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{voll}:");
    k.beendet = false;
    match &a.sonst {
        Some(b) => {
            senke_block(k, b);
            if !k.beendet {
                falle(k);
            }
            k.beendet = true;
        }
        None => {
            falle(k);
        }
    }
    let _ = writeln!(k.text, "{weiter}:");
    k.beendet = false;
    // Bedarf bereitstellen (Reserve einmalig, Commit bei Bedarf — `arena_bereit`
    // läuft bei Erfolg nach `weiter`, bei Speichermangel nach `voll`).
    let bedarf = k.tmp();
    k.zeile(&format!("{bedarf} = add i64 {idx}, 1"));
    let nach_commit = k.block("alloc_commit");
    // HINWEIS: `arena_bereit` braucht sein eigenes `voll`-Ziel — es teilt sich
    // den Block mit der Schrankenprüfung oben (beide meinen „kein Platz").
    if arena_bereit(k, &gname_tisch, &bedarf, &voll, span).is_none() {
        return;
    }
    let _ = nach_commit;
    let b = k.tmp();
    k.zeile(&format!("{b} = load i64, ptr {}, align 8", gteil(&gname_tisch, "basis")));
    let bp = k.tmp();
    k.zeile(&format!("{bp} = inttoptr i64 {b} to ptr"));
    let zelle = k.tmp();
    k.zeile(&format!(
        "{zelle} = getelementptr {}, ptr {bp}, i64 {idx}",
        ai.elem.text()
    ));
    k.zeile(&format!("store {} {}, ptr {zelle}, align {}", ai.elem.text(), w.text, nat_align(&ai.elem)));
    memory::live_change(k, &gname_tisch, &idx, true, span);
    let neu = k.tmp();
    k.zeile(&format!("{neu} = add i64 {idx}, 1"));
    k.zeile(&format!("store i64 {neu}, ptr {belegt}, align 8"));
    // Index binden (schmal — der Zähler passt immer).
    let trunc = k.tmp();
    k.zeile(&format!("{trunc} = trunc i64 {idx} to i32"));
    k.zeile(&format!("store i32 {trunc}, ptr {islot}, align 4"));
    // Hochwasser-Pfad mündet in `fertig` (wie die Freiliste oben).
    k.zeile(&format!("br label %{fertig}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{fertig}:");
    k.beendet = false;
    let _ = a.veraenderlich;
    let _ = a.typ;
}

fn senke_grow(k: &mut Koerper, g: &GrowStmt, span: Span) {
    // `grow` committet wirklich (Reserve/Commit wie `alloc`): Erfolg läuft
    // weiter, Mangel läuft in `sonst` (Pflicht-Zweig, steht immer).
    if !k.s.arenen.contains_key(&g.tisch.text) {
        weigere(k.s, "Y103", span, format!("commit on unknown arena {}", g.tisch.text));
        return;
    }
    let mehr = match konst_u64(k.s, &g.mehr) {
        Some(n) => n,
        None => {
            weigere(k.s, "Y103", span, "commit of non-constant size".to_string());
            return;
        }
    };
    let belegt = gteil(&g.tisch.text, "belegt");
    let idx = k.tmp();
    k.zeile(&format!("{idx} = load i64, ptr {belegt}, align 8"));
    let bedarf = k.tmp();
    k.zeile(&format!("{bedarf} = add i64 {idx}, {mehr}"));
    let weiter = k.block("grow_weiter");
    let voll = k.block("grow_voll");
    // HINWEIS: `arena_bereit` verzweigt selbst nach `weiter`/`voll` — hier nur
    // aufrufen, dann den `voll`-Zweig mit `sonst` füllen.
    if arena_bereit(k, &g.tisch.text, &bedarf, &voll, span).is_none() {
        return;
    }
    k.zeile(&format!("br label %{weiter}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{voll}:");
    k.beendet = false;
    senke_block(k, &g.sonst);
    if !k.beendet {
        k.zeile(&format!("br label %{weiter}"));
    }
    k.beendet = true;
    let _ = writeln!(k.text, "{weiter}:");
    k.beendet = false;
}

/// **Laute Falle (Nebenläufigkeit, Schritt 1).** Ein Fehlerpfad darf nie
/// `unreachable` allein tragen: der Optimierer liest das als „unmöglich",
/// faltet die Prüfung zu `llvm.assume` und streicht den Pfad (gemessen:
/// Klon-Fehler liefen still weiter, `rc=0` statt Falle). Die Falle ist eine
/// Seitenwirkung, die kein Pass entfernen oder durchschauen kann; das
/// `unreachable` dahinter ist dann wahrhaftig unerreichbar.
fn falle(k: &mut Koerper) {
    // The generic intrinsic: every LLVM target lowers it to its own trapping instruction,
    // and no pass removes it (it has a side effect). No per-architecture text here.
    k.s.braucht_trap = true;
    k.zeile("call void @llvm.trap()");
    k.zeile("unreachable");
    k.beendet = true;
}

/// A mapped thread region: a control page, a 64 KiB inaccessible guard,
/// and 8 MiB of stack. The child never resumes compiler-generated parent code.
const FADEN_STAPEL: u64 = 8 * 1024 * 1024;
const FADEN_GUARD: u64 = 65536;
const FADEN_REGION: u64 = FADEN_STAPEL + 2 * FADEN_GUARD;
/// CLONE_CHILD_CLEARTID: the kernel clears the per-invocation word AFTER exit.
const KLON_FLAGGEN: i64 = 0x100 | 0x200 | 0x400 | 0x800 | 0x10000 | 0x40000 | 0x200000;

fn senke_start(k: &mut Koerper, s: &StartStmt, span: Span) {
    let mut regions = Vec::new();
    for root in &s.roots {
        let Some((name, _)) = loese_fn(k.s, &k.modul, root) else {
            weigere(k.s, "Y103", span, format!("unknown thread root {}", root.text()));
            return;
        };
        k.s.start_wurzeln.insert(name.clone());
        let regs = runtime_args(k.s.ziel, &["0".into(), FADEN_REGION.to_string(), "0".into(), "34".into(), "-1".into(), "0".into()]);
        let Some(base) = laufzeit_ruf(k, "mmap", &regs, span) else { return; };
        runtime_success(k, &base);
        let accessible = base.clone();
        let regs = runtime_args(k.s.ziel, &[base.clone(), FADEN_GUARD.to_string(), "3".into()]);
        let Some(rc) = laufzeit_ruf(k, "mprotect", &regs, span) else { return; };
        runtime_success(k, &rc);
        let stack = k.tmp();
        k.zeile(&format!("{stack} = add i64 {base}, {}", 2 * FADEN_GUARD));
        let regs = runtime_args(k.s.ziel, &[stack, FADEN_STAPEL.to_string(), "3".into()]);
        let Some(rc) = laufzeit_ruf(k, "mprotect", &regs, span) else { return; };
        runtime_success(k, &rc);
        let word = k.tmp();
        k.zeile(&format!("{word} = inttoptr i64 {accessible} to ptr"));
        k.zeile(&format!("store atomic i32 1, ptr {word} release, align 4"));
        let top = k.tmp();
        k.zeile(&format!("{top} = add i64 {base}, {FADEN_REGION}"));
        let child = k.tmp();
        // This assembly is necessary at the stack switch: entering an ordinary
        // LLVM block with a replaced SP invalidates its frame/spill addresses.
        // The child calls the root on an aligned fresh stack and uses no stack
        // after it returns. The kernel, not an early userspace store, ends join.
        if k.s.ziel.name == "x86_64" {
            k.zeile(&format!("{child} = call i64 asm sideeffect \"syscall; testq %rax, %rax; jnz 1f; xorq %rbp, %rbp; callq *%r12; movq $$60, %rax; xorq %rdi, %rdi; syscall; ud2; 1:\", \"={{rax}},{{rax}},{{rdi}},{{rsi}},{{rdx}},{{r10}},{{r8}},{{r12}},~{{rcx}},~{{r11}},~{{flags}},~{{memory}}\"(i64 56, i64 {KLON_FLAGGEN}, i64 {top}, i64 0, i64 {accessible}, i64 0, ptr {})", gname(&name)));
        } else {
            k.zeile(&format!("{child} = call i64 asm sideeffect \"svc #0; cbnz x0, 1f; mov x29, xzr; blr x19; mov x8, #93; mov x0, #0; svc #0; brk #0; 1:\", \"={{x0}},{{x8}},{{x0}},{{x1}},{{x2}},{{x3}},{{x4}},{{x19}},~{{x30}},~{{memory}}\"(i64 220, i64 {KLON_FLAGGEN}, i64 {top}, i64 0, i64 0, i64 {accessible}, ptr {})", gname(&name)));
        }
        runtime_success(k, &child);
        regions.push((base, word, accessible));
    }
    // Spawn the whole group before joining any root.
    for (base, word, address) in regions {
        let head = k.block("faden_join");
        let sleep = k.block("faden_wait");
        let joined = k.block("faden_joined");
        k.zeile(&format!("br label %{head}"));
        k.beendet = true;
        let _ = writeln!(k.text, "{head}:"); k.beendet = false;
        let value = k.tmp();
        k.zeile(&format!("{value} = load atomic i32, ptr {word} acquire, align 4"));
        let done = k.tmp();
        k.zeile(&format!("{done} = icmp eq i32 {value}, 0"));
        k.zeile(&format!("br i1 {done}, label %{joined}, label %{sleep}"));
        k.beendet = true;
        let _ = writeln!(k.text, "{sleep}:"); k.beendet = false;
        // The kernel's clear_child_tid wake uses shared FUTEX_WAIT (0), not
        // FUTEX_WAIT_PRIVATE. EAGAIN/EINTR are retryable, other errors trap.
        let regs = runtime_args(k.s.ziel, &[address, "0".into(), "1".into(), "0".into(), "0".into(), "0".into()]);
        let Some(rc) = laufzeit_ruf(k, "futex", &regs, span) else { return; };
        let ok = k.tmp(); let interrupted = k.tmp(); let raced = k.tmp(); let retry = k.tmp(); let allowed = k.tmp();
        k.zeile(&format!("{ok} = icmp eq i64 {rc}, 0"));
        k.zeile(&format!("{interrupted} = icmp eq i64 {rc}, -4"));
        k.zeile(&format!("{raced} = icmp eq i64 {rc}, -11"));
        k.zeile(&format!("{retry} = or i1 {interrupted}, {raced}"));
        k.zeile(&format!("{allowed} = or i1 {ok}, {retry}"));
        let fail = k.block("faden_join_failed");
        k.zeile(&format!("br i1 {allowed}, label %{head}, label %{fail}"));
        k.beendet = true;
        let _ = writeln!(k.text, "{fail}:"); k.beendet = false; falle(k);
        let _ = writeln!(k.text, "{joined}:"); k.beendet = false;
        let regs = runtime_args(k.s.ziel, &[base, FADEN_REGION.to_string()]);
        let Some(rc) = laufzeit_ruf(k, "munmap", &regs, span) else { return; };
        runtime_success(k, &rc);
    }
}

/// Register assignment is shared by all runtime memory operations.
fn runtime_args(ziel: &Ziel, values: &[String]) -> Vec<(String, String)> {
    let names = if ziel.name == "x86_64" { ["rdi", "rsi", "rdx", "r10", "r8", "r9"] }
        else { ["x0", "x1", "x2", "x3", "x4", "x5"] };
    names.into_iter().zip(values.iter().cloned()).map(|(r, v)| (r.into(), v)).collect()
}

fn runtime_success(k: &mut Koerper, answer: &str) {
    let bad = ruf_fehlschlag(k, answer);
    let failure = k.block("runtime_failure"); let success = k.block("runtime_success");
    k.zeile(&format!("br i1 {bad}, label %{failure}, label %{success}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{failure}:"); k.beendet = false; falle(k);
    let _ = writeln!(k.text, "{success}:"); k.beendet = false;
}

// ===================================================================================
// Sammeln (Module flach, Register voll)
// ===================================================================================

/// Bits als Hexfloat (LLVM mag kein `5e-1` als Konstante).
fn hexfloat(bits: u64, f32: bool) -> String {
    if f32 {
        format!("0x{:X}", (bits >> 32) as u32)
    } else {
        format!("0x{:X}", bits)
    }
}

/// Geisttyp hinter einer Form (Geister vererben nicht — nur der Name zählt).
fn ist_geist(s: &Senke, t: &TypExpr) -> bool {
    match grundform(s, t) {
        TypExpr::Pfad(p) => p.einfach().is_some_and(|e| s.geister.contains(&e.text)),
        _ => false,
    }
}

/// Items flach mit Modulpfad (`m::f` bleibt auffindbar, Symbole heißen kurz).
fn flach(items: &[Item], prefix: &str, out: &mut Vec<(Item, String)>) {
    for it in items {
        match &it.art {
            ItemArt::Modul(m) => {
                let p = if prefix.is_empty() { m.pfad.text() } else { format!("{prefix}::{}", m.pfad.text()) };
                flach(&m.items, &p, out);
            }
            _ => out.push((it.clone(), prefix.to_string())),
        }
    }
}

/// Ziel-Architekturwort (`x86_64` / `aarch64`).
fn ziel_arch(z: &Ziel) -> &'static str {
    z.name
}

fn sammle(s: &mut Senke, baum: &Programm, bau: crate::gatter::Bau) {
    let mut items = Vec::new();
    flach(&baum.items, "", &mut items);
    // Durchgang 1: Typen, Gründe, Tabellen, Arenen, Schlösser, Atomics.
    for (it, modul) in &items {
        if skip_wegen_bau(it, bau) {
            continue;
        }
        s.modul = modul.clone();
        match &it.art {
            ItemArt::Typ(t) => sammle_typ(s, t, it.span),
            ItemArt::Reason(r) => {
                let faelle = r.faelle.iter().map(|f| (f.name.text.clone(), f.wert as i128)).collect();
                s.gruende.insert(r.name.text.clone(), faelle);
            }
            ItemArt::Tabelle(t) => sammle_tabelle(s, t, it.span),
            ItemArt::Arena(a) => sammle_arena(s, a, it.span),
            ItemArt::Lock(l) => {
                match &l.maskiert {
                    Some(w) if !masken::wort_ist_irqs(w) => {
                        weigere(s, "Y102", it.span, format!("lock {} masks `{}`, no lowering", l.name.text, w.text));
                        s.tote_items.insert(l.name.text.clone());
                    }
                    Some(_) => {
                        s.maskiert.insert(l.name.text.clone());
                        s.schloesser.insert(l.name.text.clone(), l.geteilte_haltezeit.is_some());
                    }
                    None => {
                        s.schloesser.insert(l.name.text.clone(), l.geteilte_haltezeit.is_some());
                    }
                }
            }
            ItemArt::Atomic(a) => sammle_atomic(s, a, it.span),
            ItemArt::Device(d) => sammle_device(s, d, it.span),
            ItemArt::Accumulates(acc) => {
                let alt = s.eng_modus;
                s.eng_modus = false;
                let gesenkt = senke_typ(s, &acc.typ);
                s.eng_modus = alt;
                if let Some((ll, z)) = gesenkt {
                    s.globale.insert(acc.name.text.clone(), Global {
                        typ: ll,
                        zeichen: z,
                        form: acc.typ.clone(),
                        konstant: false,
                        init_text: Some("0".to_string()),
                    });
                }
            }
            ItemArt::Format(f) => {
                let felder = f.felder.iter().map(|x| (x.name.text.clone(), x.typ.typ.clone())).collect();
                s.rekorde.insert(f.name.text.clone(), felder);
                s.formate.insert(f.name.text.clone());
            },
            ItemArt::Concurrent(c) => {
                for k in &c.koerper {
                    s.nebenlaeufig.push(kurzname(k));
                }
            }
            _ => {}
        }
    }
    // Durchgang 2: Funktionen, Tore, Externe, Globale.
    for (it, modul) in &items {
        if skip_wegen_bau(it, bau) {
            continue;
        }
        s.modul = modul.clone();
        let voll = vollname(modul, it.art.name().map(|i| i.text.clone()));
        match &it.art {
            ItemArt::Funktion(f) => sammle_funktion(s, f, &voll, it.span),
            ItemArt::Syscall(g) => sammle_tor(s, g, &voll, it.span),
            ItemArt::Konst(kd) => sammle_konst(s, kd, it.span),
            ItemArt::Statisch(sd) => sammle_statisch(s, sd, it.span),
            ItemArt::Entry(e) => eintritte::sammle(s, e, modul, it.span),
            ItemArt::Boot(b) => {
                weigere(
                    s,
                    "Y102",
                    it.span,
                    format!(
                        "boot {}: a mode-ladder sequence of axiom steps (control registers, descriptor tables) \
                         has no body to lower. The Lean model reads `boot` as a FOREIGN body (`Ax`, \
                         `Syntax.lean` section 14) and its steps as axiom calls, register reads \
                         (`bootinfo_retten(ebx)`) and a stack-pointer assignment with no instruction in \
                         the source: lowering them would invent semantics the language and the model do \
                         not state. The start state and the steps are the program's own gates",
                        b.name.text
                    ),
                );
                s.tote_items.insert(b.name.text.clone());
            }
            ItemArt::Entrust(t) => {
                weigere(
                    s,
                    "Y102",
                    it.span,
                    format!(
                        "entrust {}: the handover names a space and a register contract but no address to \
                         transfer control to, and no form of the source ever performs it (the Lean model reads \
                         `entrust` as a FOREIGN body, `Ax`, `Syntax.lean` section 14); the jump to unknown code \
                         has no sound lowering here",
                        t.name.text
                    ),
                );
                s.tote_items.insert(t.name.text.clone());
            }
            _ => {}
        }
    }
    // Rufe lösen kurz wie voll auf (Eintrag unter beiden Schlüsseln).
    s.modul = String::new();
}

/// Voller Name (`modul::name` oder `name`).
fn vollname(modul: &str, name: Option<String>) -> String {
    match name {
        Some(n) if !modul.is_empty() => format!("{modul}::{n}"),
        Some(n) => n,
        None => modul.to_string(),
    }
}

/// `when`-gesteuerte Items im Auslieferungsbau überspringen.
fn skip_wegen_bau(it: &Item, bau: crate::gatter::Bau) -> bool {
    match bau {
        crate::gatter::Bau::Auslieferung => it.when.is_some(),
        crate::gatter::Bau::Pruefbau => false,
    }
}

fn sammle_typ(s: &mut Senke, t: &TypDecl, span: Span) {
    let n = t.name.text.clone();
    if t.ghost {
        s.geister.insert(n);
        return;
    }
    match &t.rumpf {
        None => {
            if t.opaque {
                // Körperlos-`opaque`: keine Breite — der Gebrauch fällt (`Y101`).
            } else if t.linear {
                // Körperlos-lineare Marke: 1 Byte (wie der C-Erzeuger).
                s.aliase.insert(n.clone(), TypExpr::Int(IntTy {
                    wort: Kw::U8,
                    zucker: None,
                    bereich: None,
                    span,
                }));
            } else {
                weigere(s, "Y101", span, format!("bodiless type {n}"));
                s.tote_items.insert(n);
            }
        }
        Some(TypExpr::Verbund(fs, _)) => {
            let felder = fs.iter().map(|f| (f.name.text.clone(), f.typ.typ.clone())).collect();
            s.rekorde.insert(n, felder);
        }
        Some(TypExpr::Varianten(faelle, _)) => {
            let fs = faelle.iter().map(|f| (f.name.text.clone(), f.nutzlast.clone())).collect();
            s.variant_typen.insert(n, (fs, 0));
        }
        Some(seite) => {
            s.aliase.insert(n, seite.clone());
        }
    }
    let _ = t.tagged;
    let _ = t.opaque;
    let _ = t.parameter;
    let _ = t.ordnung;
}

fn sammle_tabelle(s: &mut Senke, t: &Tabelle, span: Span) {
    let n = t.name.text.clone();
    let len = match &t.kapazitaet {
        Some(e) => match konst_u64(s, e) {
            Some(v) => v,
            None => {
                weigere(s, "Y101", span, format!("table {n} with non-constant count"));
                return;
            }
        },
        None => {
            weigere(s, "Y101", span, format!("table {n} without count"));
            return;
        }
    };
    // Slot-Felder merken (Layout und Zugriffe).
    let slot_felder: Vec<(String, TypExpr)> = match &t.slot {
        Some(slot) => slot
            .felder
            .iter()
            .map(|f| {
                let t = match &f.typ {
                    SlotTyp::Typ(t) => t.clone(),
                    SlotTyp::Wrapping(i) => TypExpr::Int(i.clone()),
                };
                (f.name.text.clone(), t)
            })
            .collect(),
        None => Vec::new(),
    };
    s.tab_slots.insert(n.clone(), slot_felder);
    sammle_invarianten_bereich(s, t);
    if !t.ops.is_empty() {
        if let Some(belegt) = &t.belegt {
            let elter = t.baum.as_ref().and_then(|b| b.elter.as_ref()).map(|i| i.text.clone());
            let woerter: Vec<String> = t.ops.iter().map(|i| i.text.clone()).collect();
            s.tab_ops.insert(n.clone(), (belegt.text.clone(), elter, woerter));
        }
    }
    if let Some(b) = &t.baum {
        s.tab_baeume.insert(
            n.clone(),
            (b.elter.clone().map(|i| i.text), b.kind.clone().map(|i| i.text), b.geschwister.clone().map(|i| i.text)),
        );
    }
    // Slot-Layout faul (Name steht, Felder kommen aus `slot`).
    let slotname = format!("{n}$slot");
    s.tabellen.insert(n, (len, slotname));
    let _ = &t.slot;
}


fn sammle_arena(s: &mut Senke, a: &ArenaDecl, span: Span) {
    let lo = match konst_u64(s, &a.lo) {
        Some(v) => v,
        None => {
            weigere(s, "Y103", span, format!("arena {} with non-constant reservation", a.name.text));
            return;
        }
    };
    let hi = match konst_u64(s, &a.hi) {
        Some(v) => v,
        None => {
            weigere(s, "Y103", span, format!("arena {} with non-constant bound", a.name.text));
            return;
        }
    };
    let max = match &a.max {
        Some(e) => match konst_u64(s, e) {
            Some(v) => v,
            None => {
                weigere(s, "Y103", span, format!("arena {} with non-constant ceiling", a.name.text));
                return;
            }
        },
        // Ohne Decke MIT `pb`: die unbegrenzte Form — der Zählerraum
        // ist die Decke, die Reserve bleibt Adressraum ohne RAM (`mmap(PROT_NONE)`).
        // Ohne Decke ohne Klausel: statisch, die Decke ist `hi` (wie der Prüfer).
        None if a.probe.is_some() => u32::MAX as u64,
        None => hi,
    };
    // Probe auflösen (Tor oder nullstellige Funktion, Modul der Arena).
    let sample = match &a.probe {
        Some(d) => match resolve_sample(s, d, span) {
            Some(x) => Some(x),
            None => return,
        },
        None => None,
    };
    let alt = s.eng_modus;
    s.eng_modus = true;
    let gesenkt = senke_typ(s, &a.element);
    s.eng_modus = alt;
    let (elem, _) = match gesenkt {
        Some(x) => x,
        None => return,
    };
    let groesse = match groesse_von_ll(s, &elem) {
        Some(g) => g,
        None => {
            weigere(s, "Y103", span, format!("arena {} with unsized element", a.name.text));
            return;
        }
    };
    let info = ArenaInfo { elem, form: a.element.clone(), groesse, lo, hi, max, sample };
    if max.checked_mul(groesse.max(1)).is_none_or(|n| n > i64::MAX as u64 - 1048576)
        || memory::metadata_size(&info).is_none_or(|n| n > i64::MAX as u64 - 1048576) {
        weigere(s, "Y103", span, format!("arena {} exceeds the addressable extent", a.name.text));
        return;
    }
    s.arenen.insert(
        a.name.text.clone(),
        info,
    );
}

/// **Hold the probe at collection time.** Only threshold (due, else `Y103`)
/// and origin (path plus arena module) -- resolved at use, once all
/// items are collected. The checker (`N584`/`N585`) held the shape.
fn resolve_sample(s: &mut Senke, d: &Probe, span: Span) -> Option<Sample> {
    let schwelle = match konst_u64(s, &d.schwelle) {
        Some(v) => v,
        None => {
            weigere(s, "Y103", span, "pressure probe with non-constant threshold".to_string());
            return None;
        }
    };
    Some(Sample { pfad: d.pfad.clone(), modul: s.modul.clone(), schwelle })
}

fn sammle_atomic(s: &mut Senke, a: &AtomicDecl, span: Span) {
    let alt = s.eng_modus;
    s.eng_modus = true;
    let gesenkt = senke_typ(s, &a.typ);
    s.eng_modus = alt;
    let (mut ll, _) = match gesenkt {
        Some(x) => x,
        None => return,
    };
    // Atomares `i1` kennt LLVM nicht — Byte an der Grenze (wie `bool`-Atomics).
    if ll == LlTyp::Int(1) {
        ll = LlTyp::Int(8);
    }
    // The same for the elements of an atomic array (`atomic F : [bool; N]`).
    if let LlTyp::Feld(e, n) = &ll {
        if **e == LlTyp::Int(1) {
            ll = LlTyp::Feld(Box::new(LlTyp::Int(8)), *n);
        }
    }
    let ord = a.ordnung.as_ref().map(atomar_ordnung).unwrap_or("seq_cst");
    s.atomare.insert(a.name.text.clone(), (ll, ord.to_string()));
    let _ = span;
    let _ = &a.obermenge;
    let _ = &a.beobachtet;
}

fn sammle_funktion(s: &mut Senke, f: &FnDecl, voll: &str, span: Span) {
    let kurz = f.name.text.clone();
    // Fehlerkanal (`-> T or R`): Antwort ist der Kanal-Struct (unten gebaut).
    let klasse = f.klasse;
    // Extern: Deklaration in fremder ABI (breit, `noalias` an `own`).
    if matches!(klasse, Some(FnKlasse::Extern)) {
        let alt = s.eng_modus;
        s.eng_modus = false;
        let mut params = Vec::new();
        let mut geist = Vec::new();
        let mut ok = true;
        for p in &f.parameter {
            if ist_geist(s, &p.typ) {
                geist.push(true);
                continue;
            }
            geist.push(false);
            match senke_typ(s, &p.typ) {
                Some((ll, z)) => params.push((ll, z)),
                None => {
                    ok = false;
                    break;
                }
            }
        }
        let ret = match &f.ergebnis {
            Some(t) if ist_geist(s, t) => None,
            Some(t) => match senke_typ(s, t) {
                Some((ll, z)) => Some((ll, z)),
                None => {
                    ok = false;
                    None
                }
            },
            None => None,
        };
        s.eng_modus = alt;
        if !ok {
            s.tote_items.insert(kurz);
            return;
        }
        let or_nutz_ext = match &f.fehler {
            Some(r) => or_fuer(s, &f.ergebnis, &r.text, span),
            None => None,
        };
        let ret_ext = match or_nutz_ext.clone() {
            Some(or) => Some((or_struct(or.p), Zeichen::Egal)),
            None => ret.clone(),
        };
        if f.fehler.is_some() && or_nutz_ext.is_none() {
            s.tote_items.insert(kurz);
            return;
        }
        trage_fn_ein(s, voll, &kurz, FnSig {
            params,
            ret: ret_ext,
            ret_form: f.ergebnis.clone(),
            extern_: true,
            geist_param: geist,
            geist_rueck: false,
            or_nutz: or_nutz_ext,
            eigen_param: eigen_flags(voll, &f.parameter, s),
            vertrag_requires: f.requires.clone(),
            vertrag_ensures: f.ensures.clone(),
        });
        s.plaene.insert(schluessel_fuer(voll, &kurz, s), FnPlan::Fertig { modul: s.modul.clone() });
        return;
    }
    // Rumpflos (außer extern): nichts zu senken — Aufrufer fallen (`Y104` dort).
    let rumpf = match &f.rumpf {
        FnRumpf::Block(b) => b.clone(),
        FnRumpf::Pred(_) => {
            // `spec fn`: Beweisform — kein Laufzeitkörper.
            s.plaene.insert(schluessel_fuer(voll, &kurz, s), FnPlan::Fertig { modul: s.modul.clone() });
            return;
        }
        FnRumpf::Asm(a) => {
            assembler::sammle(s, f, a, voll, span);
            return;
        }
        FnRumpf::Keiner => {
            s.plaene.insert(schluessel_fuer(voll, &kurz, s), FnPlan::Fertig { modul: s.modul.clone() });
            return;
        }
    };
    // Signatur an der ABI-Grenze: BREIT wie erklärt (Aufrufer innen wie außen
    // reichen die deklarierte Breite; Speicher innen verengt — `main` bleibt `i32`).
    let alt = s.eng_modus;
    s.eng_modus = false;
    let mut params = Vec::new();
    let mut geist = Vec::new();
    let mut ok = true;
    for p in &f.parameter {
        if ist_geist(s, &p.typ) {
            geist.push(true);
            continue;
        }
        geist.push(false);
        match senke_typ(s, &p.typ) {
            Some((ll, z)) => params.push((ll, z)),
            None => {
                ok = false;
                break;
            }
        }
    }
    let (ret, geist_rueck) = match &f.ergebnis {
        Some(t) if ist_geist(s, t) => (None, true),
        Some(t) => match senke_typ(s, t) {
            Some((LlTyp::Void, z)) => (Some((LlTyp::Void, z)), false),
            Some(x) => (Some(x), false),
            None => {
                ok = false;
                (None, false)
            }
        },
        None => (None, false),
    };
    s.eng_modus = alt;
    if !ok {
        s.tote_items.insert(kurz);
        s.tote_items.insert(voll.to_string());
        return;
    }
    let or_nutz_impl = match &f.fehler {
        Some(r) => or_fuer(s, &f.ergebnis, &r.text, span),
        None => None,
    };
    let ret_impl = match or_nutz_impl.clone() {
        Some(or) => Some((or_struct(or.p), Zeichen::Egal)),
        None => ret.clone(),
    };
    if f.fehler.is_some() && or_nutz_impl.is_none() {
        s.tote_items.insert(kurz);
        s.tote_items.insert(voll.to_string());
        return;
    }
    trage_fn_ein(s, voll, &kurz, FnSig {
        params: params.clone(),
        ret: ret_impl,
        ret_form: f.ergebnis.clone(),
        extern_: false,
        or_nutz: or_nutz_impl,
        geist_param: geist,
        geist_rueck,
        eigen_param: eigen_flags(voll, &f.parameter, s),
        vertrag_requires: f.requires.clone(),
        vertrag_ensures: f.ensures.clone(),
    });
    // Eintritt merken (`main` + Breite).
    if kurz == "main" {
        let breite = match &ret {
            Some((LlTyp::Int(w), _)) => Some(*w),
            Some((LlTyp::Void, _)) | None => {
                // `never` als `Void`? `main -> never` senkt `Never` → Void.
                match &f.ergebnis {
                    Some(TypExpr::Never(_)) => None,
                    _ => Some(32),
                }
            }
            _ => Some(32),
        };
        // `never` erkennen: Ergebnis-Typ `Never`.
        let nie = matches!(&f.ergebnis, Some(TypExpr::Never(_)));
        s.eintritt = Some((kurz.clone(), if nie { None } else { breite }));
    }
    // Plan unter beiden Schlüsseln (Ruf löst kurz wie voll auf).
    let plan = {
        let mut namen = Vec::new();
        let mut formen = Vec::new();
        for p in &f.parameter {
            if !ist_geist(s, &p.typ) {
                namen.push(p.name.text.clone());
                formen.push(p.typ.clone());
            }
        }
        FnPlan::Impl { rumpf, params, namen, formen, modul: s.modul.clone() }
    };
    let key = schluessel_fuer(voll, &kurz, s);
    s.plaene.insert(key, plan);
}

/// `noalias`-Flags je gesenkter (nicht Geist-) Stelle: `own`, und -- in einer Funktion aus
/// `noalias_innen` -- jeder SCHREIBBARE Zeigerparameter.
fn eigen_flags(voll: &str, params: &[Parameter], s: &Senke) -> Vec<bool> {
    let innen = s.noalias_innen.contains(voll);
    params
        .iter()
        .filter(|p| !ist_geist(s, &p.typ))
        .map(|p| ist_eigen(s, &p.typ) || (innen && ist_schreibbarer_zeiger(s, &p.typ)))
        .collect()
}

fn ist_schreibbarer_zeiger(s: &Senke, t: &TypExpr) -> bool {
    match grundform(s, t) {
        TypExpr::Zeiger(z) => z
            .rechte
            .iter()
            .any(|r| matches!(r, Recht::Schreiben | Recht::LesenSchreiben | Recht::Eigen(_))),
        _ => false,
    }
}

/// **Which functions may put `noalias` on a WRITABLE pointer parameter** (`dokumente/A1-OWN-PAPER.md`,
/// slice 4). `noalias` says: during the call nothing reaches the pointee except through this
/// pointer. It is a fact about the WHOLE call, so it is emitted only where the checker has the
/// whole call in view:
///
/// * the function is not `pub`, has a body, is called from a body of this unit, and its address
///   is nowhere taken (`&f`) -- so every call goes through a call site `R014` holds against the
///   pairwise-distinct-roots rule;
/// * no entry, `boot` or `concurrent` item names it (those are entered by the runtime);
/// * its DECLARED `effects` name nothing but its own pointer parameters -- no table, static,
///   lock or arena by name -- and `E008` keeps that list a superset of the callees' effects, so
///   the function cannot reach the pointee through a global either.
///
/// **It rests on one named assumption, and says so:** a `pub` caller with a pointer pair assumes
/// its parameters distinct (`R015`). A caller outside the unit that breaks it breaks the frame
/// statement as well. **A unit with a function value outside a function body gets NO extension**
/// -- that is an address nobody walked.
fn noalias_innen(baum: &Programm, u: &crate::umgebung::Umgebung) -> BTreeSet<String> {
    fn adressen<'a>(b: &'a Block, aus: &mut Vec<&'a Pfad>) {
        for s in &b.anweisungen {
            let mut ausdruecke: Vec<&Expr> = crate::eigene_ausdruecke(s);
            for p in crate::eigene_praedikate(s) {
                ausdruecke.extend(crate::ausdruecke_im_praedikat(p));
            }
            if let StmtArt::Ruf(r) = &s.art {
                ausdruecke.extend(r.argumente.iter());
            }
            if let StmtArt::LetSonst(l) = &s.art {
                if let Some(r) = l.als_ruf() {
                    ausdruecke.extend(r.argumente.iter());
                }
            }
            for e in ausdruecke {
                for x in crate::alle_ausdruecke(e) {
                    if let ExprArt::FnWert(p) = &x.art {
                        aus.push(p);
                    }
                }
            }
            for k in crate::unterbloecke(s) {
                adressen(k, aus);
            }
        }
    }
    let mut kandidaten: BTreeSet<String> = BTreeSet::new();
    let mut weg: BTreeSet<String> = BTreeSet::new();
    let mut benannt: BTreeSet<String> = BTreeSet::new();
    let mut ausserhalb = false;
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| match &item.art {
        ItemArt::Funktion(f) => {
            let FnRumpf::Block(rumpf) = &f.rumpf else {
                return;
            };
            let mut ps: Vec<&Pfad> = Vec::new();
            adressen(rumpf, &mut ps);
            for p in ps {
                weg.extend(u.kandidaten_aufloesbar(modul, &p.text()));
            }
            if f.oeffentlich {
                return;
            }
            let zeiger: BTreeSet<&str> = f
                .parameter
                .iter()
                .filter(|p| matches!(p.typ, TypExpr::Zeiger(_)))
                .map(|p| p.name.text.as_str())
                .collect();
            let Some(w) = &f.effects else {
                return;
            };
            let nur_eigene = w.liste.iter().all(|x| match &x.art {
                WirkungArt::Liest(o) | WirkungArt::Schreibt(o) | WirkungArt::Verbraucht(o) => {
                    zeiger.contains(o.basis.text.as_str())
                }
                WirkungArt::Rein | WirkungArt::Divergiert => true,
                _ => false,
            });
            if nur_eigene {
                kandidaten.insert(crate::umgebung::qualifiziere(modul, &f.name.text));
            }
        }
        ItemArt::Entry(e) => {
            benannt.insert(e.dispatch.teile.last().map(|i| i.text.clone()).unwrap_or_default());
        }
        ItemArt::Boot(b) => {
            benannt.insert(b.dispatch.teile.last().map(|i| i.text.clone()).unwrap_or_default());
        }
        ItemArt::Concurrent(c) => {
            for k in &c.koerper {
                benannt.insert(k.teile.last().map(|i| i.text.clone()).unwrap_or_default());
            }
        }
        ItemArt::Modul(_) => {}
        other => {
            if format!("{other:?}").contains("FnWert") {
                ausserhalb = true;
            }
        }
    });
    if ausserhalb {
        return BTreeSet::new();
    }
    let g = crate::aufrufgraph::erhebe_mit(baum, u);
    let mut gerufen: BTreeSet<String> = BTreeSet::new();
    for (k, kn) in &g.knoten {
        for (ziel, _) in &kn.rufe {
            if ziel != k {
                gerufen.insert(ziel.clone());
            }
        }
    }
    kandidaten
        .into_iter()
        .filter(|k| gerufen.contains(k) && !weg.contains(k))
        .filter(|k| {
            let kurz = k.rsplit("::").next().unwrap_or(k);
            !benannt.contains(kurz)
        })
        .collect()
}
fn trage_fn_ein(s: &mut Senke, voll: &str, kurz: &str, sig: FnSig) {
    let params = sig.params.clone();
    let ret = sig.ret.clone();
    let ret_form = sig.ret_form.clone();
    let geist_param = sig.geist_param.clone();
    let eigen_param = sig.eigen_param.clone();
    let or_nutz = sig.or_nutz.clone();
    let req = sig.vertrag_requires.clone();
    let ens = sig.vertrag_ensures.clone();
    let ext = sig.extern_;
    let gr = sig.geist_rueck;
    let mk = || FnSig {
        params: params.clone(),
        ret: ret.clone(),
        ret_form: ret_form.clone(),
        extern_: ext,
        geist_param: geist_param.clone(),
        geist_rueck: gr,
        eigen_param: eigen_param.clone(),
        or_nutz: or_nutz.clone(),
        vertrag_requires: req.clone(),
        vertrag_ensures: ens.clone(),
    };
    s.fns.insert(voll.to_string(), mk());
    // Kurz nur bei Eindeutigkeit (O40: zwei Private eines Namens → voll).
    if !s.fns.contains_key(kurz) {
        s.fns.insert(kurz.to_string(), mk());
    } else if s.fns.get(kurz).is_some_and(|e| e.extern_ != ext || e.params != params) {
        // Kollision verschiedener Signaturen: kurz zeigt auf die erste — Rufe über
        // den Vollnamen treffen trotzdem (unten in `senke_ruf`).
    }
}

/// Plancode-Schlüssel: voll, damit O40-Paare je ihren Plan tragen.
fn schluessel_fuer(voll: &str, _kurz: &str, _s: &Senke) -> String {
    voll.to_string()
}

fn sammle_tor(s: &mut Senke, g: &SyscallDecl, voll: &str, span: Span) {
    let kurz = g.name.text.clone();
    // Architektur wählen (der Ruf nennt sie bei Fehlschlag).
    if g.arch.text != ziel_arch(s.ziel) {
        s.fremde_tore.insert(kurz);
        s.fremde_tore.insert(voll.to_string());
        return;
    }
    if g.ungebunden() {
        weigere(s, "Y102", span, format!("unbound gate {kurz}"));
        s.tote_items.insert(kurz);
        return;
    }
    // Stapelklausel: genau eine (`N447`), gebunden in `regs in` (`N446`) -- sonst benannt verweigert.
    let stapel_tor = match g.stapel.as_slice() {
        [] => None,
        [reg] => {
            let stelle = g
                .regs_in
                .iter()
                .find(|(r, _)| r.text == reg.text)
                .and_then(|(_, p)| g.parameter.iter().position(|q| q.name.text == p.text));
            match stelle {
                Some(stelle) => {
                    s.kind.tore.insert(kurz.clone());
                    Some(stapeltor::StapelTor { reg: reg.text.clone(), stelle })
                }
                None => {
                    weigere(s, "Y102", span, format!("stack-carrying gate {kurz}: the stack register binds no parameter"));
                    s.tote_items.insert(kurz.clone());
                    s.tote_items.insert(voll.to_string());
                    return;
                }
            }
        }
        _ => {
            weigere(s, "Y102", span, format!("stack-carrying gate {kurz} with several stack registers"));
            s.tote_items.insert(kurz.clone());
            s.tote_items.insert(voll.to_string());
            return;
        }
    };
    if matches!(g.paarung, SyscallPaarung::Kernel { .. }) {
        weigere(s, "Y102", span, format!("kernel-paired gate {kurz}"));
        s.tote_items.insert(kurz.clone());
        s.tote_items.insert(voll.to_string());
        return;
    }
    // Fehlerkanal und errno-Tabelle baut der Tor-Schwanz unten (`or_nutz_tor`).
    if g.via.is_some() {
        // Gebundene `via`-Tore: Felder kamen vom Ziel — senken wie direkt.
    }
    let nummer = match konst_u64(s, &g.nummer) {
        Some(n) => match i64::try_from(n) {
            Ok(v) => v,
            Err(_) => {
                weigere(s, "Y102", span, format!("gate {kurz} with huge number"));
                return;
            }
        },
        None => {
            weigere(s, "Y102", span, format!("gate {kurz} with non-constant number"));
            return;
        }
    };
    // Parameter breit (fremde ABI), in deklarierter Ordnung.
    let alt = s.eng_modus;
    s.eng_modus = false;
    let mut param_typen = Vec::new();
    let mut ok = true;
    for p in &g.parameter {
        match senke_typ(s, &p.typ) {
            Some((ll, z)) => param_typen.push((ll, z)),
            None => {
                ok = false;
                break;
            }
        }
    }
    let ret = match &g.ergebnis {
        Some(TypExpr::Never(_)) => None,
        Some(t) => match senke_typ(s, t) {
            Some((ll, z)) => Some((ll, z)),
            None => {
                ok = false;
                None
            }
        },
        None => None,
    };
    s.eng_modus = alt;
    if !ok {
        s.tote_items.insert(kurz);
        return;
    }
    let nie = matches!(&g.ergebnis, Some(TypExpr::Never(_)));
    // Eingaben in geschriebener Ordnung, mit Parameterplatz.
    let mut platz: HashMap<String, usize> = HashMap::new();
    for (i, p) in g.parameter.iter().enumerate() {
        platz.insert(p.name.text.clone(), i);
    }
    let mut eingaben = Vec::new();
    for (reg, param) in &g.regs_in {
        match platz.get(&param.text) {
            Some(i) => eingaben.push((reg.text.clone(), *i)),
            None => {
                weigere(s, "Y102", span, format!("gate {kurz} binds unknown parameter {}", param.text));
                return;
            }
        }
    }
    let (template, ret_reg): (&'static str, &'static str) = if s.ziel.name == "x86_64" {
        ("syscall", "rax")
    } else {
        ("svc #0", "x0")
    };
    let clobbers: Vec<String> = g.clobbers.iter().map(|c| c.text.clone()).collect();
    // Fehlerkanal am Tor: Antwort ist der Kanal-Struct, errno-Tabelle dazu.
    let or_nutz_tor = match &g.fehler {
        Some(r) => or_fuer(s, &g.ergebnis, &r.text, span),
        None => None,
    };
    let ret_tor = match or_nutz_tor.clone() {
        Some(or) => Some((or_struct(or.p), Zeichen::Egal)),
        None => ret.clone(),
    };
    if g.fehler.is_some() && or_nutz_tor.is_none() {
        s.tote_items.insert(kurz);
        return;
    }
    let errors = match dekodiere_errors(s, g, or_nutz_tor.as_ref(), span) {
        Some(e) => e,
        None => return,
    };
    let tor = Tor {
        nummer,
        eingaben: eingaben.clone(),
        param_typen,
        ret: ret_tor,
        nie,
        template,
        clobbers: clobbers.clone(),
        ret_reg,
        stapel: stapel_tor.clone(),
        or_nutz: or_nutz_tor,
        errors,
    };
    s.tore.insert(voll.to_string(), tor.clone());
    s.tore.insert(kurz.clone(), tor);
    // Beleg: Nummer, Schablone, Bindungen (`x0=0`), Austritt, Clobbers.
    let bindungen: Vec<String> = eingaben.iter().map(|(r, i)| format!("{r}={i}")).collect();
    s.beleg_tore.push(TorBeleg {
        name: kurz,
        nummer,
        schablone: if stapel_tor.is_some() { format!("{template}+child") } else { template.to_string() },
        bindungen,
        austritt: ret_reg.to_string(),
        clobbers,
    });
}

fn sammle_konst(s: &mut Senke, kd: &KonstDecl, span: Span) {
    let n = kd.name.text.clone();
    // Gleitkomma-Konstante (Bits merken — Gebrauch faltet).
    if matches!(&kd.typ, TypExpr::Float(_)) {
        if let ExprArt::Gleitkomma { bits, .. } = &kd.wert.art {
            let f32 = matches!(&kd.typ, TypExpr::Float(f) if f.wort.text() == "f32");
            s.gkonst.insert(n.clone(), (*bits, f32));
        }
    }
    let alt = s.eng_modus;
    s.eng_modus = true;
    let gesenkt = senke_typ(s, &kd.typ);
    s.eng_modus = alt;
    let (ll, z) = match gesenkt {
        Some(x) => x,
        None => return,
    };
    let init = konst_init_text(s, &kd.wert, &ll);
    match init {
        Some(t) => {
            s.globale.insert(n, Global { typ: ll, zeichen: z, form: kd.typ.clone(), konstant: true, init_text: Some(t) });
        }
        None => {
            weigere(s, "Y101", span, format!("constant {n} with non-constant initializer"));
        }
    }
    let _ = kd.oeffentlich;
}

fn sammle_statisch(s: &mut Senke, sd: &StatischDecl, span: Span) {
    let n = sd.name.text.clone();
    let alt = s.eng_modus;
    s.eng_modus = true;
    let gesenkt = senke_typ(s, &sd.typ);
    s.eng_modus = alt;
    let (ll, z) = match gesenkt {
        Some(x) => x,
        None => return,
    };
    // `= 0` an Aggregaten heißt null (wie überall in dieser Sprache).
    let init = konst_init_text(s, &sd.wert, &ll);
    if let Some(align) = sd.ausrichtung.as_ref().and_then(|e| konst_u64(s, e)) {
        s.global_align.insert(n.clone(), align);
    }
    match init {
        Some(t) => {
            s.globale.insert(n, Global { typ: ll, zeichen: z, form: sd.typ.clone(), konstant: !sd.veraenderlich, init_text: Some(t) });
        }
        None => {
            weigere(s, "Y101", span, format!("static {n} with non-constant initializer"));
        }
    }
    let _ = sd.section;
    let _ = sd.oeffentlich;
}

/// Konstanten-Init als LLVM-Text (Zahlen, `const fn`-Rufe, Verbunde, Felder).
fn konst_init_text(s: &mut Senke, e: &Expr, ll: &LlTyp) -> Option<String> {
    // Gefaltet zuerst (EIN Register — `const fn` eingeschlossen).
    if matches!(ll, LlTyp::Int(_)) {
        if let Some(v) = s.umg.konst_wert(&s.modul, e) {
            if let LlTyp::Int(w) = ll {
                return Some(falte_int(v, *w));
            }
        }
    }
    match &e.art {
        ExprArt::Zahl(v) => match ll {
            LlTyp::Int(w) => {
                let als: i128 = i128::try_from(*v).ok()?;
                Some(falte_int(als, *w))
            }
            LlTyp::Feld(_, _) | LlTyp::Anon(_) | LlTyp::Benannt(_) if *v == 0 => {
                Some("zeroinitializer".to_string())
            }
            LlTyp::F32 => Some(format!("0x00000000")),
            LlTyp::F64 => Some(format!("0x0000000000000000")),
            LlTyp::Ptr => {
                if *v == 0 {
                    Some("null".to_string())
                } else {
                    None
                }
            }
            _ => None,
        },
        ExprArt::Wahr => Some("true".to_string()),
        ExprArt::Falsch => Some("false".to_string()),
        ExprArt::Gleitkomma { bits, .. } => match ll {
            LlTyp::F32 | LlTyp::F64 => Some(hexfloat(*bits, false)),
            _ => None,
        },
        ExprArt::Ort(o) if o.suffixe.is_empty() => match ll {
            LlTyp::F32 | LlTyp::F64 => {
                let (bits, _) = s.gkonst.get(&o.basis.text).cloned()?;
                Some(hexfloat(bits, false))
            }
            _ => {
                // Bloßer Varianten-Fall als Ort (`Leer`).
                if let Some((tname, fall_nr, nutz)) = varianten_fall(s, &o.basis.text) {
                    if nutz.is_none() {
                        sorge_variante(s, &tname, false);
                        let groesste = s.variant_typen.get(&tname).map(|(_, g)| *g).unwrap_or(0);
                        if groesste == 0 {
                            return Some(format!("{{ i32 {fall_nr} }}"));
                        }
                        return Some(format!("{{ i32 {fall_nr}, [{groesste} x i8] zeroinitializer }}"));
                    }
                }
                None
            }
        },
        ExprArt::ArrayLit(xs) => match ll {
            LlTyp::Feld(elem, _) => {
                let mut teile = Vec::new();
                for x in xs {
                    teile.push(format!("{} {}", elem.text(), konst_init_text(s, x, elem)?));
                }
                Some(format!("[{}]", teile.join(", ")))
            }
            _ => None,
        },
        ExprArt::Ruf(r) => {
            // `None` als Options-Konstante.
            if r.heisst("None") && r.argumente.is_empty() {
                if let LlTyp::Benannt(n) = ll {
                    if n == "gabopt" {
                        return Some("{ i32 0, [8 x i8] zeroinitializer }".to_string());
                    }
                }
            }
            // Varianten-Fall als Konstante (`Kurz(5)`, `Leer`).
            if let Some(pfad) = r.path() {
                if r.marken.is_empty() {
                    if let Some((tname, fall_nr, nutz)) = varianten_fall(s, &kurzname(pfad)) {
                        sorge_variante(s, &tname, false);
                        let groesste = s.variant_typen.get(&tname).map(|(_, g)| *g).unwrap_or(0);
                        let nutz_text = match (&nutz, r.argumente.as_slice()) {
                            (None, []) => {
                                if groesste == 0 {
                                    String::new()
                                } else {
                                    format!(", [{groesste} x i8] zeroinitializer")
                                }
                            }
                            (Some(nt), [a]) => {
                                // Ganzzahl-Nutzlast als Bytes (little-endian).
                                let (nll, _) = senke_typ(s, nt)?;
                                let w = nll.breite()?;
                                let v = s.umg.konst_wert(&s.modul, a)?;
                                let bytes = (0..groesste.max(w as u64 / 8)).map(|i| format!("i8 {}", ((v >> (8 * i)) & 255))).collect::<Vec<_>>().join(", ");
                                format!(", [{groesste} x i8] [{bytes}]")
                            }
                            _ => return None,
                        };
                        return Some(format!("{{ i32 {fall_nr}{nutz_text} }}"));
                    }
                }
            }
            None
        }
        ExprArt::Klammer(x) => konst_init_text(s, x, ll),
        ExprArt::Ruf(r) if r.ist_verbundwert() => {
            // Verbund-Init aus Konstanten (Marken in Deklarationsordnung).
            let pfad = r.path()?.clone();
            let name = kurzname(&pfad);
            let rec_name = s.aliase.get(&name).cloned().and_then(|a| match grundform(s, &a) {
                TypExpr::Pfad(p) => p.einfach().map(|e| e.text.clone()),
                _ => None,
            }).unwrap_or(name);
            let felder = s.rekorde.get(&rec_name).cloned()?;
            let mut gegeben: HashMap<String, Expr> = HashMap::new();
            for (m, a) in r.marken.iter().zip(r.argumente.iter()) {
                gegeben.insert(m.text.clone(), a.clone());
            }
            let mut teile = Vec::new();
            for (fname, ftyp) in &felder {
                let ae = gegeben.get(fname)?;
                let (fll, _) = senke_typ(s, ftyp)?;
                teile.push(format!("{} {}", fll.text(), konst_init_text(s, ae, &fll)?));
            }
            Some(format!("{{ {} }}", teile.join(", ")))
        }
        ExprArt::Ort(o) if o.suffixe.is_empty() => {
            // Bloßer Varianten-Fall als Ort (`Leer`).
            if let Some((tname, fall_nr, nutz)) = varianten_fall(s, &o.basis.text) {
                if nutz.is_none() {
                    let groesste = s.variant_typen.get(&tname).map(|(_, g)| *g).unwrap_or(0);
                    if groesste == 0 {
                        return Some(format!("{{ i32 {fall_nr} }}"));
                    }
                    return Some(format!("{{ i32 {fall_nr}, [{groesste} x i8] zeroinitializer }}"));
                }
            }
            // Benannte Konstante (Kette über `umg` auflösen).
            let v = s.umg.konst_wert(&s.modul, e)?;
            match ll {
                LlTyp::Int(w) => Some(falte_int(v, *w)),
                _ => None,
            }
        }
        _ => None,
    }
}

// ===================================================================================
// Emission (Funktionen, Globale, Laufzeit, Eintritt)
// ===================================================================================

/// Rufer-Namen vergeben (kurz bei Eindeutigkeit, sonst `m_f`).
fn vergebe_emitnamen(s: &mut Senke) {
    let mut kurz_besitzer: BTreeMap<String, String> = BTreeMap::new();
    let mut volle: Vec<String> = s.plaene.keys().cloned().collect();
    volle.sort();
    for v in &volle {
        let kurz = v.rsplit("::").next().unwrap_or(v).to_string();
        match kurz_besitzer.get(&kurz) {
            None => {
                kurz_besitzer.insert(kurz.clone(), v.clone());
            }
            Some(_) => {
                kurz_besitzer.insert(kurz.clone(), String::new());
            }
        }
    }
    for v in &volle {
        let kurz = v.rsplit("::").next().unwrap_or(v).to_string();
        if kurz_besitzer.get(&kurz).is_some_and(|b| b == v) {
            s.emitnamen.insert(v.clone(), kurz.clone());
            // Kurzform nur, wenn der Plan unter kurz liegt — Rufe lösen beides.
            if !s.fns.contains_key(&kurz) {
                if let Some(sig) = s.fns.get(v).cloned() {
                    s.fns.insert(kurz, sig);
                }
            }
        } else {
            s.emitnamen.insert(v.clone(), v.replace("::", "_"));
        }
    }
}



/// Parametertext ohne Namen (`i32 noundef`, für `declare`).
fn param_text(t: &LlTyp, eigen: bool) -> String {
    let mut a = String::new();
    if t.ist_int() || matches!(t, LlTyp::F32 | LlTyp::F64 | LlTyp::Ptr) {
        a.push_str(" noundef");
    }
    if eigen {
        a.push_str(" noalias");
    }
    format!("{}{a}", t.text())
}

/// Parametertext mit Namen (`i64 noundef %p0` — Attribute VOR dem Namen).
fn param_text_mit(t: &LlTyp, eigen: bool, i: usize) -> String {
    let mut a = String::new();
    if t.ist_int() || matches!(t, LlTyp::F32 | LlTyp::F64 | LlTyp::Ptr) {
        a.push_str(" noundef");
    }
    if eigen {
        a.push_str(" noalias");
    }
    format!("{}{a} %p{i}", t.text())
}

/// Parameterzeile mit Zusatz-Attributen (`dereferenceable`, `align`) VOR dem Namen.
fn param_zeile(t: &LlTyp, eigen: bool, i: usize, zusatz: &str) -> String {
    let mut a = String::new();
    if t.ist_int() || matches!(t, LlTyp::F32 | LlTyp::F64 | LlTyp::Ptr) {
        a.push_str(" noundef");
    }
    if eigen {
        a.push_str(" noalias");
    }
    format!("{}{a}{zusatz} %p{i}", t.text())
}

fn emit_funktionen(s: &mut Senke) {
    let plaene: Vec<(String, FnPlan)> = s.plaene.clone().into_iter().collect();
    for (voll, plan) in plaene {
        match plan {
            FnPlan::Fertig { .. } => {
                if assembler::emittiere(s, &voll) {
                    continue;
                }
                // Extern: Deklaration (fremde ABI — kein Körper, keine Annahmen).
                if let Some(sig) = s.fns.get(&voll).cloned() {
                    if sig.extern_ {
                        let emit = s.emitnamen.get(&voll).cloned().unwrap_or_else(|| voll.clone());
                        let ret = sig.ret.clone().map(|(t, _)| t.text()).unwrap_or_else(|| "void".to_string());
                        let ps: Vec<String> = sig
                            .params
                            .iter()
                            .zip(sig.eigen_param.iter().chain(std::iter::repeat(&false)))
                            .map(|((t, _), e)| param_text(t, *e))
                            .collect();
                        let _ = writeln!(s.rumpf, "declare {ret} {}({})", gname(&emit), ps.join(", "));
                        s.beleg_funktionen.push((
                            emit,
                            sig.params.iter().map(|(t, _)| t.text()).collect(),
                            sig.ret.clone().map(|(t, _)| t.text()).unwrap_or_else(|| "void".to_string()),
                            "extern".to_string(),
                        ));
                    }
                }
            }
            FnPlan::Impl { rumpf, params, namen, formen, modul } => {
                if let Some(info) = s.rek.get(&voll).cloned() {
                    emit_rek(s, &voll, &info);
                } else {
                    emit_impl(s, &voll, &rumpf, &params, &namen, &formen, &modul);
                }
            }
            FnPlan::Fertig { .. } => {}
        }
    }
    // Ausgelagerte `child`-Regionen (ihre Funktionen stehen nach denen, die sie riefen).
    stapeltor::abarbeiten(s);
    eintritte::emittiere(s);
    let benutzt = stapeltor::benutzt_text(s);
    s.helfer.push_str(&benutzt);
}

fn emit_impl(s: &mut Senke, voll: &str, rumpf: &Block, params: &[(LlTyp, Zeichen)], namen: &[String], formen: &[TypExpr], modul: &str) {
    let emit = s.emitnamen.get(voll).cloned().unwrap_or_else(|| voll.to_string());
    let sig = match s.fns.get(voll).cloned() {
        Some(x) => x,
        None => return,
    };
    // Modul setzen (Konstanten lösen modulnah auf — `NPLAETZE` steht im Modul).
    s.modul = modul.to_string();
    let ret_ll = sig.ret.clone().map(|(t, _)| t).unwrap_or(LlTyp::Void);
    let ret_text = ret_ll.text();
    // Zusatz-Attribute aus den `requires` (dereferenceable, align).
    let zusatz = parameter_attribute(&sig.vertrag_requires, namen, &sig.params);
    let ps: Vec<String> = sig
        .params
        .iter()
        .zip(sig.eigen_param.iter().chain(std::iter::repeat(&false)))
        .enumerate()
        .map(|(i, ((t, _), e))| param_zeile(t, *e, i, zusatz.get(i).map(String::as_str).unwrap_or("")))
        .collect();
    let _ = writeln!(s.rumpf, "define {ret_text} {}({}) {{", gname(&emit), ps.join(", "));
    let _ = writeln!(s.rumpf, "eintritt:");
    let (text, allocas) = {
        let kind = stapeltor::Zustand::fuer(&s.kind, rumpf);
        let mut k = Koerper {
            s,
            text: String::new(),
            allocas: String::new(),
            zaehler: 0,
            bloecke: 0,
            bereiche: vec![HashMap::new()],
            funktionsname: emit.clone(),
            gegenwart: "eintritt".to_string(),
            rueck: sig.ret.clone(),
            beendet: false,
            schleifen: Vec::new(),
            sperren: Vec::new(),
            maske_zellen: BTreeMap::new(),
            kind,
            alt_wert: None,
            ergebnis_wert: None,
            or_nutz: sig.or_nutz.clone(),
            modul: modul.to_string(),
            geist_rueck: sig.geist_rueck,
            tausch_rueck: None,
            rek: None,
            sperrtiefe: 0,
        };
        // Parameter in Allocas (echte Namen binden — der Körper liest sie).
        // HINWEIS: Geister stehen nicht in `params` — Zählung läuft nur darüber.
        for (i, (((pt, pz), pname), pform)) in params.iter().zip(namen.iter()).zip(formen.iter()).enumerate() {
            let p = k.alloca(&pt.text());
            k.zeile(&format!("store {} %p{i}, ptr {p}, align {}", pt.text(), nat_align(pt)));
            let fl = ist_fluechtig(k.s, &Some(pform.clone()));
            k.lege_an(
                pname.clone(),
                Bindung { ptr: p, ll: pt.clone(), zeichen: *pz, form: Some(pform.clone()), fluechtig: fl },
            );
        }
        for pred in &sig.vertrag_requires.clone() {
            nehme_an(&mut k, pred, "requires");
        }
        senke_block(&mut k, rumpf);
        // Fallender Ausgang: `void` kehrt zurück, Wert bekommt `unreachable`
        // (der Prüfer hält alle Pfade — hierher kommt kein Lauf).
        if !k.beendet {
            if ret_ll == LlTyp::Void {
                k.zeile("ret void");
            } else {
                k.zeile("unreachable");
            }
        }
        (k.text, k.allocas)
    };
    s.rumpf.push_str(&allocas);
    s.rumpf.push_str(&text);
    let _ = writeln!(s.rumpf, "}}");
    s.beleg_funktionen.push((
        emit,
        sig.params.iter().map(|(t, _)| t.text()).collect(),
        ret_text,
        "impl".to_string(),
    ));
}

/// Eintritt `_start`: `main` rufen, Antwort an das Austritts-Tor reichen.
/// Die Nummern stehen je Ziel im Erzeuger (231 / 94 — `exit_group`).
fn emit_start(s: &mut Senke) {
    let (main, breite) = match s.eintritt.clone() {
        Some(x) => x,
        None => return,
    };
    let emit_main = s.emitnamen.iter().find(|(v, _)| v.rsplit("::").next() == Some(main.as_str())).map(|(_, e)| e.clone()).unwrap_or(main.clone());
    let ret_text = s.fns.get(&main).and_then(|sig| sig.ret.clone()).map(|(t, _)| t.text()).unwrap_or_else(|| "i32".to_string());
    let _ = writeln!(s.rumpf, "define void @\"_start\"() {{");
    let _ = writeln!(s.rumpf, "eintritt:");
    if breite.is_none() {
        // `main -> never`: rufen, nie zurück.
        let _ = writeln!(s.rumpf, "  call void {}()", gname(&emit_main));
        let _ = writeln!(s.rumpf, "  unreachable");
        let _ = writeln!(s.rumpf, "}}");
        return;
    }
    let _ = writeln!(s.rumpf, "  %c = call {ret_text} {}()", gname(&emit_main));
    // Austrittscode ist i64 (Antwort erweitern — Codes sind vorzeichenlos).
    let breite_main = s.fns.get(&main).and_then(|sig| sig.ret.clone()).and_then(|(t, _)| t.breite()).unwrap_or(32);
    let code = if breite_main != 64 {
        let _ = writeln!(s.rumpf, "  %c64 = zext i{breite_main} %c to i64");
        "%c64"
    } else {
        "%c"
    };
    // Austritt je Ziel (rohes Tor, Antwort im ersten Register).
    if s.ziel.name == "x86_64" {
        let _ = writeln!(
            s.rumpf,
            "  call void asm sideeffect \"syscall\", \"{{rax}},{{rdi}},~{{rcx}},~{{r11}},~{{memory}}\"(i64 231, i64 {code})"
        );
    } else {
        let _ = writeln!(
            s.rumpf,
            "  call void asm sideeffect \"svc #0\", \"{{x8}},{{x0}},~{{memory}}\"(i64 94, i64 {code})"
        );
    }
    let _ = writeln!(s.rumpf, "  unreachable");
    let _ = writeln!(s.rumpf, "}}");
    let _ = breite;
}

/// Globale, Tabellen, Schlösser, Atomics, Arenen.
fn emit_globale(s: &mut Senke) {    // Skalare und Felder.
    let globale: Vec<(String, Global)> = s.globale.clone().into_iter().collect();
    for (n, g) in &globale {
        let init = g.init_text.clone().unwrap_or_else(|| "zeroinitializer".to_string());
        let link = if g.konstant { "constant" } else { "global" };
        let alignment = s.global_align.get(n).copied().unwrap_or(u64::from(nat_align(&g.typ)));
        let _ = writeln!(s.rumpf, "@{} = {link} {} {init}, align {alignment}", escape_name(n), g.typ.text());
    }
    // Tabellen: `%Tab = type { [N x %Tab$slot] }` plus Global.
    let tabellen: Vec<(String, (u64, String))> = s.tabellen.clone().into_iter().collect();
    for (n, (len, slot)) in &tabellen {
        let felder = s.tab_slots.get(n).cloned().unwrap_or_default();
        let alt = s.eng_modus;
        s.eng_modus = true;
        let mut teile = Vec::new();
        let mut ok = true;
        for (_, ft) in &felder {
            match senke_typ(s, ft) {
                Some((ll, _)) => teile.push(ll.text()),
                None => {
                    ok = false;
                    break;
                }
            }
        }
        s.eng_modus = alt;
        if !ok {
            continue;
        }
        let slot_layout = format!("{{ {} }}", teile.join(", "));
        if s.typedefs.insert(slot.clone()) {
            let _ = writeln!(s.kopf, "%{slot} = type {slot_layout}");
            s.beleg_typen.push((slot.clone(), slot_layout));
        }
        let tab_layout = format!("{{ [{len} x %{slot}] }}");
        let _ = writeln!(s.kopf, "%{n} = type {tab_layout}");
        s.beleg_typen.push((n.clone(), tab_layout.clone()));
        let _ = writeln!(s.rumpf, "@{} = global %{n} zeroinitializer, align 8", escape_name(n));
    }
    // Schlösser: Ticket-Wörter (`naechst`/`bereit`).
    let schloesser: Vec<String> = s.schloesser.keys().cloned().collect();
    for n in &schloesser {
        let _ = writeln!(s.rumpf, "{} = global i32 0, align 4", gteil(n, "naechst"));
        let _ = writeln!(s.rumpf, "{} = global i32 0, align 4", gteil(n, "bereit"));
        if s.schloesser[n] {
            let _ = writeln!(s.rumpf, "{} = global i32 0, align 4", gteil(n, "leser"));
        }
    }
    // Atomics: ein Wort je Name.
    let atomare: Vec<(String, (LlTyp, String))> = s.atomare.clone().into_iter().collect();
    for (n, (ll, _)) in &atomare {
        let init = match ll {
            LlTyp::Feld(_, _) | LlTyp::Anon(_) | LlTyp::Benannt(_) => "zeroinitializer".to_string(),
            _ => "0".to_string(),
        };
        let _ = writeln!(s.rumpf, "@{} = global {} {init}, align {}", escape_name(n), ll.text(), nat_align(ll));
    }
    // Arenen: vier Wörter (Basis, belegt, bereit, Freilisten-Kopf) — KEIN Feld
    // (kein RAM vorab; Reserve ist Adressraum via `mmap`, Commit via `mprotect`,
    // siehe `arena_bereit`). Der Kopf trägt `-1` für leer (TODO §1-B).
    let arenen: Vec<(String, ArenaInfo)> = s.arenen.clone().into_iter().collect();
    for (n, _) in &arenen {
        let _ = writeln!(s.rumpf, "{} = global i64 0, align 8", gteil(n, "basis"));
        let _ = writeln!(s.rumpf, "{} = global i64 0, align 8", gteil(n, "belegt"));
        let _ = writeln!(s.rumpf, "{} = global i64 0, align 8", gteil(n, "bereit"));
        let _ = writeln!(s.rumpf, "{} = global i64 -1, align 8", gteil(n, "frei"));
        let _ = writeln!(s.rumpf, "{} = global i64 0, align 8", gteil(n, "meta"));
    }
}

fn escape_name(n: &str) -> String {
    format!("\"{}\"", n.replace('"', ""))
}

// ===================================================================================
// Eintrittspunkte
// ===================================================================================

fn neue_senke<'a>(absagen: &'a mut Absagen, ziel: &'static Ziel) -> Senke<'a> {
    Senke {
        absagen,
        umg: crate::umgebung::Umgebung::sammle(&Programm { items: vec![] }),
        modul: String::new(),
        tote_items: BTreeSet::new(),
        ziel,
        kopf: String::new(),
        rumpf: String::new(),
        helfer: String::new(),
        typedefs: BTreeSet::new(),
        fns: BTreeMap::new(),
        tore: BTreeMap::new(),
        fremde_tore: BTreeSet::new(),
        eintritt: None,
        plaene: BTreeMap::new(),
        globale: BTreeMap::new(),
        global_align: BTreeMap::new(),
        aliase: BTreeMap::new(),
        rekorde: BTreeMap::new(),
        varianten: BTreeMap::new(),
        variant_typen: BTreeMap::new(),
        gruende: BTreeMap::new(),
        schloesser: BTreeMap::new(),
        maskiert: BTreeSet::new(),
        kind: Default::default(),
        eintritte: Vec::new(),
        mit_eintritt: false,
        atomare: BTreeMap::new(),
        tabellen: BTreeMap::new(),
        geister: BTreeSet::new(),
        geraete: BTreeMap::new(),
        transitionen: BTreeMap::new(),
        gkonst: BTreeMap::new(),
        arenen: BTreeMap::new(),
        braucht_assume: false,
        braucht_trap: false,
        braucht_fabs: false,
        beleg_typen: Vec::new(),
        beleg_annahmen: Vec::new(),
        beleg_tore: Vec::new(),
        beleg_funktionen: Vec::new(),
        nebenlaeufig: Vec::new(),
        start_wurzeln: BTreeSet::new(),
        emitnamen: BTreeMap::new(),
        rek: BTreeMap::new(),
        tab_slots: BTreeMap::new(),
        tab_baeume: BTreeMap::new(),
        formate: BTreeSet::new(),
        tab_ops: BTreeMap::new(),
        inv_range: BTreeMap::new(),
        tbaa_pfad: BTreeMap::new(),
        tbaa_struct: BTreeMap::new(),
        tbaa_tags: BTreeMap::new(),
        meta_knoten: BTreeMap::new(),
        meta_nr: 0,
        eng_modus: true,
        noalias_innen: BTreeSet::new(),
        fakten: BTreeMap::new(),
        asm_defs: BTreeMap::new(),
        fremde_asm: BTreeMap::new(),
    }
}

/// **IR plus Beleg aus einem Lauf.** Der Beleg gehört zum IR derselben Sekunden —
/// zwei Läufe wären zwei Wahrheiten.
pub fn emittiere_llvm_mit_beleg(
    baum: &Programm,
    absagen: &mut Absagen,
    bau: crate::gatter::Bau,
    ziel: &'static Ziel,
) -> (String, LLVMBeleg) {
    let mut s = neue_senke(absagen, ziel);
    s.umg = crate::umgebung::Umgebung::sammle(baum);
    s.noalias_innen = noalias_innen(baum, &s.umg);
    sammle(&mut s, baum, bau);
    assembler::fremde_pruefen(&mut s);
    vergebe_emitnamen(&mut s);
    baue_rek_plan(&mut s);
    emit_globale(&mut s);
    emit_funktionen(&mut s);
    match stackless::lower(&s.rumpf, ziel, &s.beleg_typen) {
        Ok(body) => s.rumpf = body,
        Err(reason) => weigere(&mut s, "Y103", Span::neu(0, 0), format!("continuation lowering: {reason}")),
    }
    emit_start(&mut s);
    let mut aus = String::new();
    let _ = writeln!(aus, "; Gabbro→LLVM CANDIDATE for {} (untrusted — checker first)", ziel.triple);
    let _ = writeln!(aus, "target triple = \"{}\"", ziel.triple);
    let _ = writeln!(aus, "target datalayout = \"{}\"", ziel.datalayout);
    aus.push_str(&s.kopf);
    if s.braucht_assume {
        let _ = writeln!(aus, "declare void @llvm.assume(i1 noundef)");
    }
    if s.braucht_trap {
        let _ = writeln!(aus, "declare void @llvm.trap() cold noreturn nounwind");
    }
    if s.braucht_fabs {
        let _ = writeln!(aus, "declare float @llvm.fabs.f32(float)");
        let _ = writeln!(aus, "declare double @llvm.fabs.f64(double)");
    }
    aus.push_str(&s.rumpf);
    aus.push_str(&s.helfer);
    for (nr, def) in &s.meta_knoten {
        let _ = writeln!(aus, "!{nr} = {def}");
    }
    for (art, n) in &s.fakten {
        let _ = writeln!(aus, "; gabbro-fact {art} {n}");
    }
    if s.mit_eintritt {
        aus = eintritte::ohne_rote_zone(&aus);
    }
    let beleg = LLVMBeleg {
        ziel: ziel.triple,
        funktionen: s.beleg_funktionen.clone(),
        typen: s.beleg_typen.clone(),
        tore: s.beleg_tore.clone(),
        eintritt: s.eintritt.clone(),
        annahmen: s.beleg_annahmen.clone(),
        arenen: s
            .arenen
            .iter()
            .map(|(n, a)| (n.clone(), a.elem.text(), a.lo, a.hi, a.max))
            .collect(),
        schloesser: s.schloesser.keys().cloned().collect(),
        faeden: s.start_wurzeln.iter().cloned().collect(),
    };
    // Beleg-Funktionen nach Namen ordnen (deterministisch — gleiche Quelle, gleiche Zeilen).
    let mut beleg = beleg;
    beleg.funktionen.sort();
    beleg.typen.sort();
    (aus, beleg)
}

/// **Die Einheit als LLVM-IR-Text.** Geprüft zuerst (der Aufrufer prüft), verweigert
/// mit Namen (`Y101`–`Y104`, `Y106`).
pub fn emittiere_llvm(
    baum: &Programm,
    absagen: &mut Absagen,
    bau: crate::gatter::Bau,
    ziel: &'static Ziel,
) -> String {
    emittiere_llvm_mit_beleg(baum, absagen, bau, ziel).0
}

// ===================================================================================
// Fehlerkanal (`-> T or R`)
// ===================================================================================

/// Der Fehlerkanal (`-> T or R`): Nutzlast-Typ, Bytebreite, Grundname, T-Form.
#[derive(Clone)]
struct OrKanal {
    nutz: LlTyp,
    p: u64,
    grund: String,
    tform: Option<TypExpr>,
}

fn or_struct(p: u64) -> LlTyp {
    LlTyp::Anon(vec![LlTyp::Int(32), LlTyp::Feld(Box::new(LlTyp::Int(8)), p.max(1))])
}

/// Kanal hinter einer Ergebnisform (breit — ABI-Grenze).
fn or_fuer(s: &mut Senke, ergebnis: &Option<TypExpr>, grund: &str, span: Span) -> Option<OrKanal> {
    match ergebnis {
        Some(t) => {
            let (nll, _) = senke_typ(s, t)?;
            let groesse = match groesse_von_ll(s, &nll) {
                Some(g) => g,
                None => {
                    weigere(s, "Y102", span, "error channel over unsized answer".to_string());
                    return None;
                }
            };
            Some(OrKanal { nutz: nll, p: groesse.max(8), grund: grund.to_string(), tform: Some(t.clone()) })
        }
        None => Some(OrKanal { nutz: LlTyp::Void, p: 8, grund: grund.to_string(), tform: None }),
    }
}

/// Ok-Wert bauen (Tag 0 plus Nutzlast in die Bytes).
fn or_ok_wert(k: &mut Koerper, or: &OrKanal, v: Wert) -> Option<Wert> {
    let st = or_struct(or.p);
    let slot = k.alloca(&st.text());
    k.zeile(&format!("store {} undef, ptr {slot}, align 8", st.text()));
    let tp = k.tmp();
    k.zeile(&format!("{tp} = getelementptr {}, ptr {slot}, i32 0, i32 0", st.text()));
    k.zeile(&format!("store i32 0, ptr {tp}, align 4"));
    if or.nutz != LlTyp::Void {
        // Regions-Antwort (Tor): rohe Zahl wird Zeiger — die ZWEITE sanktionierte
        // `inttoptr`-Stelle (neben Gerätebasen): der Vertrag sagt frisch und
        // ungeteilt, die Vorlage formt die Adresse (Modell `tor.region`).
        let w = if or.nutz == LlTyp::Ptr && v.typ != LlTyp::Ptr {
            let form = v.form.clone();
            let a = angleiche(k, v, &LlTyp::Int(64), Zeichen::U)?;
            let t = k.tmp();
            k.zeile(&format!("{t} = inttoptr i64 {} to ptr", a.text));
            Wert { typ: LlTyp::Ptr, zeichen: Zeichen::Egal, text: t, form }
        } else {
            angleiche(k, v, &or.nutz, Zeichen::Egal)?
        };
        let pp = k.tmp();
        k.zeile(&format!("{pp} = getelementptr {}, ptr {slot}, i32 0, i32 1", st.text()));
        // Zeiger-Nutzlast ohne Guss (opaque Zeiger sind einander).
        let pc = if or.nutz == LlTyp::Ptr {
            pp.clone()
        } else {
            let c = k.tmp();
            k.zeile(&format!("{c} = getelementptr i8, ptr {pp}, i64 0"));
            c
        };
        k.zeile(&format!("store {} {}, ptr {pc}, align 1", or.nutz.text(), w.text));
    }
    let t = k.tmp();
    k.zeile(&format!("{t} = load {}, ptr {slot}, align 8", st.text()));
    Some(Wert { typ: st, zeichen: Zeichen::Egal, text: t, form: or.tform.clone() })
}

/// Fehler-Wert bauen (Tag 1 plus Grund in die ersten Bytes).
fn or_err_wert(k: &mut Koerper, or: &OrKanal, grund_text: &str) -> Wert {
    let st = or_struct(or.p);
    let slot = k.alloca(&st.text());
    k.zeile(&format!("store {} undef, ptr {slot}, align 8", st.text()));
    let tp = k.tmp();
    k.zeile(&format!("{tp} = getelementptr {}, ptr {slot}, i32 0, i32 0", st.text()));
    k.zeile(&format!("store i32 1, ptr {tp}, align 4"));
    let pp = k.tmp();
    k.zeile(&format!("{pp} = getelementptr {}, ptr {slot}, i32 0, i32 1", st.text()));
    let pc = k.tmp();
    k.zeile(&format!("{pc} = getelementptr i8, ptr {pp}, i64 0"));
    k.zeile(&format!("store i32 {grund_text}, ptr {pc}, align 1"));
    let t = k.tmp();
    k.zeile(&format!("{t} = load {}, ptr {slot}, align 8", st.text()));
    Wert { typ: st, zeichen: Zeichen::Egal, text: t, form: None }
}

/// Kanalwert ablegen: (Tag-Text, Nutzlast-Bytezeiger).
fn or_ablegen(k: &mut Koerper, v: &Wert, or: &OrKanal) -> (String, String) {
    let st = or_struct(or.p);
    let slot = k.alloca(&st.text());
    k.zeile(&format!("store {} {}, ptr {slot}, align 8", st.text(), v.text));
    let tp = k.tmp();
    k.zeile(&format!("{tp} = getelementptr {}, ptr {slot}, i32 0, i32 0", st.text()));
    let tag = k.tmp();
    k.zeile(&format!("{tag} = load i32, ptr {tp}, align 4"));
    let pp = k.tmp();
    k.zeile(&format!("{pp} = getelementptr {}, ptr {slot}, i32 0, i32 1", st.text()));
    (tag, pp)
}

// ===================================================================================
// errno-Dekodierung (Tor-Antwort → Kanalwert)
// ===================================================================================

/// errno-Tabelle zum Kanal: (Nummer, Grundwert) je Arm. Explizite Zahl gewinnt,
/// sonst gilt der Wert des Grundfalls (der Kern antwortet `-errno`).
fn dekodiere_errors(s: &mut Senke, g: &SyscallDecl, or: Option<&OrKanal>, span: Span) -> Option<Vec<(i64, i32)>> {
    if g.errors.is_empty() {
        return Some(Vec::new());
    }
    let or = match or {
        Some(o) => o,
        None => {
            weigere(s, "Y102", span, format!("errno decoding without error channel at gate {}", g.name.text));
            return None;
        }
    };
    let faelle = match s.gruende.get(&or.grund).cloned() {
        Some(f) => f,
        None => {
            weigere(s, "Y102", span, format!("unknown reason {}", or.grund));
            return None;
        }
    };
    let mut out = Vec::new();
    for (i, (_, fall)) in g.errors.iter().enumerate() {
        let rval = match faelle.iter().find(|(n, _)| n == &fall.text) {
            Some((_, w)) => *w as i32,
            None => {
                weigere(s, "Y102", span, format!("unknown case {} of reason {}", fall.text, or.grund));
                return None;
            }
        };
        let num: i64 = match g.errno_werte.get(i).and_then(|e| e.as_ref()) {
            Some(e) => match konst_u64(s, e) {
                Some(n) => match i64::try_from(n) {
                    Ok(v) => v,
                    Err(_) => {
                        weigere(s, "Y102", span, "huge errno number".to_string());
                        return None;
                    }
                },
                None => {
                    weigere(s, "Y102", span, "non-constant errno number".to_string());
                    return None;
                }
            },
            None => rval as i64,
        };
        out.push((num, rval));
    }
    Some(out)
}

// ===================================================================================
// Kanal-Rückgabe und Kanal-Bindung
// ===================================================================================

/// `return x` in einer Kanalfunktion: Grund → Fehler, Wert → Ok (plus `ensures`).
fn senke_return_kanal(k: &mut Koerper, x: &Expr, or: &OrKanal, rt: &LlTyp, span: Span) {
    // Grundform? → Fehlerpfad (Grundliteral, Grundort mit Grundform).
    let ist_grund = match &x.art {
        ExprArt::Grund { .. } => true,
        ExprArt::Ort(o) if o.suffixe.is_empty() => {
            k.suche(&o.basis.text).is_some_and(|b| match b.form.clone().map(|f| grundform(k.s, &f)) {
                Some(TypExpr::Pfad(p)) => p.einfach().is_some_and(|e| k.s.gruende.contains_key(&e.text)),
                _ => false,
            })
        }
        _ => false,
    };
    if ist_grund {
        let v = match senke_expr(k, x) {
            Some(v) => v,
            None => return,
        };
        let w = match angleiche_mit_weigere(k, v, &LlTyp::Int(32), span) {
            Some(w) => w,
            None => return,
        };
        let ev = or_err_wert(k, or, &w.text);
        k.zeile(&format!("ret {} {}", rt.text(), ev.text));
        return;
    }
    let v = match senke_expr(k, x) {
        Some(v) => v,
        None => return,
    };
    // Ok-Pfad: Nutzlast einwickeln (`ensures` sieht den Wert).
    let w = match angleiche(k, v, &or.nutz, Zeichen::Egal) {
        Some(w) => w,
        None => {
            weigere(k.s, "Y104", span, "return value outside the channel payload".to_string());
            return;
        }
    };
    if let Some(annahmen) = k.s.fns.get(&k.funktionsname).map(|f| f.vertrag_ensures.clone()) {
        let alt = k.ergebnis_wert.clone();
        k.ergebnis_wert = Some(w.clone());
        for pred in &annahmen {
            nehme_an(k, pred, "ensures");
        }
        k.ergebnis_wert = alt;
    }
    match or_ok_wert(k, or, w) {
        Some(ev) => {
            k.zeile(&format!("ret {} {}", rt.text(), ev.text));
        }
        None => {
            weigere(k.s, "Y104", span, "return value outside the channel payload".to_string());
        }
    }
}

/// `let x = f() else (e) { … }`: Kanal aufmachen — Wert nach `x`, Grund nach `e`.
fn senke_let_sonst_ruf(k: &mut Koerper, l: &LetSonst, r: &Ruf, span: Span) {
    // Kanal des Gerufenen (Tor wie Funktion, voller Pfad wie kurz).
    let gefunden: Option<(OrKanal, Option<TypExpr>)> = match r.path() {
        Some(p) => {
            let voll = p.text();
            let kurz = kurzname(p);
            if let Some(t) = k.s.tore.get(&voll).or_else(|| k.s.tore.get(&kurz)) {
                t.or_nutz.clone().map(|o| (o, None))
            } else if let Some(f) = k.s.fns.get(&voll).or_else(|| k.s.fns.get(&kurz)) {
                f.or_nutz.clone().map(|o| {
                    let tf = o.tform.clone();
                    (o, tf)
                })
            } else {
                None
            }
        }
        None => None,
    };
    let (or, tform): (OrKanal, Option<TypExpr>) = match gefunden {
        Some((o, tf)) => (o, tf),
        None => {
            weigere(k.s, "Y102", span, "error-channel binding without channel".to_string());
            return;
        }
    };
    let v = match senke_ruf(k, r, span) {
        Some(v) => v,
        None => return,
    };
    let (tag, pp) = or_ablegen(k, &v, &or);
    let ist_err = k.tmp();
    k.zeile(&format!("{ist_err} = icmp ne i32 {tag}, 0"));
    let weiter = k.block("sonst_weiter");
    let sonst = k.block("sonst_else");
    k.zeile(&format!("br i1 {ist_err}, label %{sonst}, label %{weiter}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{sonst}:");
    k.beendet = false;
    // Grund binden (i32 mit Grundform — `match e` versendet darüber).
    let pc = k.tmp();
    k.zeile(&format!("{pc} = getelementptr i8, ptr {pp}, i64 0"));
    let gv = k.tmp();
    k.zeile(&format!("{gv} = load i32, ptr {pc}, align 1"));
    let gslot = k.alloca("i32");
    k.zeile(&format!("store i32 {gv}, ptr {gslot}, align 4"));
    let gform = TypExpr::Pfad(Pfad {
        teile: vec![Ident { text: or.grund.clone(), span }],
        span,
    });
    k.oeffne();
    k.lege_an(
        l.fehlername.text.clone(),
        Bindung { ptr: gslot, ll: LlTyp::Int(32), zeichen: Zeichen::S, form: Some(gform) , fluechtig: false },
    );
    senke_block(k, &l.sonst);
    k.schliesse();
    if !k.beendet {
        k.zeile(&format!("br label %{weiter}"));
    }
    k.beendet = true;
    let _ = writeln!(k.text, "{weiter}:");
    k.beendet = false;
    // Nutzlast binden (Annotation oder Kanalform).
    let (ell, ez, eform) = match &l.typ {
        Some(t) => match senke_typ(k.s, t) {
            Some((ll, z)) => (ll, z, Some(t.clone())),
            None => return,
        },
        None => match tform.or(or.tform.clone()) {
            Some(tf) => match senke_typ(k.s, &tf) {
                Some((ll, z)) => (ll, z, Some(tf)),
                None => return,
            },
            None => (LlTyp::Int(8), Zeichen::U, None),
        },
    };
    if or.nutz == LlTyp::Void {
        // Kanal ohne Antwort: `x` trägt nichts (Geist-Bindung als Byte).
        let slot = k.alloca("i8");
        k.zeile(&format!("store i8 0, ptr {slot}, align 1"));
        k.lege_an(l.name.text.clone(), Bindung { ptr: slot, ll: ell, zeichen: ez, form: eform , fluechtig: false });
        return;
    }
    // Zeiger-Nutzlast braucht keinen Guss (opaque Zeiger sind einander).
    let lv = if ell == LlTyp::Ptr {
        let v = k.tmp();
        k.zeile(&format!("{v} = load ptr, ptr {pp}, align 8"));
        v
    } else {
        let pc2 = k.tmp();
        k.zeile(&format!("{pc2} = getelementptr i8, ptr {pp}, i64 0"));
        let v = k.tmp();
        k.zeile(&format!("{v} = load {}, ptr {pc2}, align 1", ell.text()));
        v
    };
    let slot = k.alloca(&ell.text());
    k.zeile(&format!("store {} {lv}, ptr {slot}, align {}", ell.text(), nat_align(&ell)));
    k.lege_an(l.name.text.clone(), Bindung { ptr: slot, ll: ell, zeichen: ez, form: eform , fluechtig: false });
}

// ===================================================================================
// Zeichenketten (begrenzt — Layout `{i32 Länge, [max x i8]}`)
// ===================================================================================

/// `gabstr`-Name aus einem LLVM-Typ.
fn gabstr_max(ll: &LlTyp) -> Option<u64> {
    match ll {
        LlTyp::Benannt(n) => n.strip_prefix("gabstr")?.parse().ok(),
        _ => None,
    }
}

/// Kettenliteral: Struct bei erwartetem `gabstr`, Bytezeiger sonst.
fn senke_kette(k: &mut Koerper, bytes: &[u8], erwartet: Option<(&LlTyp, Zeichen)>, _span: Span) -> Option<Wert> {
    if let Some((LlTyp::Benannt(n), _)) = erwartet {
        if let Some(max) = gabstr_max(&LlTyp::Benannt(n.clone())) {
            if (bytes.len() as u64) > max {
                weigere(k.s, "Y104", _span, "string literal longer than maximum".to_string());
                return None;
            }
            // Struct-Wert: Länge plus Bytes (Rest null).
            let st = LlTyp::Benannt(n.clone());
            let slot = k.alloca(&st.text());
            let lp = k.tmp();
            k.zeile(&format!("{lp} = getelementptr %{n}, ptr {slot}, i32 0, i32 0"));
            k.zeile(&format!("store i32 {}, ptr {lp}, align 4", bytes.len()));
            for (i, b) in bytes.iter().enumerate() {
                let bp = k.tmp();
                k.zeile(&format!("{bp} = getelementptr %{n}, ptr {slot}, i32 0, i32 1, i32 {i}"));
                k.zeile(&format!("store i8 {b}, ptr {bp}, align 1"));
            }
            let t = k.tmp();
            k.zeile(&format!("{t} = load %{n}, ptr {slot}, align 8"));
            return Some(Wert { typ: st, zeichen: Zeichen::Egal, text: t, form: None });
        }
    }
    // Bytezeiger (Tor-Argument, Fremdform).
    let n = k.s.meta_nr;
    k.s.meta_nr += 1;
    let name = format!(".kette_{n}");
    let len = bytes.len();
    let mut esc = String::new();
    for byte in bytes {
        esc.push_str(&format!("\\{byte:02X}"));
    }
    let _ = writeln!(k.s.kopf, "@\"{name}\" = private constant [{len} x i8] c\"{esc}\"");
    let t = k.tmp();
    k.zeile(&format!("{t} = getelementptr [{len} x i8], ptr @\"{name}\", i32 0, i32 0"));
    Some(Wert { typ: LlTyp::Ptr, zeichen: Zeichen::Egal, text: t, form: None })
}

/// `lenof`: Feldlänge als Konstante, String-Länge zur Laufzeit.
fn senke_lenof(k: &mut Koerper, t: &TypOderOrt, span: Span) -> Option<Wert> {
    match t {
        TypOderOrt::Typ(tt) => match grundform(k.s, tt) {
            TypExpr::Feld(a) => {
                let n = konst_u64(k.s, &a.laenge)?;
                Some(Wert::int(format!("{n}"), 64, Zeichen::U))
            }
            TypExpr::Zeichenkette { max, .. } => {
                let n = u64::try_from(max).ok()?;
                Some(Wert::int(format!("{n}"), 64, Zeichen::U))
            }
            _ => {
                weigere(k.s, "Y104", span, "length of this type".to_string());
                None
            }
        },
        TypOderOrt::Ort(o) => {
            let p = adresse_von_ort(k, o)?;
            match &p.ll {
                LlTyp::Feld(_, n) => Some(Wert::int(format!("{n}"), 64, Zeichen::U)),
                LlTyp::Benannt(n) if n.starts_with("gabstr") => {
                    // Laufzeit-Länge (Feld 0).
                    let lp = k.tmp();
                    k.zeile(&format!("{lp} = getelementptr %{n}, ptr {}, i32 0, i32 0", p.addr));
                    let t = k.tmp();
                    k.zeile(&format!("{t} = load i32, ptr {lp}, align 4"));
                    Some(Wert { typ: LlTyp::Int(32), zeichen: Zeichen::U, text: t, form: None })
                }
                _ => {
                    weigere(k.s, "Y104", span, "length of this place".to_string());
                    None
                }
            }
        }
    }
}

/// `sizeof`: statische Größe als Konstante.
fn senke_sizeof(k: &mut Koerper, t: &TypOderOrt, span: Span) -> Option<Wert> {
    let tt = match t {
        TypOderOrt::Typ(x) => x.clone(),
        TypOderOrt::Ort(o) => {
            let p = adresse_von_ort(k, o)?;
            match p.form.clone() {
                Some(f) => f,
                None => {
                    weigere(k.s, "Y104", span, "size of untyped place".to_string());
                    return None;
                }
            }
        }
    };
    match groesse_statisch(k.s, &tt, false) {
        Some(g) => Some(Wert::int(format!("{g}"), 64, Zeichen::U)),
        None => {
            weigere(k.s, "Y104", span, "size of unsized type".to_string());
            None
        }
    }
}

// ===================================================================================
// Zeichenketten-Operationen (Verkettung, Vergleich)
// ===================================================================================

/// Syntaktischer String-Test (ohne Emission — Kette oder `gabstr`-Form).
fn ist_string_expr(k: &Koerper, e: &Expr) -> bool {
    match &e.art {
        ExprArt::Kette(_) => true,
        ExprArt::Klammer(x) => ist_string_expr(k, x),
        ExprArt::Ort(o) => string_form_von_ort(k, o).is_some(),
        _ => false,
    }
}

/// `gabstr`-Max hinter einem Ort (nur Kartenlesung — keine Zeile).
fn string_form_von_ort(k: &Koerper, o: &Ort) -> Option<u64> {
    let t: TypExpr = if let Some(b) = k.suche(&o.basis.text) {
        b.form.clone()?
    } else if let Some(g) = k.s.globale.get(&o.basis.text) {
        g.form.clone()
    } else {
        return None;
    };
    match grundform(k.s, &t) {
        TypExpr::Zeichenkette { max, .. } => u64::try_from(max).ok(),
        _ => None,
    }
}

/// String-Operand senken: (Länge, Bytezeiger, Max).
fn string_operand(k: &mut Koerper, e: &Expr) -> Option<(String, String, u64)> {
    // Kette mit eigenem Max (Länge als Breite — Verkettung liest Längen).
    if let ExprArt::Kette(bytes) = &e.art {
        let v = senke_kette(k, bytes, None, e.span)?;
        return string_teile(k, &v);
    }
    if let ExprArt::Klammer(x) = &e.art {
        return string_operand(k, x);
    }
    let v = senke_expr(k, e)?;
    string_teile(k, &v)
}

/// Struct-Wert in (Länge, Bytezeiger, Max) legen.
fn string_teile(k: &mut Koerper, v: &Wert) -> Option<(String, String, u64)> {
    let max = gabstr_max(&v.typ)?;
    let slot = k.alloca(&v.typ.text());
    k.zeile(&format!("store {} {}, ptr {slot}, align 8", v.typ.text(), v.text));
    let lp = k.tmp();
    k.zeile(&format!("{lp} = getelementptr {}, ptr {slot}, i32 0, i32 0", v.typ.text()));
    let len = k.tmp();
    k.zeile(&format!("{len} = load i32, ptr {lp}, align 4"));
    let bp = k.tmp();
    k.zeile(&format!("{bp} = getelementptr {}, ptr {slot}, i32 0, i32 1, i32 0", v.typ.text()));
    Some((len, bp, max))
}

fn senke_string_binop(
    k: &mut Koerper,
    op: BinOp,
    a: &Expr,
    b: &Expr,
    span: Span,
    erwartet: Option<(&LlTyp, Zeichen)>,
) -> Option<Wert> {
    // Beide Seiten müssen Strings sein (sonst war die Weiche falsch).
    let (lena, bytesa, maxa) = string_operand(k, a)?;
    let (lenb, bytesb, maxb) = string_operand(k, b)?;
    match op {
        BinOp::Plus => {
            let max = match erwartet.and_then(|(t, _)| gabstr_max(t)) {
                Some(m) => m,
                None => maxa + maxb,
            };
            // Typedef für das Ergebnis (jede Breite steht einmal).
            let name = format!("gabstr{max}");
            if k.s.typedefs.insert(name.clone()) {
                let layout = format!("{{ i32, [{max} x i8] }}");
                let _ = writeln!(k.s.kopf, "%{name} = type {layout}");
                k.s.beleg_typen.push((name.clone(), layout));
            }
            let st = LlTyp::Benannt(name.clone());
            let slot = k.alloca(&st.text());
            // Summe prüfen (der Prüfer hält die Kopie — hierher kommt kein Überlauf).
            let lena64 = k.tmp();
            k.zeile(&format!("{lena64} = zext i32 {lena} to i64"));
            let lenb64 = k.tmp();
            k.zeile(&format!("{lenb64} = zext i32 {lenb} to i64"));
            let sum = k.tmp();
            k.zeile(&format!("{sum} = add i64 {lena64}, {lenb64}"));
            let passt = k.tmp();
            k.zeile(&format!("{passt} = icmp ule i64 {sum}, {max}"));
            let ok = k.block("str_ok");
            let falle = k.block("str_falle");
            k.zeile(&format!("br i1 {passt}, label %{ok}, label %{falle}"));
            k.beendet = true;
            let _ = writeln!(k.text, "{falle}:");
            k.beendet = false;
            k.zeile("unreachable");
            k.beendet = true;
            let _ = writeln!(k.text, "{ok}:");
            k.beendet = false;
            // Bytes kopieren (zweite Kopie schreibt hinter die erste).
            string_kopieren(k, &bytesa, &lena, &slot, &name, "0");
            string_kopieren(k, &bytesb, &lenb, &slot, &name, &lena64);
            // Länge setzen (zweite Kopie schreibt ab Versatz — Versatz merken).
            let lp = k.tmp();
            k.zeile(&format!("{lp} = getelementptr %{name}, ptr {slot}, i32 0, i32 0"));
            let sum32 = k.tmp();
            k.zeile(&format!("{sum32} = trunc i64 {sum} to i32"));
            k.zeile(&format!("store i32 {sum32}, ptr {lp}, align 4"));
            let t = k.tmp();
            k.zeile(&format!("{t} = load %{name}, ptr {slot}, align 8"));
            Some(Wert { typ: st, zeichen: Zeichen::Egal, text: t, form: None })
        }
        BinOp::Gleich | BinOp::Ungleich | BinOp::Kleiner | BinOp::KleinerGleich | BinOp::Groesser | BinOp::GroesserGleich => {
            // `string_vergleich` antwortet -1/0/1 (kleiner/gleich/größer).
            let r = string_vergleich(k, &lena, &bytesa, &lenb, &bytesb);
            let t = k.tmp();
            let mnemonic = match op {
                BinOp::Gleich => "eq",
                BinOp::Ungleich => "ne",
                BinOp::Kleiner => "slt",
                BinOp::KleinerGleich => "sle",
                BinOp::Groesser => "sgt",
                _ => "sge",
            };
            k.zeile(&format!("{t} = icmp {mnemonic} i32 {r}, 0"));
            Some(Wert::int(t, 1, Zeichen::Egal))
        }
        _ => {
            weigere(k.s, "Y104", span, "string operation".to_string());
            None
        }
    }
}

/// Bytefolge kopieren (Zählschleife bis `len`, ab `versatz` im Ziel).
fn string_kopieren(k: &mut Koerper, quelle: &str, len: &str, slot: &str, name: &str, versatz: &str) {
    let kopf = k.block("str_kopf");
    let rumpf = k.block("str_rumpf");
    let weiter = k.block("str_weiter");
    let danach = k.block("str_ende");
    let zaehler = k.alloca("i64");
    k.zeile(&format!("store i64 0, ptr {zaehler}, align 8"));
    // Versatz reist als i64 (der Aufrufer erweitert — `0` direkt).
    let off64 = versatz.to_string();
    k.zeile(&format!("br label %{kopf}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{kopf}:");
    k.beendet = false;
    let iv = k.tmp();
    k.zeile(&format!("{iv} = load i64, ptr {zaehler}, align 8"));
    let len64 = k.tmp();
    k.zeile(&format!("{len64} = zext i32 {len} to i64"));
    let cond = k.tmp();
    k.zeile(&format!("{cond} = icmp ult i64 {iv}, {len64}"));
    k.zeile(&format!("br i1 {cond}, label %{rumpf}, label %{danach}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{rumpf}:");
    k.beendet = false;
    let qp = k.tmp();
    k.zeile(&format!("{qp} = getelementptr i8, ptr {quelle}, i64 {iv}"));
    let qb = k.tmp();
    k.zeile(&format!("{qb} = load i8, ptr {qp}, align 1"));
    let ziel_idx = k.tmp();
    k.zeile(&format!("{ziel_idx} = add i64 {iv}, {off64}"));
    let zp = k.tmp();
    k.zeile(&format!("{zp} = getelementptr %{name}, ptr {slot}, i32 0, i32 1, i64 {ziel_idx}"));
    k.zeile(&format!("store i8 {qb}, ptr {zp}, align 1"));
    let nv = k.tmp();
    k.zeile(&format!("{nv} = add i64 {iv}, 1"));
    k.zeile(&format!("store i64 {nv}, ptr {zaehler}, align 8"));
    k.zeile(&format!("br label %{weiter}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{weiter}:");
    k.beendet = false;
    k.zeile(&format!("br label %{kopf}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{danach}:");
    k.beendet = false;
}

/// Lexikografischer Vergleich: -1/0/1 (kleiner/gleich/größer).
fn string_vergleich(k: &mut Koerper, lena: &str, bytesa: &str, lenb: &str, bytesb: &str) -> String {
    let ergebnis = k.alloca("i32");
    k.zeile(&format!("store i32 0, ptr {ergebnis}, align 4"));
    let zaehler = k.alloca("i64");
    k.zeile(&format!("store i64 0, ptr {zaehler}, align 8"));
    // Kürzere Länge als Schranke.
    let kleiner = k.tmp();
    k.zeile(&format!("{kleiner} = icmp ult i32 {lena}, {lenb}"));
    let min = k.tmp();
    k.zeile(&format!("{min} = select i1 {kleiner}, i32 {lena}, i32 {lenb}"));
    let min64 = k.tmp();
    k.zeile(&format!("{min64} = zext i32 {min} to i64"));
    let kopf = k.block("cmp_kopf");
    let rumpf = k.block("cmp_rumpf");
    let danach = k.block("cmp_ende");
    k.zeile(&format!("br label %{kopf}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{kopf}:");
    k.beendet = false;
    let iv = k.tmp();
    k.zeile(&format!("{iv} = load i64, ptr {zaehler}, align 8"));
    let cond = k.tmp();
    k.zeile(&format!("{cond} = icmp ult i64 {iv}, {min64}"));
    k.zeile(&format!("br i1 {cond}, label %{rumpf}, label %{danach}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{rumpf}:");
    k.beendet = false;
    let pa = k.tmp();
    k.zeile(&format!("{pa} = getelementptr i8, ptr {bytesa}, i64 {iv}"));
    let ba = k.tmp();
    k.zeile(&format!("{ba} = load i8, ptr {pa}, align 1"));
    let pb = k.tmp();
    k.zeile(&format!("{pb} = getelementptr i8, ptr {bytesb}, i64 {iv}"));
    let bb = k.tmp();
    k.zeile(&format!("{bb} = load i8, ptr {pb}, align 1"));
    let lt = k.tmp();
    k.zeile(&format!("{lt} = icmp ult i8 {ba}, {bb}"));
    let gt = k.tmp();
    k.zeile(&format!("{gt} = icmp ugt i8 {ba}, {bb}"));
    let schon = k.tmp();
    k.zeile(&format!("{schon} = load i32, ptr {ergebnis}, align 4"));
    let noch_null = k.tmp();
    k.zeile(&format!("{noch_null} = icmp eq i32 {schon}, 0"));
    // Erstes unterschiedliches Byte entscheidet (danach bleibt es stehen).
    let setze = k.block("cmp_setze");
    let weiter = k.block("cmp_weiter");
    let diff = k.tmp();
    k.zeile(&format!("{diff} = or i1 {lt}, {gt}"));
    let relevant = k.tmp();
    k.zeile(&format!("{relevant} = and i1 {diff}, {noch_null}"));
    k.zeile(&format!("br i1 {relevant}, label %{setze}, label %{weiter}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{setze}:");
    k.beendet = false;
    let neg = k.tmp();
    k.zeile(&format!("{neg} = select i1 {lt}, i32 -1, i32 1"));
    k.zeile(&format!("store i32 {neg}, ptr {ergebnis}, align 4"));
    k.zeile(&format!("br label %{weiter}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{weiter}:");
    k.beendet = false;
    let nv = k.tmp();
    k.zeile(&format!("{nv} = add i64 {iv}, 1"));
    k.zeile(&format!("store i64 {nv}, ptr {zaehler}, align 8"));
    k.zeile(&format!("br label %{kopf}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{danach}:");
    k.beendet = false;
    // Gleicher Präfix: die Länge entscheidet.
    let praefix = k.tmp();
    k.zeile(&format!("{praefix} = load i32, ptr {ergebnis}, align 4"));
    let praefix_null = k.tmp();
    k.zeile(&format!("{praefix_null} = icmp eq i32 {praefix}, 0"));
    let laenger = k.block("cmp_laenger");
    let fertig = k.block("cmp_fertig");
    k.zeile(&format!("br i1 {praefix_null}, label %{laenger}, label %{fertig}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{laenger}:");
    k.beendet = false;
    let ka = k.tmp();
    k.zeile(&format!("{ka} = icmp ult i32 {lena}, {lenb}"));
    let kb = k.tmp();
    k.zeile(&format!("{kb} = icmp ugt i32 {lena}, {lenb}"));
    let la = k.tmp();
    k.zeile(&format!("{la} = select i1 {ka}, i32 -1, i32 0"));
    let lb = k.tmp();
    k.zeile(&format!("{lb} = select i1 {kb}, i32 1, i32 {la}"));
    k.zeile(&format!("store i32 {lb}, ptr {ergebnis}, align 4"));
    k.zeile(&format!("br label %{fertig}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{fertig}:");
    k.beendet = false;
    let r = k.tmp();
    k.zeile(&format!("{r} = load i32, ptr {ergebnis}, align 4"));
    r
}

// ===================================================================================
// Atom-Paarung (Veröffentlichen, Warten, Tauschen — A10)
// ===================================================================================

/// Atom-Adresse hinter einem Ort (Basis oder Element eines Atom-Felds).
fn atom_adresse(k: &mut Koerper, ort: &Ort) -> Option<(String, LlTyp)> {
    let (ll, _) = k.s.atomare.get(&ort.basis.text).cloned()?;
    if ort.suffixe.is_empty() {
        if matches!(ll, LlTyp::Feld(_, _)) {
            return None;
        }
        return Some((format!("{}", gname(&ort.basis.text)), ll));
    }
    // Element eines Atom-Felds (`REGEL[r]` — ein Wort je Element).
    if let [OrtSuffix::Index(idx)] = ort.suffixe.as_slice() {
        if let LlTyp::Feld(e, _) = ll.clone() {
            let iv = senke_expr(k, idx)?;
            let ii = angleiche(k, iv, &LlTyp::Int(64), Zeichen::U)?;
            let t = k.tmp();
            k.zeile(&format!("{t} = getelementptr {}, ptr {}, i32 0, {} {}", ll.text(), gname(&ort.basis.text), ii.typ.text(), ii.text));
            return Some((t, (*e).clone()));
        }
    }
    None
}

/// `X = v publishes nothing;` — Freigabe-Speicher (der exportierte Fall).
/// Mit Nutzlast: Benennung (die Übergabe deckt der Zielsatz nicht — OFFEN O25).
fn senke_publish(k: &mut Koerper, p: &PublishStmt, span: Span) {
    // The payload is ordered by the release store below (see `publizieren.rs`).
    let (addr, ll) = match atom_adresse(k, &p.ziel) {
        Some(x) => x,
        None => {
            weigere(k.s, "Y103", span, "publish to non-atomic".to_string());
            return;
        }
    };
    let v = match senke_expr(k, &p.wert) {
        Some(v) => v,
        None => return,
    };
    let w = match angleiche_mit_weigere(k, v, &ll, span) {
        Some(w) => w,
        None => return,
    };
    // `bool`-Zelle als Byte an der Grenze.
    let (text, zugriff) = if ll == LlTyp::Int(8) && w.typ == LlTyp::Int(1) {
        let t = k.tmp();
        k.zeile(&format!("{t} = zext i1 {} to i8", w.text));
        (t, LlTyp::Int(8))
    } else {
        (w.text, ll.clone())
    };
    let ord = publizieren::schreib_ordnung(&publizieren::deklarierte_ordnung(k, &p.ziel));
    k.zeile(&format!(
        "store atomic {} {text}, ptr {addr} {ord}, align {}",
        zugriff.text(),
        nat_align(&ll)
    ));
}

/// `let x = A awaits { … };` — ONE acquire load (the C emitter writes one
/// `atomic_load_explicit` too). The payload places are not values to wait for: the branch
/// fact "this load confirms the flag" belongs to the checker (V009-V011), and what the
/// backend owes is the acquire order (`publizieren.rs`). An earlier spin loop compared the
/// loaded flag against the payload places -- a different program; removed.
fn senke_await(k: &mut Koerper, a: &AwaitLoad, span: Span) {
    let (addr, ll) = match atom_adresse(k, &a.quelle) {
        Some(x) => x,
        None => {
            weigere(k.s, "Y103", span, "await on non-atomic".to_string());
            return;
        }
    };
    let ord = publizieren::lese_ordnung(&publizieren::deklarierte_ordnung(k, &a.quelle));
    let t = k.tmp();
    k.zeile(&format!("{t} = load atomic {}, ptr {addr} {ord}, align {}", ll.text(), nat_align(&ll)));
    let v = atom_zu_bool(k, &ll, &t);
    let slot = k.alloca(&v.typ.text());
    k.zeile(&format!("store {} {}, ptr {slot}, align {}", v.typ.text(), v.text, nat_align(&v.typ)));
    k.lege_an(a.name.text.clone(), Bindung { ptr: slot, ll: v.typ.clone(), zeichen: Zeichen::Egal, form: None, fluechtig: false });
}

/// Atomwort weiterreichen (die Grenze zieht der Gebrauch am Bindungstyp).
fn atom_zu_bool(k: &mut Koerper, ll: &LlTyp, text: &str) -> Wert {
    let _ = k;
    Wert { typ: ll.clone(), zeichen: Zeichen::U, text: text.to_string(), form: None }
}

// ===================================================================================
// Tauschen (CAS-Schleife und Einzelvergleich — die Maschine ordnet, A10)
// ===================================================================================

/// `let x = A exchange …` — Ergebnis ist der ALTE Wert (Modell: `.cons alt`).
fn senke_exchange(k: &mut Koerper, e: &ExchangeStmt, span: Span) {
    let st = &*e;
    let (addr, ll) = match atom_adresse(k, &st.ort) {
        Some(x) => x,
        None => {
            weigere(k.s, "Y103", span, "exchange on non-atomic".to_string());
            return;
        }
    };
    let ord = k.s.atomare.get(&st.ort.basis.text).map(|(_, o)| o.clone()).unwrap_or_else(|| "seq_cst".to_string());
    match &st.form {
        XForm::Update { binder, schranke, bei_ueberschreitung, rumpf } => {
            let bound = match schranke {
                Some(b) => match konst_u64(k.s, b) {
                    Some(n) => n,
                    None => {
                        weigere(k.s, "Y103", span, "exchange with non-constant bound".to_string());
                        return;
                    }
                },
                None => {
                    weigere(k.s, "Y103", span, "unbounded exchange".to_string());
                    return;
                }
            };
            senke_exchange_schleife(k, &st.name, binder, &addr, &ll, &ord, bound, bei_ueberschreitung, rumpf, span);
        }
        XForm::Vergleich { wert, bedingung, ergebnis } => {
            senke_exchange_vergleich(k, &st.name, &addr, &ll, &ord, wert, bedingung, ergebnis, span);
        }
    }
    let _ = &st.nutzlast;
    let _ = &st.erwartet;
}

/// Beschränkte CAS-Schleife (Rumpf-`return` liefert neu — kein Funktionsausgang).
fn senke_exchange_schleife(
    k: &mut Koerper,
    name: &Ident,
    binder: &Ident,
    addr: &str,
    ll: &LlTyp,
    ord: &str,
    bound: u64,
    handler: &Option<Ident>,
    rumpf: &Block,
    span: Span,
) {
    let kopf = k.block("xchg_kopf");
    let versuch = k.block("xchg_versuch");
    let weiter = k.block("xchg_weiter");
    let danach = k.block("xchg_ende");
    let ueber = k.block("xchg_ueber");
    let zaehler = k.alloca("i64");
    k.zeile(&format!("store i64 0, ptr {zaehler}, align 8"));
    let neu_slot = k.alloca(&ll.text());
    k.zeile(&format!("br label %{kopf}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{kopf}:");
    k.beendet = false;
    // Schranke (der benannte Ausgang bei Überschreitung).
    let nv = k.tmp();
    k.zeile(&format!("{nv} = load i64, ptr {zaehler}, align 8"));
    let voll = k.tmp();
    k.zeile(&format!("{voll} = icmp uge i64 {nv}, {bound}"));
    k.zeile(&format!("br i1 {voll}, label %{ueber}, label %{versuch}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{ueber}:");
    k.beendet = false;
    match handler {
        Some(h) => {
            k.zeile(&format!("call void {}()", gname(&h.text)));
        }
        None => {
            weigere(k.s, "Y103", span, "exchange overflow without handler".to_string());
            return;
        }
    }
    k.zeile("unreachable");
    k.beendet = true;
    let _ = writeln!(k.text, "{versuch}:");
    k.beendet = false;
    // Alt laden, binden, neu rechnen (Rumpf-`return` → `neu_slot`).
    let alt = k.tmp();
    k.zeile(&format!("{alt} = load atomic {}, ptr {addr} acquire, align {}", ll.text(), nat_align(ll)));
    k.oeffne();
    let bslot = k.alloca(&ll.text());
    k.zeile(&format!("store {} {alt}, ptr {bslot}, align {}", ll.text(), nat_align(ll)));
    k.lege_an(binder.text.clone(), Bindung { ptr: bslot, ll: ll.clone(), zeichen: Zeichen::U, form: None, fluechtig: false });
    let alt_falle = std::mem::replace(&mut k.tausch_rueck, Some((neu_slot.clone(), ll.clone(), weiter.clone())));
    for st in &rumpf.anweisungen {
        if k.beendet {
            break;
        }
        senke_stmt(k, st);
    }
    k.tausch_rueck = alt_falle;
    k.schliesse();
    if !k.beendet {
        // Rumpf ohne `return`: neu = alt (reiner Leseversuch).
        k.zeile(&format!("store {} {alt}, ptr {neu_slot}, align {}", ll.text(), nat_align(ll)));
        k.zeile(&format!("br label %{weiter}"));
    }
    k.beendet = true;
    let _ = writeln!(k.text, "{weiter}:");
    k.beendet = false;
    let neu = k.tmp();
    k.zeile(&format!("{neu} = load {}, ptr {neu_slot}, align {}", ll.text(), nat_align(ll)));
    // Tauschen (stark, mit Ordnungen der Deklaration).
    let paar = k.tmp();
    k.zeile(&format!("{paar} = cmpxchg ptr {addr}, {} {alt}, {} {neu} {ord} {ord}, align {}", ll.text(), ll.text(), nat_align(ll)));
    let gelungen = k.tmp();
    k.zeile(&format!("{gelungen} = extractvalue {{ {}, i1 }} {paar}, 1", ll.text()));
    // Zähler hoch, weiter oder fertig.
    let nv2 = k.tmp();
    k.zeile(&format!("{nv2} = add i64 {nv}, 1"));
    k.zeile(&format!("store i64 {nv2}, ptr {zaehler}, align 8"));
    k.zeile(&format!("br i1 {gelungen}, label %{danach}, label %{kopf}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{danach}:");
    k.beendet = false;
    // Ergebnis: der ALTE Wert (Modell `.cons alt`).
    let rslot = k.alloca(&ll.text());
    k.zeile(&format!("store {} {alt}, ptr {rslot}, align {}", ll.text(), nat_align(ll)));
    k.lege_an(name.text.clone(), Bindung { ptr: rslot, ll: ll.clone(), zeichen: Zeichen::U, form: None, fluechtig: false });
}

/// Einzelvergleich: laden, prüfen (`old` gebunden), bedingt speichern.
fn senke_exchange_vergleich(
    k: &mut Koerper,
    name: &Ident,
    addr: &str,
    ll: &LlTyp,
    ord: &str,
    wert: &Expr,
    bedingung: &Pred,
    ergebnis: &Ident,
    span: Span,
) {
    let alt = k.tmp();
    let lese_ord = if ord == "release" { "acquire" } else { ord };
    k.zeile(&format!("{alt} = load atomic {}, ptr {addr} {lese_ord}, align {}", ll.text(), nat_align(ll)));
    // `old(X)` im Vergleich ist die eben geladene Antwort.
    let alt_falle = std::mem::replace(
        &mut k.alt_wert,
        Some(Wert { typ: ll.clone(), zeichen: Zeichen::U, text: alt.clone(), form: None }),
    );
    let cond = senke_predikat(k, bedingung);
    k.alt_wert = alt_falle;
    let cond = match cond {
        Some(c) => c,
        None => {
            weigere(k.s, "Y103", span, "exchange with unlowerable condition".to_string());
            return;
        }
    };
    let dann = k.block("xchgv_dann");
    let danach = k.block("xchgv_ende");
    k.zeile(&format!("br i1 {cond}, label %{dann}, label %{danach}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{dann}:");
    k.beendet = false;
    let v = match senke_expr(k, wert) {
        Some(v) => v,
        None => return,
    };
    let w = match angleiche_mit_weigere(k, v, ll, span) {
        Some(w) => w,
        None => return,
    };
    // Bedingter Speicher mit Freigabe-Ordnung der Deklaration.
    let schreib_ord = if ord == "acquire" { "release" } else { ord };
    k.zeile(&format!("store atomic {} {}, ptr {addr} {schreib_ord}, align {}", ll.text(), w.text, nat_align(ll)));
    k.zeile(&format!("br label %{danach}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{danach}:");
    k.beendet = false;
    // Ergebnis-Flagge (`returns erfolg`) plus alter Wert.
    let eslot = k.alloca("i1");
    k.zeile(&format!("store i1 {cond}, ptr {eslot}, align 1"));
    k.lege_an(ergebnis.text.clone(), Bindung { ptr: eslot, ll: LlTyp::Int(1), zeichen: Zeichen::Egal, form: None, fluechtig: false });
    let rslot = k.alloca(&ll.text());
    k.zeile(&format!("store {} {alt}, ptr {rslot}, align {}", ll.text(), nat_align(ll)));
    k.lege_an(name.text.clone(), Bindung { ptr: rslot, ll: ll.clone(), zeichen: Zeichen::U, form: None, fluechtig: false });
}

// ===================================================================================
// Options-Versand (`Some`/`None` — Modell `onOption`)
// ===================================================================================

/// `match o { Some(x) => …, None => … }` — Tag halten, Nutzlast binden.
fn senke_match_option(k: &mut Koerper, m: &MatchStmt, v: &Wert, span: Span) {
    if m.zweige.len() != 2 {
        weigere(k.s, "Y106", span, "option match without two arms".to_string());
        return;
    }
    let tag = k.tmp();
    let slot = k.alloca("%gabopt");
    k.zeile(&format!("store %gabopt {}, ptr {slot}, align 8", v.text));
    let tp = k.tmp();
    k.zeile(&format!("{tp} = getelementptr %gabopt, ptr {slot}, i32 0, i32 0"));
    k.zeile(&format!("{tag} = load i32, ptr {tp}, align 4"));
    let ist_some = k.tmp();
    k.zeile(&format!("{ist_some} = icmp ne i32 {tag}, 0"));
    let ende = k.block("opt_ende");
    for zweig in &m.zweige {
        let arm = k.block("opt_arm");
        let weiter = k.block("opt_weiter");
        let cond = if zweig.variante.text == "Some" {
            ist_some.clone()
        } else if zweig.variante.text == "None" {
            let n = k.tmp();
            k.zeile(&format!("{n} = xor i1 {ist_some}, true"));
            n
        } else {
            weigere(k.s, "Y106", zweig.span, format!("unknown option case {}", zweig.variante.text));
            return;
        };
        k.zeile(&format!("br i1 {cond}, label %{arm}, label %{weiter}"));
        k.beendet = true;
        let _ = writeln!(k.text, "{arm}:");
        k.beendet = false;
        k.oeffne();
        if let Some(binder) = &zweig.binder {
            // Nutzlast: Index aus den Bytes (i32).
            let pp = k.tmp();
            k.zeile(&format!("{pp} = getelementptr %gabopt, ptr {slot}, i32 0, i32 1"));
            let pc = k.tmp();
            k.zeile(&format!("{pc} = getelementptr i8, ptr {pp}, i64 0"));
            let lv = k.tmp();
            k.zeile(&format!("{lv} = load i32, ptr {pc}, align 1"));
            let bslot = k.alloca("i32");
            k.zeile(&format!("store i32 {lv}, ptr {bslot}, align 4"));
            k.lege_an(binder.text.clone(), Bindung { ptr: bslot, ll: LlTyp::Int(32), zeichen: Zeichen::U, form: None, fluechtig: false });
        }
        for st in &zweig.rumpf.anweisungen {
            if k.beendet {
                break;
            }
            senke_stmt(k, st);
        }
        k.schliesse();
        if !k.beendet {
            k.zeile(&format!("br label %{ende}"));
        }
        k.beendet = true;
        let _ = writeln!(k.text, "{weiter}:");
        k.beendet = false;
    }
    // Beide Arme geprüft, keiner traf — Abdeckung hält der Prüfer.
    k.zeile("unreachable");
    k.beendet = true;
    let _ = writeln!(k.text, "{ende}:");
    k.beendet = false;
    // HINWEIS: Zwei Arme mit je eigenem Test tragen beide weiter — fällt der erste,
    // läuft der zweite (kein `else`-Fall nötig, aber beide Zweige gelesen).
}

// ===================================================================================
// Indirekte Rufe (Vertrag am Zeigertyp — Modell `callInd`)
// ===================================================================================

/// `p(a, b)` durch einen Funktionszeiger: Signatur aus der deklarierten Form.
fn senke_ruf_indirekt(k: &mut Koerper, r: &Ruf, span: Span) -> Option<Wert> {
    let ort = match r.ziel {
        CallTarget::Place(ref o) => o.clone(),
        _ => {
            weigere(k.s, "Y104", span, "indirect call without place".to_string());
            return None;
        }
    };
    let p = adresse_von_ort(k, &ort)?;
    let fz = match p.form.clone().map(|f| grundform(k.s, &f)) {
        Some(TypExpr::FnZeiger(f)) => f,
        _ => {
            weigere(k.s, "Y104", span, "indirect call without function-pointer form".to_string());
            return None;
        }
    };
    let fp = k.tmp();
    k.zeile(&format!("{fp} = load ptr, ptr {}, align 8", p.addr));
    // Signatur aus der Form (breit — ABI-Grenze).
    let alt = k.s.eng_modus;
    k.s.eng_modus = false;
    let mut pts = Vec::new();
    let mut ok = true;
    for prm in &fz.parameter {
        match senke_typ(k.s, &prm.typ) {
            Some((ll, _)) => pts.push(ll),
            None => {
                ok = false;
                break;
            }
        }
    }
    let ret = match &fz.ergebnis {
        Some(t) => match senke_typ(k.s, t) {
            Some((ll, _)) => Some(ll),
            None => {
                ok = false;
                None
            }
        },
        None => Some(LlTyp::Void),
    };
    k.s.eng_modus = alt;
    if !ok {
        return None;
    }
    if r.argumente.len() != pts.len() {
        weigere(k.s, "Y104", span, "indirect call with wrong argument count".to_string());
        return None;
    }
    let mut args = Vec::new();
    for (ae, pt) in r.argumente.iter().zip(pts.iter()) {
        let w = verfall_arg(k, ae, pt, span)?;
        args.push(format!("{} {}", pt.text(), w.text));
    }
    let ret = ret.expect("ok geprüft");
    if ret == LlTyp::Void {
        k.zeile(&format!("call void {fp}({})", args.join(", ")));
        None
    } else {
        let t = k.tmp();
        k.zeile(&format!("{t} = call {} {fp}({})", ret.text(), args.join(", ")));
        Some(Wert { typ: ret, zeichen: Zeichen::Egal, text: t, form: fz.ergebnis.clone() })
    }
}

// ===================================================================================
// Gleitkomma-Verengung (Bereich und Endlichkeit — Modell `gleitNarrow`)
// ===================================================================================

/// `narrow x to lo .. hi` über Gleitkomma (`fcmp`, kein NaN-Empfang).
fn senke_narrow_gleit(k: &mut Koerper, n: &NarrowStmt, p: &Adresse, b: &Bereich, span: Span) {
    let t = k.tmp();
    let al = nat_align(&p.ll);
    k.zeile(&format!("{t} = load {}, ptr {}, align {al}", p.ll.text(), p.addr));
    // Schranken als Gleitkomma (Literale und benannte Konstanten).
    let (lo, hi, _) = match gleit_grenzen(k.s, b) {
        Some(x) => x,
        None => {
            weigere(k.s, "Y104", b.span, "non-constant float bound".to_string());
            return;
        }
    };
    let ok1 = k.tmp();
    k.zeile(&format!("{ok1} = fcmp oge {} {t}, {}", p.ll.text(), hexfloat(lo.to_bits(), p.ll == LlTyp::F32)));
    let ok2 = k.tmp();
    k.zeile(&format!("{ok2} = fcmp ole {} {t}, {}", p.ll.text(), hexfloat(hi.to_bits(), p.ll == LlTyp::F32)));
    let ok = k.tmp();
    k.zeile(&format!("{ok} = and i1 {ok1}, {ok2}"));
    let weiter = k.block("fnarrow_weiter");
    let sonst = k.block("fnarrow_sonst");
    k.zeile(&format!("br i1 {ok}, label %{weiter}, label %{sonst}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{sonst}:");
    k.beendet = false;
    senke_block(k, &n.sonst);
    if !k.beendet {
        k.zeile(&format!("br label %{weiter}"));
    }
    k.beendet = true;
    let _ = writeln!(k.text, "{weiter}:");
    k.beendet = false;
    k.s.braucht_assume = true;
    k.zeile(&format!("call void @llvm.assume(i1 {ok})"));
    k.s.beleg_annahmen.push(format!("narrow: {} finite in range holding at {:?}", n.ort.text(), span));
}

/// `narrow x to finite` — weder NaN noch unendlich.
fn senke_narrow_endlich(k: &mut Koerper, n: &NarrowStmt, span: Span) {
    let p = match adresse_von_ort(k, &n.ort) {
        Some(p) => p,
        None => return,
    };
    if !matches!(p.ll, LlTyp::F32 | LlTyp::F64) {
        weigere(k.s, "Y104", span, "finiteness of non-float".to_string());
        return;
    }
    let t = k.tmp();
    let al = nat_align(&p.ll);
    k.zeile(&format!("{t} = load {}, ptr {}, align {al}", p.ll.text(), p.addr));
    // Endlich = geordnet gegen sich selbst UND Betrag unter Unendlich.
    let geordnet = k.tmp();
    k.zeile(&format!("{geordnet} = fcmp ord {} {t}, {t}", p.ll.text()));
    let betrag = k.tmp();
    let inf = if p.ll == LlTyp::F32 { "0x7F800000" } else { "0x7FF0000000000000" };
    k.s.braucht_fabs = true;
    let fabs_name = if p.ll == LlTyp::F32 { "llvm.fabs.f32" } else { "llvm.fabs.f64" };
    k.zeile(&format!("{betrag} = call {} @{fabs_name}({} {t})", p.ll.text(), p.ll.text()));
    let endlich_wert = k.tmp();
    k.zeile(&format!("{endlich_wert} = fcmp olt {} {betrag}, {inf}", p.ll.text()));
    let geordnet = {
        let beide = k.tmp();
        k.zeile(&format!("{beide} = and i1 {geordnet}, {endlich_wert}"));
        beide
    };
    let weiter = k.block("endlich_weiter");
    let sonst = k.block("endlich_sonst");
    k.zeile(&format!("br i1 {geordnet}, label %{weiter}, label %{sonst}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{sonst}:");
    k.beendet = false;
    senke_block(k, &n.sonst);
    if !k.beendet {
        k.zeile(&format!("br label %{weiter}"));
    }
    k.beendet = true;
    let _ = writeln!(k.text, "{weiter}:");
    k.beendet = false;
    k.s.braucht_assume = true;
    k.zeile(&format!("call void @llvm.assume(i1 {geordnet})"));
    k.s.beleg_annahmen.push(format!("narrow: {} finite holding at {:?}", n.ort.text(), span));
}

// ===================================================================================
// Gerätemodell (Register am Versatz, Bitfelder, Transitionen)
// ===================================================================================

/// Ein Geräteregister: Name, Byteversatz, Typ, Bitfelder (Name, Tiefstbit, Breite).
#[derive(Clone)]
struct DevReg {
    name: String,
    versatz: u64,
    ll: LlTyp,
    zeichen: Zeichen,
    felder: Vec<(String, u32, u32)>,
    /// `device … at port`: das Register liegt im Portraum (`in`/`out`), nicht im Speicher.
    port: bool,
}

fn sammle_device(s: &mut Senke, d: &Device, span: Span) {
    // **A `device ... at port` is NOT memory (Y102, the item class).** Its register offsets are port
    // numbers reached by `in`/`out`; lowering them as `load volatile` at base+offset
    // would read RAM at the port number -- the old C-emitter defect (`gift/416`).
    // This backend has no `in`/`out` lowering (and aarch64 has no port space at all),
    // so the device is refused by name instead of lowered to a plausible wrong access.
    let port = matches!(d.raum, Raum::Port);
    if port && (!d.baenke.is_empty() || d.mirrors.is_some()) {
        weigere(s, "Y102", span, format!("device {} at port with banks or mirrors: no port-space lowering", d.name.text));
        return;
    }
    if port && s.ziel.name != "x86_64" {
        weigere(
            s,
            "Y102",
            span,
            format!(
                "device {} at port: the {} target has no port space (`in`/`out` are x86 instructions); \
                 a port device is declarable under `arch x86_64` only",
                d.name.text, s.ziel.name
            ),
        );
        return;
    }
    let mut regs = Vec::new();
    for r in &d.register {
        let versatz = match konst_u64(s, &r.versatz) {
            Some(v) => v,
            None => {
                weigere(s, "Y101", span, format!("device {} with non-constant offset", d.name.text));
                return;
            }
        };
        let (w, z) = match int_wort(r.typ.wort) {
            Some(x) => x,
            None => {
                weigere(s, "Y101", span, format!("device register {} of odd width", r.name.text));
                return;
            }
        };
        if port && w > 32 {
            weigere(
                s,
                "Y102",
                span,
                format!("port register {} of {w} bits: `in`/`out` stop at 32 bits", r.name.text),
            );
            return;
        }
        let mut felder = Vec::new();
        for (fname, pos, _) in &r.felder {
            match pos {
                BitPos::Bit(b) => match u32::try_from(*b) {
                    Ok(v) if v < w => felder.push((fname.text.clone(), v, 1)),
                    _ => {
                        weigere(s, "Y101", span, format!("bit {} outside {}", fname.text, r.name.text));
                        return;
                    }
                },
                BitPos::Bereich(hoch, tief) => match (u32::try_from(*hoch), u32::try_from(*tief)) {
                    (Ok(h), Ok(t)) if t <= h && h < w => felder.push((fname.text.clone(), t, h - t + 1)),
                    _ => {
                        weigere(s, "Y101", span, format!("bits outside {}", r.name.text));
                        return;
                    }
                },
            }
        }
        regs.push(DevReg { name: r.name.text.clone(), versatz, ll: LlTyp::Int(w), zeichen: z, felder, port });
        let _ = &r.umlaufend;
        let _ = &r.phasen;
        let _ = &r.requires;
        let _ = &r.requires_grund;
        let _ = &r.depends;
    }
    // Transitionen: Name → Schritte (Register, Feld oder "", von, nach).
    for u in &d.uebergaenge {
        let mut schritte = Vec::new();
        let mut ok = true;
        for schritt in &u.schritte {
            let (reg, feld) = match schritt.ort.suffixe.as_slice() {
                [OrtSuffix::Feld(f)] => (schritt.ort.basis.text.clone(), f.text.clone()),
                [] => (schritt.ort.basis.text.clone(), String::new()),
                _ => {
                    weigere(s, "Y102", schritt.span, "transition step of odd shape".to_string());
                    ok = false;
                    break;
                }
            };
            let von = match s.umg.konst_wert(&s.modul, &schritt.von) {
                Some(v) => v,
                None => {
                    weigere(s, "Y102", schritt.span, "transition with non-constant source".to_string());
                    ok = false;
                    break;
                }
            };
            let nach = match s.umg.konst_wert(&s.modul, &schritt.nach) {
                Some(v) => v,
                None => {
                    weigere(s, "Y102", schritt.span, "transition with non-constant target".to_string());
                    ok = false;
                    break;
                }
            };
            schritte.push((reg, feld, von, nach));
        }
        if !ok {
            return;
        }
        s.transitionen.insert(u.name.text.clone(), (d.name.text.clone(), schritte));
    }
    s.geraete.insert(d.name.text.clone(), regs);
    let _ = &d.parameter;
    let _ = &d.raum;
    let _ = &d.mirrors;
    let _ = &d.baenke;
}

// ===================================================================================
// Gerätezugriffe (Register, Bitfelder — flüchtig, am Versatz)
// ===================================================================================

/// Gerätename hinter einer Form (Zeiger aufs Gerät oder Gerätewert).
fn geraet_hinter(s: &Senke, form: &Option<TypExpr>) -> Option<String> {
    match form.clone().map(|f| grundform(s, &f)) {
        Some(TypExpr::Pfad(p)) => p.einfach().filter(|e| s.geraete.contains_key(&e.text)).map(|e| e.text.clone()),
        Some(TypExpr::Zeiger(zz)) => match grundform(s, &zz.ziel) {
            TypExpr::Pfad(p) => p.einfach().filter(|e| s.geraete.contains_key(&e.text)).map(|e| e.text.clone()),
            _ => None,
        },
        _ => None,
    }
}

/// Bitfeld (Name, Tiefstbit, Breite) hinter Gerät plus Register.
fn bitfeld(s: &Senke, dev: &str, reg: &str, feld: &str) -> Option<(String, u32, u32)> {
    s.geraete.get(dev)?.iter().find(|r| r.name == reg)?.felder.iter().find(|(n, _, _)| n == feld).cloned()
}

// ===================================================================================
// Transitionen (Bit-Schritte am Gerät — lesen-modifizieren-schreiben)
// ===================================================================================

/// `name(handle)` — jeder Schritt ein RMW am Register (flüchtig beidseitig).
fn senke_transition(
    k: &mut Koerper,
    dev: &str,
    schritte: &[(String, String, i128, i128)],
    r: &Ruf,
    span: Span,
) -> Option<Wert> {
    if r.argumente.len() != 1 {
        weigere(k.s, "Y104", span, "transition takes the device handle".to_string());
        return None;
    }
    let h = senke_expr(k, &r.argumente[0])?;
    // Griff: Zeiger oder Basisadresse als Zahl.
    let regs = match k.s.geraete.get(dev).cloned() {
        Some(x) => x,
        None => {
            weigere(k.s, "Y104", span, format!("unknown device {dev}"));
            return None;
        }
    };
    let ist_port = regs.iter().any(|x| x.port);
    let roh = match &h.typ {
        LlTyp::Ptr if ist_port => {
            let t = k.tmp();
            k.zeile(&format!("{t} = ptrtoint ptr {} to i64", h.text));
            t
        }
        LlTyp::Ptr => h.text.clone(),
        LlTyp::Int(_) => {
            let w = angleiche(k, h, &LlTyp::Int(64), Zeichen::U)?;
            if ist_port {
                w.text
            } else {
                let t = k.tmp();
                k.zeile(&format!("{t} = inttoptr i64 {} to ptr", w.text));
                t
            }
        }
        _ => {
            weigere(k.s, "Y104", span, "transition on odd handle".to_string());
            return None;
        }
    };
    for (reg, feld, _von, nach) in schritte {
        let dr = match regs.iter().find(|x| &x.name == reg) {
            Some(x) => x.clone(),
            None => {
                weigere(k.s, "Y104", span, format!("unknown register {reg}"));
                return None;
            }
        };
        let breite = dr.ll.breite().unwrap_or(32);
        // Die Adresse des Schritts: Speicher (`ptr`) oder Portnummer (`i16`).
        let bc = if dr.port {
            portraum::nummer_aus_zahl(k, &roh, dr.versatz)
        } else {
            let off = k.tmp();
            k.zeile(&format!("{off} = getelementptr i8, ptr {roh}, i64 {}", dr.versatz));
            let bc = k.tmp();
            k.zeile(&format!("{bc} = getelementptr i8, ptr {off}, i64 0"));
            bc
        };
        if feld.is_empty() {
            // Ganzes Register schreiben (flüchtig).
            let n = falte_int(*nach, breite);
            if dr.port {
                portraum::schreiben(k, &bc, &dr.ll, &n);
            } else {
                k.zeile(&format!("store volatile i{breite} {n}, ptr {bc}, align {}", nat_align(&dr.ll)));
            }
            continue;
        }
        // Bitfeld: lesen, Feld ersetzen, schreiben (`von` hält der Prüfer).
        let (lo, br) = match dr.felder.iter().find(|(n, _, _)| n == feld) {
            Some((_, lo, br)) => (*lo, *br),
            None => {
                weigere(k.s, "Y104", span, format!("unknown bit field {feld}"));
                return None;
            }
        };
        let al = nat_align(&dr.ll);
        let w = if dr.port {
            portraum::lesen(k, &bc, &dr.ll)
        } else {
            let w = k.tmp();
            k.zeile(&format!("{w} = load volatile i{breite}, ptr {bc}, align {al}"));
            w
        };
        let maske: u128 = if br >= 128 { u128::MAX } else { (1u128 << br) - 1 };
        let geloeschte: u128 = !(maske << lo) & ((1u128 << breite) - 1);
        let behalten = k.tmp();
        k.zeile(&format!("{behalten} = and i{breite} {w}, {geloeschte}"));
        let gesetzt = k.tmp();
        let n = falte_int((*nach & (maske as i128)) << lo, breite);
        k.zeile(&format!("{gesetzt} = or i{breite} {behalten}, {n}"));
        if dr.port {
            portraum::schreiben(k, &bc, &dr.ll, &gesetzt);
        } else {
            k.zeile(&format!("store volatile i{breite} {gesetzt}, ptr {bc}, align {al}"));
        }
    }
    None
}

// ===================================================================================
// Baumläufe (Ahnenkette, stapelloser Abstieg — drei Kanten, kein Stapel)
// ===================================================================================

/// Slot-Typedef (`%T$slot`) sicherstellen — überall gleich, einmalig.
fn sorge_slot(s: &mut Senke, tab: &str) -> Option<String> {
    let (_, slot) = s.tabellen.get(tab).cloned()?;
    if s.typedefs.contains(&slot) {
        return Some(slot);
    }
    let felder = s.tab_slots.get(tab).cloned()?;
    let alt = s.eng_modus;
    s.eng_modus = false;
    let mut teile = Vec::new();
    let mut ok = true;
    for (_, ft) in &felder {
        match senke_typ(s, ft) {
            Some((ll, _)) => teile.push(ll.text()),
            None => {
                ok = false;
                break;
            }
        }
    }
    s.eng_modus = alt;
    if !ok {
        return None;
    }
    s.typedefs.insert(slot.clone());
    let layout = format!("{{ {} }}", teile.join(", "));
    let _ = writeln!(s.kopf, "%{slot} = type {layout}");
    s.beleg_typen.push((slot.clone(), layout));
    Some(slot)
}

/// Slot-Feld-Adresse: (Adresse, Typ, Zeichen) für Tabelle, Feldträger, Index, Feld.
fn slot_feld(k: &mut Koerper, tab: &str, traeger: &str, idx: &str, feld: &str, span: Span) -> Option<(String, LlTyp, Zeichen)> {
    let (len, _) = k.s.tabellen.get(tab).cloned()?;
    let slot = sorge_slot(k.s, tab)?;
    let felder = k.s.tab_slots.get(tab).cloned()?;
    let (nr, ftyp) = felder.iter().position(|(n, _)| n == feld).map(|i| (i, felder[i].1.clone()))?;
    let (fll, fz) = senke_typ(k.s, &ftyp)?;
    let t = k.tmp();
    k.zeile(&format!("{t} = getelementptr [{len} x %{slot}], ptr {traeger}, i32 0, i32 {idx}, i32 {nr}"));
    let _ = span;
    Some((t, fll, fz))
}

/// Options-Index lesen: (ist-belegt, Nutzlast) aus `%gabopt`-Adresse.
fn opt_lesen(k: &mut Koerper, addr: &str) -> (String, String) {
    let tp = k.tmp();
    k.zeile(&format!("{tp} = getelementptr %gabopt, ptr {addr}, i32 0, i32 0"));
    let tag = k.tmp();
    k.zeile(&format!("{tag} = load i32, ptr {tp}, align 4"));
    let ist = k.tmp();
    k.zeile(&format!("{ist} = icmp ne i32 {tag}, 0"));
    let pp = k.tmp();
    k.zeile(&format!("{pp} = getelementptr %gabopt, ptr {addr}, i32 0, i32 1"));
    let pc = k.tmp();
    k.zeile(&format!("{pc} = getelementptr i8, ptr {pp}, i64 0"));
    let last = k.tmp();
    k.zeile(&format!("{last} = load i32, ptr {pc}, align 1"));
    (ist, last)
}

/// Baumsicht: (Tabelle, Feldträger-Adresse, Wurzel als i32) hinter dem Domänenort.
fn baum_sicht(k: &mut Koerper, o: &Ort, span: Span) -> Option<(String, String, String)> {
    // `X.slots[i]` — Tabelle hinter dem Zeiger oder dem Namen.
    if let [OrtSuffix::Feld(f), OrtSuffix::Index(idx)] = o.suffixe.as_slice() {
        if f.text != "slots" {
            weigere(k.s, "Y103", span, "tree walk outside slots".to_string());
            return None;
        }
        let mut tab = o.basis.text.clone();
        if !k.s.tabellen.contains_key(&tab) {
            // Zeigerform auflösen (`w : ptr<…> Werte`).
            let nb = k.suche(&tab).and_then(|b| b.form.clone()).map(|ff| grundform(k.s, &ff));
            match nb {
                Some(TypExpr::Zeiger(zz)) => match grundform(k.s, &zz.ziel) {
                    TypExpr::Pfad(p) => match p.einfach() {
                        Some(e) => tab = e.text.clone(),
                        None => {
                            weigere(k.s, "Y103", span, "tree walk over unnamed table".to_string());
                            return None;
                        }
                    },
                    _ => {
                        weigere(k.s, "Y103", span, "tree walk over non-table".to_string());
                        return None;
                    }
                },
                _ => {
                    weigere(k.s, "Y103", span, "tree walk over unknown table".to_string());
                    return None;
                }
            }
        }
        if !k.s.tabellen.contains_key(&tab) {
            weigere(k.s, "Y103", span, "tree walk over unknown table".to_string());
            return None;
        }
        // Feldträger: Adresse von `X.slots` (Feld ohne Index).
        let o2 = Ort { basis: o.basis.clone(), suffixe: vec![OrtSuffix::Feld(f.clone())], span: o.span };
        let p = adresse_von_ort(k, &o2)?;
        let iv = senke_expr(k, idx)?;
        let ii = angleiche(k, iv, &LlTyp::Int(32), Zeichen::U)?;
        return Some((tab, p.addr, ii.text));
    }
    // Blosser Indexname mit `index into T`-Form (`ancestors of g`).
    if o.suffixe.is_empty() {
        let form = k.suche(&o.basis.text).and_then(|b| b.form.clone()).map(|f| grundform(k.s, &f));
        if let Some(TypExpr::Index { tabelle, .. }) = form {
            let tab = tabelle.text.clone();
            if !k.s.tabellen.contains_key(&tab) {
                weigere(k.s, "Y103", span, "tree walk over unknown table".to_string());
                return None;
            }
            // Feldträger: Tabellen-Global, Feld 0.
            let (len, _) = k.s.tabellen.get(&tab).cloned()?;
            let g = gname(&tab);
            let arr = k.tmp();
            k.zeile(&format!("{arr} = getelementptr %{tab}, ptr {g}, i32 0, i32 0"));
            let v = senke_expr(k, &Expr { art: ExprArt::Ort(o.clone()), span: o.span })?;
            let ii = angleiche(k, v, &LlTyp::Int(32), Zeichen::U)?;
            let _ = len;
            return Some((tab, arr, ii.text));
        }
    }
    weigere(k.s, "Y103", span, "tree walk over this shape".to_string());
    None
}

// ===================================================================================
// Ahnen und Nachfahren (Modell `reaches` — strikt, ohne Stapel)
// ===================================================================================

/// `traverse v over ancestors of …` — bei der VATERSCHAFT beginnen (strikt),
/// bis zum Zählerstand (`count` als Wächter). `by consuming` lehnt der
/// C-Erzeuger ab — hier auch (andere Richtung, anderes Programm).
fn senke_traverse_ahnen(k: &mut Koerper, t: &Traverse, o: &Ort, span: Span) {
    if matches!(t.abstieg, Abstieg::Verbrauchend) {
        weigere(k.s, "Y103", span, "ancestors by consuming".to_string());
        return;
    }
    let (tab, traeger, wurzel) = match baum_sicht(k, o, span) {
        Some(x) => x,
        None => return,
    };
    let (elter, _, _) = match k.s.tab_baeume.get(&tab).cloned() {
        Some((Some(e), kind, geschw)) => (e, kind, geschw),
        _ => {
            weigere(k.s, "Y103", span, "ancestors without parent edge".to_string());
            return;
        }
    };
    let (len, _) = match k.s.tabellen.get(&tab).cloned() {
        Some(x) => x,
        None => return,
    };
    let kopf = k.block("ahn_kopf");
    let rumpf = k.block("ahn_rumpf");
    let danach = k.block("ahn_ende");
    sorge_gabopt(k.s);
    let vslot = k.alloca("i32");
    k.zeile(&format!("store i32 {wurzel}, ptr {vslot}, align 4"));
    k.zeile(&format!("br label %{kopf}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{kopf}:");
    k.beendet = false;
    let vc = k.tmp();
    k.zeile(&format!("{vc} = load i32, ptr {vslot}, align 4"));
    // Vater laden (Options-Index — fehlt er, ist die Kette zu Ende).
    let (faddr, _, _) = match slot_feld(k, &tab, &traeger, &vc, &elter, span) {
        Some(x) => x,
        None => return,
    };
    let (ist, last) = opt_lesen(k, &faddr);
    k.zeile(&format!("br i1 {ist}, label %{rumpf}, label %{danach}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{rumpf}:");
    k.beendet = false;
    k.zeile(&format!("store i32 {last}, ptr {vslot}, align 4"));
    if let Some(inv) = &t.invariante {
        nehme_an(k, inv, "invariant");
    }
    k.oeffne();
    k.lege_an(t.variable.text.clone(), Bindung { ptr: vslot.clone(), ll: LlTyp::Int(32), zeichen: Zeichen::U, form: None, fluechtig: false });
    k.schleifen.push(SchleifenKontext { weiter: kopf.clone(), danach: danach.clone(), marke: Some(t.variable.text.clone()), sperr_tiefe: k.sperren.len() });
    for st in &t.rumpf.anweisungen {
        if k.beendet {
            break;
        }
        senke_stmt(k, st);
    }
    k.schleifen.pop();
    k.schliesse();
    if !k.beendet {
        k.zeile(&format!("br label %{kopf}"));
    }
    k.beendet = true;
    let _ = writeln!(k.text, "{danach}:");
    k.beendet = false;
    let _ = len;
}

/// `traverse v over descendants of …` — Nachordnung, stapellos (drei Kanten).
/// Die Wurzel wird DURCHlaufen, nie besucht. `decreases` lehnt der C-Erzeuger
/// ab (welche Ordnung es bindet, steht nirgends) — hier auch.
fn senke_traverse_nachfahren(k: &mut Koerper, t: &Traverse, o: &Ort, span: Span) {
    if t.mass.is_some() {
        weigere(k.s, "Y103", span, "descendants with decreases".to_string());
        return;
    }
    let (tab, traeger, wurzel) = match baum_sicht(k, o, span) {
        Some(x) => x,
        None => return,
    };
    let (elter, kind, geschwister) = match k.s.tab_baeume.get(&tab).cloned() {
        Some((Some(e), Some(c), Some(sib))) => (e, c, sib),
        _ => {
            weigere(k.s, "Y103", span, "descendants without all three edges".to_string());
            return;
        }
    };
    if k.s.tabellen.get(&tab).is_none() {
        return;
    }
    sorge_gabopt(k.s);
    // `k` (aktuell), `h` (von unten gekommen) — beide veränderlich.
    let kslot = k.alloca("i32");
    let hslot = k.alloca("i1");
    // Wurzel als i64 falten (Index passt immer).
    let w64 = k.tmp();
    k.zeile(&format!("{w64} = sext i32 {wurzel} to i64"));
    let w = k.tmp();
    k.zeile(&format!("{w} = trunc i64 {w64} to i32"));
    k.zeile(&format!("store i32 {w}, ptr {kslot}, align 4"));
    k.zeile(&format!("store i1 false, ptr {hslot}, align 1"));
    let schritt = k.block("nach_schritt");
    let rumpf = k.block("nach_rumpf");
    let danach = k.block("nach_ende");
    k.zeile(&format!("br label %{schritt}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{schritt}:");
    k.beendet = false;
    let kc = k.tmp();
    k.zeile(&format!("{kc} = load i32, ptr {kslot}, align 4"));
    let hc = k.tmp();
    k.zeile(&format!("{hc} = load i1, ptr {hslot}, align 1"));
    // Absteigen? (`!h` und Kind vorhanden.)
    let (kaddr, _, _) = match slot_feld(k, &tab, &traeger, &kc, &kind, span) {
        Some(x) => x,
        None => return,
    };
    let (kist, klast) = opt_lesen(k, &kaddr);
    let runter_bedingt = k.tmp();
    k.zeile(&format!("{runter_bedingt} = xor i1 {hc}, true"));
    let runter = k.tmp();
    k.zeile(&format!("{runter} = and i1 {runter_bedingt}, {kist}"));
    let runter_arm = k.block("nach_runter");
    let weiter_arm = k.block("nach_weiter");
    k.zeile(&format!("br i1 {runter}, label %{runter_arm}, label %{weiter_arm}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{runter_arm}:");
    k.beendet = false;
    k.zeile(&format!("store i32 {klast}, ptr {kslot}, align 4"));
    k.zeile(&format!("store i1 false, ptr {hslot}, align 1"));
    k.zeile(&format!("br label %{schritt}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{weiter_arm}:");
    k.beendet = false;
    // Wurzel erreicht? (Durchlaufen, nie besucht.)
    let am_wurzel = k.tmp();
    k.zeile(&format!("{am_wurzel} = icmp eq i32 {kc}, {w}"));
    k.zeile(&format!("br i1 {am_wurzel}, label %{danach}, label %{rumpf}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{rumpf}:");
    k.beendet = false;
    // Nachfolger SCHON lesen (der Rumpf darf den Knoten zerstören).
    let (saddr, _, _) = match slot_feld(k, &tab, &traeger, &kc, &geschwister, span) {
        Some(x) => x,
        None => return,
    };
    let (sist, slast) = opt_lesen(k, &saddr);
    let (paddr, _, _) = match slot_feld(k, &tab, &traeger, &kc, &elter, span) {
        Some(x) => x,
        None => return,
    };
    let (pist, plast) = opt_lesen(k, &paddr);
    // `w = sibling ?? parent`, `h = sibling.is_none()` (Vater fehlt nur an der
    // Wurzel — dort bricht die Kette oben ab, hierher kommt sie nie).
    let wahl = k.tmp();
    k.zeile(&format!("{wahl} = select i1 {sist}, i32 {slast}, i32 {plast}"));
    let whahl = k.tmp();
    k.zeile(&format!("{whahl} = xor i1 {sist}, true"));
    let _ = pist;
    if let Some(inv) = &t.invariante {
        nehme_an(k, inv, "invariant");
    }
    k.oeffne();
    k.lege_an(t.variable.text.clone(), Bindung { ptr: kslot.clone(), ll: LlTyp::Int(32), zeichen: Zeichen::U, form: None, fluechtig: false });
    let fort = k.block("nach_fort");
    k.schleifen.push(SchleifenKontext { weiter: fort.clone(), danach: danach.clone(), marke: Some(t.variable.text.clone()), sperr_tiefe: k.sperren.len() });
    for st in &t.rumpf.anweisungen {
        if k.beendet {
            break;
        }
        senke_stmt(k, st);
    }
    k.schleifen.pop();
    k.schliesse();
    if !k.beendet {
        k.zeile(&format!("br label %{fort}"));
    }
    k.beendet = true;
    let _ = writeln!(k.text, "{fort}:");
    k.beendet = false;
    k.zeile(&format!("store i32 {wahl}, ptr {kslot}, align 4"));
    k.zeile(&format!("store i1 {whahl}, ptr {hslot}, align 1"));
    k.zeile(&format!("br label %{schritt}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{danach}:");
    k.beendet = false;
}

// ===================================================================================
// Gleitkomma-Schranken (Literale und benannte Konstanten)
// ===================================================================================

/// Gleitkomma-Wert hinter einem Ausdruck (Literal oder benannte Konstante).
fn gleit_wert(s: &Senke, e: &Expr) -> Option<f64> {
    match &e.art {
        ExprArt::Gleitkomma { bits, .. } => Some(f64::from_bits(*bits)),
        ExprArt::Klammer(x) => gleit_wert(s, x),
        ExprArt::Zahl(v) => Some(*v as f64),
        ExprArt::Ort(o) if o.suffixe.is_empty() => {
            let (bits, _) = s.gkonst.get(&o.basis.text).cloned()?;
            Some(f64::from_bits(bits))
        }
        _ => None,
    }
}

/// Gleitkomma-Schranken eines Bereichs (für `narrow` über Floats).
fn gleit_grenzen(s: &Senke, b: &Bereich) -> Option<(f64, f64, bool)> {
    Some((gleit_wert(s, &b.von)?, gleit_wert(s, &b.bis)?, b.exklusiv))
}

// ===================================================================================
// Zählung (`count … : …` — Zählschleife über Slots/Elemente)
// ===================================================================================

/// `count k in slots/elems of X : pred` — Zähler plus Prädikat je Element.
fn senke_zaehle(k: &mut Koerper, variable: &Ident, domaene: &Domaene, rumpf: &Pred, span: Span) -> Option<Wert> {
    // Grenze je Domäne (wie `traverse` — nur zählbare Domänen).
    let n: u64 = match domaene {
        Domaene::ElementeVon(o) => {
            let p = adresse_von_ort(k, o)?;
            match &p.ll {
                LlTyp::Feld(_, n) => *n,
                _ => {
                    weigere(k.s, "Y104", span, "counting over non-array".to_string());
                    return None;
                }
            }
        }
        Domaene::SlotsVon(o) | Domaene::Schlange(o) => {
            let tab = o.basis.text.clone();
            match k.s.tabellen.get(&tab).map(|(n, _)| *n) {
                Some(n) => n,
                None => {
                    weigere(k.s, "Y104", span, "counting over unknown table".to_string());
                    return None;
                }
            }
        }
        _ => {
            weigere(k.s, "Y104", span, "counting over this domain".to_string());
            return None;
        }
    };
    let kopf = k.block("zaehl_kopf");
    let rumpf_b = k.block("zaehl_rumpf");
    let danach = k.block("zaehl_ende");
    let zslot = k.alloca("i64");
    k.zeile(&format!("store i64 0, ptr {zslot}, align 8"));
    let islot = k.alloca("i64");
    k.zeile(&format!("store i64 0, ptr {islot}, align 8"));
    k.zeile(&format!("br label %{kopf}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{kopf}:");
    k.beendet = false;
    let iv = k.tmp();
    k.zeile(&format!("{iv} = load i64, ptr {islot}, align 8"));
    let cond = k.tmp();
    k.zeile(&format!("{cond} = icmp ult i64 {iv}, {n}"));
    k.zeile(&format!("br i1 {cond}, label %{rumpf_b}, label %{danach}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{rumpf_b}:");
    k.beendet = false;
    k.oeffne();
    // Binder als i32 (wie `traverse` — Vergleiche laufen darüber).
    let trunc = k.tmp();
    k.zeile(&format!("{trunc} = trunc i64 {iv} to i32"));
    let bslot = k.alloca("i32");
    k.zeile(&format!("store i32 {trunc}, ptr {bslot}, align 4"));
    k.lege_an(variable.text.clone(), Bindung { ptr: bslot, ll: LlTyp::Int(32), zeichen: Zeichen::U, form: None, fluechtig: false });
    let c = senke_predikat(k, rumpf);
    k.schliesse();
    let c = match c {
        Some(c) => c,
        None => {
            weigere(k.s, "Y104", span, "counting with unlowerable predicate".to_string());
            return None;
        }
    };
    let zv = k.tmp();
    k.zeile(&format!("{zv} = load i64, ptr {zslot}, align 8"));
    let plus = k.tmp();
    k.zeile(&format!("{plus} = select i1 {c}, i64 1, i64 0"));
    let neu = k.tmp();
    k.zeile(&format!("{neu} = add i64 {zv}, {plus}"));
    k.zeile(&format!("store i64 {neu}, ptr {zslot}, align 8"));
    let ni = k.tmp();
    k.zeile(&format!("{ni} = add i64 {iv}, 1"));
    k.zeile(&format!("store i64 {ni}, ptr {islot}, align 8"));
    k.zeile(&format!("br label %{kopf}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{danach}:");
    k.beendet = false;
    let t = k.tmp();
    k.zeile(&format!("{t} = load i64, ptr {zslot}, align 8"));
    Some(Wert { typ: LlTyp::Int(64), zeichen: Zeichen::U, text: t, form: None })
}

// ===================================================================================
// Erzeugte Tabellen-Operationen (`ops insert, remove, relabel`)
// ===================================================================================

/// Ruf auf eine erzeugte Operation (`Verzeichnis::insert(v, i)`).
fn senke_ops_ruf(k: &mut Koerper, tab: &str, wort: &str, r: &Ruf, span: Span) -> Option<Wert> {
    let (belegt, elter, woerter) = match k.s.tab_ops.get(tab).cloned() {
        Some(x) => x,
        None => {
            weigere(k.s, "Y104", span, format!("operation {wort} on a table without ops"));
            return None;
        }
    };
    if !woerter.iter().any(|w| w == wort) {
        weigere(k.s, "Y104", span, format!("table {tab} declares no `{wort}`"));
        return None;
    }
    // Argumente: (Träger, Index [, Elternindex]).
    let (braucht_elter, arity) = match (wort, &elter) {
        ("insert", Some(_)) => (true, 3),
        ("insert", None) => (false, 2),
        ("relabel", Some(_)) => (true, 3),
        ("remove", _) => (false, 2),
        _ => (false, 2),
    };
    if r.argumente.len() != arity {
        weigere(k.s, "Y104", span, format!("{wort} on {tab} takes {arity} arguments"));
        return None;
    }
    // Träger als Zeiger auf die Tabelle.
    let traeger = match &r.argumente[0].art {
        ExprArt::Ort(o) => {
            let p = adresse_von_ort(k, o)?;
            // Tabellenzeiger: bei Bedarf laden, sonst die Adresse.
            match &p.ll {
                LlTyp::Ptr => {
                    let t = k.tmp();
                    k.zeile(&format!("{t} = load ptr, ptr {}, align 8", p.addr));
                    t
                }
                LlTyp::Benannt(n) if n == tab => p.addr.clone(),
                _ => p.addr.clone(),
            }
        }
        _ => {
            weigere(k.s, "Y104", span, format!("{wort} needs a table place"));
            return None;
        }
    };
    let idx = senke_expr(k, &r.argumente[1])?;
    let ii = angleiche(k, idx, &LlTyp::Int(32), Zeichen::U)?;
    let (len, _) = match k.s.tabellen.get(tab).cloned() {
        Some(x) => x,
        None => return None,
    };
    let slot = sorge_slot(k.s, tab)?;
    let felder = k.s.tab_slots.get(tab).cloned().unwrap_or_default();
    // Elementzeiger.
    let zelle = k.tmp();
    k.zeile(&format!(
        "{zelle} = getelementptr [{len} x %{slot}], ptr {traeger}, i32 0, {} {}",
        ii.typ.text(),
        ii.text
    ));
    match wort {
        "insert" => {
            if braucht_elter {
                if let Some(e) = &elter {
                    let (nr, ftyp) = feld_nummer(k.s, &format!("{tab}$slot"), e)?;
                    let (fll, fz) = senke_typ(k.s, &ftyp)?;
                    let pv = senke_expr(k, &r.argumente[2])?;
                    // Elternfeld ist `option index into T`: der Ruf hängt EIN (Some p).
                    let pw = if matches!(grundform(k.s, &ftyp), TypExpr::Index { optional: true, .. }) {
                        gabopt_bauen(k, pv)?
                    } else {
                        angleiche_mit_weigere(k, pv, &fll, span)?
                    };
                    let fp = k.tmp();
                    k.zeile(&format!("{fp} = getelementptr %{slot}, ptr {zelle}, i32 0, i32 {nr}"));
                    k.zeile(&format!("store {} {}, ptr {fp}, align {}", fll.text(), pw.text, nat_align(&fll)));
                    let _ = fz;
                }
            }
            // Belegungsfeld setzen (Wahrheit).
            let (nr, ftyp) = feld_nummer(k.s, &format!("{tab}$slot"), &belegt)?;
            let (fll, _) = senke_typ(k.s, &ftyp)?;
            let fp = k.tmp();
            k.zeile(&format!("{fp} = getelementptr %{slot}, ptr {zelle}, i32 0, i32 {nr}"));
            let w = if fll == LlTyp::Int(1) {
                "true".to_string()
            } else {
                "1".to_string()
            };
            k.zeile(&format!("store {} {w}, ptr {fp}, align {}", fll.text(), nat_align(&fll)));
        }
        "remove" => {
            // Jedes Feld zurücksetzen (ein freier Slot trägt KEINEN Wert).
            for (i, (_, ftyp)) in felder.iter().enumerate() {
                let (fll, _) = senke_typ(k.s, ftyp)?;
                let nul = match fll {
                    LlTyp::Int(1) => "false".to_string(),
                    LlTyp::Int(_) => "0".to_string(),
                    LlTyp::F32 | LlTyp::F64 => "0.0".to_string(),
                    LlTyp::Ptr => "null".to_string(),
                    _ => "zeroinitializer".to_string(),
                };
                let fp = k.tmp();
                k.zeile(&format!("{fp} = getelementptr %{slot}, ptr {zelle}, i32 0, i32 {i}"));
                k.zeile(&format!("store {} {nul}, ptr {fp}, align {}", fll.text(), nat_align(&fll)));
            }
        }
        "relabel" => {
            if let Some(e) = &elter {
                let (nr, ftyp) = feld_nummer(k.s, &format!("{tab}$slot"), e)?;
                let (fll, _) = senke_typ(k.s, &ftyp)?;
                let pv = senke_expr(k, &r.argumente[2])?;
                let pw = if matches!(grundform(k.s, &ftyp), TypExpr::Index { optional: true, .. }) {
                    gabopt_bauen(k, pv)?
                } else {
                    angleiche_mit_weigere(k, pv, &fll, span)?
                };
                let fp = k.tmp();
                k.zeile(&format!("{fp} = getelementptr %{slot}, ptr {zelle}, i32 0, i32 {nr}"));
                k.zeile(&format!("store {} {}, ptr {fp}, align {}", fll.text(), pw.text, nat_align(&fll)));
            } else {
                weigere(k.s, "Y104", span, format!("relabel on {tab} without parent edge"));
                return None;
            }
        }
        _ => {
            weigere(k.s, "Y104", span, format!("operation {wort}"));
            return None;
        }
    }
    None
}

/// `Some(v)` als `%gabopt` (Tag 1, Nutzlast in den Bytes).
fn gabopt_bauen(k: &mut Koerper, v: Wert) -> Option<Wert> {
    sorge_gabopt(k.s);
    let groesse = match groesse_von_ll(k.s, &v.typ) {
        Some(g) if g <= 8 => g,
        _ => {
            weigere(k.s, "Y104", Span::neu(0, 0), "Some payload larger than 8 bytes".to_string());
            return None;
        }
    };
    let t0 = k.tmp();
    k.zeile(&format!("{t0} = insertvalue %gabopt undef, i32 1, 0"));
    let slot = k.alloca("%gabopt");
    k.zeile(&format!("store %gabopt {t0}, ptr {slot}, align 8"));
    let pp = k.tmp();
    k.zeile(&format!("{pp} = getelementptr %gabopt, ptr {slot}, i32 0, i32 1"));
    let pc = k.tmp();
    k.zeile(&format!("{pc} = getelementptr i8, ptr {pp}, i64 0"));
    k.zeile(&format!("store {} {}, ptr {pc}, align 1", v.typ.text(), v.text));
    let t1 = k.tmp();
    k.zeile(&format!("{t1} = load %gabopt, ptr {slot}, align 8"));
    let _ = groesse;
    Some(Wert { typ: LlTyp::Benannt("gabopt".to_string()), zeichen: Zeichen::Egal, text: t1, form: None })
}

// ===================================================================================
// Invarianten als Bereichs-Fakten (`forall s in slots of T : T.slots[s].f <= K`)
// ===================================================================================

/// Sammelt Bereichsfakten aus `forall`-Invarianten einer Tabelle.
fn sammle_invarianten_bereich(s: &mut Senke, t: &Tabelle) {
    let tn = t.name.text.clone();
    for inv in &t.invarianten {
        if let PredArt::Quantor(q) = &inv.pred.art {
            if q.art == QuantorArt::Alle {
                if let Domaene::SlotsVon(o) = &q.domaene {
                    // Die Domäne muss DIESE Tabelle nennen (`Self` oder der Name).
                    let passt = match o.basis.text.as_str() {
                        "Self" => true,
                        n => n == tn,
                    };
                    if passt {
                        // Der RUMPF des Quantors trägt die Aussage (nicht der Quantor).
                        sammle_vergleich_bereich(s, &tn, &q.variable.text, &q.rumpf);
                    }
                }
            }
        }
    }
}

/// Ein `forall`-Rumpf, der ein Tabellenfeld gegen eine Konstante hält.
fn sammle_vergleich_bereich(s: &mut Senke, tab: &str, var: &str, pred: &Pred) {
    // `P => Q` und `P && Q` durchsuchen (beide Hälften sind Fakten).
    match &pred.art {
        PredArt::Vergleich(e) => {
            if let ExprArt::Binaer(op, a, b) = &e.art {
                if let Some((feld, lo, hi)) = feld_gegen_konstante(s, tab, var, *op, a, b) {
                    let eintrag = s.inv_range.entry((tab.to_string(), feld)).or_insert((i128::MIN, i128::MAX));
                    eintrag.0 = eintrag.0.max(lo);
                    eintrag.1 = eintrag.1.min(hi);
                }
            }
        }
        PredArt::Folgt(a, b) | PredArt::Und(a, b) => {
            sammle_vergleich_bereich(s, tab, var, a);
            sammle_vergleich_bereich(s, tab, var, b);
        }
        PredArt::Klammer(a) => sammle_vergleich_bereich(s, tab, var, a),
        _ => {}
    }
}

/// `T.slots[v].f <op> K` (oder spiegelbildlich) → (Feld, lo, hi) inklusiv.
fn feld_gegen_konstante(
    s: &Senke,
    tab: &str,
    var: &str,
    op: BinOp,
    a: &Expr,
    b: &Expr,
) -> Option<(String, i128, i128)> {
    // Eine Seite ist der Feldzugriff, die andere eine Konstante.
    if let Some((feld, links)) = feldzugriff(s, tab, var, a) {
        let k = s.umg.konst_wert(&s.modul, b)?;
        let (_, lo, hi) = grenze_aus(op, links, k)?;
        return Some((feld, lo, hi));
    }
    if let Some((feld, links)) = feldzugriff(s, tab, var, b) {
        let k = s.umg.konst_wert(&s.modul, a)?;
        let (_, lo, hi) = grenze_aus(op, links, k)?;
        return Some((feld, lo, hi));
    }
    None
}

/// Schranke aus einem Vergleich `feld <op> K` — `links` sagt, ob das Feld links stand.
/// Steht es rechts (`K <op> feld`), dreht sich die Richtung um.
fn schranke(op: BinOp, k: i128) -> Option<(i128, i128)> {
    match op {
        BinOp::KleinerGleich => Some((i128::MIN, k)),
        BinOp::Kleiner => Some((i128::MIN, k - 1)),
        BinOp::GroesserGleich => Some((k, i128::MAX)),
        BinOp::Groesser => Some((k + 1, i128::MAX)),
        BinOp::Gleich => Some((k, k)),
        _ => None,
    }
}

fn grenze_aus(op: BinOp, links: bool, k: i128) -> Option<(String, i128, i128)> {
    let (lo, hi) = if links {
        schranke(op, k)?
    } else {
        // `K <op> f` ist `f <gedreht> K`.
        let gedreht = match op {
            BinOp::Kleiner => BinOp::Groesser,
            BinOp::KleinerGleich => BinOp::GroesserGleich,
            BinOp::Groesser => BinOp::Kleiner,
            BinOp::GroesserGleich => BinOp::KleinerGleich,
            o => o,
        };
        schranke(gedreht, k)?
    };
    Some((String::new(), lo, hi))
}

/// Erkennt `T.slots[v].f` (oder `Self.slots[v].f`) und liefert (Feld, links).
fn feldzugriff(s: &Senke, tab: &str, var: &str, e: &Expr) -> Option<(String, bool)> {
    let o = match &e.art {
        ExprArt::Ort(o) => o,
        ExprArt::Klammer(x) => return feldzugriff(s, tab, var, x),
        _ => return None,
    };
    // Suffixe: [Feld(slots), Index(var), Feld(f)]
    if o.suffixe.len() != 3 {
        return None;
    }
    let basis_ok = o.basis.text == tab || o.basis.text == "Self";
    if !basis_ok {
        return None;
    }
    match (&o.suffixe[0], &o.suffixe[1], &o.suffixe[2]) {
        (OrtSuffix::Feld(slots), OrtSuffix::Index(idx), OrtSuffix::Feld(f)) if slots.text == "slots" => {
            let idx_ok = matches!(&idx.art, ExprArt::Ort(io) if io.suffixe.is_empty() && io.basis.text == var);
            if idx_ok {
                return Some((f.text.clone(), true));
            }
        }
        _ => {}
    }
    None
}

// ===================================================================================
// Parameter-Attribute aus `requires` (dereferenceable, align)
// ===================================================================================

/// Zusatz-Attribute je Parameter aus den `requires`-Klauseln des Vertrags.
/// Was der Schreiber zugesagt hat, sagt der Erzeuger weiter — nichts erfunden.
fn parameter_attribute(requires: &[Pred], namen: &[String], params: &[(LlTyp, Zeichen)]) -> Vec<String> {
    let mut aus = vec![String::new(); params.len()];
    for pred in requires {
        if let PredArt::Vergleich(e) = &pred.art {
            // `lenof(p) >= N` / `N <= lenof(p)` → dereferenceable(N).
            if let ExprArt::Binaer(op, a, b) = &e.art {
                if let Some((name, n)) = lenof_gegen_zahl(*op, a, b) {
                    if let Some(i) = namen.iter().position(|x| x == &name) {
                        if matches!(params.get(i), Some((LlTyp::Ptr, _))) && n > 0 {
                            aus[i].push_str(&format!(" dereferenceable({n})"));
                        }
                    }
                }
            }
            // `aligned(p, N)` → align N (eine Zweierpotenz — der Prüfer hält sie).
            if let ExprArt::Eingebaut(b) = &e.art {
                if let Eingebaut::Aligned(oe, k) = &**b {
                    if let ExprArt::Ort(o) = &oe.art {
                        if o.suffixe.is_empty() {
                            if let ExprArt::Zahl(v) = &k.art {
                                if let Some(i) = namen.iter().position(|x| x == &o.basis.text) {
                                    if matches!(params.get(i), Some((LlTyp::Ptr, _))) {
                                        aus[i].push_str(&format!(" align {v}"));
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    aus
}

/// `lenof(p) >= N`, `lenof(p) > N`, `N <= lenof(p)` … → (Parametername, N).
fn lenof_gegen_zahl(op: BinOp, a: &Expr, b: &Expr) -> Option<(String, u128)> {
    fn lenof_name(e: &Expr) -> Option<String> {
        match &e.art {
            ExprArt::Eingebaut(be) => match &**be {
                Eingebaut::Lenof(TypOderOrt::Ort(o)) if o.suffixe.is_empty() => Some(o.basis.text.clone()),
                _ => None,
            },
            ExprArt::Klammer(x) => lenof_name(x),
            _ => None,
        }
    }
    fn zahl(e: &Expr) -> Option<u128> {
        match &e.art {
            ExprArt::Zahl(v) => Some(*v),
            ExprArt::Klammer(x) => zahl(x),
            _ => None,
        }
    }
    if let (Some(n), Some(k)) = (lenof_name(a), zahl(b)) {
        // `lenof(p) <op> K`
        return match op {
            BinOp::GroesserGleich | BinOp::Groesser => Some((n, k)),
            _ => None,
        };
    }
    if let (Some(k), Some(n)) = (zahl(a), lenof_name(b)) {
        // `K <op> lenof(p)`
        return match op {
            BinOp::KleinerGleich | BinOp::Kleiner => Some((n, k)),
            _ => None,
        };
    }
    None
}

// ===================================================================================
// Struct-Pfad-TBAA (kein Stempeln in dieser Sprache — darum gesund)
// ===================================================================================

/// Der ZUGRIFFS-Tag zu einem Typknoten: `!{!td, !td, i64 0}`.
/// Die Kette ist: Wurzel → Typ-Beschreiber → Tag; Anweisungen tragen den TAG.
fn tbaa_tag(s: &mut Senke, td: u32) -> u32 {
    let schluessel = format!("tag:{td}");
    if let Some(nr) = s.tbaa_tags.get(&schluessel) {
        return *nr;
    }
    let nr = s.meta_nr;
    s.meta_nr += 1;
    s.meta_knoten.insert(nr, format!("!{{!{td}, !{td}, i64 0}}"));
    s.tbaa_tags.insert(schluessel, nr);
    nr
}


/// Die TBAA-Wurzel (einmal je Einheit).
fn tbaa_wurzel(s: &mut Senke) -> u32 {
    if let Some((nr, _)) = s.meta_knoten.iter().find(|(_, d)| *d == "!{!\"gabbro-root\"}") {
        return *nr;
    }
    let nr = s.meta_nr;
    s.meta_nr += 1;
    s.meta_knoten.insert(nr, "!{!\"gabbro-root\"}".to_string());
    nr
}

/// Byte-Versatz eines Feldes im Struct (Summe der vorherigen Feldgrößen).
fn feld_versatz(s: &Senke, struktur: &str, feld: &str, eng: bool) -> Option<u64> {
    let felder: Vec<(String, TypExpr)> = if let Some(fs) = s.rekorde.get(struktur) {
        fs.clone()
    } else {
        let basis = struktur.strip_suffix("$slot").unwrap_or(struktur);
        s.tab_slots.get(basis).cloned()?
    };
    let mut off = 0u64;
    for (n, ft) in &felder {
        if n == feld {
            return Some(off);
        }
        off = off.checked_add(groesse_statisch(s, ft, eng)?)?;
    }
    None
}

/// **Strukturknoten** (clang-23-Form): `!{!"S", !m1, i64 o1, !m2, i64 o2, …}` —
/// die Feldtypen stehen EINGEBETTET, nicht als Kinder.
fn tbaa_struct_knoten(s: &mut Senke, struktur: &str) -> Option<u32> {
    if let Some(nr) = s.tbaa_struct.get(struktur) {
        return Some(*nr);
    }
    let felder: Vec<(String, TypExpr)> = if let Some(fs) = s.rekorde.get(struktur) {
        fs.clone()
    } else {
        let basis = struktur.strip_suffix("$slot").unwrap_or(struktur);
        s.tab_slots.get(basis).cloned()?
    };
    // Mitglieder mit Typknoten und Versatz (in Deklarationsordnung).
    let alt = s.eng_modus;
    s.eng_modus = false;
    let mut teile: Vec<String> = vec![format!("!\"{struktur}\"")];
    let mut off = 0u64;
    let mut ok = true;
    for (_, ft) in &felder {
        let ll = match senke_typ(s, ft) {
            Some((ll, _)) => ll,
            None => {
                ok = false;
                break;
            }
        };
        if let Some(td) = tbaa_knoten(s, &ll) {
            teile.push(format!("!{td}, i64 {off}"));
        }
        match groesse_statisch(s, ft, false) {
            Some(g) => off = off.saturating_add(g),
            None => {
                ok = false;
                break;
            }
        }
    }
    s.eng_modus = alt;
    if !ok {
        return None;
    }
    let def = format!("!{{ {} }}", teile.join(", "));
    let nr = s.meta_nr;
    s.meta_nr += 1;
    s.meta_knoten.insert(nr, def);
    s.tbaa_struct.insert(struktur.to_string(), nr);
    Some(nr)
}

/// **Zugriffs-Tag eines Feldes**: `!{!struct, !member, i64 offset}` (clang-23-Form).
fn tbaa_feld_tag(s: &mut Senke, struktur: &str, feld: &str, ll: &LlTyp, offset: u64) -> Option<u32> {
    let schluessel = format!("feldtag:{struktur}:{feld}:{offset}");
    if let Some(nr) = s.tbaa_tags.get(&schluessel) {
        return Some(*nr);
    }
    let st = tbaa_struct_knoten(s, struktur)?;
    let mt = tbaa_knoten(s, ll)?;
    // LLVM 23 verlangt, dass das Paar (Mitgliedstyp, Versatz) im Strukturknoten STEHT.
    // Steht es nicht (etwa ein Elementzugriff im Verbund-Feld), fällt der Zugriff auf
    // den flachen Skalar-Knoten zurück — nie ein Tag, den der Verifier verwirft.
    let paar = format!("!{mt}, i64 {offset}");
    let struktur_def = s.meta_knoten.get(&st).cloned().unwrap_or_default();
    if !struktur_def.contains(&paar) {
        return None;
    }
    let def = format!("!{{!{st}, !{mt}, i64 {offset}}}");
    let nr = s.meta_nr;
    s.meta_nr += 1;
    s.meta_knoten.insert(nr, def);
    s.tbaa_tags.insert(schluessel, nr);
    Some(nr)
}

// ===================================================================================
// Endrekursion als Schleife (kein Stapelwachstum — nie ein Überlauf)
// ===================================================================================

/// Rufpfade in einem Ausdruck (Rufe überall — auch in Schranken und Indizes).
fn rufe_in_expr(e: &Expr, out: &mut Vec<Pfad>) {
    match &e.art {
        ExprArt::Ruf(r) => {
            if let Some(p) = r.path() {
                out.push(p.clone());
            }
            for a in &r.argumente {
                rufe_in_expr(a, out);
            }
        }
        ExprArt::Klammer(x) => rufe_in_expr(x, out),
        ExprArt::Unaer(_, x) => rufe_in_expr(x, out),
        ExprArt::Binaer(_, a, b) => {
            rufe_in_expr(a, out);
            rufe_in_expr(b, out);
        }
        ExprArt::Ort(o) => {
            for sfx in &o.suffixe {
                if let OrtSuffix::Index(x) = sfx {
                    rufe_in_expr(x, out);
                }
            }
        }
        ExprArt::Eingebaut(b) => match &**b {
            Eingebaut::Aligned(a, c) => {
                rufe_in_expr(a, out);
                rufe_in_expr(c, out);
            }
            _ => {}
        },
        ExprArt::Zaehle { domaene, rumpf, .. } => {
            rufe_in_domaene(domaene, out);
            rufe_in_pred(rumpf, out);
        }
        _ => {}
    }
}

fn rufe_in_domaene(d: &Domaene, out: &mut Vec<Pfad>) {
    match d {
        Domaene::SlotsVon(o)
        | Domaene::NachfahrenVon(o)
        | Domaene::VorfahrenVon(o)
        | Domaene::Schlange(o)
        | Domaene::ElementeVon(o)
        | Domaene::AbbildungenVon(o) => {
            for sfx in &o.suffixe {
                if let OrtSuffix::Index(x) = sfx {
                    rufe_in_expr(x, out);
                }
            }
        }
        Domaene::KetteIn { ort, .. } => {
            for sfx in &ort.suffixe {
                if let OrtSuffix::Index(x) = sfx {
                    rufe_in_expr(x, out);
                }
            }
        }
        _ => {}
    }
}

fn rufe_in_pred(p: &Pred, out: &mut Vec<Pfad>) {
    match &p.art {
        PredArt::Vergleich(e) => rufe_in_expr(e, out),
        PredArt::Quantor(q) => {
            rufe_in_domaene(&q.domaene, out);
            rufe_in_pred(&q.rumpf, out);
        }
        PredArt::Klammer(x) => rufe_in_pred(x, out),
        PredArt::Nicht(x) => rufe_in_pred(x, out),
        PredArt::Und(a, b) | PredArt::Oder(a, b) | PredArt::Folgt(a, b) => {
            rufe_in_pred(a, out);
            rufe_in_pred(b, out);
        }
        _ => {}
    }
}

/// Alle Rufe eines Blocks (jede Stelle — auch Tausch-Rümpfe: dort echte Rufe).
fn rufe_in_block(b: &Block, out: &mut Vec<Pfad>) {
    for st in &b.anweisungen {
        rufe_in_stmt(st, out);
    }
}

fn rufe_in_stmt(st: &Stmt, out: &mut Vec<Pfad>) {
    match &st.art {
        StmtArt::Let(l) => rufe_in_expr(&l.wert, out),
        StmtArt::LetSonst(l) => match &l.quelle {
            LetQuelle::Ruf(r) => {
                if let Some(p) = r.path() {
                    out.push(p.clone());
                }
                for a in &r.argumente {
                    rufe_in_expr(a, out);
                }
            }
            LetQuelle::Ort(o) => {
                for sfx in &o.suffixe {
                    if let OrtSuffix::Index(x) = sfx {
                        rufe_in_expr(x, out);
                    }
                }
            }
        },
        StmtArt::Zuweisung(z) => {
            for sfx in &z.ziel.suffixe {
                if let OrtSuffix::Index(x) = sfx {
                    rufe_in_expr(x, out);
                }
            }
            rufe_in_expr(&z.wert, out);
        }
        StmtArt::Wenn(w) => {
            for (c, b) in &w.zweige {
                rufe_in_expr(c, out);
                rufe_in_block(b, out);
            }
            if let Some(s) = &w.sonst {
                rufe_in_block(s, out);
            }
        }
        StmtArt::Match(m) => {
            rufe_in_expr(&m.gegenstand, out);
            for z in &m.zweige {
                rufe_in_block(&z.rumpf, out);
            }
        }
        StmtArt::Schleife(s) => match &**s {
            Schleife::Traverse(t) => {
                if let Some(g) = &t.gegenstand {
                    rufe_in_expr(g, out);
                }
                if let Some(m) = &t.mass {
                    rufe_in_expr(m, out);
                }
                if let Some(i) = &t.invariante {
                    rufe_in_pred(i, out);
                }
                rufe_in_domaene(&t.domaene, out);
                rufe_in_block(&t.rumpf, out);
            }
            Schleife::Retry(r) => {
                if let Some(b) = &r.bis {
                    rufe_in_pred(b, out);
                }
                rufe_in_expr(&r.schranke, out);
                if let Some(i) = &r.invariante {
                    rufe_in_pred(i, out);
                }
                rufe_in_block(&r.rumpf, out);
            }
            Schleife::Forever(f) => {
                rufe_in_expr(&f.je_durchgang, out);
                if let Some(i) = &f.invariante {
                    rufe_in_pred(i, out);
                }
                rufe_in_block(&f.rumpf, out);
            }
        },
        StmtArt::Bricht(b) => rufe_in_block(&b.rumpf, out),
        StmtArt::Narrow(n) => {
            for sfx in &n.ort.suffixe {
                if let OrtSuffix::Index(x) = sfx {
                    rufe_in_expr(x, out);
                }
            }
            if let NarrowZiel::Bereich(b) = &n.ziel {
                rufe_in_expr(&b.von, out);
                rufe_in_expr(&b.bis, out);
            }
            rufe_in_block(&n.sonst, out);
        }
        StmtArt::Sperrt(s) => rufe_in_block(&s.rumpf, out),
        StmtArt::Observiert(o) => rufe_in_block(&o.rumpf, out),
        StmtArt::Publish(p) => rufe_in_expr(&p.wert, out),
        StmtArt::AwaitLoad(_) => {}
        StmtArt::Exchange(e) => {
            for sfx in &e.ort.suffixe {
                if let OrtSuffix::Index(x) = sfx {
                    rufe_in_expr(x, out);
                }
            }
            match &e.form {
                XForm::Update { rumpf, schranke, .. } => {
                    if let Some(s) = schranke {
                        rufe_in_expr(s, out);
                    }
                    rufe_in_block(rumpf, out);
                }
                XForm::Vergleich { wert, bedingung, .. } => {
                    rufe_in_expr(wert, out);
                    rufe_in_pred(bedingung, out);
                }
            }
        }
        StmtArt::Return(e) => {
            if let Some(x) = e {
                rufe_in_expr(x, out);
            }
        }
        StmtArt::Ruf(r) => {
            if let Some(p) = r.path() {
                out.push(p.clone());
            }
            for a in &r.argumente {
                rufe_in_expr(a, out);
            }
        }
        StmtArt::LibraryCall(l) => {
            for a in &l.args {
                rufe_in_expr(a, out);
            }
        }
        StmtArt::Alloc(a) => {
            rufe_in_expr(&a.wert, out);
            if let Some(s) = &a.sonst {
                rufe_in_block(s, out);
            }
        }
        StmtArt::ResetArena(_) | StmtArt::ResetSlot(_) => {}
        StmtArt::Grow(g) => {
            rufe_in_expr(&g.mehr, out);
            rufe_in_block(&g.sonst, out);
        }
        // **TODO §1-B:** calls in the freed slot's index expressions.
        StmtArt::Frei(f) => {
            for e in crate::ausdruecke_im_ort(&f.ort) {
                rufe_in_expr(e, out);
            }
        }
        StmtArt::Child(b) => rufe_in_block(b, out),
        StmtArt::Start(_) | StmtArt::Leave(_) | StmtArt::Next(_) => {}
    }
}

/// Schwanzrufe: `return f(…)` direkt (Klammern durchsichtig), überall im Rumpf —
/// AUSSER in Tausch-Rümpfen (dort liefert `return` neu, kein Ausgang).
fn schwanz_in_block(b: &Block, unter_tausch: bool, out: &mut Vec<Pfad>) {
    for st in &b.anweisungen {
        schwanz_in_stmt(st, unter_tausch, out);
    }
}

fn schwanz_in_stmt(st: &Stmt, unter_tausch: bool, out: &mut Vec<Pfad>) {
    match &st.art {
        StmtArt::Return(e) => {
            if !unter_tausch {
                if let Some(x) = e {
                    let mut y = x;
                    while let ExprArt::Klammer(i) = &y.art {
                        y = i;
                    }
                    if let ExprArt::Ruf(r) = &y.art {
                        if let Some(p) = r.path() {
                            out.push(p.clone());
                        }
                    }
                }
            }
        }
        StmtArt::Wenn(w) => {
            for (_, b) in &w.zweige {
                schwanz_in_block(b, unter_tausch, out);
            }
            if let Some(s) = &w.sonst {
                schwanz_in_block(s, unter_tausch, out);
            }
        }
        StmtArt::Match(m) => {
            for z in &m.zweige {
                schwanz_in_block(&z.rumpf, unter_tausch, out);
            }
        }
        StmtArt::Schleife(s) => match &**s {
            Schleife::Traverse(t) => schwanz_in_block(&t.rumpf, unter_tausch, out),
            Schleife::Retry(r) => schwanz_in_block(&r.rumpf, unter_tausch, out),
            Schleife::Forever(f) => schwanz_in_block(&f.rumpf, unter_tausch, out),
        },
        StmtArt::Bricht(b) => schwanz_in_block(&b.rumpf, unter_tausch, out),
        StmtArt::Narrow(n) => schwanz_in_block(&n.sonst, unter_tausch, out),
        StmtArt::Sperrt(s) => schwanz_in_block(&s.rumpf, unter_tausch, out),
        StmtArt::Observiert(o) => schwanz_in_block(&o.rumpf, unter_tausch, out),
        StmtArt::LetSonst(l) => schwanz_in_block(&l.sonst, unter_tausch, out),
        StmtArt::Alloc(a) => {
            if let Some(s) = &a.sonst {
                schwanz_in_block(s, unter_tausch, out);
            }
        }
        StmtArt::Grow(g) => schwanz_in_block(&g.sonst, unter_tausch, out),
        StmtArt::Child(b) => schwanz_in_block(b, unter_tausch, out),
        StmtArt::Exchange(e) => {
            if let XForm::Update { .. } = &e.form {
                // Tausch-Rumpf fängt `return` ab — kein Schwanz darunter.
            }
        }
        _ => {}
    }
}

// ===================================================================================
// Schleifenplan (Tarjan über Rufgraphen — nur endständige, einheitliche Zyklen)
// ===================================================================================

/// Ein umwandelbarer Zyklus: Mitglieder (deterministisch sortiert) mit Nummern.
#[derive(Clone)]
struct RekInfo {
    mitglieder: Vec<String>,
    ids: BTreeMap<String, u32>,
}

/// Rufgraph über `impl`-Pläne (aufgelöste Schlüssel, Tore/Extern als Blätter).
fn baue_rek_plan(s: &mut Senke) {
    // Kanten: Plan → gerufene Pläne (nur `impl`, nur direkte Rufe).
    let mut kanten: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    let plaene: Vec<(String, FnPlan)> = s.plaene.clone().into_iter().collect();
    for (voll, plan) in &plaene {
        let (rumpf, modul) = match plan {
            FnPlan::Impl { rumpf, modul, .. } => (rumpf, modul.clone()),
            FnPlan::Fertig { .. } => continue,
        };
        let mut pfade = Vec::new();
        rufe_in_block(rumpf, &mut pfade);
        let mut ziele = BTreeSet::new();
        for p in pfade {
            if let Some(k) = loese_schluessel(s, &modul, &p) {
                if matches!(s.plaene.get(&k), Some(FnPlan::Impl { .. })) {
                    ziele.insert(k);
                }
            }
        }
        kanten.insert(voll.clone(), ziele);
    }
    // Tarjan (iterativ — kein Stapelwachstum im Erzeuger selbst).
    let sccs = tarjan(&kanten);
    for scc in sccs {
        if scc.is_empty() {
            continue;
        }
        let zyklisch = scc.len() > 1 || kanten.get(&scc[0]).is_some_and(|z| z.contains(&scc[0]));
        if !zyklisch {
            continue;
        }
        if let Some(info) = rek_pruefe(s, &scc) {
            for m in &info.mitglieder {
                s.rek.insert(m.clone(), info.clone());
            }
        }
    }
}

/// Iterative Tarjan-SCC (deterministisch — sortierte Nachfolger).
fn tarjan(kanten: &BTreeMap<String, BTreeSet<String>>) -> Vec<Vec<String>> {
    let mut index: BTreeMap<String, u32> = BTreeMap::new();
    let mut tief: BTreeMap<String, u32> = BTreeMap::new();
    let mut auf_stapel: BTreeSet<String> = BTreeSet::new();
    let mut stapel: Vec<String> = Vec::new();
    let mut naechste_nr = 0u32;
    let mut sccs = Vec::new();
    // Knoten in Ordnung (deterministisch).
    let knoten: Vec<String> = kanten.keys().cloned().collect();
    for start in knoten {
        if index.contains_key(&start) {
            continue;
        }
        // Expliziter Arbeitsstapel: (Knoten, Nachfolger-rest).
        let mut arbeit: Vec<(String, Vec<String>)> = vec![(start.clone(), Vec::new())];
        // Initialisieren beim ersten Sehen (Nachfolger sortiert laden).
        while !arbeit.is_empty() {
            let v = arbeit.last().expect("Arbeitsstapel").0.clone();
            if !index.contains_key(&v) {
                index.insert(v.clone(), naechste_nr);
                tief.insert(v.clone(), naechste_nr);
                naechste_nr += 1;
                stapel.push(v.clone());
                auf_stapel.insert(v.clone());
                let mut nach: Vec<String> = kanten.get(&v).cloned().unwrap_or_default().into_iter().collect();
                nach.sort();
                arbeit.last_mut().expect("Arbeitsstapel").1 = nach;
            }
            let mut voran = false;
            while let Some(w) = arbeit.last_mut().expect("Arbeitsstapel").1.pop() {
                if !index.contains_key(&w) {
                    arbeit.push((w, Vec::new()));
                    voran = true;
                    break;
                } else if auf_stapel.contains(&w) {
                    let tv = tief[&v].min(tief[&w]);
                    tief.insert(v.clone(), tv);
                }
            }
            if voran {
                continue;
            }
            // Fertig: Wurzel einer SCC?
            arbeit_pop(&mut arbeit);
            if tief[&v] == index[&v] {
                let mut scc = Vec::new();
                while let Some(w) = stapel.pop() {
                    auf_stapel.remove(&w);
                    scc.push(w.clone());
                    if w == v {
                        break;
                    }
                }
                scc.sort();
                sccs.push(scc);
            }
            // Tiefstand zum Vorgänger reichen.
            if let Some((u, _)) = arbeit.last() {
                let tu = tief[u].min(tief[&v]);
                tief.insert(u.clone(), tu);
            }
        }
    }
    sccs
}

fn arbeit_pop(arbeit: &mut Vec<(String, Vec<String>)>) {
    arbeit.pop();
}

/// Prüft einen Zyklus auf Umwandelbarkeit (endständig, einheitlich, kanal-frei).
fn rek_pruefe(s: &Senke, scc: &[String]) -> Option<RekInfo> {
    // Einheitliche Antwort (exakt ein LlTyp — sonst echte Rufe).
    let mut ret: Option<LlTyp> = None;
    for m in scc {
        let sig = s.fns.get(m)?;
        if sig.or_nutz.is_some() {
            return None;
        }
        let (rt, _) = sig.ret.clone()?;
        if rt == LlTyp::Void {
            return None;
        }
        match &ret {
            None => ret = Some(rt),
            Some(r) if *r == rt => {}
            _ => return None,
        }
    }
    // Jeder Intra-Zyklus-Ruf endständig (sonst echte Rufe).
    let menge: BTreeSet<String> = scc.iter().cloned().collect();
    for m in scc {
        let plan = s.plaene.get(m)?;
        let (rumpf, modul) = match plan {
            FnPlan::Impl { rumpf, modul, .. } => (rumpf, modul),
            FnPlan::Fertig { .. } => return None,
        };
        let mut alle = Vec::new();
        rufe_in_block(rumpf, &mut alle);
        let mut schwanz = Vec::new();
        schwanz_in_block(rumpf, false, &mut schwanz);
        let mut schwanz_aufgeloest = BTreeSet::new();
        for p in schwanz {
            if let Some(k) = loese_schluessel(s, modul, &p) {
                schwanz_aufgeloest.insert(k);
            }
        }
        for p in alle {
            if let Some(k) = loese_schluessel(s, modul, &p) {
                if menge.contains(&k) && !schwanz_aufgeloest.contains(&k) {
                    return None;
                }
            }
        }
    }
    let mut mitglieder = scc.to_vec();
    mitglieder.sort();
    let ids = mitglieder.iter().enumerate().map(|(i, m)| (m.clone(), i as u32)).collect();
    Some(RekInfo { mitglieder, ids })
}

/// Laufzeit-Kontext einer Schleifenfunktion (Zustand, Schleife, Antwort).
struct RekKontext {
    info: RekInfo,
    /// Zustand je Mitglied (Vollname → Ablagen in Parameterordnung).
    zustand: BTreeMap<String, Vec<String>>,
    schleife: String,
    ret: (LlTyp, Zeichen),
}

// ===================================================================================
// Schleifen-Emission (Zustand je Mitglied, Versand, Schwanzsprung)
// ===================================================================================


// ===================================================================================
// Schleifen-Emission (Zustand je Mitglied, Versand, Schwanzsprung)
// ===================================================================================

/// Schwanzruf als Sprung senken (Zustand laden, Versand setzen, Schleife).
/// `None`: kein Schwanzruf hierher — der Ruf läuft normal.
fn schwanz_ruf(k: &mut Koerper, x: &Expr, span: Span) -> Option<()> {
    // Kontext klonen (keine Leihe über Senken hinweg).
    let (mitglieder, zustand, schleife) = match &k.rek {
        Some(r) => (r.info.mitglieder.clone(), r.zustand.clone(), r.schleife.clone()),
        None => return None,
    };
    let mut y = x;
    while let ExprArt::Klammer(i) = &y.art {
        y = i;
    }
    let r = match &y.art {
        ExprArt::Ruf(r) => r.clone(),
        _ => return None,
    };
    if !r.marken.is_empty() {
        return None;
    }
    let pfad = r.path()?.clone();
    let ziel = loese_schluessel(k.s, &k.modul.clone(), &pfad)?;
    if !mitglieder.contains(&ziel) {
        return None;
    }
    let tsig = k.s.fns.get(&ziel).cloned()?;
    // Argumente wie am Ruf (Geister belegen Stellen, fallen weg).
    let mut ai = 0usize;
    let mut werte: Vec<(String, String)> = Vec::new();
    for (gi, ghost) in tsig.geist_param.iter().enumerate() {
        let ae = r.argumente.get(ai)?.clone();
        ai += 1;
        if *ghost {
            continue;
        }
        let (pt, _) = tsig.params.get(werte.len()).cloned()?;
        let w = verfall_arg(k, &ae, &pt, span)?;
        let ww = angleiche(k, w, &pt, Zeichen::Egal)?;
        werte.push((pt.text(), ww.text));
        let _ = gi;
    }
    if ai != r.argumente.len() {
        return None;
    }
    let slots = zustand.get(&ziel)?.clone();
    if slots.len() != werte.len() {
        return None;
    }
    // Die Freigabe (jeder Ausgang) setzt `return_freigabe` vor den Sprung.
    for ((t, text), slot) in werte.iter().zip(slots.iter()) {
        k.zeile(&format!("store {t} {text}, ptr {slot}, align 8"));
    }
    let id = mitglieder.iter().position(|m| m == &ziel)? as u32;
    if mitglieder.len() > 1 {
        let dslot = zustand.get("!versand")?.first()?.clone();
        k.zeile(&format!("store i32 {id}, ptr {dslot}, align 4"));
    }
    k.zeile(&format!("br label %{schleife}"));
    k.beendet = true;
    Some(())
}

/// Schleifenfunktion senken (jedes Mitglied ruft über den Versand).
fn emit_rek(s: &mut Senke, voll: &str, info: &RekInfo) {
    let emit = s.emitnamen.get(voll).cloned().unwrap_or_else(|| voll.to_string());
    let sig = match s.fns.get(voll).cloned() {
        Some(x) => x,
        None => return,
    };
    let (ret_ll, _) = match sig.ret.clone() {
        Some(x) => x,
        None => return,
    };
    let ret_text = ret_ll.text();
    // Signatur des Eintritts (eigene Parameter, eigene Attribute).
    let ps: Vec<String> = sig
        .params
        .iter()
        .zip(sig.eigen_param.iter().chain(std::iter::repeat(&false)))
        .enumerate()
        .map(|(i, ((t, _), e))| param_zeile(t, *e, i, ""))
        .collect();
    let _ = writeln!(s.rumpf, "define {ret_text} {}({}) {{", gname(&emit), ps.join(", "));
    let _ = writeln!(s.rumpf, "eintritt:");
    let mut k = Koerper {
        s,
        text: String::new(),
        allocas: String::new(),
        zaehler: 0,
        bloecke: 0,
        bereiche: vec![HashMap::new()],
        funktionsname: emit.clone(),
        gegenwart: "eintritt".to_string(),
        rueck: Some((ret_ll.clone(), Zeichen::Egal)),
        beendet: false,
        schleifen: Vec::new(),
        sperren: Vec::new(),
        maske_zellen: BTreeMap::new(),
        kind: Default::default(),
        alt_wert: None,
        ergebnis_wert: None,
        or_nutz: None,
        modul: String::new(),
        geist_rueck: false,
        tausch_rueck: None,
        rek: None,
        sperrtiefe: 0,
    };
    // Zustand je Mitglied (Ablagen in Parameterordnung) plus Versand.
    let mut zustand: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for m in &info.mitglieder {
        let msig = match k.s.fns.get(m).cloned() {
            Some(x) => x,
            None => return,
        };
        let mut slots = Vec::new();
        for (pt, _) in &msig.params {
            slots.push(k.alloca(&pt.text()));
        }
        zustand.insert(m.clone(), slots);
    }
    let dslot = if info.mitglieder.len() > 1 {
        let d = k.alloca("i32");
        zustand.insert("!versand".to_string(), vec![d.clone()]);
        Some(d)
    } else {
        None
    };
    // Eintritt: eigene Parameter ablegen, Versand setzen, Schleife.
    let eigene = match zustand.get(voll) {
        Some(x) => x.clone(),
        None => return,
    };
    for (i, slot) in eigene.iter().enumerate() {
        let (pt, _) = match sig.params.get(i) {
            Some(x) => x.clone(),
            None => return,
        };
        k.zeile(&format!("store {} %p{i}, ptr {slot}, align {}", pt.text(), nat_align(&pt)));
    }
    if let Some(d) = &dslot {
        let id = info.ids.get(voll).copied().unwrap_or(0);
        k.zeile(&format!("store i32 {id}, ptr {d}, align 4"));
    }
    // Modul und Vertrag für den Rumpf.
    k.modul = modul_von_voll(voll);
    for pred in &sig.vertrag_requires.clone() {
        nehme_an(&mut k, pred, "requires");
    }
    let schleife = k.block("rek_schleife");
    k.zeile(&format!("br label %{schleife}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{schleife}:");
    k.beendet = false;
    k.rek = Some(RekKontext { info: info.clone(), zustand: zustand.clone(), schleife: schleife.clone(), ret: (ret_ll.clone(), Zeichen::Egal) });
    // Arme je Mitglied (Versand oder direkt).
    if info.mitglieder.len() == 1 {
        let m = &info.mitglieder[0];
        if emit_rek_arm(&mut k, m, &zustand).is_none() {
            return;
        }
    } else {
        let d = dslot.clone().expect("Versand geprüft");
        let dv = k.tmp();
        k.zeile(&format!("{dv} = load i32, ptr {d}, align 4"));
        let mut faelle = Vec::new();
        let mut arme = Vec::new();
        for m in &info.mitglieder {
            let arm = k.block("rek_arm");
            let id = info.ids.get(m).copied().unwrap_or(0);
            faelle.push(format!("i32 {id}, label %{arm}"));
            arme.push((m.clone(), arm));
        }
        let falle = k.block("rek_falle");
        // Fälle je Zeile (LLVM 23 lehnt kommagetrennte Einzeiler ab).
        k.zeile(&format!("switch i32 {dv}, label %{falle} ["));
        for fall in &faelle {
            k.zeile(&format!("    {fall}"));
        }
        k.zeile("]");
        k.beendet = true;
        let _ = writeln!(k.text, "{falle}:");
        k.beendet = false;
        k.zeile("unreachable");
        k.beendet = true;
        for (m, arm) in arme {
            let _ = writeln!(k.text, "{arm}:");
            k.beendet = false;
            if emit_rek_arm(&mut k, &m, &zustand).is_none() {
                return;
            }
            // Arm ohne Ausgang: Schleife (darf nicht passieren — Rümpfe kehren).
            if !k.beendet {
                k.zeile("unreachable");
                k.beendet = true;
            }
        }
    }
    let (text, allocas) = (k.text, k.allocas);
    s.rumpf.push_str(&allocas);
    s.rumpf.push_str(&text);
    let _ = writeln!(s.rumpf, "}}");
    s.beleg_funktionen.push((
        emit,
        sig.params.iter().map(|(t, _)| t.text()).collect(),
        ret_text,
        "impl".to_string(),
    ));
}

/// Ein Arm der Schleife (Parameter binden, Rumpf mit Schwanzsprung).
fn emit_rek_arm(k: &mut Koerper, m: &str, zustand: &BTreeMap<String, Vec<String>>) -> Option<()> {
    let plan = k.s.plaene.get(m).cloned()?;
    let (rumpf, params, namen, formen) = match plan {
        FnPlan::Impl { rumpf, params, namen, formen, .. } => (rumpf, params, namen, formen),
        FnPlan::Fertig { .. } => return None,
    };
    let slots = zustand.get(m)?.clone();
    k.oeffne();
    for (((pt, pz), pname), (slot, pform)) in params.iter().zip(namen.iter()).zip(slots.iter().zip(formen.iter())) {
        k.lege_an(pname.clone(), Bindung { ptr: slot.clone(), ll: pt.clone(), zeichen: *pz, form: Some(pform.clone()), fluechtig: ist_fluechtig(k.s, &Some(pform.clone())) });
    }
    senke_block(k, &rumpf);
    k.schliesse();
    if !k.beendet {
        k.zeile("unreachable");
        k.beendet = true;
    }
    Some(())
}

/// Modul aus einem Vollnamen (`m::f` → `m`, sonst leer).
fn modul_von_voll(voll: &str) -> String {
    match voll.rfind("::") {
        Some(i) => voll[..i].to_string(),
        None => String::new(),
    }
}

// ===================================================================================
// Arenen: Reserve (Adressraum) gegen Belegung (RAM) — nichts liegt vorab
// ===================================================================================

/// Rohe Tor-Nummern der Laufzeit je Ziel (nur der Kern darunter).
fn laufzeit_tor(s: &Senke, name: &str) -> Option<(i64, &'static str, &'static str)> {
    match (s.ziel.name, name) {
        ("x86_64", "mmap") => Some((9, "syscall", "rax")),
        ("x86_64", "mprotect") => Some((10, "syscall", "rax")),
        ("x86_64", "munmap") => Some((11, "syscall", "rax")),
        ("x86_64", "madvise") => Some((28, "syscall", "rax")),
        ("x86_64", "clone") => Some((56, "syscall", "rax")),
        ("x86_64", "futex") => Some((202, "syscall", "rax")),
        ("x86_64", "exit") => Some((60, "syscall", "rax")),
        ("aarch64", "mmap") => Some((222, "svc #0", "x0")),
        ("aarch64", "mprotect") => Some((226, "svc #0", "x0")),
        ("aarch64", "munmap") => Some((215, "svc #0", "x0")),
        ("aarch64", "madvise") => Some((233, "svc #0", "x0")),
        ("aarch64", "clone") => Some((220, "svc #0", "x0")),
        ("aarch64", "futex") => Some((98, "svc #0", "x0")),
        ("aarch64", "exit") => Some((93, "svc #0", "x0")),
        _ => None,
    }
}

/// Roher Tor-Ruf der Laufzeit (kein Gabbro-Tor — der Erzeuger bucht die Nummern).
/// Eingaben: (Register, Operand) in ABI-Ordnung; Antwort: i64.
fn laufzeit_ruf(k: &mut Koerper, name: &str, eingaben: &[(String, String)], span: Span) -> Option<String> {
    let (nummer, template, ret_reg) = match laufzeit_tor(k.s, name) {
        Some(x) => x,
        None => {
            weigere(k.s, "Y103", span, format!("runtime gate {name} on this target"));
            return None;
        }
    };
    let mut bind = vec![format!("={{{ret_reg}}}")];
    let num_reg = if k.s.ziel.name == "x86_64" { "rax" } else { "x8" };
    bind.push(format!("{{{num_reg}}}"));
    for (reg, _) in eingaben {
        bind.push(format!("{{{reg}}}"));
    }
    bind.push("~{memory}".to_string());
    // Clobbers je Ziel (was der Kern zerstören darf).
    if k.s.ziel.name == "x86_64" {
        bind.push("~{rcx}".to_string());
        bind.push("~{r11}".to_string());
    }
    let mut ops = vec![format!("i64 {nummer}")];
    for (_, text) in eingaben {
        ops.push(format!("i64 {text}"));
    }
    let t = k.tmp();
    k.zeile(&format!(
        "{t} = call i64 asm sideeffect \"{template}\", \"{}\"({})",
        bind.join(","),
        ops.join(", ")
    ));
    Some(t)
}

/// Rohe Antwort fehlgeschlagen? (Kernel antwortet `-errno` in `-4095..-1`.)
fn ruf_fehlschlag(k: &mut Koerper, roh: &str) -> String {
    let t = k.tmp();
    k.zeile(&format!("{t} = icmp uge i64 {roh}, -4095"));
    t
}

/// Elementbreite einer Arena (mindestens 1).
fn arena_breite(ai: &ArenaInfo) -> u64 {
    ai.groesse.max(1)
}

/// Stellt bereit: `bereit >= bedarf` Elemente (sonst `voll`). Reserve einmalig
/// (`PROT_NONE` — Adressraum ohne RAM), Commit per `mprotect` bei Bedarf.
fn arena_bereit(k: &mut Koerper, tisch: &str, bedarf: &str, voll: &str, span: Span) -> Option<()> {
    let ai = k.s.arenen.get(tisch).cloned()?;
    let breite = arena_breite(&ai);
    let basis = gteil(tisch, "basis");
    let bereit = gteil(tisch, "bereit");
    // Reserve da? (Basis 0 = keine.)
    let b = k.tmp();
    k.zeile(&format!("{b} = load i64, ptr {basis}, align 8"));
    let hat = k.tmp();
    k.zeile(&format!("{hat} = icmp ne i64 {b}, 0"));
    let hat_arm = k.block("arena_hat");
    let neu_arm = k.block("arena_neu");
    let weiter = k.block("arena_weiter");
    k.zeile(&format!("br i1 {hat}, label %{hat_arm}, label %{neu_arm}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{neu_arm}:");
    k.beendet = false;
    // Reserve: `max` Elemente Adressraum, ohne Zugriffsrecht (kein RAM).
    let gesamt = ai.max.saturating_mul(breite);
    let regs = if k.s.ziel.name == "x86_64" {
        vec![
            ("rdi".to_string(), "0".to_string()),
            ("rsi".to_string(), format!("{gesamt}")),
            ("rdx".to_string(), "0".to_string()),
            ("r10".to_string(), "34".to_string()),
            ("r8".to_string(), "-1".to_string()),
            ("r9".to_string(), "0".to_string()),
        ]
    } else {
        vec![
            ("x0".to_string(), "0".to_string()),
            ("x1".to_string(), format!("{gesamt}")),
            ("x2".to_string(), "0".to_string()),
            ("x3".to_string(), "34".to_string()),
            ("x4".to_string(), "-1".to_string()),
            ("x5".to_string(), "0".to_string()),
        ]
    };
    let roh = laufzeit_ruf(k, "mmap", &regs, span)?;
    let schlecht = ruf_fehlschlag(k, &roh);
    // Erfolg speichert die Basis SOFORT (kein SSA-Wert über den Join — Dominanz).
    let ok_arm = k.block("arena_reserviert");
    k.zeile(&format!("br i1 {schlecht}, label %{voll}, label %{ok_arm}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{ok_arm}:");
    k.beendet = false;
    // The side metadata has its own anonymous reservation. Only free links
    // and live-count words are touched; its size does not preallocate RAM.
    // Like the payload, it is reserved PROT_NONE (address space, no RAM, no
    // overcommit charge) and committed page by page together with the payload
    // chunks; only the small count words are made accessible here.
    let meta_bytes = memory::metadata_size(&ai)?;
    let args = runtime_args(k.s.ziel, &["0".into(), meta_bytes.to_string(), "0".into(), "34".into(), "-1".into(), "0".into()]);
    let meta = laufzeit_ruf(k, "mmap", &args, span)?;
    let bad_meta = ruf_fehlschlag(k, &meta);
    let meta_ok = k.block("arena_metadata"); let meta_fail = k.block("arena_metadata_failed");
    k.zeile(&format!("br i1 {bad_meta}, label %{meta_fail}, label %{meta_ok}")); k.beendet = true;
    let _ = writeln!(k.text, "{meta_fail}:"); k.beendet = false;
    let args = runtime_args(k.s.ziel, &[roh.clone(), gesamt.to_string()]);
    let unmapped = laufzeit_ruf(k, "munmap", &args, span)?;
    runtime_success(k, &unmapped);
    k.zeile(&format!("br label %{voll}")); k.beendet = true;
    let _ = writeln!(k.text, "{meta_ok}:"); k.beendet = false;
    let counts_from = (ai.max * 8) & !4095;
    let counts_to = meta_bytes.div_ceil(4096) * 4096;
    let counts_at = k.tmp();
    k.zeile(&format!("{counts_at} = add i64 {meta}, {counts_from}"));
    let args = runtime_args(k.s.ziel, &[counts_at, (counts_to - counts_from).to_string(), "3".into()]);
    let counts = laufzeit_ruf(k, "mprotect", &args, span)?;
    let bad_counts = ruf_fehlschlag(k, &counts);
    let counts_ok = k.block("arena_counts"); let counts_fail = k.block("arena_counts_failed");
    k.zeile(&format!("br i1 {bad_counts}, label %{counts_fail}, label %{counts_ok}")); k.beendet = true;
    let _ = writeln!(k.text, "{counts_fail}:"); k.beendet = false;
    let args = runtime_args(k.s.ziel, &[meta.clone(), meta_bytes.to_string()]);
    let unmapped = laufzeit_ruf(k, "munmap", &args, span)?;
    runtime_success(k, &unmapped);
    let args = runtime_args(k.s.ziel, &[roh.clone(), gesamt.to_string()]);
    let unmapped = laufzeit_ruf(k, "munmap", &args, span)?;
    runtime_success(k, &unmapped);
    k.zeile(&format!("br label %{voll}")); k.beendet = true;
    let _ = writeln!(k.text, "{counts_ok}:"); k.beendet = false;
    k.zeile(&format!("store i64 {meta}, ptr {}, align 8", gteil(tisch, "meta")));
    k.zeile(&format!("store i64 {roh}, ptr {basis}, align 8"));
    k.zeile(&format!("br label %{hat_arm}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{hat_arm}:");
    k.beendet = false;
    let commit_arm = k.block("arena_commit");
    k.zeile(&format!("br label %{commit_arm}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{commit_arm}:");
    k.beendet = false;
    // Commit-Schleife bis `bereit >= bedarf` (in Schritten, unter der Decke).
    let kopf = k.block("arena_kopf");
    let schritt = k.block("arena_schritt");
    k.zeile(&format!("br label %{kopf}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{kopf}:");
    k.beendet = false;
    let c = k.tmp();
    k.zeile(&format!("{c} = load i64, ptr {bereit}, align 8"));
    let reicht = k.tmp();
    k.zeile(&format!("{reicht} = icmp uge i64 {c}, {bedarf}"));
    k.zeile(&format!("br i1 {reicht}, label %{weiter}, label %{schritt}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{schritt}:");
    k.beendet = false;
    // Nächster Schritt (an der Decke: voll). Alles in BYTES (Elemente nur an
    // der Naht: `bereit`/`bedarf` zählen Elemente, der Rest Bytes): Bedarf in
    // Bytes, auf 1 MiB ausgerichtet (Vielfaches von 4K/16K/64K-Seiten), an der
    // Decke gekappt. Leere Länge heißt voll, nicht Wachstum.
    let vollep = ai.max.saturating_mul(breite);
    let bb = k.tmp();
    k.zeile(&format!("{bb} = load i64, ptr {basis}, align 8"));
    let versatz = k.tmp();
    k.zeile(&format!("{versatz} = mul i64 {c}, {breite}"));
    let fehlen = k.tmp();
    k.zeile(&format!("{fehlen} = sub i64 {bedarf}, {c}"));
    let brauchen = k.tmp();
    k.zeile(&format!("{brauchen} = mul i64 {fehlen}, {breite}"));
    let ende = k.tmp();
    k.zeile(&format!("{ende} = add i64 {versatz}, {brauchen}"));
    // Aufrunden auf 1 MiB (2^20): `ende + 0xFFFFF & ~0xFFFFF`.
    let ende_auf = k.tmp();
    k.zeile(&format!("{ende_auf} = add i64 {ende}, 1048575"));
    let ende_rund = k.tmp();
    k.zeile(&format!("{ende_rund} = and i64 {ende_auf}, -1048576"));
    // Von unten abrunden (bereits committete Seiten doppelt zu mappen ist
    // idempotent), an der Decke kappen.
    let von = k.tmp();
    k.zeile(&format!("{von} = and i64 {versatz}, -1048576"));
    let decke = k.tmp();
    k.zeile(&format!("{decke} = sub i64 {vollep}, {von}"));
    let bis = k.tmp();
    k.zeile(&format!("{bis} = sub i64 {ende_rund}, {von}"));
    // Kleineres von Bedarf und Rest (ohne Zweig: min über icmp+select).
    let mehr_bedarf = k.tmp();
    k.zeile(&format!("{mehr_bedarf} = icmp ult i64 {bis}, {decke}"));
    let lang = k.tmp();
    k.zeile(&format!("{lang} = select i1 {mehr_bedarf}, i64 {bis}, i64 {decke}"));
    let adr = k.tmp();
    k.zeile(&format!("{adr} = add i64 {bb}, {von}"));
    // Leere Länge: nichts mehr zu holen (Decke erreicht oder Reserve leer).
    let nichts = k.tmp();
    k.zeile(&format!("{nichts} = icmp eq i64 {lang}, 0"));
    k.zeile(&format!("br i1 {nichts}, label %{voll}, label %{weiter}_c"));
    k.beendet = true;
    let commit2 = format!("{weiter}_c");
    let _ = writeln!(k.text, "{commit2}:");
    k.beendet = false;
    // Sampling (only with `pb`): ask first, then commit. Below the
    // user threshold the `voll` branch runs (OOM path) -- freestanding the
    // user function measures itself, no OS call in the generator. ONE call per
    // chunk (1 MiB), none on the fast path (`bereit >= bedarf` never asks).
    if let Some(d) = ai.sample.clone() {
        let frei = call_sample(k, &d, span)?;
        let f64 = angleiche(k, frei, &LlTyp::Int(64), Zeichen::U)?;
        let wenig = k.tmp();
        k.zeile(&format!("{wenig} = icmp ult i64 {}, {}", f64.text, d.schwelle));
        let genug = k.block("arena_genug");
        k.zeile(&format!("br i1 {wenig}, label %{voll}, label %{genug}"));
        k.beendet = true;
        let _ = writeln!(k.text, "{genug}:");
        k.beendet = false;
    }
    // The free-link words of the slots this chunk covers become accessible
    // first (page-rounded outward; committing a page twice is idempotent).
    let bedeckt_m = k.tmp();
    k.zeile(&format!("{bedeckt_m} = add i64 {von}, {lang}"));
    let slots_lo = k.tmp();
    k.zeile(&format!("{slots_lo} = udiv i64 {von}, {breite}"));
    let slots_hi = k.tmp();
    k.zeile(&format!("{slots_hi} = udiv i64 {bedeckt_m}, {breite}"));
    let lo8 = k.tmp();
    k.zeile(&format!("{lo8} = mul i64 {slots_lo}, 8"));
    let lo_page = k.tmp();
    k.zeile(&format!("{lo_page} = and i64 {lo8}, -4096"));
    let hi8 = k.tmp();
    k.zeile(&format!("{hi8} = mul i64 {slots_hi}, 8"));
    let hi_up = k.tmp();
    k.zeile(&format!("{hi_up} = add i64 {hi8}, 4095"));
    let hi_page = k.tmp();
    k.zeile(&format!("{hi_page} = and i64 {hi_up}, -4096"));
    let meta_len = k.tmp();
    k.zeile(&format!("{meta_len} = sub i64 {hi_page}, {lo_page}"));
    let meta_raw = k.tmp();
    k.zeile(&format!("{meta_raw} = load i64, ptr {}, align 8", gteil(tisch, "meta")));
    let meta_adr = k.tmp();
    k.zeile(&format!("{meta_adr} = add i64 {meta_raw}, {lo_page}"));
    let margs = runtime_args(k.s.ziel, &[meta_adr, meta_len, "3".into()]);
    let mrc = laufzeit_ruf(k, "mprotect", &margs, span)?;
    let mbad = ruf_fehlschlag(k, &mrc);
    let mok = k.block("arena_meta_ok");
    k.zeile(&format!("br i1 {mbad}, label %{voll}, label %{mok}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{mok}:");
    k.beendet = false;
    let regs2 = if k.s.ziel.name == "x86_64" {
        vec![
            ("rdi".to_string(), adr.clone()),
            ("rsi".to_string(), lang.clone()),
            ("rdx".to_string(), "3".to_string()),
        ]
    } else {
        vec![
            ("x0".to_string(), adr.clone()),
            ("x1".to_string(), lang.clone()),
            ("x2".to_string(), "3".to_string()),
        ]
    };
    let roh2 = laufzeit_ruf(k, "mprotect", &regs2, span)?;
    let schlecht2 = ruf_fehlschlag(k, &roh2);
    let ok_arm = k.block("arena_ok");
    k.zeile(&format!("br i1 {schlecht2}, label %{voll}, label %{ok_arm}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{ok_arm}:");
    k.beendet = false;
    // Bereit rückt auf ganze bedeckte Elemente vor (nie zurück, nie über die
    // Decke hinaus -- die Schleife oben läuft, bis `bereit >= bedarf`).
    let bedeckt = k.tmp();
    k.zeile(&format!("{bedeckt} = add i64 {von}, {lang}"));
    let stuecke = k.tmp();
    k.zeile(&format!("{stuecke} = udiv i64 {bedeckt}, {breite}"));
    let weiter_vorne = k.tmp();
    k.zeile(&format!("{weiter_vorne} = icmp ult i64 {c}, {stuecke}"));
    let neu = k.tmp();
    k.zeile(&format!("{neu} = select i1 {weiter_vorne}, i64 {stuecke}, i64 {c}"));
    k.zeile(&format!("store i64 {neu}, ptr {bereit}, align 8"));
    k.zeile(&format!("br label %{kopf}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{weiter}:");
    k.beendet = false;
    Some(())
}
