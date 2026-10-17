//! **Stapeltore und `child` für LLVM: der rohe Klon mit übergebenem Stapel.**
//!
//! Ein Tor mit `stack r` (`syscall … stack rsi`) ist der Aufruf, an dem ein zweiter Faden
//! entsteht: der Kern setzt im Kind `sp` auf das Register `r` und antwortet dort mit null.
//! Die Quelle schreibt den Kindpfad als `child { … }` hinter den Ruf (`N450`: der Ruf
//! dominiert die Region, ein Ruf gibt an eine Region; `N572`: jeder Stapelruf hat eine).
//!
//! **Was der Erzeuger daraus macht**, und warum es nicht „der Rumpf läuft inline" ist: nach
//! dem Befehl läuft das Kind mit dem Stapel, den das Programm übergab, aber mit dem
//! Registersatz des Vaters. Jeder Wert, den der Übersetzer des Vaters auf SEINEN Stapel
//! gelegt hat (Spills, Rahmen), ist für das Kind eine tote Zelle. Ein Kindrumpf im
//! Rahmen des Vaters wäre daher unsound, und der Prüfer sagt es auch (`N451`/`N452`: der
//! Kindpfad liest nur, was ihm übergeben wurde).
//!
//! 1. **Der Rumpf wird ausgelagert:** `child { … }` wird zur eigenen Funktion
//!    `gabbro_kind_N(übergebener Stapel)`; sie trägt nur den Namen, den der Ruf als Stapel
//!    übergab (die einzige geteilte Zelle), und liest sonst globale Orte.
//! 2. **Der Ruf springt im Kind selbst dorthin.** Ein einziger Inline-Assembler schreibt
//!    den Befehl, prüft die Antwort auf null und ruft im Kindzweig die Funktion mit dem
//!    übergebenen Stapelregister als Argument, ausgerichtet, mit leerem Rahmenzeiger.
//!    Der Vaterzweig läuft mit unveränderten Registern weiter (die Nummer, die Eingaben
//!    und die erklärten `clobbers` stehen an der Befehlsstelle wie bei jedem Tor). **Im
//!    Kind kehrt nichts in den Rahmen des Vaters zurück:** hinter dem Aufruf steht ein
//!    Trap, und die Funktion endet nach der Quelle in einem nie kehrenden Ruf (`N448`/
//!    `N449`).
//! 3. **Die `child`-Anweisung im Vater** (erreichbar nur, wenn das Tor im Vater null
//!    antwortete, was sein Vertrag ausschließt): ruft dieselbe Funktion, dann
//!    `unreachable` (der Prüfer hält: die Region kehrt nie zurück).
//!
//! `x86_64` und `aarch64`: die Befehlsfolgen unten; die Nummer, die Register und die
//! Fehlertafel sind die Daten des Programms (`target … { … number N … }`), nichts davon
//! steht hier. **Was nicht belegt ist:** dass der Kern wirklich `sp` aus dem Register
//! setzt, ist die Annahme des Tors (`assume … falsifier`), nicht dieser Datei.

use super::*;
use std::collections::HashSet;

/// Ein Tor mit `stack r`: das Register und die Stelle des Stapelparameters.
#[derive(Clone)]
pub(super) struct StapelTor {
    pub reg: String,
    pub stelle: usize,
}

/// Auszulagernde Kindregion (nach dem Lauf über die Funktion in `abarbeiten` gesenkt).
pub(super) struct Aufgabe {
    name: String,
    region: Block,
    /// Der übergebene Stapel als Parameter: (Name, Typ, Zeichen, deklarierte Form).
    param: Option<(String, LlTyp, Zeichen, TypExpr)>,
    modul: String,
}

#[derive(Default)]
pub(super) struct SenkeZustand {
    /// Kurzname der Tore mit Stapelklausel.
    pub tore: BTreeSet<String>,
    aufgaben: Vec<Aufgabe>,
    zaehler: u32,
    /// Namen der ausgelagerten Funktionen (`@llvm.used`: nur der Assembler ruft sie).
    pub benutzt: Vec<String>,
}

/// Je Funktionskörper: welche Region zu welcher Rufanweisung gehört.
#[derive(Default)]
pub(super) struct Zustand {
    /// Die Anweisung, die gerade gesenkt wird (Spanne): die Rufstelle eines Stapeltors.
    pub stmt: Option<Span>,
    paare: HashMap<Span, Block>,
    /// Region (Spanne des Blocks) → (Funktion, hat sie einen Parameter, Name des Stapels).
    fn_von: HashMap<Span, (String, Option<String>)>,
}

impl Zustand {
    /// Die Paarung dieses Körpers (die Aussage von `N450`, als Daten).
    pub(super) fn fuer(s: &SenkeZustand, rumpf: &Block) -> Zustand {
        if s.tore.is_empty() {
            return Zustand::default();
        }
        let tore: HashSet<String> = s.tore.iter().cloned().collect();
        let paare = crate::clone::kindpaare(rumpf, &tore).into_iter().collect();
        Zustand { stmt: None, paare, fn_von: HashMap::new() }
    }
}

/// Die Befehlsfolge des Stapeltors: der Befehl, dann im Kind der Sprung in die Region.
fn vorlage(ziel: &Ziel, tor_befehl: &str, antwort: &str, stapelreg: &str, funktion: &str, mit_arg: bool) -> String {
    if ziel.name == "x86_64" {
        // `$$` ist das Dollarzeichen der Inline-Assembler-Zeichenfolge. Die Ausrichtung
        // (16) verlangt die Aufrufkonvention vor jedem `call`.
        let mut t = format!("{tor_befehl}\\0A\\09testq %{antwort}, %{antwort}\\0A\\09jnz 1f");
        if mit_arg && stapelreg != "rdi" {
            t.push_str(&format!("\\0A\\09movq %{stapelreg}, %rdi"));
        }
        t.push_str(&format!(
            "\\0A\\09xorl %ebp, %ebp\\0A\\09andq $$-16, %rsp\\0A\\09callq {funktion}\\0A\\09ud2\\0A1:"
        ));
        t
    } else {
        let mut t = format!("{tor_befehl}\\0A\\09cbnz {antwort}, 1f");
        if mit_arg && stapelreg != "x0" {
            t.push_str(&format!("\\0A\\09mov x0, {stapelreg}"));
        }
        t.push_str(&format!(
            "\\0A\\09mov x29, xzr\\0A\\09mov x9, sp\\0A\\09and x9, x9, #-16\\0A\\09mov sp, x9\\0A\\09bl {funktion}\\0A\\09brk #0\\0A1:"
        ));
        t
    }
}

/// Das Tor am Ruf: Region paaren, auslagern, die Vorlage schreiben. `None`: verweigert.
pub(super) fn vorbereiten(k: &mut Koerper, tor: &Tor, st: &StapelTor, r: &Ruf, span: Span) -> Option<String> {
    let name = kurzname_tor(r);
    if tor.nie {
        weigere(k.s, "Y102", span, format!("stack-carrying gate {name} answers never"));
        return None;
    }
    let region = match k.kind.stmt.and_then(|sp| k.kind.paare.get(&sp)).cloned() {
        Some(b) => b,
        None => {
            weigere(
                k.s,
                "Y102",
                span,
                format!("stack-carrying gate {name} called with no `child` region behind the call"),
            );
            return None;
        }
    };
    // Der übergebene Stapel: ein bloßer Name als Argument an der Stapelstelle reist ins Kind.
    let mut arg = r.argumente.get(st.stelle)?;
    while let ExprArt::Klammer(i) = &arg.art {
        arg = i;
    }
    let param = match &arg.art {
        ExprArt::Ort(o) if o.suffixe.is_empty() => {
            let b = k.suche(&o.basis.text);
            match b {
                Some(Bindung { ll: LlTyp::Int(w), zeichen, form, .. }) if matches!(w, 8 | 16 | 32 | 64) => {
                    // Ohne erklärte Form (`let stapel = …`): das geschriebene Wort der Breite.
                    let form = form.unwrap_or_else(|| {
                        let wort = match (zeichen == Zeichen::S, w) {
                            (false, 8) => Kw::U8,
                            (false, 16) => Kw::U16,
                            (false, 32) => Kw::U32,
                            (false, _) => Kw::U64,
                            (true, 8) => Kw::I8,
                            (true, 16) => Kw::I16,
                            (true, 32) => Kw::I32,
                            (true, _) => Kw::I64,
                        };
                        TypExpr::Int(IntTy { wort, zucker: None, bereich: None, span })
                    });
                    Some((o.basis.text.clone(), LlTyp::Int(w), zeichen, form))
                }
                _ => {
                    weigere(
                        k.s,
                        "Y102",
                        span,
                        format!("stack-carrying gate {name}: the handed stack `{}` is no declared integer", o.basis.text),
                    );
                    return None;
                }
            }
        }
        _ => None,
    };
    let fname = format!("gabbro_kind_{}", k.s.kind.zaehler);
    k.s.kind.zaehler += 1;
    let handed = param.as_ref().map(|p| p.0.clone());
    k.kind.fn_von.insert(region.span, (fname.clone(), handed));
    let mit_arg = param.is_some();
    let modul = k.modul.clone();
    k.s.kind.aufgaben.push(Aufgabe { name: fname.clone(), region, param, modul });
    Some(vorlage(k.s.ziel, tor.template, tor.ret_reg, &st.reg, &fname, mit_arg))
}

fn kurzname_tor(r: &Ruf) -> String {
    r.path().map(kurzname).unwrap_or_else(|| "?".to_string())
}

/// `child { … }` im Vater: dieselbe Funktion rufen (der Tor-Vertrag schließt den Eintritt
/// hier aus), danach `unreachable` — der Prüfer hält, dass die Region nie zurückkehrt.
pub(super) fn kind_stmt(k: &mut Koerper, b: &Block) {
    let (fname, handed) = match k.kind.fn_von.get(&b.span).cloned() {
        Some(x) => x,
        None => {
            weigere(
                k.s,
                "Y103",
                b.span,
                "child region with no stack-gate call lowered before it".to_string(),
            );
            return;
        }
    };
    let arg = match handed {
        Some(n) => {
            let bi = match k.suche(&n) {
                Some(x) => x,
                None => return,
            };
            let v = k.tmp();
            k.zeile(&format!("{v} = load {}, ptr {}, align {}", bi.ll.text(), bi.ptr, nat_align(&bi.ll)));
            format!("{} noundef {v}", bi.ll.text())
        }
        None => String::new(),
    };
    k.zeile(&format!("call void {}({arg})", gname(&fname)));
    k.zeile("unreachable");
    k.beendet = true;
}

/// Alle aufgelaufenen Regionen als Funktionen schreiben (nach der Funktion, die sie rief).
pub(super) fn abarbeiten(s: &mut Senke) {
    while !s.kind.aufgaben.is_empty() {
        let a = s.kind.aufgaben.remove(0);
        let (params, namen, formen): (Vec<(LlTyp, Zeichen)>, Vec<String>, Vec<TypExpr>) = match &a.param {
            Some((n, ll, z, f)) => (vec![(ll.clone(), *z)], vec![n.clone()], vec![f.clone()]),
            None => (vec![], vec![], vec![]),
        };
        let sig = FnSig {
            params: params.clone(),
            ret: None,
            ret_form: None,
            extern_: false,
            geist_param: vec![false; params.len()],
            geist_rueck: false,
            eigen_param: vec![false; params.len()],
            or_nutz: None,
            vertrag_requires: Vec::new(),
            vertrag_ensures: Vec::new(),
        };
        s.fns.insert(a.name.clone(), sig);
        s.emitnamen.insert(a.name.clone(), a.name.clone());
        emit_impl(s, &a.name, &a.region, &params, &namen, &formen, &a.modul);
        s.kind.benutzt.push(a.name);
    }
}

/// `@llvm.used`: die Funktionen, die nur der Inline-Assembler beim Namen ruft, bleiben stehen.
pub(super) fn benutzt_text(s: &Senke) -> String {
    if s.kind.benutzt.is_empty() {
        return String::new();
    }
    let n = s.kind.benutzt.len();
    let elem: Vec<String> = s.kind.benutzt.iter().map(|f| format!("ptr {}", gname(f))).collect();
    format!("@llvm.used = appending global [{n} x ptr] [{}], section \"llvm.metadata\"\n", elem.join(", "))
}
