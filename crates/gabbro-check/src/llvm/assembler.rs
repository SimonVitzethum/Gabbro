//! **`asm`-Rümpfe (`fn f(…) arch A = asm { … }`) für LLVM: eine Funktion, deren Körper EIN
//! `call asm sideeffect` ist.**
//!
//! Der Rumpf ist ein versiegeltes Loch: Gabbro liest den Befehlstext nicht (`ast::AsmRumpf`),
//! und was hier steht, ist Annahme und keine Aussage. Der Erzeuger übersetzt nur den RAHMEN,
//! den die Quelle erklärt, und nichts am Text:
//!
//! * **Nur für die Maschine, die der Rumpf nennt.** `arch x86_64` wird für das Ziel `x86_64`
//!   geschrieben und für `aarch64` beim Namen verweigert (`Y102`), und umgekehrt: derselbe
//!   Text tut auf der anderen Maschine etwas anderes oder ist kein Befehl.
//! * **Operanden:** `in { n : "c" }` und `out { result : "=c" }` werden zu LLVM-Eingängen und
//!   -Ausgang mit derselben Zwangsfolge; `%[n]` im Text wird zu `$k` (Ausgang zuerst, wie
//!   LLVM zählt), ein literales `$` zu `$$`, ein einzelnes `%` bleibt (`%eax` ist AT&T-Text).
//!   Die Breite des Operanden ist der Typ des Parameters: `u8` mit `"a"` ist `%al`, `u16` mit
//!   `"d"` ist `%dx`, wie beim C-Erzeuger (`emit.rs`, `asmtext`).
//! * **`clobbers { memory, rax, … }`** werden zu `~{memory}`, `~{rax}`, … (`cc` zu `~{cc}`).
//!   `sideeffect` steht IMMER da: wer den Text nicht liest, darf ihn nicht für entbehrlich halten.
//! * **Verweigert (`Y102`, je Fall mit seinem Satz):** ein Parameter, der kein gesenkter
//!   Skalar ist, ein Operand, den ein Geisterparameter trägt, ein Zwang mit `+`, `&`, `%`, `m`,
//!   Ziffer (Bindung an einen anderen Operanden, Speicheroperand: LLVM zählt sie anders als
//!   GCC, und ein stilles Falschzählen wäre eine Mischung), ein `out`, das nicht `result` heißt,
//!   ein `-> never` mit Ausgang (`N321` hält es im Prüfer), ein Ergebnis ohne `out { result }`.
//!
//! **Was geprüft wird und was nicht:** `llc -filetype=obj` nimmt den Text an und `objdump -d`
//! zeigt die Befehle. Ob der Text auf der Maschine tut, was die Annahme sagt, bleibt die
//! Annahme (`zeugnis` zählt die Zeilen); Befehle wie `outb`, `invlpg`, `hlt` laufen im
//! Benutzermodus nicht, und dieser Erzeuger behauptet nichts über ihre Wirkung.

use super::*;

/// Die fertige Funktion (bis auf den Emitnamen, der erst nach der Sammlung feststeht).
#[derive(Clone)]
pub(super) struct Def {
    params: Vec<LlTyp>,
    /// `None`: `void` (auch `-> never`).
    ret: Option<LlTyp>,
    nie: bool,
    /// Vorlage, schon als IR-Zeichenkette maskiert.
    vorlage: String,
    zwang: String,
    /// Parameterplätze der Eingänge, in der Ordnung der Zwangsfolge.
    eingaenge: Vec<usize>,
}

fn ir_text(t: &str) -> String {
    let mut a = String::with_capacity(t.len());
    for c in t.chars() {
        match c {
            '\\' => a.push_str("\\5C"),
            '"' => a.push_str("\\22"),
            '\n' => a.push_str("\\0A"),
            '\t' => a.push_str("\\09"),
            c if (c as u32) < 0x20 || (c as u32) > 0x7e => {
                let mut b = [0u8; 4];
                for x in c.encode_utf8(&mut b).bytes() {
                    let _ = write!(a, "\\{x:02X}");
                }
            }
            c => a.push(c),
        }
    }
    a
}

/// Ein Zwang in LLVM-Form. LLVM kennt die GCC-Einzelbuchstaben der festen x86-Register nicht
/// (`a`, `b`, `c`, `d`, `S`, `D`: das übersetzt sonst `clang`), also werden sie zu `{ax}` …;
/// die Breite des Registers wählt der Typ des Operanden. Klassenbuchstaben (`r`, `q`, `i`, `n`,
/// auf aarch64 `r`, `w`, `i`) gehen durch. Alles andere (mehrere Buchstaben, Speicher,
/// Bindung an einen anderen Operanden) hat keine 1:1-Form: `None`.
fn zwang_ok(c: &str, ausgang: bool, x86: bool) -> Option<String> {
    let c = c.trim();
    let rumpf = if ausgang { c.strip_prefix('=')? } else { c };
    if rumpf.chars().count() != 1 {
        return None;
    }
    let b = rumpf.chars().next()?;
    let l = match (x86, b) {
        (true, 'a') => "{ax}",
        (true, 'b') => "{bx}",
        (true, 'c') => "{cx}",
        (true, 'd') => "{dx}",
        (true, 'S') => "{si}",
        (true, 'D') => "{di}",
        (true, 'r' | 'q' | 'i' | 'n') => return Some(format!("{}{b}", if ausgang { "=" } else { "" })),
        (false, 'r' | 'w' | 'i' | 'n') => return Some(format!("{}{b}", if ausgang { "=" } else { "" })),
        _ => return None,
    };
    Some(format!("{}{l}", if ausgang { "=" } else { "" }))
}

/// `%[n]` → `$k`, `$` → `$$`; `%` sonst bleibt (AT&T-Register). `None`: ein unbekannter Operand.
fn vorlage(zeilen: &[String], nummer: &dyn Fn(&str) -> Option<usize>) -> Result<String, String> {
    let mut aus = String::new();
    for (i, z) in zeilen.iter().enumerate() {
        if i > 0 {
            aus.push('\n');
        }
        let mut cs = z.chars().peekable();
        while let Some(c) = cs.next() {
            match c {
                '$' => aus.push_str("$$"),
                '%' if cs.peek() == Some(&'[') => {
                    cs.next();
                    let mut n = String::new();
                    let mut zu = false;
                    for d in cs.by_ref() {
                        if d == ']' {
                            zu = true;
                            break;
                        }
                        n.push(d);
                    }
                    if !zu {
                        return Err("an operand `%[` with no closing `]`".to_string());
                    }
                    match nummer(&n) {
                        Some(k) => {
                            let _ = write!(aus, "${k}");
                        }
                        None => return Err(format!("operand `%[{n}]` names no `in`/`out` operand")),
                    }
                }
                c => aus.push(c),
            }
        }
    }
    Ok(aus)
}

/// Durchgang 2: den `asm`-Rumpf einer Funktion aufnehmen (oder beim Namen verweigern).
pub(super) fn sammle(s: &mut Senke, f: &FnDecl, a: &AsmRumpf, voll: &str, span: Span) {
    let kurz = f.name.text.clone();
    let tot = |s: &mut Senke, was: String| {
        weigere(s, "Y102", span, was);
        s.tote_items.insert(kurz.clone());
        s.tote_items.insert(voll.to_string());
    };
    match &f.arch {
        Some(arch) if arch.text == s.ziel.name => {}
        Some(arch) => {
            // Ein Rumpf für die ANDERE Maschine: still vorgemerkt. Hat die Einheit unter
            // demselben Namen einen Rumpf für dieses Ziel (zwei Erklärungen, je eine `arch`),
            // gilt der; sonst verweigert `fremde_pruefen` beim Namen.
            s.fremde_asm.entry(voll.to_string()).or_insert((kurz, arch.text.clone(), span));
            return;
        }
        None => return tot(s, format!("assembly body of {kurz} names no arch")),
    }
    let x86 = s.ziel.name == "x86_64";
    let nie = matches!(&f.ergebnis, Some(TypExpr::Never(_)));
    let alt = s.eng_modus;
    s.eng_modus = false;
    let mut params: Vec<LlTyp> = Vec::new();
    let mut zeiger: Vec<(String, Option<usize>)> = Vec::new(); // (Name, gesenkter Platz)
    let mut sig_params: Vec<(LlTyp, Zeichen)> = Vec::new();
    let mut geist = Vec::new();
    for p in &f.parameter {
        if ist_geist(s, &p.typ) {
            geist.push(true);
            zeiger.push((p.name.text.clone(), None));
            continue;
        }
        geist.push(false);
        match senke_typ(s, &p.typ) {
            Some((ll, z)) if ll.ist_int() && ll != LlTyp::Int(1) || ll == LlTyp::Ptr => {
                zeiger.push((p.name.text.clone(), Some(params.len())));
                params.push(ll.clone());
                sig_params.push((ll, z));
            }
            Some(_) => {
                s.eng_modus = alt;
                return tot(s, format!("assembly body of {kurz}: parameter `{}` is no integer or pointer operand", p.name.text));
            }
            None => {
                s.eng_modus = alt;
                s.tote_items.insert(kurz);
                s.tote_items.insert(voll.to_string());
                return;
            }
        }
    }
    let ret = match &f.ergebnis {
        None => None,
        Some(_) if nie => None,
        Some(t) => match senke_typ(s, t) {
            Some((ll, z)) if ll.ist_int() && ll != LlTyp::Int(1) => Some((ll, z)),
            Some((LlTyp::Void, _)) => None,
            Some(_) => {
                s.eng_modus = alt;
                return tot(s, format!("assembly body of {kurz}: the result is no integer operand"));
            }
            None => {
                s.eng_modus = alt;
                s.tote_items.insert(kurz);
                s.tote_items.insert(voll.to_string());
                return;
            }
        },
    };
    s.eng_modus = alt;
    if f.fehler.is_some() {
        return tot(s, format!("assembly body of {kurz} with an error channel: the text cannot answer a reason"));
    }
    // Ausgang.
    if nie && !a.aus.is_empty() {
        return tot(s, format!("assembly body of {kurz}: `-> never` with an `out` operand has no result slot (N321)"));
    }
    if a.aus.len() > 1 || a.aus.iter().any(|(n, _)| n.text != "result") {
        return tot(s, format!("assembly body of {kurz}: the only `out` operand is `result`"));
    }
    if ret.is_some() != !a.aus.is_empty() {
        return tot(s, format!("assembly body of {kurz}: the result type and `out {{ result }}` must come together"));
    }
    let mut zwang: Vec<String> = Vec::new();
    for (n, c) in &a.aus {
        match zwang_ok(&c.text, true, x86) {
            Some(z) => zwang.push(z),
            None => {
                return tot(s, format!("assembly body of {kurz}: constraint `{}` of `out {}` has no 1:1 LLVM form", c.text, n.text));
            }
        }
    }
    let mut eingaenge = Vec::new();
    let mut namen: Vec<String> = a.aus.iter().map(|(n, _)| n.text.clone()).collect();
    for (n, c) in &a.ein {
        let platz = zeiger.iter().find(|(x, _)| *x == n.text).and_then(|(_, p)| *p);
        let Some(platz) = platz else {
            return tot(s, format!("assembly body of {kurz}: `in {}` names no lowered parameter", n.text));
        };
        match zwang_ok(&c.text, false, x86) {
            Some(z) => zwang.push(z),
            None => {
                return tot(s, format!("assembly body of {kurz}: constraint `{}` of `in {}` has no 1:1 LLVM form", c.text, n.text));
            }
        }
        eingaenge.push(platz);
        namen.push(n.text.clone());
    }
    for z in &a.zerstoert {
        let t = z.text.as_str();
        zwang.push(match t {
            "memory" => "~{memory}".to_string(),
            "cc" => "~{cc}".to_string(),
            r => format!("~{{{r}}}"),
        });
    }
    let zeilen: Vec<String> = a.zeilen.iter().map(|z| z.text.clone()).collect();
    let nummer = |n: &str| namen.iter().position(|x| x == n);
    let text = match vorlage(&zeilen, &nummer) {
        Ok(t) => t,
        Err(e) => return tot(s, format!("assembly body of {kurz}: {e}")),
    };
    let def = Def {
        params,
        ret: ret.as_ref().map(|(t, _)| t.clone()),
        nie,
        vorlage: ir_text(&text),
        zwang: ir_text(&zwang.join(",")),
        eingaenge,
    };
    let sig = FnSig {
        params: sig_params,
        ret: ret.clone(),
        ret_form: f.ergebnis.clone(),
        extern_: false,
        geist_param: geist,
        geist_rueck: false,
        or_nutz: None,
        eigen_param: Vec::new(),
        vertrag_requires: f.requires.clone(),
        vertrag_ensures: f.ensures.clone(),
    };
    trage_fn_ein(s, voll, &kurz, sig);
    s.asm_defs.insert(voll.to_string(), def);
    s.plaene.insert(voll.to_string(), FnPlan::Fertig { modul: s.modul.clone() });
}

/// Die Funktion schreiben (Durchgang der Emission, nach der Vergabe der Emitnamen).
pub(super) fn emittiere(s: &mut Senke, voll: &str) -> bool {
    let Some(d) = s.asm_defs.get(voll).cloned() else {
        return false;
    };
    let emit = s.emitnamen.get(voll).cloned().unwrap_or_else(|| voll.to_string());
    let ret_text = d.ret.as_ref().map(|t| t.text()).unwrap_or_else(|| "void".to_string());
    let ps: Vec<String> = d.params.iter().enumerate().map(|(i, t)| param_text_mit(t, false, i)).collect();
    let _ = writeln!(s.rumpf, "define {ret_text} {}({}) {{", gname(&emit), ps.join(", "));
    let _ = writeln!(s.rumpf, "eintritt:");
    let ops: Vec<String> = d.eingaenge.iter().map(|&i| format!("{} %p{i}", d.params[i].text())).collect();
    match &d.ret {
        Some(t) => {
            let _ = writeln!(
                s.rumpf,
                "  %r = call {} asm sideeffect \"{}\", \"{}\"({})",
                t.text(),
                d.vorlage,
                d.zwang,
                ops.join(", ")
            );
            let _ = writeln!(s.rumpf, "  ret {} %r", t.text());
        }
        None => {
            let _ = writeln!(s.rumpf, "  call void asm sideeffect \"{}\", \"{}\"({})", d.vorlage, d.zwang, ops.join(", "));
            if d.nie {
                // Der Text ist ungeprüft; kehrt er zurück (`hlt`), ist es DOCH ein Halt: der Prüfer
                // liest ein `-> never` als Stopp, der nie weiterläuft (wie `for (;;)` in C).
                let _ = writeln!(s.rumpf, "  br label %halt");
                let _ = writeln!(s.rumpf, "halt:");
                let _ = writeln!(s.rumpf, "  br label %halt");
            } else {
                let _ = writeln!(s.rumpf, "  ret void");
            }
        }
    }
    let _ = writeln!(s.rumpf, "}}");
    s.beleg_funktionen.push((
        emit,
        d.params.iter().map(|t| t.text()).collect(),
        ret_text,
        "asm".to_string(),
    ));
    true
}

/// Nach der Sammlung: ein `asm`-Rumpf, der nur für die andere Maschine da ist, wird beim Namen
/// verweigert (derselbe Text tut auf dieser Maschine etwas anderes oder ist kein Befehl).
pub(super) fn fremde_pruefen(s: &mut Senke) {
    let fremde = std::mem::take(&mut s.fremde_asm);
    for (voll, (kurz, arch, span)) in fremde {
        if s.asm_defs.contains_key(&voll) {
            continue;
        }
        weigere(
            s,
            "Y102",
            span,
            format!(
                "assembly body of {kurz} is written for arch {arch} only, this build is {}: the same text \
                 does something else, or is no instruction, on this machine (a second declaration of \
                 `{kurz}` with `arch {}` would carry it)",
                s.ziel.name, s.ziel.name
            ),
        );
        s.tote_items.insert(kurz);
        s.tote_items.insert(voll);
    }
}
