//! **`entry` für LLVM: vom Gerät gerufene Funktionen mit festem Registervertrag.**
//!
//! Ein `entry` ist keine Funktion, die ein Gabbro-Rumpf ruft: die Hardware betritt sie
//! (`int $0x80`, eine Ausnahme, ein Gerät über die IDT) oder ein fremder Kern ruft sie auf
//! seinem Unterbrechungsweg (`via irq`). Was der Erzeuger daraus schreibt, ist nach Form
//! getrennt, und was er NICHT schreiben kann, wird beim Namen verweigert (`Y102`).
//!
//! ## `x86_64`, ein Vektor oder ein betretener Eintritt (`entry N [vector V] [via idt]`)
//!
//! Der Stub (Modul-Assembler, ein Kopf je Eintritt plus ein gemeinsamer Körper je Art):
//!
//! 1. **Alle** Mehrzweckregister auf den Stapel (der Rahmen `eintritt.rs`-seitig unten),
//!    dazu der volle x87/SSE-Zustand (`fxsave`, 512 Bytes, 16 ausgerichtet): vom Vertrag
//!    verlangt `preserves` nur die genannten, aber der übersetzte Verteiler (und jeder Ruf
//!    darunter) darf jedes Register und jedes `xmm` benutzen. Stärker als `preserves`,
//!    nie schwächer; `clobbers` ist die ERLAUBNIS, nicht die Pflicht.
//! 2. `cld` (die Aufrufkonvention verlangt DF = 0), Stapel ausrichten, die erzeugte
//!    C-Hälfte `gabbro_eintritt_N_c(rahmen)` rufen.
//! 3. Wiederherstellen, `iretq`. Die Ausnahmen mit Fehlercode (8, 10–14, 17, 21, 29, 30:
//!    Tatsache der Architektur) bekommen den **Zwillings-Stub**, der den Code vor `iretq`
//!    vom Stapel nimmt (ein einfacher Stub würde ihn als Rücksprungadresse nehmen).
//!
//! Die C-Hälfte (LLVM-IR, `define void @gabbro_eintritt_N_c(ptr)`) lädt die `regs in`
//! aus dem Rahmen in der Ordnung der Deklaration, ruft `dispatch` (ein `u64` je Register,
//! `N561` hält es) und legt die Antwort in den Rahmenplatz des `regs out`-Registers: das
//! findet der Unterbrochene nach `iretq` dort. Jedes andere Register kommt unverändert zurück.
//!
//! **Die Vektortabelle** (`@gabbro_eintritt_vektoren : [256 x ptr]`, `@gabbro_eintritt_ist
//! : [256 x i8]`): Stub-Adresse und IST-Nummer je deklariertem Vektor, null sonst. Sie ist
//! KEINE IDT: Segmentselektor, Privilegstufe und Gattertyp sind Tatsachen der Umgebung (die
//! GDT und der Start gehören dem Programm), und sie zu erfinden hieße, eine Zusage zu
//! machen, die keine Klausel trägt. Wer die IDT baut, liest diese Tabelle.
//!
//! **Zustand, den dieser Erzeuger NICHT zusagt:**
//! * `stack S per cpu` / `ist n`: der Stub läuft auf dem Stapel, den die Hardware gibt (TSS,
//!   IST-Eintrag der IDT, beides Sache dessen, der sie baut); er schaltet nicht um. Der
//!   Platzbedarf des Rahmens (15 Register, 512 Bytes SSE, Ausrichtung) steht in keiner Zahl
//!   des Programms.
//! * Das Quittieren eines Geräts (LAPIC-EOI): keine Sprachform kennt die Adresse; es ist
//!   Logik des Verteilers (über seine `device`-Register), nicht des Stubs.
//! * Die rote Zone: ein Programm mit einem `entry` trägt `noredzone` an jeder Funktion
//!   (ein Unterbrechungsrahmen auf demselben Stapel zerstörte sonst die Zellen eines
//!   Blattbefehls). Das ist die einzige Wirkung auf nicht-Eintritts-Code.
//!
//! ## `via irq` (der Unterbrechungsweg eines fremden Kerns)
//!
//! Der Kern ruft einen gewöhnlichen C-Funktionskopf (`gabbro_eintritt_N`): die Hardware ist
//! seine Sache, kein Rahmen kommt an. Der Erzeuger schreibt `define void @gabbro_eintritt_N()`,
//! die den Verteiler ruft. Verlangt: keine `regs in/out`, und `preserves` nennt nur
//! Register, die der Funktionskopf nach der System-V-Konvention behält (`rbx rbp r12–r15`).
//!
//! ## Was verweigert bleibt (`Y102`, je Fall mit seinem Satz)
//! * jede andere Architektur als das Ziel (und `aarch64`: Ausnahmetabelle `VBAR_EL1`,
//!   Rahmen und `eret` sind nicht modelliert);
//! * Register ohne Rahmenplatz (`rsp_user`, Segment- und Steuerregister), mehrere `regs out`,
//!   ein Verteiler, dessen Kopf nicht ein `u64` je Eintrittsregister nimmt;
//! * ein nicht konstanter Vektor, ein zweiter Eintritt auf demselben Vektor, ein `via`-Wort
//!   außer `idt`/`irq`, ein `ist` außerhalb 1–7.

use super::*;

/// Rahmenplatz (Byte-Versatz ab Rahmenanfang) je Register, wie der Stub sie ablegt:
/// r15 zuletzt, rax zuerst gepusht, dann der Hardware-Rahmen.
fn rahmenplatz(reg: &str) -> Option<u32> {
    const ORDNUNG: [&str; 15] = [
        "r15", "r14", "r13", "r12", "r11", "r10", "r9", "r8", "rbp", "rdi", "rsi", "rdx", "rcx", "rbx", "rax",
    ];
    ORDNUNG.iter().position(|r| *r == reg).map(|i| 8 * i as u32)
}

/// Ausnahmen, bei denen die CPU einen Fehlercode zwischen `rip` und den Registern ablegt.
fn hat_fehlercode(vektor: u64) -> bool {
    matches!(vektor, 8 | 10..=14 | 17 | 21 | 29 | 30)
}

/// Register, die ein C-Funktionskopf (System V, x86_64) behält.
fn ist_aufrufergesichert(reg: &str) -> bool {
    matches!(reg, "rbx" | "rbp" | "r12" | "r13" | "r14" | "r15")
}

/// Ein angenommener Eintritt, bis die Signatur des Verteilers bekannt ist (`emittiere`).
pub(super) struct Plan {
    name: String,
    modul: String,
    span: Span,
    vektor: Option<u64>,
    ist: u64,
    /// `via irq`: Funktionskopf statt Stub.
    ueber_irq: bool,
    regs_in: Vec<String>,
    regs_out: Vec<String>,
    dispatch: Pfad,
}

/// Eintritt aufnehmen (Durchgang 2). Verweigert beim Namen, was nicht gesenkt wird.
pub(super) fn sammle(s: &mut Senke, e: &EntryDecl, modul: &str, span: Span) {
    let name = e.name.text.clone();
    let tot = |s: &mut Senke, was: String| {
        weigere(s, "Y102", span, was);
        s.tote_items.insert(name.clone());
    };
    if e.arch.text != s.ziel.name {
        let w = if s.ziel.name == "aarch64" {
            format!(
                "entry {name} for arch {}: the {} build has no entry lowering (exception vector \
                 table, frame and `eret` are not modelled)",
                e.arch.text, s.ziel.name
            )
        } else {
            format!("entry {name} is declared for arch {}, this build is {}", e.arch.text, s.ziel.name)
        };
        return tot(s, w);
    }
    if s.ziel.name != "x86_64" {
        return tot(s, format!("entry {name}: no entry lowering for {}", s.ziel.name));
    }
    let via = e.via.as_ref().map(|v| v.text.as_str());
    let ueber_irq = match via {
        None | Some("idt") => false,
        Some("irq") => true,
        Some(w) => return tot(s, format!("entry {name} via `{w}`: no lowering for that path")),
    };
    let mut regs_in = Vec::new();
    for (_, reg) in &e.regs_in {
        regs_in.push(reg.text.clone());
    }
    let regs_out: Vec<String> = e.regs_out.iter().map(|(_, r)| r.text.clone()).collect();
    if regs_out.len() > 1 {
        return tot(s, format!("entry {name} with {} `regs out` registers: the dispatch answers one value", regs_out.len()));
    }
    if ueber_irq {
        if !regs_in.is_empty() || !regs_out.is_empty() {
            return tot(s, format!("entry {name} via irq with registers: a foreign kernel's interrupt path hands no frame"));
        }
        if let Some(r) = e.preserves.iter().find(|r| !ist_aufrufergesichert(&r.text)) {
            return tot(
                s,
                format!("entry {name} via irq preserves `{}`, which a C-ABI function head does not keep", r.text),
            );
        }
    } else {
        for r in regs_in.iter().chain(regs_out.iter()) {
            if rahmenplatz(r).is_none() {
                return tot(s, format!("entry {name}: register `{r}` has no slot in the saved frame"));
            }
        }
        for r in &e.preserves {
            if rahmenplatz(&r.text).is_none() && r.text != "rsp" && !r.text.ends_with("_user") {
                return tot(s, format!("entry {name} preserves `{}`: no such general register", r.text));
            }
        }
    }
    let vektor = match &e.vektor {
        None => None,
        Some(_) if ueber_irq => {
            return tot(s, format!("entry {name} via irq names a vector: the foreign kernel owns the table"));
        }
        Some(x) => match konst_u64(s, x) {
            Some(v) if v < 256 => Some(v),
            _ => return tot(s, format!("entry {name} with a non-constant or out-of-range vector")),
        },
    };
    let ist = match &e.ist {
        None => 0,
        Some(x) => match konst_u64(s, x) {
            Some(v) if (1..=7).contains(&v) => v,
            _ => return tot(s, format!("entry {name} with an `ist` outside 1..7")),
        },
    };
    if let Some(v) = vektor {
        if let Some(anderer) = s.eintritte.iter().find(|p| p.vektor == Some(v)) {
            let w = format!("entry {name} on vector {v}, which entry {} already takes", anderer.name);
            return tot(s, w);
        }
    }
    s.eintritte.push(Plan {
        name,
        modul: modul.to_string(),
        span,
        vektor,
        ist,
        ueber_irq,
        regs_in,
        regs_out,
        dispatch: e.dispatch.clone(),
    });
}

fn modul_asm(aus: &mut String, zeile: &str) {
    let _ = writeln!(aus, "module asm \"{}\"", zeile.replace('\\', "\\5C").replace('"', "\\22"));
}

/// Der gemeinsame Körper: alles sichern, C-Hälfte rufen (Adresse in `rax`), wiederherstellen,
/// `iretq`. Mit `fc`: der Zwilling, der den Fehlercode vor `iretq` abwirft.
fn gemeinsam(aus: &mut String, fc: bool) {
    let l = if fc { "gabbro_eintritt_gemeinsam_fc" } else { "gabbro_eintritt_gemeinsam" };
    modul_asm(aus, ".text");
    modul_asm(aus, &format!(".globl {l}"));
    modul_asm(aus, &format!("{l}:"));
    for r in ["rbx", "rcx", "rdx", "rsi", "rdi", "rbp", "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"] {
        modul_asm(aus, &format!("\tpushq %{r}"));
    }
    for z in [
        "\tmovq %rsp, %rbx",
        "\tsubq $512, %rsp",
        "\tandq $-16, %rsp",
        "\tfxsave (%rsp)",
        "\tmovq %rbx, %rdi",
        "\tcld",
        "\tcall *%rax",
        "\tfxrstor (%rsp)",
        "\tmovq %rbx, %rsp",
    ] {
        modul_asm(aus, z);
    }
    for r in ["r15", "r14", "r13", "r12", "r11", "r10", "r9", "r8", "rbp", "rdi", "rsi", "rdx", "rcx", "rbx", "rax"] {
        modul_asm(aus, &format!("\tpopq %{r}"));
    }
    if fc {
        modul_asm(aus, "\taddq $8, %rsp");
    }
    modul_asm(aus, "\tiretq");
}

/// Alle aufgenommenen Eintritte schreiben (nach den Funktionen: die Signatur des Verteilers
/// steht dann fest). Rückgabe: der Text für Kopf/Hilfsteil.
pub(super) fn emittiere(s: &mut Senke) {
    if s.eintritte.is_empty() {
        return;
    }
    let plaene = std::mem::take(&mut s.eintritte);
    let mut text = String::new();
    let mut tab: BTreeMap<u64, (String, u64)> = BTreeMap::new();
    let (mut braucht_plain, mut braucht_fc) = (false, false);
    let mut gesenkt = Vec::new();
    for p in &plaene {
        s.modul = p.modul.clone();
        let (emit, sig) = match loese_fn(s, &p.modul, &p.dispatch) {
            Some(x) => x,
            None => {
                weigere(s, "Y102", p.span, format!("entry {}: its dispatch `{}` is no function of this unit", p.name, p.dispatch.text()));
                continue;
            }
        };
        // Der Kopf: ein `u64` je Eintrittsregister, die Antwort ein Wort (oder keine).
        let nur_u64 = sig.params.len() == p.regs_in.len()
            && sig.params.iter().all(|(t, _)| *t == LlTyp::Int(64))
            && !sig.geist_param.iter().any(|g| *g);
        let antwort_ok = match (&sig.ret, p.regs_out.len()) {
            (None, 0) => true,
            (Some((LlTyp::Int(w), _)), 1) => *w <= 64,
            (Some((LlTyp::Void, _)), 0) => true,
            _ => false,
        };
        if !nur_u64 || !antwort_ok || sig.or_nutz.is_some() || sig.geist_rueck {
            weigere(
                s,
                "Y102",
                p.span,
                format!(
                    "entry {}: the dispatch head must take one u64 per `regs in` register and answer one \
                     integer for one `regs out` register (or nothing for none)",
                    p.name
                ),
            );
            continue;
        }
        if p.ueber_irq {
            let _ = writeln!(text, "define void @\"gabbro_eintritt_{}\"() {{", p.name);
            let _ = writeln!(text, "eintritt:");
            let _ = writeln!(text, "  call void {}()", gname(&emit));
            let _ = writeln!(text, "  ret void");
            let _ = writeln!(text, "}}");
            s.kind.benutzt.push(format!("gabbro_eintritt_{}", p.name));
            gesenkt.push(p.name.clone());
            continue;
        }
        // Die C-Hälfte: Rahmen lesen, Verteiler rufen, Antwort in den Rahmen schreiben.
        let _ = writeln!(text, "define void @\"gabbro_eintritt_{}_c\"(ptr noundef %r) {{", p.name);
        let _ = writeln!(text, "eintritt:");
        let mut args = Vec::new();
        for (i, reg) in p.regs_in.iter().enumerate() {
            let off = rahmenplatz(reg).unwrap_or(0);
            let _ = writeln!(text, "  %p{i} = getelementptr inbounds i8, ptr %r, i64 {off}");
            let _ = writeln!(text, "  %v{i} = load i64, ptr %p{i}, align 8");
            args.push(format!("i64 noundef %v{i}"));
        }
        match sig.ret.clone() {
            Some((LlTyp::Int(w), z)) if p.regs_out.len() == 1 => {
                let off = rahmenplatz(&p.regs_out[0]).unwrap_or(0);
                let _ = writeln!(text, "  %a = call i{w} {}({})", gname(&emit), args.join(", "));
                let wert = if w == 64 {
                    "%a".to_string()
                } else {
                    let op = if z == Zeichen::S { "sext" } else { "zext" };
                    let _ = writeln!(text, "  %a64 = {op} i{w} %a to i64");
                    "%a64".to_string()
                };
                let _ = writeln!(text, "  %pa = getelementptr inbounds i8, ptr %r, i64 {off}");
                let _ = writeln!(text, "  store i64 {wert}, ptr %pa, align 8");
            }
            _ => {
                let _ = writeln!(text, "  call void {}({})", gname(&emit), args.join(", "));
            }
        }
        let _ = writeln!(text, "  ret void");
        let _ = writeln!(text, "}}");
        s.kind.benutzt.push(format!("gabbro_eintritt_{}_c", p.name));
        let fc = p.vektor.is_some_and(hat_fehlercode);
        if fc {
            braucht_fc = true;
        } else {
            braucht_plain = true;
        }
        // Der Kopf des Stubs: rax sichern, die C-Hälfte in rax, in den gemeinsamen Körper.
        modul_asm(&mut text, ".text");
        modul_asm(&mut text, &format!(".globl gabbro_eintritt_{}", p.name));
        modul_asm(&mut text, &format!("gabbro_eintritt_{}:", p.name));
        modul_asm(&mut text, "\tpushq %rax");
        modul_asm(&mut text, &format!("\tleaq gabbro_eintritt_{}_c(%rip), %rax", p.name));
        modul_asm(&mut text, if fc { "\tjmp gabbro_eintritt_gemeinsam_fc" } else { "\tjmp gabbro_eintritt_gemeinsam" });
        let _ = writeln!(text, "declare void @\"gabbro_eintritt_{}\"()", p.name);
        if let Some(v) = p.vektor {
            tab.insert(v, (p.name.clone(), p.ist));
        }
        gesenkt.push(p.name.clone());
    }
    if braucht_plain {
        gemeinsam(&mut text, false);
    }
    if braucht_fc {
        gemeinsam(&mut text, true);
    }
    if !tab.is_empty() {
        let mut ptrs = Vec::new();
        let mut ists = Vec::new();
        for v in 0..256u64 {
            match tab.get(&v) {
                Some((n, ist)) => {
                    ptrs.push(format!("ptr @\"gabbro_eintritt_{n}\""));
                    ists.push(format!("i8 {ist}"));
                }
                None => {
                    ptrs.push("ptr null".to_string());
                    ists.push("i8 0".to_string());
                }
            }
        }
        let _ = writeln!(text, "@\"gabbro_eintritt_vektoren\" = constant [256 x ptr] [{}], align 8", ptrs.join(", "));
        let _ = writeln!(text, "@\"gabbro_eintritt_ist\" = constant [256 x i8] [{}], align 1", ists.join(", "));
    }
    s.mit_eintritt = !gesenkt.is_empty();
    s.helfer.push_str(&text);
}

/// Ein Programm mit Eintritten übersetzt jede Funktion ohne rote Zone: ein Unterbrechungsrahmen
/// auf demselben Stapel zerstörte sonst die Zellen eines Blattbefehls. `define … {` → `define … noredzone {`.
pub(super) fn ohne_rote_zone(ir: &str) -> String {
    let mut aus = String::with_capacity(ir.len() + 64);
    for z in ir.split_inclusive('\n') {
        let k = z.trim_end();
        if z.starts_with("define ") && k.ends_with(" {") && !k.contains(" noredzone ") {
            let _ = writeln!(aus, "{} noredzone {{", &k[..k.len() - 2]);
        } else {
            aus.push_str(z);
        }
    }
    aus
}
