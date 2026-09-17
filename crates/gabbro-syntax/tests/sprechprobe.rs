//! **Sprechproben in beide Richtungen** -- die Regel, die dieser Ordner an jeden Pruefer legt:
//! *ein Pruefer, der nicht fehlschlagen kann, ist kein Pruefer* (`pruefe-syntax.sh`).
//!
//! Jede Probe steht paarweise: eine **saubere** Form muss durchkommen, eine **vergiftete** muss
//! mit **benanntem** Code fallen. Der Code steht mit im Test, damit eine Absage nicht heimlich
//! ihre Bedeutung wechselt.

use gabbro_syntax::diag::Stufe;

fn faellt_nicht(quelle: &str) {
    let (_, absagen) = gabbro_syntax::lies("<probe>", quelle);
    let fehler: Vec<_> = absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .collect();
    assert!(
        fehler.is_empty(),
        "sauber, faellt aber:\n{}\n{}",
        quelle,
        absagen.zeige(quelle)
    );
}

fn faellt_mit(quelle: &str, code: &str) {
    let (_, absagen) = gabbro_syntax::lies("<probe>", quelle);
    let codes: Vec<&str> = absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code)
        .collect();
    assert!(
        codes.contains(&code),
        "erwartet war {code}, gefallen ist {codes:?}\n{quelle}\n{}",
        absagen.zeige(quelle)
    );
}

// -- Die Formen, die es absichtlich nicht gibt -------------------------------------------
// `pruefe-syntax.sh` greift sie im Text ab; hier muss der Uebersetzer sie abweisen.

#[test]
fn verbotene_formen_fallen() {
    faellt_mit("impl fn f() effects { pure } { while (x) { } }", "P035");
    faellt_mit("impl fn f() effects { pure } { for (i) { } }", "P035");
    faellt_mit("impl fn f() effects { pure } { goto ende; }", "P035");
    faellt_mit("impl fn f() effects { pure } { break; }", "P035");
    faellt_mit("impl fn f() effects { pure } { continue; }", "P035");
    // Der Auffangzweig -- die teuerste der vier: eine neue Variante soll brechen.
    faellt_mit(
        "impl fn f() effects { pure } { match k { _ => { } } }",
        "P034",
    );
    // Zuweisung ist kein Ausdruck (E2).
    faellt_mit("impl fn f() effects { pure } { if (x = y) { } }", "P001");
}

#[test]
fn sauberes_kommt_durch() {
    faellt_nicht(
        r#"
module caprock::probe {
    const N : u32 = 8;
    type Idx = u32 in 0 ..< N;
    opaque type Pa = u64;
    tagged type Kind = { Frame(Pa), Endpoint(u32) };
    linear type Parked;
    linear ghost type Held(Lock);

    lock CAPS protects { tabelle, baum } rank 2 masks irqs;
    atomic FERTIG : bool release;
    accumulates hoechststand : u64 merge max;

    spec fn wohlgeformt(c : ptr<normal, r> Raum) -> bool
        effects { pure }
        = forall s in slots of c : c.eintrag[s].benutzt;

    impl fn loeschen(c : ptr<normal, rw> Raum, s : Idx) -> u32
        requires  Held(CAPS), c.eintrag[s].benutzt
        ensures   !c.eintrag[s].benutzt, old(c.zahl) == c.zahl + 1
        maintains wohlgeformt
        effects   { writes c.eintrag, locks CAPS }
        costs     <= 200 ops
        by        induction over descendants of s
    {
        let alt = c.eintrag[s].objekt;
        c.eintrag[s].benutzt = false;
        c.zahl -= 1;
        if c.zahl == 0 {
            match c.eintrag[s].kind {
                Frame(p) => { frei(p); }
                Endpoint(e) => { }
            }
        }
        narrow c.zahl to 1 .. 4096 else { return 0; }
        traverse opfer over descendants of c.eintrag[s] by consuming
            touches consumes c.eintrag, writes c.objekte
        {
            loeschen(c, opfer);
        }
        return 0;
    }
}
"#,
    );
}

// -- Regel fuer Regel -------------------------------------------------------------------

#[test]
fn wortschatzwort_ist_ein_bezeichner() {
    faellt_nicht("impl fn f(zahl : u32) effects { pure } { }");
    // **Turned around on 2026-09-05.** Here stood `faellt_mit(… slot …, "P002")`, and the
    // rule it guarded is the one «K3» measured: `P002` on `node`, `old`, `next`, `progress`,
    // `release`, `stack` and `index` in six of eight excerpts transcribed from Linux
    // `lib/*.c`, every one of them a name the kernel itself wrote. A word of the table is a
    // keyword only where the grammar expects one; at a parameter it is a name.
    faellt_nicht("impl fn f(slot : u32) effects { pure } { }");
    faellt_nicht("impl fn f(node : u32, index : u32, next : u32) effects { pure } { }");
    // Seventeen of the 221 are still not names -- `tests/wortschatz.rs` holds the whole
    // column against the reader; one of each half stands here so this file can say why.
    faellt_mit("impl fn f(Some : u32) effects { pure } { }", "P002");
    faellt_mit("impl fn f(return : u32) effects { pure } { }", "P002");
}

/// **The one token that separates `next runde;` from `next = 0;`** -- see
/// `parse.rs::ist_ortfortsetzung`. Both halves stand here: the keyword form must survive the
/// rule that makes the place form readable.
#[test]
fn anweisungskopf_ist_auch_ein_ort() {
    faellt_nicht(
        "impl fn f(a : u32) effects { pure } \
         { let mut next = a; next = a; next += a; }",
    );
    faellt_nicht(
        "divergent fn g() effects { diverges } \
         { forever runde per_pass bounded 4 ops on_exceeded w effects { pure } \
           { if true { leave runde; } next runde; } }",
    );
}

/// **`old` and `result` are words in a contract and names in a body** -- see
/// `parse.rs::im_vertrag`. Before 2026-09-05 the body form parsed into the CONTRACT meaning
/// and `gabbro pruefe` said `0 errors` over a function returning its own return value.
#[test]
fn vertragswoerter_sind_im_rumpf_namen() {
    faellt_nicht(
        "impl fn f(a : u32) -> u32 ensures result == 1 effects { pure } costs <= 8 ops \
         { let result = a; let old = a; return result; }",
    );
}

#[test]
fn feldname_nach_punkt_darf_ein_wort_sein() {
    // `c.slots[s]` steht so in FRAGMENTE.md -- nach `.` kann kein Schluesselwort stehen,
    // also kann dort auch keins verwechselt werden.
    faellt_nicht("impl fn f(c : ptr<normal, rw> T) effects { writes c } { c.slots[0].used = true; }");
}

#[test]
fn quantorendomaene_ist_geschlossen() {
    faellt_nicht("spec fn p(c : T) -> bool effects { pure } = forall s in slots of c : s.x;");
    faellt_mit(
        "spec fn p(c : T) -> bool effects { pure } = forall s in bloedsinn of c : s.x;",
        "P013",
    );
}

#[test]
fn annahme_ohne_klasse_faellt() {
    faellt_nicht(r#"assume a "die MMU tut, was ihr Modell sagt" falsifier sonde_a;"#);
    faellt_nicht(r#"assume a "qemu64 hat kein x2APIC" unfalsifiable "kein Geraet";"#);
    // Die dritte Klasse -- *nicht gefahren* -- ist die Abwesenheit beider Angaben.
    faellt_mit(r#"assume a "irgendwas";"#, "P029");
}

#[test]
fn schleifenformen() {
    faellt_nicht(
        "impl fn f() effects { pure } { forever s per_pass bounded 4096 ops \
         on_exceeded watchdog effects { reads BEREIT } progress tick { next s; } }",
    );
    // `on_exceeded` ist Pflicht (D11) -- der Ueberlauf wird benannt, nicht gedeutet.
    faellt_mit(
        "impl fn f() effects { pure } { forever per_pass bounded 4096 ops \
         effects { reads BEREIT } { } }",
        "P001",
    );
    // `by` ist Pflicht: jede Schleife nennt ihr Abstiegsmass.
    faellt_mit(
        "impl fn f() effects { pure } { traverse t over slots of c { } }",
        "P001",
    );
}

#[test]
fn uebergang_mit_pfeil_und_ortssuffix() {
    // Die aufgeloeste Mehrdeutigkeit: `A -> B` ist hier ein Uebergang, kein Feldzugriff.
    faellt_nicht(
        "device V at mmio { reg ST : u32 @0x0 class rw \
         transition an { ST: ACK -> ACK | TREIBER } effects { writes ST } }",
    );
    // Und ausserhalb bleibt `->` ein Ortssuffix.
    faellt_nicht("impl fn f(p : ptr<normal, rw> T) effects { writes p } { p->feld = 1; }");
}

#[test]
fn lexik() {
    faellt_nicht("const A : u32 = 0xFF_FF; -- ein Kommentar\nconst B : u32 = 0b1010_1010;");
    faellt_mit("const A : u32 = 0X10;", "L004");
    faellt_mit("const A : u32 = 0b12;", "L003");
    faellt_mit("assume a \"unbeendet\n falsifier s;", "L001");
    faellt_mit("const A : u32 = 1 $ 2;", "L006");
}

// -- Lane 182: source trust (homoglyphs and bidi) --------------------------------------
//
// Gabbro's promise is that a HUMAN reads a body ("written by hand and read by a
// person"); a program that reads differently to a human than to the parser breaks that
// premise (Trojan Source, CVE-2021-42574). Four codes, one per class; the poison probes
// `beispiele/gift/960`-`963` pin the same four over files. The `\u{...}` escapes keep
// the poison OUT of this source file -- a literal U+202E here would trip the very
// guardian (`pruefe-kennungen.py`) these tests pin down.

#[test]
fn quelle_bidi_faellt_ueberall() {
    // In code, in a string, and in a comment: the reordering happens in the editor.
    faellt_mit("const A : u32 = 1\u{202e};", "P060");
    faellt_mit("assume a \"x\u{202e}y\";", "P060");
    faellt_mit("-- ein Kommentar \u{202e}\nconst A : u32 = 1;", "P060");
    faellt_mit("const A : u32 = 1\u{2066};", "P060");
    faellt_mit("const A : u32 = 1\u{200f};", "P060");
}

#[test]
fn quelle_fremde_schrift_und_gemischte_fallen() {
    // One foreign script: outside the allowed set (`P061`).
    faellt_mit("const \u{430} : u32 = 1;", "P061");
    // Two scripts in one run: the homoglyph (`P062`).
    faellt_mit("const p\u{430}ss : u32 = 1;", "P062");
    faellt_mit("const \u{3c3}x : u32 = 1;", "P062");
}

#[test]
fn quelle_unsichtbares_faellt_bom_am_anfang_nicht() {
    faellt_mit("const\u{200b}A : u32 = 1;", "P063");
    faellt_mit("const A : u32 = 1\u{200d};", "P063");
    faellt_mit("const A : u32 = 1;\u{feff}", "P063");
    faellt_nicht("\u{feff}const A : u32 = 1;");
}

#[test]
fn quelle_umlaut_kommentar_und_zahlumgebung_bleiben_sauber() {
    // The documented set (ASCII + ä ö ü ß Ä Ö Ü) still lexes; foreign letters in
    // comments are prose, not names; a letter glued to a number belongs to `L003`/`L006`.
    faellt_nicht("const Gr\u{f6}\u{df}e : u32 = 1;");
    faellt_nicht("-- Gr\u{f6}\u{df}e \u{3c3} \u{2192}\nconst A : u32 = 1;");
    let (_, absagen) = gabbro_syntax::lies("<probe>", "const A : u32 = 0\u{4000};");
    let codes: Vec<&str> = absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code)
        .collect();
    assert!(
        codes.contains(&"L006") && !codes.iter().any(|c| c.starts_with('P')),
        "die Zahlumgebung gehoert L006 allein, gefallen ist {codes:?}"
    );
}

#[test]
fn zahl_passt_in_keinen_typ() {
    faellt_nicht("const A : u64 = 18_446_744_073_709_551_615;");
    faellt_mit(
        "const A : u64 = 999999999999999999999999999999999999999999;",
        "L005",
    );
}

#[test]
fn erholung_zeigt_mehr_als_einen_befund() {
    // Ein Lauf, der beim ersten Befund aufhoert, misst nicht -- er meldet.
    // *The two words here were `slot` and `dma` and have been names since 2026-09-05; the
    // probe needs two out of the seventeen that are not.*
    let quelle = "impl fn f() effects { pure } { let Some = 1; let None = 2; }";
    let (_, absagen) = gabbro_syntax::lies("<probe>", quelle);
    let fehler = absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler && a.code == "P002")
        .count();
    assert_eq!(fehler, 2, "beide Befunde muessen erscheinen:\n{}", absagen.zeige(quelle));
}

// -- The five paper cuts of `PLAN-HARDWARE.md` §49 B3 ------------------------------------
//
// **A poison probe cannot hold any of these**, and that is why they stand here: the corpus
// harness matches CODES, and nothing about these five changes a code. What changed is the
// text under the site -- the shape that was meant, in one line. *A cure that no guardian
// reads is a cure until the next rewrite.*

/// The expected code falls AND its refusal carries the given note.
///
/// **Both halves, or neither is a measurement.** Asserting only the code would pass with the
/// note deleted; asserting only the note would pass with the refusal moved to another rule.
fn faellt_mit_notiz(quelle: &str, code: &str, teil: &str) {
    let (_, absagen) = gabbro_syntax::lies("<probe>", quelle);
    let treffer: Vec<_> = absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler && a.code == code)
        .collect();
    assert!(
        !treffer.is_empty(),
        "expected {code}:\n{quelle}\n{}",
        absagen.zeige(quelle)
    );
    assert!(
        treffer
            .iter()
            .any(|a| a.notizen.iter().any(|n| n.contains(teil))),
        "{code} fell, but no note carries {teil:?}:\n{quelle}\n{}",
        absagen.zeige(quelle)
    );
}

#[test]
fn effects_ohne_klammern_nennt_die_form() {
    // Attempt 3 of 8, the sharpest: the right word in the right place, and `` `{` expected ``
    // as the whole answer.
    faellt_nicht("impl fn f() effects { pure } { }");
    faellt_mit_notiz(
        "impl fn f() effects pure { }",
        "P001",
        "takes a BRACE LIST and not a bare word",
    );
}

#[test]
fn leere_wirkungsliste_nennt_pure() {
    // Attempt 2 of 8, the ambiguous one -- the refusal STAYS, because `pure` says the same
    // thing on purpose. What was the paper cut is that the old text listed nine words and
    // left the reader to work out which of them means "none".
    faellt_mit_notiz(
        "impl fn f() effects { } { }",
        "P014",
        "an EMPTY list is not `no effects`",
    );
}

#[test]
fn fehlender_strichpunkt_nennt_die_regel() {
    // Attempt 5 of 8. `;` expected / `}` found has exactly one meaning wherever it can
    // happen, and the rule fits in a line.
    faellt_mit_notiz(
        "impl fn f() effects { pure } { return 0 }",
        "P001",
        "the LAST statement of a block ends with `;` too",
    );
}

#[test]
fn strichpunkt_nach_block_beschreibt_die_seite() {
    // Attempt 6 of 8. Same code, same rule, same accepted programs -- the text now says what
    // stands on the PAGE (`};`) instead of what the parser sees (a `;` on its own).
    let quelle = "impl fn f() effects { pure } { if x { }; }";
    let (_, absagen) = gabbro_syntax::lies("<probe>", quelle);
    let treffer: Vec<_> = absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler && a.code == "P033")
        .collect();
    assert!(
        treffer.iter().any(|a| a.text.contains("one token too many")),
        "P033 after a block must describe the page:\n{}",
        absagen.zeige(quelle)
    );
    // And the other half of the same code keeps its own wording -- a `;` with no block in
    // front of it IS a semicolon on its own.
    let allein = "impl fn f() effects { pure } { ; }";
    let (_, a2) = gabbro_syntax::lies("<probe>", allein);
    assert!(
        a2.absagen
            .iter()
            .any(|a| a.code == "P033" && a.text.contains("on its own")),
        "P033 without a block in front keeps its wording:\n{}",
        a2.zeige(allein)
    );
}

/// **PLAN-BITS §1: `uN`/`iN` sugar -- the poison and the positive side by side.**
///
/// The vocabulary stays closed (rule 14): the lexer never learns `u13`, the type
/// rule desugars it to the storage word plus the exact range. Widths outside
/// 1..64 (`u0`, `u65`, `i0`) are refused with `P008`; the eight standard words
/// keep their full-width meaning exactly.
#[test]
fn zuckerbreiten_tragen_bereich_und_speicher() {
    // Positive side: each sugar form parses clean here; the checker and the
    // emitter probes below hold the range and the storage width.
    faellt_nicht("impl fn f(x : u1) effects { pure } { }");
    faellt_nicht("impl fn f(x : u13) effects { pure } { }");
    faellt_nicht("impl fn f(x : i37) effects { pure } { }");
    faellt_nicht("impl fn f(x : u64) effects { pure } { }");
    // The eight standard words are untouched by the sugar arm.
    faellt_nicht("impl fn f(x : u8) effects { pure } { }");
    faellt_nicht("impl fn f(x : i64) effects { pure } { }");
    // Poison side: no width outside 1..64, and never widened silently.
    // In a TYPE rule the bad width is the reader's own refusal (`P008`).
    faellt_mit("impl fn f(x : u0) effects { pure } { }", "P008");
    faellt_mit("impl fn f(x : u65) effects { pure } { }", "P008");
    faellt_mit("impl fn f(x : i0) effects { pure } { }", "P008");
    faellt_mit("impl fn f(x : i65) effects { pure } { }", "P008");
    // Sugar already carries its range: a second `in` has no room beside it.
    faellt_mit("impl fn f(x : u13 in 0 .. 7) effects { pure } { }", "P008");
}

#[test]
fn modul_mit_strichpunkt_nennt_den_rumpf() {
    faellt_nicht("module m { }");
    faellt_mit_notiz("module m;", "P001", "`module` carries a brace body");
}

// -- Lane E1: library calls ------------------------------------------------------------
// `@library#function ( args ) { region }` parses in statement position; the
// reader captures names, arguments and the brace-balanced region without
// interpreting it. (The checker says `N057`; this crate never refuses what it
// can read.)

#[test]
fn library_call_reads_names_args_and_region() {
    let quelle = "module t { impl fn f(a : u32) -> u32 effects { pure } costs <= 8 ops \
                  { @spirv#kernel(a) { dispatch { nested } 0 }; return a; } }";
    let (baum, absagen) = gabbro_syntax::lies("<probe>", quelle);
    assert!(
        !absagen.absagen.iter().any(|a| a.stufe == Stufe::Fehler),
        "a well-formed library call parses:\n{}",
        absagen.zeige(quelle)
    );
    let gabbro_syntax::ast::ItemArt::Modul(m) = &baum.items[0].art else {
        panic!("a module parses as a module");
    };
    let gabbro_syntax::ast::ItemArt::Funktion(f) = &m.items[0].art else {
        panic!("a function parses as a function");
    };
    let gabbro_syntax::ast::FnRumpf::Block(b) = &f.rumpf else {
        panic!("a body parses as a block");
    };
    let gabbro_syntax::ast::StmtArt::LibraryCall(r) = &b.anweisungen[0].art else {
        panic!("a library call parses as a library call");
    };
    assert_eq!(r.library.text, "spirv");
    assert_eq!(r.function.text, "kernel");
    assert_eq!(r.args.len(), 1);
    // The region is raw tokens: nested braces balanced, nothing interpreted.
    let rohtexte: Vec<&str> = r.region.iter().map(|t| t.text.as_str()).collect();
    assert_eq!(rohtexte, vec!["dispatch", "{", "nested", "}", "0"]);
}

// -- «SS-1» (2026-09-12), built in lane S5: `syscall` parses -------------------------
//
// **One declaration, three directions.** A `syscall …` item reads into
// `SyscallDecl` -- the `=` binding of the written examples and the `:` binding
// of the §1 production line both. And the entry name `syscall` stays legal:
// `entry syscall …` is an identifier at a name position (`ctx`), not the header
// word.
#[test]
fn syscall_wird_gelesen() {
    // The written shape: `=` bindings, bare out registers, `=>` error arms.
    faellt_nicht(
        "syscall write(fd : u64) -> u64 abi linux arch x86_64 number 1 \
         regs in { rdi = fd } regs out { rax } clobbers { rcx } \
         errors { EBADF => BadFd } effects { pure } \
         assume linux_write_contract falsifier probe_write;",
    );
    // The §1 production line spells the binding with `:` -- it reads too.
    faellt_nicht(
        "syscall write(fd : u64) -> u64 abi linux arch x86_64 number 1 \
         regs in { rdi : fd } regs out { rax } clobbers { rcx } \
         errors { EBADF => BadFd } effects { pure } \
         assume linux_write_contract falsifier probe_write;",
    );
    // The `kernel` counterpart reads too (the checker refuses it as `N068`).
    faellt_nicht(
        "syscall write(fd : u64) -> u64 abi linux arch x86_64 number 1 \
         regs in { rdi = fd } regs out { rax } clobbers { rcx } \
         errors { EBADF => BadFd } effects { pure } \
         kernel k::dispatch;",
    );
    // The name stays free: `entry syscall …` names an entry, not a syscall.
    faellt_nicht(
        "entry syscall vector 0x80 arch x86_64 { regs in { } regs out { } \
         preserves { } clobbers { r11 } stack s dispatch m::f; }",
    );
}

// -- syscall `costs` (lane-114 gap, closed) -------------------------------------------
//
// The clause stands behind `effects` in fixed order and reads into
// `SyscallDecl::costs`; without it the field is `None` (the checker says
// `N322` there -- this crate never refuses what it can read).
#[test]
fn syscall_kosten_werden_gelesen() {
    let quelle = "syscall write(fd : u64) -> u64 abi linux arch x86_64 number 1 \
         regs in { rdi = fd } regs out { rax } clobbers { rcx } \
         errors { EBADF => BadFd } effects { pure } costs <= 8 ops \
         assume linux_write_contract falsifier probe_write;";
    let (baum, absagen) = gabbro_syntax::lies("<probe>", quelle);
    assert!(
        !absagen.absagen.iter().any(|a| a.stufe == Stufe::Fehler),
        "a syscall with a costs clause parses:\n{}",
        absagen.zeige(quelle)
    );
    let gabbro_syntax::ast::ItemArt::Syscall(s) = &baum.items[0].art else {
        panic!("a syscall parses as a syscall");
    };
    assert!(
        s.costs.is_some(),
        "the costs clause lands in the field, not in nothing"
    );
    // Without the clause the field is `None`, and the declaration still reads.
    let (baum2, absagen2) = gabbro_syntax::lies(
        "<probe>",
        "syscall write(fd : u64) -> u64 abi linux arch x86_64 number 1 \
         regs in { rdi = fd } regs out { rax } clobbers { rcx } \
         errors { EBADF => BadFd } effects { pure } \
         assume linux_write_contract falsifier probe_write;",
    );
    assert!(
        !absagen2.absagen.iter().any(|a| a.stufe == Stufe::Fehler),
        "a syscall without the clause still parses:\n{}",
        absagen2.zeige(quelle)
    );
    let gabbro_syntax::ast::ItemArt::Syscall(s2) = &baum2.items[0].art else {
        panic!("a syscall parses as a syscall");
    };
    assert!(
        s2.costs.is_none(),
        "no clause, no promise -- the checker owns the refusal"
    );
}

// -- Lane 222: integer `match` arms ------------------------------------------------------
//
// `match` over an integer scrutinee with range/exact arms: the 256-way
// dispatch leaves the flat-comparison chain. Arms parse into AST that
// says what they mean (`IntFall`); exhaustiveness is lane 228's
// business, lowering lane 227's -- until they land the checker accepts
// (0 errors, bodies checked) and the emitter refuses by name (C001
// "`match` over something other than an `option index into T`"), each
// shown with the shipped binary and booked in MUSE-REPORT-222.md.

fn match_scaffold(arms: &str) -> String {
    format!(
        "impl fn f(x : u32) -> u32 effects {{ pure }} costs <= 8 ops \
         {{ match x {{ {arms} }} return 0; }}"
    )
}

/// The integer pattern of the single arm in `match x { <arm> => { return 0; } }`.
fn int_pattern_of(arm: &str) -> gabbro_syntax::ast::IntPat {
    let quelle = match_scaffold(&format!("{arm} => {{ return 0; }}"));
    let (baum, absagen) = gabbro_syntax::lies("<probe>", &quelle);
    assert!(
        !absagen
            .absagen
            .iter()
            .any(|a| a.stufe == Stufe::Fehler),
        "integer arm parses:\n{}",
        absagen.zeige(&quelle)
    );
    let gabbro_syntax::ast::ItemArt::Funktion(f) = &baum.items[0].art else {
        panic!("a function parses as a function");
    };
    let gabbro_syntax::ast::FnRumpf::Block(b) = &f.rumpf else {
        panic!("a body parses as a block");
    };
    let gabbro_syntax::ast::StmtArt::Match(m) = &b.anweisungen[0].art else {
        panic!("a match parses as a match");
    };
    assert_eq!(m.zweige.len(), 1, "one arm in, one arm out");
    m.zweige[0].intpat.clone().expect("an integer arm carries its pattern")
}

#[test]
fn lane222_int_arms_parse() {
    // Exact arms, every literal shape the lexer folds.
    faellt_nicht(&match_scaffold("0 => { return 0; }"));
    faellt_nicht(&match_scaffold("255 => { return 0; }"));
    faellt_nicht(&match_scaffold("0xFF => { return 0; }"));
    faellt_nicht(&match_scaffold("0b1010 => { return 0; }"));
    faellt_nicht(&match_scaffold("-1 => { return 0; }"));
    // Range arms, both range words, negative bounds.
    faellt_nicht(&match_scaffold("0 .. 255 => { return 0; }"));
    faellt_nicht(&match_scaffold("0 ..< 256 => { return 0; }"));
    faellt_nicht(&match_scaffold("-10 .. -1 => { return 0; }"));
    faellt_nicht(&match_scaffold("0..10 => { return 0; }"));
    // Several arms together, and mixed with variant arms: the parser
    // accepts the mix (it cannot know the scrutinee's type), and every
    // mix is refused downstream by an existing rule -- C001 exactness
    // over `tagged`/`option`, M123 invented-name over `reason`, C001
    // over integers (MUSE-REPORT-222.md carries the matrix).
    faellt_nicht(&match_scaffold(
        "0 => { return 0; } 1 ..< 4 => { return 1; } 4 .. 255 => { return 2; }",
    ));
    faellt_nicht(&match_scaffold(
        "Leer => { return 0; } 1 => { return 1; }",
    ));
    // The tagged shape from beispiele/120 keeps parsing untouched.
    faellt_nicht(&match_scaffold(
        "Leer => { return 0; } Kurz(k) => { return k; }",
    ));
}

#[test]
fn lane222_int_arm_poison_keeps_existing_codes() {
    // A `-` before anything but a literal is no bound at all.
    faellt_mit(&match_scaffold("-x => { return 0; }"), "P004");
    // An integer arm binds nothing: `0(k)` has no `=>` where one stands.
    faellt_mit(&match_scaffold("0(k) => { return 0; }"), "P001");
    // An open range is an unfinished bound.
    faellt_mit(&match_scaffold("0 .. => { return 0; }"), "P004");
    // A float is not an integer arm and not a variant arm either.
    let (_, absagen) = gabbro_syntax::lies("<probe>", &match_scaffold("1.5 => { return 0; }"));
    assert!(
        absagen.absagen.iter().any(|a| a.stufe == Stufe::Fehler),
        "a float arm falls, with whatever code names the position"
    );
}

#[test]
fn lane222_int_pattern_prints_and_round_trips() {
    use gabbro_syntax::ast::IntPat;
    // Two spellings of one value print to one canonical text: the tree
    // says what the arm means, not how the bound was spelled. (Spans
    // differ, as they should -- `Ident` compares with its span house-wide.)
    assert_eq!(
        gabbro_syntax::print::int_pattern(&int_pattern_of("0x10")),
        "16"
    );
    assert_eq!(
        gabbro_syntax::print::int_pattern(&int_pattern_of("0x10")),
        gabbro_syntax::print::int_pattern(&int_pattern_of("16"))
    );
    assert_eq!(
        gabbro_syntax::print::int_pattern(&int_pattern_of("0b1010")),
        gabbro_syntax::print::int_pattern(&int_pattern_of("10"))
    );
    // Each shape prints canonically, and the printed text re-parses to
    // the same pattern -- print/parse round-trip of the new form.
    for (spell, canonical) in [
        ("3", "3"),
        ("-1", "-1"),
        ("0xFF", "255"),
        ("0 .. 255", "0 .. 255"),
        ("0 ..< 256", "0 ..< 256"),
        ("-10 .. -1", "-10 .. -1"),
    ] {
        let pat = int_pattern_of(spell);
        let printed = gabbro_syntax::print::int_pattern(&pat);
        assert_eq!(printed, canonical, "canonical print of {spell}");
        let back = int_pattern_of(&printed);
        assert!(
            match (&pat, &back) {
                (IntPat::Exact(a), IntPat::Exact(b)) => a.negative == b.negative && a.value == b.value,
                (
                    IntPat::Range {
                        lo: a1,
                        hi: b1,
                        exclusive: e1,
                    },
                    IntPat::Range {
                        lo: a2,
                        hi: b2,
                        exclusive: e2,
                    },
                ) => {
                    a1.negative == a2.negative
                        && a1.value == a2.value
                        && b1.negative == b2.negative
                        && b1.value == b2.value
                        && e1 == e2
                }
                _ => false,
            },
            "print/parse round-trip of {spell}"
        );
    }
}

// -- Lane 222: the windowed `traverse` domain --------------------------------------------
//
// `traverse i over slots of T from <start> count <len> by …`: the bm13
// window shape (start plus length). The reader fixes the shape
// precisely and refuses it with the pre-existing `P001` plus a handoff
// note -- there is no AST home for the window that keeps the checker
// compiling (a new `Domaene` variant breaks its exhaustive matches, a
// new `Traverse` field its literal constructions), so carrying it
// silently as a whole-table walk is the one thing the reader must not
// do, and no new code is issued for it. Lanes 229 and 234 lift the
// refusal.

/// The refusal a well-formed windowed walk carries, code and sentence.
///
/// Both halves, or neither is a measurement: the code alone would pass
/// with the handoff note deleted, the note alone with the refusal moved
/// to another rule (same shape as `faellt_mit_notiz` above).
fn falls_with_note(quelle: &str, code: &str, teil: &str) {
    let (_, absagen) = gabbro_syntax::lies("<probe>", quelle);
    let treffer: Vec<_> = absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler && a.code == code)
        .collect();
    assert!(
        !treffer.is_empty(),
        "expected {code}:\n{quelle}\n{}",
        absagen.zeige(quelle)
    );
    assert!(
        treffer.iter().any(|a| a.text.contains(teil)
            || a.notizen.iter().any(|n| n.contains(teil))),
        "{code} fell, but neither text nor note carries {teil:?}:\n{quelle}\n{}",
        absagen.zeige(quelle)
    );
}

fn traverse_scaffold(domain: &str) -> String {
    format!(
        "module probe {{ table T count 4 {{ slot {{ v : u32, }} }} \
         impl fn f() effects {{ writes T.slots }} costs <= 64 ops \
         {{ traverse i over {domain} by unvisited {{ T.slots[i].v = 0; }} }} }}"
    )
}

#[test]
fn lane222_windowed_traverse_refused_by_name() {
    // The well-formed window: table, start expression, length
    // expression -- refused with P001, naming the handoff in the note.
    falls_with_note(
        &traverse_scaffold("slots of T from 2 count 2"),
        "P001",
        "has no lowering yet",
    );
    falls_with_note(
        &traverse_scaffold("slots of T from 0 count 4"),
        "P001",
        "lane 234",
    );
    // Computed bounds are the shape, not a corner.
    faellt_mit(
        &traverse_scaffold("slots of T from base + i count n - k"),
        "P001",
    );
    // The plain walk beside it parses untouched.
    faellt_nicht(&traverse_scaffold("slots of T"));
}

#[test]
fn lane222_window_malformed_keeps_existing_codes() {
    // `from` without `count` is an unfinished clause: `count` expected.
    faellt_mit(&traverse_scaffold("slots of T from 2"), "P001");
    // `from` without a bound is no bound at all.
    let (_, absagen) =
        gabbro_syntax::lies("<probe>", &traverse_scaffold("slots of T from by unvisited"));
    assert!(
        absagen.absagen.iter().any(|a| a.stufe == Stufe::Fehler),
        "a window without a start falls"
    );
    // A window over any other domain is still `by`-shaped: the old
    // refusal stands, no new code fires there.
    faellt_mit(
        &traverse_scaffold("descendants of T from 2 count 2"),
        "P001",
    );
}

// -- Lane 222: `TIEFE_MAX` over the corpus ------------------------------------------------
//
// 32 stands 4x over the corpus (the reader's own ledger line,
// `parse.rs::TIEFE_MAX`): the deepest corpus file nests 8 deep. This
// test re-measures the true parser depth over every corpus file -- a
// bump would be a constant plus fuzz evidence, never a redesign.

#[test]
fn lane222_depth_stands_fourfold_over_corpus() {
    let wurzel = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..");
    let mut tiefst = 0usize;
    let mut dateien = 0usize;
    let mut gelesene: Vec<_> = std::fs::read_dir(wurzel.join("beispiele"))
        .expect("beispiele readable")
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|e| e == "gab"))
        .collect();
    gelesene.sort();
    for pfad in &gelesene {
        let quelle = std::fs::read_to_string(pfad)
            .unwrap_or_else(|e| panic!("{}: {e}", pfad.display()));
        let mut absagen = gabbro_syntax::Absagen::neu("<korpus>");
        let (_, stand) = gabbro_syntax::parse::parse_with_max_depth(&quelle, &mut absagen);
        dateien += 1;
        if stand > tiefst {
            tiefst = stand;
        }
        assert!(
            !absagen
                .absagen
                .iter()
                .any(|a| a.stufe == Stufe::Fehler && a.code == "P038"),
            "no corpus file hits TIEFE_MAX: {}",
            pfad.display()
        );
    }
    assert!(dateien > 100, "the corpus population stands: {dateien} files");
    // The measurement, printed so a run says the number, not just the verdict.
    eprintln!("lane222: deepest corpus nesting {tiefst} over {dateien} files");
    assert!(
        tiefst * 4 <= gabbro_syntax::parse::TIEFE_MAX,
        "deepest corpus file nests {tiefst} -- TIEFE_MAX {} no longer stands 4x over it",
        gabbro_syntax::parse::TIEFE_MAX
    );
}
