/-
  File:      Grammatik/Parser/Item/ElementTiefProben2.lean
  Subject:   T3 PART 3: the `decide` probes for the deep item
               readers, part 2 of 7 (tt16..tt29).

  The probes are split over seven modules only so that each one
  builds under the 4 GiB memory ceiling; part 6 carries the CUTS
  block for all seven.

  Like `Parser/AnweisungProben.lean`: one kernel evaluation per
  theorem keeps every worker small. Each probe is split in two: a
  lex pin (`tNN_lex`: the source line lexes to this token list)
  and a tree pin (`tNN`: the reader maps the list to this
  shape). A mistranscribed list fails its lex pin loudly. Tree
  shapes were compared against `ast.rs`/`parse.rs` by reading (no
  cargo in this lane); all differences are booked in the CUTS
  block of `Parser/ElementTief.lean`.
  Corpus sites stand at each probe; probes with no corpus line say
  so. The end-to-end probe is `tEnd` (beispiele/112, the smallest
  whole file with a table, a lock and contracted functions).
-/
import Grammatik.Parser.Item.ElementTief

namespace Gabbro.Grammatik.Parser

set_option maxRecDepth 100000

def tt16 : List Token :=
  [.wort "spec", .wort "fn", .ident "ist_blatt", .zeichen "(",
   .ident "c", .zeichen ":", .wort "ptr", .zeichen "<",
   .wort "normal", .zeichen ",", .wort "r", .zeichen ">",
   .ident "Kappenraum", .zeichen ",", .ident "s", .zeichen ":",
   .wort "index", .wort "into", .ident "Kappenraum", .zeichen ")",
   .zeichen "->", .wort "bool", .wort "effects", .zeichen "{",
   .wort "pure", .zeichen "}",
   .zeichen "=", .ident "c", .zeichen ".", .wort "slots",
   .zeichen "[", .ident "s", .zeichen "]", .zeichen ".",
   .ident "benutzt", .zeichen "&&", .ident "c", .zeichen ".",
   .wort "slots", .zeichen "[", .ident "s", .zeichen "]",
   .zeichen ".", .ident "erstes_kind", .zeichen "==",
   .wort "None", .zeichen ";", .ende]
theorem t16_lex :
    lex "spec fn ist_blatt(c : ptr<normal, r> Kappenraum, s : index into Kappenraum) -> bool effects { pure } = c.slots[s].benutzt && c.slots[s].erstes_kind == None;" =
      .ok tt16 := by
  decide
theorem t16 : beqTopTief (parseTopTief tt16)
    (.ok [.specT
      { art := "spec", name := "ist_blatt",
        params := [("c", .ptr "normal" "r" (.atom "Kappenraum")),
          ("s", .index false "Kappenraum")],
        res := .some (.atom "bool"), fehler := .none,
        klauseln := [.effs [.pure]] }
      (.bin "&&"
        (.field (.index (.field (.variable "c") "slots")
          (.variable "s")) "benutzt")
        (.bin "=="
          (.field (.index (.field (.variable "c") "slots")
            (.variable "s")) "erstes_kind")
          (.call "None" [])))]) = true := by
  decide
-- beispiele/01-tabelle.gab (the `ist_blatt` predicate helper).
-- Rust: `Funktion` with `= pred` -- same shape (a `ptr` and an
-- `index into` parameter, a `pure` effect).
def tt17 : List Token :=
  [.wort "impl", .wort "fn", .ident "ausgeben", .zeichen "(",
   .ident "tor", .zeichen ":", .wort "u16", .zeichen ",",
   .ident "wert", .zeichen ":", .wort "u8", .zeichen ")",
   .wort "effects", .zeichen "{", .wort "writes", .ident "GERAET",
   .zeichen "}", .wort "costs", .zeichen "<=", .num 1,
   .wort "ops", .wort "arch", .ident "x86_64", .zeichen "=",
   .wort "asm", .zeichen "{", .text "outb %[wert], %[tor]",
   .wort "in", .zeichen "{", .ident "wert", .zeichen ":",
   .text "a", .zeichen ",", .ident "tor", .zeichen ":",
   .text "d", .zeichen "}", .wort "clobbers", .zeichen "{",
   .ident "memory", .zeichen "}", .zeichen "}", .zeichen ";",
   .ende]
theorem t17_lex :
    lex "impl fn ausgeben(tor : u16, wert : u8) effects { writes GERAET } costs <= 1 ops arch x86_64 = asm { \"outb %[wert], %[tor]\" in { wert : \"a\", tor : \"d\" } clobbers { memory } };" =
      .ok tt17 := by
  decide
theorem t17 : beqTopTief (parseTopTief tt17)
    (.ok [.asmT
      { art := "impl", name := "ausgeben",
        params := [("tor", .atom "u16"), ("wert", .atom "u8")],
        res := .none, fehler := .none,
        klauseln := [.effs [.writes (.variable "GERAET")],
          .cost (.lit 1), .arch "x86_64"] }
      "asm { \"outb %[wert], %[tor]\" in { wert : \"a\" , tor : \"d\" } clobbers { memory } } "]) = true := by
  decide
-- beispiele/36-asm.gab:17-27. Rust: `Funktion` with `= asm` --
-- the assembler body rides raw and balanced (see CUTS).
def tt18 : List Token :=
  [.wort "impl", .wort "fn", .ident "f", .zeichen "(", .zeichen ")",
   .wort "deadline", .zeichen "<=", .num 10, .wort "ops",
   .wort "arch", .ident "x86_64", .wort "falsifier", .ident "s",
   .zeichen ";", .ende]
theorem t18_lex :
    lex "impl fn f() deadline <= 10 ops arch x86_64 falsifier s;" =
      .ok tt18 := by
  decide
theorem t18 : beqTopTief (parseTopTief tt18)
    (.ok [.protoT
      { art := "impl", name := "f", params := [], res := .none,
        fehler := .none,
        klauseln := [.limit
          "deadline <= 10 ops arch x86_64 falsifier s"] }]) = true := by
  decide
-- The `deadline` clause shape is beispiele/36-asm.gab:36 (on a
-- bodied `asm` function there); the bare-proto carrier is
-- synthetic. Rust: the clause rides the signature.
def tt19 : List Token :=
  [.wort "translator", .ident "build", .wort "for", .ident "sum",
   .zeichen "(", .ident "region", .zeichen ":", .ident "SumTab",
   .zeichen ")", .zeichen "->", .ident "SumTab", .wort "effects",
   .zeichen "{", .wort "pure", .zeichen "}", .wort "costs",
   .zeichen "<=", .num 8, .wort "ops", .wort "decreases",
   .ident "region", .zeichen ".", .ident "v", .zeichen "{",
   .wort "return", .ident "region", .zeichen ";", .zeichen "}",
   .ende]
theorem t19_lex :
    lex "translator build for sum(region : SumTab) -> SumTab effects { pure } costs <= 8 ops decreases region.v { return region; }" =
      .ok tt19 := by
  decide
theorem t19 : beqTopTief (parseTopTief tt19)
    (.ok [.transT "sum"
      { art := "", name := "build",
        params := [("region", .atom "SumTab")],
        res := .some (.atom "SumTab"), fehler := .none,
        klauseln := [.effs [.pure], .cost (.lit 8),
          .drops (.field (.variable "region") "v")] }
      (.block [] (.some (.ret (.some (.variable "region")))))]) = true := by
  decide
-- beispiele/106-summe-uebersetzt.gab (the `build` translator).
-- Rust: `Translator` -- same shape (a `pure` contract with a
-- `decreases` witness).
def tt20 : List Token :=
  [.wort "arena", .ident "Log", .wort "capacity", .num 2,
   .zeichen "..", .num 8, .wort "of", .wort "u32", .zeichen ";",
   .ende]
theorem t20_lex :
    lex "arena Log capacity 2 .. 8 of u32;" = .ok tt20 := by
  decide
theorem t20 : beqTopTief (parseTopTief tt20)
    (.ok [.arenaT "Log" (.lit 2) (.lit 8) .none (.atom "u32") .none]) = true := by
  decide
-- beispiele/98-arena-erklaert.gab. Rust: `Arena` -- same shape.
def tt21 : List Token :=
  [.wort "format", .ident "Elf64Kopf", .wort "endian",
   .wort "little", .zeichen "{", .ident "e_typ", .zeichen ":",
   .wort "u16", .wort "in", .num 1, .zeichen "..", .num 4,
   .zeichen ",", .ident "e_maschine", .zeichen ":", .wort "u16",
   .zeichen ",", .ident "e_shoff", .zeichen ":", .wort "u64",
   .wort "offset_into", .wort "Self", .wort "where",
   .ident "e_shoff", .zeichen "<=", .wort "lenof", .zeichen "(",
   .wort "Self", .zeichen ")", .zeichen ",", .ident "e_flags",
   .zeichen ":", .wort "u32", .wort "reserved", .zeichen ",",
   .zeichen "}", .ende]
theorem t21_lex :
    lex "format Elf64Kopf endian little { e_typ : u16 in 1 .. 4, e_maschine : u16, e_shoff : u64 offset_into Self where e_shoff <= lenof(Self), e_flags : u32 reserved, }" =
      .ok tt21 := by
  decide
theorem t21 : beqTopTief (parseTopTief tt21)
    (.ok [.formatT "Elf64Kopf" .none (.some "little")
      [{ fname := "e_typ",
          ftyp := .range (.atom "u16") (.lit 1) (.lit 4) false,
          pos := .none, bezug := .none, wo := .none,
          reserviert := false, byOps := false },
        { fname := "e_maschine", ftyp := .atom "u16",
          pos := .none, bezug := .none, wo := .none,
          reserviert := false, byOps := false },
        { fname := "e_shoff", ftyp := .atom "u64",
          pos := .none, bezug := (.some "Self"),
          wo := (.some (.bin "<=" (.variable "e_shoff")
            (.built "lenof" [.variable "Self"]))),
          reserviert := false, byOps := false },
        { fname := "e_flags", ftyp := .atom "u32",
          pos := .none, bezug := .none, wo := .none,
          reserviert := true, byOps := false }]]) = true := by
  decide
-- beispiele/03-format.gab:12-24 (fields from adjacent lines).
-- Rust: `Format` with ranged, plain, `offset_into`/`where` and
-- `reserved` fields -- same shape.
def tt22 : List Token :=
  [.wort "reason", .ident "KappenFehler", .zeichen "{",
   .ident "KeinSlot", .zeichen "=", .num 1,
   .text "kein freier Slot mehr", .ident "Ungueltig",
   .zeichen "=", .num 2, .text "abgelaufenes Handle",
   .ident "HatKinder", .zeichen "=", .num 3,
   .text "erst die Nachfahren einsammeln", .wort "exhaustive",
   .zeichen "}", .ende]
theorem t22_lex :
    lex "reason KappenFehler { KeinSlot = 1 \"kein freier Slot mehr\" Ungueltig = 2 \"abgelaufenes Handle\" HatKinder = 3 \"erst die Nachfahren einsammeln\" exhaustive }" =
      .ok tt22 := by
  decide
theorem t22 : beqTopTief (parseTopTief tt22)
    (.ok [.whyT "KappenFehler"
      [("KeinSlot", .lit 1, "kein freier Slot mehr"),
        ("Ungueltig", .lit 2, "abgelaufenes Handle"),
        ("HatKinder", .lit 3, "erst die Nachfahren einsammeln")]
      true]) = true := by
  decide
-- beispiele/01-tabelle.gab (the `KappenFehler` grounds). Rust:
-- `Reason` with an `exhaustive` tail -- same shape.
def tt23 : List Token :=
  [.wort "state", .ident "Ampel", .zeichen "{", .wort "transition",
   .ident "schalten", .zeichen "{", .ident "licht", .zeichen ":",
   .ident "rot", .zeichen "->", .ident "gruen", .zeichen "}",
   .wort "requires", .ident "bereit", .zeichen "==", .wort "true",
   .wort "effects", .zeichen "{", .wort "writes", .ident "licht",
   .zeichen "}", .zeichen "}", .ende]
theorem t23_lex :
    lex "state Ampel { transition schalten { licht : rot -> gruen } requires bereit == true effects { writes licht } }" =
      .ok tt23 := by
  decide
theorem t23 : beqTopTief (parseTopTief tt23)
    (.ok [.stateT "Ampel"
      [{ tname := "schalten",
         schritte := [(.variable "licht", .variable "rot",
           .variable "gruen")],
         voraus := .some (.bin "==" (.variable "bereit") .tru),
         wirkung := [.writes (.variable "licht")] }]]) = true := by
  decide
-- Synthetic (no `state` item in the corpus, measured 2026-09-13;
-- the transition arms follow beispiele/20-falle-vier.gab).
-- Rust: `State` with one guarded transition.
def tt24 : List Token :=
  [.wort "assume", .ident "mmu_folgt_ihrem_modell",
   .text "Eine Uebersetzung mit P=0 faultet, bevor ein Zugriff die Zeile beruehrt.",
   .wort "falsifier", .ident "sonde_pf_bei_p0", .zeichen ";",
   .ende]
theorem t24_lex :
    lex "assume mmu_folgt_ihrem_modell \"Eine Uebersetzung mit P=0 faultet, bevor ein Zugriff die Zeile beruehrt.\" falsifier sonde_pf_bei_p0;" =
      .ok tt24 := by
  decide
theorem t24 : beqTopTief (parseTopTief tt24)
    (.ok [.assumT "mmu_folgt_ihrem_modell" .none
      "Eine Uebersetzung mit P=0 faultet, bevor ein Zugriff die Zeile beruehrt."
      (.probe "sonde_pf_bei_p0")]) = true := by
  decide
-- beispiele/06-annahmen.gab:15-17. Rust: `Assume` with a
-- falsifier -- same shape.
def tt25 : List Token :=
  [.wort "axiom", .ident "write_cr3", .zeichen "(", .ident "p",
   .zeichen ":", .ident "Pa", .zeichen ")", .wort "effects",
   .zeichen "{", .wort "writes", .ident "tlb", .zeichen ",",
   .wort "writes", .ident "aktive_tabelle", .zeichen "}",
   .wort "falsifier",
   .ident "sonde_cr3", .zeichen ";", .ende]
theorem t25_lex :
    lex "axiom write_cr3(p : Pa) effects { writes tlb, writes aktive_tabelle } falsifier sonde_cr3;" =
      .ok tt25 := by
  decide
theorem t25 : beqTopTief (parseTopTief tt25)
    (.ok [.axiomT "write_cr3" [("p", .atom "Pa")] .none .none
      [.writes (.variable "tlb"),
        .writes (.variable "aktive_tabelle")]
      (.probe "sonde_cr3")]) = true := by
  decide
-- beispiele/06-annahmen.gab:80. Rust: `Axiom` with two writes --
-- same shape.
def tt26 : List Token :=
  [.wort "check", .ident "stapel_wasserstand", .zeichen "{",
   .wort "claim",
   .text "Kein Kern hat je mehr als 3/4 seines Stapels benutzt.",
   .wort "measures", .ident "tiefe_max", .zeichen ",",
   .ident "tiefe_lebend", .zeichen ",", .ident "kerne_gemessen",
   .wort "gates", .ident "abnahme", .zeichen ",",
   .ident "freigabe", .wort "can_fail",
   .zeichen "{", .wort "let", .ident "g", .zeichen "=",
   .ident "groesse_gemessen", .zeichen "(", .zeichen ")",
   .wort "else", .zeichen "(", .ident "e1", .zeichen ")",
   .zeichen "{", .wort "return", .wort "false", .zeichen ";",
   .zeichen "}", .wort "if", .ident "tiefe_max", .zeichen "*",
   .num 4, .zeichen ">=", .ident "g", .zeichen "*", .num 3,
   .zeichen "{", .wort "return", .wort "false", .zeichen ";",
   .zeichen "}", .wort "return", .wort "true", .zeichen ";",
   .zeichen "}", .wort "floor", .ident "kerne_gemessen",
   .zeichen ">=", .num 2, .zeichen ",", .ident "tiefe_max",
   .zeichen ">=", .num 1, .wort "counterprobe",
   .text "Ein Kern mit kuenstlich tiefem Aufruf muss die Pflicht fallen lassen.",
   .wort "expects", .ident "sonde_tiefer_stapel", .zeichen "}",
   .ende]
set_option maxHeartbeats 800000 in
theorem t26_lex :
    lex "check stapel_wasserstand { claim \"Kein Kern hat je mehr als 3/4 seines Stapels benutzt.\" measures tiefe_max, tiefe_lebend, kerne_gemessen gates abnahme, freigabe can_fail { let g = groesse_gemessen() else (e1) { return false; } if tiefe_max * 4 >= g * 3 { return false; } return true; } floor kerne_gemessen >= 2, tiefe_max >= 1 counterprobe \"Ein Kern mit kuenstlich tiefem Aufruf muss die Pflicht fallen lassen.\" expects sonde_tiefer_stapel }" =
      .ok tt26 := by
  decide
theorem t26 : beqTopTief (parseTopTief tt26)
    (.ok [.checkT
      { cname := "stapel_wasserstand",
        claim := "Kein Kern hat je mehr als 3/4 seines Stapels benutzt.",
        misst := [.variable "tiefe_max", .variable "tiefe_lebend",
          .variable "kerne_gemessen"],
        gates := ["abnahme", "freigabe"],
        canFail :=
          (.block
            [.bindElse "g" .none (.call "groesse_gemessen" []) "e1"
              (.block [] (.some (.ret (.some .fls)))),
              .cond (.bin ">=" (.bin "*" (.variable "tiefe_max") (.lit 4))
                (.bin "*" (.variable "g") (.lit 3)))
                (.block [] (.some (.ret (.some .fls)))) [] .none]
            (.some (.ret (.some .tru)))),
        boden := [.bin ">=" (.variable "kerne_gemessen") (.lit 2),
          .bin ">=" (.variable "tiefe_max") (.lit 1)],
        sonde := .some ("Ein Kern mit kuenstlich tiefem Aufruf muss die Pflicht fallen lassen.",
          "sonde_tiefer_stapel") }]) = true := by
  decide
-- beispiele/06-annahmen.gab:127-146 (comments dropped, one
-- string re-encoded without umlauts -- see CUTS). Rust: `Check`
-- with `floor` and `counterprobe` -- same shape.
def tt27 : List Token :=
  [.wort "table", .ident "Verzeichnis", .wort "count",
   .ident "N", .zeichen "{", .wort "slot", .zeichen "{",
   .ident "benutzt", .zeichen ":", .wort "bool", .zeichen ",",
   .ident "marke", .zeichen ":", .wort "u32", .zeichen ",",
   .zeichen "}", .wort "ops", .wort "insert", .zeichen ",",
   .wort "remove", .zeichen ";", .wort "occupied", .ident "benutzt",
   .zeichen ";", .zeichen "}", .ende]
theorem t27_lex :
    lex "table Verzeichnis count N { slot { benutzt : bool, marke : u32, } ops insert, remove; occupied benutzt; }" =
      .ok tt27 := by
  decide
theorem t27 : beqTopTief (parseTopTief tt27)
    (.ok [.tableT "Verzeichnis" .none (.some (.variable "N")) .none .none
      false
      [.tSlot [{ fname := "benutzt", ftyp := .atom "bool",
                   pos := .none, bezug := .none, wo := .none,
                   reserviert := false, byOps := false },
                 { fname := "marke", ftyp := .atom "u32",
                   pos := .none, bezug := .none, wo := .none,
                   reserviert := false, byOps := false }],
        .tOps ["insert", "remove"], .tBusy "benutzt"]]) = true := by
  decide
-- beispiele/47-ops-wortmenge.gab:60-71 (comments dropped).
-- Rust: `Tabelle` with generated `ops` and an `occupied` field
-- -- same shape.
def tt28 : List Token :=
  [.wort "table", .ident "T", .wort "count", .num 4,
   .zeichen "{", .wort "const", .ident "WURZEL", .zeichen ":",
   .wort "u32", .zeichen "=", .num 0, .zeichen ";",
   .wort "slot", .zeichen "{", .ident "b", .zeichen ":",
   .wort "bool", .zeichen ",", .zeichen "}", .zeichen "}",
   .ende]
theorem t28_lex :
    lex "table T count 4 { const WURZEL : u32 = 0; slot { b : bool, } }" =
      .ok tt28 := by
  decide
theorem t28 : beqTopTief (parseTopTief tt28)
    (.ok [.tableT "T" .none (.some (.lit 4)) .none .none false
      [.tConst "WURZEL" (.atom "u32") (.one (.lit 0)),
        .tSlot [{ fname := "b", ftyp := .atom "bool",
                   pos := .none, bezug := .none, wo := .none,
                   reserviert := false, byOps := false }]]]) = true := by
  decide
-- beispiele/01-tabelle.gab (the `WURZEL` table constant beside a
-- slot). Rust: `Tabelle` with a `const` member -- same shape.
def tt29 : List Token :=
  [.wort "table", .ident "K", .wort "count", .num 4,
   .zeichen "{", .wort "tree", .zeichen "{", .wort "parent",
   .ident "elter", .zeichen ",", .wort "child",
   .ident "erstes_kind", .zeichen ",", .wort "sibling",
   .ident "naechstes", .zeichen "}", .wort "slot", .zeichen "{",
   .ident "b", .zeichen ":", .wort "bool", .zeichen ",",
   .zeichen "}", .zeichen "}", .ende]
theorem t29_lex :
    lex "table K count 4 { tree { parent elter, child erstes_kind, sibling naechstes } slot { b : bool, } }" =
      .ok tt29 := by
  decide
theorem t29 : beqTopTief (parseTopTief tt29)
    (.ok [.tableT "K" .none (.some (.lit 4)) .none .none false
      [.tTree [("parent", "elter"), ("child", "erstes_kind"),
        ("sibling", "naechstes")],
        .tSlot [{ fname := "b", ftyp := .atom "bool",
                   pos := .none, bezug := .none, wo := .none,
                   reserviert := false, byOps := false }]]]) = true := by
  decide
-- beispiele/01-tabelle.gab (the «B41b» edge beside a slot).
-- Rust: `Tabelle` with a `tree` member -- same shape.
end Gabbro.Grammatik.Parser
