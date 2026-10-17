/-
  File:      Grammatik/Parser/ElementTiefProben.lean
  Subject:   T3 PART 3: the `decide` probes for the deep item
               readers.

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

def tt01 : List Token :=
  [.wort "table", .ident "Zustand", .wort "count", .num 4,
   .zeichen "{", .wort "slot", .zeichen "{", .ident "bereit",
   .zeichen ":", .wort "u32", .zeichen ",", .zeichen "}",
   .zeichen "}", .ende]
theorem t01_lex :
    lex "table Zustand count 4 { slot { bereit : u32, } }" =
      .ok tt01 := by
  decide
theorem t01 : beqTopTief (parseTopTief tt01)
    (.ok [.tableT "Zustand" (.some (.lit 4)) .none .none false
      [.tSlot [{ fname := "bereit", ftyp := .atom "u32",
                  pos := .none, bezug := .none, wo := .none,
                  reserviert := false, byOps := false }]]]) = true := by
  decide
-- beispiele/112-register-traeger-bewacht.gab (the `Zustand`
-- table). Rust: `Tabelle` with one slot field -- same shape.
def tt02 : List Token :=
  [.wort "lock", .ident "Sperre", .wort "protects", .zeichen "{",
   .ident "Zustand", .zeichen "}", .wort "rank", .num 0,
   .zeichen ";", .ende]
theorem t02_lex :
    lex "lock Sperre protects { Zustand } rank 0;" = .ok tt02 := by
  decide
theorem t02 : beqTopTief (parseTopTief tt02)
    (.ok [.lockT "Sperre" [.variable "Zustand"] (.lit 0)
      .none .none .none .none]) = true := by
  decide
-- beispiele/112 (the `Sperre` lock). Rust: `Lock` with one
-- carrier and a bare rank -- same shape.
def tt03 : List Token :=
  [.wort "device", .ident "Geraet", .zeichen "(", .ident "basis",
   .zeichen ":", .wort "u64", .zeichen ")", .wort "at",
   .wort "mmio", .zeichen "{", .wort "reg", .ident "ST",
   .zeichen ":", .wort "u32", .zeichen "@", .num 0,
   .wort "class", .wort "r", .wort "depends", .zeichen "{",
   .ident "Zustand", .zeichen "}", .zeichen "}", .ende]
theorem t03_lex :
    lex "device Geraet(basis : u64) at mmio { reg ST : u32 @0x00 class r depends { Zustand } }" =
      .ok tt03 := by
  decide
theorem t03 : beqTopTief (parseTopTief tt03)
    (.ok [.devT "Geraet" [("basis", .atom "u64")] "mmio"
      [.reg { name := "ST", rtyp := .atom "u32",
                   addr := .lit 0, klasse := "r", stage := [],
                   felder := [], voraus := .none,
                   elseF := .none,
                   abhaengt := [["Zustand"]] }]]) = true := by
  decide
-- beispiele/112 (the `Geraet` device). Rust: `Device` with one
-- parameter and one `depends` register -- same shape.
def tt04 : List Token :=
  [.wort "impl", .wort "fn", .ident "lesen", .zeichen "(",
   .ident "d", .zeichen ":", .ident "Geraet", .zeichen ")",
   .zeichen "->", .wort "u32", .wort "requires", .ident "Held",
   .zeichen "(", .ident "Sperre", .zeichen ")", .wort "effects",
   .zeichen "{", .wort "reads", .ident "d", .zeichen "}",
   .wort "costs", .zeichen "<=", .num 8, .wort "ops",
   .zeichen "{", .wort "let", .ident "stand", .zeichen "=",
   .ident "d", .zeichen ".", .ident "ST", .zeichen ";",
   .wort "return", .ident "stand", .zeichen ";", .zeichen "}",
   .ende]
theorem t04_lex :
    lex "impl fn lesen(d : Geraet) -> u32 requires Held(Sperre) effects { reads d } costs <= 8 ops { let stand = d.ST; return stand; }" =
      .ok tt04 := by
  decide
theorem t04 : beqTopTief (parseTopTief tt04)
    (.ok [.fnT
      { art := "impl", name := "lesen", params := [("d", .atom "Geraet")],
        res := .some (.atom "u32"), fehler := .none,
        klauseln := [.needs (.call "Held" [.variable "Sperre"]),
          .effs [.reads (.variable "d")], .cost (.lit 8)] }
      (.block [.bind false "stand" .none (.field (.variable "d") "ST")]
        (.some (.ret (.some (.variable "stand")))))]) = true := by
  decide
-- beispiele/112 (the `lesen` reader). Rust: `Funktion` with one
-- `requires`, an `effects` and a `costs` clause -- same shape.
def tt05 : List Token :=
  [.wort "impl", .wort "fn", .ident "schreiben", .zeichen "(",
   .ident "i", .zeichen ":", .wort "index", .wort "into",
   .ident "Zustand", .zeichen ",", .wort "w", .zeichen ":",
   .wort "u32", .zeichen ")", .zeichen "->", .wort "u32",
   .wort "requires", .ident "Held", .zeichen "(", .ident "Sperre",
   .zeichen ")", .wort "effects", .zeichen "{", .wort "writes",
   .ident "Zustand", .zeichen "}", .wort "costs", .zeichen "<=",
   .num 8, .wort "ops", .zeichen "{", .ident "Zustand",
   .zeichen ".", .wort "slots", .zeichen "[", .ident "i",
   .zeichen "]", .zeichen ".", .ident "bereit", .zeichen "=",
   .wort "w", .zeichen ";", .wort "return", .num 0,
   .zeichen ";", .zeichen "}", .ende]
theorem t05_lex :
    lex "impl fn schreiben(i : index into Zustand, w : u32) -> u32 requires Held(Sperre) effects { writes Zustand } costs <= 8 ops { Zustand.slots[i].bereit = w; return 0; }" =
      .ok tt05 := by
  decide
theorem t05 : beqTopTief (parseTopTief tt05)
    (.ok [.fnT
      { art := "impl", name := "schreiben",
        params := [("i", .index false "Zustand"), ("w", .atom "u32")],
        res := .some (.atom "u32"), fehler := .none,
        klauseln := [.needs (.call "Held" [.variable "Sperre"]),
          .effs [.writes (.variable "Zustand")], .cost (.lit 8)] }
      (.block [.set
        (.field (.index (.field (.variable "Zustand") "slots")
          (.variable "i")) "bereit")
        "=" (.variable "w")]
        (.some (.ret (.some (.lit 0)))))]) = true := by
  decide
-- beispiele/112 (the `schreiben` writer). Rust: `Funktion` over
-- an `index into` parameter -- same shape.
def tt06 : List Token :=
  [.wort "use", .ident "beispiel", .zeichen "::",
   .ident "adressen", .zeichen "::", .ident "Pa", .zeichen ";",
   .ende]
theorem t06_lex :
    lex "use beispiel::adressen::Pa;" = .ok tt06 := by
  decide
theorem t06 : beqTopTief (parseTopTief tt06)
    (.ok [.useT ["beispiel", "adressen", "Pa"]]) = true := by
  decide
-- beispiele/29-undurchsichtig.gab:42. Rust: `Use` -- same shape
-- (the path rides split here, raw in `SItem`).
def tt07 : List Token :=
  [.wort "opaque", .wort "type", .ident "Pa", .zeichen "=",
   .wort "u64", .zeichen ";", .ende]
theorem t07_lex :
    lex "opaque type Pa = u64;" = .ok tt07 := by
  decide
theorem t07 : beqTopTief (parseTopTief tt07)
    (.ok [.typeT ["opaque"] "Pa" [] [] (.some (.atom "u64"))]) = true := by
  decide
-- beispiele/01-tabelle.gab:18. Rust: `Typ` with the `opaque`
-- flag -- same shape.
def tt08 : List Token :=
  [.wort "type", .ident "Zaehler", .zeichen "=", .wort "u32",
   .wort "in", .num 0, .zeichen "..", .num 65535, .zeichen ";",
   .ende]
theorem t08_lex :
    lex "type Zaehler = u32 in 0 .. 65535;" = .ok tt08 := by
  decide
theorem t08 : beqTopTief (parseTopTief tt08)
    (.ok [.typeT [] "Zaehler" [] []
      (.some (.range (.atom "u32") (.lit 0) (.lit 65535) false))]) = true := by
  decide
-- beispiele/01-tabelle.gab:16. Rust: `Typ` over a ranged
-- integer -- same shape.
def tt09 : List Token :=
  [.wort "tagged", .wort "type", .ident "ObjektArt", .zeichen "=",
   .zeichen "{", .ident "Speicher", .zeichen "(", .ident "Pa",
   .zeichen ")", .zeichen ",", .ident "Endpunkt", .zeichen "(",
   .ident "EpId", .zeichen ")", .zeichen ",", .ident "Faden",
   .zeichen "(", .ident "FadenId", .zeichen ")", .zeichen ",",
   .ident "Antwort", .zeichen "(", .ident "EpId", .zeichen ")",
   .zeichen "}", .zeichen ";", .ende]
theorem t09_lex :
    lex "tagged type ObjektArt = { Speicher(Pa), Endpunkt(EpId), Faden(FadenId), Antwort(EpId) };" =
      .ok tt09 := by
  decide
theorem t09 : beqTopTief (parseTopTief tt09)
    (.ok [.typeT ["tagged"] "ObjektArt" [] [] (.some (.raw
      "{ Speicher ( Pa ) , Endpunkt ( EpId ) , Faden ( FadenId ) , Antwort ( EpId ) } "))]) = true := by
  decide
-- beispiele/01-tabelle.gab:22. Rust: `Typ` over variants -- the
-- payload types ride raw and balanced (see CUTS).
def tt10 : List Token :=
  [.wort "linear", .wort "ghost", .wort "type",
   .ident "QueuePhase", .wort "order", .zeichen "{",
   .ident "setup", .zeichen ",", .ident "live", .zeichen "}",
   .zeichen ";", .ende]
theorem t10_lex :
    lex "linear ghost type QueuePhase order { setup, live };" =
      .ok tt10 := by
  decide
theorem t10 : beqTopTief (parseTopTief tt10)
    (.ok [.typeT ["linear", "ghost"] "QueuePhase" [] ["setup", "live"]
      .none]) = true := by
  decide
-- beispiele/02-geraet.gab:115. Rust: `Typ` with a mark order --
-- same shape.
def tt11 : List Token :=
  [.wort "const", .ident "NSLOTS", .zeichen ":", .wort "u32",
   .zeichen "=", .num 4096, .zeichen ";", .ende]
theorem t11_lex :
    lex "const NSLOTS : u32 = 4096;" = .ok tt11 := by
  decide
theorem t11 : beqTopTief (parseTopTief tt11)
    (.ok [.constT "NSLOTS" (.atom "u32") (.one (.lit 4096))]) = true := by
  decide
-- beispiele/01-tabelle.gab:10. Rust: `Konst` -- same shape.
def tt12 : List Token :=
  [.wort "static", .wort "mut", .ident "zaehler", .zeichen ":",
   .wort "u32", .zeichen "=", .num 0, .zeichen ";", .ende]
theorem t12_lex :
    lex "static mut zaehler : u32 = 0;" = .ok tt12 := by
  decide
theorem t12 : beqTopTief (parseTopTief tt12)
    (.ok [.globT true "zaehler" (.atom "u32") (.one (.lit 0)) .none .none
      false]) = true := by
  decide
-- beispiele/110-fussgarantie.gab:12. Rust: `Statisch` -- same
-- shape.
def tt13 : List Token :=
  [.wort "static", .ident "KERNZAHL", .zeichen ":", .wort "u32",
   .zeichen "=", .num 64, .wort "section", .text ".rodata",
   .zeichen ";", .ende]
theorem t13_lex :
    lex "static KERNZAHL : u32 = 64 section \".rodata\";" =
      .ok tt13 := by
  decide
theorem t13 : beqTopTief (parseTopTief tt13)
    (.ok [.globT false "KERNZAHL" (.atom "u32") (.one (.lit 64)) .none
      (.some ".rodata") false]) = true := by
  decide
-- beispiele/05-nebenlaeufigkeit.gab:44. Rust: `Statisch` with a
-- section -- same shape.
def tt14 : List Token :=
  [.wort "static", .wort "mut", .ident "zaehl", .zeichen ":",
   .wort "u32", .zeichen "=", .num 0, .wort "shared",
   .zeichen ";", .ende]
theorem t14_lex :
    lex "static mut zaehl : u32 = 0 shared;" = .ok tt14 := by
  decide
theorem t14 : beqTopTief (parseTopTief tt14)
    (.ok [.globT true "zaehl" (.atom "u32") (.one (.lit 0)) .none .none true]) = true := by
  decide
-- Synthetic (no corpus occurrence, measured 2026-09-13): the
-- `shared` tail of `staticdecl`. Rust: `Statisch`.
def tt15 : List Token :=
  [.wort "extern", .wort "fn", .ident "speicher_freigeben",
   .zeichen "(", .ident "p", .zeichen ":", .ident "Pa",
   .zeichen ")", .wort "effects", .zeichen "{", .wort "writes",
   .ident "halde", .zeichen "}", .wort "costs", .zeichen "<=",
   .num 64, .wort "ops", .zeichen ";", .ende]
theorem t15_lex :
    lex "extern fn speicher_freigeben(p : Pa) effects { writes halde } costs <= 64 ops;" =
      .ok tt15 := by
  decide
theorem t15 : beqTopTief (parseTopTief tt15)
    (.ok [.protoT
      { art := "extern", name := "speicher_freigeben",
        params := [("p", .atom "Pa")], res := .none,
        fehler := .none,
        klauseln := [.effs [.writes (.variable "halde")],
          .cost (.lit 64)] }]) = true := by
  decide
-- beispiele/01-tabelle.gab (the `speicher_freigeben` foreign
-- body). Rust: `Funktion` without a body -- same shape.
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
    (.ok [.tableT "Verzeichnis" (.some (.variable "N")) .none .none
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
    (.ok [.tableT "T" (.some (.lit 4)) .none .none false
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
    (.ok [.tableT "K" (.some (.lit 4)) .none .none false
      [.tTree [("parent", "elter"), ("child", "erstes_kind"),
        ("sibling", "naechstes")],
        .tSlot [{ fname := "b", ftyp := .atom "bool",
                   pos := .none, bezug := .none, wo := .none,
                   reserviert := false, byOps := false }]]]) = true := by
  decide
-- beispiele/01-tabelle.gab (the «B41b» edge beside a slot).
-- Rust: `Tabelle` with a `tree` member -- same shape.
def tt30 : List Token :=
  [.wort "table", .ident "T", .wort "count", .num 4,
   .zeichen "{", .wort "slot", .zeichen "{", .ident "b",
   .zeichen ":", .wort "bool", .zeichen ",", .zeichen "}",
   .wort "invariant", .ident "inv", .wort "cost", .ident "O",
   .zeichen "(", .num 1, .zeichen ")", .wort "runs",
   .wort "online", .zeichen ":", .ident "T", .zeichen ".",
   .wort "slots", .zeichen "[", .ident "i", .zeichen "]",
   .zeichen ".", .ident "b", .zeichen ";", .zeichen "}",
   .ende]
theorem t30_lex :
    lex "table T count 4 { slot { b : bool, } invariant inv cost O(1) runs online : T.slots[i].b; }" =
      .ok tt30 := by
  decide
theorem t30 : beqTopTief (parseTopTief tt30)
    (.ok [.tableT "T" (.some (.lit 4)) .none .none false [.tSlot [{ fname := "b", ftyp := .atom "bool", pos := .none, bezug := .none, wo := .none, reserviert := false, byOps := false }], .tInv { name := "inv", kosten := .lit 1, online := true, proof := .none, pred := (.field (.index (.field (.variable "T") "slots") (.variable "i")) "b") }]]) = true := by
  decide
-- The `invariant` member shape is beispiele/01-tabelle.gab (the
-- header row); the `pred` is synthetic and quantifier-free --
-- quantified predicates ride no `SExpr` shape (see CUTS).
def tt31 : List Token :=
  [.wort "atomic", .ident "fertig", .zeichen ":", .wort "bool",
   .wort "publishes", .zeichen "{", .ident "bericht",
   .zeichen "}", .wort "release", .zeichen ";", .ende]
theorem t31_lex :
    lex "atomic fertig : bool publishes { bericht } release;" =
      .ok tt31 := by
  decide
theorem t31 : beqTopTief (parseTopTief tt31)
    (.ok [.atomT "fertig" (.atom "bool")
      (.some [.variable "bericht"]) (.some "release") .none]) = true := by
  decide
-- beispiele/11-grammatikbefunde.gab:13. Rust: `Atomic` with a
-- payload and an ordering -- same shape.
def tt32 : List Token :=
  [.wort "atomic", .ident "AVAIL_IDX", .zeichen ":", .wort "u32",
   .wort "release", .wort "observed", .wort "by",
   .ident "karte_liest_nach_dem_index", .zeichen ";", .ende]
theorem t32_lex :
    lex "atomic AVAIL_IDX : u32 release observed by karte_liest_nach_dem_index;" =
      .ok tt32 := by
  decide
theorem t32 : beqTopTief (parseTopTief tt32)
    (.ok [.atomT "AVAIL_IDX" (.atom "u32") .none (.some "release")
      (.some "karte_liest_nach_dem_index")]) = true := by
  decide
-- beispiele/41-handschlag.gab:49. Rust: `Atomic` with an
-- `observed by` assumption -- same shape.
def tt33 : List Token :=
  [.wort "rcu", .ident "BACCT", .wort "protects", .zeichen "{",
   .ident "Konten", .zeichen "}", .wort "reclaims", .ident "frei",
   .zeichen ";", .ende]
theorem t33_lex :
    lex "rcu BACCT protects { Konten } reclaims frei;" = .ok tt33 := by
  decide
theorem t33 : beqTopTief (parseTopTief tt33)
    (.ok [.rcuT "BACCT" [.variable "Konten"]
      (.some (.variable "frei"))]) = true := by
  decide
-- beispiele/31-rcu.gab:24. Rust: `Rcu` with a reclaim site --
-- same shape.
def tt34 : List Token :=
  [.wort "group", .ident "Zustellung", .wort "over", .zeichen "{",
   .ident "Endpunkte", .zeichen ",", .ident "Faeden",
   .zeichen "}", .zeichen "{", .wort "invariant",
   .ident "wartende_haben_grund", .wort "cost", .ident "O",
   .zeichen "(", .ident "n", .zeichen ")", .wort "runs",
   .wort "offline", .zeichen ":", .ident "Faeden",
   .zeichen ".", .wort "slots", .zeichen "[",
   .ident "wartende", .zeichen "]", .zeichen ".",
   .ident "gruende", .zeichen ">", .num 0, .zeichen ";",
   .zeichen "}", .ende]
theorem t34_lex :
    lex "group Zustellung over { Endpunkte, Faeden } { invariant wartende_haben_grund cost O(n) runs offline : Faeden.slots[wartende].gruende > 0; }" =
      .ok tt34 := by
  decide
theorem t34 : beqTopTief (parseTopTief tt34)
    (.ok [.groupT "Zustellung" ["Endpunkte", "Faeden"] [{ name := "wartende_haben_grund", kosten := (.variable "n"), online := false, proof := .none, pred := (.bin ">" (.field (.index (.field (.variable "Faeden") "slots") (.variable "wartende")) "gruende") (.lit 0)) }]]) = true := by
  decide
-- The `group` frame is beispiele/17-gruppe-ueber-zwei-sperren.gab:42-47;
-- the `pred` is simplified (the corpus body quantifies -- see CUTS).
def tt35 : List Token :=
  [.wort "concurrent", .zeichen "{", .ident "read_a",
   .zeichen ",", .ident "read_c", .zeichen "}", .zeichen ";",
   .ende]
theorem t35_lex :
    lex "concurrent { read_a, read_c };" = .ok tt35 := by
  decide
theorem t35 : beqTopTief (parseTopTief tt35)
    (.ok [.concT [["read_a"], ["read_c"]]]) = true := by
  decide
-- beispiele/108-disjoint-start-locks.gab (the declared pair).
-- Rust: `Concurrent` -- same shape.
def tt36 : List Token :=
  [.wort "accumulates", .ident "fehlerzahl", .zeichen ":",
   .wort "u32", .wort "merge", .wort "add", .wort "per",
   .wort "cpu", .ident "NKERNE", .zeichen ";", .ende]
theorem t36_lex :
    lex "accumulates fehlerzahl : u32 merge add per cpu NKERNE;" =
      .ok tt36 := by
  decide
theorem t36 : beqTopTief (parseTopTief tt36)
    (.ok [.accT "fehlerzahl" (.atom "u32") "add"
      (.some (.variable "NKERNE"))]) = true := by
  decide
-- beispiele/23-akkumulatoren.gab:45. Rust: `Accumulates` with a
-- cell count -- same shape.
def tt37 : List Token :=
  [.wort "walk", .ident "Seitentabelle", .wort "levels", .num 4,
   .zeichen "{", .wort "node", .zeichen ":", .zeichen "[",
   .ident "Pte", .zeichen ";", .num 512, .zeichen "]",
   .zeichen ",", .wort "down", .zeichen ":", .ident "rahmen",
   .wort "when", .ident "it", .zeichen ".", .ident "praesent",
   .zeichen "&&", .zeichen "!", .ident "it", .zeichen ".",
   .ident "gross", .zeichen ",", .wort "leaf", .zeichen ":",
   .ident "it", .zeichen ".", .ident "praesent", .zeichen "&&",
   .zeichen "!", .ident "it", .zeichen ".", .ident "gross",
   .zeichen ",", .zeichen "}", .ende]
theorem t37_lex :
    lex "walk Seitentabelle levels 4 { node : [Pte; 512], down : rahmen when it.praesent && !it.gross, leaf : it.praesent && !it.gross, }" =
      .ok tt37 := by
  decide
theorem t37 : beqTopTief (parseTopTief tt37)
    (.ok [.walkT { name := "Seitentabelle", stufen := (.lit 4), node := (.array (.atom "Pte") (.lit 512)), dname := "rahmen", dwhen := (.bin "&&" (.field (.variable "it") "praesent") (.un "!" (.field (.variable "it") "gross"))), blatt := (.bin "&&" (.field (.variable "it") "praesent") (.un "!" (.field (.variable "it") "gross"))), invarianten := [] }]) = true := by
  decide
-- beispiele/07-eintritt-und-boot.gab:26-29 (invariants dropped --
-- they quantify, see CUTS). Rust: `Walk` with node, down and
-- leaf -- same shape.
def tt38 : List Token :=
  [.wort "entry", .ident "entry_a", .wort "vector", .num 128,
   .wort "arch", .ident "x86_64", .zeichen "{", .wort "regs",
   .wort "in", .zeichen "{", .zeichen "}", .wort "regs",
   .wort "out", .zeichen "{", .zeichen "}", .wort "preserves",
   .zeichen "{", .ident "rbx", .zeichen "}", .wort "clobbers",
   .zeichen "{", .ident "rcx", .zeichen "}", .wort "stack",
   .ident "ka", .wort "per", .wort "cpu", .wort "nested",
   .wort "never", .wort "dispatch", .ident "beispiel",
   .zeichen "::", .ident "lockfree_entry_roots", .zeichen "::",
   .ident "distribute_a", .zeichen ";", .zeichen "}", .ende]
theorem t38_lex :
    lex "entry entry_a vector 0x80 arch x86_64 { regs in { } regs out { } preserves { rbx } clobbers { rcx } stack ka per cpu nested never dispatch beispiel::lockfree_entry_roots::distribute_a; }" =
      .ok tt38 := by
  decide
theorem t38 : beqTopTief (parseTopTief tt38)
    (.ok [.entryT { name := "entry_a", vektor := (.some (.lit 128)), via := .none, arch := "x86_64", regIn := [], regOut := [], erhaelt := ["rbx"], kills := ["rcx"], stapel := "ka", perCpu := true, ist := .none, nest := (.some "never"), dispatch := ["beispiel", "lockfree_entry_roots", "distribute_a"] }]) = true := by
  decide
-- beispiele/109-lockfree-entry-roots.gab (the `entry_a` root).
-- Rust: `Entry` with empty register maps -- same shape.
def tt39 : List Token :=
  [.wort "entrust", .ident "jitpuffer", .wort "at",
   .ident "Gastbild", .wort "arch", .ident "x86_64",
   .zeichen "{", .wort "regs", .wort "in", .zeichen "{",
   .ident "eintritt", .zeichen ":", .ident "rdi", .zeichen ",",
   .ident "kappe", .zeichen ":", .ident "rsi", .zeichen ",",
   .zeichen "}", .wort "stack", .ident "gaststapel",
   .wort "assume", .ident "gast_bleibt_in_seinem_raum",
   .zeichen ";", .zeichen "}", .ende]
theorem t39_lex :
    lex "entrust jitpuffer at Gastbild arch x86_64 { regs in { eintritt : rdi, kappe : rsi, } stack gaststapel assume gast_bleibt_in_seinem_raum; }" =
      .ok tt39 := by
  decide
theorem t39 : beqTopTief (parseTopTief tt39)
    (.ok [.trustT "jitpuffer" "Gastbild" "x86_64"
      [.binds "eintritt" "rdi", .binds "kappe" "rsi"]
      "gaststapel" "gast_bleibt_in_seinem_raum"]) = true := by
  decide
-- beispiele/25-entrust.gab:32-36. Rust: `Entrust` -- same shape.
def tt40 : List Token :=
  [.wort "boot", .ident "multiboot1", .wort "arch",
   .ident "x86_64", .zeichen "{", .wort "step",
   .ident "stapelzeiger", .zeichen "=", .ident "boot_stapel_oben",
   .zeichen ";", .wort "step", .ident "bootinfo_retten",
   .zeichen "(", .ident "ebx", .zeichen ")", .zeichen ";",
   .wort "dispatch", .ident "beispiel", .zeichen "::",
   .ident "eintritt", .zeichen "::", .ident "rust_eintritt",
   .zeichen ";", .zeichen "}", .ende]
theorem t40_lex :
    lex "boot multiboot1 arch x86_64 { step stapelzeiger = boot_stapel_oben; step bootinfo_retten(ebx); dispatch beispiel::eintritt::rust_eintritt; }" =
      .ok tt40 := by
  decide
theorem t40 : beqTopTief (parseTopTief tt40)
    (.ok [.bootT "multiboot1" "x86_64"
      [.set "stapelzeiger" (.variable "boot_stapel_oben"),
        .call ["bootinfo_retten"] [.variable "ebx"]]
      ["beispiel", "eintritt", "rust_eintritt"]]) = true := by
  decide
-- beispiele/07-eintritt-und-boot.gab:86-97 (two steps stand for
-- the ten). Rust: `Boot` with steps and a dispatch -- same shape.
def tt41 : List Token :=
  [.wort "syscall", .ident "write", .zeichen "(", .ident "fd",
   .zeichen ":", .wort "u64", .zeichen ",", .ident "buf",
   .zeichen ":", .wort "u64", .zeichen ",", .ident "len",
   .zeichen ":", .wort "u64", .zeichen ")", .zeichen "->",
   .wort "u64", .wort "or", .ident "IoError", .wort "abi",
   .ident "linux", .wort "arch", .ident "x86_64", .wort "number",
   .num 1, .wort "regs", .wort "in", .zeichen "{",
   .ident "rdi", .zeichen "=", .ident "fd", .zeichen ",",
   .ident "rsi", .zeichen "=", .ident "buf", .zeichen ",",
   .ident "rdx", .zeichen "=", .ident "len", .zeichen "}",
   .wort "regs", .wort "out", .zeichen "{", .ident "rax",
   .zeichen "}", .wort "clobbers", .zeichen "{", .ident "rcx",
   .zeichen ",", .ident "r11", .zeichen "}", .wort "errors",
   .zeichen "{", .ident "EBADF", .zeichen "=>", .ident "BadFd",
   .zeichen ",", .ident "EINTR", .zeichen "=>",
   .ident "Interrupted", .zeichen ",", .ident "EAGAIN",
   .zeichen "=>", .ident "WouldBlock", .zeichen "}",
   .wort "requires", .ident "len", .zeichen "<=", .num 1024,
   .wort "ensures", .wort "result", .zeichen "<=", .ident "len",
   .wort "effects", .zeichen "{", .wort "pure", .zeichen "}",
   .wort "assume", .ident "linux_write_contract", .wort "falsifier",
   .ident "sonde_write", .zeichen ";", .ende]
theorem t41_lex :
    lex "syscall write(fd : u64, buf : u64, len : u64) -> u64 or IoError abi linux arch x86_64 number 1 regs in { rdi = fd, rsi = buf, rdx = len } regs out { rax } clobbers { rcx, r11 } errors { EBADF => BadFd, EINTR => Interrupted, EAGAIN => WouldBlock } requires len <= 1024 ensures result <= len effects { pure } assume linux_write_contract falsifier sonde_write;" =
      .ok tt41 := by
  decide
theorem t41 : beqTopTief (parseTopTief tt41)
    (.ok [.callT { name := "write", params := [("fd", (.atom "u64")), ("buf", (.atom "u64")), ("len", (.atom "u64"))], res := (.some (.atom "u64")), fail := (.some "IoError"), way := .lit "linux" "x86_64" { id := (.lit 1), ins := [.binds "rdi" "fd", .binds "rsi" "buf", .binds "rdx" "len"], outs := [.reg "rax"], stack := [], dirty := ["rcx", "r11"], codes := [("EBADF", .none, "BadFd"), ("EINTR", .none, "Interrupted"), ("EAGAIN", .none, "WouldBlock")] } (.assum "linux_write_contract" (.probe "sonde_write")), gate := { pre := [(.bin "<=" (.variable "len") (.lit 1024))], post := [(.bin "<=" .res (.variable "len"))], uses := [.pure], cost := .none } }]) = true := by
  decide
-- beispiele/90-syscall-errno.gab:22-31. Rust: `Syscall` with an
-- error channel, maps and contracts -- same shape.
def tt42 : List Token :=
  [.wort "library", .wort "fn", .ident "sum", .zeichen "(",
   .ident "t", .zeichen ":", .wort "ptr", .zeichen "<",
   .wort "normal", .zeichen ",", .wort "r", .zeichen ">",
   .ident "SumTab", .zeichen ")", .zeichen "->", .wort "u32",
   .wort "in", .num 0, .zeichen "..", .num 400, .wort "payload",
   .ident "SumTab", .wort "ensures", .wort "result",
   .zeichen "<=", .num 400, .wort "effects", .zeichen "{",
   .wort "reads", .ident "t", .zeichen ".", .wort "slots",
   .zeichen "}", .wort "costs", .zeichen "<=", .num 16,
   .wort "ops", .zeichen "{", .wort "return", .ident "t",
   .zeichen ".", .wort "slots", .zeichen "[", .num 0,
   .zeichen "]", .zeichen ".", .ident "v", .zeichen "+",
   .ident "t", .zeichen ".", .wort "slots", .zeichen "[",
   .num 1, .zeichen "]", .zeichen ".", .ident "v",
   .zeichen "+", .ident "t", .zeichen ".", .wort "slots",
   .zeichen "[", .num 2, .zeichen "]", .zeichen ".",
   .ident "v", .zeichen "+", .ident "t", .zeichen ".",
   .wort "slots", .zeichen "[", .num 3, .zeichen "]",
   .zeichen ".", .ident "v", .zeichen ";", .zeichen "}",
   .ende]
theorem t42_lex :
    lex "library fn sum(t : ptr<normal, r> SumTab) -> u32 in 0 .. 400 payload SumTab ensures result <= 400 effects { reads t.slots } costs <= 16 ops { return t.slots[0].v + t.slots[1].v + t.slots[2].v + t.slots[3].v; }" =
      .ok tt42 := by
  decide
theorem t42 : beqTopTief (parseTopTief tt42)
    (.ok [.fnT { art := "library", name := "sum", params := [(("t", (.ptr "normal" "r" (.atom "SumTab"))))], res := (.some ((.range (.atom "u32") (.lit 0) (.lit 400) false))), fehler := .none, klauseln := [(.load ["SumTab"]), (.gives ((.bin "<=" .res (.lit 400)))), (.effs [(.reads ((.field (.variable "t") "slots")))]), (.cost (.lit 16))] } (.block [] (.some (.ret (.some ((.bin "+" ((.bin "+" ((.bin "+" ((.field ((.index ((.field ((.variable "t")) "slots")) (.lit 0))) "v")) ((.field ((.index ((.field ((.variable "t")) "slots")) (.lit 1))) "v")))) ((.field ((.index ((.field ((.variable "t")) "slots")) (.lit 2))) "v")))) ((.field ((.index ((.field ((.variable "t")) "slots")) (.lit 3))) "v"))))))))]) = true := by
  decide
-- beispiele/106-summe-uebersetzt.gab:16-23 (the `sum` library).
-- Rust: `Funktion` with a payload type and a ranged result --
-- same shape.
def tt43 : List Token :=
  [.wort "lock", .ident "KAPPEN", .wort "protects", .zeichen "{",
   .ident "belegt", .zeichen ",", .ident "rechte", .zeichen ",",
   .ident "objekt", .zeichen "}", .wort "rank", .num 0,
   .wort "held", .zeichen "<=", .num 3, .wort "ops",
   .wort "shared", .wort "held", .zeichen "<=", .num 4,
   .wort "ops", .zeichen ";", .ende]
theorem t43_lex :
    lex "lock KAPPEN protects { belegt, rechte, objekt } rank 0 held <= 3 ops shared held <= 4 ops;" =
      .ok tt43 := by
  decide
theorem t43 : beqTopTief (parseTopTief tt43)
    (.ok [.lockT "KAPPEN" [.variable "belegt", .variable "rechte", .variable "objekt"] (.lit 0) (.some (.lit 3)) (.some (.lit 4)) .none .none]) = true := by
  decide
-- beispiele/10-geteilte-sperre.gab (the `KAPPEN` reader-writer
-- lock). Rust: `Lock` with both held bounds -- same shape.
def tt44 : List Token :=
  [.wort "lock", .ident "KAPPEN", .wort "protects", .zeichen "{",
   .ident "eintraege", .zeichen ",", .ident "baum", .zeichen "}",
   .wort "rank", .num 0, .wort "held", .zeichen "<=",
   .num 400, .wort "ops", .wort "masks", .ident "irqs",
   .zeichen ";", .ende]
theorem t44_lex :
    lex "lock KAPPEN protects { eintraege, baum } rank 0 held <= 400 ops masks irqs;" =
      .ok tt44 := by
  decide
theorem t44 : beqTopTief (parseTopTief tt44)
    (.ok [.lockT "KAPPEN" [.variable "eintraege", .variable "baum"]
      (.lit 0) (.some (.lit 400)) .none (.some "irqs") .none]) = true := by
  decide
-- beispiele/01-tabelle.gab:31. Rust: `Lock` with a held bound
-- and an irq mask -- same shape.
def tt45 : List Token :=
  [.wort "device", .ident "D", .wort "at", .wort "mmio",
   .zeichen "{", .wort "bank", .ident "FRR", .wort "at",
   .ident "CAP", .zeichen ".", .ident "FRO", .zeichen "*",
   .num 16, .wort "stride", .num 16, .wort "count", .num 256,
   .zeichen "{", .wort "reg", .ident "FR_LO", .zeichen ":",
   .wort "u64", .zeichen "@", .num 0, .wort "class", .wort "rw",
   .wort "reg", .ident "FR_HI", .zeichen ":", .wort "u64",
   .zeichen "@", .num 8, .wort "class", .wort "rw",
   .zeichen "}", .zeichen "}", .ende]
theorem t45_lex :
    lex "device D at mmio { bank FRR at CAP.FRO * 16 stride 16 count 256 { reg FR_LO : u64 @0x0 class rw reg FR_HI : u64 @0x8 class rw } }" =
      .ok tt45 := by
  decide
theorem t45 : beqTopTief (parseTopTief tt45)
    (.ok [.devT "D" [] "mmio"
      [.bank "bank FRR at (CAP.FRO * 16) stride 16 count 256 { reg FR_LO : u64 @ 0 class rw reg FR_HI : u64 @ 8 class rw } "]]) = true := by
  decide
-- beispiele/02-geraet.gab:22-25 (the `FRR` bank). Rust: `Device`
-- with a `Bank` member -- the bank body rides raw (see CUTS).
def tt46 : List Token :=
  [.wort "device", .ident "Einheit", .zeichen "(", .ident "basis",
   .zeichen ":", .ident "Pa", .zeichen ")", .wort "at",
   .wort "mmio", .zeichen "{", .wort "mirrors", .ident "GCMD",
   .wort "from", .ident "GSTS", .zeichen ";", .wort "reg",
   .ident "GCMD", .zeichen ":", .wort "u32", .zeichen "@",
   .num 24, .wort "class", .wort "w", .wort "fields",
   .zeichen "{", .ident "SRTP", .zeichen "@", .num 30,
   .zeichen ",", .ident "TE", .zeichen "@", .num 31,
   .zeichen ",", .zeichen "}", .wort "transition",
   .ident "setze_rtp", .zeichen "{", .ident "GCMD", .zeichen ".",
   .ident "SRTP", .zeichen ":", .num 0, .zeichen "->",
   .num 1, .zeichen "}", .wort "requires", .ident "GSTS",
   .zeichen ".", .ident "TES", .zeichen "==", .num 0,
   .wort "effects", .zeichen "{", .wort "writes", .ident "GCMD",
   .zeichen "}", .zeichen "}", .ende]
theorem t46_lex :
    lex "device Einheit(basis : Pa) at mmio { mirrors GCMD from GSTS; reg GCMD : u32 @0x18 class w fields { SRTP @30, TE @31, } transition setze_rtp { GCMD.SRTP: 0 -> 1 } requires GSTS.TES == 0 effects { writes GCMD } }" =
      .ok tt46 := by
  decide
theorem t46 : beqTopTief (parseTopTief tt46)
    (.ok [.devT "Einheit" [("basis", (.atom "Pa"))] "mmio" [.copy (.variable "GCMD") (.variable "GSTS"), .reg { name := "GCMD", rtyp := (.atom "u32"), addr := (.lit 24), klasse := "w", stage := [], felder := [{ name := "SRTP", pos := "30", klasse := .none }, { name := "TE", pos := "31", klasse := .none }], voraus := .none, elseF := .none, abhaengt := [] }, .trans { tname := "setze_rtp", schritte := [((.field (.variable "GCMD") "SRTP"), (.lit 0), (.lit 1))], voraus := (.some ((.bin "==" ((.field (.variable "GSTS") "TES")) (.lit 0)))), wirkung := [(.writes (.variable "GCMD"))] }]]) = true := by
  decide
-- beispiele/20-falle-vier.gab (the `Einheit` device). Rust:
-- `Device` with `mirrors`, a bit-field register and a guarded
-- transition -- same shape.
def tt47 : List Token :=
  [.wort "profile", .zeichen "{", .wort "arch", .ident "x86_64",
   .zeichen ";", .wort "rounding", .ident "nearest",
   .zeichen ";", .wort "fp_contract", .ident "off", .zeichen ";",
   .wort "assume", .ident "plattform_takt_stabil", .zeichen ";",
   .zeichen "}", .zeichen ";", .ende]
theorem t47_lex :
    lex "profile { arch x86_64; rounding nearest; fp_contract off; assume plattform_takt_stabil; };" =
      .ok tt47 := by
  decide
theorem t47 : beqTopTief (parseTopTief tt47)
    (.ok [.profT false
      [.mode "arch" "x86_64",
        .mode "rounding" "nearest",
        .mode "fp_contract" "off",
        .assum "plattform_takt_stabil"]]) = true := by
  decide
-- beispiele/100-hardwareprofil.gab:50-55. Rust: `Profil` with
-- keyed modes and an assumption -- same shape.
def tt48 : List Token :=
  [.wort "requires", .wort "profile", .zeichen "{",
   .wort "arch", .ident "x86_64", .zeichen ";", .wort "assume",
   .ident "plattform_takt_stabil", .zeichen ";", .zeichen "}",
   .zeichen ";", .ende]
theorem t48_lex :
    lex "requires profile { arch x86_64; assume plattform_takt_stabil; };" =
      .ok tt48 := by
  decide
theorem t48 : beqTopTief (parseTopTief tt48)
    (.ok [.profT true
      [.mode "arch" "x86_64",
        .assum "plattform_takt_stabil"]]) = true := by
  decide
-- beispiele/100-hardwareprofil.gab:26-29. Rust: `ProfilBedarf`
-- -- same shape.
def tt49 : List Token :=
  [.wort "when", .ident "TESTBUILD", .wort "static", .wort "mut",
   .ident "hoechstmarke", .zeichen ":", .ident "Fuellstand",
   .zeichen "=", .num 0, .zeichen ";", .ende]
theorem t49_lex :
    lex "when TESTBUILD static mut hoechstmarke : Fuellstand = 0;" =
      .ok tt49 := by
  decide
theorem t49 : beqTopTief (parseTopTief tt49)
    (.ok [.gateT (.globT true "hoechstmarke" (.atom "Fuellstand")
      (.one (.lit 0)) .none .none false)]) = true := by
  decide
-- beispiele/52-baugatter.gab:61-62. Rust: a gated `Statisch` --
-- same shape.
def tt50 : List Token :=
  [.wort "const", .wort "fn", .ident "quad", .zeichen "(",
   .ident "i", .zeichen ":", .wort "u32", .wort "in", .num 0,
   .zeichen "..", .num 64, .zeichen ")", .zeichen "->",
   .wort "u32", .wort "effects", .zeichen "{", .wort "pure",
   .zeichen "}", .wort "costs", .zeichen "<=", .num 4,
   .wort "ops", .zeichen "{", .wort "return", .ident "i",
   .zeichen "*", .ident "i", .zeichen ";", .zeichen "}",
   .ende]
theorem t50_lex :
    lex "const fn quad(i : u32 in 0 .. 64) -> u32 effects { pure } costs <= 4 ops { return i * i; }" =
      .ok tt50 := by
  decide
theorem t50 : beqTopTief (parseTopTief tt50)
    (.ok [.fnT { art := "const", name := "quad", params := [(("i", (.range (.atom "u32") (.lit 0) (.lit 64) false)))], res := (.some (.atom "u32")), fehler := .none, klauseln := [(.effs [(.pure)]), (.cost (.lit 4))] } (.block [] (.some (.ret (.some (.bin "*" (.variable "i") (.variable "i"))))))]) = true := by
  decide
-- beispiele/92-const-squares.gab:11. Rust: `Funktion` with the
-- `const` modifier and a ranged parameter -- same shape.
def tt51 : List Token :=
  [.wort "impl", .wort "fn", .ident "freigeben", .zeichen "(",
   .ident "p", .zeichen ":", .wort "index", .wort "into",
   .ident "Buch", .zeichen ")", .wort "refines", .ident "ist_frei",
   .wort "requires", .ident "Held", .zeichen "(", .ident "BUCH",
   .zeichen ")", .zeichen ",", .ident "Buch", .zeichen ".",
   .wort "slots", .zeichen "[", .ident "p", .zeichen "]",
   .zeichen ".", .ident "belegt", .wort "effects", .zeichen "{",
   .wort "reads", .ident "Buch", .zeichen ".", .wort "slots",
   .zeichen ",", .wort "writes", .ident "Buch", .zeichen ".",
   .wort "slots", .zeichen ",", .wort "locks", .ident "BUCH",
   .zeichen "}", .wort "costs", .zeichen "<=", .num 8,
   .wort "ops", .zeichen "{", .ident "Buch", .zeichen ".",
   .wort "slots", .zeichen "[", .ident "p", .zeichen "]",
   .zeichen ".", .ident "belegt", .zeichen "=", .wort "false",
   .zeichen ";", .ident "Buch", .zeichen ".", .wort "slots",
   .zeichen "[", .ident "p", .zeichen "]", .zeichen ".",
   .ident "wert", .zeichen "=", .num 0, .zeichen ";",
   .zeichen "}", .ende]
theorem t51_lex :
    lex "impl fn freigeben(p : index into Buch) refines ist_frei requires Held(BUCH), Buch.slots[p].belegt effects { reads Buch.slots, writes Buch.slots, locks BUCH } costs <= 8 ops { Buch.slots[p].belegt = false; Buch.slots[p].wert = 0; }" =
      .ok tt51 := by
  decide
theorem t51 : beqTopTief (parseTopTief tt51)
    (.ok [.fnT { art := "impl", name := "freigeben", params := [("p", .index false "Buch")], res := .none, fehler := .none, klauseln := [.refs ["ist_frei"], .needs (.call "Held" [.variable "BUCH"]), .needs (.field (.index (.field (.variable "Buch") "slots") (.variable "p")) "belegt"), .effs [.reads (.field (.variable "Buch") "slots"), .writes (.field (.variable "Buch") "slots"), .locks false (.variable "BUCH")], .cost (.lit 8)] } (.block [.set (.field (.index (.field (.variable "Buch") "slots") (.variable "p")) "belegt") "=" .fls, .set (.field (.index (.field (.variable "Buch") "slots") (.variable "p")) "wert") "=" (.lit 0)] .none)]) = true := by
  decide
-- beispiele/50-verfeinerung.gab (the `freigeben` refinement).
-- Rust: `Funktion` with `refines`, two `requires` and three
-- effects -- same shape.
def tt52 : List Token :=
  [.wort "extern", .wort "fn", .ident "groesse_gemessen",
   .zeichen "(", .zeichen ")", .zeichen "->", .ident "Stapelgroesse",
   .wort "or", .ident "MessFehler", .wort "ensures",
   .wort "result", .zeichen ">=", .num 1, .wort "effects",
   .zeichen "{", .wort "reads", .ident "stapel", .zeichen "}",
   .zeichen ";", .ende]
theorem t52_lex :
    lex "extern fn groesse_gemessen() -> Stapelgroesse or MessFehler ensures result >= 1 effects { reads stapel };" =
      .ok tt52 := by
  decide
theorem t52 : beqTopTief (parseTopTief tt52)
    (.ok [.protoT { art := "extern", name := "groesse_gemessen", params := [], res := (.some (.atom "Stapelgroesse")), fehler := (.some "MessFehler"), klauseln := [(.gives ((.bin ">=" .res (.lit 1)))), (.effs [(.reads (.variable "stapel"))])] }]) = true := by
  decide
-- beispiele/06-annahmen.gab:163-165. Rust: `Funktion` with the
-- `or` error channel -- same shape.
def tt53 : List Token :=
  [.wort "prim", .wort "fn", .ident "wechseln", .zeichen "(",
   .ident "von", .zeichen ":", .wort "ptr", .zeichen "<",
   .wort "normal", .zeichen ",", .wort "rw", .zeichen ">",
   .ident "Kontext", .zeichen ",", .ident "nach", .zeichen ":",
   .wort "ptr", .zeichen "<", .wort "normal", .zeichen ",",
   .wort "r", .zeichen ">", .ident "Kontext", .zeichen ")",
   .zeichen "->", .wort "never", .wort "effects", .zeichen "{",
   .wort "writes", .ident "maschinenzustand", .zeichen ",",
   .wort "writes", .ident "stapel", .zeichen ",", .wort "diverges",
   .zeichen "}", .zeichen ";", .ende]
theorem t53_lex :
    lex "prim fn wechseln(von : ptr<normal, rw> Kontext, nach : ptr<normal, r> Kontext) -> never effects { writes maschinenzustand, writes stapel, diverges };" =
      .ok tt53 := by
  decide
theorem t53 : beqTopTief (parseTopTief tt53)
    (.ok [.protoT { art := "prim", name := "wechseln", params := [(("von", (.ptr "normal" "rw" (.atom "Kontext")))), (("nach", (.ptr "normal" "r" (.atom "Kontext"))))], res := (.some (.atom "never")), fehler := .none, klauseln := [(.effs [(.writes (.variable "maschinenzustand")), (.writes (.variable "stapel")), .loops])] }]) = true := by
  decide
-- beispiele/07-eintritt-und-boot.gab:148-149. Rust: `Funktion`
-- over `never` with a diverging effect -- same shape.
def tt54 : List Token :=
  [.wort "impl", .wort "fn", .ident "f", .zeichen "(",
   .zeichen ")", .wort "maintains", .ident "invA", .zeichen ",",
   .ident "invB", .wort "by", .wort "induction", .wort "over",
   .wort "descendants", .wort "of", .ident "s",
   .wort "section", .text ".text", .wort "arch", .ident "x86_64",
   .wort "advances", .ident "roh", .zeichen "->", .ident "mmu",
   .wort "retires", .ident "t", .wort "from", .wort "boot",
   .wort "falsifier", .ident "p", .zeichen ";", .ende]
theorem t54_lex :
    lex "impl fn f() maintains invA, invB by induction over descendants of s section \".text\" arch x86_64 advances roh -> mmu retires t from boot falsifier p;" =
      .ok tt54 := by
  decide
theorem t54 : beqTopTief (parseTopTief tt54)
    (.ok [.protoT { art := "impl", name := "f", params := [], res := .none, fehler := .none, klauseln := [(.keeps ["invA", "invB"]), (.induc "induction over descendants of s "), (.part ".text"), (.arch "x86_64"), (.moves "roh" "mmu"), (.quits "t from boot falsifier p")] }]) = true := by
  decide
-- Synthetic carrier for the remaining clause forms; each cites
-- its corpus shape: `maintains` (beispiele/01-tabelle.gab:94),
-- `by induction over` (beispiele/01-tabelle.gab:77),
-- `section`/`arch` (beispiele/36-asm.gab:27),
-- `advances a -> b` (beispiele/02-geraet.gab:129),
-- `retires` (beispiele/07-eintritt-und-boot.gab:137).
def tt55 : List Token :=
  [.wort "table", .ident "Halde", .wort "count", .num 1048576,
   .wort "backed", .ident "hinterlegt", .zeichen "{",
   .wort "slot", .zeichen "{", .ident "b", .zeichen ":",
   .wort "bool", .zeichen ",", .zeichen "}", .zeichen "}",
   .ende]
theorem t55_lex :
    lex "table Halde count 1048576 backed hinterlegt { slot { b : bool, } }" =
      .ok tt55 := by
  decide
theorem t55 : beqTopTief (parseTopTief tt55)
    (.ok [.tableT "Halde" (.some (.lit 1048576)) (.some "hinterlegt") .none false [.tSlot [{ fname := "b", ftyp := (.atom "bool"), pos := .none, bezug := .none, wo := .none, reserviert := false, byOps := false }]]]) = true := by
  decide
-- beispiele/28-reserve-und-hinterlegung.gab:19 (the header;
-- memory kinds are values, not checked here). Rust: `Tabelle`
-- with a `backed` bound -- same shape.

-- The variadic marker `...` (C-free lane, C2, 2026-09-30): lexed `..` `.`, skipped by the
-- parameter list -- every declared parameter stays, in order. Rust: `params_variadisch`.
def ttVar : List Token :=
  [.wort "extern", .wort "fn", .ident "druck", .zeichen "(",
   .ident "fmt", .zeichen ":", .ident "Text", .zeichen ",",
   .zeichen "..", .zeichen ".", .zeichen ",",
   .ident "a", .zeichen ":", .wort "u64", .zeichen ")",
   .wort "costs", .zeichen "<=", .num 8, .wort "ops", .zeichen ";", .ende]
theorem tVar_lex :
    lex "extern fn druck(fmt : Text, ..., a : u64) costs <= 8 ops;" = .ok ttVar := by
  decide
theorem tVar : beqTopTief (parseTopTief ttVar)
    (.ok [.protoT
      { art := "extern", name := "druck",
        params := [("fmt", .atom "Text"), ("a", .atom "u64")], res := .none,
        fehler := .none, klauseln := [.cost (.lit 8)] }]) = true := by
  decide
def ttEnd : List Token :=
  [.wort "module", .ident "beispiel112", .zeichen "{",
  .wort "table", .ident "Zustand", .wort "count", .num 4,
   .zeichen "{", .wort "slot", .zeichen "{", .ident "bereit",
   .zeichen ":", .wort "u32", .zeichen ",", .zeichen "}",
   .zeichen "}",
  .wort "lock", .ident "Sperre", .wort "protects", .zeichen "{",
   .ident "Zustand", .zeichen "}", .wort "rank", .num 0,
   .zeichen ";",
  .wort "device", .ident "Geraet", .zeichen "(", .ident "basis",
   .zeichen ":", .wort "u64", .zeichen ")", .wort "at",
   .wort "mmio", .zeichen "{", .wort "reg", .ident "ST",
   .zeichen ":", .wort "u32", .zeichen "@", .num 0,
   .wort "class", .wort "r", .wort "depends", .zeichen "{",
   .ident "Zustand", .zeichen "}", .zeichen "}",
  .wort "impl", .wort "fn", .ident "lesen", .zeichen "(",
   .ident "d", .zeichen ":", .ident "Geraet", .zeichen ")",
   .zeichen "->", .wort "u32", .wort "requires", .ident "Held",
   .zeichen "(", .ident "Sperre", .zeichen ")", .wort "effects",
   .zeichen "{", .wort "reads", .ident "d", .zeichen "}",
   .wort "costs", .zeichen "<=", .num 8, .wort "ops",
   .zeichen "{", .wort "let", .ident "stand", .zeichen "=",
   .ident "d", .zeichen ".", .ident "ST", .zeichen ";",
   .wort "return", .ident "stand", .zeichen ";", .zeichen "}",
  .wort "impl", .wort "fn", .ident "schreiben", .zeichen "(",
   .ident "i", .zeichen ":", .wort "index", .wort "into",
   .ident "Zustand", .zeichen ",", .wort "w", .zeichen ":",
   .wort "u32", .zeichen ")", .zeichen "->", .wort "u32",
   .wort "requires", .ident "Held", .zeichen "(", .ident "Sperre",
   .zeichen ")", .wort "effects", .zeichen "{", .wort "writes",
   .ident "Zustand", .zeichen "}", .wort "costs", .zeichen "<=",
   .num 8, .wort "ops", .zeichen "{", .ident "Zustand",
   .zeichen ".", .wort "slots", .zeichen "[", .ident "i",
   .zeichen "]", .zeichen ".", .ident "bereit", .zeichen "=",
   .wort "w", .zeichen ";", .wort "return", .num 0,
   .zeichen ";", .zeichen "}",
  .zeichen "}", .ende]
set_option maxHeartbeats 1600000 in
theorem tEnd_lex :
    lex "module beispiel112 { table Zustand count 4 { slot { bereit : u32, } } lock Sperre protects { Zustand } rank 0; device Geraet(basis : u64) at mmio { reg ST : u32 @0x00 class r depends { Zustand } } impl fn lesen(d : Geraet) -> u32 requires Held(Sperre) effects { reads d } costs <= 8 ops { let stand = d.ST; return stand; } impl fn schreiben(i : index into Zustand, w : u32) -> u32 requires Held(Sperre) effects { writes Zustand } costs <= 8 ops { Zustand.slots[i].bereit = w; return 0; } }" =
      .ok ttEnd := by
  decide
theorem tEnd : beqTopTief (parseTopTief ttEnd)
    (.ok [.modT "beispiel112" [
.tableT "Zustand" (.some (.lit 4)) .none .none false
      [.tSlot [{ fname := "bereit", ftyp := .atom "u32",
                  pos := .none, bezug := .none, wo := .none,
                  reserviert := false, byOps := false }]],
.lockT "Sperre" [.variable "Zustand"] (.lit 0)
      .none .none .none .none,
.devT "Geraet" [("basis", .atom "u64")] "mmio"
      [.reg { name := "ST", rtyp := .atom "u32",
                   addr := .lit 0, klasse := "r", stage := [],
                   felder := [], voraus := .none,
                   elseF := .none,
                   abhaengt := [["Zustand"]] }],
.fnT
      { art := "impl", name := "lesen", params := [("d", .atom "Geraet")],
        res := .some (.atom "u32"), fehler := .none,
        klauseln := [.needs (.call "Held" [.variable "Sperre"]),
          .effs [.reads (.variable "d")], .cost (.lit 8)] }
      (.block [.bind false "stand" .none (.field (.variable "d") "ST")]
        (.some (.ret (.some (.variable "stand"))))),
.fnT
      { art := "impl", name := "schreiben",
        params := [("i", .index false "Zustand"), ("w", .atom "u32")],
        res := .some (.atom "u32"), fehler := .none,
        klauseln := [.needs (.call "Held" [.variable "Sperre"]),
          .effs [.writes (.variable "Zustand")], .cost (.lit 8)] }
      (.block [.set
        (.field (.index (.field (.variable "Zustand") "slots")
          (.variable "i")) "bereit")
        "=" (.variable "w")]
        (.some (.ret (.some (.lit 0)))))]]) = true := by
  decide
-- beispiele/112-register-traeger-bewacht.gab, whole file (38 lines): the smallest whole corpus file with a table, a lock and contracted functions. Module, table, lock, device and both function bodies parse end to end with nothing skipped.
def tt56 : List Token :=
  [.wort "const", .ident "T", .zeichen ":", .zeichen "[",
   .wort "u32", .zeichen ";", .num 2, .zeichen "]",
   .zeichen "=", .zeichen "[", .num 1, .zeichen ",", .num 2,
   .zeichen "]", .zeichen ";", .ende]
theorem t56_lex :
    lex "const T : [u32; 2] = [1, 2];" = .ok tt56 := by
  decide
theorem t56 : beqTopTief (parseTopTief tt56)
    (.ok [.constT "T" (.array (.atom "u32") (.lit 2))
      (.rows [.one (.lit 1), .one (.lit 2)])]) = true := by
  decide
-- beispiele/92-const-squares.gab:13 (shortened from 64
-- elements; the lane-111 const-table literal). Rust: `Konst`
-- over an array type with an `arraylit` value -- same shape.
def tt57 : List Token :=
  [.wort "pub", .wort "module", .ident "a", .zeichen "::",
   .ident "b", .zeichen "{", .wort "use", .ident "c",
   .zeichen "::", .ident "d", .zeichen ";", .zeichen "}",
   .ende]
theorem t57_lex :
    lex "pub module a::b { use c::d; }" = .ok tt57 := by
  decide
theorem t57 : beqTopTief (parseTopTief tt57)
    (.ok [.modT "a::b" [.useT ["c", "d"]]]) = true := by
  decide
-- Synthetic (no `pub module` in the corpus, measured
-- 2026-09-13): the `pub` prefix and nested members. Rust:
-- `Modul` with a `Use` member.
def tt58 : List Token :=
  [.wort "device", .ident "Ring", .zeichen "(", .ident "basis",
   .zeichen ":", .wort "u64", .zeichen ")", .wort "at",
   .wort "mmio", .zeichen "{", .wort "reg", .ident "AVAIL_IDX",
   .zeichen ":", .wort "u16", .wort "wrapping", .zeichen "@",
   .num 258, .wort "class", .wort "rw", .wort "reg",
   .ident "RING_LEN", .zeichen ":", .wort "u16", .zeichen "@",
   .num 260, .wort "class", .wort "r", .zeichen "}", .ende]
theorem t58_lex :
    lex "device Ring(basis : u64) at mmio { reg AVAIL_IDX : u16 wrapping @0x102 class rw reg RING_LEN : u16 @0x104 class r }" =
      .ok tt58 := by
  decide
theorem t58 : beqTopTief (parseTopTief tt58)
    (.ok [.devT "Ring" [("basis", (.atom "u64"))] "mmio" [.reg { name := "AVAIL_IDX", rtyp := (.wrap (.atom "u16")), addr := (.lit 258), klasse := "rw", stage := [], felder := [], voraus := .none, elseF := .none, abhaengt := [] }, .reg { name := "RING_LEN", rtyp := (.atom "u16"), addr := (.lit 260), klasse := "r", stage := [], felder := [], voraus := .none, elseF := .none, abhaengt := [] }]]) = true := by
  decide
-- beispiele/12-umlaufendes-register.gab (the `Ring` device).
-- Rust: `Device` with a `wrapping` register -- the width rides
-- the type (`wrap`), not the register.

end Gabbro.Grammatik.Parser

/-
  CUTS: what is not proved here.

  * The tree shapes above are checked by kernel `Bool` evaluation
    (`beqTopTief … = true`), not by a soundness theorem for
    `beqSItemTief` -- the same cut as item 11 of the CUTS block in
    `Parser/Ausdruck.lean`.
  * Every shape difference against `crates/gabbro-syntax` found by
    these probes is booked in the CUTS block of
    `Parser/ElementTief.lean`; the probe comments name the Rust
    counterpart (`ast.rs`) of each form.
  * Corpus text is quoted comment-free (comments lex away); the
    five shortened probes (`t40` two of ten boot steps, `t56`
    two of 64 array elements, `t34`/`t30` simplified invariant
    bodies, `t37` dropped quantified walk invariants) pin the
    surrounding shape, not the dropped text -- each says so.
  * Synthetic probes (no corpus occurrence, measured 2026-09-13):
    `t14` (`static … shared`), `t18` (bare-proto `deadline`
    carrier), `t23` (`state` item), `t54` (the clause-comb
    carrier), `t57` (`pub module`). The `t30`/`t34` invariant
    bodies are synthetic and quantifier-free; every corpus
    invariant quantifies (see CUTS item 1 of
    `Parser/ElementTief.lean`).
  * Heartbeat budgets: `t26_lex` runs at 800000 (default 200000
    fails), `tEnd_lex` at 1600000 -- the price of whole-item
    lexing through `String ==` over byte arrays (the same
   finder as lane 135 finding 6: tree comparisons run on
    character lists, source text does not).
  * New single-line proof terms (`t42`, `t50`, `t51`, `t30`,
    `t34`, `t38`, `t41`, `t58`): hand-nested `SExpr` terms are
    balanced mechanically (a paren counter over the line) before
    probing -- two committed probes carried a slip each.
-/

#print axioms Gabbro.Grammatik.Parser.tEnd
