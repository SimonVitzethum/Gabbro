/-
  File:      Grammatik/Parser/Item/ElementTiefProben3.lean
  Subject:   T3 PART 3: the `decide` probes for the deep item
               readers, part 3 of 7 (tt30..tt50).

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
end Gabbro.Grammatik.Parser
