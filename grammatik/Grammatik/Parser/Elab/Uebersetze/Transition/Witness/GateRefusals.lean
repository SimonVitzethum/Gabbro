module

public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil12
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice

@[expose] public section

namespace Gabbro.Grammatik.Parser.GateRefusals

open Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

/-!
  Witnesses for the refusals the gate/foreign-head elaboration restores
  (`Uebersetze/Teil/Teil11.lean` `uAxKlauseln`/`uAxKopf`, `Teil12.lean` `elabGateKopf`):
  `N464` (gate buffers), `N574` (foreign code parameters), `N064` (clobbered answer),
  `N067` (error map against the `or` channel), `N068` (`kernel` pairing), `N447` (double
  `stack`), `A005`/`A006` (foreign `arch` clauses). One positive and one negative fixture
  per rule, as short surface structures in the style of `ElementTiefProben3.t41`.

  Negative witnesses pin the exact diagnostic. The N464 positive buffer witnesses check
  the binding layer itself: a valid byte buffer still meets the independent, existing
  refusal of live byte capabilities when its signature is lowered. The scalar positive
  witnesses exercise the full head elaborator. No byte capability is admitted here.
-/

/-- A head is refused exactly when elaboration answers with an error. -/
@[expose] def refused : Except String α → Bool
  | .error _ => true
  | .ok _ => false

/-- The exact refusal of a head, for the witnesses that pin the diagnostic. -/
@[expose] def refusalIs : Except String α → String → Bool
  | .error e, want => strEq e want
  | .ok _, _ => false

/-! ## Fixtures -/

/-- The reason channel of the fixtures: two declared cases. -/
@[expose] def leseGrund : UWhy :=
  { name := "ReadError", cases := ["BadFd", "Interrupted"] }

/-- A clean binding: answer `rax` carried out, `rcx` destroyed, one mapped errno. -/
@[expose] def sauberBind : SBind :=
  { id := .lit 1, ins := [.binds "rdi" "fd", .binds "rdx" "len"],
    outs := [.reg "rax"], stack := [], dirty := ["rcx"],
    codes := [("EBADF", none, "BadFd")] }

/-- A clean contract: the length is held against the buffer it bounds. -/
@[expose] def sauberTor : SGate :=
  { pre := [.bin "<=" (.variable "len") (.built "lenof" [.variable "buf"])],
    post := [.bin "<=" .res (.variable "len")], uses := [.pure], cost := none }

/-- A clean scalar gate with one mapped errno. -/
@[expose] def lesetor : SSyscall :=
  { name := "gate_read",
    params := [("fd", .atom "u32"), ("len", .atom "u64")],
    res := some (.atom "u64"), fail := some "ReadError",
    way := .lit "linux" "x86_64" sauberBind
      (.assum "linux_read_contract" (.probe "sonde_read")),
    gate := { sauberTor with pre := [] } }

/-- A clean foreign body. -/
@[expose] def reineSig : FnSig :=
  { art := "extern", name := "fremd", params := [], res := none, fehler := none,
    klauseln := [.effs [.pure]] }

/-! ## N064: the answer register is not clobbered -/

theorem n064_positiv_zeuge :
    refused (elabGateKopf [] [] [leseGrund] [] lesetor) = false := by decide +kernel

/-- `rax` carries the answer out and stands under `clobbers` at once (gift 803). -/
@[expose] def zerstoerteAntwort : SSyscall :=
  { lesetor with way := (.lit "linux" "x86_64"
    ({ sauberBind with outs := [.reg "rax"], dirty := ["rax", "rcx"] })
    (.assum "linux_read_contract" (.probe "sonde_read"))) }

theorem n064_zeuge :
    refusalIs (elabGateKopf [] [] [leseGrund] [] zerstoerteAntwort)
      "syscall gate answer register clobbered without G form: rax" = true := by decide +kernel

/-! ## N067: the error map answers the declared channel -/

theorem n067_positiv_zeuge :
    refused (elabGateKopf [] [] [leseGrund] [] lesetor) = false := by decide +kernel

/-- An errno mapped to a reason the channel never declares (gift 804). -/
@[expose] def fremderGrund : SSyscall :=
  { lesetor with way := (.lit "linux" "x86_64"
    ({ sauberBind with codes := [("EBADF", none, "QuotenFehler")] })
    (.assum "linux_read_contract" (.probe "sonde_read"))) }

theorem n067_fremder_grund_zeuge :
    refusalIs (elabGateKopf [] [] [leseGrund] [] fremderGrund)
      "syscall gate error target without a declared case without G form: EBADF => QuotenFehler" = true := by decide +kernel

/-- Every listed errno has exactly one arm (gift 811). -/
@[expose] def doppelErrno : SSyscall :=
  { lesetor with way := (.lit "linux" "x86_64"
    ({ sauberBind with codes := [("EBADF", none, "BadFd"), ("EBADF", none, "Interrupted")] })
    (.assum "linux_read_contract" (.probe "sonde_read"))) }

theorem n067_doppelt_zeuge :
    refusalIs (elabGateKopf [] [] [leseGrund] [] doppelErrno)
      "syscall gate error listed twice without G form: EBADF" = true := by decide +kernel

/-- An errors map with no channel has nowhere to deliver (gift 812). -/
@[expose] def kanalLos : SSyscall :=
  { lesetor with fail := none }

theorem n067_ohne_kanal_zeuge :
    refusalIs (elabGateKopf [] [] [leseGrund] [] kanalLos)
      "syscall gate errors map without a reason channel without G form: EBADF" = true := by decide +kernel

/-- A channel that resolves nowhere is refused where the head is read. -/
@[expose] def unbekannterKanal : SSyscall :=
  { lesetor with fail := some "GibtEsNicht" }

theorem n067_unbekannter_kanal_zeuge :
    refusalIs (elabGateKopf [] [] [leseGrund] [] unbekannterKanal)
      "reason unknown: GibtEsNicht" = true := by decide +kernel

/-! ## N068: the `kernel` pairing is refused -/

theorem n068_positiv_zeuge :
    refused (elabGateKopf [] [] [leseGrund] [] lesetor) = false := by decide +kernel

/-- With `kernel` the call is paired with a Gabbro kernel's dispatch entry (gift 806). -/
@[expose] def kernpaarung : SSyscall :=
  { lesetor with way := .lit "linux" "x86_64" sauberBind (.core ["kern", "dispatch"]) }

theorem n068_zeuge :
    refusalIs (elabGateKopf [] [] [leseGrund] [] kernpaarung)
      "syscall gate kernel pairing without G form: kern::dispatch" = true := by decide +kernel

/-! ## N447: the stack clause stands at most once -/

/-- One handed-stack register, bound in the inputs and preserved (gift 1107 shape). -/
@[expose] def einStapel : SSyscall :=
  { lesetor with way := (.lit "linux" "x86_64"
    ({ sauberBind with ins := [.binds "rdi" "fd", .binds "rsi" "len"], stack := ["rsi"] })
    (.assum "linux_read_contract" (.probe "sonde_read"))) }

theorem n447_positiv_zeuge :
    refused (elabGateKopf [] [] [leseGrund] [] einStapel) = false := by decide +kernel

/-- Stack-ness claimed twice (gift 1108). -/
@[expose] def doppelStapel : SSyscall :=
  { lesetor with
    params := (lesetor.params ++ [("childStack", .atom "u64")]),
    way := (.lit "linux" "x86_64"
      ({ sauberBind with ins := [.binds "rdi" "fd", .binds "rsi" "len",
          .binds "rdx" "childStack"], stack := ["rsi", "rdx"] })
      (.assum "linux_read_contract" (.probe "sonde_read"))) }

theorem n447_zeuge :
    refusalIs (elabGateKopf [] [] [leseGrund] [] doppelStapel)
      "syscall gate second stack clause without G form: rdx" = true := by decide +kernel

/-! ## N464: a gate buffer points at bytes and carries its bound -/

/-- A byte buffer with its length bound passes the binding checks. -/
@[expose] def byteBuffer : SSyscall :=
  { lesetor with
    params := [("fd", .atom "u32"),
      ("buf", .ptr "normal" "w" (.atom "u8")), ("len", .atom "u64")],
    gate := sauberTor,
    way := (.lit "linux" "x86_64"
      ({ sauberBind with ins := [.binds "rdi" "fd", .binds "rsi" "buf", .binds "rdx" "len"] })
      (.assum "linux_read_contract" (.probe "sonde_read"))) }

theorem n464_positiv_zeuge :
    refused (uTorBindungPruef [] [] [leseGrund] byteBuffer) = false := by decide +kernel

/-- Parameter order does not affect the bound: the length may precede the buffer. -/
theorem n464_length_first_zeuge :
    refused (uTorBindungPruef [] [] [leseGrund]
      { byteBuffer with params := [("fd", .atom "u32"), ("len", .atom "u64"),
        ("buf", .ptr "normal" "w" (.atom "u8"))] }) = false := by decide +kernel

/-- A boolean cannot stand in for the integer length of a transfer. -/
theorem n464_non_numeric_length_zeuge :
    refusalIs (uTorBindungPruef [] [] [leseGrund]
      { byteBuffer with params := [("len", .atom "bool"),
        ("buf", .ptr "normal" "w" (.atom "u8"))] })
      "syscall gate buffer without length bound without G form: buf" = true := by decide +kernel

/-- A bound on another buffer does not bound this transfer. -/
theorem n464_other_buffer_zeuge :
    refusalIs (uTorBindungPruef [] [] [leseGrund]
      { byteBuffer with gate := { sauberTor with
        pre := [.bin "<=" (.variable "len") (.built "lenof" [.variable "other"])] } })
      "syscall gate buffer without length bound without G form: buf" = true := by decide +kernel

/-- A mirrored bound and a signed byte buffer express the same transfer limit. -/
theorem n464_mirrored_zeuge :
    refused (uTorBindungPruef [] [] [leseGrund]
      { byteBuffer with
        params := [("fd", .atom "u32"), ("buf", .ptr "normal" "w" (.atom "i8")),
          ("len", .atom "u64")],
        gate := { sauberTor with
          pre := [.bin ">=" (.built "lenof" [.variable "buf"]) (.variable "len")] } }) = false := by decide +kernel

/-- A binding variable supplies registers, not a waiver of the buffer contract. -/
theorem n464_via_zeuge :
    refusalIs (elabGateKopf [] [] [leseGrund] []
      { byteBuffer with way := .via "binding", gate := { sauberTor with pre := [] } }
      (spaces := ["normal"]))
      "syscall gate buffer without length bound without G form: buf" = true := by decide +kernel

theorem n464_via_positiv_zeuge :
    refused (uTorBindungPruef [] [] [leseGrund]
      { byteBuffer with way := .via "binding" }) = false := by decide +kernel

/-- Either conjunct is a promise of the complete precondition. -/
theorem n464_conjunction_zeuge :
    refused (uTorBindungPruef [] [] [leseGrund]
      { byteBuffer with gate := { sauberTor with
        pre := [.bin "&&" .tru (.bin "<=" (.variable "len") (.built "lenof" [.variable "buf"]))] } }) = false := by decide +kernel

/-- A bound in just one alternative supplies no unconditional transfer bound. -/
theorem n464_disjunction_zeuge :
    refusalIs (uTorBindungPruef [] [] [leseGrund]
      { byteBuffer with gate := { sauberTor with
        pre := [.bin "||" (.bin "<=" (.variable "len") (.built "lenof" [.variable "buf"])) .tru] } })
      "syscall gate buffer without length bound without G form: buf" = true := by decide +kernel

/-- Fixed-size transfers need a positive extent, as in the deleted checker's object case. -/
theorem n464_constant_zeuge :
    refused (uTorBindungPruef [] [] [leseGrund]
      { byteBuffer with gate := { sauberTor with
        pre := [.bin "<=" (.lit 4) (.built "lenof" [.variable "buf"])] } }) = false := by decide +kernel

theorem n464_zero_constant_zeuge :
    refusalIs (uTorBindungPruef [] [] [leseGrund]
      { byteBuffer with gate := { sauberTor with
        pre := [.bin "<=" (.lit 0) (.built "lenof" [.variable "buf"])] } })
      "syscall gate buffer without length bound without G form: buf" = true := by decide +kernel

/-- Passing N464 does not bypass the existing refusal of live byte capabilities. -/
theorem n464_lowering_refusal_zeuge :
    refusalIs (elabGateKopf [] [] [leseGrund] [] byteBuffer (spaces := ["normal"]))
      "live byte capability requires C01 value flow, C08 grant generations and C09 loans" = true := by decide +kernel

/-- A buffer of words where the kernel counts bytes (gift 1158). -/
@[expose] def wortPuffer : SSyscall :=
  { byteBuffer with
    params := [("fd", .atom "u32"), ("buf", .ptr "normal" "w" (.atom "u32")),
      ("len", .atom "u64")], gate := sauberTor }

theorem n464_wort_zeuge :
    refusalIs (elabGateKopf [] [] [leseGrund] [] wortPuffer (spaces := ["normal"]))
      "syscall gate buffer without byte pointee without G form: buf" = true := by decide +kernel

/-- A read buffer with no bound on what the kernel writes (gift 1155). -/
@[expose] def schrankenlos : SSyscall :=
  { byteBuffer with
    gate := { sauberTor with pre := [.bin "<=" (.variable "len") (.lit 1024)] } }

theorem n464_schranke_zeuge :
    refusalIs (elabGateKopf [] [] [leseGrund] [] schrankenlos (spaces := ["normal"]))
      "syscall gate buffer without length bound without G form: buf" = true := by decide +kernel

/-! ## N574: a foreign body takes no Gabbro code -/

/-- The walk finds a function pointer behind a pointer (gift 1393 shape). -/
theorem n574_weg_zeuge :
    sTypTraegtCode (.ptr "normal" "r" (.raw "fn ( t : u32 ) costs <= 1 ops")) = true := by decide +kernel

/-- The walk looks through tuples. -/
theorem n574_tupel_zeuge :
    sTypTraegtCode (.tuple [.atom "u32", .raw "fn ( t : u32 ) costs <= 1 ops"]) = true := by decide +kernel

/-- The walk spares the `entry fn` exception (`N575`--`N577`). -/
theorem n574_ausnahme_zeuge :
    sTypTraegtCode (.entry "params" none) = false := by decide +kernel

/-- A foreign body taking Gabbro code (gift 1392). -/
@[expose] def codeSig : FnSig :=
  { reineSig with
    name := "starte",
    params := [("f", .raw "fn ( d : u64 ) -> u32 costs <= 1 ops"), ("d", .atom "u64")] }

theorem n574_zeuge :
    refusalIs ((elabAxKopf [] [] [] [] false) codeSig)
      "foreign parameter with a function pointer without G form: f" = true := by decide +kernel

/-- A foreign body taking no code elaborates. -/
theorem n574_positiv_zeuge :
    refused ((elabAxKopf [] [] [] [] false) reineSig) = false := by decide +kernel

/-! ## A005/A006: a foreign `arch` names a declared, open machine -/

/-- An `arch` the unit declares (at its entry) is validated. -/
@[expose] def erklaerteSig : FnSig :=
  { reineSig with klauseln := [.effs [.pure], .arch "x86_64"] }

theorem a005_positiv_zeuge :
    refused ((elabAxKopf [] [] [] [] false (erklaert := ["x86_64"])) erklaerteSig) = false := by decide +kernel

/-- An `arch` no declaration names (gifts 805/1401 shape). -/
theorem a005_zeuge :
    refusalIs ((elabAxKopf [] [] [] [] false) erklaerteSig)
      "foreign arch without declared machine without G form: x86_64" = true := by decide +kernel

theorem a006_positiv_zeuge :
    refused ((elabAxKopf [] [] [] [] false (erklaert := ["x86_64"])) erklaerteSig) = false := by decide +kernel

/-- A sealed machine is refused as sealed, even where declared (gift 810 shape). -/
@[expose] def versiegelteSig : FnSig :=
  { reineSig with klauseln := [.effs [.pure], .arch "riscv64"] }

theorem a006_zeuge :
    refusalIs ((elabAxKopf [] [] [] [] false (erklaert := ["riscv64"])) versiegelteSig)
      "foreign arch sealed without G form: riscv64" = true := by decide +kernel

/-- A sealed machine at a gate is refused as sealed. -/
@[expose] def versiegeltesTor : SSyscall :=
  { lesetor with
    way := (.lit "linux" "riscv64" sauberBind
      (.assum "linux_read_contract" (.probe "sonde_read"))) }

theorem a006_tor_zeuge :
    refusalIs (elabGateKopf [] [] [leseGrund] [] versiegeltesTor)
      "syscall gate arch sealed without G form: riscv64" = true := by decide +kernel

/-! ## The declared set -/

/-- The collector reads entries, bodies and `= asm` machines, never claims. -/
@[expose] def beispielEinheit : List SItemTief :=
  [.entryT ({
      name := "e",
      vektor := none,
      via := none,
      arch := "x86_64",
      regIn := [],
      regOut := [],
      erhaelt := [],
      kills := [],
      stapel := "k",
      perCpu := true,
      ist := none,
      nest := none,
      dispatch := ["m", "w"] }),
   .protoT ({ reineSig with klauseln := [.effs [.pure], .arch "aarch64"] })]
