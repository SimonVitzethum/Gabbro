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

  Shape of the evidence: `refused` below is `true` exactly for the refused heads; every
  negative witness pins its named error as well. Two frontiers stay open and are recorded
  here, not weakened around:

  * a byte-buffer gate that CARRIES its bound (`ptr<normal, w> u8` with
    `requires len <= lenof(buf)`) still falls downstream -- `uTypIn` refuses every live byte
    capability until the C01 value flow lands ("live byte capability requires C01 ..."). The
    `N464` check runs first, so the boundless buffer already falls by name; the full positive
    arrives with C01.
  * the `arch` of an `assume` declaration is not held here: `assumT` items never reach the
    head elaboration (their names alone travel into `UProg.annahmen`), and the item check
    (`uRestFehler`) is shared with `GabbroV` by definitional unfolding, so no hook fits
    without breaking that boundary. Gifts 462/463 stay for that wave.
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
  { id := .lit 1, ins := [.binds "rdi" "fd"],
    outs := [.reg "rax"], stack := [], dirty := ["rcx"],
    codes := [("EBADF", none, "BadFd")] }

/-- A clean contract: the length is held against the buffer it bounds. -/
@[expose] def sauberTor : SGate :=
  { pre := [.bin "<=" (.variable "len") (.built "lenof" [.variable "buf"])],
    post := [.bin "<=" .res (.variable "len")], uses := [.pure], cost := none }

/-- A clean gate: one length, one byte buffer beside it, one mapped errno. -/
@[expose] def lesetor : SSyscall :=
  { name := "gate_read",
    params := [("fd", .atom "u32"), ("len", .atom "u64")],
    res := some (.atom "u64"), fail := some "ReadError",
    way := .lit "linux" "x86_64" sauberBind
      (.assum "linux_read_contract" (.probe "sonde_read")),
    gate := sauberTor }

/-- A clean foreign body. -/
@[expose] def reineSig : FnSig :=
  { art := "extern", name := "fremd", params := [], res := none, fehler := none,
    klauseln := [.effs [.pure]] }

/-! ## N064: the answer register is not clobbered -/

theorem n064_positiv_zeuge :
    refused (elabGateKopf [] [] [leseGrund] [] lesetor) = false := by decide +kernel

/-- `rax` carries the answer out and stands under `clobbers` at once (gift 803). -/
@[expose] def zerstoerteAntwort : SSyscall :=
  { lesetor with way := .lit "linux" "x86_64"
    ({ sauberBind with outs := [.reg "rax"], dirty := ["rax", "rcx"] })
    (.assum "linux_read_contract" (.probe "sonde_read")) }

theorem n064_zeuge :
    refusalIs (elabGateKopf [] [] [leseGrund] [] zerstoerteAntwort)
      "syscall gate answer register clobbered without G form: rax" = true := by decide +kernel

/-! ## N067: the error map answers the declared channel -/

theorem n067_positiv_zeuge :
    refused (elabGateKopf [] [] [leseGrund] [] lesetor) = false := by decide +kernel

/-- An errno mapped to a reason the channel never declares (gift 804). -/
@[expose] def fremderGrund : SSyscall :=
  { lesetor with way := .lit "linux" "x86_64"
    ({ sauberBind with codes := [("EBADF", none, "QuotenFehler")] })
    (.assum "linux_read_contract" (.probe "sonde_read")) }

theorem n067_fremder_grund_zeuge :
    refusalIs (elabGateKopf [] [] [leseGrund] [] fremderGrund)
      "syscall gate error target without a declared case without G form: EBADF => QuotenFehler" = true := by decide +kernel

/-- Every listed errno has exactly one arm (gift 811). -/
@[expose] def doppelErrno : SSyscall :=
  { lesetor with way := .lit "linux" "x86_64"
    ({ sauberBind with codes := [("EBADF", none, "BadFd"), ("EBADF", none, "Interrupted")] })
    (.assum "linux_read_contract" (.probe "sonde_read")) }

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

/-- One handed-stack register, bound, kept and answered (gift 1107 shape). -/
@[expose] def einStapel : SSyscall :=
  { lesetor with way := .lit "linux" "x86_64"
    ({ sauberBind with stack := ["rsi"] })
    (.assum "linux_read_contract" (.probe "sonde_read")) }

theorem n447_positiv_zeuge :
    refused (elabGateKopf [] [] [leseGrund] [] einStapel) = false := by decide +kernel

/-- Stack-ness claimed twice (gift 1108). -/
@[expose] def doppelStapel : SSyscall :=
  { lesetor with way := .lit "linux" "x86_64"
    ({ sauberBind with stack := ["rsi", "rsi"] })
    (.assum "linux_read_contract" (.probe "sonde_read")) }

theorem n447_zeuge :
    refusalIs (elabGateKopf [] [] [leseGrund] [] doppelStapel)
      "syscall gate second stack clause without G form: rsi" = true := by decide +kernel

/-! ## N464: a gate buffer points at bytes and carries its bound -/

/-- A gate with no pointer parameter owes no buffer clause. -/
theorem n464_positiv_zeuge :
    refused (elabGateKopf [] [] [leseGrund] [] lesetor) = false := by decide +kernel

/-- A buffer of words where the kernel counts bytes (gift 1158). -/
@[expose] def wortPuffer : SSyscall :=
  { lesetor with
    params := [("fd", .atom "u32"), ("buf", .ptr "normal" "w" (.atom "u32")),
      ("len", .atom "u64")] }

theorem n464_wort_zeuge :
    refusalIs (elabGateKopf [] [] [leseGrund] [] wortPuffer)
      "syscall gate buffer without byte pointee without G form: buf" = true := by decide +kernel

/-- A read buffer with no bound on what the kernel writes (gift 1155). -/
@[expose] def schrankenlos : SSyscall :=
  { lesetor with
    params := [("fd", .atom "u32"), ("buf", .ptr "normal" "w" (.atom "u8")),
      ("len", .atom "u64")],
    gate := { sauberTor with pre := [.bin "<=" (.variable "len") (.lit 1024)] } }

theorem n464_schranke_zeuge :
    refusalIs (elabGateKopf [] [] [leseGrund] [] schrankenlos)
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
  { reineSig with name := "starte",
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

/-- A sealed machine is refused as sealed, even where declared (gift 810 shape). -/
@[expose] def versiegelteSig : FnSig :=
  { reineSig with klauseln := [.effs [.pure], .arch "riscv64"] }

theorem a006_zeuge :
    refusalIs ((elabAxKopf [] [] [] [] false (erklaert := ["riscv64"])) versiegelteSig)
      "foreign arch sealed without G form: riscv64" = true := by decide +kernel

/-- A sealed machine at a gate is refused as sealed. -/
@[expose] def versiegeltesTor : SSyscall :=
  { lesetor with way := .lit "linux" "riscv64" sauberBind
    (.assum "linux_read_contract" (.probe "sonde_read")) }

theorem a006_tor_zeuge :
    refusalIs (elabGateKopf [] [] [leseGrund] [] versiegeltesTor)
      "syscall gate arch sealed without G form: riscv64" = true := by decide +kernel

/-! ## The declared set -/

/-- The collector reads entries, bodies and `= asm` machines, never claims. -/
@[expose] def beispielEinheit : List SItemTief :=
  [.entryT { name := "e", vektor := none, via := none, arch := "x86_64", regIn := [],
    regOut := [], erhaelt := [], kills := [], stapel := "k", perCpu := true, ist := none,
    nest := none, dispatch := ["m", "w"] },
   .protoT { reineSig with klauseln := [.effs [.pure], .arch "aarch64"] }]

theorem erklaerte_arch_zeuge :
    uErklaerteArch beispielEinheit = ["x86_64"] := by decide +kernel

end Gabbro.Grammatik.Parser.GateRefusals
