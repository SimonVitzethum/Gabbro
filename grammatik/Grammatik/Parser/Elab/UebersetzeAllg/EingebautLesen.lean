module

public import Grammatik.Parser.Elab.Uebersetze
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

/-
  C13 reading-side fixtures (`_zeuge`): the surface forms of the closed integer builtins, of `count`, of `sizeof`
  and of the numeric `aligned` read by the exporter (`uSeite`, `uSichert`, `uSpTy`), generic in nothing but the
  context they name:
  * every builtin at the declared storage width of a parameter, a static, a field read through a pointer, a field
    read at a table, an arena element, a conversion `T(e)` and an alias of a word type (`uSpeicherBreite`);
  * the refusals: an unknown width (a parameter without a bare word type, a literal, a field without a declared
    width), and `old`/`result` inside a builtin or a count body (`seiteAltErg`);
  * `count` as a NUMBER at the `+ - *` layer of a comparison over each of its domains (`slots of`, `descendants of`,
    `elems of`), with a guarded read and a read of a static inside the body, and the refusals (an unmodelled
    domain, an unheld guard);
  * `sizeof` of a type name, a parameter and a field, `aligned` with a positive constant and its refusals.
  Every statement is checked by evaluation (`rfl`).
-/

namespace Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.Uebersetze

namespace EingebautLesen

/-- The empty context the fixtures extend. -/
def lb : UCtx :=
  { names := [], kinds := [], types := [], tabs := [], locks := [], held := [], res := none, fname := "f", alias := [], lits := [] }

/-- Four numeric parameters `a b n z`: `a`, `b` and `n` are bare bytes, `z` has no declared storage width. -/
def cw : UCtx :=
  { lb with names := ["a", "b", "n", "z"], kinds := [.int, .int, .int, .int], types := [.int 0 255, .int 0 255, .int 0 7, .int 0 255], bits := [8, 8, 8, 0] }

/-- A table `T` of four slots with a byte field `v` of declared storage width `8` and a field `w` without one. -/
def tt : UTab :=
  { name := "T", count := 4, cols := [("v", (0, 255)), ("w", (0, 100))], breiten := [("v", 8)] }

/-- An arena `A` of three halfwords. -/
def aa : UTab :=
  { name := "A", count := 3, cols := [("wert", (0, 65535))], arena := true, breiten := [("wert", 16)] }

/-- A static byte `G`. -/
def gg : UGlob := { name := "G", ty := .int 0 255, init := 0, breite := 8 }

/-- The context of a function with a pointer parameter `p` to `T` and the unit's table, arena and static. -/
def ct : UCtx :=
  { lb with names := ["p"], kinds := [.ptr 0 true], types := [.ptr 0 true], tabs := [tt, aa], globs := [gg] }

/-! ## The builtins at a declared storage width -/

theorem wrap_lesen_zeuge :
    uSeite cw (.bin "+%" (.variable "a") (.variable "b")) = .ok (.ib2 .addW 8 (.param "a") (.param "b")) ∧
    uSeite cw (.bin "-%" (.variable "a") (.variable "b")) = .ok (.ib2 .subW 8 (.param "a") (.param "b")) ∧
    uSeite cw (.bin "*%" (.variable "a") (.variable "b")) = .ok (.ib2 .mulW 8 (.param "a") (.param "b")) ∧
    uSeite cw (.bin "<<%" (.variable "a") (.variable "n")) = .ok (.ib2 .shlW 8 (.param "a") (.param "n")) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The saturating addition carries no width: its range is the operands'. -/
theorem saettigung_lesen_zeuge :
    uSeite cw (.bin "+|" (.variable "a") (.variable "b")) = .ok (.ib2 .addS 0 (.param "a") (.param "b")) := by rfl

theorem bitzaehler_lesen_zeuge :
    uSeite cw (.call "clz" [.variable "a"]) = .ok (.ib1 .clz 8 (.param "a")) ∧
    uSeite cw (.call "ctz" [.variable "a"]) = .ok (.ib1 .ctz 8 (.param "a")) ∧
    uSeite cw (.call "log2_floor" [.variable "a"]) = .ok (.ib1 .log2Floor 8 (.param "a")) ∧
    uSeite cw (.call "popcount" [.variable "a"]) = .ok (.ib1 .popcount 8 (.param "a")) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem drehung_lesen_zeuge :
    uSeite cw (.call "rotl" [.variable "a", .variable "n"]) = .ok (.ib2 .rotl 8 (.param "a") (.param "n")) ∧
    uSeite cw (.call "rotr" [.variable "a", .variable "n"]) = .ok (.ib2 .rotr 8 (.param "a") (.param "n")) :=
  ⟨rfl, rfl⟩

/-- A conversion `u16(a)` names the declared width `16`; the byte swap keeps the conversion as its operand. -/
theorem bswap_umwandlung_lesen_zeuge :
    uSeite cw (.call "bswap" [.call "u16" [.variable "a"]]) = .ok (.ib1 .bswap 16 (.conv 0 65535 (.param "a"))) := by
  rfl

/-- An alias of `u32 in 0 .. 65535` is stored in 32 bits: the width is the declaration's, not the range's. -/
theorem alias_lesen_zeuge :
    uSeite { cw with alias := [("W", (0, 65535)), ("W#bits", (32, 32))] }
        (.call "bswap" [.call "W" [.variable "a"]]) =
      .ok (.ib1 .bswap 32 (.conv 0 65535 (.param "a"))) := by rfl

/-- A static of a declared word type. -/
theorem statik_lesen_zeuge :
    uSeite ct (.call "popcount" [.variable "G"]) = .ok (.ib1 .popcount 8 (.glob "G")) := by rfl

/-- A field read through a pointer parameter, and at the table by its name. -/
theorem feld_lesen_zeuge :
    uSeite ct (.call "popcount" [.field (.index (.field (.variable "p") "slots") (.lit 0)) "v"]) =
      .ok (.ib1 .popcount 8 (.slot "p" "v" (.lit 0))) ∧
    uSeite ct (.call "popcount" [.field (.index (.field (.variable "T") "slots") (.lit 2)) "v"]) =
      .ok (.ib1 .popcount 8 (.tab "T" "v" (.lit 2))) := ⟨rfl, rfl⟩

/-- An arena element carries the width of its declared element type. -/
theorem arena_lesen_zeuge :
    uSeite ct (.call "popcount" [.index (.variable "A") (.lit 1)]) =
      .ok (.ib1 .popcount 16 (.tab "A" "wert" (.lit 1))) := by rfl

/-! ## Refusals: the width is never guessed -/

/-- A parameter without a declared word storage has no width. -/
theorem breite_unbekannt_lesen_zeuge :
    uSeite cw (.call "popcount" [.variable "z"]) = .error "builtin of unknown width" := by rfl

/-- A literal has no storage width. -/
theorem literal_lesen_zeuge :
    uSeite cw (.call "popcount" [.lit 5]) = .error "builtin of unknown width" ∧
    uSeite cw (.bin "+%" (.lit 1) (.lit 2)) = .error "builtin of unknown width" := ⟨rfl, rfl⟩

/-- A field without a declared storage width has none, even though its range is a byte. -/
theorem feld_ohne_breite_lesen_zeuge :
    uSeite ct (.call "popcount" [.field (.index (.field (.variable "p") "slots") (.lit 0)) "w"]) =
      .error "builtin of unknown width" := by rfl

/-- `old` and `result` inside a builtin operand or a count body are found, so a body refuses them. -/
theorem alt_erg_zeuge :
    seiteAltErg (.ib1 .clz 8 .erg) = true ∧
    seiteAltErg (.zaehle "T" "x" (.cmp ">" .erg (.lit 1))) = true ∧
    seiteAltErg (.zaehle "T" "x" (.cmp ">" (.param "x") (.lit 1))) = false := ⟨rfl, rfl, rfl⟩

/-! ## `count` as a number -/

/-- The table `T` of the count fixtures, with an index binder `x` read as `T.slots[x].v`. -/
def feldLesen : SExpr := .field (.index (.field (.variable "T") "slots") (.variable "x")) "v"

def zaehleSlots : SExpr := .ext .count ["x", "slots"] [.variable "T", .bin ">" feldLesen (.lit 10)]

def zaehleSlotsU : USide := .zaehle "T" "x" (.cmp ">" (.tab "T" "v" (.param "x")) (.lit 10))

/-- The count of a table's slots against a number, in either order, and under `+ - *`. -/
theorem zaehle_slots_lesen_zeuge :
    uSichert { lb with tabs := [tt] } (.bin "==" zaehleSlots (.lit 2)) = .ok (.cmp "==" zaehleSlotsU (.lit 2)) ∧
    uSichert { lb with tabs := [tt] } (.bin "<=" (.lit 1) zaehleSlots) = .ok (.cmp "<=" (.lit 1) zaehleSlotsU) ∧
    uSichert { lb with tabs := [tt] } (.bin "<=" (.bin "+" zaehleSlots (.lit 1)) (.lit 3)) =
      .ok (.cmp "<=" (.add zaehleSlotsU (.lit 1)) (.lit 3)) ∧
    uSichert { lb with tabs := [tt] } (.bin "<" (.bin "-" (.lit 3) zaehleSlots) (.bin "*" zaehleSlots (.lit 2))) =
      .ok (.cmp "<" (.sub (.lit 3) zaehleSlotsU) (.mul zaehleSlotsU (.lit 2))) := ⟨rfl, rfl, rfl, rfl⟩

/-- A count in a count body: the inner binder shadows the outer one. -/
theorem zaehle_verschachtelt_lesen_zeuge :
    uSichert { lb with tabs := [tt] }
        (.bin ">=" (.ext .count ["x", "slots"] [.variable "T", .bin "==" zaehleSlots (.lit 1)]) (.lit 0)) =
      .ok (.cmp ">=" (.zaehle "T" "x" (.cmp "==" zaehleSlotsU (.lit 1))) (.lit 0)) := by rfl

/-- A read of a guarded table inside the body needs the lock; held, it is read as everywhere else. -/
theorem zaehle_bewacht_lesen_zeuge :
    uSichert { lb with tabs := [tt], locks := [{ name := "L", rank := 1, guard := ["T"] }] }
        (.bin "==" zaehleSlots (.lit 2)) = .error "access without held guard" ∧
    uSichert { lb with tabs := [tt], locks := [{ name := "L", rank := 1, guard := ["T"] }], held := ["L"] }
        (.bin "==" zaehleSlots (.lit 2)) = .ok (.cmp "==" zaehleSlotsU (.lit 2)) := ⟨rfl, rfl⟩

/-- A static read inside the body is the static, not a binder. -/
theorem zaehle_global_lesen_zeuge :
    uSichert { lb with tabs := [tt], globs := [gg] }
        (.bin "==" (.ext .count ["x", "slots"] [.variable "T", .bin "<" feldLesen (.variable "G")]) (.lit 1)) =
      .ok (.cmp "==" (.zaehle "T" "x" (.cmp "<" (.tab "T" "v" (.param "x")) (.glob "G"))) (.lit 1)) := by rfl

/-- The tree domains: the table of the edge, the binder, the declared edge field, whether the walk is reversed, the
    outer seed (an index parameter) and the body. -/
def baumU : UTab := { name := "T", count := 3, cols := [("next", (0, 0))], opts := [("next", 0)], kanten := [("child", "next")] }

def baumCtx : UCtx :=
  { lb with names := ["root"], kinds := [.index 0], types := [.index 3], tabs := [baumU] }

theorem zaehle_baum_lesen_zeuge :
    uSichert baumCtx (.bin "==" (.ext .count ["x", "descendants"] [.variable "root", .tru]) (.lit 3)) =
      .ok (.cmp "==" (.zaehleBaum "T" "x" "next" false (.param "root") .tru) (.lit 3)) ∧
    uSichert baumCtx (.bin "==" (.ext .count ["x", "ancestors"] [.variable "root", .tru]) (.lit 1)) =
      .ok (.cmp "==" (.zaehleBaum "T" "x" "next" true (.param "root") .tru) (.lit 1)) := ⟨rfl, rfl⟩

/-- The array domain: the binder is an INDEX into `0 ..< n` (LANGUAGE section 6); the body reads the element. -/
def feldCtx : UCtx :=
  { lb with names := ["data"], kinds := [.wert], types := [.arr (.int 0 255) 2] }

theorem zaehle_feld_lesen_zeuge :
    uSichert feldCtx
        (.bin "==" (.ext .count ["i", "elems"] [.variable "data", .bin "==" (.index (.variable "data") (.variable "i")) (.lit 1)])
          (.lit 1)) =
      .ok (.cmp "==" (.zaehleFeld (.param "data") "i" (.cmp "==" (.idx (.param "data") (.param "i")) (.lit 1))) (.lit 1)) := by
  rfl

/-- A domain without a canonical expansion, and a count in a position that is no comparison, are refused. -/
theorem zaehle_abgelehnt_lesen_zeuge :
    uSichert { lb with tabs := [tt] }
        (.bin "==" (.ext .count ["x", "queue"] [.variable "T", .tru]) (.lit 1)) =
      .error "source export: count domain lacks a canonical G expansion" ∧
    uSichert { lb with tabs := [tt] } zaehleSlots = .error "ensures clause without G form" := ⟨rfl, rfl⟩

/-! ## `sizeof` and `aligned` -/

/-- The declared size of a type name, a parameter and a field. -/
theorem sizeof_lesen_zeuge :
    uSeite cw (.built "sizeof" [.variable "u32"]) = .ok (.lit 4) ∧
    uSeite cw (.built "sizeof" [.variable "u8"]) = .ok (.lit 1) ∧
    uSeite cw (.built "sizeof" [.variable "a"]) = .ok (.lit 1) ∧
    uSeite ct (.built "sizeof" [.field (.index (.field (.variable "p") "slots") (.lit 0)) "v"]) = .ok (.lit 1) ∧
    uSeite { cw with alias := [("W", (0, 65535)), ("W#bits", (32, 32))] } (.built "sizeof" [.variable "W"]) =
      .ok (.lit 4) := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- An unresolved operand, a literal and a parameter without a declared word have no size. -/
theorem sizeof_abgelehnt_lesen_zeuge :
    uSeite cw (.built "sizeof" [.variable "q"]) = .error "sizeof without a resolved declared size" ∧
    uSeite cw (.built "sizeof" [.variable "z"]) = .error "sizeof without a resolved declared size" ∧
    uSeite cw (.built "sizeof" [.lit 4]) = .error "sizeof without a resolved declared size" := ⟨rfl, rfl, rfl⟩

/-- `aligned(x, N)` is `x mod N = 0`. -/
theorem aligned_lesen_zeuge :
    uSichert cw (.built "aligned" [.variable "a", .lit 16]) =
      .ok (.cmp "==" (.rem (.param "a") (.lit 16)) (.lit 0)) := by rfl

/-- A zero alignment is no positive constant; a capability is no number. -/
theorem aligned_abgelehnt_lesen_zeuge :
    uSichert cw (.built "aligned" [.variable "a", .lit 0]) =
      .error "source export: alignment must be a positive constant" ∧
    uSichert ct (.built "aligned" [.variable "p", .lit 8]) = .error "pointer in a compare without G form" := ⟨rfl, rfl⟩

end EingebautLesen

end Gabbro.Grammatik.Parser.UebersetzeAllg
