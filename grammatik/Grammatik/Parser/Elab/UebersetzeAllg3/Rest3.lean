module

public import Grammatik.Parser.Elab.ExportControl
public import Grammatik.Parser.Elab.UebersetzeSum
public import Grammatik.Bausteine.Arena.ArenaZucker
public import Grammatik.Parser.Namen.Oeffentlich
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
public import Grammatik.Parser.Elab.UebersetzeAllg3.Stufe
public import Grammatik.Parser.Elab.UebersetzeAllg3.Rest2

@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
set_option maxRecDepth 100000

-- SRC-BEGIN src108
/-- The real `beispiele/0108-disjoint-start-locks.gab` text, one entry per source line (a long
    line cut again after a space). `zaehle-kette.py` compares the
    pieces against the file, byte for byte. WHY PIECES and not one
    literal: `Parser/Lexer.lean`'s `lex_ofList` -- one 2082-byte
    literal costs the kernel tens of gigabytes (O13). -/
def srcZeilen108 : List (List Char) :=
  ["// 108 -- Two lock-free readers over one ".toList,
   "shared, never-written table.\n".toList,
   "//\n".toList,
   "// TRANSFER of `StartExklusiv` ".toList,
   "(`RufMaschineG.lean`): the start ".toList,
   "functions of\n".toList,
   "// distinct threads hold no signature ".toList,
   "lock in common -- and since lane 183\n".toList,
   "// (`wurzelnB`) they hold NO signature ".toList,
   "lock at all: nobody holds a lock for a\n".toList,
   "// thread before it starts. This file ".toList,
   "used to show the disjoint shape\n".toList,
   "// (`read_a` under `Held(L)`, `read_c` ".toList,
   "under `Held(M)`); that shape is now\n".toList,
   "// refused at both starts (`N303`), and ".toList,
   "the take-inside remedy has no G form\n".toList,
   "// for value readers (`LG004`: no ".toList,
   "`return` under `locks`). What remains ".toList,
   "is\n".toList,
   "// the silent side both rules share: two ".toList,
   "readers over one table nobody\n".toList,
   "// writes -- every rule stays silent ".toList,
   "(`N240`/`N303`: nothing held; `N290`/\n".toList,
   "// `N291`/`N300`/`N301`: unwritten ".toList,
   "carriers; `W001`: reads overlap ".toList,
   "freely).\n".toList,
   "// The refused root shape lives in ".toList,
   "`beispiele/gift/967`, the pair side in\n".toList,
   "// gifts 910-915. The G export of this ".toList,
   "file is pinned in\n".toList,
   "// ".toList,
   "`grammatik/Grammatik/Export108.lean`.\n".toList,
   "//\n".toList,
   "// Evidence: the pre-183 program this ".toList,
   "file replaces, kept verbatim as a\n".toList,
   "// comment. It is refused since lane 183 ".toList,
   "at both starts by `N303`\n".toList,
   "// (`wurzelnB`: `D.haelt w = []` -- ".toList,
   "nobody holds a lock for a thread before\n".toList,
   "// it starts), although `N240` stays ".toList,
   "silent on it (disjoint held sets):\n".toList,
   "//   table U count 4 {\n".toList,
   "//       slot { v : u32, }\n".toList,
   "//   }\n".toList,
   "//   lock L protects { T } rank 0 held ".toList,
   "<= 100 ops;\n".toList,
   "//   lock M protects { U } rank 1 held ".toList,
   "<= 100 ops;\n".toList,
   "//   impl fn read_a() -> u32\n".toList,
   "//       requires Held(L)\n".toList,
   "//       effects { reads T.slots }\n".toList,
   "//       costs <= 4 ops\n".toList,
   "//   {\n".toList,
   "//       return T.slots[0].v;\n".toList,
   "//   }\n".toList,
   "//   impl fn read_c() -> u32\n".toList,
   "//       requires Held(M)\n".toList,
   "//       effects { reads U.slots }\n".toList,
   "//       costs <= 4 ops\n".toList,
   "//   {\n".toList,
   "//       return U.slots[0].v;\n".toList,
   "//   }\n".toList,
   "module beispiel::disjoint_start_locks {\n".toList,
   "\n".toList,
   "table T count 4 {\n".toList,
   "    slot { v : u32, }\n".toList,
   "}\n".toList,
   "\n".toList,
   "impl fn read_a() -> u32\n".toList,
   "    effects { reads T.slots }\n".toList,
   "    costs <= 4 ops\n".toList,
   "{\n".toList,
   "    return T.slots[0].v;\n".toList,
   "}\n".toList,
   "\n".toList,
   "impl fn read_c() -> u32\n".toList,
   "    effects { reads T.slots }\n".toList,
   "    costs <= 4 ops\n".toList,
   "{\n".toList,
   "    return T.slots[1].v;\n".toList,
   "}\n".toList,
   "\n".toList,
   "concurrent { read_a, read_c };\n".toList,
   "\n".toList,
   "}\n".toList]
-- SRC-END src108

/-- The pinned text as characters. -/
def srcQuelle108 : List Char := srcZeilen108.flatten

/-- The pinned text as the `String` the chain is indexed by. -/
def src108 : String := String.ofList srcQuelle108

/-- The token list of the 108 source (`lex108` checks it). -/
def toks108 : List Token := [.wort "module",
 .ident "beispiel",
 .zeichen "::",
 .ident "disjoint_start_locks",
 .zeichen "{",
 .wort "table",
 .ident "T",
 .wort "count",
 .num 4,
 .zeichen "{",
 .wort "slot",
 .zeichen "{",
 .ident "v",
 .zeichen ":",
 .wort "u32",
 .zeichen ",",
 .zeichen "}",
 .zeichen "}",
 .wort "impl",
 .wort "fn",
 .ident "read_a",
 .zeichen "(",
 .zeichen ")",
 .zeichen "->",
 .wort "u32",
 .wort "effects",
 .zeichen "{",
 .wort "reads",
 .ident "T",
 .zeichen ".",
 .wort "slots",
 .zeichen "}",
 .wort "costs",
 .zeichen "<=",
 .num 4,
 .wort "ops",
 .zeichen "{",
 .wort "return",
 .ident "T",
 .zeichen ".",
 .wort "slots",
 .zeichen "[",
 .num 0,
 .zeichen "]",
 .zeichen ".",
 .ident "v",
 .zeichen ";",
 .zeichen "}",
 .wort "impl",
 .wort "fn",
 .ident "read_c",
 .zeichen "(",
 .zeichen ")",
 .zeichen "->",
 .wort "u32",
 .wort "effects",
 .zeichen "{",
 .wort "reads",
 .ident "T",
 .zeichen ".",
 .wort "slots",
 .zeichen "}",
 .wort "costs",
 .zeichen "<=",
 .num 4,
 .wort "ops",
 .zeichen "{",
 .wort "return",
 .ident "T",
 .zeichen ".",
 .wort "slots",
 .zeichen "[",
 .num 1,
 .zeichen "]",
 .zeichen ".",
 .ident "v",
 .zeichen ";",
 .zeichen "}",
 .wort "concurrent",
 .zeichen "{",
 .ident "read_a",
 .zeichen ",",
 .ident "read_c",
 .zeichen "}",
 .zeichen ";",
 .zeichen "}",
 .ende]


set_option maxHeartbeats 4000000 in
/-- **THE REAL 108 TEXT LEXES TO `toks108`**, over the characters (O13). -/
theorem lexL108 : lexL srcQuelle108 = .ok toks108 := by
  decide

/-- The same, as a statement about the `String` -- through `lex_ofList`
    and never through the UTF-8 decoder (O13). -/
theorem lex108 : lex src108 = .ok toks108 := by
  show lex (String.ofList srcQuelle108) = _
  rw [lex_ofList]
  exact lexL108

/-- The parsed 108 surface tree (raw, `concurrent` inside;
    `parse108` checks it against the reader). -/
def items108 : List SItemTief := [.modT
   "beispiel::disjoint_start_locks"
   [.tableT
      "T"
      none
      (some (.lit 4))
      none
      none
      false
      [.tSlot
         [{ fname := "v",
            ftyp := .atom "u32",
            pos := none,
            bezug := none,
            wo := none,
            reserviert := false,
            byOps := false }]],
    .fnT
      { art := "impl",
        name := "read_a",
        params := [],
        res := some (.atom "u32"),
        fehler := none,
        klauseln := [.effs
                       [.reads
                          (.field (.variable "T") "slots")],
                     .cost (.lit 4)] }
      (.block
        []
        (some (.ret
           (some (.field
              (.index
                (.field (.variable "T") "slots")
                (.lit 0))
              "v"))))),
    .fnT
      { art := "impl",
        name := "read_c",
        params := [],
        res := some (.atom "u32"),
        fehler := none,
        klauseln := [.effs
                       [.reads
                          (.field (.variable "T") "slots")],
                     .cost (.lit 4)] }
      (.block
        []
        (some (.ret
           (some (.field
              (.index
                (.field (.variable "T") "slots")
                (.lit 1))
              "v"))))),
    .concT [(["read_a"], []), (["read_c"], [])]]]

theorem parse108 : beqTopTief (parseTopTief toks108) (.ok items108) = true := by
  decide

/-- The elaborated 108 program (`elab108` checks it against
    the elaborator run after `pre108`). -/

def uExp108 : UProg := { tabs := [{ name := "T", count := 4, cols := [("v", 0, 4294967295)] }], locks := [], fns := [{ name := "read_a", params := [], kinds := [], res := some (0, 4294967295), held := [], puts := [], gives := [], body := [], ret := .val (.tab "T" "v" (.lit 0)) }, { name := "read_c", params := [], kinds := [], res := some (0, 4294967295), held := [], puts := [], gives := [], body := [], ret := .val (.tab "T" "v" (.lit 1)) }], roots := ["read_a", "read_c"], exportGate := ExportMetadata.check (uMembers (pre108 items108)) }

theorem elab108 : beqElabU (elabU (pre108 items108)) (.ok uExp108) = true := by
  decide

/-- The fragment check on the generically lowered 108 program. -/
theorem lowerAllg108fragment :
    (match lowerAllg uExp108 with
      | .ok (P, fs) => programmImFragmentG P fs
      | .error _ => false) = true := by
  decide

/-- The footprint check on the generically lowered 108 program. -/
theorem lowerAllg108fuss :
    (match lowerAllg uExp108 with
      | .ok (P, fs) => fussOrtGB P fs
      | .error _ => false) = true := by
  decide

/-- Declaration data agreement for 108: the generic
    declaration built from `uExp108` agrees with the exporter
    universe `G108_disjoint_start_locks.gD`. -/
theorem lowerAllg108data :
    (declOf uExp108).count ⟨0, by decide⟩ = 4 ∧
    G108_disjoint_start_locks.gD.count G108_disjoint_start_locks.GTab.T = 4 ∧
    (declOf uExp108).typ ⟨0, by decide⟩ ⟨0, by decide⟩ = .int 0 4294967295 ∧
    G108_disjoint_start_locks.gD.typ G108_disjoint_start_locks.GTab.T G108_disjoint_start_locks.GTFeld.v = .int 0 4294967295 ∧
    ((declOf uExp108).signatur ⟨0, by decide⟩).haelt = ([] : List (declOf uExp108).Lock) ∧
    G108_disjoint_start_locks.gD.haelt G108_disjoint_start_locks.g_read_a = [] ∧
    ((declOf uExp108).signatur ⟨1, by decide⟩).haelt = ([] : List (declOf uExp108).Lock) ∧
    G108_disjoint_start_locks.gD.haelt G108_disjoint_start_locks.g_read_c = [] ∧
    ((declOf uExp108).signatur ⟨0, by decide⟩).schreibt ⟨0, by decide⟩ = false ∧
    (G108_disjoint_start_locks.gD.signatur G108_disjoint_start_locks.g_read_a).schreibt G108_disjoint_start_locks.GTab.T = false ∧
    ((declOf uExp108).signatur ⟨1, by decide⟩).schreibt ⟨0, by decide⟩ = false ∧
    (G108_disjoint_start_locks.gD.signatur G108_disjoint_start_locks.g_read_c).schreibt G108_disjoint_start_locks.GTab.T = false := by
  decide

/-- One theorem chaining every stage for 108. -/
theorem kette108 : lex src108 = .ok toks108 ∧
    beqTopTief (parseTopTief toks108) (.ok items108) = true ∧
    beqElabU (elabU (pre108 items108)) (.ok uExp108) = true ∧
    (match lowerAllg uExp108 with
      | .ok (P, fs) => programmImFragmentG P fs && fussOrtGB P fs
      | .error _ => false) = true := by
  refine ⟨lex108, parse108, elab108, ?_⟩
  decide

end Gabbro.Grammatik.Parser.UebersetzeAllg2

/-
  CUTS: what is not proved here.

  1. `RufPasst`: `hh` asks the callee held set inside the caller
     resources; `hx` and `hb` are decided against the floors, which
     are DATA of the elaborated functions (`UFn.boden`, filled by
     `uMitBoden` with `floorOf`) and read by `mkSig`.
  2. `beq`-style soundness is proved for nothing new here; the
     `beqElabU`/`beqTopTief` pins are reused from `Uebersetze.lean`
     (same cut as there).
  3. The shift fix in `UebersetzeAllg.lean` (`sh` on `lowIdx`,
     `lowParamSide`, `lowDurch`, `lowTabRead`, `lowAltRead`):
     `ensures` positions ride one past the result when one is
     present. Without it `lowerAllg` fails on every result-bearing
     function whose contract reads a slot (measured on `lies`).
  4. 108 is done the same way as 104: `pre108` unwraps the
     module and normalises bare `u32` to its
     full range before `elabU`; `toks108`/`items108`/`uExp108`
     are probe-generated literals (`#eval` + `Repr`, then pinned
     by `lex108`/`parse108`/`elab108`), with the fragment,
     footprint, data and chaining pins on top.
  5. Membership across the `Fin`/carrier line does not synthesize:
     `L ∈ S.haelt` with `L : Fin _` has no `Decidable` instance,
     the unfolded `∀ w ∈ braucht` form and `D.Lock`-quantified
     harvests do. List literals compared against carrier lists
     need an explicit `List (declOf u).Lock` ascription.
-/

#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg2.sigSchreibt_eq
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg2.nach_eq
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg2.lowerEach_all_ok
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg2.lowerAllg104fragment
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg2.lowerAllg104fuss
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg2.lowerAllg104data
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg2.lex104real
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg2.kette104
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg2.lex108
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg2.parse108
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg2.elab108
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg2.lowerAllg108fragment
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg2.lowerAllg108fuss
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg2.lowerAllg108data
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg2.kette108
