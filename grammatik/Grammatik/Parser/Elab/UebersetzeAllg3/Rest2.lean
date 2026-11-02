module
public import Grammatik.Parser.Elab.UebersetzeAllg3.Rest2a
public import Grammatik.Parser.Elab.Export.ExportControl
public import Grammatik.Parser.Elab.UebersetzeSum
public import Grammatik.Bausteine.Arena.ArenaZucker
public import Grammatik.Parser.Namen.Oeffentlich
public import Grammatik.Parser.Elab.SourceNormalization
public import Grammatik.Parser.Elab.Modules.Expansion
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
public import Grammatik.Parser.Elab.UebersetzeAllg3.Rest1
public import Grammatik.Parser.Elab.UebersetzeAllg3.Measures.Export
@[expose] public section
namespace Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
set_option maxRecDepth 100000
/-! ## 104 pins on the generically lowered program -/

/-- The fragment check on the generically lowered 104 program. -/
theorem lowerAllg104fragment :
    (match lowerAllg uExp104 with
      | .ok (P, fs) => programmImFragmentG P fs
      | .error _ => false) = true := by
  decide

/-- The footprint check on the generically lowered 104 program. -/
theorem lowerAllg104fuss :
    (match lowerAllg uExp104 with
      | .ok (P, fs) => fussOrtGB P fs
      | .error _ => false) = true := by
  decide

/-- Declaration data agreement, construct by construct: the
    generic declaration built from `uExp104` agrees with the
    exporter universe `G104_referenz.gD` (counts, ranges, ranks,
    guards, held sets, writes). -/
theorem lowerAllg104data :
    (declOf uExp104).count ⟨0, by decide⟩ = 2 ∧
    G104_referenz.gD.count G104_referenz.GTab.Konto = 2 ∧
    (declOf uExp104).typ ⟨0, by decide⟩ ⟨0, by decide⟩ =
      .int 0 100 ∧
    G104_referenz.gD.typ G104_referenz.GTab.Konto
      G104_referenz.GKontoFeld.stand = .int 0 100 ∧
    (declOf uExp104).rang ⟨0, by decide⟩ = 0 ∧
    G104_referenz.gD.rang G104_referenz.GLock.M = 0 ∧
    (declOf uExp104).braucht ⟨0, by decide⟩ =
      ([.inl (⟨0, by decide⟩ : Fin uExp104.locks.length)] :
        List ((declOf uExp104).Lock ⊕
          ((declOf uExp104).Marke × Nat))) ∧
    G104_referenz.gD.braucht G104_referenz.GTab.Konto =
      [.inl G104_referenz.GLock.M] ∧
    ((declOf uExp104).signatur ⟨0, by decide⟩).haelt =
      ([(⟨0, by decide⟩ : Fin uExp104.locks.length)] :
        List (declOf uExp104).Lock) ∧
    G104_referenz.gD.haelt G104_referenz.g_einzahlen =
      [G104_referenz.GLock.M] ∧
    ((declOf uExp104).signatur ⟨1, by decide⟩).haelt =
      ([(⟨0, by decide⟩ : Fin uExp104.locks.length)] :
        List (declOf uExp104).Lock) ∧
    G104_referenz.gD.haelt G104_referenz.g_lies =
      [G104_referenz.GLock.M] ∧
    ((declOf uExp104).signatur ⟨0, by decide⟩).schreibt
      ⟨0, by decide⟩ = true ∧
    (G104_referenz.gD.signatur
      G104_referenz.g_einzahlen).schreibt
      G104_referenz.GTab.Konto = true ∧
    ((declOf uExp104).signatur ⟨1, by decide⟩).schreibt
      ⟨0, by decide⟩ = false ∧
    (G104_referenz.gD.signatur
      G104_referenz.g_lies).schreibt
      G104_referenz.GTab.Konto = false := by
  decide

/-! ## The real-text lexer pin for 104 -/

-- SRC-BEGIN src104real
/-- The real `beispiele/0104-referenz.gab` text, one entry per source line (a long
    line cut again after a space). `zaehle-kette.py` compares the
    pieces against the file, byte for byte. WHY PIECES and not one
    literal: `Parser/Lexer.lean`'s `lex_ofList` -- one 2064-byte
    literal costs the kernel tens of gigabytes (O13). -/
def srcZeilen104 : List (List Char) :=
  ["// 104 -- The reference fixture as a ".toList,
   "real Gabbro program (lane 126).\n".toList,
   "//\n".toList,
   "// This is ".toList,
   "`grammatik/Grammatik/ReferenzB.lean` ".toList,
   "(`refD`/`refP`) in surface\n".toList,
   "// syntax: one table `Konto` of 2 slots ".toList,
   "with one `0 .. 100` field, guarded by\n".toList,
   "// the single lock `M`; `einzahlen` (one ".toList,
   "`0 .. 10` parameter, no result,\n".toList,
   "// writes the table, ensures the slot ".toList,
   "did not decrease) and `lies` (no\n".toList,
   "// parameters, one `0 .. 100` result, ".toList,
   "reads, ensures the answer equals the\n".toList,
   "// slot). Both run under the held lock ".toList,
   "(`requires Held(M)`, the `beispiele/01`\n".toList,
   "// idiom: the caller's duty, so the ".toList,
   "bodies touch the guarded slot ".toList,
   "directly).\n".toList,
   "// Not declared `concurrent`: both ".toList,
   "functions hold `M` by signature, and ".toList,
   "the\n".toList,
   "// start rule N240 (the goal theorem's ".toList,
   "`StartExklusiv`) forbids two threads\n".toList,
   "// starting in functions that share a ".toList,
   "signature lock. The earlier note: the ".toList,
   "declaration\n".toList,
   "// (lane 141: the certificate census ".toList,
   "classifies `concurrent` as erased -- ".toList,
   "the\n".toList,
   "// emitter writes nothing for it -- so ".toList,
   "the declaration passes stage 7 of\n".toList,
   "// `pruefe-emission.sh`). Threads cannot ".toList,
   "be driven from a C driver anyway, so\n".toList,
   "// the driver runs both threads one ".toList,
   "after the other -- the sequential\n".toList,
   "// composition the emitter produces: ".toList,
   "`einzahlen` like thread 1, then `lies`\n".toList,
   "// like thread 0. That is the observable ".toList,
   "half of the fixture\n".toList,
   "// (`refB_schreibt`: slot `0 -> 100`).\n".toList,
   "\n".toList,
   "module beispiel::referenz {\n".toList,
   "\n".toList,
   "const NKONTO : u32 = 2;\n".toList,
   "\n".toList,
   "type Betrag = u32 in 0 .. 10;\n".toList,
   "type Stand = u32 in 0 .. 100;\n".toList,
   "\n".toList,
   "table Konto count NKONTO {\n".toList,
   "    slot {\n".toList,
   "        stand : Stand,\n".toList,
   "    }\n".toList,
   "}\n".toList,
   "\n".toList,
   "lock M protects { stand } rank 0 held <= ".toList,
   "50 ops;\n".toList,
   "\n".toList,
   "impl fn einzahlen(k : ptr<normal, rw> ".toList,
   "Konto, i : index into Konto, b : ".toList,
   "Betrag)\n".toList,
   "    requires Held(M)\n".toList,
   "    ensures  old(k.slots[i].stand) <= ".toList,
   "k.slots[i].stand\n".toList,
   "    effects  { reads k.slots, writes ".toList,
   "k.slots, locks M }\n".toList,
   "    costs    <= 16 ops\n".toList,
   "{\n".toList,
   "    k.slots[i].stand = 100;\n".toList,
   "    lies(k, i);\n".toList,
   "}\n".toList,
   "\n".toList,
   "impl fn lies(k : ptr<normal, r> Konto, i ".toList,
   ": index into Konto) -> Stand\n".toList,
   "    requires Held(M)\n".toList,
   "    ensures  result == k.slots[i].stand\n".toList,
   "    effects  { reads k.slots, locks M }\n".toList,
   "    costs    <= 8 ops\n".toList,
   "{\n".toList,
   "    return k.slots[i].stand;\n".toList,
   "}\n".toList,
   "\n".toList,
   "\n".toList,
   "}\n".toList]
-- SRC-END src104real

/-- The pinned text as characters. -/
def srcQuelle104 : List Char := srcZeilen104.flatten

/-- The pinned text as the `String` the chain is indexed by. -/
def src104real : String := String.ofList srcQuelle104

set_option maxHeartbeats 4000000 in
/-- **THE REAL 104 TEXT LEXES TO `tt104`** -- over the CHARACTERS, which is
    the only form the kernel ever sees (O13): the pieces are short literals,
    and the whole scan costs a fraction of one long literal's decode. -/
theorem lexL104real : lexL srcQuelle104 = .ok tt104 := by
  decide

/-- The same, as a statement about the `String` the chain is indexed by.
    `lex_ofList` carries the pin across WITHOUT running the UTF-8 decoder,
    so this theorem is a rewrite and not a reduction. -/
theorem lex104real : lex src104real = .ok tt104 := by
  show lex (String.ofList srcQuelle104) = _
  rw [lex_ofList]
  exact lexL104real

/-! ## The 104 chain, end to end -/

/-- One theorem chaining every stage for 104: real-text lexing,
    deep parsing, elaboration, generic lowering, and the fragment
    and footprint checks on the lowered program. -/
theorem kette104 : lex src104real = .ok tt104 ∧
    beqTopTief (parseTopTief tt104) (.ok items104) = true ∧
    beqElabU (elabU items104) (.ok uExp104) = true ∧
    (match lowerAllg uExp104 with
      | .ok (P, fs) => programmImFragmentG P fs && fussOrtGB P fs
      | .error _ => false) = true := by
  refine ⟨lex104real, u104parse, u104elab, ?_⟩
  decide

/-! ## 108 preprocessing: `concurrent` stripping, bare-`u32` norms -/

/-- The preprocessing of the bridge instances: check `pub` (`Oeffentlich.huelleZu`), resolve every name
    and open the modules
    (`Aufloesung.loese`: a unit of one name space is unwrapped as `uMembers` does), then normalise
    bare `u32`, before `elabU` (`concurrent` items are elaborated into the thread roots now). -/
def pre108 (items : List SItemTief) : List SItemTief :=
  -- Module applications must retain their lexical scopes and static requirements until elabU.
  if Modules.syntaxList items then items
  else if Oeffentlich.huelleZu items then normTopU32 (Aufloesung.loese items)
  -- An open export hull (or a `pub` where none may stand) refuses the unit: a lone `use` has no G form.
  else [.useT ["pub"]]

/-! ## 108 pins: strip, normalise, elaborate, lower -/

/-! ## C18 fixture: a closed static-array reset through the generic lowering -/

/-- **A unit with a static-array reset** (C18): `static mut A : [u8; 4]` and one writer that
    zeroes `[1, 3)` via `reset A at 1 count 2;`. Closed: literals only, no parameters. -/
def uReset : UProg :=
  { tabs := [], locks := [], fns := [{ name := "leere", params := [], kinds := [], res := none, held := [], puts := [], gputs := ["A"], gives := [], body := [.resetRange "A" (.lit 1) (.lit 2)], ret := .empty }], globs := [{ name := "A", ty := .wert (.arr (.int 0 255) 4), init := 0, var := true }] }

/-- The generic lowering accepts the reset unit: the range elaborates, checks, and expands
    into the typed array store. -/
theorem uReset_lower : (lowerAllg uReset).toOption.isSome = true := by decide

end Gabbro.Grammatik.Parser.UebersetzeAllg2
