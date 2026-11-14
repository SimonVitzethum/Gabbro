module
public import Bruecke.Kette.Formen.ZeugenSchritte
public import Grammatik.Parser.Stmt.LibraryFixtureScanning
public import Bruecke.Anweisung.Zweig.SchattenZeuge
import all Init.Data.String.Length
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.Repr
import all Init.Data.String.Decode
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
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
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil12
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Erzeuge
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Torhuelle
import all Grammatik.Parser.Elab.Generic.StaticConformance
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil5
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest1
import all Grammatik.Parser.Elab.UebersetzeAllg3.Body
@[expose] public section

namespace Gabbro.Bruecke.SchattenKetteZeuge

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open SchattenZeuge

open Gabbro.Grammatik.Uebersetzung.LibraryFixtureScanning

set_option maxRecDepth 100000
set_option maxHeartbeats 400000

attribute [local cbv_eval] Parser.strEq_apply_eq_decide

attribute [local cbv_eval] Nat.log2_def lowEns.eq_def lowCmp.eq_def lowWertE.eq_def

-- Each scanner certificate keeps an arbitrary suffix and remaining fuel.
-- module shadowing { impl fn shadow() ->
def sourceChunk0 : Chunk where
  characters := ['m', 'o', 'd', 'u', 'l', 'e', ' ', 's', 'h', 'a', 'd', 'o', 'w', 'i', 'n', 'g', ' ', '{', ' ', 'i', 'm', 'p',
    'l', ' ', 'f', 'n', ' ', 's', 'h', 'a', 'd', 'o', 'w', '(', ')', ' ', '-', '>', ' ']
  tokens := [.wort "module", .ident "shadowing", .zeichen "{", .wort "impl", .wort "fn", .ident "shadow",
    .zeichen "(", .zeichen ")", .zeichen "->"]
  steps := 16
  scanned := by intro rest remaining; cbv

-- u32 in 0 .. 1 { let mut x : u32 in 0 .. 1
def sourceChunk1 : Chunk where
  characters := ['u', '3', '2', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', ' ', '{', ' ', 'l', 'e', 't', ' ', 'm', 'u',
    't', ' ', 'x', ' ', ':', ' ', 'u', '3', '2', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', ' ']
  tokens := [.wort "u32", .wort "in", .num 0, .zeichen "..", .num 1, .zeichen "{",
    .wort "let", .wort "mut", .wort "x", .zeichen ":", .wort "u32", .wort "in",
    .num 0, .zeichen "..", .num 1]
  steps := 30
  scanned := by intro rest remaining; cbv

-- = 1; if true { let x : u32 in 0 .. 0 = 0;
def sourceChunk2 : Chunk where
  characters := ['=', ' ', '1', ';', ' ', 'i', 'f', ' ', 't', 'r', 'u', 'e', ' ', '{', ' ', 'l', 'e', 't', ' ', 'x', ' ', ':',
    ' ', 'u', '3', '2', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '0', ' ', '=', ' ', '0', ';', ' ']
  tokens := [.zeichen "=", .num 1, .zeichen ";", .wort "if", .wort "true", .zeichen "{",
    .wort "let", .wort "x", .zeichen ":", .wort "u32", .wort "in", .num 0,
    .zeichen "..", .num 0, .zeichen "=", .num 0, .zeichen ";"]
  steps := 32
  scanned := by intro rest remaining; cbv

-- } return x; } }
def sourceChunk3 : Chunk where
  characters := ['}', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'x', ';', ' ', '}', ' ', '}']
  tokens := [.zeichen "}", .wort "return", .wort "x", .zeichen ";", .zeichen "}", .zeichen "}"]
  steps := 10
  scanned := by intro rest remaining; cbv

def sourceChunks : List Chunk :=
  [sourceChunk0, sourceChunk1, sourceChunk2, sourceChunk3]

def source : String := String.ofList (characters sourceChunks)

def program : Programm (declOf unit) :=
  ((lowerAllg unit).toOption.get lowered_some_zeuge).1

def functions : List (declOf unit).Fn :=
  ((lowerAllg unit).toOption.get lowered_some_zeuge).2

theorem lowered : lowerAllg unit = .ok (program, functions) :=
  except_ok_get lowered_some_zeuge

def scanned : { tokens : List Parser.Token // Parser.lex source = .ok tokens } :=
  ⟨tokens sourceChunks, by
    rw [source, Parser.lex_ofList]
    exact lex_chunks sourceChunks (by cbv)⟩

theorem parsed_some : (Parser.parseTopTief scanned.val).toOption.isSome = true := by cbv

noncomputable def parsed : { items : List Parser.SItemTief //
    Parser.parseTopTief scanned.val = .ok items } :=
  ⟨(Parser.parseTopTief scanned.val).toOption.get parsed_some, except_ok_get parsed_some⟩

theorem exported : elabU (pre108 parsed.val) = .ok unit := by cbv

/-- The source anchor includes parsing, elaboration and the actual canonical lowering. -/
theorem translated : uebersetzeAllg source = .ok ⟨unit, program, functions⟩ :=
  witness_translation scanned.property parsed.property exported lowered

/-- O43 is discharged on the actual lowered contract, including the live self-signature.
    Neither contract component is assumed to be trivial. -/
theorem interfaces : SchnittstellenPflicht unit := by
  apply witness_interfaces_empty
  · rintro ⟨index, bound⟩
    have small : index < 1 := bound
    have zero : index = 0 := by omega
    subst index
    all_goals cbv
  · intro n
    rcases n with _ | n <;> constructor <;> cbv

theorem duties : ∀ c : Fin unit.fns.length, ∃ bs,
    zuBodyZ unit (fnAt unit c) = some bs ∧ meetsU unit (wfU unit) (fnAt unit c) bs := by
  intro c
  have hc : c = ⟨0, (by decide)⟩ := by
    apply Fin.ext
    have hb : c.val < 1 := c.isLt
    show c.val = 0
    omega
  subst c
  exact ⟨body, translation_zeuge, routine_meets_zeuge⟩

/-- Checked indices share scalar names; missing kind information remains protected. -/
theorem kind_admission_zeuge :
    bindFrischB { routine with params := [("x", .int 0 1)], kinds := [.int] } = true ∧
      bindFrischB { routine with params := [("x", .int 0 1)], kinds := [.index 0] } = true ∧
      bindFrischB { routine with params := [("x", .int 0 1)], kinds := [] } = false := by
  cbv

theorem all_duties : PflichtenAlle source :=
  ⟨unit, uOf_eq translated, (by cbv), (by cbv),
    (by cbv), (by cbv), (by cbv), interfaces, duties⟩

theorem carried_duties : PflichtenTeilG source (u := unit) (fun _ => True) := by
  refine ⟨uOf_eq translated, (by cbv),
    getragenG_of_bools (by cbv) (by cbv) (by cbv),
    (by cbv), fun P fs hlow c _ => interfaces P fs hlow c,
    fun c _ => duties c, ?_⟩
  intro c hc
  exact (hc True.intro).elim

/-- All three premises of the final source-chain theorem hold together on the shadowing
    function: source duties, open-start duties and successful translation. -/
theorem nutzer_aus_quelleG_schatten_zeuge :
    PflichtenTeilG source (u := unit) (fun _ => True) ∧
      (∀ hn : nullB unit = true, OffeneStartPflicht unit (fun _ => True) program hn) ∧
      uebersetzeAllg source = .ok ⟨unit, program, functions⟩ ∧
      ∃ hn : nullB unit = true, Zielsatz.NutzerPflicht (einheitAllg unit program hn) := by
  have hStart : ∀ hn : nullB unit = true,
      OffeneStartPflicht unit (fun _ => True) program hn :=
    fun _ _ _ hc => (hc True.intro).elim
  exact ⟨carried_duties, hStart, translated,
    nutzer_aus_quelleG carried_duties hStart translated⟩

#print axioms nutzer_aus_quelleG_schatten_zeuge

end Gabbro.Bruecke.SchattenKetteZeuge
