module
public import Bruecke.Kette.Formen.ZeugenSchritte
public import Grammatik.Parser.Stmt.LibraryFixtureScanning
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

/-! # Joint source witness for both bare tag arms -/
namespace Gabbro.Bruecke.TagZeuge
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Uebersetzung.LibraryFixtureScanning

set_option maxRecDepth 100000
set_option maxHeartbeats 400000

attribute [local cbv_eval] Parser.strEq_apply_eq_decide
attribute [local cbv_eval] Nat.log2_def lowEns.eq_def lowCmp.eq_def lowWertE.eq_def

def test : UFn :=
  { name := "test", params := [("v", .sum [none, none])], kinds := [.sum 0], res := some (0, 1),
    held := [], puts := [], gives := [],
    body := [.matchTagBeg 0 "v" ["", ""], .ret (.val (.lit 1)), .ifElse,
      .ret (.val (.lit 0)), .blkEnd], ret := .val (.lit 0) }

def unit : UProg :=
  { tabs := [], locks := [], fns := [test],
    sums := [{ name := "Choice", cases := [("First", none), ("Second", none)] }] }

-- Each scanner certificate keeps an arbitrary suffix and remaining fuel.
-- module tags { tagged type Choice = {
def sourceChunk0 : Chunk where
  characters := ['m', 'o', 'd', 'u', 'l', 'e', ' ', 't', 'a', 'g', 's', ' ', '{', ' ', 't', 'a', 'g', 'g', 'e', 'd', ' ', 't',
    'y', 'p', 'e', ' ', 'C', 'h', 'o', 'i', 'c', 'e', ' ', '=', ' ', '{', ' ']
  tokens := [.wort "module", .ident "tags", .zeichen "{", .wort "tagged", .wort "type", .ident "Choice",
    .zeichen "=", .zeichen "{"]
  steps := 16
  scanned := by intro rest remaining; cbv

-- First, Second }; impl fn test(v : Choice)
def sourceChunk1 : Chunk where
  characters := ['F', 'i', 'r', 's', 't', ',', ' ', 'S', 'e', 'c', 'o', 'n', 'd', ' ', '}', ';', ' ', 'i', 'm', 'p', 'l', ' ',
    'f', 'n', ' ', 't', 'e', 's', 't', '(', 'v', ' ', ':', ' ', 'C', 'h', 'o', 'i', 'c', 'e', ')', ' ']
  tokens := [.ident "First", .zeichen ",", .ident "Second", .zeichen "}", .zeichen ";", .wort "impl",
    .wort "fn", .ident "test", .zeichen "(", .ident "v", .zeichen ":", .ident "Choice",
    .zeichen ")"]
  steps := 21
  scanned := by intro rest remaining; cbv

-- -> u8 in 0 .. 1 { match v { First => {
def sourceChunk2 : Chunk where
  characters := ['-', '>', ' ', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', ' ', '{', ' ', 'm', 'a', 't', 'c',
    'h', ' ', 'v', ' ', '{', ' ', 'F', 'i', 'r', 's', 't', ' ', '=', '>', ' ', '{', ' ']
  tokens := [.zeichen "->", .wort "u8", .wort "in", .num 0, .zeichen "..", .num 1,
    .zeichen "{", .wort "match", .ident "v", .zeichen "{", .ident "First", .zeichen "=>",
    .zeichen "{"]
  steps := 26
  scanned := by intro rest remaining; cbv

-- return 1; } Second => { return 0; } }
def sourceChunk3 : Chunk where
  characters := ['r', 'e', 't', 'u', 'r', 'n', ' ', '1', ';', ' ', '}', ' ', 'S', 'e', 'c', 'o', 'n', 'd', ' ', '=', '>', ' ',
    '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', '0', ';', ' ', '}', ' ', '}', ' ']
  tokens := [.wort "return", .num 1, .zeichen ";", .zeichen "}", .ident "Second", .zeichen "=>",
    .zeichen "{", .wort "return", .num 0, .zeichen ";", .zeichen "}", .zeichen "}"]
  steps := 22
  scanned := by intro rest remaining; cbv

-- return 0; } }
def sourceChunk4 : Chunk where
  characters := ['r', 'e', 't', 'u', 'r', 'n', ' ', '0', ';', ' ', '}', ' ', '}']
  tokens := [.wort "return", .num 0, .zeichen ";", .zeichen "}", .zeichen "}"]
  steps := 8
  scanned := by intro rest remaining; cbv

def sourceChunks : List Chunk :=
  [sourceChunk0, sourceChunk1, sourceChunk2, sourceChunk3, sourceChunk4]

def source : String := String.ofList (characters sourceChunks)

def arms : List (String × List Gabbro.Body.Stmt) :=
  [(caseLabel 0, [.ret (some (.lit (.int 1)))]), (caseLabel 1, [.ret (some (.lit (.int 0)))])]
def body : List Gabbro.Body.Stmt :=
  [.onTag (.name "v") (tagArms arms), .ret (some (.lit (.int 0)))]

theorem reader_form : zuBodyZ unit test = some body := by cbv

theorem lowered_some : (lowerAllg unit).toOption.isSome = true := by
  apply Gabbro.Grammatik.Uebersetzung.LibraryFixtureProofs.lowering_ok
  · rfl
  · cbv
  · rintro ⟨index, bound⟩
    have small : index < 1 := bound
    have zero : index = 0 := by omega
    subst index
    constructor <;> cbv

def program : Programm (declOf unit) := ((lowerAllg unit).toOption.get lowered_some).1
def functions : List (declOf unit).Fn := ((lowerAllg unit).toOption.get lowered_some).2

theorem lowered : lowerAllg unit = .ok (program, functions) := except_ok_get lowered_some

def scanned : { tokens : List Parser.Token // Parser.lex source = .ok tokens } :=
  ⟨tokens sourceChunks, by
    rw [source, Parser.lex_ofList]
    exact lex_chunks sourceChunks (by cbv)⟩
theorem parsed_some : (Parser.parseTopTief scanned.val).toOption.isSome = true := by cbv

noncomputable def parsed : { items : List Parser.SItemTief // Parser.parseTopTief scanned.val = .ok items } :=
  ⟨(Parser.parseTopTief scanned.val).toOption.get parsed_some, except_ok_get parsed_some⟩
theorem exported : elabU (pre108 parsed.val) = .ok unit := by cbv

theorem translated : uebersetzeAllg source = .ok ⟨unit, program, functions⟩ :=
  witness_translation scanned.property parsed.property exported lowered

theorem interfaces : SchnittstellenPflicht unit := by
  apply witness_interfaces_empty
  · rintro ⟨index, bound⟩
    have small : index < 1 := bound
    have zero : index = 0 := by omega
    subst index
    cbv
  · intro n
    rcases n with _ | n <;> constructor <;> cbv

theorem meets : meetsU unit (wfU unit) test body := by
  intro ρB s hW hpre
  change some (Gabbro.Body.Value.bool ((s.local' "v").hasShape (.sum [(caseLabel 0, none), (caseLabel 1, none)]))) =
    some (Gabbro.Body.Value.bool true) at hpre
  have hs := Option.some.inj hpre
  injection hs with hs
  obtain ⟨label, payload, hv, hc⟩ := Gabbro.Body.Value.hasShape_sum_true (s.local' "v") _ hs
  simp only [Gabbro.Body.Shape.caseOk_cons, Gabbro.Body.Shape.caseOk_nil, Bool.or_false,
    Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Gabbro.Body.Shape.payloadOk_none_iff] at hc
  have hne : caseLabel 0 ≠ caseLabel 1 := by
    intro h
    have := caseLabel_injective h
    omega
  rcases hc with ⟨hlabel, rfl⟩ | ⟨hlabel, rfl⟩
  · subst label
    have hex : Gabbro.Body.exec ρB body s = .returned s (some (.int 1)) := by
      simp only [body, Gabbro.Body.exec, Gabbro.Body.step, Gabbro.Body.eval, hv, pickTag_bare,
        arms, Gabbro.Body.pickArm, ↓reduceIte]
    change ∃ s', Gabbro.Body.finalState (Gabbro.Body.exec ρB body s) = some s' ∧
      (postU unit (wfU unit) test s s' (Gabbro.Body.finalValue (Gabbro.Body.exec ρB body s))).getD False
    rw [hex]
    exact ⟨s, rfl, hW, 1, rfl, by decide⟩
  · subst label
    have hex : Gabbro.Body.exec ρB body s = .returned s (some (.int 0)) := by
      simp only [body, Gabbro.Body.exec, Gabbro.Body.step, Gabbro.Body.eval, hv, pickTag_bare,
        arms, Gabbro.Body.pickArm, hne, ↓reduceIte]
    change ∃ s', Gabbro.Body.finalState (Gabbro.Body.exec ρB body s) = some s' ∧
      (postU unit (wfU unit) test s s' (Gabbro.Body.finalValue (Gabbro.Body.exec ρB body s))).getD False
    rw [hex]
    exact ⟨s, rfl, hW, 0, rfl, by decide⟩

theorem payload_refusal :
    tagSubject { test with params := [("v", .sum [none, some (.int 0 9)])] }
      (BodyNames.start test) "v" = none := by cbv

theorem carried_duties : PflichtenTeilG source (u := unit) (fun _ => True) := by
  refine ⟨uOf_eq translated, (by cbv), getragenG_of_bools (by cbv) (by cbv) (by cbv),
    (by cbv), fun P fs hlow c _ => interfaces P fs hlow c, ?_, ?_⟩
  · intro c _
    have hc : c = ⟨0, by decide⟩ := Fin.ext (by
      change c.val = 0
      have h : c.val < 1 := c.isLt
      omega)
    subst c
    exact ⟨body, reader_form, meets⟩
  · intro c hc
    exact (hc True.intro).elim

/-- The actual source, all carried duties and the final user-duty endpoint hold jointly. -/
theorem nutzer_aus_quelleG_tag_zeuge :
    PflichtenTeilG source (u := unit) (fun _ => True) ∧
      uebersetzeAllg source = .ok ⟨unit, program, functions⟩ ∧
      ∃ hn : nullB unit = true, Zielsatz.NutzerPflicht (einheitAllg unit program hn) := by
  have hStart : ∀ hn : nullB unit = true,
      OffeneStartPflicht unit (fun _ => True) program hn := fun _ _ _ hc => (hc True.intro).elim
  exact ⟨carried_duties, translated, nutzer_aus_quelleG carried_duties hStart translated⟩

#print axioms nutzer_aus_quelleG_tag_zeuge
end Gabbro.Bruecke.TagZeuge
