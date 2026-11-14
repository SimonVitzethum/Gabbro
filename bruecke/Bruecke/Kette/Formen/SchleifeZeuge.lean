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

/-! # A nonempty three-slot traversal under the source-to-user-duty theorem -/

namespace Gabbro.Bruecke.SchleifeZeuge

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

open Gabbro.Grammatik.Uebersetzung.LibraryFixtureScanning

set_option maxRecDepth 100000
set_option maxHeartbeats 400000

attribute [local cbv_eval] Parser.strEq_apply_eq_decide

attribute [local cbv_eval] Nat.log2_def lowEns.eq_def lowCmp.eq_def lowWertE.eq_def

def tafel : UTab :=
  { name := "T"
    count := 3
    cols := [("v", (0, 9))]
    breiten := [("v", 8)] }

def fill : UFn :=
  { name := "fill"
    params := []
    kinds := []
    res := none
    held := []
    puts := ["T"]
    gives := []
    body := [.loopBeg "i" "T" .tru, .assignTab "T" "v" (.param "i") (.lit 7), .blkEnd]
    ret := .empty }

def unit : UProg :=
  { tabs := [tafel]
    locks := []
    fns := [fill] }

-- Each scanner certificate keeps an arbitrary suffix and remaining fuel.
-- module loops { table T count 3 { slot { v
def sourceChunk0 : Chunk where
  characters := ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'l', 'o', 'o', 'p', 's', ' ', '{', ' ', 't', 'a', 'b', 'l', 'e', ' ', 'T',
    ' ', 'c', 'o', 'u', 'n', 't', ' ', '3', ' ', '{', ' ', 's', 'l', 'o', 't', ' ', '{', ' ', 'v', ' ']
  tokens := [.wort "module", .ident "loops", .zeichen "{", .wort "table", .ident "T", .wort "count",
    .num 3, .zeichen "{", .wort "slot", .zeichen "{", .ident "v"]
  steps := 22
  scanned := by intro rest remaining; cbv

-- : u8 in 0 .. 9, } } impl fn fill()
def sourceChunk1 : Chunk where
  characters := [':', ' ', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '9', ',', ' ', '}', ' ', '}', ' ', 'i', 'm',
    'p', 'l', ' ', 'f', 'n', ' ', 'f', 'i', 'l', 'l', '(', ')', ' ']
  tokens := [.zeichen ":", .wort "u8", .wort "in", .num 0, .zeichen "..", .num 9,
    .zeichen ",", .zeichen "}", .zeichen "}", .wort "impl", .wort "fn", .ident "fill",
    .zeichen "(", .zeichen ")"]
  steps := 25
  scanned := by intro rest remaining; cbv

-- effects { writes T.slots } { traverse i
def sourceChunk2 : Chunk where
  characters := ['e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' ', 'w', 'r', 'i', 't', 'e', 's', ' ', 'T', '.', 's', 'l', 'o',
    't', 's', ' ', '}', ' ', '{', ' ', 't', 'r', 'a', 'v', 'e', 'r', 's', 'e', ' ', 'i', ' ']
  tokens := [.wort "effects", .zeichen "{", .wort "writes", .ident "T", .zeichen ".", .wort "slots",
    .zeichen "}", .zeichen "{", .wort "traverse", .ident "i"]
  steps := 18
  scanned := by intro rest remaining; cbv

-- over slots of T by unvisited touches
def sourceChunk3 : Chunk where
  characters := ['o', 'v', 'e', 'r', ' ', 's', 'l', 'o', 't', 's', ' ', 'o', 'f', ' ', 'T', ' ', 'b', 'y', ' ', 'u', 'n', 'v',
    'i', 's', 'i', 't', 'e', 'd', ' ', 't', 'o', 'u', 'c', 'h', 'e', 's', ' ']
  tokens := [.wort "over", .wort "slots", .wort "of", .ident "T", .wort "by", .wort "unvisited",
    .wort "touches"]
  steps := 14
  scanned := by intro rest remaining; cbv

-- writes T.slots { T.slots[i].v = 7; } } }
def sourceChunk4 : Chunk where
  characters := ['w', 'r', 'i', 't', 'e', 's', ' ', 'T', '.', 's', 'l', 'o', 't', 's', ' ', '{', ' ', 'T', '.', 's', 'l', 'o',
    't', 's', '[', 'i', ']', '.', 'v', ' ', '=', ' ', '7', ';', ' ', '}', ' ', '}', ' ', '}']
  tokens := [.wort "writes", .ident "T", .zeichen ".", .wort "slots", .zeichen "{", .ident "T",
    .zeichen ".", .wort "slots", .zeichen "[", .ident "i", .zeichen "]", .zeichen ".",
    .ident "v", .zeichen "=", .num 7, .zeichen ";", .zeichen "}", .zeichen "}",
    .zeichen "}"]
  steps := 27
  scanned := by intro rest remaining; cbv

def sourceChunks : List Chunk :=
  [sourceChunk0, sourceChunk1, sourceChunk2, sourceChunk3, sourceChunk4]

def source : String := String.ofList (characters sourceChunks)

def body : List Gabbro.Body.Stmt :=
  [.forEach "i" [0, 1, 2] [.assign "T" (.name "i") "v" (.lit (.int 7))]]

theorem reader_form : zuBodyZ unit fill = some body := by cbv

theorem lowered_some : (lowerAllg unit).toOption.isSome = true := by
  apply Gabbro.Grammatik.Uebersetzung.LibraryFixtureProofs.lowering_ok
  · rfl
  · cbv
  · rintro ⟨index, bound⟩
    have small : index < 1 := bound
    have zero : index = 0 := by omega
    subst index
    all_goals constructor <;> cbv

def program : Programm (declOf unit) := ((lowerAllg unit).toOption.get lowered_some).1
def functions : List (declOf unit).Fn := ((lowerAllg unit).toOption.get lowered_some).2

theorem lowered : lowerAllg unit = .ok (program, functions) := except_ok_get lowered_some

def scanned : { tokens : List Parser.Token // Parser.lex source = .ok tokens } :=
  ⟨tokens sourceChunks, by
    rw [source, Parser.lex_ofList]
    exact lex_chunks sourceChunks (by cbv)⟩

theorem parsed_some : (Parser.parseTopTief scanned.val).toOption.isSome = true := by cbv

noncomputable def parsed : { items : List Parser.SItemTief //
    Parser.parseTopTief scanned.val = .ok items } :=
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
    all_goals cbv
  · intro n
    rcases n with _ | n <;> constructor <;> cbv

def filled (s : Gabbro.Body.State) : Gabbro.Body.State :=
  ⟨Gabbro.Body.store
    (Gabbro.Body.store (Gabbro.Body.store s.world (.slot "T" 0 "v") (.int 7))
      (.slot "T" 1 "v") (.int 7)) (.slot "T" 2 "v") (.int 7),
    Gabbro.Body.bindLocal (Gabbro.Body.bindLocal (Gabbro.Body.bindLocal s.local' "i" (.int 0))
      "i" (.int 1)) "i" (.int 2)⟩

theorem executed (ρB : Gabbro.Body.Env) (s : Gabbro.Body.State) :
    Gabbro.Body.exec ρB body s = .running (filled s) := by
  simp only [body, Gabbro.Body.exec, Gabbro.Body.step, Gabbro.Body.traverseRun,
    Gabbro.Body.eval, Gabbro.Body.bindLocal_here, filled]

theorem store_wf (world : Gabbro.Body.World) (hw : Gabbro.Body.WF (shapeOfUG unit) world) (i : Int) :
    Gabbro.Body.WF (shapeOfUG unit) (Gabbro.Body.store world (.slot "T" i "v") (.int 7)) := by
  apply Gabbro.Body.WF_store (shapeOfUG unit) world (.slot "T" i "v") (.int 7) hw
  intro sh hsh
  have hs : shapeOfUG unit (.slot "T" i "v") = some (.intIn 0 9) := by cbv
  rw [hs] at hsh
  cases hsh
  cbv

theorem meets : meetsU unit (wfU unit) fill body := by
  intro ρB s hW _
  change ∃ t, Gabbro.Body.finalState (Gabbro.Body.exec ρB body s) = some t ∧ wfU unit t
  rw [executed]
  exact ⟨filled s, rfl, store_wf _ (store_wf _ (store_wf _ hW 0) 1) 2⟩

/-- All three passes occur and write different table cells. -/
theorem nonempty_writes (s : Gabbro.Body.State) :
    (filled s).world (.slot "T" 0 "v") = .int 7 ∧
      (filled s).world (.slot "T" 1 "v") = .int 7 ∧
      (filled s).world (.slot "T" 2 "v") = .int 7 := by
  simp [filled, Gabbro.Body.store]

theorem carried_duties : PflichtenTeilG source (u := unit) (fun _ => True) := by
  refine ⟨uOf_eq translated, (by cbv),
    getragenG_of_bools (by cbv) (by cbv) (by cbv),
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

theorem nutzer_aus_quelleG_schleife_zeuge :
    PflichtenTeilG source (u := unit) (fun _ => True) ∧
      uebersetzeAllg source = .ok ⟨unit, program, functions⟩ ∧
      ∃ hn : nullB unit = true, Zielsatz.NutzerPflicht (einheitAllg unit program hn) := by
  have hStart : ∀ hn : nullB unit = true,
      OffeneStartPflicht unit (fun _ => True) program hn := fun _ _ _ hc => (hc True.intro).elim
  exact ⟨carried_duties, translated, nutzer_aus_quelleG carried_duties hStart translated⟩

/-- A nontrivial invariant or a call in the body remains explicitly outside this first fragment. -/
theorem traversal_refusals :
    zuBodyZ unit { fill with body := [.loopBeg "i" "T" .fls, .blkEnd] } = none ∧
      zuBodyZ unit { fill with body := [.loopBeg "i" "T" .tru, .call "fill" [], .blkEnd] } = none := by
  constructor <;> cbv

#print axioms nutzer_aus_quelleG_schleife_zeuge

end Gabbro.Bruecke.SchleifeZeuge
