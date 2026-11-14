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

/-! # Joint source witness for both numeric narrowing outcomes -/

namespace Gabbro.Bruecke.BereichZeuge

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

open Gabbro.Grammatik.Uebersetzung.LibraryFixtureScanning

set_option maxRecDepth 100000
set_option maxHeartbeats 400000

attribute [local cbv_eval] Parser.strEq_apply_eq_decide

attribute [local cbv_eval] Nat.log2_def lowEns.eq_def lowCmp.eq_def lowWertE.eq_def

def clip : UFn :=
  { name := "clip"
    params := [("x", .int 0 9)]
    kinds := [.int]
    res := some (0, 3)
    held := []
    puts := []
    gives := []
    body := [.narrowBeg "x" 0 3, .ret (.val (.lit 0)), .blkEnd]
    ret := .val (.param "x") }

def unit : UProg :=
  { tabs := []
    locks := []
    fns := [clip] }

-- Each scanner certificate keeps an arbitrary suffix and remaining fuel.
-- module ranges { impl fn clip(x : u8 in 0
def sourceChunk0 : Chunk where
  characters := ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'r', 'a', 'n', 'g', 'e', 's', ' ', '{', ' ', 'i', 'm', 'p', 'l', ' ', 'f',
    'n', ' ', 'c', 'l', 'i', 'p', '(', 'x', ' ', ':', ' ', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ']
  tokens := [.wort "module", .ident "ranges", .zeichen "{", .wort "impl", .wort "fn", .ident "clip",
    .zeichen "(", .wort "x", .zeichen ":", .wort "u8", .wort "in", .num 0]
  steps := 22
  scanned := by intro rest remaining; cbv

-- .. 9) -> u8 in 0 .. 3 { narrow x to 0 ..
def sourceChunk1 : Chunk where
  characters := ['.', '.', ' ', '9', ')', ' ', '-', '>', ' ', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '3', ' ',
    '{', ' ', 'n', 'a', 'r', 'r', 'o', 'w', ' ', 'x', ' ', 't', 'o', ' ', '0', ' ', '.', '.', ' ']
  tokens := [.zeichen "..", .num 9, .zeichen ")", .zeichen "->", .wort "u8", .wort "in",
    .num 0, .zeichen "..", .num 3, .zeichen "{", .wort "narrow", .wort "x",
    .wort "to", .num 0, .zeichen ".."]
  steps := 29
  scanned := by intro rest remaining; cbv

-- 3 else { return 0; } return x; } }
def sourceChunk2 : Chunk where
  characters := ['3', ' ', 'e', 'l', 's', 'e', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', '0', ';', ' ', '}', ' ', 'r',
    'e', 't', 'u', 'r', 'n', ' ', 'x', ';', ' ', '}', ' ', '}']
  tokens := [.num 3, .wort "else", .zeichen "{", .wort "return", .num 0, .zeichen ";",
    .zeichen "}", .wort "return", .wort "x", .zeichen ";", .zeichen "}", .zeichen "}"]
  steps := 21
  scanned := by intro rest remaining; cbv

def sourceChunks : List Chunk :=
  [sourceChunk0, sourceChunk1, sourceChunk2]

def source : String := String.ofList (characters sourceChunks)

def body : List Gabbro.Body.Stmt :=
  [narrowStep (BodyNames.start clip) "x" 0 3 (.name "x") [.ret (some (.lit (.int 0)))],
    .ret (some (.name "x##"))]

theorem reader_form : zuBodyZ unit clip = some body := by cbv

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

theorem meets : meetsU unit (wfU unit) clip body := by
  intro ρB s hW hpre
  change some (Gabbro.Body.Value.bool ((s.local' "x").hasShape (.intIn 0 9))) = some (Gabbro.Body.Value.bool true) at hpre
  have hshape := Option.some.inj hpre
  injection hshape with hshape
  obtain ⟨n, hn, hlo, hhi⟩ := Gabbro.Body.Value.hasShape_intIn_true (s.local' "x") 0 9 hshape
  have hv : Gabbro.Body.eval s (.name "x") = some (.int n) := by simp only [Gabbro.Body.eval, hn]
  have ht := narrowTest_eval (lo := 0) (hi := 3) hv
  by_cases hb : 0 ≤ n ∧ n ≤ 3
  · let s' : Gabbro.Body.State :=
      ⟨s.world, Gabbro.Body.bindLocal s.local' "x##" (.int n)⟩
    have hfresh : (BodyNames.start clip).fresh "x" = "x##" := by cbv
    have hex : Gabbro.Body.exec ρB body s = .returned s' (some (.int n)) := by
      simp only [body, narrowStep, hfresh, Gabbro.Body.exec, Gabbro.Body.step, ht,
        hb, and_self, decide_true, hv, hn, Gabbro.Body.eval, Gabbro.Body.bindLocal_here]
      rfl
    change ∃ t, Gabbro.Body.finalState (Gabbro.Body.exec ρB body s) = some t ∧
      (postU unit (wfU unit) clip s t (Gabbro.Body.finalValue (Gabbro.Body.exec ρB body s))).getD False
    rw [hex]
    exact ⟨s', rfl, hW, n, rfl, hb.1, hb.2⟩
  · have hex : Gabbro.Body.exec ρB body s = .returned s (some (.int 0)) := by
      simp only [body, narrowStep, Gabbro.Body.exec, Gabbro.Body.step, ht,
        hb, decide_false, Gabbro.Body.eval]
    change ∃ t, Gabbro.Body.finalState (Gabbro.Body.exec ρB body s) = some t ∧
      (postU unit (wfU unit) clip s t (Gabbro.Body.finalValue (Gabbro.Body.exec ρB body s))).getD False
    rw [hex]
    exact ⟨s, rfl, hW, 0, rfl, by decide, by decide⟩

/-- Both source-level alternatives occur; the failure branch is not excluded by the precondition. -/
theorem branch_witnesses (ρB : Gabbro.Body.Env) :
    Gabbro.Body.finalValue (Gabbro.Body.exec ρB body ⟨fun _ => .absent, fun _ => .int 2⟩) = some (.int 2) ∧
    Gabbro.Body.finalValue (Gabbro.Body.exec ρB body ⟨fun _ => .absent, fun _ => .int 8⟩) = some (.int 0) := by
  constructor <;> cbv

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

theorem nutzer_aus_quelleG_bereich_zeuge :
    PflichtenTeilG source (u := unit) (fun _ => True) ∧
      uebersetzeAllg source = .ok ⟨unit, program, functions⟩ ∧
      ∃ hn : nullB unit = true, Zielsatz.NutzerPflicht (einheitAllg unit program hn) := by
  have hStart : ∀ hn : nullB unit = true,
      OffeneStartPflicht unit (fun _ => True) program hn := fun _ _ _ hc => (hc True.intro).elim
  exact ⟨carried_duties, translated, nutzer_aus_quelleG carried_duties hStart translated⟩

#print axioms nutzer_aus_quelleG_bereich_zeuge

end Gabbro.Bruecke.BereichZeuge
