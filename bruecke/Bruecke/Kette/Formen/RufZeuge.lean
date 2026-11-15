module
public import Bruecke.Kette.Formen.ZeugenSchritte
public import Grammatik.Parser.Stmt.LibraryFixtureScanning
import all Grammatik.Parser.Elab.Uebersetze.Akku.ProbenPhases
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

/-! # Source witness for pure numeric and boolean result bindings -/

namespace Gabbro.Bruecke.RufZeuge

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

open Gabbro.Grammatik.Uebersetzung.LibraryFixtureScanning

set_option maxRecDepth 100000
set_option maxHeartbeats 400000

-- Select one actual reader node before inspecting its large-fuel callbacks.
attribute [local cbv_opaque] uAnwReihe uAnwReiheCore uAkkuBinder uZeigerAnw uStartNamen
attribute [local cbv_eval] row_nil row_cons core_bind core_call core_set
  bound_names_select pointer_source_select start_source_select
attribute [local cbv_eval] Parser.strEq_apply_eq_decide

attribute [local cbv_eval] Nat.log2_def lowEns.eq_def lowCmp.eq_def lowWertE.eq_def

def number : UFn :=
  { name := "number"
    params := []
    kinds := []
    res := some (0, 9)
    held := []
    puts := []
    gives := []
    body := []
    ret := .val (.lit 7) }

def answer : UFn :=
  { name := "answer"
    params := []
    kinds := []
    res := none
    resBool := true
    held := []
    puts := []
    gives := []
    body := []
    ret := .bool .tru }

def caller : UFn :=
  { name := "use_results"
    params := []
    kinds := []
    res := none
    held := []
    puts := []
    gives := []
    body := [.bindCall "n" "number" [], .bindCall "ok" "answer" []]
    ret := .empty }

def unit : UProg :=
  { tabs := []
    locks := []
    fns := [number, answer, caller] }

-- Each scanner certificate keeps an arbitrary suffix and remaining fuel.
-- module results { impl fn number() -> u8
def sourceChunk0 : Chunk where
  characters := ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'r', 'e', 's', 'u', 'l', 't', 's', ' ', '{', ' ', 'i', 'm', 'p', 'l', ' ',
    'f', 'n', ' ', 'n', 'u', 'm', 'b', 'e', 'r', '(', ')', ' ', '-', '>', ' ', 'u', '8', ' ']
  tokens := [.wort "module", .ident "results", .zeichen "{", .wort "impl", .wort "fn", .wort "number",
    .zeichen "(", .zeichen ")", .zeichen "->", .wort "u8"]
  steps := 18
  scanned := by intro rest remaining; cbv

-- in 0 .. 9 { return 7; } impl fn answer()
def sourceChunk1 : Chunk where
  characters := ['i', 'n', ' ', '0', ' ', '.', '.', ' ', '9', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', '7', ';', ' ',
    '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'a', 'n', 's', 'w', 'e', 'r', '(', ')', ' ']
  tokens := [.wort "in", .num 0, .zeichen "..", .num 9, .zeichen "{", .wort "return",
    .num 7, .zeichen ";", .zeichen "}", .wort "impl", .wort "fn", .ident "answer",
    .zeichen "(", .zeichen ")"]
  steps := 25
  scanned := by intro rest remaining; cbv

-- -> bool { return true; } impl fn
def sourceChunk2 : Chunk where
  characters := ['-', '>', ' ', 'b', 'o', 'o', 'l', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 't', 'r', 'u', 'e', ';',
    ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ']
  tokens := [.zeichen "->", .wort "bool", .zeichen "{", .wort "return", .wort "true", .zeichen ";",
    .zeichen "}", .wort "impl", .wort "fn"]
  steps := 17
  scanned := by intro rest remaining; cbv

-- use_results() { let n = number(); let ok
def sourceChunk3 : Chunk where
  characters := ['u', 's', 'e', '_', 'r', 'e', 's', 'u', 'l', 't', 's', '(', ')', ' ', '{', ' ', 'l', 'e', 't', ' ', 'n', ' ',
    '=', ' ', 'n', 'u', 'm', 'b', 'e', 'r', '(', ')', ';', ' ', 'l', 'e', 't', ' ', 'o', 'k', ' ']
  tokens := [.ident "use_results", .zeichen "(", .zeichen ")", .zeichen "{", .wort "let", .ident "n",
    .zeichen "=", .wort "number", .zeichen "(", .zeichen ")", .zeichen ";", .wort "let",
    .ident "ok"]
  steps := 21
  scanned := by intro rest remaining; cbv

-- = answer(); } }
def sourceChunk4 : Chunk where
  characters := ['=', ' ', 'a', 'n', 's', 'w', 'e', 'r', '(', ')', ';', ' ', '}', ' ', '}']
  tokens := [.zeichen "=", .ident "answer", .zeichen "(", .zeichen ")", .zeichen ";", .zeichen "}",
    .zeichen "}"]
  steps := 10
  scanned := by intro rest remaining; cbv

def sourceChunks : List Chunk :=
  [sourceChunk0, sourceChunk1, sourceChunk2, sourceChunk3, sourceChunk4]

def source : String := String.ofList (characters sourceChunks)

def numberBody : List Gabbro.Body.Stmt := [.ret (some (.lit (.int 7)))]
def answerBody : List Gabbro.Body.Stmt := [.ret (some (.lit (.bool true)))]
def callerBody : List Gabbro.Body.Stmt :=
  [.bindCall "n" "number" [] [] (.lit (.bool true)),
    .bindCall "ok" "answer" [] [] (.lit (.bool true))]

theorem reader_forms : zuBodyZ unit number = some numberBody ∧
    zuBodyZ unit answer = some answerBody ∧ zuBodyZ unit caller = some callerBody :=
  ⟨by cbv, by cbv, by cbv⟩

theorem lowered_some : (lowerAllg unit).toOption.isSome = true := by
  apply Gabbro.Grammatik.Uebersetzung.LibraryFixtureProofs.lowering_ok
  · rfl
  · cbv
  · rintro ⟨index, bound⟩
    have small : index < 3 := bound
    have choices : index = 0 ∨ index = 1 ∨ index = 2 := by omega
    rcases choices with rfl | rfl | rfl
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

-- Retain phase outputs before proving the next phase, so no certificate repeats
-- name resolution and module preparation while checking the exported function bodies.
noncomputable def prepared : { items : List Parser.SItemTief // pre108 parsed.val = items } :=
  ⟨pre108 parsed.val, rfl⟩

theorem expanded_some : (expandU prepared.val).toOption.isSome = true := by cbv

noncomputable def expanded : { result : List Parser.SItemTief × List (Parser.STyp × String) //
    expandU prepared.val = .ok result } :=
  ⟨(expandU prepared.val).toOption.get expanded_some, except_ok_get expanded_some⟩

/-- Heavy evaluation of the export phase; this witness module is off the compiler path. -/
theorem exported : elabU (pre108 parsed.val) = .ok unit := by
  rw [prepared.property]
  unfold elabU
  rw [expanded.property]
  decide +kernel

theorem translated : uebersetzeAllg source = .ok ⟨unit, program, functions⟩ :=
  witness_translation scanned.property parsed.property exported lowered

theorem interfaces : SchnittstellenPflicht unit := by
  apply witness_interfaces_empty
  · rintro ⟨index, bound⟩
    have small : index < 3 := bound
    have choices : index = 0 ∨ index = 1 ∨ index = 2 := by omega
    rcases choices with rfl | rfl | rfl
    all_goals cbv
  · intro n
    rcases n with _ | _ | _ | n <;> constructor <;> cbv

theorem number_meets : meetsU unit (wfU unit) number numberBody := by
  intro ρB s hW _
  exact ⟨s, rfl, hW, 7, rfl, by decide, by decide⟩

theorem answer_meets : meetsU unit (wfU unit) answer answerBody := by
  intro ρB s hW _
  exact ⟨s, rfl, hW, true, rfl⟩

theorem caller_meets : meetsU unit (wfU unit) caller callerBody := by
  intro ρB s hW _
  change Gabbro.Body.Contract ρB "answer" (preProp (wfU unit) answer)
      (fun s s' r => (postU unit (wfU unit) answer s s' r).getD False) →
    Gabbro.Body.Frame ρB "answer" [callClock] →
    Gabbro.Body.Contract ρB "number" (preProp (wfU unit) number)
      (fun s s' r => (postU unit (wfU unit) number s s' r).getD False) →
    Gabbro.Body.Frame ρB "number" [callClock] → _
  intro ha _ hn _
  let t0 : Gabbro.Body.State := ⟨s.world, fun _ => .absent⟩
  obtain ⟨hw1, n, hnum, _, _⟩ := hn t0 ⟨hW, rfl⟩
  let s1 : Gabbro.Body.State := ⟨(ρB "number" t0).1.world, Gabbro.Body.bindLocal s.local' "n" (.int n)⟩
  let t1 : Gabbro.Body.State := ⟨s1.world, fun _ => .absent⟩
  obtain ⟨hw2, ok, hbool⟩ := ha t1 ⟨hw1, rfl⟩
  let s2 : Gabbro.Body.State := ⟨(ρB "answer" t1).1.world, Gabbro.Body.bindLocal s1.local' "ok" (.bool ok)⟩
  have hstep0 : Gabbro.Body.step ρB (.bindCall "n" "number" [] [] (.lit (.bool true))) s =
      .running s1 := by
    simp only [Gabbro.Body.step, Gabbro.Body.evalAll, Gabbro.Body.eval, Gabbro.Body.bindAll]
    rw [hnum]
  have hstep1 : Gabbro.Body.step ρB (.bindCall "ok" "answer" [] [] (.lit (.bool true))) s1 =
      .running s2 := by
    simp only [Gabbro.Body.step, Gabbro.Body.evalAll, Gabbro.Body.eval, Gabbro.Body.bindAll]
    rw [hbool]
  refine ⟨s2, ?_, hw2⟩
  simp only [callerBody, Gabbro.Body.exec, hstep0, hstep1, Gabbro.Body.finalState]

theorem duties : ∀ c : Fin unit.fns.length, ∃ bs,
    zuBodyZ unit (fnAt unit c) = some bs ∧ meetsU unit (wfU unit) (fnAt unit c) bs := by
  intro ⟨c, hc⟩
  rcases c with _ | _ | _ | c
  · exact ⟨numberBody, reader_forms.1, number_meets⟩
  · exact ⟨answerBody, reader_forms.2.1, answer_meets⟩
  · exact ⟨callerBody, reader_forms.2.2, caller_meets⟩
  · have hh : c + 3 < 3 := hc
    omega

theorem carried_duties : PflichtenTeilG source (u := unit) (fun _ => True) := by
  refine ⟨uOf_eq translated, (by cbv),
    getragenG_of_bools (by cbv) (by cbv) (by cbv),
    (by cbv), fun P fs hlow c _ => interfaces P fs hlow c,
    fun c _ => duties c, ?_⟩
  intro c hc
  exact (hc True.intro).elim

theorem nutzer_aus_quelleG_ruf_zeuge :
    PflichtenTeilG source (u := unit) (fun _ => True) ∧
      uebersetzeAllg source = .ok ⟨unit, program, functions⟩ ∧
      ∃ hn : nullB unit = true, Zielsatz.NutzerPflicht (einheitAllg unit program hn) := by
  have hStart : ∀ hn : nullB unit = true,
      OffeneStartPflicht unit (fun _ => True) program hn := fun _ _ _ hc => (hc True.intro).elim
  exact ⟨carried_duties, translated, nutzer_aus_quelleG carried_duties hStart translated⟩

#print axioms nutzer_aus_quelleG_ruf_zeuge

end Gabbro.Bruecke.RufZeuge
