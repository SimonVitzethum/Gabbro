module
public import Bruecke.Kette.Formen.ZeugenSchritte
public import Grammatik.Parser.Stmt.LibraryFixtureScanning
import all Grammatik.Parser.Elab.Uebersetze.Akku.ProbenPhases
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

namespace Gabbro.Bruecke.StatischZeuge

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

def writer : UFn :=
  { name := "write_counter", params := [], kinds := [], res := none, held := [], puts := [],
    gputs := ["counter"], gives := [], body := [.assignGlob "counter" (.lit 9)], ret := .empty }

def reader : UFn :=
  { name := "read_counter", params := [], kinds := [], res := none, held := [], puts := [],
    gives := [], body := [.bind "seen" none (.glob "counter")], ret := .empty }

def caller : UFn :=
  { name := "use_counter", params := [], kinds := [], res := none, held := [], puts := [],
    gputs := ["counter"], gives := [],
    body := [.call "write_counter" [], .call "read_counter" []], ret := .empty }

def unit : UProg :=
  { tabs := [], locks := [], fns := [writer, reader, caller],
    globs := [{ name := "counter", ty := .int 3 10, init := 7, var := true, breite := 8 }] }

-- Each scanner certificate keeps an arbitrary suffix and remaining fuel.
-- module statics { static mut counter : u8
def sourceChunk0 : Chunk where
  characters := ['m', 'o', 'd', 'u', 'l', 'e', ' ', 's', 't', 'a', 't', 'i', 'c', 's', ' ', '{', ' ', 's', 't', 'a', 't', 'i',
    'c', ' ', 'm', 'u', 't', ' ', 'c', 'o', 'u', 'n', 't', 'e', 'r', ' ', ':', ' ', 'u', '8', ' ']
  tokens := [.wort "module", .ident "statics", .zeichen "{", .wort "static", .wort "mut", .ident "counter",
    .zeichen ":", .wort "u8"]
  steps := 16
  scanned := by intro rest remaining; cbv

-- in 3 .. 10 = 7; impl fn write_counter()
def sourceChunk1 : Chunk where
  characters := ['i', 'n', ' ', '3', ' ', '.', '.', ' ', '1', '0', ' ', '=', ' ', '7', ';', ' ', 'i', 'm', 'p', 'l', ' ', 'f',
    'n', ' ', 'w', 'r', 'i', 't', 'e', '_', 'c', 'o', 'u', 'n', 't', 'e', 'r', '(', ')', ' ']
  tokens := [.wort "in", .num 3, .zeichen "..", .num 10, .zeichen "=", .num 7,
    .zeichen ";", .wort "impl", .wort "fn", .ident "write_counter", .zeichen "(", .zeichen ")"]
  steps := 21
  scanned := by intro rest remaining; cbv

-- effects { writes counter } { counter = 9;
def sourceChunk2 : Chunk where
  characters := ['e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' ', 'w', 'r', 'i', 't', 'e', 's', ' ', 'c', 'o', 'u', 'n', 't',
    'e', 'r', ' ', '}', ' ', '{', ' ', 'c', 'o', 'u', 'n', 't', 'e', 'r', ' ', '=', ' ', '9', ';', ' ']
  tokens := [.wort "effects", .zeichen "{", .wort "writes", .ident "counter", .zeichen "}", .zeichen "{",
    .ident "counter", .zeichen "=", .num 9, .zeichen ";"]
  steps := 19
  scanned := by intro rest remaining; cbv

-- } impl fn read_counter() effects { reads
def sourceChunk3 : Chunk where
  characters := ['}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'r', 'e', 'a', 'd', '_', 'c', 'o', 'u', 'n', 't', 'e', 'r',
    '(', ')', ' ', 'e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' ', 'r', 'e', 'a', 'd', 's', ' ']
  tokens := [.zeichen "}", .wort "impl", .wort "fn", .ident "read_counter", .zeichen "(", .zeichen ")",
    .wort "effects", .zeichen "{", .wort "reads"]
  steps := 16
  scanned := by intro rest remaining; cbv

-- counter } { let seen = counter; } impl fn
def sourceChunk4 : Chunk where
  characters := ['c', 'o', 'u', 'n', 't', 'e', 'r', ' ', '}', ' ', '{', ' ', 'l', 'e', 't', ' ', 's', 'e', 'e', 'n', ' ', '=',
    ' ', 'c', 'o', 'u', 'n', 't', 'e', 'r', ';', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ']
  tokens := [.ident "counter", .zeichen "}", .zeichen "{", .wort "let", .ident "seen", .zeichen "=",
    .ident "counter", .zeichen ";", .zeichen "}", .wort "impl", .wort "fn"]
  steps := 21
  scanned := by intro rest remaining; cbv

-- use_counter() effects { writes counter }
def sourceChunk5 : Chunk where
  characters := ['u', 's', 'e', '_', 'c', 'o', 'u', 'n', 't', 'e', 'r', '(', ')', ' ', 'e', 'f', 'f', 'e', 'c', 't', 's', ' ',
    '{', ' ', 'w', 'r', 'i', 't', 'e', 's', ' ', 'c', 'o', 'u', 'n', 't', 'e', 'r', ' ', '}', ' ']
  tokens := [.ident "use_counter", .zeichen "(", .zeichen ")", .wort "effects", .zeichen "{", .wort "writes",
    .ident "counter", .zeichen "}"]
  steps := 14
  scanned := by intro rest remaining; cbv

-- { write_counter(); read_counter(); } }
def sourceChunk6 : Chunk where
  characters := ['{', ' ', 'w', 'r', 'i', 't', 'e', '_', 'c', 'o', 'u', 'n', 't', 'e', 'r', '(', ')', ';', ' ', 'r', 'e', 'a',
    'd', '_', 'c', 'o', 'u', 'n', 't', 'e', 'r', '(', ')', ';', ' ', '}', ' ', '}']
  tokens := [.zeichen "{", .ident "write_counter", .zeichen "(", .zeichen ")", .zeichen ";", .ident "read_counter",
    .zeichen "(", .zeichen ")", .zeichen ";", .zeichen "}", .zeichen "}"]
  steps := 15
  scanned := by intro rest remaining; cbv

def sourceChunks : List Chunk :=
  [sourceChunk0, sourceChunk1, sourceChunk2, sourceChunk3, sourceChunk4, sourceChunk5, sourceChunk6]

def source : String := String.ofList (characters sourceChunks)

def writerBody : List Gabbro.Body.Stmt := [.assignGlobal "counter" (.lit (.int 9))]
def readerBody : List Gabbro.Body.Stmt := [.bindName "seen" (.global "counter")]
def callerBody : List Gabbro.Body.Stmt :=
  [.call "write_counter" [] [] (.lit (.bool true)), .call "read_counter" [] [] (.lit (.bool true))]

theorem reader_forms :
    zuBodyZ unit writer = some writerBody ∧ zuBodyZ unit reader = some readerBody ∧
      zuBodyZ unit caller = some callerBody := by
  exact ⟨by cbv, by cbv, by cbv⟩

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

/-- Initializer seven is retained even though the declared range excludes zero. -/
theorem initial_value_zeuge : nullB unit = true ∧
    ∀ hn : nullB unit = true,
      valOf ((declOf unit).gtyp ⟨0, by decide⟩) ((nullSp unit hn).globs ⟨0, by decide⟩) = .int 7 := by
  refine ⟨by cbv, fun hn => ?_⟩
  cbv

/-- Unsupported static kinds and an out-of-range initializer keep explicit refusal gates. -/
theorem static_refusals_zeuge :
    staticsB { unit with globs := [{ name := "flag", ty := .bool, init := 0 }] } = false ∧
    staticsB { unit with globs := [{ name := "array", ty := .wert (.arr (.int 0 10) 1), init := 0 }] } = false ∧
    staticsB { unit with globs := [{ name := "atomic", ty := .int 0 10, init := 0, atomic := true }] } = false ∧
    nullB { unit with globs := [{ name := "outside", ty := .int 3 10, init := 0 }] } = false := by
  cbv

/-- O43 is proved over every matching computed signature of all three lowered functions. -/
theorem interfaces : SchnittstellenPflicht unit := by
  apply witness_interfaces_empty
  · rintro ⟨index, bound⟩
    have small : index < 3 := bound
    have choices : index = 0 ∨ index = 1 ∨ index = 2 := by omega
    rcases choices with rfl | rfl | rfl
    all_goals cbv
  · intro n
    rcases n with _ | _ | _ | n <;> constructor <;> cbv

theorem writer_meets : meetsU unit (wfU unit) writer writerBody := by
  intro ρB s hW _
  change ∃ s', Gabbro.Body.finalState (Gabbro.Body.exec ρB writerBody s) = some s' ∧ wfU unit s'
  refine ⟨⟨Gabbro.Body.store s.world (.global "counter") (.int 9), s.local'⟩, rfl, ?_⟩
  apply Gabbro.Body.WF_store (shapeOfUG unit) s.world (.global "counter") (.int 9) hW
  intro sh hsh
  have hs : shapeOfUG unit (.global "counter") = some (.intIn 3 10) := by cbv
  rw [hs] at hsh
  cases hsh
  cbv

theorem reader_meets : meetsU unit (wfU unit) reader readerBody := by
  intro ρB s hW _
  change ∃ s', Gabbro.Body.finalState (Gabbro.Body.exec ρB readerBody s) = some s' ∧ wfU unit s'
  exact ⟨⟨s.world, Gabbro.Body.bindLocal s.local' "seen" (s.world (.global "counter"))⟩, rfl, hW⟩

theorem caller_meets : meetsU unit (wfU unit) caller callerBody := by
  intro ρB s hW _
  change Gabbro.Body.Contract ρB "read_counter" (preProp (wfU unit) reader)
      (fun s s' r => (postU unit (wfU unit) reader s s' r).getD False) →
    Gabbro.Body.Frame ρB "read_counter" [callClock] →
    Gabbro.Body.Contract ρB "write_counter" (preProp (wfU unit) writer)
      (fun s s' r => (postU unit (wfU unit) writer s s' r).getD False) →
    Gabbro.Body.Frame ρB "write_counter" ["counter", callClock] →
    ∃ s', Gabbro.Body.finalState (Gabbro.Body.exec ρB callerBody s) = some s' ∧ wfU unit s'
  intro hread _ hwrite _
  let t0 : Gabbro.Body.State := ⟨s.world, fun _ => .absent⟩
  let t1 := (ρB "write_counter" t0).1
  have hw1 : wfU unit t1 := hwrite t0 ⟨hW, rfl⟩
  let t2 : Gabbro.Body.State := ⟨t1.world, fun _ => .absent⟩
  let t3 := (ρB "read_counter" t2).1
  have hw3 : wfU unit t3 := hread t2 ⟨hw1, rfl⟩
  exact ⟨⟨t3.world, s.local'⟩, rfl, hw3⟩

theorem duties : ∀ c : Fin unit.fns.length, ∃ bs,
    zuBodyZ unit (fnAt unit c) = some bs ∧ meetsU unit (wfU unit) (fnAt unit c) bs := by
  intro ⟨c, hc⟩
  rcases c with _ | _ | _ | c
  · exact ⟨writerBody, reader_forms.1, writer_meets⟩
  · exact ⟨readerBody, reader_forms.2.1, reader_meets⟩
  · exact ⟨callerBody, reader_forms.2.2, caller_meets⟩
  · have hh : c + 3 < 3 := hc
    omega

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

/-- The source anchor, computed contracts, carried duties and final theorem hold together. -/
theorem nutzer_aus_quelleG_statisch_zeuge :
    PflichtenTeilG source (u := unit) (fun _ => True) ∧
      (∀ hn : nullB unit = true, OffeneStartPflicht unit (fun _ => True) program hn) ∧
      uebersetzeAllg source = .ok ⟨unit, program, functions⟩ ∧
      ∃ hn : nullB unit = true, Zielsatz.NutzerPflicht (einheitAllg unit program hn) := by
  have hStart : ∀ hn : nullB unit = true,
      OffeneStartPflicht unit (fun _ => True) program hn := fun _ _ _ hc => (hc True.intro).elim
  exact ⟨carried_duties, hStart, translated, nutzer_aus_quelleG carried_duties hStart translated⟩

/-- Nonempty ordinary statics also use the unchanged atomic-rely source endpoint. -/
theorem atomic_rely_zeuge :
    ∃ hn : nullB unit = true, Zielsatz.NutzerPflichtA (einheitAllg unit program hn) :=
  nutzerA_aus_quelleG carried_duties (fun _ _ _ hc => (hc True.intro).elim) translated

#print axioms nutzer_aus_quelleG_statisch_zeuge
#print axioms atomic_rely_zeuge


end Gabbro.Bruecke.StatischZeuge
