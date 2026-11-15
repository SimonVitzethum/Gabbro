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

/-! # Joint source witness: construction, projection, local replacement and record results -/

namespace Gabbro.Bruecke.RecordZeuge
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Uebersetzung.LibraryFixtureScanning

set_option maxRecDepth 100000
set_option maxHeartbeats 400000

attribute [local cbv_eval] Parser.strEq_apply_eq_decide

def schema : URecord :=
  { name := "R"
    identity := 0
    fields := [("a", .int 0 9), ("b", .bool)]
    breiten := [("a", 8)] }

def build : UFn :=
  { name := "build"
    params := []
    kinds := []
    res := none
    resTy := some schema.ty
    held := []
    puts := []
    gives := []
    body := []
    ret := .wert (.product 0 false [(.int 0 9, .lit 3), (.bool, .truth true)]) }

def proj : UFn :=
  { name := "proj"
    params := [("r", schema.ty)]
    kinds := [.wert]
    res := some (0, 9)
    held := []
    puts := []
    gives := []
    body := []
    ret := .val (.field (.param "r") "a") }

def upd : UFn :=
  { name := "upd"
    params := [("r", schema.ty)]
    kinds := [.wert]
    res := none
    resTy := some schema.ty
    held := []
    puts := []
    gives := []
    body := [.bindW "out" (some schema.ty) (.param "r"),
      .setVar "out" (.replace (.param "out") "a" (.lit 5))]
    ret := .wert (.param "out") }

def identity : UFn :=
  { name := "identity"
    params := [("r", schema.ty)]
    kinds := [.wert]
    res := none
    resTy := some schema.ty
    held := []
    puts := []
    gives := []
    body := []
    ret := .wert (.param "r") }

def unit : UProg :=
  { tabs := []
    locks := []
    fns := [build, proj, upd, identity]
    records := [schema] }

-- Each scanner certificate keeps an arbitrary suffix and remaining fuel.
-- module records { type R = { a : u8 in 0
def sourceChunk0 : Chunk where
  characters := ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'r', 'e', 'c', 'o', 'r', 'd', 's', ' ', '{', ' ', 't', 'y', 'p', 'e', ' ',
    'R', ' ', '=', ' ', '{', ' ', 'a', ' ', ':', ' ', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ']
  tokens := [.wort "module", .ident "records", .zeichen "{", .wort "type", .ident "R", .zeichen "=",
    .zeichen "{", .ident "a", .zeichen ":", .wort "u8", .wort "in", .num 0]
  steps := 24
  scanned := by intro rest remaining; cbv

-- .. 9, b : bool, }; impl fn build() -> R {
def sourceChunk1 : Chunk where
  characters := ['.', '.', ' ', '9', ',', ' ', 'b', ' ', ':', ' ', 'b', 'o', 'o', 'l', ',', ' ', '}', ';', ' ', 'i', 'm', 'p',
    'l', ' ', 'f', 'n', ' ', 'b', 'u', 'i', 'l', 'd', '(', ')', ' ', '-', '>', ' ', 'R', ' ', '{', ' ']
  tokens := [.zeichen "..", .num 9, .zeichen ",", .ident "b", .zeichen ":", .wort "bool",
    .zeichen ",", .zeichen "}", .zeichen ";", .wort "impl", .wort "fn", .ident "build",
    .zeichen "(", .zeichen ")", .zeichen "->", .ident "R", .zeichen "{"]
  steps := 29
  scanned := by intro rest remaining; cbv

-- return R(a: 3, b: true); } impl fn proj(r
def sourceChunk2 : Chunk where
  characters := ['r', 'e', 't', 'u', 'r', 'n', ' ', 'R', '(', 'a', ':', ' ', '3', ',', ' ', 'b', ':', ' ', 't', 'r', 'u', 'e',
    ')', ';', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'p', 'r', 'o', 'j', '(', 'r', ' ']
  tokens := [.wort "return", .ident "R", .zeichen "(", .ident "a", .zeichen ":", .num 3,
    .zeichen ",", .ident "b", .zeichen ":", .wort "true", .zeichen ")", .zeichen ";",
    .zeichen "}", .wort "impl", .wort "fn", .ident "proj", .zeichen "(", .wort "r"]
  steps := 27
  scanned := by intro rest remaining; cbv

-- : R) -> u8 in 0 .. 9 { return r.a; } impl
def sourceChunk3 : Chunk where
  characters := [':', ' ', 'R', ')', ' ', '-', '>', ' ', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '9', ' ', '{',
    ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'r', '.', 'a', ';', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ']
  tokens := [.zeichen ":", .ident "R", .zeichen ")", .zeichen "->", .wort "u8", .wort "in",
    .num 0, .zeichen "..", .num 9, .zeichen "{", .wort "return", .wort "r",
    .zeichen ".", .ident "a", .zeichen ";", .zeichen "}", .wort "impl"]
  steps := 30
  scanned := by intro rest remaining; cbv

-- fn upd(r : R) -> R { let mut out : R = r;
def sourceChunk4 : Chunk where
  characters := ['f', 'n', ' ', 'u', 'p', 'd', '(', 'r', ' ', ':', ' ', 'R', ')', ' ', '-', '>', ' ', 'R', ' ', '{', ' ', 'l',
    'e', 't', ' ', 'm', 'u', 't', ' ', 'o', 'u', 't', ' ', ':', ' ', 'R', ' ', '=', ' ', 'r', ';', ' ']
  tokens := [.wort "fn", .ident "upd", .zeichen "(", .wort "r", .zeichen ":", .ident "R",
    .zeichen ")", .zeichen "->", .ident "R", .zeichen "{", .wort "let", .wort "mut",
    .wort "out", .zeichen ":", .ident "R", .zeichen "=", .wort "r", .zeichen ";"]
  steps := 32
  scanned := by intro rest remaining; cbv

-- out.a = 5; return out; } impl fn
def sourceChunk5 : Chunk where
  characters := ['o', 'u', 't', '.', 'a', ' ', '=', ' ', '5', ';', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'o', 'u', 't', ';',
    ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ']
  tokens := [.wort "out", .zeichen ".", .ident "a", .zeichen "=", .num 5, .zeichen ";",
    .wort "return", .wort "out", .zeichen ";", .zeichen "}", .wort "impl", .wort "fn"]
  steps := 20
  scanned := by intro rest remaining; cbv

-- identity(r : R) -> R { return r; } }
def sourceChunk6 : Chunk where
  characters := ['i', 'd', 'e', 'n', 't', 'i', 't', 'y', '(', 'r', ' ', ':', ' ', 'R', ')', ' ', '-', '>', ' ', 'R', ' ', '{',
    ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'r', ';', ' ', '}', ' ', '}']
  tokens := [.ident "identity", .zeichen "(", .wort "r", .zeichen ":", .ident "R", .zeichen ")",
    .zeichen "->", .ident "R", .zeichen "{", .wort "return", .wort "r", .zeichen ";",
    .zeichen "}", .zeichen "}"]
  steps := 23
  scanned := by intro rest remaining; cbv

def sourceChunks : List Chunk :=
  [sourceChunk0, sourceChunk1, sourceChunk2, sourceChunk3, sourceChunk4, sourceChunk5, sourceChunk6]

def source : String := String.ofList (characters sourceChunks)

def buildBody : List Gabbro.Body.Stmt :=
  [.ret (some (.recOf [.lit (.int 3), .lit (.bool true)]))]
def projBody : List Gabbro.Body.Stmt := [.ret (some (.recGet (.name "r") 0))]
def updBody : List Gabbro.Body.Stmt :=
  [.bindName "out" (.name "r"), .bindName "out" (.recSet (.name "out") 0 (.lit (.int 5))),
    .ret (some (.name "out"))]
def identityBody : List Gabbro.Body.Stmt := [.ret (some (.name "r"))]

theorem reader_forms : zuBodyZ unit build = some buildBody ∧ zuBodyZ unit proj = some projBody ∧
    zuBodyZ unit upd = some updBody ∧ zuBodyZ unit identity = some identityBody :=
  ⟨by cbv, by cbv, by cbv, by cbv⟩

theorem lowered_some : (lowerAllg unit).toOption.isSome = true := by
  apply Gabbro.Grammatik.Uebersetzung.LibraryFixtureProofs.lowering_ok
  · rfl
  · cbv
  · rintro ⟨index, bound⟩
    have small : index < 4 := bound
    have choices : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
    rcases choices with rfl | rfl | rfl | rfl
    all_goals constructor <;> cbv

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

/-- Both interface refinement directions hold for every matching computed signature. -/
theorem interfaces : SchnittstellenPflicht unit := by
  apply witness_interfaces_empty
  · rintro ⟨index, bound⟩
    have small : index < 4 := bound
    have choices : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
    rcases choices with rfl | rfl | rfl | rfl
    all_goals cbv
  · intro n
    rcases n with _ | _ | _ | _ | n <;> constructor <;> cbv

theorem open_record (v : Gabbro.Body.Value)
    (h : v.hasShape (.record [.intIn 0 9, .bool]) = true) :
    ∃ (n : Int) (b : Bool), v = .record [.int n, .bool b] ∧ 0 ≤ n ∧ n ≤ 9 := by
  obtain ⟨vs, rfl, hlen, hf⟩ := Gabbro.Body.Value.hasShape_rec_true v _ h
  cases vs with
  | nil => cases hlen
  | cons a tail =>
      cases tail with
      | nil => cases hlen
      | cons b rest =>
          have hr : rest = [] := List.eq_nil_of_length_eq_zero (Nat.succ.inj (Nat.succ.inj hlen))
          subst rest
          have hs : a.hasShape (.intIn 0 9) = true ∧ b.hasShape .bool = true := by
            simpa only [Gabbro.Body.Value.fieldsHaveShape_cons_cons,
              Gabbro.Body.Value.fieldsHaveShape_nil_nil, Bool.and_true, Bool.and_eq_true] using hf
          obtain ⟨n, ha, hlo, hhi⟩ := Gabbro.Body.Value.hasShape_intIn_true a 0 9 hs.1
          obtain ⟨b', hb⟩ := Gabbro.Body.Value.hasShape_bool_true b hs.2
          exact ⟨n, b', by rw [ha, hb], hlo, hhi⟩

theorem build_meets : meetsU unit (wfU unit) build buildBody := by
  intro ρB s hW _
  change ∃ s', Gabbro.Body.finalState (Gabbro.Body.exec ρB buildBody s) = some s' ∧
    wfU unit s' ∧ ∃ v, Gabbro.Body.finalValue (Gabbro.Body.exec ρB buildBody s) = some v ∧
      v.hasShape (.record [.intIn 0 9, .bool]) = true
  exact ⟨s, rfl, hW, .record [.int 3, .bool true], rfl, by cbv⟩

theorem proj_meets : meetsU unit (wfU unit) proj projBody := by
  intro ρB s hW hpre
  change some (Gabbro.Body.Value.bool ((s.local' "r").hasShape (.record [.intIn 0 9, .bool]))) =
    some (Gabbro.Body.Value.bool true) at hpre
  have hshape : (s.local' "r").hasShape (.record [.intIn 0 9, .bool]) = true := by
    injection hpre with hpre
    injection hpre
  obtain ⟨n, b, hr, hlo, hhi⟩ := open_record _ hshape
  have hex : Gabbro.Body.exec ρB projBody s = .returned s (some (.int n)) := by
    simp only [projBody, Gabbro.Body.exec, Gabbro.Body.step, Gabbro.Body.eval, hr,
      List.getElem?_cons_zero]
  change ∃ s', Gabbro.Body.finalState (Gabbro.Body.exec ρB projBody s) = some s' ∧
    wfU unit s' ∧ ∃ x, Gabbro.Body.finalValue (Gabbro.Body.exec ρB projBody s) = some (.int x) ∧
      0 ≤ x ∧ x ≤ 9
  rw [hex]
  exact ⟨s, rfl, hW, n, rfl, hlo, hhi⟩

theorem upd_meets : meetsU unit (wfU unit) upd updBody := by
  intro ρB s hW hpre
  change some (Gabbro.Body.Value.bool ((s.local' "r").hasShape (.record [.intIn 0 9, .bool]))) =
    some (Gabbro.Body.Value.bool true) at hpre
  have hshape : (s.local' "r").hasShape (.record [.intIn 0 9, .bool]) = true := by
    injection hpre with hpre
    injection hpre
  obtain ⟨n, b, hr, _, _⟩ := open_record _ hshape
  let t : Gabbro.Body.State := ⟨s.world,
    Gabbro.Body.bindLocal (Gabbro.Body.bindLocal s.local' "out" (.record [.int n, .bool b]))
      "out" (.record [.int 5, .bool b])⟩
  have hex : Gabbro.Body.exec ρB updBody s = .returned t (some (.record [.int 5, .bool b])) := by
    simp [updBody, t, Gabbro.Body.exec, Gabbro.Body.step, Gabbro.Body.eval, hr,
      Gabbro.Body.bindLocal_here]
  change ∃ s', Gabbro.Body.finalState (Gabbro.Body.exec ρB updBody s) = some s' ∧
    wfU unit s' ∧ ∃ v, Gabbro.Body.finalValue (Gabbro.Body.exec ρB updBody s) = some v ∧
      v.hasShape (.record [.intIn 0 9, .bool]) = true
  rw [hex]
  refine ⟨t, rfl, hW, .record [.int 5, .bool b], rfl, ?_⟩
  simp [Gabbro.Body.Value.hasShape, Gabbro.Body.Value.fieldsHaveShape]

theorem identity_meets : meetsU unit (wfU unit) identity identityBody := by
  intro ρB s hW hpre
  change some (Gabbro.Body.Value.bool ((s.local' "r").hasShape (.record [.intIn 0 9, .bool]))) =
    some (Gabbro.Body.Value.bool true) at hpre
  have hshape : (s.local' "r").hasShape (.record [.intIn 0 9, .bool]) = true := by
    injection hpre with hpre
    injection hpre
  change ∃ s', Gabbro.Body.finalState (Gabbro.Body.exec ρB identityBody s) = some s' ∧
    wfU unit s' ∧ ∃ v, Gabbro.Body.finalValue (Gabbro.Body.exec ρB identityBody s) = some v ∧
      v.hasShape (.record [.intIn 0 9, .bool]) = true
  exact ⟨s, rfl, hW, s.local' "r", rfl, hshape⟩

theorem duties : ∀ c : Fin unit.fns.length, ∃ bs,
    zuBodyZ unit (fnAt unit c) = some bs ∧ meetsU unit (wfU unit) (fnAt unit c) bs := by
  intro ⟨c, hc⟩
  rcases c with _ | _ | _ | _ | c
  · exact ⟨buildBody, reader_forms.1, build_meets⟩
  · exact ⟨projBody, reader_forms.2.1, proj_meets⟩
  · exact ⟨updBody, reader_forms.2.2.1, upd_meets⟩
  · exact ⟨identityBody, reader_forms.2.2.2, identity_meets⟩
  · have hh : c + 4 < 4 := hc
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

/-- The four record cases, source anchor, interfaces, duties and final source theorem are joint. -/
theorem nutzer_aus_quelleG_record_zeuge :
    PflichtenTeilG source (u := unit) (fun _ => True) ∧
      (∀ hn : nullB unit = true, OffeneStartPflicht unit (fun _ => True) program hn) ∧
      uebersetzeAllg source = .ok ⟨unit, program, functions⟩ ∧
      ∃ hn : nullB unit = true, Zielsatz.NutzerPflicht (einheitAllg unit program hn) := by
  have hStart : ∀ hn : nullB unit = true, OffeneStartPflicht unit (fun _ => True) program hn :=
    fun _ _ _ hc => (hc True.intro).elim
  exact ⟨carried_duties, hStart, translated, nutzer_aus_quelleG carried_duties hStart translated⟩

/-- No elaborated-unit measurement was run: record-typed slots and statics retain explicit
    refusal, and a record comparison does not enter the scalar contract fragment. -/
theorem storage_and_contract_refusals :
    keinBoolB { unit with tabs := [{ name := "Rows", count := 1, cols := [], werte := [("payload", schema.ty)] }] } = false ∧
    staticsB { unit with globs := [{ name := "saved", ty := .wert schema.ty, init := 0 }] } = false ∧
    ensExpr unit identity {} (.cmp "==" (.param "r") (.param "r")) = none := by
  cbv

#print axioms nutzer_aus_quelleG_record_zeuge

end Gabbro.Bruecke.RecordZeuge
