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

/-! # Joint source witness for bool results, parameters, locals and conditions -/

namespace Gabbro.Bruecke.BoolZeuge

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

open Gabbro.Grammatik.Uebersetzung.LibraryFixtureScanning

set_option maxRecDepth 100000
set_option maxHeartbeats 400000

attribute [local cbv_eval] Parser.strEq_apply_eq_decide

attribute [local cbv_eval] Nat.log2_def lowEns.eq_def lowCmp.eq_def lowWertE.eq_def

def predicate : UFn :=
  { name := "is_digit"
    params := [("ch", .int 0 127)]
    kinds := [.int]
    res := none
    resBool := true
    held := []
    puts := []
    gives := []
    body := []
    ret := .bool (.and (.cmp ">=" (.param "ch") (.lit 48)) (.cmp "<=" (.param "ch") (.lit 57))) }

def toggle : UFn :=
  { name := "toggle"
    params := [("enabled", .bool)]
    kinds := [.bool]
    res := none
    resBool := true
    held := []
    puts := []
    gives := []
    body := [.bindB "seen" .fls, .ifBeg (.var "enabled"), .setVarB "seen" .tru,
      .ifElse, .blkEnd, .ifBeg (.var "seen"), .setVarB "seen" .fls,
      .ifElse, .ret (.bool .tru), .blkEnd]
    ret := .bool (.var "seen") }

def caller : UFn :=
  { name := "use_bools"
    params := []
    kinds := []
    res := none
    held := []
    puts := []
    gives := []
    body := [.call "is_digit" [.val (.lit 55)], .call "toggle" [.bval .tru]]
    ret := .empty }

def unit : UProg :=
  { tabs := []
    locks := []
    fns := [predicate, toggle, caller] }

-- Each scanner certificate keeps an arbitrary suffix and remaining fuel.
-- module bools { impl fn is_digit(ch : u8
def sourceChunk0 : Chunk where
  characters := ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'b', 'o', 'o', 'l', 's', ' ', '{', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n',
    ' ', 'i', 's', '_', 'd', 'i', 'g', 'i', 't', '(', 'c', 'h', ' ', ':', ' ', 'u', '8', ' ']
  tokens := [.wort "module", .ident "bools", .zeichen "{", .wort "impl", .wort "fn", .ident "is_digit",
    .zeichen "(", .ident "ch", .zeichen ":", .wort "u8"]
  steps := 18
  scanned := by intro rest remaining; cbv

-- in 0 .. 127) -> bool { return ch >= 48 &&
def sourceChunk1 : Chunk where
  characters := ['i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '2', '7', ')', ' ', '-', '>', ' ', 'b', 'o', 'o', 'l', ' ', '{',
    ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'c', 'h', ' ', '>', '=', ' ', '4', '8', ' ', '&', '&', ' ']
  tokens := [.wort "in", .num 0, .zeichen "..", .num 127, .zeichen ")", .zeichen "->",
    .wort "bool", .zeichen "{", .wort "return", .ident "ch", .zeichen ">=", .num 48,
    .zeichen "&&"]
  steps := 25
  scanned := by intro rest remaining; cbv

-- ch <= 57; } impl fn toggle(enabled :
def sourceChunk2 : Chunk where
  characters := ['c', 'h', ' ', '<', '=', ' ', '5', '7', ';', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 't', 'o',
    'g', 'g', 'l', 'e', '(', 'e', 'n', 'a', 'b', 'l', 'e', 'd', ' ', ':', ' ']
  tokens := [.ident "ch", .zeichen "<=", .num 57, .zeichen ";", .zeichen "}", .wort "impl",
    .wort "fn", .ident "toggle", .zeichen "(", .ident "enabled", .zeichen ":"]
  steps := 19
  scanned := by intro rest remaining; cbv

-- bool) -> bool { let mut seen : bool =
def sourceChunk3 : Chunk where
  characters := ['b', 'o', 'o', 'l', ')', ' ', '-', '>', ' ', 'b', 'o', 'o', 'l', ' ', '{', ' ', 'l', 'e', 't', ' ', 'm', 'u',
    't', ' ', 's', 'e', 'e', 'n', ' ', ':', ' ', 'b', 'o', 'o', 'l', ' ', '=', ' ']
  tokens := [.wort "bool", .zeichen ")", .zeichen "->", .wort "bool", .zeichen "{", .wort "let",
    .wort "mut", .ident "seen", .zeichen ":", .wort "bool", .zeichen "="]
  steps := 21
  scanned := by intro rest remaining; cbv

-- false; if enabled { seen = true; } if
def sourceChunk4 : Chunk where
  characters := ['f', 'a', 'l', 's', 'e', ';', ' ', 'i', 'f', ' ', 'e', 'n', 'a', 'b', 'l', 'e', 'd', ' ', '{', ' ', 's', 'e',
    'e', 'n', ' ', '=', ' ', 't', 'r', 'u', 'e', ';', ' ', '}', ' ', 'i', 'f', ' ']
  tokens := [.wort "false", .zeichen ";", .wort "if", .ident "enabled", .zeichen "{", .ident "seen",
    .zeichen "=", .wort "true", .zeichen ";", .zeichen "}", .wort "if"]
  steps := 20
  scanned := by intro rest remaining; cbv

-- seen { seen = false; } else { return
def sourceChunk5 : Chunk where
  characters := ['s', 'e', 'e', 'n', ' ', '{', ' ', 's', 'e', 'e', 'n', ' ', '=', ' ', 'f', 'a', 'l', 's', 'e', ';', ' ', '}',
    ' ', 'e', 'l', 's', 'e', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ']
  tokens := [.ident "seen", .zeichen "{", .ident "seen", .zeichen "=", .wort "false", .zeichen ";",
    .zeichen "}", .wort "else", .zeichen "{", .wort "return"]
  steps := 19
  scanned := by intro rest remaining; cbv

-- true; } return seen; } impl fn
def sourceChunk6 : Chunk where
  characters := ['t', 'r', 'u', 'e', ';', ' ', '}', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 's', 'e', 'e', 'n', ';', ' ', '}',
    ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ']
  tokens := [.wort "true", .zeichen ";", .zeichen "}", .wort "return", .ident "seen", .zeichen ";",
    .zeichen "}", .wort "impl", .wort "fn"]
  steps := 16
  scanned := by intro rest remaining; cbv

-- use_bools() { is_digit(55); toggle(true);
def sourceChunk7 : Chunk where
  characters := ['u', 's', 'e', '_', 'b', 'o', 'o', 'l', 's', '(', ')', ' ', '{', ' ', 'i', 's', '_', 'd', 'i', 'g', 'i', 't',
    '(', '5', '5', ')', ';', ' ', 't', 'o', 'g', 'g', 'l', 'e', '(', 't', 'r', 'u', 'e', ')', ';', ' ']
  tokens := [.ident "use_bools", .zeichen "(", .zeichen ")", .zeichen "{", .ident "is_digit", .zeichen "(",
    .num 55, .zeichen ")", .zeichen ";", .ident "toggle", .zeichen "(", .wort "true",
    .zeichen ")", .zeichen ";"]
  steps := 18
  scanned := by intro rest remaining; cbv

-- } }
def sourceChunk8 : Chunk where
  characters := ['}', ' ', '}']
  tokens := [.zeichen "}", .zeichen "}"]
  steps := 3
  scanned := by intro rest remaining; cbv

def sourceChunks : List Chunk :=
  [sourceChunk0, sourceChunk1, sourceChunk2, sourceChunk3, sourceChunk4, sourceChunk5, sourceChunk6, sourceChunk7, sourceChunk8]

def source : String := String.ofList (characters sourceChunks)

def predicateBody : List Gabbro.Body.Stmt :=
  [.ret (some (.bin .and (.bin .ge (.name "ch") (.lit (.int 48)))
    (.bin .le (.name "ch") (.lit (.int 57)))))]

def toggleBody : List Gabbro.Body.Stmt :=
  [.bindName "seen" (.lit (.bool false)),
    .ite (.name "enabled") [.bindName "seen" (.lit (.bool true))] [],
    .ite (.name "seen") [.bindName "seen" (.lit (.bool false))]
      [.ret (some (.lit (.bool true)))],
    .ret (some (.name "seen"))]

def callerBody : List Gabbro.Body.Stmt :=
  [.call "is_digit" ["ch"] [.lit (.int 55)] (.hasShape "ch" (.intIn 0 127)),
    .call "toggle" ["enabled"] [.lit (.bool true)] (.hasShape "enabled" .bool)]

theorem reader_forms :
    zuBodyZ unit predicate = some predicateBody ∧ zuBodyZ unit toggle = some toggleBody ∧
      zuBodyZ unit caller = some callerBody :=
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

theorem exported : elabU (pre108 parsed.val) = .ok unit := by cbv

theorem translated : uebersetzeAllg source = .ok ⟨unit, program, functions⟩ :=
  witness_translation scanned.property parsed.property exported lowered

/-- Both refinement directions are checked against the actual lowered contracts and signatures. -/
theorem interfaces : SchnittstellenPflicht unit := by
  apply witness_interfaces_empty
  · rintro ⟨index, bound⟩
    have small : index < 3 := bound
    have choices : index = 0 ∨ index = 1 ∨ index = 2 := by omega
    rcases choices with rfl | rfl | rfl
    all_goals cbv
  · intro n
    rcases n with _ | _ | _ | n <;> constructor <;> cbv

theorem predicate_meets : meetsU unit (wfU unit) predicate predicateBody := by
  intro ρB s hW hpre
  change some (Gabbro.Body.Value.bool ((s.local' "ch").hasShape (.intIn 0 127))) = some (Gabbro.Body.Value.bool true) at hpre
  have hshape := Option.some.inj hpre
  injection hshape with hshape
  obtain ⟨n, hn, _, _⟩ := Gabbro.Body.Value.hasShape_intIn_true (s.local' "ch") 0 127 hshape
  have hex : Gabbro.Body.exec ρB predicateBody s =
      .returned s (some (.bool (decide (n ≥ 48) && decide (n ≤ 57)))) := by
    simp only [predicateBody, Gabbro.Body.exec, Gabbro.Body.step, Gabbro.Body.eval, hn,
      Gabbro.Body.binop, Gabbro.Body.andBool_some]
  change ∃ s', Gabbro.Body.finalState (Gabbro.Body.exec ρB predicateBody s) = some s' ∧
    (postU unit (wfU unit) predicate s s'
      (Gabbro.Body.finalValue (Gabbro.Body.exec ρB predicateBody s))).getD False
  rw [hex]
  exact ⟨s, rfl, hW, _, rfl⟩

def middle (s : Gabbro.Body.State) (b : Bool) : Gabbro.Body.Binding :=
  let β := Gabbro.Body.bindLocal s.local' "seen" (.bool false)
  if b then Gabbro.Body.bindLocal β "seen" (.bool true) else β

def after (s : Gabbro.Body.State) (b : Bool) : Gabbro.Body.State :=
  ⟨s.world, if b then Gabbro.Body.bindLocal (middle s b) "seen" (.bool false) else middle s b⟩

theorem toggle_exec (ρB : Gabbro.Body.Env) (s : Gabbro.Body.State) (b : Bool)
    (hb : s.local' "enabled" = .bool b) :
    Gabbro.Body.exec ρB toggleBody s = .returned (after s b) (some (.bool (!b))) := by
  have hne : ("enabled" : String) ≠ "seen" := by decide
  cases b <;> simp only [toggleBody, Gabbro.Body.exec, Gabbro.Body.step, Gabbro.Body.eval,
    Gabbro.Body.bindLocal_here, Gabbro.Body.bindLocal_elsewhere _ _ _ _ hne, hb,
    after, middle, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

theorem toggle_meets : meetsU unit (wfU unit) toggle toggleBody := by
  intro ρB s hW hpre
  change some (Gabbro.Body.Value.bool ((s.local' "enabled").hasShape .bool)) = some (Gabbro.Body.Value.bool true) at hpre
  have hshape := Option.some.inj hpre
  injection hshape with hshape
  obtain ⟨b, hb⟩ := Gabbro.Body.Value.hasShape_bool_true (s.local' "enabled") hshape
  change ∃ s', Gabbro.Body.finalState (Gabbro.Body.exec ρB toggleBody s) = some s' ∧
    (postU unit (wfU unit) toggle s s'
      (Gabbro.Body.finalValue (Gabbro.Body.exec ρB toggleBody s))).getD False
  rw [toggle_exec ρB s b hb]
  exact ⟨after s b, rfl, hW, !b, rfl⟩

theorem caller_meets : meetsU unit (wfU unit) caller callerBody := by
  intro ρB s hW _
  change Gabbro.Body.Contract ρB "is_digit" (preProp (wfU unit) predicate)
      (fun s s' r => (postU unit (wfU unit) predicate s s' r).getD False) →
    Gabbro.Body.Frame ρB "is_digit" [callClock] →
    Gabbro.Body.Contract ρB "toggle" (preProp (wfU unit) toggle)
      (fun s s' r => (postU unit (wfU unit) toggle s s' r).getD False) →
    Gabbro.Body.Frame ρB "toggle" [callClock] →
    ∃ s', Gabbro.Body.finalState (Gabbro.Body.exec ρB callerBody s) = some s' ∧ wfU unit s'
  intro hdigit _ htoggle _
  let t0 : Gabbro.Body.State :=
    ⟨s.world, Gabbro.Body.bindAll ["ch"] [.int 55] (fun _ => .absent)⟩
  let t1 := (ρB "is_digit" t0).1
  have hw1 : wfU unit t1 := (hdigit t0 ⟨hW, rfl⟩).1
  let t2 : Gabbro.Body.State :=
    ⟨t1.world, Gabbro.Body.bindAll ["enabled"] [.bool true] (fun _ => .absent)⟩
  let t3 := (ρB "toggle" t2).1
  have hw3 : wfU unit t3 := (htoggle t2 ⟨hw1, rfl⟩).1
  exact ⟨⟨t3.world, s.local'⟩, rfl, hw3⟩

theorem duties : ∀ c : Fin unit.fns.length, ∃ bs,
    zuBodyZ unit (fnAt unit c) = some bs ∧ meetsU unit (wfU unit) (fnAt unit c) bs := by
  intro ⟨c, hc⟩
  rcases c with _ | _ | _ | c
  · exact ⟨predicateBody, reader_forms.1, predicate_meets⟩
  · exact ⟨toggleBody, reader_forms.2.1, toggle_meets⟩
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

/-- Source translation, computed-contract refinement and carried duties hold jointly. -/
theorem nutzer_aus_quelleG_bool_zeuge :
    PflichtenTeilG source (u := unit) (fun _ => True) ∧
      (∀ hn : nullB unit = true, OffeneStartPflicht unit (fun _ => True) program hn) ∧
      uebersetzeAllg source = .ok ⟨unit, program, functions⟩ ∧
      ∃ hn : nullB unit = true, Zielsatz.NutzerPflicht (einheitAllg unit program hn) := by
  have hStart : ∀ hn : nullB unit = true,
      OffeneStartPflicht unit (fun _ => True) program hn := fun _ _ _ hc => (hc True.intro).elim
  exact ⟨carried_duties, hStart, translated,
    nutzer_aus_quelleG carried_duties hStart translated⟩

/-- Bool shadowing retains the outer value positionally and restores it at block exit. -/
theorem shadowing_zeuge (β : Gabbro.Body.Binding) :
    PositionalLRel (caller.mitBindungB "flag") ["flag"] 0
      (Env.cons (D := declOf unit) (τ := .bool) true Env.nil)
      (Gabbro.Body.bindLocal (Gabbro.Body.bindLocal β "flag" (.bool true)) "flag#####" (.bool false)) := by
  have h0 : PositionalLRel caller [] 0 (Env.nil : Env (declOf unit) []) β := by
    refine ⟨rfl, List.Pairwise.nil, ?_⟩
    intro j id hj
    cases hj
  have h1 := h0.pushB "flag" "flag" (by decide) true
  have h2 := h1.pushB "flag" "flag#####" (by decide) false
  exact h2.tailB

/-- The actual reader allocates a separate identifier for the hidden bool local. -/
theorem shadowing_reader_zeuge :
    zuBodyZ unit { caller with
      body := [.bindB "flag" .tru, .ifBeg .tru, .bindB "flag" .fls, .ifElse, .blkEnd]
      ret := .bool (.var "flag") } =
      some [.bindName "flag" (.lit (.bool true)),
        .ite (.lit (.bool true)) [.bindName "flag#####" (.lit (.bool false))] [],
        .ret (some (.name "flag"))] := by
  cbv

/-- Unsupported bool storage is still refused by its explicit gate, not silently omitted. -/
theorem storage_refusals_zeuge :
    keinBoolB { unit with tabs := [{ name := "Flags", count := 1, cols := [], bools := ["ready"] }] } = false ∧
      staticsB { unit with globs := [{ name := "ready", ty := .bool, init := 0 }] } = false := by
  cbv

#print axioms nutzer_aus_quelleG_bool_zeuge

end Gabbro.Bruecke.BoolZeuge
