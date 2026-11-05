/-
  File:      Grammatik/Parser/Elab/Proben/Formen/UebersetzeProben31.lean
  Subject:   Track P: the pipeline with the declared starts (`uebersetzeMitStarts`): the `concurrent` members and
             the entry dispatch roots (`Starts.roots`), the handlers entered by hardware (`Starts.hands`) and the
             threads of `start { .. };` (`Starts.gestartet`), as functions of the declaration.
-/
module
public import Grammatik.Parser.Elab.UebersetzePipeline
public import Grammatik.Parser.Elab.Proben.Fruehe.UebersetzeProben3Basis
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil11
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil12
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Erzeuge
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Torhuelle
import all Grammatik.Parser.Elab.Generic.StaticConformance
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest1
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest2a
import all Grammatik.Parser.Elab.UebersetzeAllg3.Body
import all Grammatik.Parser.Elab.UebersetzeAllg3.Stufe
import all Grammatik.Parser.Elab.UebersetzeAllg3.Seq
import all Grammatik.Parser.Elab.UebersetzeAllg3.Struct
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
@[expose] public section


namespace Gabbro.Grammatik.Parser.UebersetzeProben31

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

set_option maxRecDepth 100000

/-- The function numbers of the declared starts: roots, handlers, started threads. -/
def startNr (s : String) : Option (List Nat × List Nat × List Nat) :=
  match uebersetzeMitStarts s with
  | .error _ => none
  | .ok ⟨_, _, _, st⟩ =>
    some (st.roots.map (fun (f : Fin _) => f.val), st.hands.map (fun (f : Fin _) => f.val),
          st.gestartet.map (fun (f : Fin _) => f.val))

/-- Two concurrent members, one of them also an interrupt handler through an entry with `via`. -/
def starts_ok : String :=
  "module m { impl fn w() { } impl fn r() { } concurrent { r, w }; entry e vector 1 via idt arch x86_64 { regs in { } regs out { } preserves { } clobbers { } stack k per cpu nested never dispatch m::w; } }"

/-- A thread created by `start { .. };`. -/
def gestartet_ok : String :=
  "module m { impl fn w() { } impl fn h() { start { w }; } concurrent { h }; }"

/-- A start that names a function with parameters has no form: no starts are returned. -/
def starts_refused : String :=
  "module m { impl fn w(a : u32 in 0 .. 1) { } concurrent { w }; }"

/-! Keep the canonical fuel record symbolic and select only the operation used
    by an actual body. These are the existing production equations. -/
attribute [local cbv_opaque] lowStufe lowSeqL lowStructL
attribute [local cbv_eval] UebersetzeProben2.seq_select UebersetzeProben2.struct_select
  lowStufe_seq lowStufe_struct

private def startFields (unit : Uebersetze.UProg) : List Nat × List Nat × List Nat :=
  ((startsOf unit).roots.map (fun f : Fin unit.fns.length => f.val),
    (startsOf unit).hands.map (fun f : Fin unit.fns.length => f.val),
    (startsOf unit).gestartet.map (fun f : Fin unit.fns.length => f.val))

/-- Extract actual success from the certified lowering diagnostic, without
    evaluating the dependent program assembled by lowerAllg. -/
private theorem lower_success (unit : Uebersetze.UProg)
    (stage : UebersetzeProben2.lowerStage unit = "OK") :
    (lowerAllg unit).toOption.isSome = true := by
  cases outcome : lowerAllg unit with
  | ok value => rfl
  | error error =>
    have mismatch : "lower: " ++ error = "OK" := by
      simpa only [UebersetzeProben2.lowerStage, outcome] using stage
    have first := congrArg (fun text : String => text.toList.head?) mismatch
    rw [String.toList_append] at first
    change (some 'l' : Option Char) = some 'O' at first
    exact False.elim ((by decide : (some 'l' : Option Char) ≠ some 'O') first)

private theorem startNr_phases {source : String} {characters : List Char} {tokens : List Token}
    {items : List SItemTief} {unit : Uebersetze.UProg} {expected : List Nat × List Nat × List Nat}
    (text : source = String.ofList characters) (lexed : lexL characters = .ok tokens)
    (parsed : parseTopTief tokens = .ok items) (elaborated : elabU (pre108 items) = .ok unit)
    (lowered : (lowerAllg unit).toOption.isSome = true) (observed : startFields unit = expected) :
    startNr source = some expected := by
  let payload : Programm (declOf unit) × List (declOf unit).Fn :=
    (lowerAllg unit).toOption.get lowered
  have body : lowerAllg unit = .ok (payload.1, payload.2) :=
    except_ok_get (ε := String) (α := Programm (declOf unit) × List (declOf unit).Fn)
      (x := lowerAllg unit) lowered
  have pipeline := uebersetzeAllg_von_zeichen lexed parsed elaborated body
  have withStarts := uebersetzeMitStarts_ok pipeline
  rw [text]
  unfold startNr
  rw [withStarts]
  exact congrArg some observed

private theorem startNr_elab_error {source : String} {characters : List Char} {tokens : List Token}
    {items : List SItemTief} {error : String}
    (text : source = String.ofList characters) (lexed : lexL characters = .ok tokens)
    (parsed : parseTopTief tokens = .ok items) (elaborated : elabU (pre108 items) = .error error) :
    startNr source = none := by
  rw [text]
  unfold startNr uebersetzeMitStarts uebersetzeAllg
  rw [lex_ofList, lexed]
  dsimp only
  rw [parsed]
  dsimp only
  rw [elaborated]

private theorem scan_compose {source rest : List Char} {fuel remaining : Nat}
    {emitted tokens : List Token} (tail : scan false rest remaining = .ok tokens)
    (head : scan false source fuel =
      emitted.foldr (fun t result => Except.map (t :: ·) result) (scan false rest remaining)) :
    scan false source fuel = .ok (emitted ++ tokens) := by
  rw [tail, UebersetzeProben2.token_maps] at head
  exact head

private def tokens_fn_r : List Token := [.wort "impl", .wort "fn", .wort "r", .zeichen "(", .zeichen ")", .zeichen "{", .zeichen "}"]

private theorem scan_fn_r (rest : List Char) (n : Nat) :
    scan false (['i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'r', '(', ')', ' ', '{', ' ', '}', ' '] ++ rest) (n + 12) =
      tokens_fn_r.foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

private def tokens_roots_rw : List Token := [.wort "r", .zeichen ",", .wort "w", .zeichen "}", .zeichen ";"]

private theorem scan_roots_rw (rest : List Char) (n : Nat) :
    scan false (['r', ',', ' ', 'w', ' ', '}', ';', ' '] ++ rest) (n + 8) =
      tokens_roots_rw.foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

private def tokens_fn_h_open : List Token := [.wort "impl", .wort "fn", .ident "h", .zeichen "(", .zeichen ")", .zeichen "{"]

private theorem scan_fn_h_open (rest : List Char) (n : Nat) :
    scan false (['i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'h', '(', ')', ' ', '{', ' '] ++ rest) (n + 10) =
      tokens_fn_h_open.foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

private def tokens_spawn_w : List Token := [.ident "start", .zeichen "{", .wort "w", .zeichen "}", .zeichen ";"]

private theorem scan_spawn_w (rest : List Char) (n : Nat) :
    scan false (['s', 't', 'a', 'r', 't', ' ', '{', ' ', 'w', ' ', '}', ';', ' '] ++ rest) (n + 9) =
      tokens_spawn_w.foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

private def tokens_root_h : List Token := [.ident "h", .zeichen "}", .zeichen ";"]

private theorem scan_root_h (rest : List Char) (n : Nat) :
    scan false (['h', ' ', '}', ';', ' '] ++ rest) (n + 5) =
      tokens_root_h.foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

private def tokens_fn_w_parameter : List Token := [.wort "impl", .wort "fn", .wort "w", .zeichen "(", .ident "a", .zeichen ":", .wort "u32", .wort "in", .num 0, .zeichen ".."]

private theorem scan_fn_w_parameter (rest : List Char) (n : Nat) :
    scan false (['i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'w', '(', 'a', ' ', ':', ' ', 'u', '3', '2', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' '] ++ rest) (n + 18) =
      tokens_fn_w_parameter.foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

private def starts_ok_characters : List Char :=
  ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'm', ' ', '{', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'w', '(', ')', ' ',
   '{', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'r', '(', ')', ' ', '{', ' ', '}', ' ', 'c', 'o', 'n',
   'c', 'u', 'r', 'r', 'e', 'n', 't', ' ', '{', ' ', 'r', ',', ' ', 'w', ' ', '}', ';', ' ', 'e', 'n', 't', 'r', 'y',
   ' ', 'e', ' ', 'v', 'e', 'c', 't', 'o', 'r', ' ', '1', ' ', 'v', 'i', 'a', ' ', 'i', 'd', 't', ' ', 'a', 'r', 'c',
   'h', ' ', 'x', '8', '6', '_', '6', '4', ' ', '{', ' ', 'r', 'e', 'g', 's', ' ', 'i', 'n', ' ', '{', ' ', '}', ' ',
   'r', 'e', 'g', 's', ' ', 'o', 'u', 't', ' ', '{', ' ', '}', ' ', 'p', 'r', 'e', 's', 'e', 'r', 'v', 'e', 's', ' ',
   '{', ' ', '}', ' ', 'c', 'l', 'o', 'b', 'b', 'e', 'r', 's', ' ', '{', ' ', '}', ' ', 's', 't', 'a', 'c', 'k', ' ',
   'k', ' ', 'p', 'e', 'r', ' ', 'c', 'p', 'u', ' ', 'n', 'e', 's', 't', 'e', 'd', ' ', 'n', 'e', 'v', 'e', 'r', ' ',
   'd', 'i', 's', 'p', 'a', 't', 'c', 'h', ' ', 'm', ':', ':', 'w', ';', ' ', '}', ' ', '}']

private def starts_ok_tokens : List Token :=
  UebersetzeProben3.tokens_module ++ UebersetzeProben3.tokens_fn_w ++ tokens_fn_r ++
    UebersetzeProben3.tokens_concurrent ++ tokens_roots_rw ++ UebersetzeProben3.tokens_entry_e ++
    UebersetzeProben3.tokens_via ++ UebersetzeProben3.tokens_arch ++ UebersetzeProben3.tokens_regs ++
    UebersetzeProben3.tokens_preserves ++ UebersetzeProben3.tokens_stack ++
    UebersetzeProben3.tokens_dispatch_w ++ UebersetzeProben3.tokens_close ++ [.zeichen "}", .ende]

private theorem starts_ok_lexed : lexL starts_ok_characters = .ok starts_ok_tokens := by
  change scan false starts_ok_characters 203 = .ok starts_ok_tokens
  have composed := scan_compose (UebersetzeProben2.scan_end 93) (UebersetzeProben2.scan_close (starts_ok_characters.drop 201) 94)
  have composed := scan_compose composed (UebersetzeProben3.scan3_dispatch_w (starts_ok_characters.drop 199) 96)
  have composed := scan_compose composed (UebersetzeProben3.scan3_stack (starts_ok_characters.drop 184) 103)
  have composed := scan_compose composed (UebersetzeProben3.scan3_preserves (starts_ok_characters.drop 155) 115)
  have composed := scan_compose composed (UebersetzeProben3.scan3_regs (starts_ok_characters.drop 128) 127)
  have composed := scan_compose composed (UebersetzeProben3.scan3_arch (starts_ok_characters.drop 103) 143)
  have composed := scan_compose composed (UebersetzeProben3.scan3_via (starts_ok_characters.drop 89) 149)
  have composed := scan_compose composed (UebersetzeProben3.scan3_entry_e (starts_ok_characters.drop 81) 153)
  have composed := scan_compose composed (scan_roots_rw (starts_ok_characters.drop 64) 161)
  have composed := scan_compose composed (UebersetzeProben3.scan3_concurrent (starts_ok_characters.drop 56) 169)
  have composed := scan_compose composed (scan_fn_r (starts_ok_characters.drop 43) 173)
  have composed := scan_compose composed (UebersetzeProben3.scan3_fn_w (starts_ok_characters.drop 27) 185)
  have complete := scan_compose composed (UebersetzeProben3.scan3_module (starts_ok_characters.drop 11) 197)
  exact complete

private theorem starts_ok_text : starts_ok = String.ofList starts_ok_characters := by cbv

private theorem starts_ok_parsed : (parseTopTief starts_ok_tokens).toOption.isSome = true := by cbv
private def starts_ok_items : List SItemTief := (parseTopTief starts_ok_tokens).toOption.get starts_ok_parsed

private def gestartet_ok_characters : List Char :=
  ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'm', ' ', '{', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'w', '(', ')', ' ',
   '{', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'h', '(', ')', ' ', '{', ' ', 's', 't', 'a', 'r', 't',
   ' ', '{', ' ', 'w', ' ', '}', ';', ' ', '}', ' ', 'c', 'o', 'n', 'c', 'u', 'r', 'r', 'e', 'n', 't', ' ', '{', ' ',
   'h', ' ', '}', ';', ' ', '}']

private def gestartet_ok_tokens : List Token :=
  UebersetzeProben3.tokens_module ++ UebersetzeProben3.tokens_fn_w ++ tokens_fn_h_open ++ tokens_spawn_w ++
    UebersetzeProben3.tokens_close ++ UebersetzeProben3.tokens_concurrent ++ tokens_root_h ++
    [.zeichen "}", .ende]

private theorem gestartet_ok_lexed : lexL gestartet_ok_characters = .ok gestartet_ok_tokens := by
  change scan false gestartet_ok_characters 76 = .ok gestartet_ok_tokens
  have composed := scan_compose (UebersetzeProben2.scan_end 27) (scan_root_h (gestartet_ok_characters.drop 74) 28)
  have composed := scan_compose composed (UebersetzeProben3.scan3_concurrent (gestartet_ok_characters.drop 69) 33)
  have composed := scan_compose composed (UebersetzeProben2.scan_close (gestartet_ok_characters.drop 56) 37)
  have composed := scan_compose composed (scan_spawn_w (gestartet_ok_characters.drop 54) 39)
  have composed := scan_compose composed (scan_fn_h_open (gestartet_ok_characters.drop 41) 48)
  have composed := scan_compose composed (UebersetzeProben3.scan3_fn_w (gestartet_ok_characters.drop 27) 58)
  have complete := scan_compose composed (UebersetzeProben3.scan3_module (gestartet_ok_characters.drop 11) 70)
  exact complete

private theorem gestartet_ok_text : gestartet_ok = String.ofList gestartet_ok_characters := by cbv

private theorem gestartet_ok_parsed : (parseTopTief gestartet_ok_tokens).toOption.isSome = true := by cbv
private def gestartet_ok_items : List SItemTief := (parseTopTief gestartet_ok_tokens).toOption.get gestartet_ok_parsed

private def starts_refused_characters : List Char :=
  ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'm', ' ', '{', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'w', '(', 'a', ' ',
   ':', ' ', 'u', '3', '2', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', ')', ' ', '{', ' ', '}', ' ', 'c', 'o',
   'n', 'c', 'u', 'r', 'r', 'e', 'n', 't', ' ', '{', ' ', 'w', ' ', '}', ';', ' ', '}']

private def starts_refused_tokens : List Token :=
  UebersetzeProben3.tokens_module ++ tokens_fn_w_parameter ++ UebersetzeProben3.tokens_int_tail ++
    UebersetzeProben3.tokens_concurrent ++ UebersetzeProben3.tokens_root_w ++ [.zeichen "}", .ende]

private theorem starts_refused_lexed : lexL starts_refused_characters = .ok starts_refused_tokens := by
  change scan false starts_refused_characters 64 = .ok starts_refused_tokens
  have composed := scan_compose (UebersetzeProben2.scan_end 23) (UebersetzeProben3.scan3_root_w (starts_refused_characters.drop 62) 24)
  have composed := scan_compose composed (UebersetzeProben3.scan3_concurrent (starts_refused_characters.drop 57) 29)
  have composed := scan_compose composed (UebersetzeProben3.scan3_int_tail (starts_refused_characters.drop 44) 33)
  have composed := scan_compose composed (scan_fn_w_parameter (starts_refused_characters.drop 37) 40)
  have complete := scan_compose composed (UebersetzeProben3.scan3_module (starts_refused_characters.drop 11) 58)
  exact complete

private theorem starts_refused_text : starts_refused = String.ofList starts_refused_characters := by cbv

private theorem starts_refused_parsed : (parseTopTief starts_refused_tokens).toOption.isSome = true := by cbv
private def starts_refused_items : List SItemTief := (parseTopTief starts_refused_tokens).toOption.get starts_refused_parsed

private theorem starts_ok_elaborated :
    (elabU (pre108 starts_ok_items)).toOption.isSome = true := by cbv
private def starts_ok_unit : Uebersetze.UProg :=
  (elabU (pre108 starts_ok_items)).toOption.get starts_ok_elaborated

/-- Construct the complete package on the actual result before introducing a function index. -/
private theorem starts_ok_metadata : starts_ok_unit.invs = [] ∧
    contractGate starts_ok_unit = true ∧
    (∀ f : Fin starts_ok_unit.fns.length,
      (lowerFnAt starts_ok_unit f).toOption.isSome = true ∧
        (fnAt starts_ok_unit f).decreases = none) ∧
    startFields starts_ok_unit = ([1, 0, 0], [0], []) := by
  have certificate : ∃ unit : Uebersetze.UProg,
      elabU (pre108 starts_ok_items) = .ok unit ∧ unit.invs = [] ∧ contractGate unit = true ∧
      (∀ f : Fin unit.fns.length,
        (lowerFnAt unit f).toOption.isSome = true ∧ (fnAt unit f).decreases = none) ∧
      startFields unit = ([1, 0, 0], [0], []) := by
    refine ⟨?unit, ?elaborated, ?invariants, ?contracts, ?functions, ?observed⟩
    case elaborated => cbv <;> exact Eq.refl _
    case invariants => cbv
    case contracts => cbv
    case functions =>
      intro f
      rcases f with ⟨index, bound⟩
      have small : index < 2 := bound
      rcases (by omega : index = 0 ∨ index = 1) with rfl | rfl <;>
        constructor <;> cbv
    case observed => cbv
  obtain ⟨unit, elaborated, facts⟩ := certificate
  have same : unit = starts_ok_unit := Except.ok.inj (elaborated.symm.trans
    (except_ok_get (ε := String) (α := Uebersetze.UProg)
      (x := elabU (pre108 starts_ok_items)) starts_ok_elaborated))
  cases same
  exact facts

private theorem starts_ok_lowered : (lowerAllg starts_ok_unit).toOption.isSome = true :=
  lower_success starts_ok_unit (UebersetzeProben2.lowerStage_ok starts_ok_unit
    starts_ok_metadata.1 starts_ok_metadata.2.2.1 starts_ok_metadata.2.1)

private theorem gestartet_ok_elaborated :
    (elabU (pre108 gestartet_ok_items)).toOption.isSome = true := by cbv
private def gestartet_ok_unit : Uebersetze.UProg :=
  (elabU (pre108 gestartet_ok_items)).toOption.get gestartet_ok_elaborated

/-- Construct the complete package on the actual result before introducing a function index. -/
private theorem gestartet_ok_metadata : gestartet_ok_unit.invs = [] ∧
    contractGate gestartet_ok_unit = true ∧
    (∀ f : Fin gestartet_ok_unit.fns.length,
      (lowerFnAt gestartet_ok_unit f).toOption.isSome = true ∧
        (fnAt gestartet_ok_unit f).decreases = none) ∧
    startFields gestartet_ok_unit = ([1], [], [0]) := by
  have certificate : ∃ unit : Uebersetze.UProg,
      elabU (pre108 gestartet_ok_items) = .ok unit ∧ unit.invs = [] ∧ contractGate unit = true ∧
      (∀ f : Fin unit.fns.length,
        (lowerFnAt unit f).toOption.isSome = true ∧ (fnAt unit f).decreases = none) ∧
      startFields unit = ([1], [], [0]) := by
    refine ⟨?unit, ?elaborated, ?invariants, ?contracts, ?functions, ?observed⟩
    case elaborated => cbv <;> exact Eq.refl _
    case invariants => cbv
    case contracts => cbv
    case functions =>
      intro f
      rcases f with ⟨index, bound⟩
      have small : index < 2 := bound
      rcases (by omega : index = 0 ∨ index = 1) with rfl | rfl <;>
        constructor <;> cbv
    case observed => cbv
  obtain ⟨unit, elaborated, facts⟩ := certificate
  have same : unit = gestartet_ok_unit := Except.ok.inj (elaborated.symm.trans
    (except_ok_get (ε := String) (α := Uebersetze.UProg)
      (x := elabU (pre108 gestartet_ok_items)) gestartet_ok_elaborated))
  cases same
  exact facts

private theorem gestartet_ok_lowered : (lowerAllg gestartet_ok_unit).toOption.isSome = true :=
  lower_success gestartet_ok_unit (UebersetzeProben2.lowerStage_ok gestartet_ok_unit
    gestartet_ok_metadata.1 gestartet_ok_metadata.2.2.1 gestartet_ok_metadata.2.1)

private theorem starts_refused_elaborated :
    elabU (pre108 starts_refused_items) =
      .error "concurrent member with 0 arguments for 1 parameters: w" := by cbv

theorem starts_ok_nr : startNr starts_ok = some ([1, 0, 0], [0], []) :=
  startNr_phases (source := starts_ok) (characters := starts_ok_characters)
    (tokens := starts_ok_tokens) (items := starts_ok_items) (unit := starts_ok_unit)
    starts_ok_text starts_ok_lexed
    (except_ok_get (ε := String) (α := List SItemTief)
      (x := parseTopTief starts_ok_tokens) starts_ok_parsed)
    (except_ok_get (ε := String) (α := Uebersetze.UProg)
      (x := elabU (pre108 starts_ok_items)) starts_ok_elaborated)
    starts_ok_lowered starts_ok_metadata.2.2.2

theorem gestartet_ok_nr : startNr gestartet_ok = some ([1], [], [0]) :=
  startNr_phases (source := gestartet_ok) (characters := gestartet_ok_characters)
    (tokens := gestartet_ok_tokens) (items := gestartet_ok_items) (unit := gestartet_ok_unit)
    gestartet_ok_text gestartet_ok_lexed
    (except_ok_get (ε := String) (α := List SItemTief)
      (x := parseTopTief gestartet_ok_tokens) gestartet_ok_parsed)
    (except_ok_get (ε := String) (α := Uebersetze.UProg)
      (x := elabU (pre108 gestartet_ok_items)) gestartet_ok_elaborated)
    gestartet_ok_lowered gestartet_ok_metadata.2.2.2

theorem starts_refused_nr : startNr starts_refused = none :=
  startNr_elab_error (source := starts_refused) (characters := starts_refused_characters)
    (tokens := starts_refused_tokens) (items := starts_refused_items)
    starts_refused_text starts_refused_lexed
    (except_ok_get (ε := String) (α := List SItemTief)
      (x := parseTopTief starts_refused_tokens) starts_refused_parsed) starts_refused_elaborated

end Gabbro.Grammatik.Parser.UebersetzeProben31
