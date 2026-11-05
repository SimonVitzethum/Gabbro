/-
  File:      Grammatik/Parser/Elab/Proben/Fruehe/UebersetzeProben2Basis.lean
  Subject:   Canonical scanner and phase certificates for the unchanged lock fixtures.
-/
module
public import Grammatik.Parser.Elab.UebersetzePipeline
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


namespace Gabbro.Grammatik.Parser.UebersetzeProben2

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

set_option maxRecDepth 100000

/-- The stage of `uebersetzeAllg` that stops a source (`OK` when none does). -/
def stufe (s : String) : String :=
  match lex s with
  | .error _ => "lex"
  | .ok toks =>
    match parseTopTief toks with
    | .error e => "parse: " ++ e
    | .ok items =>
      match elabU (pre108 items) with
      | .error e => "elab: " ++ e
      | .ok u =>
        match lowerAllg u with
        | .error e => "lower: " ++ e
        | .ok _ => "OK"

/-- Name the existing diagnostic projection so dependent result matchers stay typed
    identically at every phase-certificate application. -/
def lowerStage (unit : Uebersetze.UProg) : String :=
  match lowerAllg unit with
  | .error error => "lower: " ++ error
  | .ok _ => "OK"

/-- Link the actual phases without reducing the UTF-8 decoder inside later proofs. -/
theorem stufe_phases {source : String} {characters : List Char} {tokens : List Token}
    {items : List SItemTief} {unit : Uebersetze.UProg} {answer : String}
    (text : source = String.ofList characters) (lexed : lexL characters = .ok tokens)
    (parsed : parseTopTief tokens = .ok items) (elaborated : elabU (pre108 items) = .ok unit)
    (lowered : lowerStage unit = answer) : stufe source = answer := by
  rw [text]
  unfold stufe
  rw [lex_ofList, lexed]
  dsimp only
  rw [parsed]
  dsimp only
  rw [elaborated]
  change lowerStage unit = answer
  exact lowered

/-- The existing sequence selector takes one level only when its source run needs it. -/
theorem seq_succ (u : Uebersetze.UProg) (caller : Fin u.fns.length) (n : Nat)
    {l : Bool} (Γ : Ctx) (fn : UFn) (Λ : List (Res (declOf u)))
    (pe : AtTop u caller Λ) (ss : List UStmt) :
    lowSeqL (l := l) u caller Γ fn (n + 1) Λ pe ss =
      lowSeqStep u caller (lowStufe u caller n) Γ fn Λ pe ss := rfl

-- Expose a match on the actual fuel argument before selecting its field.
-- The canonical record stays opaque and is unfolded by one level only.
theorem seq_select (u : Uebersetze.UProg) (caller : Fin u.fns.length) (n : Nat)
    {l : Bool} (Γ : Ctx) (fn : UFn) (Λ : List (Res (declOf u)))
    (pe : AtTop u caller Λ) (ss : List UStmt) :
    lowSeqL (l := l) u caller Γ fn n Λ pe ss = match n with
      | 0 => .error "lower: blocks nested too deep"
      | k + 1 => lowSeqStep (l := l) u caller (lowStufe u caller k) Γ fn Λ pe ss := by
  cases n <;> rfl

theorem struct_select (u : Uebersetze.UProg) (caller : Fin u.fns.length) (n : Nat)
    {l : Bool} (Γ : Ctx) (fn : UFn) (Λ : List (Res (declOf u)))
    (pe : AtTop u caller Λ) (s : UStmt) (ss : List UStmt) :
    lowStructL (l := l) u caller Γ fn n Λ pe s ss = match n with
      | 0 => .error "lower: blocks nested too deep"
      | k + 1 => lowStructStep (l := l) u caller (lowStufe u caller k) Γ fn Λ pe s ss := by
  cases n <;> rfl

-- Keep the canonical fuel record symbolic: evaluate its selected operation, not all 100000 levels.
-- These local proof rules are equations of the unchanged producer, not another lowering path.
attribute [local cbv_opaque] lowStufe lowSeqL lowStructL
attribute [local cbv_eval] seq_select struct_select lowStufe_seq lowStufe_struct

/-- Small equations of the existing scanner, with an unevaluated continuation.
    Each whitespace-terminated fragment consumes exactly its tokens and spaces. -/
theorem scan_prelude (rest : List Char) (n : Nat) :
    scan false (['m', 'o', 'd', 'u', 'l', 'e', ' ', 'm', ' ', '{', ' ', 't', 'a', 'b', 'l', 'e', ' ', 'T', ' ', 'c', 'o', 'u', 'n', 't', ' ', '2', ' ', '{', ' '] ++ rest) (n + 16) =
    [.wort "module", .ident "m", .zeichen "{", .wort "table", .ident "T", .wort "count", .num 2, .zeichen "{"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

theorem scan_slot (rest : List Char) (n : Nat) :
    scan false (['s', 'l', 'o', 't', ' ', '{', ' ', 'v', ' ', ':', ' ', 'u', '3', '2', ',', ' ', '}', ' ', '}', ' '] ++ rest) (n + 15) =
    [.wort "slot", .zeichen "{", .ident "v", .zeichen ":", .wort "u32", .zeichen ",", .zeichen "}", .zeichen "}"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

theorem scan_lock (rest : List Char) (n : Nat) :
    scan false (['l', 'o', 'c', 'k', ' ', 'L', ' ', 'p', 'r', 'o', 't', 'e', 'c', 't', 's', ' ', '{', ' ', 'T', ' ', '}', ' ', 'r', 'a', 'n', 'k', ' ', '0', ';', ' '] ++ rest) (n + 17) =
    [.wort "lock", .ident "L", .wort "protects", .zeichen "{", .ident "T", .zeichen "}", .wort "rank", .num 0, .zeichen ";"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

theorem scan_second_lock (rest : List Char) (n : Nat) :
    scan false (['l', 'o', 'c', 'k', ' ', 'M', ' ', 'p', 'r', 'o', 't', 'e', 'c', 't', 's', ' ', '{', ' ', '}', ' ', 'r', 'a', 'n', 'k', ' ', '1', ';', ' '] ++ rest) (n + 15) =
    [.wort "lock", .ident "M", .wort "protects", .zeichen "{", .zeichen "}", .wort "rank", .num 1, .zeichen ";"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

theorem scan_writer (rest : List Char) (n : Nat) :
    scan false (['i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'w', '(', 'k', ' ', ':', ' ', 'p', 't', 'r', '<', 'n', 'o', 'r', 'm', 'a', 'l', ',', ' ', 'r', 'w', '>', ' ', 'T', ',', ' '] ++ rest) (n + 21) =
    [.wort "impl", .wort "fn", .wort "w", .zeichen "(", .ident "k", .zeichen ":", .wort "ptr", .zeichen "<", .wort "normal", .zeichen ",", .wort "rw", .zeichen ">", .ident "T", .zeichen ","].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

theorem scan_callee (rest : List Char) (n : Nat) :
    scan false (['i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'g', '(', 'k', ' ', ':', ' ', 'p', 't', 'r', '<', 'n', 'o', 'r', 'm', 'a', 'l', ',', ' ', 'r', 'w', '>', ' ', 'T', ',', ' '] ++ rest) (n + 21) =
    [.wort "impl", .wort "fn", .ident "g", .zeichen "(", .ident "k", .zeichen ":", .wort "ptr", .zeichen "<", .wort "normal", .zeichen ",", .wort "rw", .zeichen ">", .ident "T", .zeichen ","].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

theorem scan_parameters (rest : List Char) (n : Nat) :
    scan false (['i', ' ', ':', ' ', 'i', 'n', 'd', 'e', 'x', ' ', 'i', 'n', 't', 'o', ' ', 'T', ')', ' ', 'e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' '] ++ rest) (n + 15) =
    [.ident "i", .zeichen ":", .wort "index", .wort "into", .ident "T", .zeichen ")", .wort "effects", .zeichen "{"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

theorem scan_effects (rest : List Char) (n : Nat) :
    scan false (['w', 'r', 'i', 't', 'e', 's', ' ', 'k', '.', 's', 'l', 'o', 't', 's', ',', ' ', 'l', 'o', 'c', 'k', 's', ' ', 'L', ' '] ++ rest) (n + 11) =
    [.wort "writes", .ident "k", .zeichen ".", .wort "slots", .zeichen ",", .wort "locks", .ident "L"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

theorem scan_two_effects (rest : List Char) (n : Nat) :
    scan false (['w', 'r', 'i', 't', 'e', 's', ' ', 'k', '.', 's', 'l', 'o', 't', 's', ',', ' ', 'l', 'o', 'c', 'k', 's', ' ', 'L', ',', ' ', 'l', 'o', 'c', 'k', 's', ' ', 'M', ' '] ++ rest) (n + 16) =
    [.wort "writes", .ident "k", .zeichen ".", .wort "slots", .zeichen ",", .wort "locks", .ident "L", .zeichen ",", .wort "locks", .ident "M"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

theorem scan_open (rest : List Char) (n : Nat) :
    scan false (['{', ' '] ++ rest) (n + 2) =
    [.zeichen "{"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

theorem scan_take (rest : List Char) (n : Nat) :
    scan false (['l', 'o', 'c', 'k', 's', ' ', 'L', ' ', '{', ' '] ++ rest) (n + 6) =
    [.wort "locks", .ident "L", .zeichen "{"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

theorem scan_take_second (rest : List Char) (n : Nat) :
    scan false (['l', 'o', 'c', 'k', 's', ' ', 'M', ' ', '{', ' '] ++ rest) (n + 6) =
    [.wort "locks", .ident "M", .zeichen "{"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

theorem scan_write_one (rest : List Char) (n : Nat) :
    scan false (['k', '.', 's', 'l', 'o', 't', 's', '[', 'i', ']', '.', 'v', ' ', '=', ' ', '1', ';', ' '] ++ rest) (n + 14) =
    [.ident "k", .zeichen ".", .wort "slots", .zeichen "[", .ident "i", .zeichen "]", .zeichen ".", .ident "v", .zeichen "=", .num 1, .zeichen ";"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

theorem scan_write_two (rest : List Char) (n : Nat) :
    scan false (['k', '.', 's', 'l', 'o', 't', 's', '[', 'i', ']', '.', 'v', ' ', '=', ' ', '2', ';', ' '] ++ rest) (n + 14) =
    [.ident "k", .zeichen ".", .wort "slots", .zeichen "[", .ident "i", .zeichen "]", .zeichen ".", .ident "v", .zeichen "=", .num 2, .zeichen ";"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

theorem scan_write_three (rest : List Char) (n : Nat) :
    scan false (['k', '.', 's', 'l', 'o', 't', 's', '[', 'i', ']', '.', 'v', ' ', '=', ' ', '3', ';', ' '] ++ rest) (n + 14) =
    [.ident "k", .zeichen ".", .wort "slots", .zeichen "[", .ident "i", .zeichen "]", .zeichen ".", .ident "v", .zeichen "=", .num 3, .zeichen ";"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

theorem scan_close (rest : List Char) (n : Nat) :
    scan false (['}', ' '] ++ rest) (n + 2) =
    [.zeichen "}"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

theorem scan_call (rest : List Char) (n : Nat) :
    scan false (['g', '(', 'k', ',', ' ', 'i', ')', ';', ' '] ++ rest) (n + 9) =
    [.ident "g", .zeichen "(", .ident "k", .zeichen ",", .ident "i", .zeichen ")", .zeichen ";"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

theorem scan_end (n : Nat) :
    scan false ['}'] (n + 1) = .ok [.zeichen "}", .ende] := by cbv

theorem token_maps (tokens : List Token) (result : Except LexFehler (List Token)) :
    tokens.foldr (fun t answer => Except.map (t :: ·) answer) result =
      Except.map (tokens ++ ·) result := by
  induction tokens with
  | nil => cases result <;> rfl
  | cons t ts ih =>
    simp only [List.foldr, ih]
    cases result <;> rfl

/-- Canonical token snapshots shared by the six unchanged source texts. -/
def table_tokens : List Token :=
    [.wort "module", .ident "m", .zeichen "{", .wort "table", .ident "T", .wort "count", .num 2, .zeichen "{", .wort "slot", .zeichen "{", .ident "v", .zeichen ":", .wort "u32", .zeichen ",", .zeichen "}", .zeichen "}", .wort "lock", .ident "L", .wort "protects", .zeichen "{", .ident "T", .zeichen "}", .wort "rank", .num 0, .zeichen ";"]

def parameter_tokens : List Token :=
    [.zeichen "(", .ident "k", .zeichen ":", .wort "ptr", .zeichen "<", .wort "normal", .zeichen ",", .wort "rw", .zeichen ">", .ident "T", .zeichen ",", .ident "i", .zeichen ":", .wort "index", .wort "into", .ident "T", .zeichen ")", .wort "effects", .zeichen "{"]

def effect_tokens : List Token := [.wort "writes", .ident "k", .zeichen ".", .wort "slots", .zeichen ",", .wort "locks", .ident "L"]

def write_tokens (n : Nat) : List Token :=
    [.ident "k", .zeichen ".", .wort "slots", .zeichen "[", .ident "i", .zeichen "]", .zeichen ".", .ident "v", .zeichen "=", .num n, .zeichen ";"]

/-- A closed function-count certificate supplies the bound independently of the
    function subsequently classified. The witness is the existing canonical Fin. -/
def singleFn (unit : Uebersetze.UProg) (count : unit.fns.length = 1) : Fin unit.fns.length :=
  ⟨0, by rw [count]; decide⟩

theorem singleFn_all (unit : Uebersetze.UProg) (count : unit.fns.length = 1)
    (P : Fin unit.fns.length → Prop) (first : P (singleFn unit count)) : ∀ f, P f := by
  intro f
  have bound := f.isLt
  have zero : f.val = 0 := by omega
  have same : f = singleFn unit count := Fin.ext zero
  subst f
  exact first

private theorem invs_empty (unit : Uebersetze.UProg) (empty : unit.invs = []) :
    lowerInvs unit (List.finRange unit.invs.length) = .ok () := by
  cases enumeration : List.finRange unit.invs.length with
  | nil => rfl
  | cons i rest =>
    have count : unit.invs.length = 0 := congrArg List.length empty
    have bound := i.isLt
    omega

private theorem each_success (unit : Uebersetze.UProg)
    (success : ∀ f : Fin unit.fns.length, (lowerFnAt unit f).toOption.isSome = true) :
    ∀ fs, lowerEach unit fs = .ok ()
  | [] => rfl
  | f :: fs => by
    rw [lowerEach, except_ok_get (ε := String)
      (α := EnsTy unit f × RumpTy unit f × ReqTy unit f) (x := lowerFnAt unit f) (success f)]
    exact each_success unit success fs

private theorem each_error (unit : Uebersetze.UProg) (error : String)
    (outcomes : ∀ f : Fin unit.fns.length,
      lowerFnAt unit f = .error error ∨ (lowerFnAt unit f).toOption.isSome = true) :
    ∀ fs, (∃ f ∈ fs, lowerFnAt unit f = .error error) → lowerEach unit fs = .error error
  | [], bad => by rcases bad with ⟨f, member, _⟩; cases member
  | f :: fs, bad => by
    rcases outcomes f with failure | success
    · simp only [lowerEach, failure]
    · have head := except_ok_get (ε := String)
        (α := EnsTy unit f × RumpTy unit f × ReqTy unit f) (x := lowerFnAt unit f) success
      have tail : ∃ g ∈ fs, lowerFnAt unit g = .error error := by
        rcases bad with ⟨g, member, failure⟩
        rcases List.mem_cons.mp member with same | member
        · subst g
          rw [head] at failure
          cases failure
        · exact ⟨g, member, failure⟩
      rw [lowerEach, head]
      exact each_error unit error outcomes fs tail

private theorem collect_success : ∀ (n : Nat) (T : Fin n → Type)
    (get : (i : Fin n) → Except String (T i)),
    (∀ i, (get i).toOption.isSome = true) →
      (Measures.collect n T get).toOption.isSome = true
  | 0, _, _, _ => rfl
  | n + 1, T, get, success => by
    have head := except_ok_get (ε := String) (α := T 0) (x := get 0) (success 0)
    have tail := collect_success n (fun i => T i.succ) (fun i => get i.succ) (fun i => success i.succ)
    have tailValue := except_ok_get (ε := String) (α := (i : Fin n) → T i.succ)
      (x := Measures.collect n (fun i => T i.succ) (fun i => get i.succ)) tail
    rw [Measures.collect, head]
    dsimp only [bind, Except.bind]
    rw [tailValue]

private theorem absent_measures (unit : Uebersetze.UProg)
    (absent : ∀ f : Fin unit.fns.length, (fnAt unit f).decreases = none) :
    (Measures.lowerMeasures unit).toOption.isSome = true := by
  have entries := collect_success unit.fns.length (fun f => Measures.At unit f)
    (fun f => Measures.lowerAt unit f) (fun f => by
      simp only [Measures.lowerAt, absent f, Except.toOption, Option.isSome])
  have collected := except_ok_get (ε := String) (α := (f : Fin unit.fns.length) → Measures.At unit f)
    (x := Measures.collect unit.fns.length (Measures.At unit) (Measures.lowerAt unit)) entries
  unfold Measures.lowerMeasures
  rw [collected]

/-- Actual function successes, contracts and absent source measures close the
    existing assembler without normalizing its dependent program body. -/
theorem lowerStage_ok (unit : Uebersetze.UProg) (noInvs : unit.invs = [])
    (functions : ∀ f : Fin unit.fns.length,
      (lowerFnAt unit f).toOption.isSome = true ∧ (fnAt unit f).decreases = none)
    (contracts : contractGate unit = true) : lowerStage unit = "OK" := by
  have measures := absent_measures unit (fun f => (functions f).2)
  let exported : Measures.Export unit := (Measures.lowerMeasures unit).toOption.get measures
  have measured : Measures.lowerMeasures unit = .ok exported := except_ok_get measures
  have checked (P : Programm (declOf unit)) :
      (Measures.checkedProgram unit P).toOption.isSome = true := by
    have lengths : Measures.cycleLengths unit P exported.mass = true := by
      unfold Measures.cycleLengths
      apply List.all_eq_true.mpr
      intro f _
      apply List.all_eq_true.mpr
      intro g _
      have empty (i : (declOf unit).Fn) : exported.mass i = [] :=
        Measures.lowerMeasures_absent unit exported i (functions i).2
      rw [empty f, empty g]
      change (!zykS P (List.finRange unit.fns.length) f g || true) = true
      exact Bool.or_true _
    unfold Measures.checkedProgram
    rw [measured]
    change (if Measures.cycleLengths unit P exported.mass then true else false) = true
    rw [ite_eq_left lengths]
  have invariants := invs_empty unit noInvs
  have functions := each_success unit (fun f => (functions f).1) (List.finRange unit.fns.length)
  have lowered : (lowerAllg unit).toOption.isSome = true := by
    unfold lowerAllg
    split
    · rename_i error failed
      rw [invariants] at failed
      cases failed
    · split
      · rename_i error failed
        rw [functions] at failed
        cases failed
      · split
        · exact checked _
        · contradiction
  unfold lowerStage
  rw [except_ok_get (ε := String) (α := Programm (declOf unit) × List (declOf unit).Fn)
    (x := lowerAllg unit) lowered]

/-- Preserve the exact first refusal: every failed function has this diagnostic,
    and at least one actual member fails. The ordinary invariant gate still runs. -/
theorem lowerStage_error (unit : Uebersetze.UProg) (error : String) (noInvs : unit.invs = [])
    (outcomes : ∀ f : Fin unit.fns.length,
      lowerFnAt unit f = .error error ∨ (lowerFnAt unit f).toOption.isSome = true)
    (bad : ∃ f : Fin unit.fns.length, lowerFnAt unit f = .error error) :
    lowerStage unit = "lower: " ++ error := by
  have invariants := invs_empty unit noInvs
  have functions := each_error unit error outcomes (List.finRange unit.fns.length)
    (by rcases bad with ⟨f, failure⟩; exact ⟨f, List.mem_finRange f, failure⟩)
  have failed : lowerAllg unit = .error error := by
    unfold lowerAllg
    split
    · rename_i reason failure
      rw [invariants] at failure
      cases failure
    · split
      · rename_i reason failure
        rw [functions] at failure
        cases failure
        rfl
      · rename_i value success
        rw [functions] at success
        cases success
  unfold lowerStage
  rw [failed]

end Gabbro.Grammatik.Parser.UebersetzeProben2
