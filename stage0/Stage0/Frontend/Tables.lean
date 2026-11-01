module
public import Grammatik.Parser.Elab.UebersetzePipeline
public import Grammatik.Parser.Elab.UebersetzeAllg
public import Mathlib.Basic.IsEmpty.Defs
@[expose] public section


namespace Gabbro.Stage0.Frontend
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg

/-- Existing table metadata with an empty canonical field domain. Counts remain exact integers;
    no storage, field, provider or implicit occupancy mark is introduced. -/
def emptyTable (name : String) (count : Int) (shared : Bool)
    (edges : List (String × String)) : UTab :=
  { name, count, cols := [], shared, kanten := edges }

/-- Provenance of the sole newly elaborated case. Invariants remain in the original item for
    canonical uInvs and the checker; this adapter only exports the table declaration data. -/
def EmptyTableMeaning (values : List (String × Int)) (item : SItemTief) (table : UTab) : Prop :=
  ∃ name count shared parts invs amount,
    item = .tableT name none (some count) none none shared parts ∧
    parts.filter (fun p => match p with | .tTree _ => false | _ => true) = .tSlot [] :: invs ∧
    invs.all (fun p => match p with | .tInv _ => true | _ => false) = true ∧
    uAnzahl values count = .ok amount ∧ 0 ≤ amount ∧
    table = emptyTable name amount shared
      (parts.flatMap (fun p => match p with | .tTree edges => edges | _ => []))

/-- Export empty fixed-count slots through the existing table model; every other declaration
    and every nonempty table uses the frozen canonical elaborator. -/
def tableWithEmpty (values : List (String × Int)) (typeEnv : List (String × (Int × Int)))
    (names : List String) (item : SItemTief) : Except String UTab :=
  match item with
  | .tableT name none (some count) none none shared parts =>
    match parts.filter (fun p => match p with | .tTree _ => false | _ => true) with
    | .tSlot [] :: invs =>
      if !invs.all (fun p => match p with | .tInv _ => true | _ => false) then
        .error "table without G form"
      else match uAnzahl values count with
      | .error e => .error e
      | .ok amount =>
        if 0 ≤ amount then .ok (emptyTable name amount shared
          (parts.flatMap (fun p => match p with | .tTree edges => edges | _ => [])))
        else .error "empty table with a negative count"
    | _ => uTabelle values typeEnv names item
  | _ => uTabelle values typeEnv names item

/-- All successful table exports are either exactly canonical or preserve the complete empty
    source declaration above. In particular, no failed declaration is erased. -/
theorem tableWithEmpty_sound (values : List (String × Int)) (typeEnv : List (String × (Int × Int)))
    (names : List String) (item : SItemTief) (table : UTab)
    (h : tableWithEmpty values typeEnv names item = .ok table) :
    uTabelle values typeEnv names item = .ok table ∨ EmptyTableMeaning values item table := by
  unfold tableWithEmpty at h
  split at h
  · rename_i name count shared parts
    split at h
    · rename_i invs hf
      split at h
      · contradiction
      · rename_i hi
        have hi' : invs.all (fun p => match p with | .tInv _ => true | _ => false) = true := by
          have h' := hi
          simp only [Bool.not_eq_true, Bool.not_eq_eq_eq_not, Bool.not_false] at h'
          exact Bool.of_not_eq_false h'
        split at h
        · contradiction
        · rename_i amount hc
          split at h
          · rename_i hn
            have he := Except.ok.inj h
            exact Or.inr ⟨name, count, shared, parts, invs, amount, rfl, hf, hi', hc, hn, he.symm⟩
          · contradiction
    · exact Or.inl h
  · exact Or.inl h

/-- The existing canonical declaration has the original count and no possible field/cell. -/
theorem emptyTable_model (u : UProg) (t : Fin u.tabs.length)
    (name : String) (amount : Int) (shared : Bool) (edges : List (String × String))
    (h : tabAt u t = emptyTable name amount shared edges) :
    (declOf u).count t = amount ∧ fieldCount u t = 0 ∧
      IsEmpty ((declOf u).Feld t) ∧ (declOf u).offen t = false := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (tabAt u t).count = amount
    rw [h]; rfl
  · change (tabAt u t).cols.length = 0
    rw [h]; rfl
  · refine ⟨fun f => ?_⟩
    have hf := f.isLt
    change f.val < (tabAt u t).cols.length at hf
    rw [h] at hf
    simp [emptyTable] at hf
  · change (tabAt u t).von.isSome = false
    rw [h]; rfl

/-- An actual empty table retains a large source count without inventing a field. -/
theorem tableWithEmpty_sound_zeuge :
    EmptyTableMeaning []
      (.tableT "Empty" none (some (.lit (2 ^ 32))) none none false [.tSlot []])
      (emptyTable "Empty" (2 ^ 32) false []) := by
  have h := tableWithEmpty_sound [] [] ["Empty"]
    (.tableT "Empty" none (some (.lit (2 ^ 32))) none none false [.tSlot []])
    (emptyTable "Empty" (2 ^ 32) false []) (by rfl)
  rcases h with h | h
  · change Except.error "table without fields" = Except.ok _ at h
    contradiction
  · exact h

end Gabbro.Stage0.Frontend
