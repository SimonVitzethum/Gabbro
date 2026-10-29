/- Subject: Joint witnesses on a real two-cell provider region, beyond the source count zero. -/
import Stage0.Senke.BildLese
import Grammatik.Bausteine.Arena.Unbounded.GRegion

namespace Gabbro.Stage0.Senke.ReferenceProbe
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
variable [Kern]

abbrev D := GRegion.rD
abbrev Γ : Ctx := [.ref 0, .ref 0]

def layout : Lay D where
  regionCells _ := 2
  col _ _ := 8192
  ga g := nomatch g
  lo := 8192
  hi := 8208
  tor _ := some ⟨39, regsIn 0, []⟩
  byte _ := none

def world : World D where
  slots _ k _ := ⟨if k = 0 then 11 else 22, by split <;> decide, by split <;> decide⟩
  globs g := nomatch g
  spur := []

def env : Env D Γ := .cons (Val.vonZelle 0) (.cons (Val.vonZelle 1) .nil)
def first : Expr D Γ [] (.ref 0) := .var .here
def second : Expr D Γ [] (.ref 0) := .var (.there .here)
def read (r : Expr D Γ [] (.ref 0)) : Expr D Γ [] (.int 0 255) :=
  .slotRef r () rfl rfl () (fun _ h => nomatch h)
def checks : Expr D Γ [] .bool :=
  .and (.refEq first first) (.and (.not (.refEq first second))
    (.and (.eq (read first) (.lit 11)) (.eq (read second) (.lit 22))))

def assignment : Stmt D (vertragVon D ()) false Γ [] [] :=
  .assignSlotRef second () rfl rfl () (.widen (by decide) (by decide) (.lit 73)) rfl
    (fun _ h => nomatch h)

def readCode : List II := ((lowE layout checks 5).getD ([], 0)).1
def readTop : Nat := ((lowE layout checks 5).getD ([], 0)).2
def writeCode : List II := ((lowS (fun _ => 0) layout 3 ([], 0) [] (0, 0) assignment).getD ([], 0)).1
def writeTop : Nat := ((lowS (fun _ => 0) layout 3 ([], 0) [] (0, 0) assignment).getD ([], 0)).2

/-- A real code segment, a frame containing provider references 1 and 0, and two region cells. -/
def memory (code : List II) : Runner.Mem where
  b a := if a.toNat < (code.flatMap encII).length then ((code.flatMap encII)[a.toNat]?).getD 0
    else if a.toNat = 4120 then 1 else if a.toNat = 8192 then 11 else if a.toNat = 8200 then 22 else 0
  rd _ := true
  wr _ := true

theorem layout_in : LayIn layout := by
  refine ⟨fun t f k hk => ?_, (fun g => nomatch g), by decide⟩
  change (k : Int) < 0 + 2 at hk
  change 8192 ≤ 8192 + 8 * k ∧ 8192 + 8 * k + 8 ≤ 8208
  omega

theorem layout_dis : LayDis layout := by
  constructor
  · intro c c' hc hc' he
    cases c with
    | glob g => nomatch g
    | elem t f k =>
      cases c' with
      | glob g => nomatch g
      | elem t' f' k' =>
        cases t; cases t'; cases f; cases f'
        change 8192 + 8 * k = 8192 + 8 * k' at he
        have : k = k' := by omega
        subst k'
        rfl
  · intro c hc
    cases c with
    | glob g => nomatch g
    | elem t f k => change (8192 + 8 * k) % 8 = 8192 % 8; omega

theorem region_zeuge : D.count () = 0 ∧ layout.count () = 2 ∧ LayIn layout ∧ LayDis layout :=
  ⟨rfl, rfl, layout_in, layout_dis⟩

theorem lowering_zeuge : lowE layout checks 5 = some (readCode, readTop) ∧
    lowS (fun _ => 0) layout 3 ([], 0) [] (0, 0) assignment = some (writeCode, writeTop) ∧
    readCode ≠ [] ∧ writeCode ≠ [] ∧ readTop ≤ 64 ∧ writeTop ≤ 64 := by decide +kernel

theorem semantics_zeuge : eval world checks world env = true ∧
    ∀ O passes R, ∃ σ', execStmt O passes R assignment world env = .ok σ' env ∧
      (σ'.slots () 1 ()).n = 73 ∧ (σ'.slots () 0 ()).n = 11 := by
  refine ⟨by rfl, fun O passes R => ?_⟩
  exact ⟨_, rfl, rfl, rfl⟩

theorem bytes (code : List II) (hsize : (code.flatMap encII).length < 2 ^ 64) :
    BytesAt (memory code) 0 (code.flatMap encII) := by
  intro i hi
  refine ⟨rfl, rfl, ?_⟩
  simp only [memory, Nat.zero_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), hi, ↓reduceIte,
    List.getElem?_eq_getElem hi, Option.getD_some]

theorem encoded_zeuge : Enc layout (.ref 0) (Val.vonZelle 0) 0 ∧
    Enc layout (.ref 0) (Val.vonZelle 1) 1 ∧
    ¬ Enc layout (.ref 0) (Val.vonZelle 2) 2 ∧
    ¬ Enc layout (.ref 0) (Val.vonZelle (2 ^ 64)) 0 := by
  refine ⟨⟨rfl, by decide, (), rfl, rfl, by decide⟩,
    ⟨rfl, by decide, (), rfl, rfl, by decide⟩, ?_, ?_⟩
  · intro h
    have := enc_ref_cell h (t := ()) rfl
    change (2 : Int) < 2 at this
    omega
  · intro h
    have := h.2.1
    exact (Nat.lt_irrefl (2 ^ 64)) this

/-- Static images have no supplied region; raw provider words are not accepted as regions. -/
theorem refused_zeuge : chkC (some (.ref 0)) 5 = none ∧
    lowEnd (fun _ => 0) layout 3 ([], 0) [] (0, 0) GRegion.rumpf = none := by decide +kernel

end Gabbro.Stage0.Senke.ReferenceProbe
