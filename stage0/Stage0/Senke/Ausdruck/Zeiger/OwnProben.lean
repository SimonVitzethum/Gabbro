/-
  Subject: Owned access image witness: `thruOwn` reads and `assignThruOwn` writes
           through an `own@M` capability lower exactly like the plain `thru`/`assignThru`
           forms on the underlying table; the owner mark emits no code.
-/
module
public import Stage0.Senke.Images.Bild
public import Stage0.Senke.Images.BildLese
public import Stage0.Senke.Welt.Anordnung
@[expose] public section


namespace Gabbro.Stage0.Senke.OwnProbe
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Runner.IR

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

/-- One two-cell table guarded by the declared linear owner mark `M`. -/
def u : UProg := {
  tabs := [{ name := "T", count := 2, cols := [("v", (0, 100))], owner := some "M" }]
  locks := []
  fns := [{ name := "main", params := [], kinds := [], res := some (0, 100), held := [], puts := ["T"], gives := [], body := [], ret := .val (.lit 0) }]
  marken := ["M"]
  eigner := ["M"]
}

abbrev D := declOf u
abbrev tab : D.Tab := ⟨0, by decide⟩
abbrev field : D.Feld tab := ⟨0, by decide⟩
abbrev entry : D.Fn := ⟨0, by decide⟩
abbrev mark : D.Marke := ⟨0, by decide⟩

abbrev ptrCap : Ty := .ptr ⟨0, ⟨true, true, some 0⟩, .table 0⟩
abbrev Γown : Ctx := [ptrCap, .index 2]
abbrev Λown : List (Res D) := [Res.marke mark 0]

theorem capTabOwn : D.capTab 0 0 = some tab := by decide
theorem ownerNrOwn : D.ownerNr 0 = some mark := by decide
theorem eignerOwn : mark ∈ D.eigner tab := by decide
theorem brauchtOwn : Sum.inr (mark, 0) ∈ D.braucht tab := by decide
theorem darfOwn : darf D tab Λown := by decide
theorem schreibtOwn : (vertragVon D entry).schreibt tab = true := by decide

def ptrVar : Expr D Γown Λown ptrCap := .var .here

def idx (k : Nat) (hk : k < 2) : Expr D Γown Λown (.index 2) :=
  .widen (by omega) (by omega) (.lit k)

/-- The owned read of cell 1. -/
def readOwn : Expr D Γown Λown (D.typ tab field) :=
  .thruOwn ptrVar tab capTabOwn field (idx 1 (by decide)) mark 0 ownerNrOwn eignerOwn brauchtOwn darfOwn

/-- The plain read of cell 1 through a fresh capability. -/
def plainRead : Expr D Γown Λown (D.typ tab field) :=
  .thru (.ptrOf tab 0 capTabOwn (true, true)) tab capTabOwn field (idx 1 (by decide)) darfOwn

/-- The owned write of 7 to cell 0. -/
def writeOwn : Stmt D (vertragVon D entry) false Γown Λown Λown :=
  .assignThruOwn ptrVar tab capTabOwn field (idx 0 (by decide))
    (.widen (by decide) (by decide) (.lit 7)) mark 0 ownerNrOwn eignerOwn brauchtOwn schreibtOwn darfOwn

def layout : Lay D where
  col _ _ := 8192
  ga g := nomatch g
  lo := 8192
  hi := 8208
  tor a := nomatch a
  byte _ := none

def world : World D where
  slots t k f := by
    obtain ⟨t, ht⟩ := t
    have hz : t = 0 := by change t < 1 at ht; omega
    subst t
    obtain ⟨f, hf⟩ := f
    have hz : f = 0 := by change f < 1 at hf; omega
    subst f
    exact ⟨if k = 0 then 11 else 22, by split <;> decide, by split <;> decide⟩
  globs g := Fin.elim0 g
  spur := []

def env : Env D Γown := .cons () (.cons ⟨1, by decide, by decide⟩ .nil)

/-- Owned and plain reads evaluate to the same cell. -/
theorem ownEval_zeuge : eval world readOwn world env = eval world plainRead world env := rfl

/-- Owned and plain reads emit the same fragment. -/
theorem ownLowerEq_zeuge : lowE layout readOwn 6 = lowE layout plainRead 6 := by
  simp only [readOwn, plainRead, lowE_thruOwn, lowE_thru]

def readCode : List II := ((lowE layout readOwn 6).getD ([], 0)).1
def readTop : Nat := ((lowE layout readOwn 6).getD ([], 0)).2

/-- The owned read reaches actual IR: nonempty code within the scratch bound. -/
theorem ownRead_image_zeuge :
    lowE layout readOwn 6 = some (readCode, readTop) ∧ readCode ≠ [] ∧ readTop ≤ 64 := by
  decide +kernel

def writeCode : List II :=
  ((lowS 1 (fun _ => 0) layout (⟨[], none, 0, 0, 0⟩ : FrameLayout) ([], 0) [] (0, 0) writeOwn).getD ([], 0)).1
def writeTop : Nat :=
  ((lowS 1 (fun _ => 0) layout (⟨[], none, 0, 0, 0⟩ : FrameLayout) ([], 0) [] (0, 0) writeOwn).getD ([], 0)).2

/-- The owned write reaches actual IR: nonempty code within the scratch bound. -/
theorem ownWrite_image_zeuge :
    lowS 1 (fun _ => 0) layout (⟨[], none, 0, 0, 0⟩ : FrameLayout) ([], 0) [] (0, 0) writeOwn =
      some (writeCode, writeTop) ∧
    writeCode ≠ [] ∧ writeTop ≤ 64 := by
  decide +kernel

/-- Owned read then owned write: both images exist and the owned read shares
    its evaluation and its fragment with the plain read. -/
theorem own_access_zeuge :
    (∃ c top, lowE layout readOwn 6 = some (c, top)) ∧
    (∃ c top, lowS 1 (fun _ => 0) layout (⟨[], none, 0, 0, 0⟩ : FrameLayout) ([], 0) [] (0, 0) writeOwn = some (c, top)) ∧
    eval world readOwn world env = eval world plainRead world env := by
  exact ⟨⟨readCode, readTop, ownRead_image_zeuge.1⟩,
    ⟨writeCode, writeTop, ownWrite_image_zeuge.1⟩, ownEval_zeuge⟩

end Gabbro.Stage0.Senke.OwnProbe
