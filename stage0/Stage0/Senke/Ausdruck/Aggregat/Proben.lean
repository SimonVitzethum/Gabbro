/- Subject: Inhabited aggregate fixtures, limits and a concrete IR simulation with all premises supplied. -/
import Stage0.Senke.Welt.Anordnung

namespace Gabbro.Stage0.Senke.AggregateProbe
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Runner.IR
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def u : UProg := {
  tabs := [], locks := []
  fns := [{ name := "main", params := [], kinds := [], res := some (0, 100), held := [], puts := [], gives := [], body := [], ret := .val (.lit 0) }]
}
abbrev D := declOf u

def layout : Lay D := layU u (fun _ => none) 65536

def world : World D where
  slots t := Fin.elim0 t
  globs g := Fin.elim0 g
  spur := []

def byte (b : Int) (hl : 0 ≤ b) (hh : b ≤ 255) : Expr D [] [] (.str 1) :=
  .strLit [⟨b, hl, hh⟩] (by simp)

def empty : Expr D [] [] (.str 0) := .strLit [] (by decide)
def zero := byte 0 (by decide) (by decide)
def high := byte 255 (by decide) (by decide)
def letter := byte 65 (by decide) (by decide)

def array : Expr D [] [] (.arr (.int (-100) 100) 1) :=
  .arrCons (.widen (by decide) (by decide) (.lit (-7))) .arrNil

def index : Expr D [] [] (.index 1) := .lit 0

def replaced : Expr D [] [] (.arr (.int (-100) 100) 1) :=
  .arrSet array index (.widen (by decide) (by decide) (.lit 49))

def checks : Expr D [] [] .bool :=
  [ .eq (.add (.arrGet array index) (.arrGet replaced index)) (.lit 42),
    .eq (.arrGet (.arrGet (.arrCons array .arrNil) index) index) (.lit (-7)),
    .eq (.strLen (.strCat empty letter)) (.lit 1),
    .strEq (.strCat letter empty) letter,
    .strEq (.strWeit 0 high) empty,
    .strEq (.strWeit 1 empty) (Expr.strLit (n := 1) [] (by decide)),
    .eq (.strGet high (.lit 0)) (.lit 255),
    .eq (.strGet high (.lit (-1))) (.lit 0),
    .eq (.strGet high (.lit 1)) (.lit 0),
    .eq (.strGet empty (.lit 0)) (.lit 0),
    .not (.strEq empty zero), .strLt empty zero, .not (.strLt high letter)
  ].foldr Expr.and .tru

theorem semantics_zeuge : wahr? (eval world checks world .nil) = true := by decide +kernel

def lowered := lowE layout checks 4

theorem lowered_zeuge : lowered.isSome = true := by decide +kernel

def code : List II := (lowered.getD ([], 0)).1
def top : Nat := (lowered.getD ([], 0)).2

theorem lowering_zeuge : lowE layout checks 4 = some (code, top) := by decide +kernel

def memory : Runner.Mem where
  b a := ((code.flatMap encII)[a.toNat]?).getD 0
  rd _ := true
  wr _ := true

theorem bytes : BytesAt memory 0 (code.flatMap encII) := by
  intro i hi
  refine ⟨rfl, rfl, ?_⟩
  have hsize : (code.flatMap encII).length < 2 ^ 64 := by decide +kernel
  simp only [memory, Nat.zero_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), List.getElem?_eq_getElem hi, Option.getD_some]

theorem pre [Kern] : PreS layout memory 0 65536 64 4 code (Env.nil : Env D []) := by
  refine ⟨by decide, by decide, ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩, ?_, ?_, ?_, trivial, wstab_true _ _⟩
  · exact codeAt_bytes code 0 (by decide +kernel) bytes
  · unfold CodeFar; decide +kernel
  · intro _ x; nomatch x

/-- The lowering equation, nonempty code, real frame and simulation hold together. -/
theorem simulation_zeuge [Kern] :
    lowE layout checks 4 = some (code, top) ∧ code ≠ [] ∧ top ≤ 64 ∧
    PreS layout memory 0 65536 64 4 code (Env.nil : Env D []) ∧
    Ok memory 0 65536 64 4 code (Enc layout .bool true) := by
  refine ⟨lowering_zeuge, by decide +kernel, by decide +kernel, pre, ?_⟩
  have hw : ∀ m, WeltAt m layout world := by
    intro m
    refine ⟨?_, ?_, ?_⟩
    · intro t; exact Fin.elim0 t
    · intro g; exact Fin.elim0 g
    · intro x hl hh
      change 65536 ≤ x at hl
      change x < 65536 at hh
      omega
  have h := lowE_ok world world (W := fun _ => True) (fun m _ => hw m)
    checks 4 code top lowering_zeuge (by decide +kernel) memory 0 .nil pre
  simpa only [show eval world checks world .nil = true from semantics_zeuge] using h

def program : Programm D where
  invariante _ := .tru
  requires _ := .tru
  ensures _ := .tru
  rumpf f := by
    obtain ⟨f, hf⟩ := f
    have hz : f = 0 := by change f < 1 at hf; omega
    subst f
    exact .ret (.val (.wenn checks (.widen (by decide) (by decide) (.lit 42))
      (.widen (by decide) (by decide) (.lit 0)))) (.refl [])

def image : Except String (List Runner.B) := do
  let b ← bild program (layU u (fun _ => none)) [⟨0, by decide⟩] Fin.val
    (fun _ => "main") ⟨0, by decide⟩ [] 1024
  pure b.bytes

theorem image_zeuge : image.isOk = true := by decide +kernel

/-- Unsupported aggregates are refused at reads as well as constructors, including nested types. -/
theorem read_refused_zeuge :
    lowE layout (Expr.var (D := D) (Λ := []) (Γ := [.arr .bool 2]) .here) 3 = none ∧
    lowE layout (Expr.var (D := D) (Λ := []) (Γ := [.str 2]) .here) 3 = none ∧
    lowE layout (Expr.var (D := D) (Λ := []) (Γ := [.arr (.str 2) 1]) .here) 3 = none ∧
    aggregateFits (.arr (.str 2) 0) = true := by decide +kernel

/-- Each unsupported operation fails at its own static representation guard. -/
theorem refused_zeuge :
    lowE layout (.arrCons (Expr.lit (D := D) (Γ := []) (Λ := []) 1) (.arrCons (Expr.lit (D := D) (Γ := []) (Λ := []) 1) .arrNil)) 3 = none ∧
    lowE layout (.arrGet (.arrCons (Expr.lit (D := D) (Γ := []) (Λ := []) 1) (.arrCons (Expr.lit (D := D) (Γ := []) (Λ := []) 1) .arrNil))
      (.widen (by decide) (by decide) (.lit 0))) 3 = none ∧
    lowE layout (.arrSet (.arrCons (Expr.lit (D := D) (Γ := []) (Λ := []) 1) (.arrCons (Expr.lit (D := D) (Γ := []) (Λ := []) 1) .arrNil))
      (.widen (by decide) (by decide) (.lit 0)) (.lit 1)) 3 = none ∧
    lowE layout (Expr.strLit (D := D) (Γ := []) (Λ := []) (n := 2) [] (by decide)) 3 = none ∧
    lowE layout (.strCat letter letter) 3 = none ∧
    lowE layout (.strWeit 2 letter) 3 = none ∧
    lowE layout (.strGet letter (.lit (2 ^ 63))) 3 = none := by decide +kernel

/-- The word representation distinguishes empty from a zero byte and preserves byte 255. -/
theorem representation_zeuge :
    Enc layout (.str 0) (⟨[], by decide⟩ : Wert D (.str 0)) 0 ∧
    Enc layout (.str 1) (⟨[⟨0, by decide, by decide⟩], by decide⟩ : Wert D (.str 1)) 256 ∧
    Enc layout (.str 1) (⟨[⟨255, by decide, by decide⟩], by decide⟩ : Wert D (.str 1)) 511 ∧
    Enc layout (.arr .bool 0) (fun i => i.elim0) 0 := by
  exact ⟨⟨by decide, rfl⟩, ⟨by decide, rfl⟩, ⟨by decide, rfl⟩, rfl⟩
end Gabbro.Stage0.Senke.AggregateProbe
