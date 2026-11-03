/- Subject: Inhabited aggregate fixtures, limits and a concrete IR simulation with all premises supplied. -/
module
public import Stage0.Senke.Welt.Anordnung
@[expose] public section


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

/-- Both a zero payload and a nonzero high limb retain their independent tag. -/
def wideSome (n : Int) (lo : 0 ≤ n) (hi : n ≤ 2^100-1) : Expr D [] [] (.opt (2^100)) :=
  .some (.widen lo hi (.lit n))

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
    .not (.strEq empty zero), .strLt empty zero, .not (.strLt high letter),
    .istSome (wideSome 0 (by decide) (by decide)),
    .istSome (wideSome (2^80+5) (by decide) (by decide)),
    .not (.istSome (.none (2^100))),
    .istSome (.wenn .tru (wideSome (2^80+5) (by decide) (by decide)) (.none (2^100)))
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

theorem hLay : LayIn layout := ⟨(fun t => Fin.elim0 t), (fun g => Fin.elim0 g), by decide⟩

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
  have h := (lowE_ok (same := by intro _; rfl) world world (W := fun _ => True) (fun m _ => hw m) hLay
    checks 4 code top lowering_zeuge (by decide +kernel) memory 0 .nil pre).word trivial
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
  let b ← bild 1 program (layU u (fun _ => none)) [⟨0, by decide⟩] Fin.val
    (fun _ => "main") ⟨0, by decide⟩ .nil [] 1024 0
  pure b.bytes

theorem image_zeuge : image.isOk = true := by decide +kernel

/-- Aggregate variables are read at their complete span, nested types and long strings included. -/
theorem read_accepted_zeuge :
    (lowE layout (Expr.var (D := D) (Λ := []) (Γ := [.arr .bool 2]) .here) 3).isSome = true ∧
    (lowE layout (Expr.var (D := D) (Λ := []) (Γ := [.str 2]) .here) 3).isSome = true ∧
    (lowE layout (Expr.var (D := D) (Λ := []) (Γ := [.arr (.str 2) 1]) .here) 3).isSome = true ∧
    aggregateFits (.arr (.str 2) 0) = true := by decide +kernel

/-- Local presence tests use the complete option read, including its tag, and
    need no table-count or signed-word restriction on the payload interval. -/
theorem wide_option_read_zeuge :
    (lowE layout (Expr.istSome
      (Expr.var (D := D) (Λ := []) (Γ := [.opt (2^100)]) .here)) 4).isSome = true := by
  decide +kernel

/-- Constructors, indexing and literals of every length are accepted. -/
theorem accepted_zeuge :
    (lowE layout (.arrCons (Expr.lit (D := D) (Γ := []) (Λ := []) 1) (.arrCons (Expr.lit (D := D) (Γ := []) (Λ := []) 1) .arrNil)) 3).isSome = true ∧
    (lowE layout (.arrGet (.arrCons (Expr.lit (D := D) (Γ := []) (Λ := []) 1) (.arrCons (Expr.lit (D := D) (Γ := []) (Λ := []) 1) .arrNil))
      (.widen (by decide) (by decide) (.lit 0))) 3).isSome = true ∧
    (lowE layout (.arrSet (.arrCons (Expr.lit (D := D) (Γ := []) (Λ := []) 1) (.arrCons (Expr.lit (D := D) (Γ := []) (Λ := []) 1) .arrNil))
      (.widen (by decide) (by decide) (.lit 0)) (.lit 1)) 3).isSome = true ∧
    (lowE layout (Expr.strLit (D := D) (Γ := []) (Λ := []) (n := 2) [] (by decide)) 3).isSome = true := by decide +kernel

/-- Each still unsupported operation fails at its own static representation guard. -/
theorem refused_zeuge :
    lowE layout (.strCat (Expr.strLit (n := 2^31) [] (by decide)) letter) 3 = none ∧
    lowE layout (.strGet letter (.lit (2 ^ 63))) 3 = none := by decide +kernel

/-- The word representation distinguishes empty from a zero byte and preserves byte 255. -/
theorem representation_zeuge :
    Enc layout (.str 0) (⟨[], by decide⟩ : Wert D (.str 0)) 0 ∧
    Enc layout (.str 1) (⟨[⟨0, by decide, by decide⟩], by decide⟩ : Wert D (.str 1)) 256 ∧
    Enc layout (.str 1) (⟨[⟨255, by decide, by decide⟩], by decide⟩ : Wert D (.str 1)) 511 ∧
    Enc layout (.arr .bool 0) (fun i => i.elim0) 0 := by
  exact ⟨⟨by decide, rfl⟩, ⟨by decide, rfl⟩, ⟨by decide, rfl⟩, rfl⟩
end Gabbro.Stage0.Senke.AggregateProbe

namespace Gabbro.Stage0.Senke.AggregateProbe.Reserved
open Gabbro.Grammatik Runner.IR Runner.Mem

def expr : Expr D [.bool] [] .bool := .and (.var .here) .tru
def env : Env D [.bool] := .cons false .nil
def code : List II := ((lowE layout (reserved := 3) expr 10).getD ([], 0)).1
def memory : Runner.Mem where
  b a := ((code.flatMap encII)[a.toNat]?).getD 0
  rd _ := true
  wr _ := true

theorem simulation_zeuge [Kern] :
    lowE layout (reserved := 3) expr 10 = some (code, 12) ∧
    Pre layout memory 0 65536 64 10 code env (fun _ => True) 3 ∧
    Ok memory 0 65536 64 10 code (Enc layout .bool false) := by
  have hl : lowE layout (reserved := 3) expr 10 = some (code, 12) := by decide +kernel
  have hp : Pre layout memory 0 65536 64 10 code env (fun _ => True) 3 := by
    refine ⟨by decide, by decide, ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩, ?_, ?_, ?_, trivial, wstab_true _ _⟩
    · apply codeAt_bytes code 0 (by decide +kernel)
      intro i hi
      have hs : (code.flatMap encII).length < 2 ^ 64 := by decide +kernel
      refine ⟨rfl, rfl, ?_⟩
      simp only [memory, Nat.zero_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), List.getElem?_eq_getElem hi, Option.getD_some]
    · unfold CodeFar; decide +kernel
    · intro τ x
      cases x with
      | here => exact ValueAt.of_enc (w := 0) (by decide) (by decide +kernel) rfl
      | there x => nomatch x
  refine ⟨hl, hp, ?_⟩
  have hw : ∀ m, WeltAt m layout world := by
    intro m
    refine ⟨(fun t => Fin.elim0 t), (fun g => Fin.elim0 g), ?_⟩
    intro x hl hh
    change 65536 ≤ x at hl
    change x < 65536 at hh
    omega
  exact (lowE_ok (same := by intro _; rfl) world world (W := fun _ => True) (fun m _ => hw m) hLay
    expr 10 code 12 hl (by decide) memory 0 env hp).word trivial
end Gabbro.Stage0.Senke.AggregateProbe.Reserved

namespace Gabbro.Stage0.Senke.AggregateProbe.Case
open Gabbro.Grammatik Runner.IR Runner.Mem

/-- Both the payload and its lower bound require the shared word materializer. -/
def expr : Expr D [] [] (.sum [none, some (2 ^ 32, 2 ^ 32 + 100)]) :=
  .case _ ⟨1, by decide⟩ (.num (.widen (by decide) (by decide) (.lit (2 ^ 32 + 42))))
def code : List II := ((lowE layout expr 4).getD ([], 0)).1
def top : Nat := ((lowE layout expr 4).getD ([], 0)).2

def memory : Runner.Mem where
  b a := ((code.flatMap encII)[a.toNat]?).getD 0
  rd _ := true
  wr _ := true

/-- All premises of the actual generic lowering theorem hold together; its result
    has tag 1 and offset 42, with the two scratch words included in the frame. -/
theorem simulation_zeuge [Kern] :
    lowE layout expr 4 = some (code, top) ∧ top = 7 ∧ code ≠ [] ∧
    PreS layout memory 0 65536 64 4 code (Env.nil : Env D []) ∧
    Enc layout (.sum [none, some (2 ^ 32, 2 ^ 32 + 100)])
      (eval world expr world .nil) 10753 ∧
    Ok memory 0 65536 64 4 code (· = 10753) := by
  have hl : lowE layout expr 4 = some (code, top) := by decide +kernel
  have hp : PreS layout memory 0 65536 64 4 code (Env.nil : Env D []) := by
    refine ⟨by decide, by decide, ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩,
      ?_, ?_, ?_, trivial, wstab_true _ _⟩
    · apply codeAt_bytes code 0 (by decide +kernel)
      intro i hi
      have hs : (code.flatMap encII).length < 2 ^ 64 := by decide +kernel
      refine ⟨rfl, rfl, ?_⟩
      simp only [memory, Nat.zero_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), List.getElem?_eq_getElem hi, Option.getD_some]
    · unfold CodeFar; decide +kernel
    · intro _ x; nomatch x
  have hw : ∀ m, WeltAt m layout world := by
    intro m
    refine ⟨(fun t => Fin.elim0 t), (fun g => Fin.elim0 g), ?_⟩
    · intro x hl hh
      change 65536 ≤ x at hl
      change x < 65536 at hh
      omega
  have he : Enc layout (.sum [none, some (2 ^ 32, 2 ^ 32 + 100)])
      (eval world expr world .nil) 10753 := by constructor <;> decide +kernel
  refine ⟨hl, by decide +kernel, by decide +kernel, hp, he, ?_⟩
  exact (lowE_ok (same := by intro _; rfl) world world (W := fun _ => True) (fun m _ => hw m) hLay
    expr 4 code top hl (by decide +kernel) memory 0 .nil hp).word (wordCompatB_sound _ (by decide +kernel)) |>.mono (fun _ hn => hn.2.trans he.2.symm)

end Gabbro.Stage0.Senke.AggregateProbe.Case

namespace Gabbro.Stage0.Senke.AggregateProbe.Narrow
open Gabbro.Grammatik Runner.IR

/-- Strings of capacity three: the surface language never narrows, so the narrowing and wide-index lowerings are
    exercised on the model directly. -/
def wide : Expr D [] [] (.str 3) :=
  .strLit [⟨97, by decide, by decide⟩, ⟨98, by decide, by decide⟩, ⟨99, by decide, by decide⟩] (by simp)

def ab : Expr D [] [] (.str 2) :=
  .strLit [⟨97, by decide, by decide⟩, ⟨98, by decide, by decide⟩] (by simp)

/-- Narrowing keeps the first bytes and the clamped length; indices outside the string read zero. -/
theorem narrow_semantics_zeuge :
    wahr? (eval world (.strEq (.strWeit 2 wide) ab) world .nil) = true ∧
    wahr? (eval world (.strEq (.strWeit 1 wide) (byte 97 (by decide) (by decide))) world .nil) = true ∧
    wahr? (eval world (.strEq (.strWeit 0 wide) empty) world .nil) = true ∧
    wahr? (eval world (.eq (.strGet wide (.lit (-1))) (.lit 0)) world .nil) = true ∧
    wahr? (eval world (.eq (.strGet wide (.lit 7)) (.lit 0)) world .nil) = true ∧
    wahr? (eval world (.eq (.strGet wide (.lit 2)) (.lit 99)) world .nil) = true := by decide +kernel

theorem narrow_lowered_zeuge :
    (lowE layout (.strWeit 2 wide) 4).isSome = true ∧ (lowE layout (.strWeit 1 wide) 4).isSome = true ∧
    (lowE layout (.strWeit 0 wide) 4).isSome = true ∧
    (lowE layout (.strGet wide (.lit (-1))) 4).isSome = true ∧
    (lowE layout (.strGet wide (.lit 7)) 4).isSome = true ∧
    (lowE layout (.strWeit 2 letter) 4).isSome = true ∧ (lowE layout (.strWeit 3 empty) 4).isSome = true ∧
    (lowE layout (.strEq letter wide) 4).isSome = true ∧ (lowE layout (.strEq wide letter) 4).isSome = true ∧
    (lowE layout (.strEq empty wide) 4).isSome = true := by decide +kernel

end Gabbro.Stage0.Senke.AggregateProbe.Narrow

namespace Gabbro.Stage0.Senke.AggregateProbe.Product
open Gabbro.Grammatik Runner.IR

/-- Distinct heterogeneous fields exercise both the word order and the typed offset. -/
def pair : Expr D [] [] (.prod 7 [.int 17 17, .bool]) :=
  .prod 7 (.cons (.lit 17) (.cons .tru .nil))

theorem prod_ok_zeuge :
    lowE layout pair 4 = some ([ci 1 4 17 0, ci 1 5 1 0], 6) ∧
    encodeWords layout (.prod 7 [.int 17 17, .bool])
      (eval world pair world .nil) = [17, 1] := ⟨rfl, rfl⟩

theorem prodGet_ok_zeuge :
    lowE layout (.prodGet pair (.tail .head)) 4 =
      some ([ci 1 4 17 0, ci 1 5 1 0, ci 2 4 5 0], 6) ∧
    eval world (.prodGet pair (.tail .head)) world .nil = true := ⟨rfl, rfl⟩

theorem prodSet_ok_zeuge :
    lowE layout (.prodSet pair (.tail .head) .fls) 4 =
      some ([ci 1 4 17 0, ci 1 5 1 0, ci 1 6 0 0, ci 2 5 6 0], 7) ∧
    encodeWords layout (.prod 7 [.int 17 17, .bool])
      (eval world (.prodSet pair (.tail .head) .fls) world .nil) = [17, 0] := ⟨rfl, rfl⟩

/-- The constructor owns the empty marker even though its argument list emits no code. -/
theorem prod_empty_zeuge :
    lowE layout (Γ := []) (Λ := []) (.prod 7 .nil) 4 = some ([ci 1 4 0 0], 5) ∧
    encodeWords layout (.prod 7 []) () = [0] := ⟨rfl, rfl⟩

end Gabbro.Stage0.Senke.AggregateProbe.Product
