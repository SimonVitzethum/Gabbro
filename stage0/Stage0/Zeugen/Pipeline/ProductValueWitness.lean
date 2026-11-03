/- Product construction, projection and replacement through expression and block lowering. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Proben
@[expose] public section

namespace Gabbro.Stage0.Pipeline.ProductValueWitness
open Gabbro.Grammatik Gabbro.Stage0.Senke Runner.IR
open Gabbro.Stage0.Senke.AggregateProbe (D layout world hLay)

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

abbrev Pair : Ty := .prod 7 [.int 17 17, .bool]
abbrev entry : D.Fn := ⟨0, by decide⟩

def pair {Γ : Ctx} {Λ : List (Res D)} : Expr D Γ Λ Pair :=
  .prod 7 (.cons (.lit 17) (.cons .tru .nil))

def updated : Expr D [] [] Pair := .prodSet pair (.tail .head) .fls

/-- Read the original field, the changed field and the preserved sibling together. -/
def checks : Expr D [] [] .bool :=
  .and (.prodGet pair (.tail .head))
    (.and (.not (.prodGet updated (.tail .head)))
      (.eq (.prodGet updated .head) (.lit 17)))

theorem semantics_zeuge : eval world checks world .nil = true := by
  decide +kernel

/-- The update retains both words, rather than returning only its selected field. -/
theorem encoding_zeuge :
    encodeWords layout Pair (eval world pair world .nil) = [17, 1] ∧
    encodeWords layout Pair (eval world updated world .nil) = [17, 0] := by
  exact ⟨rfl, rfl⟩

/-- A multiword middle field is followed by an integer with a nonzero high limb. -/
def widePair : Expr D [] []
    (.prod 9 [.bool, .arr .bool 2, .int (2 ^ 64 + 7) (2 ^ 64 + 7)]) :=
  .prod 9 (.cons .tru
    (.cons (.arrCons .tru (.arrCons .fls .arrNil))
      (.cons (.lit (2 ^ 64 + 7)) .nil)))

def wideUpdated :=
  Expr.prodSet widePair (.tail .head) (.arrCons .fls (.arrCons .tru .arrNil))

/-- Replacement copies the complete field and keeps the following integer's high limb. -/
theorem wide_encoding_zeuge :
    encodeWords layout _ (eval world widePair world .nil) = [1, 1, 0, 7, 1] ∧
    encodeWords layout _ (eval world wideUpdated world .nil) = [1, 0, 1, 7, 1] := by
  decide +kernel

theorem wide_lowering_zeuge :
    (lowE layout widePair 4).isSome = true ∧
    (lowE layout wideUpdated 4).isSome = true ∧
    (lowE layout (.prodGet wideUpdated (.tail .head)) 4).isSome = true := by
  decide +kernel

def code : List II := ((lowE layout checks 4).getD ([], 0)).1
def top : Nat := ((lowE layout checks 4).getD ([], 0)).2

theorem lowering_zeuge : lowE layout checks 4 = some (code, top) := by
  decide +kernel

def memory : Runner.Mem where
  b a := ((code.flatMap encII)[a.toNat]?).getD 0
  rd _ := true
  wr _ := true

private theorem worldAt (m : Runner.Mem) : WeltAt m layout world := by
  refine ⟨(fun t => Fin.elim0 t), (fun g => Fin.elim0 g), ?_⟩
  intro x hl hh
  change 65536 ≤ x at hl
  change x < 65536 at hh
  omega

/-- Code, frame and environment premises are inhabited jointly. -/
theorem pre [Kern] :
    PreS layout memory 0 65536 64 4 code (Env.nil : Env D []) := by
  refine ⟨by decide, by decide, ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩,
    ?_, ?_, ?_, trivial, wstab_true _ _⟩
  · apply codeAt_bytes code 0 (by decide +kernel)
    intro i hi
    have size : (code.flatMap encII).length < 2 ^ 64 := by decide +kernel
    refine ⟨rfl, rfl, ?_⟩
    simp only [memory, Nat.zero_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega),
      List.getElem?_eq_getElem hi, Option.getD_some]
  · unfold CodeFar
    decide +kernel
  · intro _ x
    nomatch x

/-- This run is supplied by the generic compiler theorem, including every product arm. -/
theorem simulation_zeuge [Kern] :
    lowE layout checks 4 = some (code, top) ∧ code ≠ [] ∧ top ≤ 64 ∧
    PreS layout memory 0 65536 64 4 code (Env.nil : Env D []) ∧
    Ok memory 0 65536 64 4 code (Enc layout .bool true) := by
  refine ⟨lowering_zeuge, by decide +kernel, by decide +kernel, pre, ?_⟩
  have run := (lowE_ok (same := by intro _; rfl) world world
    (W := fun _ => True) (fun m _ => worldAt m) hLay checks 4 code top
    lowering_zeuge (by decide +kernel) memory 0 .nil pre).word trivial
  simpa only [semantics_zeuge] using run

/-- The product is bound once; updating its local uses the normal aggregate assignment.
    The reads before and after replacement occupy separate lexical binders. -/
def body : Block D (vertragVon D entry) false [] [] [] :=
  .bind pair
    (.bind (.prodGet (.var .here) (.tail .head))
      (.cons (.assignVar (.there .here)
        (.prodSet (.var (.there .here)) (.tail .head) .fls))
        (.bind (.prodGet (.var (.there .here)) (.tail .head))
          (.bind (.prodGet (.var (.there (.there .here))) .head) .nil))))

/-- The actual lowB path accepts construction, projection, assignment and projection. -/
theorem block_lowering_zeuge :
    (lowB 1 (fun _ => 0) layout (⟨[], none, 0, 0, 0⟩ : FrameLayout)
      ([], 0) [] (0, 0) body).isSome = true := by
  decide +kernel

def program : Programm D where
  invariante _ := .tru
  requires _ := .tru
  ensures _ := .tru
  rumpf f := by
    obtain ⟨f, hf⟩ := f
    have zero : f = 0 := by change f < 1 at hf; omega
    subst f
    exact .cons (.ite .tru body .nil)
      (.ret (.val (.widen (by decide) (by decide) (.lit 42))) (.refl []))

def image : Except String (List Runner.B) := do
  let result ← bild 1 program
    (layU AggregateProbe.u (fun _ => none)) [entry] Fin.val
    (fun _ => "main") entry .nil [] 1024 0
  pure result.bytes

/-- The ordinary block also reaches complete image emission. -/
theorem image_zeuge : image.isOk = true := by
  decide +kernel

end Gabbro.Stage0.Pipeline.ProductValueWitness
