/- Native source comparisons consume the two actual float operand executions. -/
module
public import Stage0.Senke.Gleit.Native.Execution
public import Stage0.Senke.Ausdruck.Aggregat.Werte.NativeFloat
@[expose] public section

variable {currentOld : Bool}
namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}

/-- Source comparison uses the native CPU order. No source-specific arithmetic
    lemma or well-formedness assumption is needed for intrinsic native values. -/
theorem floatExprE_ok {fp : Runner.W} {K d top : Nat} {Γ : Ctx} {Λ : List (Res D)}
    {ρ : Env D Γ} {W : Runner.Mem → Prop} (σ₀ σ : World D) {l1 h1 l2 h2 : Int × Int}
    (le : Bool) (a : Expr D Γ Λ (.fl l1 h1)) (b : Expr D Γ Λ (.fl l2 h2)) {c : List II}
    (iha : ∀ d c top, lowE (currentOld := currentOld) L a (reserved := reserved) d = some (c, top) → top ≤ K →
      ∀ m pc, Pre L m pc fp K d c ρ W reserved → Ok m pc fp K d c (Enc L (.fl l1 h1) (eval σ₀ a σ ρ)))
    (ihb : ∀ d c top, lowE (currentOld := currentOld) L b (reserved := reserved) d = some (c, top) → top ≤ K →
      ∀ m pc, Pre L m pc fp K d c ρ W reserved → Ok m pc fp K d c (Enc L (.fl l2 h2) (eval σ₀ b σ ρ)))
    (h : floatExprL le d (lowE (currentOld := currentOld) L a (reserved := reserved))
      (lowE (currentOld := currentOld) L b (reserved := reserved)) = some (c, top)) (hK : top ≤ K)
    {m : Runner.Mem} {pc : Runner.W} (hp : Pre L m pc fp K d c ρ W reserved) :
    Ok m pc fp K d c (Enc L .bool
      (eval σ₀ (if le then Expr.flle b a else Expr.fllt a b) σ ρ)) := by
  cases le
  · refine nativeFPWordL_ok (.lt .f64) (op_fp rfl) h hK
      (fun ca ta he ht => iha _ ca ta he ht)
      (fun cb tb he ht => ihb _ cb tb he ht) ?_ hp
    intro wa wb ha hb
    change wa = (eval σ₀ a σ ρ).x.toBits.toBitVec at ha
    change wb = (eval σ₀ b σ ρ).x.toBits.toBitVec at hb
    subst wa; subst wb
    refine ⟨Runner.IR.bool (gleitLt (eval σ₀ a σ ρ).x (eval σ₀ b σ ρ).x), ?_, ?_⟩
    · simp only [Runner.NativeFPEval, Runner.nativeFP, Runner.NativeFPValue.Matches,
        nativeFloat_read_word]
      rfl
    · change Enc L .bool (gleitLt (eval σ₀ a σ ρ).x (eval σ₀ b σ ρ).x)
        (Runner.IR.bool (gleitLt (eval σ₀ a σ ρ).x (eval σ₀ b σ ρ).x))
      cases gleitLt (eval σ₀ a σ ρ).x (eval σ₀ b σ ρ).x <;> rfl
  · refine nativeFPWordL_ok (.le .f64) (op_fp rfl) h hK
      (fun cb tb he ht => ihb _ cb tb he ht)
      (fun ca ta he ht => iha _ ca ta he ht) ?_ hp
    intro wb wa hb ha
    change wa = (eval σ₀ a σ ρ).x.toBits.toBitVec at ha
    change wb = (eval σ₀ b σ ρ).x.toBits.toBitVec at hb
    subst wa; subst wb
    refine ⟨Runner.IR.bool (gleitLe (eval σ₀ b σ ρ).x (eval σ₀ a σ ρ).x), ?_, ?_⟩
    · simp only [Runner.NativeFPEval, Runner.nativeFP, Runner.NativeFPValue.Matches,
        nativeFloat_read_word]
      rfl
    · change Enc L .bool (gleitLe (eval σ₀ b σ ρ).x (eval σ₀ a σ ρ).x)
        (Runner.IR.bool (gleitLe (eval σ₀ b σ ρ).x (eval σ₀ a σ ρ).x))
      cases gleitLe (eval σ₀ b σ ρ).x (eval σ₀ a σ ρ).x <;> rfl

end Gabbro.Stage0.Senke
