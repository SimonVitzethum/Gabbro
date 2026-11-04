/- Native value and complete-word transports for the actual FP emitter. -/
module
public import Stage0.Senke.Gleit.Native.Execution
public import Stage0.Senke.Ausdruck.Gleit.Komposition
public import Stage0.Senke.Ausdruck.Aggregat.Werte.NativeFloat
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}

/-- This is an execution witness in the native relation. It does not assert that
    every CPU NaN answer has the representative's bits. -/
theorem nativeArithmetic_eval (op : GleitOp) (a b : GFloat) :
    Runner.NativeFPEval (nativeArithmeticOp op) a.toBits.toBitVec b.toBits.toBitVec
      (gleitRechne op a b).toBits.toBitVec := by
  cases op <;>
    simp only [nativeArithmeticOp, Runner.NativeFPEval, Runner.nativeFP,
      Runner.NativeFPValue.Matches, nativeFloat_read_word, gleitRechne]
  all_goals rfl

/-- Native results are observed as decoded values, including NaNs. Their raw
    representation becomes the frame encoding only after source finiteness. -/
abbrev NativeFloatCode (ρ : Env D Γ) (W : Runner.Mem → Prop)
    (a : Nat → Option (List II × Nat)) (x : GFloat) (reserved : Nat := 0) : Prop :=
  ∀ {fp K d c top}, a d = some (c, top) → top ≤ K → ∀ m pc,
    Pre L m pc fp K d c ρ W reserved → Ok m pc fp K d c (fun w => Runner.readFloat w = x)

/-- The operands use the canonical source ABI; the native result remains a
    decoded value until an accepted binder establishes its finite encoding. -/
theorem floatWordsL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    (op : GleitOp) (x y : GFloat) {a b : Nat → Option (List II × Nat)}
    (ha : WordCode (L := L) (reserved := reserved) ρ W a x.toBits.toBitVec)
    (hb : WordCode (L := L) (reserved := reserved) ρ W b y.toBits.toBitVec) :
    NativeFloatCode (L := L) (reserved := reserved) ρ W
      (fun d => floatWordsL op d a b) (gleitRechne op x y) := by
  intro fp K d c top h hK m pc hp
  refine nativeFPWordL_ok (nativeArithmeticOp op) (by cases op <;> rfl) h hK
    (fun _ _ he ht => ha he ht) (fun _ _ he ht => hb he ht) ?_ hp
  intro wa wb hx hy
  subst wa; subst wb
  exact ⟨_, nativeArithmetic_eval op x y, nativeFloat_read_word _⟩

end Gabbro.Stage0.Senke
