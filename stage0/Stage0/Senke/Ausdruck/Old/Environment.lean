/- Complete snapshots and preserved parameters form one typed frame environment.
   Expression kernels can therefore reuse their ordinary environment contracts. -/
module
public import Stage0.Senke.Ausdruck.Old.Spans
public import Stage0.Senke.Ausdruck.Quant.Frame
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable {D : Deklaration} {L : Lay D}

namespace EntrySnapshots

@[simp] theorem contextWords_append (left right : Ctx) :
    contextWords (left ++ right) = contextWords left + contextWords right := by
  induction left with
  | nil => simp only [List.nil_append, contextWords_nil, Nat.zero_add]
  | cons ty rest ih => simp only [List.cons_append, contextWords_cons, ih]; omega

/-- Append the older, lower-addressed variables after the lexical context. -/
def appendEnv {Γ Δ : Ctx} : Env D Γ → Env D Δ → Env D (Γ ++ Δ)
  | .nil, older => older
  | .cons value rest, older => .cons value (appendEnv rest older)

theorem appendEnv_at {Γ Δ : Ctx} (newer : Env D Γ) (older : Env D Δ)
    {m : Runner.Mem} {fp : Runner.W} {reserved : Nat} :
    EnvAt L m fp (appendEnv newer older) reserved ↔
      EnvAt L m fp newer (reserved + contextWords Δ) ∧ EnvAt L m fp older reserved := by
  induction newer with
  | nil =>
    constructor
    · intro value
      constructor
      · intro ty x; nomatch x
      · simpa only [appendEnv] using value
    · intro value; simpa only [appendEnv] using value.2
  | @cons ty Γ value rest ih =>
    have slotEq : frei (Γ ++ Δ) reserved = frei Γ (reserved + contextWords Δ) := by
      simp only [frei, contextWords_append]; omega
    constructor
    · intro env
      obtain ⟨left, right⟩ := ih.mp (envAt_tail env)
      refine ⟨envAt_cons left ?_, right⟩
      have head := env ty .here
      change ValueAt L m fp (frei (Γ ++ Δ) reserved) ty value at head
      rw [slotEq] at head
      exact head
    · rintro ⟨left, right⟩
      apply envAt_cons (ih.mpr ⟨envAt_tail left, right⟩)
      simpa only [appendEnv, vslot_here, Env.get, slotEq] using left ty .here

/-- A bounded lexical environment above an exact write footprint retains all limbs. -/
theorem envAt_above [Kern] {Γ : Ctx} {ρ : Env D Γ} {m m' : Runner.Mem} {fp : Runner.W}
    {lo last K reserved : Nat} (env : EnvAt L m fp ρ reserved)
    (changed : Agree fp lo last m m') (frame : FrameOK m fp K)
    (afterWrite : last ≤ FB + reserved) (fits : frei Γ reserved ≤ K) :
    EnvAt L m' fp ρ reserved := by
  intro ty x
  obtain ⟨valid, words⟩ := env ty x
  refine ⟨valid, ?_⟩
  intro i hi
  have width := encodeWords_length L ty (ρ.get x)
  have bound := variableOffset_bound x
  rw [agree_rd_above changed frame.room (by unfold vslot; omega)
    (by unfold vslot frei at *; omega)]
  exact words i hi

/-- Reverse context order matches increasing physical capture addresses. -/
def types : List (Zelle D) → Ctx
  | [] => []
  | cell :: rest => types rest ++ [cell.ty]

@[simp] theorem types_words (cells : List (Zelle D)) : contextWords (types cells) = words cells := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
    simp only [types, contextWords_append, contextWords_cons, contextWords_nil, ih, words]
    omega

/-- The typed values are ghost proof data; actual snapshots are emitted by capture. -/
def values (world : World D) : (cells : List (Zelle D)) → Env D (types cells)
  | [] => .nil
  | cell :: rest => appendEnv (values world rest) (.cons (cell.val world) .nil)

/-- All saved limbs are exactly an ordinary typed environment, at any reservation. -/
theorem values_at (world : World D) (cells : List (Zelle D))
    {m : Runner.Mem} {fp : Runner.W} {reserved : Nat} :
    EnvAt L m fp (values world cells) reserved ↔ At L world m fp cells (FB + reserved) := by
  induction cells generalizing reserved with
  | nil =>
    constructor
    · intro _; trivial
    · intro _ _ x; nomatch x
  | cons cell rest ih =>
    change EnvAt L m fp (appendEnv (values world rest) (.cons (cell.val world) .nil)) reserved ↔ _
    rw [appendEnv_at]
    simp only [contextWords_cons, contextWords_nil, Nat.add_zero, Nat.zero_add]
    constructor
    · rintro ⟨tail, head⟩
      refine ⟨?_, ?_⟩
      · simpa only [vslot_here, frei, contextWords_nil, Nat.add_zero, Env.get] using head cell.ty .here
      · simpa only [Nat.add_assoc] using ih.mp tail
    · rintro ⟨head, tail⟩
      refine ⟨ih.mpr (by simpa only [Nat.add_assoc] using tail), envAt_cons (fun _ x => nomatch x) ?_⟩
      simpa only [frei, contextWords_nil, Nat.add_zero, Nat.zero_add] using head

/-- Parameters and every complete snapshot share one generic environment relation. -/
theorem complete_at {Γ : Ctx} (params : Env D Γ) (world : World D) (cells : List (Zelle D))
    {m : Runner.Mem} {fp : Runner.W} :
    EnvAt L m fp (appendEnv params (values world cells)) ↔
      EnvAt L m fp params (words cells) ∧ At L world m fp cells FB := by
  rw [appendEnv_at, types_words, values_at]
  simp only [Nat.zero_add, Nat.add_zero]

end EntrySnapshots
end Gabbro.Stage0.Senke
