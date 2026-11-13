module
public import Stage0.Senke.Welt.Rahmen
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR

/-- Executable frame metadata carried beside the canonical typing context.
    Extending a scope adds one width; it never folds the live context again. -/
structure FrameCache (Γ : Ctx) where
  words : Nat
  correct : words = contextWords Γ

namespace FrameCache

def ofCtx (Γ : Ctx) : FrameCache Γ :=
  { words := contextWords Γ
    correct := rfl }

theorem eq_ofCtx {Γ : Ctx} (frame : FrameCache Γ) : frame = ofCtx Γ := by
  cases frame with
  | mk words correct => cases correct; rfl

def push {Γ : Ctx} (frame : FrameCache Γ) (τ : Ty) : FrameCache (τ :: Γ) :=
  { words := frame.words + valueWords τ
    correct := (by simp only [frame.correct, contextWords_cons]) }

def free {Γ : Ctx} (frame : FrameCache Γ) (reserved : Nat) : Nat :=
  FB + reserved + frame.words

theorem free_eq {Γ : Ctx} (frame : FrameCache Γ) (reserved : Nat) :
    frame.free reserved = frei Γ reserved := by
  unfold free frei
  rw [frame.correct]

/-- A variable already contains its de Bruijn path. Follow that path once while
    subtracting widths, instead of folding the entire context at its final node.
    A head variable therefore takes constant time even in a long live scope. -/
def offset (words : Nat) : {Γ : Ctx} → {τ : Ty} → Var Γ τ → Nat
  | σ :: _, _, .here => words - valueWords σ
  | σ :: _, _, .there x => offset (words - valueWords σ) x

theorem offset_eq {Γ : Ctx} {τ : Ty} (x : Var Γ τ) :
    offset (contextWords Γ) x = variableOffset x := by
  induction x with
  | here => simp only [offset, contextWords_cons, Nat.add_sub_cancel, variableOffset]
  | there x ih =>
    simp only [offset, contextWords_cons, Nat.add_sub_cancel, variableOffset, ih]

def slot {Γ : Ctx} {τ : Ty} (frame : FrameCache Γ) (x : Var Γ τ)
    (reserved : Nat) : Nat := FB + reserved + offset frame.words x

theorem slot_eq {Γ : Ctx} {τ : Ty} (frame : FrameCache Γ) (x : Var Γ τ)
    (reserved : Nat) : frame.slot x reserved = vslot x reserved := by
  simp only [slot, frame.correct, offset_eq, vslot]

end FrameCache

/-- The shared expression traversal varies only in how it reads frame metadata.
    Both implementations have the same domain, including every valid cache. -/
structure FrameLookup where
  slot : {Γ : Ctx} → {τ : Ty} → FrameCache Γ → Var Γ τ → Nat → Nat
  free : {Γ : Ctx} → FrameCache Γ → Nat → Nat
  push : {Γ : Ctx} → FrameCache Γ → (τ : Ty) → FrameCache (τ :: Γ)

/-- Ignore incoming cache state even at binders. After lookup specialization the
    canonical traversal does not need the cached word count at runtime. -/
@[inline] def specLookup : FrameLookup :=
  { slot := fun {Γ} {τ} _ x reserved => vslot x reserved
    free := fun {Γ} _ reserved => frei Γ reserved
    push := fun {Γ} _ τ => FrameCache.ofCtx (τ :: Γ) }

@[inline] def cachedLookup : FrameLookup :=
  { slot := fun {Γ} {τ} frame x reserved => frame.slot x reserved
    free := fun {Γ} frame reserved => frame.free reserved
    push := fun {Γ} frame τ => frame.push τ }

/-- Pointwise cache correctness identifies the entire lookup interface. No
    expression recursion or generated lowering equations are needed. -/
theorem cachedLookup_eq : cachedLookup = specLookup := by
  unfold cachedLookup specLookup
  congr 1
  · funext Γ τ frame x reserved
    exact FrameCache.slot_eq frame x reserved
  · funext Γ frame reserved
    exact FrameCache.free_eq frame reserved
  · funext Γ frame τ
    exact FrameCache.eq_ofCtx (frame.push τ)

end Gabbro.Stage0.Senke
