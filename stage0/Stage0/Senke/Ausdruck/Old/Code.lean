/- Entry snapshots for postconditions. Slot 3 belongs to the immutable frame header. -/
import Stage0.Senke.Ausdruck.Satz

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable {D : Deklaration}

/-- Only literal indices (including range widening) are fixed at entry. -/
def entryIndex {Γ : Ctx} {Λ : List (Res D)} :
    {τ : Ty} → Expr D Γ Λ τ → Option Int
  | _, .lit n => some n
  | _, .widen _ _ e => entryIndex e
  | _, _ => none

def Zelle.ty : Zelle D → Ty
  | .glob g => D.gtyp g
  | .elem t f _ => D.typ t f

def Zelle.val (σ : World D) : (c : Zelle D) → Wert D c.ty
  | .glob g => σ.globs g
  | .elem t f k => σ.slots t k f

/-- The cells needed by the supported postcondition fragment, in traversal order. -/
def oldCells {Γ : Ctx} {Λ : List (Res D)} : {τ : Ty} → Expr D Γ Λ τ → List (Zelle D)
  | _, .oldG g _ => [.glob g]
  | _, .oldS t f i _ => match entryIndex i with
    | some k => [.elem t f k.toNat]
    | none => []
  | _, .widen _ _ e => oldCells e
  | _, .add a b | _, .sub a b | _, .mul a b | _, .eq a b | _, .lt a b
  | _, .and a b | _, .or a b => oldCells a ++ oldCells b
  | _, _ => []

/-- All captured occurrences currently share the one reserved header word.
    The entry compiler refuses more than one occurrence before emitting any image. -/
def SnapAt (L : Lay D) (cs : List (Zelle D)) (σ : World D) (m : Runner.Mem) (fp : Runner.W) : Prop :=
  ∀ c ∈ cs, ∃ w, m.rd64 (slot fp (BitVec.ofNat 64 3)) = some w ∧ Enc L c.ty (c.val σ) w

instance (c : Zelle D) : Decidable c.da := by
  cases c <;> unfold Zelle.da <;> infer_instance

/-- Snapshot code writes only the reserved header word. -/
def snapC (L : Lay D) : List (Zelle D) → Option (List II)
  | [] => some []
  | [c] => if decide c.da && lit32 (c.adr L) then some [ci 1 3 (c.adr L) 0, ci 15 3 3 0] else none
  | _ => none

/-- Postcondition lowering uses the same arithmetic instructions as ordinary expressions.
    Ordinary expression lowering continues to refuse entry reads outside this context. -/
def lowEns (L : Lay D) {Γ : Ctx} {Λ : List (Res D)} :
    {τ : Ty} → Expr D Γ Λ τ → Nat → Option (List II × Nat)
  | _, .oldG _ _, d => some ([ci 2 d 3 0], d + 1)
  | _, .oldS _ _ i _, d => do
      let _ ← entryIndex i
      pure ([ci 2 d 3 0], d + 1)
  | _, .widen _ _ e, d => lowEns L e d
  | _, .add a b, d => do let ca ← lowEns L a d; let cb ← lowEns L b (d+1); pure (bin2 3 d ca cb)
  | _, .sub a b, d => do let ca ← lowEns L a d; let cb ← lowEns L b (d+1); pure (bin2 4 d ca cb)
  | _, .mul a b, d => do let ca ← lowEns L a d; let cb ← lowEns L b (d+1); pure (bin2 5 d ca cb)
  | _, @Expr.eq _ _ _ l1 h1 l2 h2 a b, d =>
      if inW l1 h1 && inW l2 h2 then do
        let ca ← lowEns L a d; let cb ← lowEns L b (d+1); pure (bin2 14 d ca cb)
      else none
  | _, @Expr.lt _ _ _ l1 h1 l2 h2 a b, d =>
      if inW l1 h1 && inW l2 h2 then do
        let ca ← lowEns L a d; let cb ← lowEns L b (d+1); pure (bin2 13 d ca cb)
      else none
  | _, .and a b, d => do let ca ← lowEns L a d; let cb ← lowEns L b (d+1); pure (bin2 8 d ca cb)
  | _, .or a b, d => do let ca ← lowEns L a d; let cb ← lowEns L b (d+1); pure (bin2 9 d ca cb)
  | _, e, d => lowE L e d

end Gabbro.Stage0.Senke
