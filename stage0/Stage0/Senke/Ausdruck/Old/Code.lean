/- Complete entry snapshots below the immutable postcondition parameter environment. -/
module
public import Stage0.Senke.Ausdruck.Satz
public import Stage0.Senke.Ausdruck.Old.Environment
public import Stage0.Senke.Ausdruck.Aggregat.Frame.Layout
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable {D : Deklaration}

/-- Closed scalar arithmetic indices are independent of both entry and exit environments. -/
def entryIndex {Γ : Ctx} {Λ : List (Res D)} :
    {τ : Ty} → Expr D Γ Λ τ → Option Int
  | _, .lit n => some n
  | _, .widen _ _ e => entryIndex e
  | _, .add a b => return (← entryIndex a) + (← entryIndex b)
  | _, .sub a b => return (← entryIndex a) - (← entryIndex b)
  | _, .mul a b => return (← entryIndex a) * (← entryIndex b)
  | _, .neg a => return -(← entryIndex a)
  | _, _ => none

/-- The cells needed by the supported postcondition fragment, in traversal order. -/
def oldCells {Γ : Ctx} {Λ : List (Res D)} : {τ : Ty} → Expr D Γ Λ τ → List (Zelle D)
  | _, .oldG g _ => [.glob g]
  | _, .oldS t f i _ => match entryIndex i with
    | some k => [.elem t f k.toNat]
    | none => []
  | _, .widen _ _ e | _, .not e | _, .neg e => oldCells e
  | _, .add a b | _, .sub a b | _, .mul a b | _, .eq a b | _, .lt a b | _, .le a b
  | _, .and a b | _, .or a b => oldCells a ++ oldCells b
  | _, .intBuiltin1 _ a => oldCells a
  | _, .intBuiltin2 _ a b => oldCells a ++ oldCells b
  | _, _ => []

/-- Postcondition lowering uses the same arithmetic instructions as ordinary expressions.
    Ordinary expression lowering continues to refuse entry reads outside this context. -/
def lowEnsAt (L : Lay D) (layout : FrameLayout) (start : Nat) {Γ : Ctx} {Λ : List (Res D)} :
    {τ : Ty} → Expr D Γ Λ τ → Nat → Option (List II × Nat)
  | _, .oldG g _, d =>
      some (copyWords (valueWords (D.gtyp g)) d start, d + valueWords (D.gtyp g))
  | _, .oldS t f i _, d => do
      let _ ← entryIndex i
      pure (copyWords (valueWords (D.typ t f)) d start, d + valueWords (D.typ t f))
  | _, .widen (lo := lo) (hi := hi) (lo' := lo') (hi' := hi') _ _ e, d =>
      resizeIntegerL lo hi lo' hi' d (lowEnsAt L layout start e d)
  | _, .not a, d => do
      let ca ← lowEnsAt L layout start a d
      pure (bin2 10 d ca ([ci 1 (d + 1) 1 0], d + 2))
  | _, @Expr.add _ _ _ l1 h1 l2 h2 a b, d =>
      wideAddL l1 h1 l2 h2 (l1 + l2) (h1 + h2) d
        (lowEnsAt L layout start a)
        (lowEnsAt L layout (start + EntrySnapshots.words (oldCells a)) b)
  | _, @Expr.sub _ _ _ l1 h1 l2 h2 a b, d =>
      wideSubL l1 h1 l2 h2 (l1 - h2) (h1 - l2) d
        (lowEnsAt L layout start a)
        (lowEnsAt L layout (start + EntrySnapshots.words (oldCells a)) b)
  | _, @Expr.mul _ _ _ l1 h1 l2 h2 a b, d =>
      wideMulL l1 h1 l2 h2
        (imin (imin (l1*l2) (l1*h2)) (imin (h1*l2) (h1*h2)))
        (imax (imax (l1*l2) (l1*h2)) (imax (h1*l2) (h1*h2))) d
        (lowEnsAt L layout start a)
        (lowEnsAt L layout (start + EntrySnapshots.words (oldCells a)) b)
  | _, @Expr.neg _ _ _ lo hi a, d =>
      wideNegL lo hi (-hi) (-lo) d (lowEnsAt L layout start a)
  | _, @Expr.eq _ _ _ l1 h1 l2 h2 a b, d =>
      wideEqL l1 h1 l2 h2 d
        (lowEnsAt L layout start a)
        (lowEnsAt L layout (start + EntrySnapshots.words (oldCells a)) b)
  | _, @Expr.lt _ _ _ l1 h1 l2 h2 a b, d =>
      wideLtL l1 h1 l2 h2 d
        (lowEnsAt L layout start a)
        (lowEnsAt L layout (start + EntrySnapshots.words (oldCells a)) b)
  | _, @Expr.le _ _ _ l1 h1 l2 h2 a b, d =>
      wideLeL l1 h1 l2 h2 d
        (lowEnsAt L layout start a)
        (lowEnsAt L layout (start + EntrySnapshots.words (oldCells a)) b)
  | _, .and a b, d => do let ca ← lowEnsAt L layout start a d; let cb ← lowEnsAt L layout (start + EntrySnapshots.words (oldCells a)) b (d+1); pure (bin2 8 d ca cb)
  | _, .or a b, d => do let ca ← lowEnsAt L layout start a d; let cb ← lowEnsAt L layout (start + EntrySnapshots.words (oldCells a)) b (d+1); pure (bin2 9 d ca cb)
  | _, .intBuiltin2 op a b, d => intBuiltin2L op d
      (lowEnsAt L layout start a)
      (lowEnsAt L layout (start + EntrySnapshots.words (oldCells a)) b)
  -- Count uses the ordinary binder path. Entry reads inside a nonempty count
  -- remain refused there until binder-dependent snapshot capture is proved.
  | _, e, d => lowE (reserved := layout.ensReserved) L e d

/-- Function postconditions read the checked snapshot prefix described by this layout. -/
def lowEns (L : Lay D) (layout : FrameLayout) {Γ : Ctx} {Λ : List (Res D)}
    {τ : Ty} (e : Expr D Γ Λ τ) (d : Nat) : Option (List II × Nat) :=
  lowEnsAt L layout layout.snapshotBase e d

end Gabbro.Stage0.Senke
