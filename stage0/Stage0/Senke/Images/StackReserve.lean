/- Automatic stack sizing reuses the frame high-water mark already computed by
   image emission. Runtime guards and all frame/execution relations stay intact. -/
module
public import Stage0.Senke.Images.Bild
public import Grammatik.Logik.Ruf.RufKeinAbstiegTief
public import Grammatik.Logik.Terminierung.Entscheidung.Teil1
public import Grammatik.Nebenlaeufigkeit.Allgemein.FadenMerkmal.Stellen
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR

/-- Explicit capacities retain the existing checked builder behavior. -/
theorem stackReserve_explicit (requested largest scratch : Nat) (positive : requested ≠ 0) :
    stackReserve requested largest scratch = requested := by
  simp only [stackReserve, if_neg positive]

/-- An automatic reserve keeps the old image geometry whenever its floor suffices. -/
theorem stackReserve_unchanged (largest scratch : Nat)
    (frames : FB + (stackReserveDepth + 1) * largest ≤ stackReserveFloor)
    (startup : scratch ≤ stackReserveFloor) :
    stackReserve 0 largest scratch = stackReserveFloor := by
  simp only [stackReserve, ↓reduceIte, ite_true]
  omega

/-- The reservation covers the floor, all requested frame levels and startup scratch. -/
theorem stackReserve_bounds (largest scratch : Nat) :
    stackReserveFloor ≤ stackReserve 0 largest scratch ∧
    FB + (stackReserveDepth + 1) * largest ≤ stackReserve 0 largest scratch ∧
    scratch ≤ stackReserve 0 largest scratch := by
  simp only [stackReserve, ↓reduceIte, ite_true]
  omega

/-- Frame width cannot reduce the depth selected from that same high-water mark. -/
theorem stackReserve_depth (largest scratch : Nat) (positive : 0 < largest) :
    stackReserveDepth ≤ depthOf (stackReserve 0 largest scratch) largest := by
  have room := (stackReserve_bounds largest scratch).2.1
  have quotient : stackReserveDepth + 1 ≤ (stackReserve 0 largest scratch - FB) / largest :=
    (Nat.le_div_iff_mul_le positive).mpr (by omega)
  unfold depthOf
  omega

/-- The actual final lowering, rather than an assumed address-independent frame size,
    certifies the depth of every accepted automatic image. -/
theorem bild_auto_depth {D : Deklaration} {passes : Nat} {P : Programm D}
    {Y : Nat → Lay D} {fs : List D.Fn} {pos : D.Fn → Nat} {name : D.Fn → String}
    {main : D.Fn} {args : Env D (D.params main)}
    {starts : List (Σ f : D.Fn, Env D (D.params f))} {req : Nat} {image : Bild D}
    (emitted : bild passes P Y fs pos name main args starts 0 req = .ok image) :
    stackReserveDepth ≤ image.depth := by
  simp only [bild] at emitted
  split at emitted
  · cases emitted
  · next preliminary firstPass =>
    split at emitted
    · cases emitted
    · next relocated secondPass =>
      split at emitted
      · next accepted =>
        simp only [Except.ok.injEq] at emitted
        subst image
        rcases accepted.2.2 with nonzero | enough
        · exact False.elim (nonzero rfl)
        · exact enough
      · exfalso
        revert emitted
        repeat' split
        all_goals intro emitted; cases emitted

private theorem depthLookup_ofFn {functions : Nat} (f : Fin functions → Bool) (fn : Fin functions) :
    (Array.ofFn f)[fn.val]?.getD false = f fn := by
  simp [fn.isLt]

private theorem depthSites_ofFn {α : Type} {functions : Nat} (f : Fin functions → α)
    (fn : Fin functions) (inside : fn.val < (Array.ofFn f).size) :
    (Array.ofFn f)[fn.val]'inside = f fn :=
  (Array.getElem_ofFn inside).trans (congrArg f (Fin.ext rfl))

def imageDepthRounds {D : Deklaration} {functions : Nat} (index : Fin functions ≃ D.Fn)
    (sites : Fin functions → List (Stelle D)) : Nat → Array Bool
  | 0 => Array.ofFn fun _ : Fin functions => false
  | depth + 1 =>
    let previous := imageDepthRounds index sites depth
    Array.ofFn fun f => (sites f).all
      (Merkmal.an ⟨fun g => previous[(index.symm g).val]?.getD false, fun _ => false, fun _ => true⟩)

/-- Compute the call-depth predicate for all functions together. The
    call sites are read once from the canonical typed bodies. Each round
    uses only the previous table, rather than recursively walking the
    transitive call tree separately for each root. -/
def imageDepthTable {D : Deklaration} {functions : Nat} (index : Fin functions ≃ D.Fn)
    (P : Programm D) (depth : Nat) : Array Bool :=
  let sites := Array.ofFn fun f : Fin functions => stellenE (P.rumpf (index f))
  imageDepthRounds index (fun f => sites[f.val]'(by simp [sites, f.isLt])) depth

/-- The table computes exactly the model predicate with the emitted
    depth, including refusal of an unbounded indirect call. -/
theorem imageDepthTable_exact {D : Deklaration} {functions : Nat} (index : Fin functions ≃ D.Fn)
    (P : Programm D) (depth : Nat) (fn : D.Fn) :
    (imageDepthTable index P depth)[(index.symm fn).val]?.getD false = rufTief P depth fn := by
  induction depth generalizing fn with
  | zero =>
    change (Array.ofFn fun _ : Fin functions => false)[(index.symm fn).val]?.getD false = false
    exact depthLookup_ofFn _ _
  | succ depth ih =>
    change (Array.ofFn fun f : Fin functions => _)[(index.symm fn).val]?.getD false = _
    rw [depthLookup_ofFn, depthSites_ofFn]
    change (stellenE (P.rumpf (index (index.symm fn)))).all
      (Merkmal.an ⟨fun g => (imageDepthTable index P depth)[(index.symm g).val]?.getD false,
        fun _ => false, fun _ => true⟩) = rufTief P (depth + 1) fn
    rw [Equiv.apply_symm_apply, rufTief, rufeE_mE, mE_stellen]
    exact congrArg (fun admitted => (stellenE (P.rumpf fn)).all
      (Merkmal.an ⟨admitted, fun _ => false, fun _ => true⟩)) (funext ih)

end Gabbro.Stage0.Senke
