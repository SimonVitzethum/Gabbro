module

public import Stage0.Senke.Welt.WeltAt
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuhe.Teil1

@[expose] public section

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik

variable {D : Deklaration}

/-- Relabel the very same image layout for the logical idle extension.
    Every emitted function keeps its address. The logical idle root
    has no emitted entry point. -/
def Lay.withIdle (L : Lay D) : Lay D.mitRuhe where
  fa := fun f => f.elim 0 L.fa
  regionCells := L.regionCells
  col := L.col
  ga := L.ga
  lo := L.lo
  hi := L.hi
  tor := L.tor
  byte := L.byte
  sb := L.sb
  st := L.st
  lk := L.lk
  sye := L.sye
  lockWait := L.lockWait

theorem sumFits_mapNumbers (sigNum tabNum : Nat → Nat) (cases : List (Option Ty)) :
    sumFits (Ty.mapCases sigNum tabNum cases) = sumFits cases := by
  have packed : ∀ cs : List (Option Ty),
      (Ty.mapCases sigNum tabNum cs).all (fun
        | none => true
        | some (.int lo hi) => decide (hi - lo < 2 ^ 56)
        | some _ => false) =
      cs.all (fun
        | none => true
        | some (.int lo hi) => decide (hi - lo < 2 ^ 56)
        | some _ => false) := by
    intro cs
    induction cs with
    | nil => rfl
    | cons c cs ih =>
      cases c with
      | none => simp only [Ty.mapCases, List.all_cons, ih]
      | some ty => cases ty <;> simp only [Ty.mapCases, Ty.mapNumbers, List.all_cons, ih]
  simp only [sumFits, Ty.mapCases_length, packed]

mutual
/-- Representation widths are invariant under renumbering of nominal
    signatures and table names. This includes nested aggregates. -/
theorem valueWords_mapNumbers (sigNum tabNum : Nat → Nat) : ∀ τ : Ty,
    valueWords (τ.mapNumbers sigNum tabNum) = valueWords τ
  | .arr τ n => by
    simp only [Ty.mapNumbers, valueWords, valueWords_mapNumbers sigNum tabNum τ]
  | .prod _ fields => by
    simp only [Ty.mapNumbers, valueWords, productWords_mapFields sigNum tabNum fields]
  | .sum cs => by
    simp only [Ty.mapNumbers, valueWords, Ty.mapCases_length, sumFits_mapNumbers,
      sumPayloadWords_mapCases sigNum tabNum cs]
  | .ptr ⟨_, _, .table _⟩ => rfl
  | .int .. | .bool | .opt .. | .why .. | .never | .fl .. | .fnptr .. | .ref .. | .str .. => rfl
termination_by structural τ => τ

theorem productWords_mapFields (sigNum tabNum : Nat → Nat) : ∀ fields : List Ty,
    productWords (Ty.mapFields sigNum tabNum fields) = productWords fields
  | [] => rfl
  | τ :: rest => by
    simp only [Ty.mapFields, productWords, valueWords_mapNumbers sigNum tabNum τ,
      productWords_mapFields sigNum tabNum rest]
termination_by structural fields => fields

theorem sumPayloadWords_mapCases (sigNum tabNum : Nat → Nat) : ∀ cs : List (Option Ty),
    sumPayloadWords (Ty.mapCases sigNum tabNum cs) = sumPayloadWords cs
  | [] => rfl
  | none :: rest => by
    simp only [Ty.mapCases, sumPayloadWords, sumPayloadWords_mapCases sigNum tabNum rest]
  | some τ :: rest => by
    simp only [Ty.mapCases, sumPayloadWords, valueWords_mapNumbers sigNum tabNum τ,
      sumPayloadWords_mapCases sigNum tabNum rest]
termination_by structural cs => cs
end

theorem Lay.withIdle_elem (L : Lay D) (t : D.Tab) (f : D.Feld t) (i : Nat) :
    L.withIdle.elem t f i = L.elem t f i := by
  simp only [Lay.elem, Lay.withIdle, Deklaration.mitRuhe, tyR, valueWords_mapNumbers]

theorem Lay.withIdle_count (L : Lay D) (t : D.Tab) : L.withIdle.count t = L.count t := rfl

end Gabbro.Stage0.Senke
