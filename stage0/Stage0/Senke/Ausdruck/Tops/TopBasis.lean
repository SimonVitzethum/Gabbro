/-
  File:      stage0/Stage0/Senke/Ausdruck/Top.lean
  Subject:   The slot an expression's code stops at (`lowE_top`), and the shape of a binary operation's code
             (`bin_some`, `binE_ok`): its two operands, then one instruction.
-/
module
public import Stage0.Senke.Ausdruck.Gleit.Grenze
public import Stage0.Senke.Ausdruck.Gleichungen
public import Stage0.Senke.Ausdruck.Sim
public import Stage0.Senke.Ausdruck.Wort.Wort
public import Stage0.Senke.Welt.Spans.CellCode
@[expose] public section

variable {currentOld : Bool}


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration} {L : Lay D}

/-! ## The slot the lowering stops at -/

theorem constValue_top {τ : Ty} (v : Wert D τ) {d top : Nat} {c : List II}
    (lower : some (constWords (encodeWords L τ v) d) = some (c, top)) : d < top := by
  have eq := congrArg (fun p => p.map Prod.snd) lower
  simp only [Option.map_some, Option.some.injEq] at eq
  have span := constWords_span (encodeWords L τ v) d
  have width := encodeWords_length L τ v
  have positive := valueWords_pos τ
  omega

theorem integerExtensionL_span {lo : Int} {extra base top : Nat} {c : List II}
    (lower : integerExtensionL lo extra base = some (c, top)) : base + extra ≤ top := by
  have zeros := constWords_span (List.replicate extra (0 : Runner.W)) base
  simp only [List.length_replicate] at zeros
  simp only [integerExtensionL] at lower
  split at lower
  · simp only [wennL, bind, Option.bind_some] at lower
    split at lower
    · have ceiling := congrArg Prod.snd (Option.some.inj lower)
      dsimp only at ceiling
      omega
    · cases lower
  · have ceiling := congrArg Prod.snd (Option.some.inj lower)
    dsimp only at ceiling
    omega

theorem resizeIntegerL_top {lo hi lo' hi' : Int} {d top : Nat}
    {child : Option (List II × Nat)} {c : List II}
    (lower : resizeIntegerL lo hi lo' hi' d child = some (c, top))
    (childTop : ∀ cc tt, child = some (cc, tt) → d < tt) : d < top := by
  simp only [resizeIntegerL, bind, Option.bind_eq_some_iff] at lower
  obtain ⟨⟨cc, tt⟩, hc, lower⟩ := lower
  have bound := childTop cc tt hc
  split at lower
  · simp only [pure, Option.some.injEq, Prod.mk.injEq] at lower; omega
  · change (integerExtensionL lo (integerWords lo' hi' - integerWords lo hi) (d + integerWords lo hi)).bind
      (fun extension => some (cc ++ extension.1, max tt extension.2)) = some (c, top) at lower
    rw [Option.bind_eq_some_iff] at lower
    obtain ⟨⟨ce, te⟩, _, lower⟩ := lower
    simp only [pure, Option.some.injEq, Prod.mk.injEq] at lower
    omega

/-- The code of a binary operation stops above `d` once its first operand does. -/
theorem bin_top {reserved : Nat} {Λ : List (Res D)} {Γ : Ctx} {τa τb : Ty} {a : Expr D Γ Λ τa} {b : Expr D Γ Λ τb} {o d : Nat}
    {c : List II} {top : Nat} (ht : ∀ c t, lowE (currentOld := currentOld) L (reserved := reserved) a d = some (c, t) → d < t)
    (h : (do let ca ← lowE (currentOld := currentOld) L (reserved := reserved) a d; let cb ← lowE (currentOld := currentOld) L (reserved := reserved) b (d + 1); pure (bin2 o d ca cb)) = some (c, top)) : d < top := by
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨ca, ta⟩, ha, ⟨cb, tb⟩, _, he⟩ := h
  simp only [bin2, pure, Option.some.injEq, Prod.mk.injEq] at he
  have := ht ca ta ha
  omega

theorem lowN_top {reserved : Nat} {Λ : List (Res D)} {Γ : Ctx} {tag : Nat} :
    {a : Option Ty} → (e : NutzlastExpr D Γ Λ a) → (d : Nat) → (c : List II) →
    (top : Nat) → lowN (currentOld := currentOld) L (reserved := reserved) tag e d = some (c, top) → d < top
  | _, .empty, d, c, top, h => by
    simp only [lowE_eqs, Option.some.injEq, Prod.mk.injEq] at h; omega
  | some τ, .val e, d, c, top, h => by
    cases τ with
    | int lo hi =>
      simp only [lowE_eqs, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨⟨ce, te⟩, _, he⟩ := h
      simp only [packSum, bin2, Prod.mk.injEq] at he
      omega
    | bool | opt _ | sum _ | why _ | never | fl _ _ | fnptr _ | ptr _ | ref _ | arr _ _ | prod _ _ | str _ => by
      have hnone : lowN (currentOld := currentOld) L (reserved := reserved) tag e d = none := rfl
      rw [hnone] at h
      cases h

theorem readBytesL_top (L : Lay D) (t : D.Tab) (f : D.Feld t) (idx : Nat → Option (List II × Nat)) :
    (n j d : Nat) → (c : List II) → (top : Nat) →
    readBytesL L t f idx j n d = some (c, top) → d < top
  | 0, j, d, c, top, h => by
    simp only [readBytesL, Option.some.injEq, Prod.mk.injEq] at h; omega
  | n + 1, j, d, c, top, h => by
    simp only [readBytesL, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨ci', _, head, _, tail, _, h⟩ := h
    simp only [bin2, Prod.mk.injEq] at h
    omega

theorem reachEqL_top {d top : Nat} {a b : Option (List II × Nat)} {c : List II}
    (h : reachEqL d a b = some (c, top)) : d < top := by
  simp only [reachEqL, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨ca, _, cb, _, he⟩ := h
  simp only [Prod.mk.injEq] at he
  omega

theorem reachL_top {d top : Nat} {L : Lay D} {t : D.Tab} {f : D.Feld t} {c : List II}
    (n : Nat) (a b : Option (List II × Nat)) (h : reachL L t f d n a b = some (c, top)) : d < top := by
  cases n with
  | zero => exact reachEqL_top h
  | succ n =>
    simp only [reachL, wennL, bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨cc, tc⟩, hc, ca, _, cb, _, h⟩ := h
    have := reachEqL_top hc
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
    · cases h

theorem wordL_top {o d top : Nat} {a b : Option (List II × Nat)} {c : List II}
    (h : wordL o d a b = some (c, top)) : d < top := by
  simp only [wordL, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨ca, _, cb, _, h⟩ := h
  obtain ⟨_, rfl⟩ := Prod.mk.inj h
  omega

theorem scalarCompareL_top {equal : Bool} {d top : Nat} {l1 h1 l2 h2 : Int}
    {a b : Option (List II × Nat)} {c : List II}
    (left : ∀ ca ta, a = some (ca, ta) → d < ta)
    (lower : scalarCompareL equal d l1 h1 l2 h2 a b = some (c, top)) : d < top := by
  simp only [scalarCompareL, bind, Option.bind_eq_some_iff] at lower
  obtain ⟨⟨ca, ta⟩, ha, ⟨cb, tb⟩, _, lower⟩ := lower
  have := left ca ta ha
  split at lower
  · simp only [pure, Option.some.injEq, Prod.mk.injEq, bin2] at lower; omega
  · split at lower
    · simp only [pure, Option.some.injEq, Prod.mk.injEq] at lower; omega
    · cases lower

theorem strGetL_top {d top : Nat} {a b : Option (List II × Nat)} {c : List II}
    (h : strGetL d a b = some (c, top)) : d < top := by
  simp only [strGetL, wennL, bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨cc, tc⟩, hc, ca, _, cb, _, h⟩ := h
  have := wordL_top hc
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
  · cases h


end Gabbro.Stage0.Senke
