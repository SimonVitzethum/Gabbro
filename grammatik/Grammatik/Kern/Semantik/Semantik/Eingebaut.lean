/- C13: the value semantics of the closed integer builtins and of the bounded count fold.

   `evalIntBuiltin1/2` apply only `Zahl.addW/subW/mulW/shlW/addS` (`Kern/Semantik/Ueberlauf`) and
   `Zahl.clz/ctz/log2_floor/popcount/rotl/rotr/bswap16/32/64` (`Kern/Syntax/Bits/T2`); no new
   arithmetic is defined here. `zaehleWahr` counts over `alleIndizes`, with the bound `count ≤ n`
   in its type. `alleIndizes` itself moved here unchanged from `Semantik/T1/Teil1`. -/

module

public import Grammatik.Kern.Syntax.Syntax.Teil2
public import Grammatik.Kern.Semantik.Ueberlauf
public import Grammatik.Kern.Syntax.Bits.T2.Teil1

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- Alle Indizes `0 ..< n`, als Werte des Indextyps. -/
def alleIndizes (n : Int) : List (Zahl 0 (n - 1)) :=
  (List.range n.toNat).filterMap fun (k : Nat) =>
    if h : ((k : Nat) : Int) ≤ n - 1 then some ⟨((k : Nat) : Int), by omega, h⟩ else none

/-- There are at most `n` indices `0 ..< n`. -/
theorem alleIndizes_length_le (n : Nat) : (alleIndizes (n : Int)).length ≤ n := by
  unfold alleIndizes
  refine Nat.le_trans (List.length_filterMap_le _ _) ?_
  have h2 : ∀ m : Nat, (List.range m).length = m := fun m => List.length_range
  have h3 := h2 (n : Int).toNat
  omega

/-- The index domain is EXACT: there are exactly `n` indices `0 ..< n` (the cardinality of every finite count
    domain: a table's slots, a fixed array's indices; a tree domain filters these by `reaches`). -/
theorem alleIndizes_length (n : Nat) : (alleIndizes (n : Int)).length = n := by
  unfold alleIndizes
  rw [Int.toNat_natCast]
  have h := List.filterMap_length_eq_length
    (f := fun (k : Nat) => if h : ((k : Nat) : Int) ≤ (n : Int) - 1 then
      some (⟨((k : Nat) : Int), by omega, h⟩ : Zahl 0 ((n : Int) - 1)) else none) (l := List.range n)
  rw [List.length_range] at h
  refine h.mpr ?_
  intro k hk
  have hk' : k < n := List.mem_range.mp hk
  have hle : ((k : Nat) : Int) ≤ (n : Int) - 1 := by omega
  simp only [hle, ↓reduceDIte, Option.isSome_some]

/-- The count fold: how many of the indices `0 ..< n` satisfy `p`, with the bound `count ≤ n`. -/
def zaehleWahr (n : Nat) (p : Zahl 0 ((n : Int) - 1) → Bool) : Zahl 0 (n : Int) :=
  ⟨(((alleIndizes (n : Int)).filter p).length : Nat), by omega,
    Int.ofNat_le.mpr (Nat.le_trans (List.length_filter_le p _) (alleIndizes_length_le n))⟩

/-- Two numbers with the same value are equal (proofs are irrelevant). -/
theorem Zahl.ext_n {lo hi : Int} {a b : Zahl lo hi} (h : a.n = b.n) : a = b := by
  cases a; cases b; simp only at h; subst h; rfl

/-- Predicates that agree on every index count alike. -/
theorem zaehleWahr_congr (n : Nat) (p q : Zahl 0 ((n : Int) - 1) → Bool)
    (h : ∀ k, k ∈ alleIndizes (n : Int) → p k = q k) : zaehleWahr n p = zaehleWahr n q :=
  Zahl.ext_n (congrArg (fun m : Nat => (m : Int)) (congrArg List.length (List.filter_congr h)))

/-- A one-operand builtin applied to its operand value. -/
def evalIntBuiltin1 {τ1 τ : Ty} : IntBuiltin [τ1] τ → Wert D τ1 → Wert D τ
  | .clz w, x => Zahl.clz w x
  | .ctz w, x => Zahl.ctz w x
  | .log2Floor w, x => Zahl.log2_floor w x
  | .popcount w, x => Zahl.popcount w x
  | .bswap16, x => Zahl.bswap16 x
  | .bswap32, x => Zahl.bswap32 x
  | .bswap64, x => Zahl.bswap64 x

/-- A two-operand builtin applied to its operand values. -/
def evalIntBuiltin2 {τ1 τ2 τ : Ty} : IntBuiltin [τ1, τ2] τ → Wert D τ1 → Wert D τ2 → Wert D τ
  | .addW w, a, b => Zahl.addW w a b
  | .subW w, a, b => Zahl.subW w a b
  | .mulW w, a, b => Zahl.mulW w a b
  | .shlW w, a, s => Zahl.shlW w a s
  | .addS _ _, a, b => Zahl.addS a b
  | .rotl w, a, s => Zahl.rotl w a s
  | .rotr w, a, s => Zahl.rotr w a s

end Gabbro.Grammatik
