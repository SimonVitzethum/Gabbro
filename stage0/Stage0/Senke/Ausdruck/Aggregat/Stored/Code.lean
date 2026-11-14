/- Read stored aggregate elements without materialising the enclosing value. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Hilfen
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR
variable {D : Deklaration}

/-- Only actual storage roots qualify. Computed values retain value lowering.
    Old reads retain their separate snapshot-aware path. -/
def storedExpr {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} : Expr D Γ Λ τ → Bool
  | .var .. | .glob .. | .slot .. | .thru .. | .thruOwn .. | .slotRef .. => true
  | _ => false

/-- Address and index occupy three words above the result, independent of the
    array length. The typed index already supplies the source bounds check. -/
def arrReadL (τ : Ty) (n d : Nat) (address index : Option (List II × Nat)) :
    Option (List II × Nat) :=
  if 0 < n ∧ 8 * valueWords τ < 2 ^ 31 then do
    let ca ← address
    let ci' ← index
    let ptr := d + valueWords τ
    pure (ca.1 ++ ci'.1 ++
      [ci 1 (ptr + 2) (8 * valueWords τ) 0, ci 5 (ptr + 1) (ptr + 1) (ptr + 2),
       ci 3 ptr ptr (ptr + 1)] ++ loadPointerSpan (valueWords τ) d ptr (ptr + 2) 0,
      max (max ca.2 ci'.2) (ptr + 3))
  else none

theorem arrReadL_top {τ : Ty} {n d top : Nat} {a i : Option (List II × Nat)} {c : List II}
    (made : arrReadL τ n d a i = some (c, top)) : d < top := by
  unfold arrReadL at made
  split at made
  · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at made
    obtain ⟨⟨ca, ta⟩, _, ⟨ci', ti⟩, _, _, rfl⟩ := made
    omega
  · cases made

end Gabbro.Stage0.Senke
