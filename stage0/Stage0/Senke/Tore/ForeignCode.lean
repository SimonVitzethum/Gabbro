/- One foreign result interface for register and explicit result-area profiles. -/
module
public import Stage0.Senke.Tore.AreaCode
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR
variable {D : Deklaration}

def usesArea (L : Lay D) (a : D.Ax) : Bool :=
  ((L.tor a).bind TorB.resultArea).isSome

/-- A complete nonfallible foreign prefix leaves the whole value at `s`.
    Consumers do not need to know which profile transported the answer. -/
def plainForeignC (L : Lay D) {Γ : Ctx} {Λ : List (Res D)} (a : D.Ax)
    (args : Args D Γ Λ (D.aparams a)) (τ : Ty) (s reserved : Nat) :
    Option (List II × Nat) :=
  if usesArea L a then
    if D.agruende a = 0 then do
      let request ← areaC L a args τ s reserved
      pure (request.1 ++ areaReceive τ s, request.2)
    else none
  else do
    let request ← torC0 L a args s reserved
    let check ← chkC (D.aerg a) s
    pure (request.1 ++ check, max request.2 (s + 10))

/-- The common fallible prefix dispatches a listed errno across `skip` following
    instructions. A success always leaves the complete typed value at `s`.
    VOID calls keep the existing binder without a value decoder. -/
def fallibleForeignC (L : Lay D) {Γ : Ctx} {Λ : List (Res D)} (a : D.Ax)
    (args : Args D Γ Λ (D.aparams a)) (τ : Ty) (s skip reserved : Nat) :
    Option (List II × Nat) := do
  let b ← L.tor a
  if fehlGut (D.agruende a) b.fehler = true ∧ 0 < D.agruende a ∧
      valueWords (.why (D.agruende a)) = 1 then
    let (request, check) ← if usesArea L a then do
        let request ← areaC L a args τ s reserved
        pure (request, areaReceive τ s)
      else if fallibleTy τ then do
        let request ← torC L a args s reserved
        let check ← chkC (some τ) s
        pure (request, check)
      else none
    if 16 + 16 * (6 * b.fehler.length) + 16 * (check.length + skip) < 2 ^ 31 then
      pure (request.1 ++ fehlC s b.fehler (16 * (check.length + skip)) ++ check,
        max request.2 (s + 10))
    else none
  else none

end Gabbro.Stage0.Senke
