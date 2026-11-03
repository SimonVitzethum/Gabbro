/- Explicit caller-owned result areas share the ordinary value ABI. -/
module
public import Stage0.Senke.Tor
public import Stage0.Senke.Ausdruck.Aggregat.Frame.Copy
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR
variable {D : Deklaration}

/-- Hidden result pointers use an unused request argument register. Source
    arguments retain their existing order; no argument may be overwritten. -/
def areaGut (b : TorB) (n j : Nat) : Bool :=
  decide (n ≤ j ∧ j < 6) && b.regs == regsIn n && lit32 b.nr &&
    decide (b.resultArea = some j)

/-- Keep the request and its stop/check scratch below the canonical result
    span. Argument evaluation may use this span before the provider fills it. -/
def foreignResultBase (s : Nat) : Nat := s + 10

/-- Ordinary request construction, plus the explicit hidden argument. -/
def areaRequest (b : TorB) (s n j : Nat) (arguments : List II) : List II :=
  arguments ++ zeroC (s + 1 + n) (6 - n) ++
    [ci 17 (s + 1 + j) (foreignResultBase s) 0, ci 1 s b.nr 0, ci 23 s s 0]

/-- A result-area provider writes exactly the same complete value encoding as
    an ordinary callee. Pointer-buffer arguments keep their separate packing
    profile; this profile currently accepts scalar request arguments. -/
def areaC (L : Lay D) {Γ : Ctx} {Λ : List (Res D)} (a : D.Ax)
    (args : Args D Γ Λ (D.aparams a)) (τ : Ty) (s reserved : Nat) :
    Option (List II × Nat) := do
  let b ← L.tor a
  let j ← b.resultArea
  if areaGut b (D.aparams a).length j &&
      (D.aparams a).all (fun ty => wortTy ty && !isPtr ty) then
    let arguments ← lowR L args (s + 1) reserved
    pure (areaRequest b s (D.aparams a).length j arguments.1,
      max arguments.2 (foreignResultBase s + valueWords τ))
  else none

/-- Zero is success; errno dispatch precedes this check for a fallible call.
    An unknown nonzero tag stops with 110 and never copies an unspecified span. -/
def areaCheck (s : Nat) : List II :=
  [ci 1 (s + 1) 0 0, ci 14 (s + 1) s (s + 1)] ++ guardC (s + 1) 110 (s + 2)

/-- Copy the complete normal result back to the lexical binder's value slot. -/
def areaReceive (τ : Ty) (s : Nat) : List II :=
  areaCheck s ++ copyWords (valueWords τ) s (foreignResultBase s)

theorem areaCheck_length (s : Nat) : (areaCheck s).length = 7 := rfl

theorem areaReceive_length (τ : Ty) (s : Nat) :
    (areaReceive τ s).length = 7 + valueWords τ := by
  simp only [areaReceive, List.length_append, areaCheck_length, copyWords_length]

/-- The request and complete result span are represented in the reported frame. -/
theorem areaC_top {L : Lay D} {Γ : Ctx} {Λ : List (Res D)} {a : D.Ax}
    {args : Args D Γ Λ (D.aparams a)} {τ : Ty} {s reserved top : Nat} {code : List II}
    (emitted : areaC L a args τ s reserved = some (code, top)) :
    foreignResultBase s + valueWords τ ≤ top := by
  simp only [areaC, bind, Option.bind_eq_some_iff] at emitted
  obtain ⟨b, bound, j, register, emitted⟩ := emitted
  split at emitted
  · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at emitted
    obtain ⟨arguments, generated, _, rfl⟩ := emitted
    exact Nat.le_max_right _ _
  · cases emitted

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
