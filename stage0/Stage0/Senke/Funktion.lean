/-
  File:      stage0/Stage0/Senke/Funktion.lean
  Subject:   The lowering of stage 0, part 3: function bodies (end blocks) and functions with their contracts.

  A function `f` with `np` parameters runs in a frame whose slots 0 and 1 the `call` wrote, slot 2 holds the
  depth (G's `fuel`), the parameters follow. Its code:
  * depth 0: `exit_group(105)` (`abstieg`); then `requires` into slot `FB + np`, false: `exit_group(101)`;
  * the body (`lowEnd`), which writes no slot below `FB + np`, so the parameters stay as the call gave them;
  * every `ret e`: `e`, into slot `lo = FB + np`, then `ensures` over the result and the parameters into the
    slot above, false: `exit_group(102)`; else the result into slot 2 and `ret`.
  Refused: a function with invariants to keep (`schuldet`), without a result, or a form outside the fragment.
-/
import Stage0.Senke.Anweisung
import Stage0.Senke.Stopp

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR

variable {D : Deklaration} {V : Vertrag D}

def lowErg {Λ : List (Res D)} {Γ : Ctx} : {e : Option Ty} → ErgExpr D Γ Λ e → Nat → Option (List II × Nat)
  | _, .empty, _ => none
  | _, .val e, d => lowE e d

/-- `ret`: the result from slot `r` into slot `q` (`FB + np`, the slot of `ensures`' result variable), the
    `ensures` code `ens`, the check, slot 2, back. -/
def retC (q r : Nat) (ens : List II) : List II :=
  [ci 2 q r 0] ++ ens ++ [ci 19 ((q + 1 : Nat) : Int) 48 0, ci 2 2 q 0, ci 21 0 0 0] ++ stopC 102 (q + 1)

def retTop (q : Nat) : Nat := q + 1 + 8

def lowEnd (A : D.Fn → Nat) (lo : Nat) (ens : List II × Nat) :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → Endblock D V l Γ Λ → Option (List II × Nat)
  | _, Γ, _, .ret e _ => do
    let ce ← lowErg e (frei Γ)
    pure (ce.1 ++ retC lo (frei Γ) ens.1, max ce.2 (max ens.2 (retTop lo)))
  | _, _, _, .cons s rest => do
    let cs ← lowS A lo s
    let cr ← lowEnd A lo ens rest
    pure (cs.1 ++ cr.1, max cs.2 cr.2)
  | _, Γ, _, .bind e rest => do
    let ce ← lowE e (frei Γ)
    let cr ← lowEnd A lo ens rest
    pure (ce.1 ++ cr.1, max ce.2 cr.2)
  | _, Γ, _, .bindCall f args _ _ _ rest => do
    let ca ← lowA args (frei Γ + FB)
    let cr ← lowEnd A lo ens rest
    pure (callC A f (frei Γ) ca.1 ++ [ci 2 (frei Γ) (frei Γ + 2) 0] ++ cr.1, max (callTop f (frei Γ) ca.2) cr.2)
  | _, Γ, _, .ite c t e => do
    let cc ← lowE c (frei Γ)
    let ct ← lowEnd A lo ens t
    let ce ← lowEnd A lo ens e
    pure (cc.1 ++ [ci 19 (frei Γ) (16 * (ct.1.length + 1)) 0] ++ ct.1 ++ ce.1, max cc.2 (max ct.2 ce.2))
  | _, _, _, _ => none

/-- `brz a` over a stop: if slot `a` is zero, `exit_group(c)`; else on after it. -/
def guardC (a c s : Nat) : List II := [ci 19 a 32 0, ci 18 64 0 0] ++ stopC c s

/-- The code of `f`, and the first slot it does not write. -/
def lowFun (P : Programm D) (A : D.Fn → Nat) (f : D.Fn) : Option (List II × Nat) :=
  let np := (D.params f).length
  if (D.invs.filter (schuldet f)).isEmpty && (D.erg f).isSome then do
    let req ← lowE (P.requires f) (FB + np)
    let ens ← lowE (P.ensures f) (FB + np + 1)
    let body ← lowEnd A (FB + np) ens (P.rumpf f)
    pure (guardC 2 105 (FB + np) ++ req.1 ++ guardC (FB + np) 101 (FB + np) ++ body.1,
      max (FB + np + 8) (max req.2 body.2))
  else none

end Gabbro.Stage0.Senke
