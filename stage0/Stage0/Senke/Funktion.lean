/-
  File:      stage0/Stage0/Senke/Funktion.lean
  Subject:   The lowering of stage 0, part 3: function bodies (end blocks) and functions with their contracts.

  A function `f` with `np` parameters runs in a frame whose slots 0 and 1 the `call` wrote, slot 2 holds the
  depth (G's `fuel`), the parameters follow. Its code:
  * depth 0: `exit_group(105)` (`abstieg`); then `requires` into slot `FB + np`, false: `exit_group(101)`;
  * the body (`lowEnd`), which writes no slot below `FB + np`, so the parameters stay as the call gave them;
  * every `ret e`: `e`, into slot `lo = FB + np`, then `ensures` over the result and the parameters into the
    slot above, false: `exit_group(102)`; else the result into slot 2 and `ret`.
  Refused: a function with invariants to keep (`schuldet`), or a form outside the fragment. A function without a
  result returns whatever word slot `FB + np` holds; nobody reads it.
-/
import Stage0.Senke.Anweisung
import Stage0.Senke.Stopp

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR

variable {D : Deklaration} {V : Vertrag D}

def lowEnd (A : D.Fn → Nat) (L : Lay D) (lo : Nat) (ens : List II × Nat) (pr : List Nat) (ex : Int × Int) :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → Endblock D V l Γ Λ → Option (List II × Nat)
  | _, Γ, _, .ret e _ => do
    let ce ← lowErg L e (frei Γ)
    pure (ce.1 ++ retC lo (frei Γ) ens.1, max ce.2 (max ens.2 (retTop lo)))
  | _, _, _, .cons s rest => do
    let cr ← lowEnd A L lo ens pr ex rest
    let cs ← lowS A L lo ens pr (exPlus ex cr.1.length) s
    pure (cs.1 ++ cr.1, max cs.2 cr.2)
  | _, Γ, _, .bind e rest => do
    let ce ← lowE L e (frei Γ)
    let cr ← lowEnd A L lo ens pr ex rest
    pure (ce.1 ++ cr.1, max ce.2 cr.2)
  | _, Γ, _, .bindCall f args _ _ _ rest => do
    let ca ← lowA L args (frei Γ + FB)
    let cr ← lowEnd A L lo ens pr ex rest
    pure (callC A f (frei Γ) ca.1 ++ [ci 2 (frei Γ) (frei Γ + 2) 0] ++ cr.1, max (callTop f (frei Γ) ca.2) cr.2)
  | _, Γ, _, .ite c t e => do
    let cc ← lowE L c (frei Γ)
    let ce ← lowEnd A L lo ens pr ex e
    let ct ← lowEnd A L lo ens pr (exPlus ex ce.1.length) t
    pure (cc.1 ++ [ci 19 (frei Γ) (16 * (ct.1.length + 1)) 0] ++ ct.1 ++ ce.1, max cc.2 (max ct.2 ce.2))
  | _, Γ, _, .bindAxiom a args _ _ _ _ _ rest => do
    let ct ← torC0 L a args (frei Γ)
    let ck ← chkC (D.aerg a) (frei Γ)
    let cr ← lowEnd A L lo ens pr ex rest
    pure (ct.1 ++ ck ++ cr.1, max ct.2 (max (frei Γ + 10) cr.2))
  | _, Γ, _, .awaits g _ _ _ _ rest =>
    if lit32 (L.ga g) then do
      let cr ← lowEnd A L lo ens pr ex rest
      pure ([ci 1 (frei Γ) (L.ga g) 0, ci 15 (frei Γ) (frei Γ) 0] ++ cr.1, max (frei Γ + 1) cr.2)
    else none
  | _, Γ, _, .exchange g neu _ _ rest =>
    if lit32 (L.ga g) then do
      let cn ← lowE L neu (frei Γ + 1)
      let cr ← lowEnd A L lo ens pr ex rest
      if 16 * (cn.1.length + 5) < 2 ^ 31 then
        pure (exC (frei Γ) (L.ga g) cn.1 ++ cr.1, max (max cn.2 (frei Γ + 4)) cr.2)
      else none
    else none
  | _, Γ, _, .bindAxiomElse a args _ _ _ _ _ _ err rest =>
    match L.tor a, D.aerg a with
    | some b, some (.int lo' hi') =>
      if fehlGut (D.agruende a) b.fehler = true ∧ 0 ≤ lo' ∧ 0 < D.agruende a then do
        let ct ← torC L a args (frei Γ)
        let ck ← chkC (some (.int lo' hi')) (frei Γ)
        let ce ← lowEnd A L lo ens pr ex err
        let cr ← lowEnd A L lo ens pr (exPlus ex ce.1.length) rest
        if 16 + 16 * (6 * b.fehler.length) + 16 * (ck.length + cr.1.length) < 2 ^ 31 then
          pure (ct.1 ++ fehlC (frei Γ) b.fehler ((16 * (ck.length + cr.1.length) : Nat) : Int) ++ ck ++ cr.1 ++ ce.1,
            max ct.2 (max (frei Γ + 10) (max cr.2 ce.2)))
        else none
      else none
    | _, _ => none
  | _, _, _, _ => none

/-- The code of `f`, and the first slot it does not write. -/
def lowFun (P : Programm D) (A : D.Fn → Nat) (L : Lay D) (f : D.Fn) : Option (List II × Nat) :=
  let np := (D.params f).length
  if (D.invs.filter (schuldet f)).isEmpty then do
    let req ← lowE L (P.requires f) (FB + np)
    let ens ← lowE L (P.ensures f) (FB + np + 1)
    let body ← lowEnd A L (FB + np) ens [] (0, 0) (P.rumpf f)
    pure (guardC 2 105 (FB + np) ++ req.1 ++ guardC (FB + np) 101 (FB + np) ++ body.1,
      max (FB + np + 8) (max req.2 body.2))
  else none

end Gabbro.Stage0.Senke
