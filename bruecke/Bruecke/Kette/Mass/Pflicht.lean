module
public import Bruecke.Realisierung
public import Bruecke.Anweisung.Zweig.Benannt
@[expose] public section

/-!
# Recursion: callee duties bounded by a well-founded measure

`meetsU` puts the FULL contract of every callee in front of the turnstile. For a recursive
function that is circular: the duty assumes the very contract it is meant to establish, and no
Body environment can be built from it. `meetsUM` replaces it by the measure form of
`Gabbro.Body.contracts_of_duties_rec`: a callee's contract is assumed only on entry states whose
measure lies strictly below the caller's entry value, in one well-founded order shared by the
whole unit. Frames stay unconditional (a frame never depends on the entry state's measure).

The measure is part of the person's proof, not of the trusted statement: the realisation
(`Kette/Mass/Realisierung.lean`) is sound for EVERY well-founded measure. A `decreases` clause
is one way to supply it; the call-graph rank of an acyclic unit is another (`meetsUM_of_rang`),
so every acyclic duty `meetsU` carries over unchanged.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- **A well-founded measure on Body entries**: a value per called name and entry state, and a
    well-founded order on the values. Mutual recursion shares one order across its cycle. -/
structure MassU where
  /-- The measure values. -/
  Wert : Type
  /-- `lt a b`: `a` lies strictly below `b`. -/
  lt : Wert → Wert → Prop
  /-- No infinite descent. -/
  wf : WellFounded lt
  /-- The value of an entry into the function named `n` at state `t`. -/
  mass : String → Gabbro.Body.State → Wert

/-- The measure of a call-graph rank: constant per name, ordered by `<` on `Nat`. -/
def MassU.rang (rk : String → Nat) : MassU where
  Wert := Nat
  lt := fun a b => a < b
  wf := Nat.lt_wfRel.wf
  mass := fun n _ => rk n

/-- The callee hypotheses under a bound: the contract of `g` only on entry states `t` with
    `unter g t`, the frame everywhere. -/
def hypsM (u : UProg) (wf : Gabbro.Body.State → Prop) (ρ : Gabbro.Body.Env)
    (unter : String → Gabbro.Body.State → Prop) : List String → Prop → Prop
  | [], c => c
  | g :: gs, c =>
      match fnSuch u g with
      | some gf =>
          Gabbro.Body.Contract ρ g (fun t => unter g t ∧ preProp wf gf t)
            (fun s s' r => (postU u wf gf s s' r).getD False) →
          Gabbro.Body.Frame ρ g (writesU gf) → hypsM u wf ρ unter gs c
      | none => False

/-- **`meets` under a measure**: from every well-formed entry `s` satisfying the precondition,
    the body ends with the promise, assuming each callee's contract only strictly below the
    entry value `M.mass f.name s`. -/
def meetsUM (u : UProg) (wf : Gabbro.Body.State → Prop) (M : MassU) (f : UFn)
    (body : List Gabbro.Body.Stmt) : Prop :=
  ∀ (ρ : Gabbro.Body.Env) (s : Gabbro.Body.State), wf s →
    Gabbro.Body.eval s (preExpr f) = some (.bool true) →
    hypsM u wf ρ (fun g t => M.lt (M.mass g t) (M.mass f.name s)) (calleesOf f)
      (∃ s', Gabbro.Body.finalState (Gabbro.Body.exec ρ body s) = some s' ∧
        (postU u wf f s s' (Gabbro.Body.finalValue (Gabbro.Body.exec ρ body s))).getD False)

/-- The duties of the carried functions, under one measure for the whole unit. -/
def MassPflichtU (u : UProg) (C : Fin u.fns.length → Prop) (M : MassU) : Prop :=
  ∀ c : Fin u.fns.length, C c → ∃ body, zuBodyZ u (fnAt u c) = some body ∧
    meetsUM u (wfU u) M (fnAt u c) body

variable {u : UProg}

/-- Discharging the bounded hypotheses from bounded contracts and frames. -/
theorem hypsM_elim (wf : Gabbro.Body.State → Prop) (ρ : Gabbro.Body.Env)
    (unter : String → Gabbro.Body.State → Prop) : ∀ (gs : List String) (c : Prop),
    (∀ g ∈ gs, ∃ gf, fnSuch u g = some gf ∧
      Gabbro.Body.Contract ρ g (fun t => unter g t ∧ preProp wf gf t)
        (fun s s' r => (postU u wf gf s s' r).getD False) ∧
      Gabbro.Body.Frame ρ g (writesU gf)) → hypsM u wf ρ unter gs c → c
  | [], _, _, h => h
  | g :: gs, c, hg, h => by
      obtain ⟨gf, hgf, hc, hfr⟩ := hg g (List.mem_cons_self ..)
      simp only [hypsM, hgf] at h
      exact hypsM_elim wf ρ unter gs c (fun g' hm => hg g' (List.mem_cons_of_mem _ hm)) (h hc hfr)

/-- A full contract is a bounded one, for every bound. -/
theorem contract_unter {ρ : Gabbro.Body.Env} {g : String} {pre : Gabbro.Body.State → Prop}
    {post : Gabbro.Body.State → Gabbro.Body.State → Option Gabbro.Body.Value → Prop}
    (unter : Gabbro.Body.State → Prop) (h : Gabbro.Body.Contract ρ g pre post) :
    Gabbro.Body.Contract ρ g (fun t => unter t ∧ pre t) post :=
  fun t ht => h t ht.2

/-- Where the bound holds on every state of every callee, the full hypotheses give the
    bounded ones. -/
theorem hypsM_of_hyps (wf : Gabbro.Body.State → Prop) (ρ : Gabbro.Body.Env)
    (unter : String → Gabbro.Body.State → Prop) : ∀ (gs : List String) (c : Prop),
    (∀ g ∈ gs, ∀ t, unter g t) → hyps u wf ρ gs c → hypsM u wf ρ unter gs c
  | [], _, _, h => h
  | g :: gs, c, hall, h => by
      cases hgf : fnSuch u g with
      | none => simp only [hyps, hgf] at h
      | some gf =>
        simp only [hyps, hgf] at h
        simp only [hypsM, hgf]
        intro hc hfr
        exact hypsM_of_hyps wf ρ unter gs c (fun g' hm => hall g' (List.mem_cons_of_mem _ hm))
          (h (fun t ht => hc t ⟨hall g (List.mem_cons_self ..) t, ht⟩) hfr)

/-- **An acyclic duty is a measure duty**: under a rank, the call-graph rank is a measure
    whose bound holds on every callee entry. -/
theorem meetsUM_of_rang {rk : String → Nat} (hR : Rang u rk) (wf : Gabbro.Body.State → Prop)
    (c : Fin u.fns.length) {body : List Gabbro.Body.Stmt}
    (h : meetsU u wf (fnAt u c) body) : meetsUM u wf (MassU.rang rk) (fnAt u c) body := by
  intro ρ s hs hpre
  apply hypsM_of_hyps wf ρ _ (calleesOf (fnAt u c)) _ _ (h ρ s hs hpre)
  intro g hg t
  obtain ⟨args, hm⟩ := mem_calleesOf hg
  exact hR c g args hm

/-- The rank duties of an acyclic unit, as measure duties. -/
theorem massPflichtU_of_rang {C : Fin u.fns.length → Prop} {rk : String → Nat} (hR : Rang u rk)
    (hZ : ∀ c : Fin u.fns.length, C c → ∃ body, zuBodyZ u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body) : MassPflichtU u C (MassU.rang rk) := by
  intro c hc
  obtain ⟨body, hb, hm⟩ := hZ c hc
  exact ⟨body, hb, meetsUM_of_rang hR (wfU u) c hm⟩

end Gabbro.Bruecke
