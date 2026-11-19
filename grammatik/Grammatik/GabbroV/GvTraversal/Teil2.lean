module

public import Grammatik.Kern.Semantik.Semantik
public import Grammatik.GabbroV.GvTraversal.Teil1

@[expose] public section

namespace Gabbro.Grammatik.GabbroV.GvTraversal
open Gabbro.Grammatik
variable {D : Deklaration} {V : Vertrag D} {τ : Ty} {Γ : Ctx} {l : Bool}

/-- The invariant holds at every boundary; the world passes through. -/
def gvInv : World gvD → Env gvD [] → World gvD × Bool :=
  fun σ _ => (σ, true)

/-- Every pass writes its index into its slot and continues. -/
def gvSchrittPos :
    World gvD → Env gvD (Ty.index 3 :: []) → Ausgang gvV true (Ty.index 3 :: [])
  | σ, Env.cons k ρ' =>
    .ok (σ.schreibSlot () [] k.n () ⟨7, by omega, by omega⟩) (Env.cons k ρ')

/-- The first pass writes slot `0` and continues; every later pass leaves. -/
def gvSchrittLeave :
    World gvD → Env gvD (Ty.index 3 :: []) → Ausgang gvV true (Ty.index 3 :: [])
  | σ, Env.cons k ρ' =>
    if k.n = 0 then
      .ok (σ.schreibSlot () [] k.n () ⟨7, by omega, by omega⟩) (Env.cons k ρ')
    else .leave rfl σ (Env.cons k ρ')

/-! ## CUTS

    Proved: the visit schedule of `Stmt.traverse` is exactly its
    domain — every member scheduled (`trav_schedule_vollstaendig`),
    none twice (`trav_schedule_injektiv`), every scheduled index in
    range (`trav_schedule_bereich`) — and a run whose every pass
    continues visits every member (`trav_ohne_verlasse_weiter` over
    the leave-free ghost `WeiterSpur`), with every run owning a
    faithful ghost (`trav_lauf_hat_spur`) whose log stays inside the
    schedule (`trav_spur_besucht_im_plan`). Witnesses: coverage holds
    over three writing passes, and fails with a gap at the third
    member when the second pass leaves.

    NOT proved, and stated nowhere as a theorem:
    - the (S-desc) shape `traverse … over descendants … by consuming`
      (`01`, `09`, `kapraum`): no G form (exporter LG006); its domain
      is a chain from a start slot and needs the `kette`/reachability
      form, not `alleIndizes`;
    - the all-states continuation hypothesis of
      `trav_ohne_verlasse_weiter` is stronger than needed (a per-run
      statement would quantify over reached states only);
    - the visited set as a language surface (`by unvisited` witness,
      who resets it, its cost) is a proposal in REPORT-03.md,
      not a language change;
    - no bridge to `RunsLoop*`/`NutzerPflicht`: different model
      (`programmlogik/` needs mathlib), read but not edited.
-/

#print axioms besuchtDeckt_mono
#print axioms trav_schedule_vollstaendig
#print axioms trav_schedule_injektiv
#print axioms trav_schedule_bereich
#print axioms trav_lauf_hat_spur
#print axioms trav_spur_besucht_im_plan
#print axioms weiter_besucht_voll
#print axioms trav_ohne_verlasse_weiter
#print axioms weiter_zu_lauf
