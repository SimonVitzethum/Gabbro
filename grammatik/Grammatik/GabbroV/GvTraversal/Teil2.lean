module

public import Grammatik.Kern.Semantik.Semantik
public import Grammatik.GabbroV.GvTraversal.Teil1

@[expose] public section

namespace Gabbro.Grammatik.GabbroV.GvTraversal
open Gabbro.Grammatik
variable {D : Deklaration} {V : Vertrag D} {τ : Ty} {Γ : Ctx} {l : Bool}

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

/-- The middle member is scheduled. -/
theorem trav_schedule_vollstaendig_zeuge : gz1 ∈ alleIndizes 3 := by
  rw [gvKs_eq]
  exact List.mem_cons_of_mem _ (List.mem_cons_self ..)

/-- Positions `0` and `2` are valid and hold different indices. -/
theorem trav_schedule_injektiv_zeuge :
    ((alleIndizes 3)[0]).n = 0 ∧ ((alleIndizes 3)[0]).n ≠ ((alleIndizes 3)[2]).n := by
  have hi : 0 < (alleIndizes 3).length := by rw [gvKs_eq]; show (0 : Nat) < 3; omega
  have hj : 2 < (alleIndizes 3).length := by rw [gvKs_eq]; show (2 : Nat) < 3; omega
  refine ⟨by simpa using alleIndizes_get 3 0 hi, ?_⟩
  intro hcon
  have e0 := alleIndizes_get 3 0 hi
  have e2 := alleIndizes_get 3 2 hj
  omega

/-- The last member is in range. -/
theorem trav_schedule_bereich_zeuge : gz2.n.toNat < (3 : Int).toNat := by
  have hmem : gz2 ∈ alleIndizes 3 := by
    rw [gvKs_eq]
    exact List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  exact trav_schedule_bereich 3 gz2 hmem

/-- The positive run: three writing passes, each with a trace, covering
    the schedule. -/
theorem trav_ohne_verlasse_deckt_zeuge :
    (∃ (besucht : List (Wert gvD (Ty.index 3))) (aus : Ausgang gvV true []),
      WeiterSpur gvSchrittPos gvInv (alleIndizes 3) gvW0 Env.nil besucht aus ∧
      besucht = alleIndizes 3 ∧
      traverseLauf gvSchrittPos gvInv (alleIndizes 3) gvW0 Env.nil = aus)
    ∧ (gvW0.schreibSlot () [] gz0.n () ⟨7, by omega, by omega⟩).spur.length = 1 ∧
      gvW0.spur.length = 0 := by
  refine ⟨?_, rfl, rfl⟩
  apply trav_ohne_verlasse_weiter
  · intro σ ρ
    rfl
  · intro k σ ρ hkm
    -- `hkm` is unused because `gvSchrittPos` continues on every
    -- index, not only on domain members; the membership is still
    -- proved (as `trav_schedule_vollstaendig_zeuge` shows).
    exact Or.inl ⟨_, _, rfl⟩

/-- Faithful ghost for the positive run. -/
theorem trav_lauf_hat_spur_zeuge :
    ∃ (besucht : List (Wert gvD (Ty.index 3))) (aus : Ausgang gvV true []),
      LaufSpur gvSchrittPos gvInv (alleIndizes 3) gvW0 Env.nil besucht aus ∧
      traverseLauf gvSchrittPos gvInv (alleIndizes 3) gvW0 Env.nil = aus := by
  obtain ⟨besucht, aus, hspur, heq1, heq2⟩ :=
    trav_ohne_verlasse_weiter gvSchrittPos gvInv (alleIndizes 3) gvW0 Env.nil
      (fun σ ρ => rfl) (fun k σ ρ hkm => Or.inl ⟨_, _, rfl⟩)
  exact ⟨besucht, aus, weiter_zu_lauf _ _ _ _ _ _ _ hspur, heq2⟩

/-- The poison: one writing pass, then `leave`; the third member is
    scheduled but never visited. The visited log is still within the
    schedule. -/
theorem trav_spur_luecke_zeuge :
    ∃ (besucht : List (Wert gvD (Ty.index 3))) (aus : Ausgang gvV true []),
      LaufSpur gvSchrittLeave gvInv (alleIndizes 3) gvW0 Env.nil besucht aus ∧
      (∀ x ∈ besucht, x ∈ alleIndizes 3) ∧ gz2 ∈ alleIndizes 3 ∧ gz2 ∉ besucht := by
  have hs0 : gvSchrittLeave gvW0 (Env.cons gz0 Env.nil) =
      .ok (gvW0.schreibSlot () [] gz0.n () ⟨7, by omega, by omega⟩)
        (Env.cons gz0 Env.nil) := rfl
  have hs1 : ∀ σ', gvSchrittLeave σ' (Env.cons gz1 Env.nil) =
      .leave rfl σ' (Env.cons gz1 Env.nil) := fun σ' => rfl
  have hrest : ∀ σ', LaufSpur gvSchrittLeave gvInv [gz1, gz2] σ' Env.nil [gz1]
      (.ok σ' Env.nil) :=
    fun σ' => @LaufSpur.verlassOk gvD gvV (Ty.index 3) [] true gvSchrittLeave gvInv
      gz1 [gz2] σ' Env.nil rfl σ' (Env.cons gz1 Env.nil) rfl (hs1 σ') rfl
  have hspur : LaufSpur gvSchrittLeave gvInv [gz0, gz1, gz2] gvW0 Env.nil [gz0, gz1]
      (.ok (gvW0.schreibSlot () [] gz0.n () ⟨7, by omega, by omega⟩) Env.nil) :=
    @LaufSpur.weiterOk gvD gvV (Ty.index 3) [] true gvSchrittLeave gvInv
      gz0 [gz1, gz2] gvW0 Env.nil
      (gvW0.schreibSlot () [] gz0.n () ⟨7, by omega, by omega⟩) (Env.cons gz0 Env.nil)
      [gz1]
      (.ok (gvW0.schreibSlot () [] gz0.n () ⟨7, by omega, by omega⟩) Env.nil)
      rfl hs0
      (hrest (gvW0.schreibSlot () [] gz0.n () ⟨7, by omega, by omega⟩))
  have hmem2 : gz2 ∈ alleIndizes 3 := by
    rw [gvKs_eq]
    exact List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hsub : ∀ x ∈ [gz0, gz1], x ∈ alleIndizes 3 := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · rw [gvKs_eq]
      exact List.mem_cons_self ..
    · rcases List.mem_cons.mp hx' with rfl | hx''
      · rw [gvKs_eq]
        exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
      · cases hx''
  have hgap : gz2 ∉ [gz0, gz1] := by
    intro hmem
    rcases List.mem_cons.mp hmem with hEq | hmem'
    · have hc0 : gz2.n = gz0.n := congrArg Zahl.n hEq
      have e0 : gz0.n = 0 := rfl
      have e2 : gz2.n = 2 := rfl
      omega
    · rcases List.mem_cons.mp hmem' with hEq | hmem''
      · have hc1 : gz2.n = gz1.n := congrArg Zahl.n hEq
        have e1 : gz1.n = 1 := rfl
        have e2 : gz2.n = 2 := rfl
        omega
      · cases hmem''
  have hP : LaufSpur gvSchrittLeave gvInv (alleIndizes 3) gvW0 Env.nil [gz0, gz1]
      (@Ausgang.ok gvD gvV [] true
        (gvW0.schreibSlot () [] gz0.n () ⟨7, by omega, by omega⟩) Env.nil) := by
    rw [gvKs_eq]
    exact hspur
  exact ⟨[gz0, gz1], _, hP, hsub, hmem2, hgap⟩

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
#print axioms trav_schedule_vollstaendig_zeuge
#print axioms trav_schedule_injektiv_zeuge
#print axioms trav_schedule_bereich_zeuge
#print axioms trav_ohne_verlasse_deckt_zeuge
#print axioms trav_lauf_hat_spur_zeuge
#print axioms trav_spur_luecke_zeuge
