module
public import Bruecke.Anweisung.Match.Rahmen
@[expose] public section
namespace Gabbro.Bruecke

theorem reason_pick_frame {ρB : Gabbro.Body.Env} {puts : List String} :
    ∀ (arms : List (String × List Gabbro.Body.Stmt)),
      (∀ arm ∈ arms, Statisch ρB puts arm.2) → ∀ label t s',
      Gabbro.Body.finalState (Gabbro.Body.pickArm ρB arms label t) = some s' →
      ∀ p, p.carrier ∉ puts → s'.world p = t.world p
  | [], _, _, _, _, h => by cases h
  | (name, body) :: arms, hA, label, t, s', h => by
    simp only [Gabbro.Body.pickArm] at h
    split at h
    · exact exec_statisch (hA _ (List.mem_cons_self ..)) t s' h
    · exact reason_pick_frame arms (fun arm hm => hA arm (List.mem_cons_of_mem _ hm)) label t s' h

theorem reason_frame {ρB : Gabbro.Body.Env} {puts : List String}
    {e : Gabbro.Body.Expr} {arms : List (String × List Gabbro.Body.Stmt)}
    (hA : ∀ arm ∈ arms, Statisch ρB puts arm.2) :
    ∀ t s', Gabbro.Body.finalState (Gabbro.Body.step ρB (.onReason e arms) t) = some s' →
      ∀ p, p.carrier ∉ puts → s'.world p = t.world p := by
  intro t s' h
  simp only [Gabbro.Body.step] at h
  split at h
  · exact reason_pick_frame arms hA _ t s' h
  · cases h

end Gabbro.Bruecke
