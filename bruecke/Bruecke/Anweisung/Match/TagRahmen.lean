module
public import Bruecke.Anweisung.Match.TagLesen
public import Bruecke.Anweisung.Match.ReasonRahmen
@[expose] public section
namespace Gabbro.Bruecke

theorem tag_frame {ρB : Gabbro.Body.Env} {puts : List String}
    {e : Gabbro.Body.Expr} {arms : List (String × List Gabbro.Body.Stmt)}
    (hA : ∀ arm ∈ arms, Statisch ρB puts arm.2) :
    ∀ t s', Gabbro.Body.finalState (Gabbro.Body.step ρB (.onTag e (tagArms arms)) t) = some s' →
      ∀ p, p.carrier ∉ puts → s'.world p = t.world p := by
  intro t s' h
  simp only [Gabbro.Body.step] at h
  split at h
  · rw [pickTag_bare] at h
    exact reason_pick_frame arms hA _ t s' h
  · cases h

end Gabbro.Bruecke
