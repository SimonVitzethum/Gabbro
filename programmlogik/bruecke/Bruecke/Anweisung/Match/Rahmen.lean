module
public import Bruecke.Anweisung.Zweig.Rahmen
@[expose] public section

namespace Gabbro.Bruecke

theorem option_frame {ρB : Gabbro.Body.Env} {puts : List String}
    {e : Gabbro.Body.Expr} {x : String} {pb ab : List Gabbro.Body.Stmt}
    (hp : Statisch ρB puts pb) (ha : Statisch ρB puts ab) :
    ∀ t s', Gabbro.Body.finalState (Gabbro.Body.step ρB (.onOption e x pb ab) t) = some s' →
      ∀ p, p.carrier ∉ puts → s'.world p = t.world p := by
  intro t s' h p hnp
  simp only [Gabbro.Body.step] at h
  split at h
  · exact exec_statisch hp _ s' h p hnp
  · exact exec_statisch ha t s' h p hnp
  · cases h

end Gabbro.Bruecke
