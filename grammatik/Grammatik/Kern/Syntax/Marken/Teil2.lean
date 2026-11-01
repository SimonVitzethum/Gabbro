module

public import Grammatik.Kern.Syntax.Marken.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Marken

/-! ## 8. The trace link, run through the Verlauf -- from outcomes to `Einfaedig`

    Section 7 closes W4 against `Einfaedig` assumed over a run; `Wettlauf.lean`
    section 8 closes it against `verlauf_einfaedig` plus `SpurLink` -- every
    projected event names only what its thread owns at one shared reachable
    stand. What neither closes is the run BEHIND the stand: which runs are
    carried by a `Verlauf`, and how that carried-ness is built step by step.
    This section is that link, in mirror (no index entry, no import -- the
    sibling is not read from here, same direction as ever).

    `Getragen` is the mirror of `SpurLink`: every mark an event names is owned
    by that event's thread at the stand. `verlauf_aus_lauf` is the link: a run
    carried by the final stand of a `Verlauf` satisfies `Einfaedig`, through
    `verlauf_einfaedig`. The step lemmas say how carried-ness is BUILT: the
    empty run is carried everywhere; appending an event that names only owned
    marks keeps it carried; extending the `Verlauf` by a step on a mark the run
    never names (`Unbenannt`) keeps it carried -- `belebe_anders` and
    `loesche_anders` move ownership nowhere else.

    NARROWING (proved, stated): the carried class is single-generation. A step
    that frees or retakes a mark the run NAMES (`verbrauche` or `erzeuge` on a
    named mark) ends carried-ness: the old event names an owner the new stand
    no longer has, or a new owner the old event never met. The three `weiter`
    lemmas take `Unbenannt` exactly there -- reuse across threads is excluded
    by hypothesis, not by construction.

    NOT the narrowing: race-freedom through `kein_wettlauf`. That theorem
    CONSUMES W4 (`marke_eindeutig` in the mark-guard case, `Wettlauf.lean`), so
    narrowing W4 by it would be circular. What `kein_wettlauf` needs from W4,
    this section supplies for carried runs -- the arrow points the other way.

    HONEST REMAINDER: `Getragen` itself. `exec` runs `advances` and `retires`
    as world no-ops (`.ok`, `Semantik.lean`), so no sentence in this cone can
    READ a `Verlauf` off an `exec` outcome -- the dynamic ownership the link
    reads is not in the world. The `Verlauf` travels alongside the run (its
    step shapes mirror the static context discipline of `Stmt.advances` and
    `Stmt.retires`, `Syntax.lean`); that the real projection IS carried at one
    shared stand is the residual premise, already named `SpurLink` in
    `Wettlauf.lean` section 8.

    APPLY SITE (statement-level, `Wettlauf.lean` untouched): `verlauf_aus_lauf`
    concludes `Einfaedig l`, which at `l := laufProj code run` is exactly the
    `hEin` argument of `bruecke_exec_gesittet` (`Wettlauf.lean`) and the
    `einfaedig` field of `ExecEng` (`Ziel.lean`). The wiring is a one-line
    `exact` at the use site and is deliberately not edited here. -/

/-- A run carried by a stand: every mark an event names is owned by that
    event's thread at `σ`. The mirror of `SpurLink` (`Wettlauf.lean` section 8)
    over the mirror run -- same shape, no index entry, so it stands here
    without importing its sibling. -/
def Getragen (σ : Stand) (l : Lauf) : Prop :=
  ∀ (i : Nat) (f : Faden) (ei : Ereignis),
    l[i]? = some (Schritt.mk f ei) →
    ∀ (m : Marke) (s : Nat), Res.marke m s ∈ ei.lambda → Besitzt σ f m

/-- A mark untouched by a run: no event names it, at any stage. The frame the
    three `weiter` lemmas read. -/
def Unbenannt (m : Marke) (l : Lauf) : Prop :=
  ∀ (i : Nat) (f : Faden) (ei : Ereignis),
    l[i]? = some (Schritt.mk f ei) →
    ∀ (s : Nat), Res.marke m s ∉ ei.lambda

/-- The empty run is carried everywhere: no event, no owner owed. -/
theorem getragen_leer (σ : Stand) : Getragen σ [] := by
  intro i f ei hi m s hm
  simp only [List.length_nil, Nat.not_lt_zero, not_false_eq_true, getElem?_neg, reduceCtorEq] at hi

/-- Appending an event that names only owned marks keeps the run carried. -/
theorem getragen_cons (σ : Stand) (q : Schritt) (l : Lauf)
    (hq : ∀ (m : Marke) (s : Nat),
      Res.marke m s ∈ q.ereignis.lambda → Besitzt σ q.faden m)
    (hl : Getragen σ l) : Getragen σ (q :: l) := by
  intro i f ei hi m s hm
  cases i with
  | zero =>
      have h1 : q = Schritt.mk f ei := by simpa using hi
      have hf : f = q.faden := congrArg Schritt.faden h1.symm
      have he : ei = q.ereignis := congrArg Schritt.ereignis h1.symm
      rw [hf]
      exact hq m s (he ▸ hm)
  | succ i =>
      have hi' : l[i]? = some (Schritt.mk f ei) := by simpa using hi
      exact hl i f ei hi' m s hm

/-- The empty run names nothing. -/
theorem unbenannt_leer (m : Marke) : Unbenannt m [] := by
  intro i f ei hi s
  simp only [List.length_nil, Nat.not_lt_zero, not_false_eq_true, getElem?_neg, reduceCtorEq] at hi

/-- Appending an event that avoids `m` keeps `m` unnamed. -/
theorem unbenannt_cons (m : Marke) (q : Schritt) (l : Lauf)
    (hq : ∀ (s : Nat), Res.marke m s ∉ q.ereignis.lambda)
    (hl : Unbenannt m l) : Unbenannt m (q :: l) := by
  intro i f ei hi s
  cases i with
  | zero =>
      have h1 : q = Schritt.mk f ei := by simpa using hi
      have he : ei = q.ereignis := congrArg Schritt.ereignis h1.symm
      exact he ▸ hq s
  | succ i =>
      have hi' : l[i]? = some (Schritt.mk f ei) := by simpa using hi
      exact hl i f ei hi' s

/-- Creating on an unnamed mark keeps the run carried: the touched mark is
    named nowhere, and `belebe_anders` moves ownership nowhere else. -/
theorem getragen_erzeuge_unberuehrt (κ : MarkDekl) {σ : Stand}
    (m₀ : Marke) (f₀ : Faden) (s₀ : Nat)
    (_hfrei : σ m₀ = none) (_hstufe : s₀ < κ.stufen m₀)
    (_hfremd : ¬ κ.istEigner m₀)
    (l : Lauf) (hU : Unbenannt m₀ l) (hG : Getragen σ l) :
    Getragen (belebe σ m₀ f₀ s₀) l := by
  intro i f ei hi m s hm
  obtain ⟨t, ht⟩ := hG i f ei hi m s hm
  by_cases heq : m = m₀
  · subst heq
    exact absurd hm (hU i f ei hi s)
  · exact ⟨t, by rw [belebe_anders _ _ _ _ _ heq]; exact ht⟩

/-- Leading to the next stage on an unnamed mark keeps the run carried. -/
theorem getragen_fuehre_unberuehrt (κ : MarkDekl) {σ : Stand}
    (m₀ : Marke) (f₀ : Faden) (a : Nat)
    (_hbesitz : σ m₀ = some (f₀, a)) (_hstufe : a + 1 < κ.stufen m₀)
    (l : Lauf) (hU : Unbenannt m₀ l) (hG : Getragen σ l) :
    Getragen (belebe σ m₀ f₀ (a + 1)) l := by
  intro i f ei hi m s hm
  obtain ⟨t, ht⟩ := hG i f ei hi m s hm
  by_cases heq : m = m₀
  · subst heq
    exact absurd hm (hU i f ei hi s)
  · exact ⟨t, by rw [belebe_anders _ _ _ _ _ heq]; exact ht⟩

/-- Consuming an unnamed mark keeps the run carried: the freed mark is named
    nowhere, and `loesche_anders` moves ownership nowhere else. -/
theorem getragen_verbrauche_unberuehrt {σ : Stand}
    (m₀ : Marke) (f₀ : Faden) (s₀ : Nat)
    (_hbesitz : σ m₀ = some (f₀, s₀))
    (l : Lauf) (hU : Unbenannt m₀ l) (hG : Getragen σ l) :
    Getragen (loesche σ m₀) l := by
  intro i f ei hi m s hm
  obtain ⟨t, ht⟩ := hG i f ei hi m s hm
  by_cases heq : m = m₀
  · subst heq
    exact absurd hm (hU i f ei hi s)
  · exact ⟨t, by rw [loesche_anders _ _ _ heq]; exact ht⟩

/-- **The trace link, run through the Verlauf.** A run carried by the final
    stand of a `Verlauf` satisfies `Einfaedig`: both naming events owe the
    same stand an owner, and `verlauf_einfaedig` names one thread. -/
theorem verlauf_aus_lauf (κ : MarkDekl) {σ : Stand} (v : Verlauf κ σ)
    (l : Lauf) (hT : Getragen σ l) : Einfaedig l := by
  intro i j f g m s s' ei ej hi hj hmi hmj
  exact verlauf_einfaedig κ v m f g
    (hT i f ei hi m s hmi) (hT j g ej hj m s' hmj)

/-- **Corollary: the `hEin` premise, discharged for carried runs.** At
    `l := laufProj code run` this term has exactly the type of `hEin` in
    `bruecke_exec_gesittet` (`Wettlauf.lean`) and of the `einfaedig` field of
    `ExecEng` (`Ziel.lean`): `exact einfaedig_aus_verlauf_getragen κ v _ hT`
    at the use site, with `hT` the carried-ness of the projection. No edit to
    either file -- the wiring stays a use-site line. -/
theorem einfaedig_aus_verlauf_getragen (κ : MarkDekl) {σ : Stand}
    (v : Verlauf κ σ) (l : Lauf) (hT : Getragen σ l) : Einfaedig l :=
  verlauf_aus_lauf κ v l hT

#print axioms Gabbro.Grammatik.Marken.getragen_leer
#print axioms Gabbro.Grammatik.Marken.getragen_cons
#print axioms Gabbro.Grammatik.Marken.unbenannt_leer
#print axioms Gabbro.Grammatik.Marken.unbenannt_cons
#print axioms Gabbro.Grammatik.Marken.getragen_erzeuge_unberuehrt
#print axioms Gabbro.Grammatik.Marken.getragen_fuehre_unberuehrt
#print axioms Gabbro.Grammatik.Marken.getragen_verbrauche_unberuehrt
#print axioms Gabbro.Grammatik.Marken.verlauf_aus_lauf
#print axioms Gabbro.Grammatik.Marken.einfaedig_aus_verlauf_getragen

end Gabbro.Grammatik.Marken
