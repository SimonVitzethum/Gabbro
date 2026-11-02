/- Part 11 of `FremdRuf` (C08): the grant-history ghost preservation.

   The grant history is a separate ghost relation over runs (lead decision,
   2026-11-02): no positional field in `RufMaschineG`, nothing emitted. What
   the machine steps must preserve is stated here at the ghost level, reusing
   the step judgment (`ProviderSchritt`, T6) and the binding promise
   (`ProviderBindung`, T6):

   * a linked canonical step extends a realized history (`providerOk_schritt`);
   * spawn starts empty (`granthistorie_start`: the empty history is realized
     under the binding promise);
   * a linked canonical record extends a linked history (`granthistorie_schritt`);
   * linked histories concatenate (`granthistorie_anhang`: the link case);
   * every history linked under the promise is pairwise-disjoint live
     (`granthistorie_treu`: the `ProviderTreueG` goal leg).

   The ghost is oracle-level: records tie to `O.wirkt`, never to `Tg`, spawn
   tables or machine positions, so the same `H` serves G and GX, and
   non-boundary steps preserve it by leaving `H` unchanged. The run-level
   induction (each foreign step appends exactly its record; other steps keep
   `H`) is a premise for the lead's integration over the machine steps. -/
module

public import Grammatik.Logik.Ruf.FremdRuf.T6

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- A realized history extends by one linked step meeting its step judgment:
    ghost preservation for a foreign step (other steps keep `H`). -/
theorem providerRealisiert_schritt {O : Orakel D} {H : List (BoundaryRecord D)}
    {r : BoundaryRecord D} (link : RecordGebunden O r) {inv : List (Konzession D)}
    (hinv : ProviderOk O inv H) (hs : ProviderSchritt inv r) :
    ProviderRealisiert O (H ++ [r]) :=
  ⟨_, providerOk_schritt hinv link hs⟩

/-- Spawn base: under the binding promise the empty history is realized. -/
theorem granthistorie_start {O : Orakel D} {Kan : BoundaryRecord D → Prop}
    (hb : ProviderBindung O Kan) : ProviderRealisiert O [] :=
  providerRealisiert_aus_bindung hb [] (fun r hr => absurd hr List.not_mem_nil)

/-- A linked canonical record extends a linked history: the single-step link. -/
theorem granthistorie_schritt {O : Orakel D} {Kan : BoundaryRecord D → Prop}
    (hb : ProviderBindung O Kan) {H : List (BoundaryRecord D)}
    (hg : ∀ r ∈ H, RecordGebunden O r ∧ Kan r) {r : BoundaryRecord D}
    (hr : RecordGebunden O r ∧ Kan r) : ProviderRealisiert O (H ++ [r]) :=
  providerRealisiert_aus_bindung hb (H ++ [r]) (by
    intro s hs
    simp only [List.mem_append, List.mem_singleton] at hs
    rcases hs with h | h
    · exact hg s h
    · subst h
      exact hr)

/-- Linked histories concatenate: the link case for composed runs. -/
theorem granthistorie_anhang {O : Orakel D} {Kan : BoundaryRecord D → Prop}
    (hb : ProviderBindung O Kan) {H1 H2 : List (BoundaryRecord D)}
    (hg1 : ∀ r ∈ H1, RecordGebunden O r ∧ Kan r)
    (hg2 : ∀ r ∈ H2, RecordGebunden O r ∧ Kan r) :
    ProviderRealisiert O (H1 ++ H2) :=
  providerRealisiert_aus_bindung hb (H1 ++ H2) (by
    intro s hs
    simp only [List.mem_append] at hs
    rcases hs with h | h
    · exact hg1 s h
    · exact hg2 s h)

/-- Every history linked under the promise is pairwise-disjoint live: the
    `ProviderTreueG` goal leg from the binding promise. -/
theorem granthistorie_treu {O : Orakel D} {Kan : BoundaryRecord D → Prop}
    (hb : ProviderBindung O Kan) {H : List (BoundaryRecord D)}
    (hg : ∀ r ∈ H, RecordGebunden O r ∧ Kan r) : ProviderTreueG O H :=
  providerTreueG_aus_bindung hb hg

end Gabbro.Grammatik
