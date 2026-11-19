module

public import Grammatik.Kern.Semantik.Boundary.Proben

@[expose] public section

namespace Gabbro.Grammatik.Boundary

/-- The same executable bound as `probeCheck`, in the raw-oracle summary
    interface shared by `AxVertragO` and C08's `AxVertragOP`. Both decode the ABI
    word before its tag is removed; the fallible machine removes the tag first. -/
def probeBound : AxEns probeD := fun _ _ value => decide (value.n ≤ 4096)

def probeAtBound : ErgVal probeD (probeD.aerg ()) :=
  ⟨4096, by decide, by decide⟩

/-- In the one-reason ABI the only normal encoding of 4096 is 8192.
    This is independent of the oracle and of any contract assumption. -/
theorem probe_at_bound_encoding (z : Int → Option probeD.Fn) (word : Int)
    (h : sonstPasst z (some (.int 0 65535)) 1 word = some (.inl probeAtBound)) :
    word = 8192 := by
  unfold sonstPasst at h
  dsimp only at h
  split at h
  · rename_i htag
    change word % 2 = 0 at htag
    change Option.map (Sum.inl (β := Fin 1))
      (einpassen z (.int 0 65535) (word / 2)) =
        some (.inl (⟨4096, by decide, by decide⟩ : Zahl 0 65535)) at h
    cases hv : einpassen z (.int 0 65535) (word / 2) with
    | none =>
        rw [hv] at h
        cases h
    | some value =>
        rw [hv] at h
        have heq : value = probeAtBound := Sum.inl.inj (Option.some.inj h)
        have hword : word / 2 = value.n := by
          simp only [einpassen] at hv
          split at hv
          · cases hv
            rfl
          · cases hv
        rw [heq] at hword
        change word / 2 = 4096 at hword
        omega
  · split at h
    · cases h
    · cases h

/-- The old class is inhabited too: the transfer failure does not depend on an
    inconsistent full contract or an empty class of permitted environments. -/
theorem probe_old_class_inhabited : AxVertragO probeBound (probeOracle 0) := by
  intro a question args value decoded
  change some (⟨0, by decide, by decide⟩ : ErgVal probeD (probeD.aerg a)) =
    some value at decoded
  cases decoded
  rfl

/-- C08 still excludes the observation at the actual question world. The pre
    is true because this fixture's item has hardware origin: `PreQ P` reduces
    to this pre for every `P`. The obstruction needs no software item or duty. -/
theorem probe_conditional_duty_excludes_bound (O : Orakel probeD)
    (hQ : AxVertragOP (fun _ _ _ => true) probeBound O) :
    (axiomAntwortSonst O () probeWorld .nil probeCheck (some probeFailure)).2 ≠
      some (.inl probeAtBound) := by
  intro accepted
  simp only [axiomAntwortSonst, Option.isSome_some, Bool.or_true, ↓reduceIte] at accepted
  obtain ⟨decoded, _⟩ := gate_success _ _ _ probeAtBound accepted
  have encoded := probe_at_bound_encoding O.zeiger
    (O.wirkt () (probeWorld.fragt (.inl ())) .nil).2 decoded
  have fits : einpassenErg O.zeiger (probeD.aerg ())
      (O.wirkt () (probeWorld.fragt (.inl ())) .nil).2 =
      some (⟨8192, by decide, by decide⟩ : ErgVal probeD (probeD.aerg ())) := by
    rw [encoded]
    rfl
  have impossible := hQ () probeWorld .nil _ rfl fits
  change false = true at impossible
  cases impossible

/-- The full-summary statement is retained unchanged for `GabbroZielVoll`.
    Its class is contained in C08's conditional class at a true pre. -/
theorem probe_old_duty_excludes_bound (O : Orakel probeD) (hQ : AxVertragO probeBound O) :
    (axiomAntwortSonst O () probeWorld .nil probeCheck (some probeFailure)).2 ≠
      some (.inl probeAtBound) :=
  probe_conditional_duty_excludes_bound O (axVertragOP_of_O _ hQ)

/-- The remainder-only class contains the concrete oracle that the gate accepts
    at 4096. Its remainder is empty; no environment promise about the bound is
    used. Thus this fixture is non-vacuous on both sides of entry validation. -/
theorem probe_rest_admits_bound :
    AxVertragO_rest probeEntryParts (fun _ _ _ _ _ => true) (probeOracle 8192) ∧
      (axiomAntwortSonst (probeOracle 8192) () probeWorld .nil
        probeCheck (some probeFailure)).2 = some (.inl probeAtBound) :=
  ⟨axVertragO_rest_empty _ _ _ (fun _ => rfl), answer_4096_success_zeuge⟩


end Gabbro.Grammatik.Boundary
