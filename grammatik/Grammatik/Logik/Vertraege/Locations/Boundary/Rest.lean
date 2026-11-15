module

public import Grammatik.Kern.Semantik.Semantik.T2.Teil1

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- The computed projections of each foreign contract, retaining original
    arguments and the optional normal answer in its expression context. -/
abbrev AxEntryParts (D : Deklaration) :=
  ∀ a : D.Ax, Boundary.Parts D (ErgCtx (D.aparams a) (D.aerg a)) []

/-- Per-contract interpretations of named, unobservable R3 clauses. -/
abbrev AxEntryRemainders (D : Deklaration) :=
  ∀ a : D.Ax, Boundary.Remainders D (ErgCtx (D.aparams a) (D.aerg a))

/-- Normal results of the existing scalar foreign ABI. A reason has no normal
    postcondition. With zero reasons its tag base is one, the infallible ABI. -/
def entryNormalAnswer (z : Int → Option D.Fn) (a : D.Ax) (word : Int) :
    Option (ErgVal D (D.aerg a)) :=
  (sonstPasst z (D.aerg a) (D.agruende a) word).bind fun answer =>
    match answer with
    | .inl value => some value
    | .inr _ => none

/-- The environment assumption covers only the named R3 remainder of a
    type-correct normal answer. It promises neither `Q_check` nor successful
    validation. Software items are excluded; their summaries are user logic.
    Question worlds already contain the recorded outside-call event. -/
def AxVertragO_rest (parts : AxEntryParts D) (R : AxEntryRemainders D)
    (O : Orakel D) : Prop :=
  ∀ (a : D.Ax), D.axHerkunft a ≠ some AxOrigin.software →
    ∀ (question : World D) (ρ : Env D (D.aparams a)) (v : ErgVal D (D.aerg a)),
      entryNormalAnswer O.zeiger a (O.wirkt a question ρ).2 = some v →
      (parts a).Q_rest (R a) question (O.wirkt a question ρ).1
        (ergEnv (D.aerg a) v ρ) = true

/-- A wholly executable contract requires no foreign-contract assumption. -/
theorem axVertragO_rest_empty (parts : AxEntryParts D) (R : AxEntryRemainders D)
    (O : Orakel D) (h : ∀ a, (parts a).remainder = []) : AxVertragO_rest parts R O := by
  intro a _ question ρ v _
  simp only [Boundary.Parts.Q_rest, h a, List.all_nil]

/-- At the fallible entry gate, the full written post follows from an actual
    successful check and only the named remainder assumption. A failing value
    instead becomes a reason, so this theorem never excuses its continuation. -/
theorem axiomAntwortSonst_contract (contracts : ∀ a : D.Ax,
    Boundary.Contract D (ErgCtx (D.aparams a) (D.aerg a)) [])
    (parts : AxEntryParts D) (R : AxEntryRemainders D)
    (hSplit : ∀ a, (contracts a).split = .ok (parts a))
    (O : Orakel D) (hR : AxVertragO_rest parts R O)
    (a : D.Ax) (environment : D.axHerkunft a ≠ some AxOrigin.software)
    (σ : World D) (ρ : Env D (D.aparams a))
    (failure : Fin (D.agruende a)) (v : ErgVal D (D.aerg a))
    (accepted : (axiomAntwortSonst O a σ ρ (parts a).checked (some failure)).2 =
      some (.inl v)) :
    (contracts a).denote (R a) (σ.fragt (.inl a))
      (O.wirkt a (σ.fragt (.inl a)) ρ).1 (ergEnv (D.aerg a) v ρ) = true := by
  simp only [axiomAntwortSonst, Option.isSome_some, Bool.or_true, ↓reduceIte] at accepted
  obtain ⟨decoded, checked⟩ := Boundary.gate_success _ _ _ v accepted
  have normal : entryNormalAnswer O.zeiger a
      (O.wirkt a (σ.fragt (.inl a)) ρ).2 = some v := by
    unfold entryNormalAnswer
    rw [decoded]
    rfl
  exact (contracts a).of_checked_and_rest (parts a) (hSplit a) (R a)
    (σ.fragt (.inl a)) _ (ergEnv (D.aerg a) v ρ) checked
    (hR a environment (σ.fragt (.inl a)) ρ v normal)

end Gabbro.Grammatik
