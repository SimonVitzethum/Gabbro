module

public import Grammatik.Logik.Vertraege.AxiomVertrag
public import Grammatik.Kern.Semantik.Boundary.Answer
public import Grammatik.Logik.Vertraege.Locations.Boundary.Rest

@[expose] public section

namespace Gabbro.Grammatik.Boundary

/-- An environment gate answers a word; the contract narrows it to 4096.
    The declared closed reason channel has the boundary-failure case 0. -/
def probeD : Deklaration := {
  axD with
  aerg := fun _ => some (.int 0 65535)
  agruende := fun _ => 1
  anbieter_passt := by
    intro _ _ h
    cases h
  axHerkunft := fun _ => some .hardware
  axBeleg := fun _ => some ()
}

def probeWorld : World probeD where
  slots := fun _ _ _ => ⟨0, by decide, by decide⟩
  globs := fun g => nomatch g
  spur := []

/-- The raw normal answer uses the existing fallible ABI, with tag 0 and base 2.
    The environment adds no events; `Orakel.wirkt` preserves the question trace. -/
def probeOracle (word : Int) : Orakel probeD where
  wirktL := fun _ σ _ => ({ σ with spur := [] }, word)
  regLiesL := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbarL := fun g => nomatch g

/-- The read-blind fixture keeps the entire asking world, including past reads.
    Returning that trace from `wirktL` instead would duplicate it. -/
theorem probeOracle_wirkt (word : Int) (σ : World probeD) :
    (probeOracle word).wirkt () σ .nil = (σ, word) := rfl

theorem probeOracle_wirkt_zeuge :
    (probeOracle 8192).wirkt () (probeWorld.fragt (.inl ())) .nil =
      (probeWorld.fragt (.inl ()), 8192) :=
  probeOracle_wirkt 8192 _

def probeCheck : Check probeD [.int 0 65535] [] where
  expression := .le (.var .here) (.lit 4096)
  admitted := rfl

def probeFailure : Fin (probeD.agruende ()) := ⟨0, by decide⟩

/-- Kernel computation: a type-correct 5000 fails the contract and carries the
    declared error-arm reason, rather than disappearing into a hardware stop. -/
theorem answer_5000_error_zeuge :
    (axiomAntwortSonst (probeOracle 10000) () probeWorld .nil
      probeCheck (some probeFailure)).2 = some (.inr probeFailure) := rfl

/-- Kernel computation: a fitting result at the bound passes unchanged. -/
theorem answer_4096_success_zeuge :
    (axiomAntwortSonst (probeOracle 8192) () probeWorld .nil
      probeCheck (some probeFailure)).2 = some (.inl ⟨4096, by decide, by decide⟩) := rfl

/-- Kernel computation: a result outside the declared type takes the same arm. -/
theorem answer_outside_type_error_zeuge :
    (axiomAntwortSonst (probeOracle 140000) () probeWorld .nil
      probeCheck (some probeFailure)).2 = some (.inr probeFailure) := rfl

/-- Kernel computation: an existing environment reason is forwarded unchanged. -/
theorem answer_reason_forwarded_zeuge :
    (axiomAntwortSonst (probeOracle 1) () probeWorld .nil
      probeCheck (some probeFailure)).2 = some (.inr probeFailure) := rfl

/-- The very same check is refused at a call with no declared error arm. -/
theorem answer_no_arm_refused_zeuge : callB probeCheck false = false := rfl

theorem answer_with_arm_admitted_zeuge : callB probeCheck true = true := rfl

theorem unbounded_refused_zeuge :
    (Contract.refused (D := probeD) (Γ := []) (Λ := []) .unbounded).split =
      .error .unbounded := rfl

theorem liveness_refused_zeuge :
    (Contract.refused (D := probeD) (Γ := []) (Λ := []) .liveness).split =
      .error .liveness := rfl

theorem float_exact_refused_zeuge :
    (Contract.refused (D := probeD) (Γ := []) (Λ := []) .floatExact).split =
      .error .floatExact := rfl

theorem prose_refused_zeuge :
    (Contract.refused (D := probeD) (Γ := []) (Λ := []) .prose).split =
      .error .prose := rfl

def probeContract : Contract probeD [.int 0 65535] [] :=
  .conjunction (.predicate probeCheck.expression) (.deviceInternal "device.fifo")

def probeParts : Parts probeD [.int 0 65535] [] where
  checked := {
    expression := .and probeCheck.expression .tru
    admitted := rfl
  }
  remainder := ["device.fifo"]

theorem split_correct_zeuge :
    probeContract.denote (fun _ _ _ _ => true) probeWorld probeWorld
      (.cons ⟨4096, by decide, by decide⟩ .nil) =
    (probeParts.Q_check probeWorld probeWorld (.cons ⟨4096, by decide, by decide⟩ .nil) &&
      probeParts.Q_rest (fun _ _ _ _ => true) probeWorld probeWorld
        (.cons ⟨4096, by decide, by decide⟩ .nil)) :=
  probeContract.split_correct probeParts rfl _ _ _ _

def probeContracts : ∀ a : probeD.Ax,
    Contract probeD (ErgCtx (probeD.aparams a) (probeD.aerg a)) [] :=
  fun _ => .predicate probeCheck.expression

def probeEntryParts : AxEntryParts probeD := fun _ => {
  checked := probeCheck
  remainder := []
}

theorem probe_rest : AxVertragO_rest probeEntryParts (fun _ _ _ _ _ => true)
    (probeOracle 8192) :=
  axVertragO_rest_empty _ _ _ (fun _ => rfl)

/-- The full post at a successful gate needs only the empty remainder, rather
    than a promise that the environment always meets the checked bound. -/
theorem axiomAntwortSonst_contract_zeuge :
    (probeContracts ()).denote (fun _ _ _ _ => true)
      (probeWorld.fragt (.inl ())) (probeWorld.fragt (.inl ()))
      (.cons ⟨4096, by decide, by decide⟩ .nil) = true :=
  axiomAntwortSonst_contract probeContracts probeEntryParts (fun _ _ _ _ _ => true)
    (fun _ => rfl) (probeOracle 8192) probe_rest () (by decide) probeWorld .nil
    probeFailure ⟨4096, by decide, by decide⟩ answer_4096_success_zeuge

#print axioms Gabbro.Grammatik.Boundary.Contract.split_correct
#print axioms Gabbro.Grammatik.axiomAntwortSonst_contract
#print axioms Gabbro.Grammatik.Boundary.axiomAntwortSonst_contract_zeuge

end Gabbro.Grammatik.Boundary
