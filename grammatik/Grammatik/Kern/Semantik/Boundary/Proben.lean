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

def probeCheck : Check probeD [.int 0 65535] [] where
  expression := .le (.var .here) (.lit 4096)
  admitted := rfl

def probeFailure : Fin (probeD.agruende ()) := ⟨0, by decide⟩

/-- Kernel computation: a fitting result at the bound passes unchanged. -/
theorem answer_4096_success_zeuge :
    (axiomAntwortSonst (probeOracle 8192) () probeWorld .nil
      probeCheck (some probeFailure)).2 = some (.inl ⟨4096, by decide, by decide⟩) := rfl

def probeContract : Contract probeD [.int 0 65535] [] :=
  .conjunction (.predicate probeCheck.expression) (.deviceInternal "device.fifo")

def probeParts : Parts probeD [.int 0 65535] [] where
  checked := {
    expression := .and probeCheck.expression .tru
    admitted := rfl
  }
  remainder := ["device.fifo"]

def probeAnswer : Env probeD [.int 0 65535] :=
  .cons ⟨4096, by decide, by decide⟩ .nil

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

#print axioms Gabbro.Grammatik.Boundary.Contract.split_correct
#print axioms Gabbro.Grammatik.axiomAntwortSonst_contract

end Gabbro.Grammatik.Boundary
