module

public import Grammatik.Korpus.Referenz.ReferenzB
public import Grammatik.Bausteine.Schablonen.SchablonenT5.T1.Teil1

@[expose] public section

namespace Gabbro.Grammatik

/-- Soundness of `transition.transset`: the named observer sees no
    change anywhere in the trace. `hObs` names both moved places as
    outside the footprint; `hw`/`hq` fix the world and the observed
    place. All four are consumed. -/
theorem joint_move_hidden (σ : Nat → Nat) (p1 p2 v1 v2 : Nat)
    (Obs : List Nat) (hObs : p1 ∉ Obs ∧ p2 ∉ Obs)
    (w : Nat → Nat) (hw : w ∈ jointTrace σ p1 p2 v1 v2)
    (q : Nat) (hq : q ∈ Obs) : w q = σ q := by
  have h1 : q ≠ p1 := fun he => hObs.1 (he ▸ hq)
  have h2 : q ≠ p2 := fun he => hObs.2 (he ▸ hq)
  simp only [jointTrace, List.mem_cons] at hw
  simp only [List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · rfl
  · simp only [jointMove, if_neg h1, if_neg h2]

/-- Witness for `joint_move_hidden`: moving places `0`/`1`, observer of
    place `2` sees nothing. -/
theorem joint_move_hidden_zeuge :
    ((fun _ => 0) 2 = (fun _ => (0 : Nat)) 2)
:= by
  have hObs : (0 : Nat) ∉ ([2] : List Nat) ∧ 1 ∉ ([2] : List Nat) := by
    decide
  have hw : (fun _ => (0 : Nat)) ∈ jointTrace (fun _ => 0) 0 1 7 8 := by
    simp only [jointTrace, List.mem_cons, List.not_mem_nil, or_false, true_or]
  have hq : (2 : Nat) ∈ ([2] : List Nat) := by decide
  exact joint_move_hidden _ 0 1 7 8 [2] hObs _ hw 2 hq

/-! ## 10. `exchange.rmw` (exchange: 31 corpus lines).

The body of `update(v)` is pure (mechanically, Pass 8 -- in the model
a body IS a function of the read value, so purity holds by
construction). The atomicity of the read-modify-write sequence is NOT
a template obligation but an assumption of the axiom layer. What Lean
checks is the serial content: an RMW chain applies innermost first --
the fold direction is fixed, no interleaving inside. -/

/-- An RMW chain: each body sees the previous write. -/
def runRmw : List (Nat → Nat) → Nat → Nat
  | [], σ => σ
  | f :: rest, σ => runRmw rest (f σ)

/-- Soundness core of `exchange.rmw`: the chain equals the left fold --
    bodies apply innermost first, deterministically. -/
theorem rmw_chain_order (fs : List (Nat → Nat)) (σ : Nat) :
    runRmw fs σ = fs.foldl (fun s f => f s) σ := by
  induction fs generalizing σ with
  | nil => rfl
  | cons f rest ih =>
    show runRmw rest (f σ) = rest.foldl (fun s g => g s) (f σ)
    exact ih _

/-- Witness for `rmw_chain_order`:     `[+1, *2]` from `5` gives `12`. -/
theorem rmw_chain_order_zeuge :
    (runRmw [(· + 1), (· * 2)] 5 = 12)
:= by
  have hchain := rmw_chain_order [(· + 1), (· * 2)] 5
  have hval : ([(· + 1), (· * 2)] : List (Nat → Nat)).foldl (fun s f => f s) 5 = 12 := by
    decide
  exact hchain.trans hval


end Gabbro.Grammatik
