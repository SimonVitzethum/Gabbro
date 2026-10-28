/-
  File:      Grammatik/Adaequanz/Baum.lean
  Subject:   ADEQUACY OF A TEST SET (TODO Phase C item 8) -- the abstract setting.

             A ranked signature `Sig` (constructor labels with arities), its trees `Baum`, one-hole contexts
             `Kontext`, and a deterministic bottom-up finite tree automaton with output (`Automat`): a state per
             constructor and tuple of child states, an output per state. This is the class of PROGRAM-NEUTRAL
             implementations: the result on a term is a function of the constructor and of the results on the
             immediate subterms, through a state of a fixed type (finite when `Fintype`). A top-down context
             (held locks, loop flag, contract) with finitely many values is covered too: the state of a subtree
             is then the function from the inherited context to the synthesized result (attribute grammars with
             finite domains are tree automata).

             The spec (the Lean model's verdict, or its semantics) is an `Automat` as well; the question of the
             test set is when an implementation `I` that agrees with the spec `S` on finitely many trees agrees
             on all (`Hinlaenglich.lean`), and why no smaller set does (`Minimal.lean`).

  The run over a context depends on the plugged tree only through its state (`lauf_ein`): the one fact
  every argument below uses.
-/
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Fin

namespace Gabbro.Grammatik.Adaequanz

/-- A ranked signature: constructor labels and their arities. -/
structure Sig where
  K : Type
  ar : K → Nat

variable {σ : Sig}

/-- The trees over a signature: a constructor and one child per argument position. -/
inductive Baum (σ : Sig) where
  | knoten (k : σ.K) (kinder : Fin (σ.ar k) → Baum σ)

/-- A one-hole context: the hole, or a constructor whose child `i` is a context and whose other children
    are trees (`rest i` is ignored). -/
inductive Kontext (σ : Sig) where
  | loch
  | knoten (k : σ.K) (i : Fin (σ.ar k)) (rest : Fin (σ.ar k) → Baum σ) (K : Kontext σ)

/-- Plug a tree into the hole. -/
def Kontext.ein : Kontext σ → Baum σ → Baum σ
  | .loch, t => t
  | .knoten k i rest K, t => .knoten k (Function.update rest i (K.ein t))

/-- **A deterministic bottom-up tree automaton with output**: the state of a node is a function of its
    constructor and its children's states; the result of a tree is the output of its state. -/
structure Automat (σ : Sig) (Q O : Type) where
  δ : (k : σ.K) → (Fin (σ.ar k) → Q) → Q
  aus : Q → O

namespace Automat

variable {Q O : Type} (A : Automat σ Q O)

/-- The state of a tree. -/
def lauf : Baum σ → Q
  | .knoten k ch => A.δ k (fun i => lauf (ch i))

/-- The result of a tree. -/
def sem (t : Baum σ) : O := A.aus (A.lauf t)

/-- The state at the root of a context whose hole has state `q`. -/
def laufK : Kontext σ → Q → Q
  | .loch, q => q
  | .knoten k i rest K, q => A.δ k (Function.update (fun j => A.lauf (rest j)) i (laufK K q))

/-- The result of a context whose hole has state `q`. -/
def semK (K : Kontext σ) (q : Q) : O := A.aus (A.laufK K q)

theorem lauf_knoten (k : σ.K) (ch : Fin (σ.ar k) → Baum σ) :
    A.lauf (.knoten k ch) = A.δ k (fun i => A.lauf (ch i)) := rfl

/-- **The run over a context depends on the plugged tree only through its state.** -/
theorem lauf_ein (K : Kontext σ) (t : Baum σ) : A.lauf (K.ein t) = A.laufK K (A.lauf t) := by
  induction K with
  | loch => rfl
  | knoten k i rest K ih =>
      simp only [Kontext.ein, lauf_knoten, laufK]
      congr 1
      funext j
      by_cases h : j = i
      · subst h; simp only [Function.update_self, ih]
      · simp only [Function.update_of_ne h]

theorem sem_ein (K : Kontext σ) (t : Baum σ) : A.sem (K.ein t) = A.semK K (A.lauf t) := by
  simp only [sem, lauf_ein, semK]

end Automat

end Gabbro.Grammatik.Adaequanz
