/-
  File:      core/Core/Speicher/GraphmaschineErfuellbar.lean
  Subject:   SATISFIABILITY of the graph machine's premise bundle (AGENTS.md §3): the premises of
             `Zustand.erzeugt` hold jointly for the message-passing graph of `Erfuellbar.lean`
             (initial writes, thread 1 `x := 1; y.sc := 1`, thread 2 reads `y = 1`, then `x = 1`),
             so the machine reaches a state that is that graph (`graphmaschine_erfuellbar`).
-/
module

public import Core.Speicher.GraphmaschineVollstaendig
public import Core.Speicher.Erfuellbar

@[expose] public section

namespace Gabbro.Core.Speicher

open MpEv

/-- The threads of the message-passing graph: the initial writes, thread 1, thread 2. -/
def mpFaden : MpEv → Nat
  | ix => 0
  | iy => 0
  | wx => 1
  | wy => 1
  | ry => 2
  | rx => 2

instance : Finite MpEv :=
  Finite.of_injective (fun e => (⟨mpRang e, by cases e <;> decide⟩ : Fin 6))
    (fun a b h => by
      have h' : mpRang a = mpRang b := congrArg Fin.val h
      cases a <;> cases b <;> first | rfl | exact absurd h' (by decide))

/-- Both reads of the message-passing graph have a source. -/
theorem mp_vollstaendig : mpGraph.Vollstaendig := by
  intro r hr
  cases r with
  | ix => exact (hr : False).elim
  | iy => exact (hr : False).elim
  | wx => exact (hr : False).elim
  | wy => exact (hr : False).elim
  | ry => exact ⟨wy, Or.inl ⟨rfl, rfl⟩⟩
  | rx => exact ⟨wx, Or.inr ⟨rfl, rfl⟩⟩

/-- The events of one thread are ordered by program order. -/
theorem mp_faden_po (a b : MpEv) (h : mpFaden a = mpFaden b) (hne : a ≠ b) :
    mpGraph.po a b ∨ mpGraph.po b a := by
  cases a <;> cases b <;> first
    | exact absurd rfl hne
    | exact absurd h (by decide)
    | exact Or.inl (Or.inl ⟨rfl, by decide⟩)
    | exact Or.inr (Or.inl ⟨rfl, by decide⟩)
    | exact Or.inl (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    | exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    | exact Or.inl (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
    | exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))

/-- **The premises of the machine's completeness hold jointly**, and the machine reaches the
    message-passing graph with a plain carrier, a `seq_cst` flag and two reads-from edges. -/
theorem graphmaschine_erfuellbar : Zustand.Erzeugt mpGraph mpFaden :=
  Zustand.erzeugt mpGraph mpFaden mp_konsistent mp_vollstaendig mp_faden_po

end Gabbro.Core.Speicher
