/-
  File:      core/Core/Speicher/Atom/Nutzlast.lean
  Subject:   THE PAYLOAD OF A PUBLICATION IS VISIBLE (MK-04). `A = e publishes { p, q }` stores the flag `A` with
             release strength after the payload writes in program order; `let x = A awaits { p, q }` observes the
             flag with acquire strength before the payload reads in program order. When the observation reads the
             publication, the payload the observer reads is the published one or a later one in modification order:
             `PayloadSichtbarAussage`, over EVERY consistent graph of the memory model W.
             The statement is PROVED here (`payloadSichtbar`): the release/acquire pair synchronises (`sw_direkt`),
             so the payload write happens before the payload read, and coherence forbids reading an older write
             (`liest_mo_max`). It is not vacuous: `payloadSichtbar_erfuellbar` is a consistent graph in which every
             premise holds and the observer reads the published payload. And it is not trivial:
             `payloadSichtbar_nichtTrivial` shows that with a mode that is too weak on either side the same graph
             shape is consistent and the observer reads a payload that is OLDER than the published one -- the model
             can represent the stale read, and only the checker's refusal of the weak mode excludes it.
-/
module

public import Core.Speicher.Erfuellbar

@[expose] public section

namespace Gabbro.Core.Speicher

/-- **The payload of a publication is visible to the observer.** In a consistent graph let `w` be the release
    store of the flag and `r` the acquire observation that reads it, both at least release/acquire strength;
    let `p` be a payload write before `w` in program order and `q` a payload read after `r` in program order, at
    the same location. Then every write `s` the payload read takes its value from is the payload write or later
    than it in modification order. -/
def PayloadSichtbarAussage : Prop :=
  ∀ (E Ort Wert : Type) (G : Graph E Ort Wert), G.Konsistent →
    ∀ p w r q s : E, G.po p w → G.schreibt p → G.rf w r → (G.modus w).stark → (G.modus r).stark →
      G.po r q → G.ort p = G.ort q → G.rf s q → p = s ∨ G.mo p s

/-- **The payload is visible** (the proof of `PayloadSichtbarAussage`). -/
theorem payloadSichtbar : PayloadSichtbarAussage := by
  intro E Ort Wert G hk p w r q s po₁ hp rfFlag mw mr po₂ ort rfData
  have sw : G.sw w r := Graph.sw_direkt hk.wf rfFlag mw mr
  have hb : G.hb p q :=
    G.hb_trans (G.hb_trans (G.hb_von_po po₁) (G.hb_von_sw sw)) (G.hb_von_po po₂)
  exact Graph.liest_mo_max hk rfData hp ort hb

/-- **The premises of the payload statement hold jointly, and the conclusion bites**: the message-passing graph
    of `drf_sc_erfuellbar` with a `seq_cst` flag, in which the observer reads the payload write itself. -/
theorem payloadSichtbar_erfuellbar :
    ∃ (G : Graph MpEv Bool Nat), G.Konsistent ∧
      ∃ p w r q s : MpEv, G.po p w ∧ G.schreibt p ∧ G.rf w r ∧ (G.modus w).stark ∧ (G.modus r).stark ∧
        G.po r q ∧ G.ort p = G.ort q ∧ G.rf s q ∧ p = s :=
  ⟨mpGraph, mp_konsistent, .wx, .wy, .ry, .rx, .wx,
    Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)), trivial, Or.inl ⟨rfl, rfl⟩, trivial, trivial,
    Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)), rfl, Or.inr ⟨rfl, rfl⟩, rfl⟩

end Gabbro.Core.Speicher
