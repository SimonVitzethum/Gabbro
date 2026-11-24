/-
  File:      Core/Ziel/Sicherheit.lean
  Subject:   The SHAPE of the four safety theorems beside the goal (`dokumente/PERFECT-MODEL.md` §2.2).

  The goal theorem of §2 already implies memory safety, invariant preservation, race freedom and TOCTOU freedom
  through the refinement of `I`. These four are stated AGAIN, directly over the implementation runs, as a safety
  net (owner, 2026-11-24): their definitions never mention `I`, `Sim`, `Verfeinert` or `Akzeptiert`, so a mistake
  in the ideal meaning or in the refinement cannot hide a violation of them. Like `GabbroZielForm`, this file
  fixes the shape only; M12 states `gabbro_sicherheit : GabbroSicherheitForm R₀ S₀` over the pinned concrete
  constants, and `SicherheitNichtLeer` makes each property refutable by some run, so none is trivially true.
-/
module

public import Core.Ziel.Form

@[expose] public section

namespace Gabbro.Core.Ziel

/-- The four safety properties of an implementation run (PERFECT-MODEL §2.2), each defined over the
implementation machine, the memory model and the outside rule only. -/
structure Sicherheit (R : Rahmen) where
  /-- Every memory access of the run is to an allocated, live (current generation), in-extent location through
  a handle the acting context holds with the needed right; no release of a released or foreign object. -/
  Speichersicher : R.Einheit → R.Umgebung → R.Lauf → Prop
  /-- Every declared invariant (type, lock-protected, module and loop invariants) holds at every cut at which no
  context is inside a writer of it, at every release and at every acquisition of its lock. -/
  InvariantenErhalten : R.Einheit → R.Umgebung → R.Lauf → Prop
  /-- In the run's memory graph every two conflicting accesses (same location, one a write, one non-atomic) are
  ordered by happens-before; device registers are accessed only under linear device authority. -/
  Rennfrei : R.Einheit → R.Umgebung → R.Lauf → Prop
  /-- Every outside effect the run commits is valid at its commit (`GueltigBeiCommit`) under every outside
  history the selected rows admit; no effect is authorised by an earlier answer. -/
  ToctouFrei : R.Einheit → R.Umgebung → R.Lauf → Prop

/-- Each property is refutable: for each, some run of some unit violates it. -/
def SicherheitNichtLeer (R : Rahmen) (S : Sicherheit R) : Prop :=
    (∃ E H ρ, R.Laeufe E H ρ ∧ ¬ S.Speichersicher E H ρ)
  ∧ (∃ E H ρ, R.Laeufe E H ρ ∧ ¬ S.InvariantenErhalten E H ρ)
  ∧ (∃ E H ρ, R.Laeufe E H ρ ∧ ¬ S.Rennfrei E H ρ)
  ∧ (∃ E H ρ, R.Laeufe E H ρ ∧ ¬ S.ToctouFrei E H ρ)

/-- The safety theorems of PERFECT-MODEL §2.2: every run of every accepted program denoted by raw text, on
catalogue-conformant hardware, fair or not, is memory safe, preserves the invariants, is race free and TOCTOU
free; and none of the four properties is trivially true. -/
def GabbroSicherheitForm (R : Rahmen) (S : Sicherheit R) : Prop :=
    SicherheitNichtLeer R S
  ∧ ∀ a E, R.Bezeichnet a E → R.Akzeptiert E → ∀ H, R.Hardware (R.katalog E) H → ∀ ρ, R.Laeufe E H ρ →
      S.Speichersicher E H ρ ∧ S.InvariantenErhalten E H ρ ∧ S.Rennfrei E H ρ ∧ S.ToctouFrei E H ρ

end Gabbro.Core.Ziel
