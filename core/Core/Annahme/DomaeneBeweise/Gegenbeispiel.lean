/-
  File:      core/Core/Annahme/DomaeneBeweise/Gegenbeispiel.lean
  Subject:   The core MK-17 statement `IsolationAussage` is false as pinned: acceptance and static
             coherence do not bind the externally chosen domain plan to the unit's authority.
             A counterexample is the accepted hosted unit (which issues an owned question) paired
             with a well-formed plan that puts every device object in a foreign domain and
             declares no channel. The negation is proved in Lean; the missing premise is the
             per-form duty `RegelIsolation` of `Bruecke.lean`.
-/
module

public import Core.Annahme.Domaene
public import Core.Annahme.HostedLauf

@[expose] public section

namespace Gabbro.Core.Annahme

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog
open Gabbro.Core.Annahme.Hosted

/-- A well-formed two-domain plan: every context in domain `0`, every device object in the
    foreign domain `1`, no channel between them. Memory objects stay in domain `0`. -/
def fremdeFragePlan : DomaenenPlan where
  domaenen := 2
  kontextDomaene := fun _ => 0
  objektDomaene := fun _ => 0
  geraetDomaene := fun _ => 1
  kanaele := []

theorem fremdeFragePlan_wohlgeformt : fremdeFragePlan.wohlgeformt := rfl

theorem fremdeFragePlan_kohaerent : DomaenenKohaerenz Hosted.einheit fremdeFragePlan := by
  refine ⟨?_, ?_, ?_⟩
  · intro c
    exact Nat.zero_lt_succ 1
  · intro x
    exact Nat.zero_lt_succ 1
  · intro o
    exact Nat.succ_lt_succ Nat.zero_lt_one

/-- The accepted hosted unit issues its owned question in an admitted concrete run; the
    recorded spur carries that question under the acting context. -/
theorem isolation_aussage_widerlegt : ¬ IsolationAussage := by
  intro h
  obtain ⟨s, zul⟩ :=
    zulStart_erfuellbar (Hosted.erlaubt []) Gabbro.Core.Sicherheit.Laufkonstruktion.bild_gueltig
  obtain ⟨ρ, _g, _g', lauf, _start, _hw, _z0, _z1, _z2, _z3, _spur0, spur1, _spur2, _leer⟩ :=
    Hosted.konkreter_lauf zul []
  have respektiert := h Hosted.einheit fremdeFragePlan fremdeFragePlan_wohlgeformt
    Hosted.akzeptiert fremdeFragePlan_kohaerent (Hosted.umgebung []) ρ lauf 1
    (SchrittWahl.kontext Hosted.kontext ()) (Hosted.frageSpur s) spur1 Hosted.kontext () rfl
  have dabei : Ereignis.frage (Hosted.gestellt s) ∈ (Hosted.frageSpur s).aussen := by
    simp only [Hosted.frageSpur, List.mem_singleton]
  have nichtFremd := respektiert.2 (Hosted.gestellt s) dabei Hosted.kontext rfl
  have fremd : FremdeFrage fremdeFragePlan Hosted.kontext (Hosted.gestellt s).question := by
    unfold FremdeFrage DomaenenPlan.erlaubt
    intro h
    rcases h with h | h
    · exact Nat.zero_ne_one h
    · exact List.not_mem_nil h
  exact nichtFremd fremd

/-- The pinned collection root is false as well: its first conjunct is the refuted core statement. -/
theorem domaenen_aussage_widerlegt : ¬ DomaenenAussage := by
  intro h
  exact isolation_aussage_widerlegt h.1

end Gabbro.Core.Annahme
