module

public import Stage0.Senke.Bild.Mehr.SCSchritt
public import Stage0.Senke.Bild.Mehr.Schritt

@[expose] public section

namespace Gabbro.Stage0.Senke.BildMehr

open Runner Runner.IR Runner.Beweis Runner.Mach Gabbro.Grammatik

/-- A memory-only SC path with private requests preserves the image relation
    and its thread footprints. Every prefix has the same committed G state. -/
theorem sc_private_runs_refine {D : Deklaration} [Runner.IR.Kern] {hardwareLayout : Runner.Beweis.Lay}
    {c0 c : Cfg (SC hardwareLayout) (Res T)}
    {P : Programm D} {O : Orakel D} {passes : Nat} {layout : Senke.Lay D}
    {K : FadenMaschine D} {initial : Nat → Option Solo} {positions : Nat → MLage D}
    {committed : Mem}
    (relation : MTRel P O passes layout ⟨c0.ms.1, c0.ths⟩ K initial positions committed)
    (blind : AlleBlind c0.ths)
    (access : ∀ {before after i}, SCErreichbar hardwareLayout c0 before →
      SCSchritt hardwareLayout i before after → ∀ {s o k},
      initial i = some s → before.ths[i]? = some (some (.ask o k)) →
      (∀ y, fussOp o y → s.F y) ∧ (schreibtOp o = true → ∀ y, fussOp o y → s.Wr y))
    (reached : SCErreichbar hardwareLayout c0 c) :
    ∃ snapshots, MTRel P O passes layout ⟨c.ms.1, c.ths⟩ K snapshots positions committed ∧
      AlleBlind c.ths ∧ ∀ i s, snapshots i = some s →
        ∃ original, initial i = some original ∧ s.F = original.F ∧ s.Wr = original.Wr := by
  induction reached with
  | start => exact ⟨initial, relation, blind, fun _ s found => ⟨s, found, rfl, rfl⟩⟩
  | @schritt before after i reachedBefore step ih =>
    obtain ⟨snapshots, beforeRelation, beforeBlind, sameSets⟩ := ih
    have live : ∃ result, before.ths[i]? = some (some result) := by
      cases step with
      | priv found => exact ⟨_, found⟩
      | ask found _ _ => exact ⟨_, found⟩
    obtain ⟨result, live⟩ := live
    obtain ⟨s, found⟩ := beforeRelation.lebend i result live
    have privateRequest : ImFuss s := by
      intro o k request
      obtain ⟨original, originalFound, footprint, writes⟩ := sameSets i s found
      have pending := beforeRelation.zustand i s found
      rw [request] at pending
      simpa only [footprint, writes] using access reachedBefore step originalFound pending
    obtain ⟨next, footprint, writes, afterRelation⟩ :=
      mtRel_schritt beforeRelation found privateRequest (sc_mSchritt step (beforeBlind i))
    refine ⟨setzeS snapshots i next, afterRelation, alleBlind_schritt step beforeBlind, ?_⟩
    intro j s' updated
    obtain ⟨beforeSnapshot, beforeFound, sameFootprint, sameWrites⟩ :=
      setzeS_fuss found footprint writes updated
    obtain ⟨original, originalFound, oldFootprint, oldWrites⟩ := sameSets j beforeSnapshot beforeFound
    exact ⟨original, originalFound, sameFootprint.trans oldFootprint, sameWrites.trans oldWrites⟩

end Gabbro.Stage0.Senke.BildMehr
