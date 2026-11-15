/-
  File:      stage0/Stage0/Senke/Bild/Mehr/Schritt.lean
  Subject:   THE SINGLE-STEP LIFT (multi-thread image theorem, package MT1). A step of runner thread `i` that the
             memory answers alone (`MSchritt i`: the start of an instruction, or a request) and whose request lies
             in `i`'s private footprint -- in its write set if it writes (`ImFuss`): so NOT a lock step and NOT an
             atomic step, whose words lie in no private footprint -- keeps the simulation relation with the SAME
             thread machine `K`, the same positions and the same committed memory: machine G stutters
             (`mtRel_schritt`). The thread's footprint and write set are kept, its solo run is one request longer
             (`SoloLauf.priv`, `SoloLauf.ask`), and the shared memory changed inside its write set only, so the
             other threads' solo memories still agree with it (`verschmolzen_ask`). At every instruction boundary
             the thread's solo state corresponds to machine G by the single-thread chain (`mtRel_korrespondenz`).
-/
module
public import Stage0.Senke.Bild.Mehr.Relation
@[expose] public section

namespace Gabbro.Stage0.Senke.BildMehr

open Gabbro.Grammatik Gabbro.Stage0.Senke Gabbro.Stage0.Senke.BildLauf Runner.IR

set_option linter.unusedSectionVars false

variable {D : Deklaration} [Kern]

/-- The thread's entry in the configuration is its `Solo` state. -/
theorem MTRel.zustand_eq {P : Programm D} {O : Orakel D} {passes : Nat} {L : Lay D} {c : PCfg}
    {K : FadenMaschine D} {S : Nat → Option Solo} {X : Nat → MLage D} {mk : Runner.Mem}
    (hR : MTRel P O passes L c K S X mk) {i : Nat} {s : Solo} (hi : S i = some s) {r : Runner.Res T}
    (h : c.ths[i]? = some (some r)) : s.r = r :=
  Option.some.inj (Option.some.inj ((hR.zustand i s hi).symm.trans h))

/-- **The single-step lift.** A step of thread `i` answered by the memory alone, with its request inside the thread's
    private footprint, keeps the relation with the same `K`, positions and committed memory; the thread keeps its
    footprint and write set. -/
theorem mtRel_schritt {P : Programm D} {O : Orakel D} {passes : Nat} {L : Lay D} {c c' : PCfg}
    {K : FadenMaschine D} {S : Nat → Option Solo} {X : Nat → MLage D} {mk : Runner.Mem}
    (hR : MTRel P O passes L c K S X mk) {i : Nat} {s : Solo} (hi : S i = some s) (hF : ImFuss s)
    (hs : MSchritt i c c') :
    ∃ s' : Solo, s'.F = s.F ∧ s'.Wr = s.Wr ∧ MTRel P O passes L c' K (setzeS S i s') X mk := by
  cases hs with
  | @priv t ht =>
    have hr := hR.zustand_eq hi ht
    have hsolo := hR.solo i s hi
    rw [hr] at hsolo
    refine ⟨{ s with r := step t }, rfl, rfl, hR.nach hi rfl (set_selbst ht) (fun j hj => set_fremd _ _ hj)
      (verschmolzen_gleich hR.mem hi rfl rfl rfl) hsolo.priv (fun y _ => GleichAt.refl _ y)⟩
  | @ask o k a m' ht hm =>
    have hr := hR.zustand_eq hi ht
    obtain ⟨m2', hm2, hV, hau⟩ := verschmolzen_ask hR.mem hi hr hF hm
    have hsolo := hR.solo i s hi
    rw [hr] at hsolo
    exact ⟨{ s with r := k a, m := m2' }, rfl, rfl, hR.nach hi rfl (set_selbst ht) (fun j hj => set_fremd _ _ hj)
      hV (hsolo.ask hm2) hau⟩

/-- **P0-P5 inside the relation**: a thread with a `Solo` that stands at an instruction boundary corresponds to
    machine G by the single-thread chain, from its position's view machine. -/
theorem mtRel_korrespondenz {P : Programm D} {O : Orakel D} {passes : Nat} {L : Lay D} {c : PCfg}
    {K : FadenMaschine D} {S : Nat → Option Solo} {X : Nat → MLage D} {mk : Runner.Mem}
    (hR : MTRel P O passes L c K S X mk) {i : Nat} {s : Solo} (hi : S i = some s) {t : T} (ht : s.r = .next t) :
    (∃ M', RufLaufG (X i).B.P (X i).B.O (X i).B.passes (X i).thr (X i).M M' ∧
        Korrespondenz (X i).B (X i).thr (X i).stapel (X i).rho (X i).s0 (X i).Agl (X i).l t s.m M') ∨
    (∃ (pce : Runner.W) (me : Runner.Mem) (Me : RufMaschineG D),
        Rand (X i).B (X i).thr (X i).stapel (X i).rho (X i).s0 (X i).Agl (X i).ebe pce me Me (X i).σe (X i).ρe ∧
        RufLaufG (X i).B.P (X i).B.O (X i).B.passes (X i).thr (X i).M Me ∧
        ∃ k, StarM k ⟨pce, (X i).B.fp⟩ me t s.m) := by
  have hsolo := hR.solo i s hi
  rw [ht] at hsolo
  exact MLage.korrespondenz (hR.lage i s hi) hsolo

end Gabbro.Stage0.Senke.BildMehr
