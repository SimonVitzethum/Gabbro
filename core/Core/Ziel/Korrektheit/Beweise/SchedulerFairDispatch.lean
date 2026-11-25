/-
  File:      core/Core/Ziel/Korrektheit/Beweise/SchedulerFairDispatch.lean
  Subject:   DISPATCH DISCIPLINE OF ELABORATED UNITS — the two run facts the scheduler
              duties need about every matched ideal run.

  On an ideal run matched to an implementation run, every elaborated unit keeps
  a strict dispatch discipline: a context is dispatched on at most one core and
  only while live (`einheitVon_dispatch_eindeutig`), because entry needs a
  resting context, every instruction step is frame-only (its plan is `intern`,
  so cores and stacks never move), answers touch no core state, and a crash
  resets to the single entry dispatch. On a suffix where a context stays open
  (`BleibtOffen`: dispatched, headed, live, never discharged) the dispatch
  core therefore never changes (`einheitVon_dispatch_konstant`): context steps
  and answers preserve all cores, a crash would discharge the context, and an
  interrupt on the context's own core would displace it.

  These are properties of the elaborated machine, proved once for every
  elaborated unit; the scheduler duties of `SchedulerFairEinheit.lean` build on
  them. No statement here is changed by the scheduler fairness of `Laeufe`.
-/
module

public import Core.Ziel.Korrektheit.Beweise.FortschrittAkzeptiert

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core
open Gabbro.Core.Maschine

/-- The implementation state at a cut of a matched run is the ideal state: the
    protocol agrees on everything but the local frames, and the local relation
    of an elaborated unit is equality. -/
theorem einheitVon_bezug_gleich (P : Katalog.Plattform) (t : Ast.Unit)
    {H : Katalog.Umgebung} {ρ : Maschine.Lauf (einheitVon P t)}
    {η : Maschine.I.Lauf (einheitVon P t)}
    (matched : Maschine.I.Laufabgleich ρ η)
    (tick : Nat) (s : Ast.Semantik.Zustand)
    (hz : ρ.zeit.zustand tick = some s) :
    s = η.zeit.zustand tick := by
  obtain ⟨x, hx, bezug⟩ := matched.zustand tick
  have xeq : x = s := Option.some.inj (hx.symm.trans hz)
  obtain ⟨proto, lokal⟩ := bezug
  have hlokal : (einheitVon P t).lokalerBezug = Eq := rfl
  rw [hlokal] at lokal
  have hxstate : x = η.zeit.zustand tick := by
    have h2 : ({x with lokal := (η.zeit.zustand tick).lokal} : Ast.Semantik.Zustand) =
        η.zeit.zustand tick := proto
    rw [← lokal] at h2
    exact h2
  rw [← xeq]
  exact hxstate

/-- Every instruction step of an elaborated unit is frame-only: the rule forces
    the private plan, whose action is `intern`, so the post-state agrees with
    the pre-state on cores and status. -/
theorem einheitVon_kontext_erhaelt (P : Katalog.Plattform) (t : Ast.Unit)
    {c : Maschine.Kontext} {s u : Ast.Semantik.Zustand} {w : PUnit}
    {plan : Ast.Semantik.Plan} {spur : Maschine.SchrittSpur Ast.Semantik.Zelle Int}
    {s' : Ast.Semantik.Zustand} {tick : Nat}
    (regel : (einheitVon P t).system.ISchritt c s w [plan] u)
    (aus : Maschine.FuehrtSchrittAus (einheitVon P t).einrichtung tick c s u plan spur s') :
    s'.kerne = s.kerne ∧ s'.status = s.status := by
  obtain ⟨b, _, ideal⟩ := regel
  have hideal :=
    (Ast.Semantik.Befehl.ideal_privat b c s w [plan] u).mp ideal
  have planEq : plan = Ast.Semantik.plan := (List.cons.inj hideal.1).1
  have ueq : u = Ast.Semantik.Befehl.nach b c s := hideal.2
  have hakt : plan.aktion = .intern := by rw [planEq]; rfl
  obtain ⟨rahmen, _, _, _, fuaus, _, seq⟩ := aus
  generalize haussen : spur.aussen = aussen at fuaus
  rw [hakt] at fuaus
  cases fuaus with
  | intern =>
    have kerneEq : s'.kerne = s.kerne := by rw [seq]; exact rahmen.kerne
    have statusEq : s'.status = s.status := by rw [seq, ueq]; rfl
    exact ⟨kerneEq, statusEq⟩

/-- An answer arrival touches no core state: neither dispatch nor status moves. -/
theorem einheitVon_antwort_erhaelt {a : Katalog.AntwortEreignis}
    {s s' : Ast.Semantik.Zustand} {spur : Maschine.SchrittSpur Ast.Semantik.Zelle Int}
    (hstate : s' = {s.antwort a with graph := s'.graph}) :
    s'.kerne = s.kerne ∧ s'.status = s.status := by
  have h1 : s'.kerne = ((s.antwort a).kerne) := by rw [hstate]
  have h2 : ((s.antwort a).kerne) = s.kerne := rfl
  have h3 : s'.status = ((s.antwort a).status) := by rw [hstate]
  have h4 : ((s.antwort a).status) = s.status := rfl
  exact ⟨h1.trans h2, h3.trans h4⟩

/-- Dispatch discipline of every matched ideal run of every elaborated unit: a
    dispatched context is live, and no context is dispatched on two cores. The
    induction follows every ideal transition; context steps and answers
    preserve cores and status, an interrupt enters a resting context, and a
    crash resets to the single entry dispatch. -/
theorem einheitVon_dispatch_eindeutig (P : Katalog.Plattform) (t : Ast.Unit)
    {H : Katalog.Umgebung} {ρ : Maschine.Lauf (einheitVon P t)}
    {η : Maschine.I.Lauf (einheitVon P t)}
    (valid : Maschine.I.Laeufe (einheitVon P t) η)
    (matched : Maschine.I.Laufabgleich ρ η) :
    (∀ tick c k, ((η.zeit.zustand tick).kerne k).laeuft = some c →
      (η.zeit.zustand tick).status c = .laeuft) ∧
    (∀ tick c k₁ k₂, ((η.zeit.zustand tick).kerne k₁).laeuft = some c →
      ((η.zeit.zustand tick).kerne k₂).laeuft = some c → k₁ = k₂) := by
  have hbild : (einheitVon P t).bild.entries = [0] := rfl
  have zul : (einheitVon P t).ZulStart η.umgebung η.start := valid.2.2.1
  obtain ⟨k₀, assign0⟩ := zul.2.2.1 0 (by rw [hbild]; decide)
  have hinit : η.zeit.zustand 0 = (Maschine.I.start (einheitVon P t) η.start).2 := valid.2.2.2.1
  have startkerne : ∀ k c,
      ((((Maschine.I.start (einheitVon P t) η.start).2).kerne k).laeuft = some c) →
      k = k₀ ∧ c = Ast.Semantik.eintritt := by
    intro k c h
    have hif : (if some k = η.start.assignment 0 then some Ast.Semantik.eintritt
        else none) = some c := h
    rw [assign0] at hif
    by_cases hk : some k = some k₀
    · have hkk : k = k₀ := Option.some.inj hk
      subst hkk
      rw [if_pos rfl] at hif
      exact ⟨rfl, (Option.some.inj hif).symm⟩
    · rw [if_neg hk] at hif
      cases hif
  have startstatus : ∀ c, c = Ast.Semantik.eintritt →
      ((Maschine.I.start (einheitVon P t) η.start).2.status c) = .laeuft := by
    intro c hc
    subst hc
    rfl
  have key : ∀ n, (∀ c k, (((η.zeit.zustand n).kerne k).laeuft = some c) →
      (η.zeit.zustand n).status c = .laeuft) ∧
      (∀ c k₁ k₂, (((η.zeit.zustand n).kerne k₁).laeuft = some c) →
        (((η.zeit.zustand n).kerne k₂).laeuft = some c) → k₁ = k₂) := by
    intro n
    induction n with
    | zero =>
      rw [hinit]
      refine ⟨fun c k h => ?_, fun c k₁ k₂ h₁ h₂ => ?_⟩
      · obtain ⟨_, hc⟩ := startkerne k c h
        exact startstatus c hc
      · obtain ⟨h₁, _⟩ := startkerne k₁ c h₁
        obtain ⟨h₂, _⟩ := startkerne k₂ c h₂
        exact h₁.trans h₂.symm
    | succ n ih =>
      obtain ⟨ihlive, ihsingle⟩ := ih
      cases htakt : η.zeit.takt n with
      | schritt label step =>
        cases step with
        | @kontext _ u plan spur _ _ _ _ regel aus =>
          obtain ⟨kerneEq, statusEq⟩ :=
            einheitVon_kontext_erhaelt P t regel aus
          refine ⟨fun c k h => ?_, fun c k₁ k₂ h₁ h₂ => ?_⟩
          · rw [kerneEq] at h
            have hlive := ihlive c k h
            rw [statusEq]
            exact hlive
          · rw [kerneEq] at h₁ h₂
            exact ihsingle c k₁ k₂ h₁ h₂
        | @antwort _ _ a_ev _ arrives =>
          obtain ⟨_, _, _, hstate⟩ := arrives
          obtain ⟨kerneEq, statusEq⟩ := einheitVon_antwort_erhaelt hstate
          refine ⟨fun c k h => ?_, fun c k₁ k₂ h₁ h₂ => ?_⟩
          · rw [kerneEq] at h
            have hlive := ihlive c k h
            rw [statusEq]
            exact hlive
          · rw [kerneEq] at h₁ h₂
            exact ihsingle c k₁ k₂ h₁ h₂
        | @interrupt _ _ id_ev _ enters =>
          obtain ⟨k', _, c', nmi, _, _, _, dormant, _, _, hstate⟩ := enters
          have skerne : (η.zeit.zustand (n + 1)).kerne =
              (Maschine.Zustandseintritt (η.zeit.zustand n) k' id_ev c' nmi).kerne := by
            have h := congrArg (fun (x : Ast.Semantik.Zustand) => x.kerne) hstate
            exact h
          have einkern : ∀ k, (Maschine.Zustandseintritt (η.zeit.zustand n) k' id_ev c' nmi).kerne k =
              if k = k' then ((η.zeit.zustand n).kerne k').unterbrechen c' nmi
              else (η.zeit.zustand n).kerne k := by
            intro k
            by_cases heq : k = k'
            · rw [heq]
              show Function.update _ _ _ _ = _
              rw [Function.update_self, if_pos rfl]
            · show Function.update _ _ _ _ = _
              rw [Function.update_of_ne heq, if_neg heq]
          have statusEq : ∀ d, (η.zeit.zustand (n + 1)).status d =
              (Function.update (η.zeit.zustand n).status c' .laeuft) d := by
            intro d
            have h := congrArg (fun (x : Ast.Semantik.Zustand) => x.status d) hstate
            exact h
          have entered : (η.zeit.zustand (n + 1)).status c' = .laeuft := by
            rw [statusEq, Function.update_self]
          have fresh : ∀ k, (((η.zeit.zustand n).kerne k).laeuft = some c') → False := by
            intro k hk
            have hlive := ihlive c' k hk
            rw [dormant] at hlive
            cases hlive
          refine ⟨fun c k h => ?_, fun c k₁ k₂ h₁ h₂ => ?_⟩
          · rw [skerne, einkern] at h
            by_cases heq : k = k'
            · rw [heq, if_pos rfl] at h
              have hdispatch : ((((η.zeit.zustand n).kerne k').unterbrechen c' nmi)).laeuft
                  = some c' := rfl
              rw [hdispatch] at h
              have hc' : c' = c := Option.some.inj h
              subst hc'
              exact entered
            · rw [if_neg heq] at h
              have hlive := ihlive c k h
              have hne' : ¬ c = c' := fun hcc => fresh k (hcc ▸ h)
              rw [statusEq, Function.update_of_ne hne']
              exact hlive
          · rw [skerne, einkern] at h₁ h₂
            by_cases heq₁ : k₁ = k'
            · by_cases heq₂ : k₂ = k'
              · exact heq₁.trans heq₂.symm
              · rw [heq₁, if_pos rfl] at h₁
                rw [if_neg heq₂] at h₂
                have hdispatch : ((((η.zeit.zustand n).kerne k').unterbrechen c' nmi)).laeuft
                    = some c' := rfl
                rw [hdispatch] at h₁
                have hc' : c' = c := Option.some.inj h₁
                have hne' : ((η.zeit.zustand n).kerne k₂).laeuft = some c' := hc' ▸ h₂
                exact (fresh k₂ hne').elim
            · by_cases heq₂ : k₂ = k'
              · rw [if_neg heq₁] at h₁
                rw [heq₂, if_pos rfl] at h₂
                have hdispatch : ((((η.zeit.zustand n).kerne k').unterbrechen c' nmi)).laeuft
                    = some c' := rfl
                rw [hdispatch] at h₂
                have hc' : c' = c := Option.some.inj h₂
                have hne' : ((η.zeit.zustand n).kerne k₁).laeuft = some c' := hc' ▸ h₁
                exact (fresh k₁ hne').elim
              · rw [if_neg heq₁] at h₁
                rw [if_neg heq₂] at h₂
                exact ihsingle c k₁ k₂ h₁ h₂
        | absturz crash =>
          obtain ⟨_, heq⟩ := crash.genau
          have skernew : (η.zeit.zustand (n + 1)).kerne =
              (((η.zeit.zustand n).wiederanlauf (einheitVon P t).einrichtung.wiederanlauf n
                (Maschine.nachAbsturz (η.zeit.zustand n).persistenz)).kerne) :=
            congrArg _ heq
          refine ⟨fun c k h => ?_, fun c k₁ k₂ h₁ h₂ => ?_⟩
          · rw [skernew] at h
            have hif : (if k = 0 then some Ast.Semantik.eintritt else none) =
                some c := h
            by_cases hk : k = 0
            · subst hk
              rw [if_pos rfl] at hif
              have hc : c = Ast.Semantik.eintritt := (Option.some.inj hif).symm
              subst hc
              have hst : (η.zeit.zustand (n + 1)).status Ast.Semantik.eintritt = .laeuft := by
                have h := congrArg
                  (fun (x : Ast.Semantik.Zustand) => x.status Ast.Semantik.eintritt) heq
                exact h
              exact hst
            · rw [if_neg hk] at hif
              cases hif
          · rw [skernew] at h₁ h₂
            have hif₁ : (if k₁ = 0 then some Ast.Semantik.eintritt else none) =
                some c := h₁
            have hif₂ : (if k₂ = 0 then some Ast.Semantik.eintritt else none) =
                some c := h₂
            by_cases hk₁ : k₁ = 0
            · by_cases hk₂ : k₂ = 0
              · exact hk₁.trans hk₂.symm
              · rw [if_neg hk₂] at hif₂
                cases hif₂
            · rw [if_neg hk₁] at hif₁
              cases hif₁
      | wartet label eq _ =>
        refine ⟨fun c k h => ?_, fun c k₁ k₂ h₁ h₂ => ?_⟩
        · rw [eq] at h
          rw [eq]
          exact ihlive c k h
        · rw [eq] at h₁ h₂
          exact ihsingle c k₁ k₂ h₁ h₂
  refine ⟨?_, ?_⟩
  · intro tick
    obtain ⟨hlive, _⟩ := key tick
    exact fun c k h => hlive c k h
  · intro tick
    obtain ⟨_, hsingle⟩ := key tick
    exact fun c k₁ k₂ h₁ h₂ => hsingle c k₁ k₂ h₁ h₂

/-- On an open suffix the dispatch core never changes: context steps and
    answers preserve all cores, a crash would discharge the context, and an
    interrupt anywhere but on the context's own core leaves it alone, while an
    interrupt on its own core would displace it. -/
theorem einheitVon_dispatch_konstant (P : Katalog.Plattform) (t : Ast.Unit)
    {H : Katalog.Umgebung} {ρ : Maschine.Lauf (einheitVon P t)}
    {η : Maschine.I.Lauf (einheitVon P t)}
    (valid : Maschine.I.Laeufe (einheitVon P t) η)
    (matched : Maschine.I.Laufabgleich ρ η)
    {a : Nat} {c : Maschine.Kontext} {f : Ast.Semantik.Befehl}
    (offen : Maschine.I.BleibtOffen η c f a) :
    ∃ k, ∀ t', a ≤ t' → ((η.zeit.zustand t').kerne k).laeuft = some c := by
  obtain ⟨k, hk⟩ := offen.1 a (Nat.le_refl _)
  obtain ⟨ihlive, ihsingle⟩ := einheitVon_dispatch_eindeutig P t valid matched
  refine ⟨k, fun t' ht' => ?_⟩
  induction ht' with
  | refl => exact hk
  | step hm ih =>
    rename_i m
    cases htakt : η.zeit.takt m with
    | schritt label step =>
      cases step with
      | @kontext _ u plan spur _ _ _ _ regel aus =>
        obtain ⟨kerneEq, _⟩ := einheitVon_kontext_erhaelt P t regel aus
        rw [kerneEq]
        exact ih
      | @antwort _ _ a_ev _ arrives =>
        obtain ⟨_, _, _, hstate⟩ := arrives
        obtain ⟨kerneEq, _⟩ := einheitVon_antwort_erhaelt hstate
        rw [kerneEq]
        exact ih
      | @interrupt _ _ id_ev _ enters =>
        obtain ⟨k', _, c', nmi, _, _, _, dormant, _, _, hstate⟩ := enters
        have skerne : (η.zeit.zustand (m + 1)).kerne =
            (Maschine.Zustandseintritt (η.zeit.zustand m) k' id_ev c' nmi).kerne := by
          have h := congrArg (fun (x : Ast.Semantik.Zustand) => x.kerne) hstate
          exact h
        have einkern : ∀ k, (Maschine.Zustandseintritt (η.zeit.zustand m) k' id_ev c' nmi).kerne k =
            if k = k' then ((η.zeit.zustand m).kerne k').unterbrechen c' nmi
            else (η.zeit.zustand m).kerne k := by
          intro k
          by_cases heq : k = k'
          · rw [heq]
            show Function.update _ _ _ _ = _
            rw [Function.update_self, if_pos rfl]
          · show Function.update _ _ _ _ = _
            rw [Function.update_of_ne heq, if_neg heq]
        have hlive : (η.zeit.zustand m).status c = .laeuft :=
          (offen.2 m hm).2.1
        have hne : c' ≠ c := by
          intro hcc
          rw [hcc] at dormant
          rw [hlive] at dormant
          cases dormant
        obtain ⟨k₂, hk₂⟩ := offen.1 (m + 1) (Nat.le_succ_of_le hm)
        by_cases heq : k₂ = k'
        · rw [heq, skerne, einkern, if_pos rfl] at hk₂
          have hdispatch : ((((η.zeit.zustand m).kerne k').unterbrechen c' nmi)).laeuft
              = some c' := rfl
          rw [hdispatch] at hk₂
          have hc' : c' = c := Option.some.inj hk₂
          exact (hne hc').elim
        · have hsame : (η.zeit.zustand (m + 1)).kerne k₂ =
              (η.zeit.zustand m).kerne k₂ := by
            rw [skerne, einkern, if_neg heq]
          rw [hsame] at hk₂
          have hkk : k₂ = k := ihsingle m c k₂ k hk₂ ih
          have hne : k ≠ k' := hkk ▸ heq
          simpa only [skerne, einkern, if_neg hne] using ih
      | absturz crash =>
        obtain ⟨offer, _, _, _, _⟩ := crash
        have hcrash := (Maschine.I.absturz_am_schnitt (einheitVon P t) η offer).1
        exact ((offen.2 m hm).2.2 (Or.inr (Or.inl hcrash))).elim
    | wartet label eq _ =>
      rw [eq]
      exact ih

end Gabbro.Core.Ziel.Korrektheit
