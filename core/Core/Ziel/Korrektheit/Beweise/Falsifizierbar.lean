/-
  File:      core/Core/Ziel/Korrektheit/Beweise/Falsifizierbar.lean
  Subject:   THE THREE FALSIFIABILITY STATEMENTS of `Ziel/Korrektheit/Verfeinerung`: the per-form
             simulation duty is discriminating, the whole-run simulation separates ideal runs, and the
             refinement refuses an implementation run. The shared concrete unit and run come from
             `FalsifizierbarBasis`. Two rule variants give the witnesses: an empty ideal rule refutes
             every ideal run and discriminates the per-form duty; a tolerant rule with stutter bound
             zero has one matched ideal run and one that spends the private tick, separated by
             `nicht_sim_bei_stotterueberlauf`. The pinned statements are unchanged.
-/
module

public import Core.Ziel.Korrektheit.Beweise.FalsifizierbarBasis

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core Maschine Katalog
open Gabbro.Core.Maschine.I


/-! ### The per-form duty distinguishes a rule whose ideal side is empty -/

theorem regelSimDiskriminiert : RegelSimDiskriminiertAussage := by
  obtain ⟨s, z, z', u, plan, spur, ρ, zul, zStart, planEq, uEq, z'Eq, ρstart, ρhw, konkret,
    ρspur0, spurEq, ρz0, ρz1, implSchritt, exec, ready, normal⟩ := falsifizierbar_konfiguration
  subst u
  subst plan
  subst spur
  have z'z : z' = z := z'Eq.trans rfl
  subst z'
  let syRef : MaschinenSystem Unit Unit Unit Unit Unit Unit Unit Unit Unit :=
    { falsifizierbaresSystem with regel := fun _ => ⟨falsifizierbareImpl, fun _ _ _ _ _ => False⟩ }
  let ERef : Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit :=
    { falsifizierbareEinheit with system := syRef, stotterLaenge := fun _ => 0 }
  refine ⟨ERef, (), ?_⟩
  intro sim
  have folgerung := sim falsifizierbarerHw 0 falsifizierbarerEintrag () z z z
    z falsifizierbarerPlan ⟨[], []⟩ ⟨ProtokollBezug.refl z, rfl⟩ normal ready rfl implSchritt exec
  cases folgerung with
  | inl idealFolge =>
      obtain ⟨i', idealSchritt, _⟩ := idealFolge
      cases idealSchritt with
      | kontext _ _ regelIdeal _ =>
          obtain ⟨j, _, idealJ⟩ := regelIdeal
          simpa only [ERef, syRef] using idealJ
  | inr privat =>
      rcases privat with ⟨_, _, _, _, ueberlauf⟩
      have null : 0 < 0 := by
        simpa only [ERef] using ueberlauf
      exact (Nat.lt_irrefl 0 null)

/-! ### The same real match and a stuttering ideal run separate `Sim` -/

theorem simTrennt : SimTrenntAussage := by
  obtain ⟨s, z, z', u, plan, spur, ρ, zul, zStart, planEq, uEq, z'Eq, ρstart, ρhw, konkret,
    ρspur0, spurEq, ρz0, ρz1, implSchritt, exec, ready, normal⟩ := falsifizierbar_konfiguration
  subst u
  subst plan
  subst spur
  have z'z : z' = z := z'Eq.trans rfl
  subst z'
  let label : SchrittWahl Unit × SchrittSpur Unit Unit := (.kontext falsifizierbarerEintrag (), ⟨[], []⟩)
  let syTrenn : MaschinenSystem Unit Unit Unit Unit Unit Unit Unit Unit Unit :=
    { falsifizierbaresSystem with
      regel := fun _ => ⟨falsifizierbareImpl,
        fun _ x _ plans v => plans = [falsifizierbarerPlan] ∧ v = x⟩ }
  let ETrenn : Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit :=
    { falsifizierbareEinheit with
      system := syTrenn
      lokalerBezug := fun l i => ∀ c, c ≠ falsifizierbarerEintrag → l c = i c
      stotterLaenge := fun _ => 0 }
  have startZ : (start ETrenn s).2 = z := by
    change (start falsifizierbareEinheit s).2 = z
    exact zStart
  have initial : Zustandsbezug ETrenn z z := ⟨ProtokollBezug.refl z, fun _ _ => rfl⟩
  have final : Zustandsbezug ETrenn z z := initial
  have konform : falsifizierbarerHw.konform ETrenn.katalog falsifizierbareUmgebung := by
    rw [← ρhw]
    exact konkret.2.1
  have loaded : ETrenn.laden s (falsifizierbareUmgebung.lade ETrenn.bild) = some z := by
    change falsifizierbareEinheit.laden s (falsifizierbareUmgebung.lade falsifizierbaresBild) = some z
    rw [← ρstart]
    exact (ρz0.symm.trans konkret.2.2.2.1).symm
  have lastOpportunity : (letztesAngebot falsifizierbarerHw).gelegenheit 0 0 := by
    change falsifizierbarerHw.gelegenheit 0 0
    exact congrArg some (Nat.mod_one 0)
  have boot : s.bootCore = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ zul.2.1)
  have dispatchZ : (z.kerne 0).laeuft = some falsifizierbarerEintrag := by
    rw [← zStart]
    change (if 0 = s.bootCore then some falsifizierbarerEintrag else none) = some falsifizierbarerEintrag
    rw [boot, ite_eq_left rfl]
  have liveZ : z.status falsifizierbarerEintrag = .laeuft := by
    rw [← zStart]
    change (if falsifizierbarerEintrag = falsifizierbarerEintrag then Status.laeuft else Status.ruht) =
      (Status.laeuft : Status Unit Unit)
    exact ite_eq_left rfl
  have lastReady : KannSchreiten (letztesAngebot falsifizierbarerHw) 0 falsifizierbarerEintrag z :=
    ⟨0, lastOpportunity, dispatchZ, liveZ⟩
  have privateStep : ImplSchritt falsifizierbareEinrichtung syTrenn ETrenn.katalog
      (letztesAngebot falsifizierbarerHw) 0 z
      (.kontext falsifizierbarerEintrag (), ⟨[], []⟩) z :=
    .kontext rfl lastReady ⟨(), rfl, rfl, rfl⟩ exec
  have execKeep : FuehrtSchrittAus falsifizierbareEinrichtung 0 falsifizierbarerEintrag z z
      falsifizierbarerPlan ⟨[], []⟩ z := by
    exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      fun _ h => (List.not_mem_nil h).elim, [], z, .intern, .nil _, rfl⟩
  have idealStepKeep : Schritt falsifizierbareEinrichtung syTrenn ETrenn.katalog
      (letztesAngebot falsifizierbarerHw) 0 z
      (.kontext falsifizierbarerEintrag (), ⟨[], []⟩) z :=
    .kontext rfl lastReady ⟨(), rfl, rfl, rfl⟩ execKeep
  have konformLetztes := falsifizierbares_letztesAngebot_konform konform
  let ρT : Maschine.Lauf ETrenn := ⟨s, letztesAngebot falsifizierbarerHw, {
    zustand := fun _ => some z
    spur := fun | 0 => some label | _ + 1 => none
    takt := fun
      | 0 => .schritt rfl (.schritt privateStep)
      | t + 1 => .wartet rfl rfl (falsifizierbares_letztesAngebot_konkret ETrenn t z) }⟩
  have stillT : ∀ t, 1 ≤ t → ∀ s, ρT.zeit.zustand t = some s →
      KeinSchritt (Lauffolge ETrenn ρT.hw) t (some s) := by
    intro t ht s hs ev next step
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega)
    have hss : s = z := (Option.some.inj hs).symm
    subst hss
    exact falsifizierbares_letztesAngebot_konkret ETrenn m z ev next step
  have runT : Maschine.Laeufe ETrenn falsifizierbareUmgebung ρT :=
    ⟨konkret.1, konformLetztes, zul, by
      change some z = ETrenn.laden s (falsifizierbareUmgebung.lade ETrenn.bild)
      exact loaded.symm, SchedulerFair_aus_stillstand_ab ETrenn ρT 1 stillT⟩
  let η₂ : I.Lauf ETrenn := ⟨s, falsifizierbareUmgebung, letztesAngebot falsifizierbarerHw, {
    zustand := fun _ => z
    spur := fun _ => none
    takt := fun
      | 0 => .wartet rfl rfl (fun h => Bool.false_ne_true (normal.symm.trans h.2))
      | t + 1 => .wartet rfl rfl (fun h => Bool.false_ne_true h.2) },
    fun | 0 => some falsifizierbarerEintrag | _ + 1 => none⟩
  have valid₂ : Laeufe ETrenn η₂ := by
    refine ⟨konkret.1, konformLetztes, zul, startZ.symm, ?_, ?_⟩
    · constructor
      · intro t still frei
        cases t with
        | zero =>
            change some falsifizierbarerEintrag = none at frei
            cases frei
        | succ t => exact falsifizierbares_letztesAngebot_ideal ETrenn t z
      · intro endlich
        refine ⟨1, fun i after => ?_⟩
        cases i with
        | zero => exact (Nat.not_succ_le_zero _ after).elim
        | succ _ => rfl
    · intro t d mark
      cases t with
      | zero =>
          change some falsifizierbarerEintrag = some d at mark
          cases Option.some.inj mark
          exact ⟨rfl, lastReady⟩
      | succ _ => exact (Option.some_ne_none _ mark.symm).elim
  let η₁ : I.Lauf ETrenn := ⟨s, falsifizierbareUmgebung, letztesAngebot falsifizierbarerHw, {
    zustand := fun _ => z
    spur := fun | 0 => some label | _ + 1 => none
    takt := fun
      | 0 => .schritt rfl idealStepKeep
      | t + 1 => .wartet rfl rfl (fun h => Bool.false_ne_true h.2) },
    fun _ => none⟩
  have valid₁ : Laeufe ETrenn η₁ := by
    refine ⟨konkret.1, konformLetztes, zul, startZ.symm, ?_, ?_⟩
    · constructor
      · intro t still frei
        cases t with
        | zero =>
            change some label = none at still
            cases still
        | succ t => exact falsifizierbares_letztesAngebot_ideal ETrenn t z
      · intro endlich
        exact ⟨0, fun _ _ => rfl⟩
    · intro t d mark
      cases mark
  have matched₁ : Laufabgleich ρT η₁ := by
    refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
    · intro t
      exact ⟨z, rfl, initial⟩
    · intro t
      cases t with
      | zero => exact .schritt label
      | succ _ => exact .pause
    · intro t
      cases t with
      | zero =>
          refine ⟨fun _ => Or.inr ?_, fun _ => rfl⟩
          change some label ≠ none
          exact Option.some_ne_none _
      | succ _ => exact ⟨fun _ => Or.inl rfl, fun _ => rfl⟩
    · intro t d mark
      cases mark
  have authorityT : ∀ t, BerechtigungAmTakt ρT t := by
    intro t a b c w sp u p ha hb hspur hcrash hready himpl hex
    cases t with
    | zero =>
        rcases himpl with ⟨i, hi, implI⟩
        change falsifizierbareImpl c a () [p] u at implI
        obtain ⟨hp, _⟩ := implI
        cases (List.cons.inj hp).1
        exact falsifizierbarerPlan_autorisiert a c
    | succ t =>
        change none = some (SchrittWahl.kontext c w, sp) at hspur
        cases hspur
  have continuationT : ∀ a i, Zustandsbezug ETrenn a i → FortsetzungsBezug ETrenn a i := by
    intro a i related c
    exact ⟨congrFun (congrArg Zustand.status related.1) c, Iff.rfl, fun _ => Iff.rfl⟩
  have simη₁ : Sim ETrenn ρT η₁ :=
    matched₁.sim valid₁ (StotterSchranke.ohne_stottern (fun _ => rfl)) authorityT continuationT
  have interval₂ : Stotterintervall η₂ falsifizierbarerEintrag () 0 1 := by
    intro t lower upper
    have ht : t = 0 := by omega
    subst t
    refine ⟨rfl, ?_, ?_⟩
    · intro w sp h
      exact (Option.some_ne_none _ h.symm).elim
    · intro h
      exact (Option.some_ne_none _ h.symm).elim
  have mark₂ : η₂.belegt 0 = some falsifizierbarerEintrag := rfl
  have ueberlauf₂ : ETrenn.stotterLaenge () <
      zaehle (fun t => decide (η₂.belegt t = some falsifizierbarerEintrag)) 0 1 := by
    change 0 < zaehle (fun t => decide (η₂.belegt t = some falsifizierbarerEintrag)) 0 1
    simpa only [zaehle, Nat.zero_add, decide_eq_true mark₂, ite_true] using Nat.zero_lt_one
  have notSim₂ : ¬ Sim ETrenn ρT η₂ := nicht_sim_bei_stotterueberlauf interval₂ ueberlauf₂
  exact ⟨ETrenn, ρT, η₁, η₂, valid₁, simη₁, valid₂, notSim₂⟩

/-! ### The empty ideal rule refutes every ideal run of a concrete implementation run -/

theorem simRefutierbar : SimRefutierbarAussage := by
  obtain ⟨s, z, z', u, plan, spur, ρ, zul, zStart, planEq, uEq, z'Eq, ρstart, ρhw, konkret,
    ρspur0, spurEq, ρz0, ρz1, implSchritt, exec, ready, normal⟩ := falsifizierbar_konfiguration
  subst u
  subst plan
  subst spur
  have z'z : z' = z := z'Eq.trans rfl
  subst z'
  let syRef : MaschinenSystem Unit Unit Unit Unit Unit Unit Unit Unit Unit :=
    { falsifizierbaresSystem with regel := fun _ => ⟨falsifizierbareImpl, fun _ _ _ _ _ => False⟩ }
  let ERef : Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit :=
    { falsifizierbareEinheit with system := syRef, stotterLaenge := fun _ => 0 }
  let label : SchrittWahl Unit × SchrittSpur Unit Unit := (.kontext falsifizierbarerEintrag (), ⟨[], []⟩)
  have konform : falsifizierbarerHw.konform ERef.katalog falsifizierbareUmgebung := by
    rw [← ρhw]
    exact konkret.2.1
  have loaded : ERef.laden s (falsifizierbareUmgebung.lade ERef.bild) = some z := by
    change falsifizierbareEinheit.laden s (falsifizierbareUmgebung.lade falsifizierbaresBild) = some z
    rw [← ρstart]
    exact (ρz0.symm.trans konkret.2.2.2.1).symm
  have lastOpportunity : (letztesAngebot falsifizierbarerHw).gelegenheit 0 0 := by
    change falsifizierbarerHw.gelegenheit 0 0
    exact congrArg some (Nat.mod_one 0)
  have boot : s.bootCore = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ zul.2.1)
  have dispatchZ : (z.kerne 0).laeuft = some falsifizierbarerEintrag := by
    rw [← zStart]
    change (if 0 = s.bootCore then some falsifizierbarerEintrag else none) = some falsifizierbarerEintrag
    rw [boot, ite_eq_left rfl]
  have liveZ : z.status falsifizierbarerEintrag = .laeuft := by
    rw [← zStart]
    change (if falsifizierbarerEintrag = falsifizierbarerEintrag then Status.laeuft else Status.ruht) =
      (Status.laeuft : Status Unit Unit)
    exact ite_eq_left rfl
  have lastReady : KannSchreiten (letztesAngebot falsifizierbarerHw) 0 falsifizierbarerEintrag z :=
    ⟨0, lastOpportunity, dispatchZ, liveZ⟩
  have privateStepRef : ImplSchritt ERef.einrichtung ERef.system ERef.katalog
      (letztesAngebot falsifizierbarerHw) 0 z label z :=
    .kontext rfl lastReady ⟨(), rfl, rfl, rfl⟩ exec
  let ρRef : Maschine.Lauf ERef := ⟨s, letztesAngebot falsifizierbarerHw, {
    zustand := fun _ => some z
    spur := fun | 0 => some label | _ + 1 => none
    takt := fun
      | 0 => .schritt rfl (.schritt privateStepRef)
      | t + 1 => .wartet rfl rfl (falsifizierbares_letztesAngebot_konkret ERef t z) }⟩
  have ρRefSpur0 : ρRef.zeit.spur 0 = some label := rfl
  have runRef : Maschine.Laeufe ERef falsifizierbareUmgebung ρRef :=
    ⟨konkret.1, falsifizierbares_letztesAngebot_konform konform, zul, by
      change some z = ERef.laden s (falsifizierbareUmgebung.lade ERef.bild)
      exact loaded.symm⟩
  refine ⟨ERef, falsifizierbareUmgebung, ρRef, runRef, ?_⟩
  intro η validη simη
  rcases simη with ⟨ordnung, matched, bound, rest⟩
  have sp0 : SpurAbgleich (some label) (η.zeit.spur 0) := by
    simpa only [ρRefSpur0] using matched.spur 0
  rcases SpurAbgleich.ideales_etikett sp0 with ηleer | ηlabel
  · have ηbelegt : η.belegt 0 ≠ none := by
      intro leer
      have alternatives := (matched.frei 0).mp leer
      cases alternatives with
      | inl ρleer =>
          exact (Option.some_ne_none _ (ρRefSpur0.symm.trans ρleer)).elim
      | inr ηaktiv => exact ηaktiv ηleer
    cases hmark : η.belegt 0 with
    | none => exact (ηbelegt hmark).elim
    | some d =>
        obtain ⟨w', f, ρspurPrivat, headF⟩ := matched.belegt 0 d hmark
        have eq := Option.some.inj (ρspurPrivat.symm.trans ρRefSpur0)
        have fst := congrArg Prod.fst eq
        change SchrittWahl.kontext d w' = SchrittWahl.kontext falsifizierbarerEintrag () at fst
        injection fst with hd hw'
        subst d
        have interval : Stotterintervall η falsifizierbarerEintrag f 0 1 := by
          intro t lower upper
          have ht : t = 0 := by omega
          subst t
          refine ⟨headF, ?_, ?_⟩
          · intro w s h
            exact (Option.some_ne_none _ (h.symm.trans ηleer)).elim
          · intro h
            exact (Option.some_ne_none _ (h.symm.trans ηleer)).elim
        have ueberlauf : ERef.stotterLaenge f <
            zaehle (fun t => decide (η.belegt t = some falsifizierbarerEintrag)) 0 1 := by
          change 0 < zaehle (fun t => decide (η.belegt t = some falsifizierbarerEintrag)) 0 1
          simpa only [zaehle, Nat.zero_add, decide_eq_true hmark, ite_true] using Nat.zero_lt_one
        exact (nicht_sim_bei_stotterueberlauf (ρ := ρRef) interval ueberlauf) ⟨ordnung, matched, bound, rest⟩
  · have etakt := η.zeit.takt 0
    rw [ηlabel] at etakt
    cases etakt with
    | wartet still _ _ =>
        exact (Option.some_ne_none label still).elim
    | schritt labelEq idealSchritt =>
        have evEq := Option.some.inj labelEq.symm
        cases idealSchritt with
        | kontext _ _ regelIdeal _ =>
            obtain ⟨i, _, idealI⟩ := regelIdeal
            simpa only [ERef, syRef] using idealI
        | antwort a h =>
            have fstEq := congrArg Prod.fst evEq
            cases fstEq
        | interrupt id h =>
            have fstEq := congrArg Prod.fst evEq
            cases fstEq
        | absturz h =>
            have fstEq := congrArg Prod.fst evEq
            cases fstEq

end Gabbro.Core.Ziel.Korrektheit