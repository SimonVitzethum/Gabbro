/-
  File:      core/Core/Ziel/Korrektheit/Beweise/FortschrittAkzeptiert.lean
  Subject:   THE PROGRESS PROMISE FOR EVERY ACCEPTED ELABORATED UNIT — the legs that hold today, and the one
             scheduler premise missing for the pinned statement.

  `FortschrittAkzeptiertAussage` is pinned through `KorrektheitAussagen` and is not changed here. Two of its
  legs are available for every accepted unit today: a matched ideal run with whole-run simulation
  (`sim_im_lauf`) and the composed per-cut alternatives (`fortschritt_im_lauf`). The four form-side fields of
  `FortschrittsPflichten` are theorems of the elaborated system (`Fragment.fertig`, `Befehl.fortschritt`,
  `Befehl.komponierbar`, `Fragment.bereit_eindeutig`), collected in `einheit_fortschrittsfelder`.

  The remaining leg is per-context liveness: `¬ Haengt` asks that a continuously enabled, dispatched context
  eventually be serviced on a hardware-fair history. `FairLaeufe` speaks about cores, deliveries and cycles
  only — explicitly "independently of dispatch ... or the existence of a successful implementation step"
  (`Katalog/Lauf.lean`) — so it does not arbitrate which ready context takes a step. The four scheduler fields
  `angebot`, `wahl`, `individuell` and `systemweit` of `FortschrittsPflichten` are therefore an additional
  premise (`SchedulerFortschrittVoraussetzung`), not a theorem of the current model. With that premise the pinned
  statement follows by `sim_ziel_fortschritt_im_lauf`; without it the strongest theorem here is
  `fortschritt_akzeptiert_ohne_haengen`, which leaves exactly the no-hang leg open.
-/
module

public import Core.Ziel.Korrektheit.Verfeinerung
public import Core.Verfeinerung.Fortschritt
public import Core.Verfeinerung.Simulation
public import Core.Ast.Semantik.Pflichten

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core
open Gabbro.Core.Maschine
open Gabbro.Core.Ideal (RegelFortschritt)

/-- THE MISSING SCHEDULER PREMISE. On every fair run of every accepted elaborated unit, the matched ideal run
    admits a selection predicate `nutzbar` for which the four dispatch and selection duties hold: `angebot`
    (a dispatched core offers a tick), `wahl` (the recorded run takes the offered context step), `individuell`
    (a continuously enabled open context is offered again past every cut) and `systemweit` (the system-wide
    completion duty; vacuous for `blockierend`). The other four fields of `FortschrittsPflichten` are theorems
    over the elaborated system (`einheit_fortschrittsfelder`), so this is exactly the hypothesis that
    `sim_ziel_fortschritt_im_lauf` still needs for the pinned `FortschrittAkzeptiertAussage`. -/
def SchedulerFortschrittVoraussetzung : Prop :=
  ∀ (P : Katalog.Plattform) (t : Ast.Unit), Annahme.Akzeptiert (einheitVon P t) →
    ∀ (H : Katalog.Umgebung) (ρ : Maschine.Lauf (einheitVon P t)),
      Maschine.Laeufe (einheitVon P t) H ρ → Katalog.FairLaeufe (einheitVon P t).katalog H ρ.hw →
      ∀ η : Maschine.I.Lauf (einheitVon P t),
        Maschine.I.Laeufe (einheitVon P t) η →
        Maschine.I.Laufabgleich ρ η →
        η.umgebung = H →
        ∃ nutzbar, Maschine.I.FortschrittsPflichten
          (Maschine.I.FortschrittsKlasse.blockierend : Maschine.I.FortschrittsKlasse Ast.Semantik.Befehl)
          ρ η nutzbar

/-- The four form-side fields of `FortschrittsPflichten` hold for the elaborated unit without any acceptance
    or run premise: a headless context is finished, every instruction has its ideal step, that step composes
    through the shared protocol, and a ready context is neither finished nor blocked. -/
theorem einheit_fortschrittsfelder (P : Katalog.Plattform) (t : Ast.Unit) :
    (∀ s c, (einheitVon P t).system.kopf s c = none → (einheitVon P t).system.fertig s c) ∧
    (∀ f : Ast.Semantik.Befehl, RegelFortschritt (einheitVon P t).system f) ∧
    (∀ f : Ast.Semantik.Befehl,
      Maschine.I.RegelKomponierbar (einheitVon P t).einrichtung (einheitVon P t).system f) ∧
    (∀ s c, Maschine.I.Bereit (E := einheitVon P t) s c →
      ¬ (einheitVon P t).system.fertig s c ∧ ∀ b, ¬ (einheitVon P t).system.blockiert s c b) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Ast.Semantik.Fragment.fertig (Ast.Semantik.fragment Ast.Category.unit t) P
  · intro f
    exact Ast.Semantik.Befehl.fortschritt (Ast.Semantik.fragment Ast.Category.unit t) f
  · intro f
    exact Ast.Semantik.Befehl.komponierbar (Ast.Semantik.fragment Ast.Category.unit t) P f
  · intro s c bereit
    rcases bereit with ⟨w, plans, u, step⟩
    exact Ast.Semantik.Fragment.bereit_eindeutig (Ast.Semantik.fragment Ast.Category.unit t) P step

/-- TODAY'S PROGRESS LEG FOR EVERY ACCEPTED ELABORATED UNIT: a matched ideal run with whole-run simulation and
    the composed per-cut alternatives exist. This is all of the pinned statement except the per-context
    no-hang leg; the scheduler duty `SchedulerFortschrittVoraussetzung` is what remains. -/
theorem fortschritt_akzeptiert_ohne_haengen :
    ∀ (P : Katalog.Plattform) (t : Ast.Unit), Annahme.Akzeptiert (einheitVon P t) →
      ∀ (H : Katalog.Umgebung) (ρ : Maschine.Lauf (einheitVon P t)),
        Maschine.Laeufe (einheitVon P t) H ρ →
        ∃ η : Maschine.I.Lauf (einheitVon P t),
          Maschine.I.Laeufe (einheitVon P t) η ∧
          Maschine.I.Sim (einheitVon P t) ρ η ∧
          Maschine.I.FortschrittDerKlasse
            (Maschine.I.FortschrittsKlasse.blockierend : Maschine.I.FortschrittsKlasse Ast.Semantik.Befehl) η := by
  intro P t _ H ρ lauf
  have pflicht : Maschine.I.SimPflichten (einheitVon P t) :=
    (Ast.Semantik.Fragment.simBasis (Ast.Semantik.fragment Ast.Category.unit t) P).mit_formen
      (Ast.Semantik.sim_formen (Ast.Semantik.fragment Ast.Category.unit t) P)
  obtain ⟨η, valid, sim⟩ := Maschine.I.sim_im_lauf pflicht lauf
  refine ⟨η, valid, sim, ?_⟩
  obtain ⟨fertig, regeln, komponierbar, _⟩ := einheit_fortschrittsfelder P t
  refine ⟨?_, trivial⟩
  intro zeit kontext live dispatch
  exact Maschine.I.fortschritt_im_lauf valid fertig regeln komponierbar zeit kontext live dispatch

/-- The pinned statement follows once the scheduler duties are stated for the elaborated unit:
    `sim_ziel_fortschritt_im_lauf` consumes exactly `SchedulerFortschrittVoraussetzung`, and every other premise is
    already a theorem. -/
theorem fortschritt_akzeptiert_aus_scheduler (scheduler : SchedulerFortschrittVoraussetzung) :
    FortschrittAkzeptiertAussage := by
  intro P t akzeptiert H ρ lauf fair
  have pflicht : Maschine.I.SimPflichten (einheitVon P t) :=
    (Ast.Semantik.Fragment.simBasis (Ast.Semantik.fragment Ast.Category.unit t) P).mit_formen
      (Ast.Semantik.sim_formen (Ast.Semantik.fragment Ast.Category.unit t) P)
  obtain ⟨η, valid, sim, _, rest⟩ :=
    Maschine.I.sim_ziel_fortschritt_im_lauf
      (klasse := (Maschine.I.FortschrittsKlasse.blockierend : Maschine.I.FortschrittsKlasse Ast.Semantik.Befehl))
      pflicht lauf
      (fun η valid matched environment fairness =>
        scheduler P t akzeptiert H ρ lauf fairness η valid matched environment)
  exact ⟨η, valid, sim, (rest fair).1, (rest fair).2⟩

/-- Rule transfer for elaborated units: every ideal form step is an implementation step
    (both are the private plan with the frame transfer). -/
theorem einheitVon_impl_aus_ideal (P : Katalog.Plattform) (t : Ast.Unit)
    {c : Maschine.Kontext} {s u : Ast.Semantik.Zustand} {w : PUnit}
    {plans : List Ast.Semantik.Plan}
    (h : (einheitVon P t).system.ISchritt c s w plans u) :
    (einheitVon P t).system.ImplSchritt c s w plans u := by
  obtain ⟨i, kopf, ideal⟩ := h
  have same := (Ast.Semantik.Befehl.ideal_privat i c s w plans u).mp ideal
  obtain ⟨rfl, rfl⟩ := same
  exact ⟨i, kopf, (Ast.Semantik.Befehl.impl_privat i c s w [Ast.Semantik.plan]
    (i.nach c s)).mpr ⟨rfl, rfl⟩⟩

/-- No lock-taking step exists for elaborated units: every plan is the private one. -/
theorem einheitVon_kein_sperre (P : Katalog.Plattform) (t : Ast.Unit)
    {c : Maschine.Kontext} {s u : Ast.Semantik.Zustand} {w : PUnit} {plan : Ast.Semantik.Plan}
    {l : Nat} {a : Maschine.SperrAktion}
    (h : (einheitVon P t).system.ISchritt c s w [plan] u)
    (hsperre : plan.aktion = Maschine.Aktion.sperre l a) : False := by
  obtain ⟨i, _, ideal⟩ := h
  have same := (Ast.Semantik.Befehl.ideal_privat i c s w [plan] u).mp ideal
  have hplan : plan = Ast.Semantik.plan := (List.cons.inj same.1).1
  subst hplan
  cases hsperre

/-- Every ready context of an elaborated unit offers a complete protocol step. -/
theorem einheitVon_bereit_vollzug (P : Katalog.Plattform) (t : Ast.Unit)
    {c : Maschine.Kontext} {s : Ast.Semantik.Zustand} (tick : Nat)
    (h : Maschine.I.Bereit (E := einheitVon P t) s c) :
    ∃ w plan u spur s', (einheitVon P t).system.ImplSchritt c s w [plan] u ∧
      Maschine.FuehrtSchrittAus (einheitVon P t).einrichtung tick c s u plan spur s' := by
  obtain ⟨w, plans, u, ischritt⟩ := h
  obtain ⟨i, kopf, ideal⟩ := ischritt
  have same := (Ast.Semantik.Befehl.ideal_privat i c s w plans u).mp ideal
  obtain ⟨rfl, rfl⟩ := same
  refine ⟨w, Ast.Semantik.plan, i.nach c s, ⟨[], []⟩, i.nach c s, ⟨i, kopf, ?_⟩, ?_⟩
  · exact (Ast.Semantik.Befehl.impl_privat i c s w [Ast.Semantik.plan]
      (i.nach c s)).mpr ⟨rfl, rfl⟩
  · exact Ast.Semantik.Befehl.vollzug _ i tick c s

/-- Every context the elaborated unit dispatches runs on a valid core, as does every
    saved preemption: only the entry context starts dispatched (on its assigned core),
    deliveries name valid cores, crashes reset to core zero. -/
theorem einheitVon_dispatch_gueltig (P : Katalog.Plattform) (t : Ast.Unit)
    {H : Katalog.Umgebung} {ρ : Maschine.Lauf (einheitVon P t)}
    (lauf : Maschine.Laeufe (einheitVon P t) H ρ)
    {η : Maschine.I.Lauf (einheitVon P t)} (valid : Maschine.I.Laeufe (einheitVon P t) η)
    (matched : Maschine.I.Laufabgleich ρ η)
    {tick : Nat} {s : Ast.Semantik.Zustand} :
    ρ.zeit.zustand tick = some s →
    (∀ k c, (s.kerne k).laeuft = some c → k < H.kernzahl) ∧
    (∀ k v n, (v, n) ∈ (s.kerne k).stapel → ∀ c, v = some c → k < H.kernzahl) := by
  have konform : ρ.hw.konform (einheitVon P t).katalog H := lauf.2.1
  have zul := lauf.2.2.1
  have hw := lauf.1
  have hbild : (einheitVon P t).bild.entries = [0] := rfl
  obtain ⟨k₀, assign0⟩ := zul.2.2.1 0 (by rw [hbild]; decide)
  have k0lt : k₀ < H.kernzahl := (zul.2.2.2.1 0 k₀ assign0).2
  -- The canonical initial state dispatches the entry context on its assigned core only.
  have startkerne : ∀ k c, (((Maschine.I.start (einheitVon P t) ρ.start).2.kerne k).laeuft =
      some c) → k = k₀ := by
    intro k c h
    have hif : (if some k = ρ.start.assignment 0 then some Ast.Semantik.eintritt
        else none) = some c := h
    rw [assign0] at hif
    split at hif with hk
    · exact Option.some.inj hk ▸ rfl
    · cases hif
  have startstapel : ∀ k v n, (v, n) ∈
      ((Maschine.I.start (einheitVon P t) ρ.start).2.kerne k).stapel → False := by
    intro k v n h
    have hempty : ((Maschine.I.start (einheitVon P t) ρ.start).2.kerne k).stapel = [] :=
      rfl
    rw [hempty] at h
    exact List.not_mem_nil h
  -- Recovery dispatches the entry context on core zero with empty stacks.
  have wkern : (einheitVon P t).einrichtung.wiederanlauf.kern = 0 := rfl
  have weintritt : (einheitVon P t).einrichtung.wiederanlauf.eintritt =
      Ast.Semantik.eintritt := rfl
  have key : ∀ n s, ρ.zeit.zustand n = some s →
      (∀ k c, (s.kerne k).laeuft = some c → k < H.kernzahl) ∧
      (∀ k v m, (v, m) ∈ (s.kerne k).stapel → ∀ c, v = some c → k < H.kernzahl) := by
    intro n
    induction n with
    | zero =>
      intro s hs
      obtain ⟨x, hx, bezug⟩ := matched.zustand 0
      have xeq : x = s := Option.some.inj (hx.symm.trans hs)
      subst xeq
      obtain ⟨proto, lokal⟩ := bezug
      have hlokal : (einheitVon P t).lokalerBezug = Eq := rfl
      rw [hlokal] at lokal
      have hstate : s = η.zeit.zustand 0 := by
        have h := proto
        rw [← lokal] at h
        exact h
      have hinit := valid.2.2.2.1
      rw [matched.start] at hinit
      rw [hstate, hinit]
      refine ⟨fun k c h => ?_, fun k v m h c hc => ?_⟩
      · have hkk : k = k₀ := startkerne k c h
        subst hkk
        exact k0lt
      · exact (startstapel k v m h).elim
    | succ n ih =>
      intro s hsucc
      cases htakt : ρ.zeit.takt n with
      | schritt label step =>
        cases hzn : ρ.zeit.zustand n with
        | none => rw [hzn] at step; cases step
        | some z =>
          rw [hzn] at step
          cases hsucc' : ρ.zeit.zustand (n + 1) with
          | none => rw [hsucc'] at step; cases step
          | some s' =>
            rw [hsucc'] at step
            cases step with
            | schritt trans =>
              have seq : s' = s := Option.some.inj (hsucc'.symm.trans hsucc)
              subst seq
              have hz : ρ.zeit.zustand n = some z := hzn
              obtain ⟨ihd, ihs⟩ := ih z hz
            cases trans with
            | kontext _ _ _ aus =>
              obtain ⟨rahmen, _, _, _, aktion, _, seq⟩ := aus
              have ukerne : u.kerne = z.kerne := rahmen.kerne
              have ustack : ∀ k, (u.kerne k).stapel = (z.kerne k).stapel :=
                fun k => congrArg _ (congrArg _ ukerne)
              have skerne : s.kerne = v.kerne := congrArg _ seq
              have sstack : ∀ k, (s.kerne k).stapel = (v.kerne k).stapel :=
                fun k => congrArg _ (congrArg _ seq)
              have ustack : ∀ k, (u.kerne k).stapel = (z.kerne k).stapel :=
                fun k => congrArg _ (congrArg _ ukerne)
              cases aktion with
              | intern =>
                have vuk : v.kerne = u.kerne := rfl
                refine ⟨fun k c h => ?_, fun k w m h c hc => ?_⟩
                · rw [skerne, vuk, ukerne] at h
                  exact ihd k c h
                · rw [sstack, vuk] at h
                  rw [ustack] at h
                  exact ihs k w m h c hc
              | warte =>
                have vuk : v.kerne = u.kerne := rfl
                refine ⟨fun k c h => ?_, fun k w m h c hc => ?_⟩
                · rw [skerne, vuk, ukerne] at h
                  exact ihd k c h
                · rw [sstack, vuk] at h
                  rw [ustack] at h
                  exact ihs k w m h c hc
              | sperre =>
                have vuk : v.kerne = u.kerne := rfl
                refine ⟨fun k c h => ?_, fun k w m h c hc => ?_⟩
                · rw [skerne, vuk, ukerne] at h
                  exact ihd k c h
                · rw [sstack, vuk] at h
                  rw [ustack] at h
                  exact ihs k w m h c hc
              | frage =>
                have vuk : v.kerne = u.kerne := rfl
                refine ⟨fun k c h => ?_, fun k w m h c hc => ?_⟩
                · rw [skerne, vuk, ukerne] at h
                  exact ihd k c h
                · rw [sstack, vuk] at h
                  rw [ustack] at h
                  exact ihs k w m h c hc
              | verbrauche =>
                have vuk : v.kerne = u.kerne := rfl
                refine ⟨fun k c h => ?_, fun k w m h c hc => ?_⟩
                · rw [skerne, vuk, ukerne] at h
                  exact ihd k c h
                · rw [sstack, vuk] at h
                  rw [ustack] at h
                  exact ihs k w m h c hc
              | rueckkehr k' =>
                refine ⟨fun k c h => ?_, fun k w m h c hc => ?_⟩
                · rw [skerne] at h
                  by_cases heq : k = k'
                  · subst heq
                    have hv : v.kerne k' = (u.kerne k').zurueck := by
                      show Function.update _ _ _ _ = _
                      rw [Function.update_self]
                    cases hst : (u.kerne k').stapel with
                    | nil =>
                      have hnone : ((u.kerne k').zurueck).laeuft = none := by
                        rw [hst]
                        rfl
                      rw [hv, hnone] at h
                      cases h
                    | cons top rest =>
                      obtain ⟨w, n⟩ := top
                      have hpop : (v.kerne k').laeuft = w := by
                        rw [hv, hst]
                        rfl
                      rw [hpop] at h
                      have hmem : (w, n) ∈ (u.kerne k').stapel := by
                        rw [hst]
                        exact List.mem_cons_self
                      rw [ustack] at hmem
                      exact ihs k' w n hmem c h
                  · have hsame : v.kerne k = u.kerne k := by
                      show Function.update _ _ _ _ = _
                      rw [Function.update_of_ne heq]
                    rw [hsame, ukerne] at h
                    exact ihd k c h
                · rw [sstack] at h
                  by_cases heq : k = k'
                  · subst heq
                    have hv : v.kerne k' = (u.kerne k').zurueck := by
                      show Function.update _ _ _ _ = _
                      rw [Function.update_self]
                    cases hst : (u.kerne k').stapel with
                    | nil =>
                      have hnil : ((u.kerne k').zurueck).stapel = [] := by
                        rw [hst]
                        rfl
                      rw [hv, hnil] at h
                      exact (List.not_mem_nil h).elim
                    | cons top rest =>
                      have hcons : ((u.kerne k').zurueck).stapel = rest := by
                        rw [hst]
                        rfl
                      rw [hv, hcons] at h
                      have hmem : (w, m) ∈ (u.kerne k').stapel := by
                        rw [hst]
                        exact List.mem_cons_of_mem _ h
                      rw [ustack] at hmem
                      exact ihs k' w m hmem c hc
                  · have hsame : (v.kerne k).stapel = (u.kerne k).stapel := by
                      show (Function.update _ _ _ _).stapel = _
                      rw [Function.update_of_ne heq]
                    rw [hsame, ustack] at h
                    exact ihs k w m h c hc
            | antwort _ arrives =>
              obtain ⟨_, _, _, hstate⟩ := arrives
              have skerne : s.kerne = z.kerne := by
                have h1 : s.kerne = ((z.antwort _).kerne) := congrArg _ hstate
                have h2 : ((z.antwort _).kerne) = z.kerne := rfl
                exact h1.trans h2
              rw [skerne]
              exact ih z hz
            | interrupt _ enters =>
              obtain ⟨k', irq, c', nmi, hoffer, _, _, _, _, _, hstate⟩ := enters
              have hkk : k' < H.kernzahl := (konform.2 n).2.1 k' hoffer
              have skerne : s.kerne =
                  (Maschine.Zustandseintritt z k' id c' nmi).kerne := congrArg _ hstate
              have einkern : ∀ k, (Maschine.Zustandseintritt z k' id c' nmi).kerne k =
                  if k = k' then (z.kerne k').unterbrechen c' nmi else z.kerne k := by
                intro k
                by_cases heq : k = k'
                · subst heq
                  show Function.update _ _ _ _ = _
                  rw [Function.update_self]
                · show Function.update _ _ _ _ = _
                  rw [Function.update_of_ne heq]
              refine ⟨fun k c h => ?_, fun k w m h c hc => ?_⟩
              · rw [skerne, einkern] at h
                by_cases heq : k = k'
                · subst heq
                  simp only [if_true] at h
                  have hdispatch : ((z.kerne k').unterbrechen c' nmi).laeuft = some c' :=
                    rfl
                  rw [hdispatch] at h
                  have : c = c' := Option.some.inj h
                  subst this
                  exact hkk
                · simp only [if_neg heq] at h
                  exact ihd k c h
              · rw [skerne, einkern] at h
                by_cases heq : k = k'
                · subst heq
                  simp only [if_true] at h
                  cases List.mem_cons.mp h with
                  | inl htop =>
                    obtain ⟨rfl, rfl⟩ := Prod.mk.inj htop
                    exact ihd k' c (by rfl ▸ hc)
                  | inr hrest =>
                    exact ihs k' w m hrest c hc
                · simp only [if_neg heq] at h
                  exact ihs k w m h c hc
            | absturz crash =>
              obtain ⟨_, heq⟩ := crash.genau
              have skernew : s.kerne =
                  (z.wiederanlauf (einheitVon P t).einrichtung.wiederanlauf n
                    (Katalog.nachAbsturz z.persistenz)).kerne := congrArg _ heq
              rw [wkern, weintritt] at *
              refine ⟨fun k c h => ?_, fun k w m h c hc => ?_⟩
              · rw [skernew] at h
                have hif : (if k = 0 then some Ast.Semantik.eintritt else none) =
                    some c := h
                split at hif with hk
                · exact hk ▸ hw.kerne
                · cases hif
              · rw [skernew] at h
                have hempty : ((z.wiederanlauf (einheitVon P t).einrichtung.wiederanlauf n
                    (Katalog.nachAbsturz z.persistenz)).kerne k).stapel = [] := rfl
                rw [hempty] at h
                exact (List.not_mem_nil h).elim
      | wartet label eq _ =>
        rw [eq] at hsucc
        exact ih s hsucc
  exact key tick s hz

end Gabbro.Core.Ziel.Korrektheit
