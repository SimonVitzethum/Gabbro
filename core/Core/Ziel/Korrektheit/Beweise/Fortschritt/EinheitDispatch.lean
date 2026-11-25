/-
  File:      core/Core/Ziel/Korrektheit/Beweise/Fortschritt/EinheitDispatch.lean
  Subject:   DISPATCH DISCIPLINE OF ELABORATED UNITS — core validity and uniqueness on every
             matched run.

  On an implementation run matched to an ideal run, every elaborated unit dispatches each
  context on a valid core (`einheitVon_dispatch_gueltig`): only the entry context starts
  dispatched (on its assigned core), context steps and answers preserve all cores, an interrupt
  enters on a valid core, and a crash resets to core zero. Moreover every matched ideal run
  keeps a strict dispatch discipline (`einheitVon_dispatch_eindeutig`): a dispatched context
  is live, and no context is dispatched on two cores — context steps and answers preserve
  cores and status, an interrupt enters a resting context, and a crash resets to the single
  entry dispatch. Transported to the implementation run (`einheitVon_dispatch_eindeutig_rho`),
  this pins down every preemption analysis in `VerdraengungKonstanz.lean`.
-/
module

public import Core.Ziel.Korrektheit.Beweise.Fortschritt.EinheitLaeufe

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core
open Gabbro.Core.Maschine

/-- Every context the elaborated unit dispatches runs on a valid core, as does every
    saved preemption: only the entry context starts dispatched (on its assigned core),
    deliveries name valid cores, crashes reset to core zero. -/
theorem einheitVon_dispatch_gueltig (P : Katalog.Plattform) (t : Ast.Unit)
    {H : Katalog.Umgebung} {ρ : Maschine.Lauf (einheitVon P t)}
    (lauf : Maschine.Laeufe (einheitVon P t) H ρ)
    {η : Maschine.I.Lauf (einheitVon P t)} (valid : Maschine.I.Laeufe (einheitVon P t) η)
    (matched : Maschine.I.Laufabgleich ρ η)
    {tick : Nat} {s : Ast.Semantik.Zustand} (hz : ρ.zeit.zustand tick = some s) :
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
    by_cases hk : some k = some k₀
    · exact Option.some.inj hk
    · rw [if_neg hk] at hif
      cases hif
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
      obtain ⟨proto, lokal⟩ := bezug
      have hlokal : (einheitVon P t).lokalerBezug = Eq := rfl
      rw [hlokal] at lokal
      have hstate : s = η.zeit.zustand 0 := by
        have hxstate : x = η.zeit.zustand 0 := by
          unfold Maschine.I.ProtokollBezug at proto
          rw [← lokal] at proto
          exact proto
        rw [← xeq]
        exact hxstate
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
        | none =>
          rw [hzn] at step
          cases step
        | some z =>
          rw [hzn] at step
          cases hsucc' : ρ.zeit.zustand (n + 1) with
          | none =>
            rw [hsucc'] at step
            cases step
          | some s' =>
            rw [hsucc'] at step
            cases step with
            | schritt trans =>
              have seq : s = s' := Option.some.inj (hsucc.symm.trans hsucc')
              subst seq
              have hz : ρ.zeit.zustand n = some z := hzn
              obtain ⟨ihd, ihs⟩ := ih z hz
              cases trans with
              | @kontext _ u plan spur _ _ _ _ regel aus =>
                obtain ⟨kerneEq, _⟩ := einheitVon_kontext_erhaelt_impl P t regel aus
                refine ⟨fun k c h => ?_, fun k w m h c hc => ?_⟩
                · rw [kerneEq] at h
                  exact ihd k c h
                · rw [kerneEq] at h
                  exact ihs k w m h c hc
              | @antwort _ _ a_ev _ arrives =>
                obtain ⟨_, _, _, hstate⟩ := arrives
                have skerne : s.kerne = z.kerne := by
                  have h1 : s.kerne = ((z.antwort a_ev).kerne) := by rw [hstate]
                  have h2 : ((z.antwort a_ev).kerne) = z.kerne := rfl
                  exact h1.trans h2
                rw [skerne]
                exact ih z hz
              | @interrupt _ _ id_ev _ enters =>
                obtain ⟨k', irq, c', nmi, hoffer, _, _, _, _, _, hstate⟩ := enters
                have hkk : k' < H.kernzahl := (konform.2 n).2.1 k' hoffer
                have skerne : s.kerne =
                    (Maschine.Zustandseintritt z k' id_ev c' nmi).kerne := by
                  have h := congrArg (fun (x : Ast.Semantik.Zustand) => x.kerne) hstate
                  exact h
                have einkern : ∀ k, (Maschine.Zustandseintritt z k' id_ev c' nmi).kerne k =
                    if k = k' then (z.kerne k').unterbrechen c' nmi else z.kerne k := by
                  intro k
                  by_cases heq : k = k'
                  · rw [heq]
                    show Function.update _ _ _ _ = _
                    rw [Function.update_self, if_pos rfl]
                  · show Function.update _ _ _ _ = _
                    rw [Function.update_of_ne heq, if_neg heq]
                refine ⟨fun k c h => ?_, fun k w m h c hc => ?_⟩
                · rw [skerne, einkern] at h
                  by_cases heq : k = k'
                  · subst k
                    simp only [if_true] at h
                    have hdispatch : ((z.kerne k').unterbrechen c' nmi).laeuft
                        = some c' := rfl
                    rw [hdispatch] at h
                    have hc' : c' = c := Option.some.inj h
                    subst hc'
                    exact hkk
                  · simp only [if_neg heq] at h
                    exact ihd k c h
                · rw [skerne, einkern] at h
                  by_cases heq : k = k'
                  · subst k
                    simp only [if_true] at h
                    cases List.mem_cons.mp h with
                    | inl htop =>
                      obtain ⟨rfl, rfl⟩ := Prod.mk.inj htop
                      exact ihd k' c hc
                    | inr hrest =>
                      exact ihs k' w m hrest c hc
                  · simp only [if_neg heq] at h
                    exact ihs k w m h c hc
              | absturz crash =>
                obtain ⟨_, heq⟩ := crash.genau
                have skernew : s.kerne =
                    (z.wiederanlauf (einheitVon P t).einrichtung.wiederanlauf n
                      (Maschine.nachAbsturz z.persistenz)).kerne := congrArg _ heq
                rw [wkern, weintritt] at *
                refine ⟨fun k c h => ?_, fun k w m h c hc => ?_⟩
                · rw [skernew] at h
                  have hif : (if k = 0 then some Ast.Semantik.eintritt else none) =
                      some c := h
                  by_cases hk : k = 0
                  · subst hk
                    exact hw.kerne
                  · rw [if_neg hk] at hif
                    cases hif
                · rw [skernew] at h
                  have hempty : ((z.wiederanlauf (einheitVon P t).einrichtung.wiederanlauf n
                      (Maschine.nachAbsturz z.persistenz)).kerne k).stapel = [] := rfl
                  rw [hempty] at h
                  exact (List.not_mem_nil h).elim
      | wartet label eq _ =>
        rw [eq] at hsucc
        exact ih s hsucc
  exact key tick s hz

/-- Dispatch discipline of every matched ideal run of every elaborated unit: a
    dispatched context is live, and no context is dispatched on two cores. The
    induction follows every ideal transition; context steps and answers
    preserve cores and status, an interrupt enters a resting context, and a
    crash resets to the single entry dispatch. -/
theorem einheitVon_dispatch_eindeutig (P : Katalog.Plattform) (t : Ast.Unit)
    {ρ : Maschine.Lauf (einheitVon P t)}
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

/-- The implementation run inherits the dispatch discipline through the matched
    ideal state: dispatched contexts are live, and no context runs on two cores. -/
theorem einheitVon_dispatch_eindeutig_rho (P : Katalog.Plattform) (t : Ast.Unit)
    {H : Katalog.Umgebung} {ρ : Maschine.Lauf (einheitVon P t)}
    (lauf : Maschine.Laeufe (einheitVon P t) H ρ)
    {η : Maschine.I.Lauf (einheitVon P t)} (valid : Maschine.I.Laeufe (einheitVon P t) η)
    (matched : Maschine.I.Laufabgleich ρ η) :
    (∀ tick s c k, ρ.zeit.zustand tick = some s → (s.kerne k).laeuft = some c →
      s.status c = .laeuft) ∧
    (∀ tick s c k₁ k₂, ρ.zeit.zustand tick = some s → (s.kerne k₁).laeuft = some c →
      (s.kerne k₂).laeuft = some c → k₁ = k₂) := by
  obtain ⟨hlive, hsingle⟩ := einheitVon_dispatch_eindeutig P t valid matched
  refine ⟨?_, ?_⟩
  · intro tick s c k hs h
    have heq : s = η.zeit.zustand tick :=
      einheitVon_zustand_gleich P t matched tick s hs
    rw [heq] at h ⊢
    exact hlive tick c k h
  · intro tick s c k₁ k₂ hs h₁ h₂
    have heq : s = η.zeit.zustand tick :=
      einheitVon_zustand_gleich P t matched tick s hs
    rw [heq] at h₁ h₂
    exact hsingle tick c k₁ k₂ h₁ h₂

end Gabbro.Core.Ziel.Korrektheit
