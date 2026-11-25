/-
  File:      core/Core/Ziel/Korrektheit/Beweise/Fortschritt/VerdraengungKonstanz.lean
  Subject:   DISPATCH CONSTANCY FROM THE RETURN PREMISE — no re-dispatch, no displacement,
             one core.

  On an open suffix (`BleibtOffen`, dev form: dispatched once, head/live/undischarged
  throughout) no transition re-dispatches an absent live context (`einheitVon_kein_wiedereinsatz`):
  context steps and answers preserve all cores, an interrupt enters a resting handler, and a
  crash is excluded by crash-freedom. Hence a displacement of a live context from its core
  (`einheitVon_keine_verdraengung`) is impossible under the return premise
  `VerdraengungKehrtZurueck`: the demanded strictly later return would start with a
  re-dispatch. The dispatch core therefore never changes on the suffix
  (`einheitVon_dispatch_konstant_neu`), and scheduler fairness applies to it.
-/
module

public import Core.Ziel.Korrektheit.Beweise.Fortschritt.EinheitDispatch

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core
open Gabbro.Core.Maschine

/-- A live context that is nowhere dispatched stays nowhere dispatched across one tick:
    context steps and answers preserve all cores, an interrupt enters a resting handler
    (never the live context), and a crash is excluded on the open suffix. -/
theorem einheitVon_kein_wiedereinsatz (P : Katalog.Plattform) (t : Ast.Unit)
    {H : Katalog.Umgebung} {ρ : Maschine.Lauf (einheitVon P t)}
    (lauf : Maschine.Laeufe (einheitVon P t) H ρ)
    {η : Maschine.I.Lauf (einheitVon P t)} (valid : Maschine.I.Laeufe (einheitVon P t) η)
    (matched : Maschine.I.Laufabgleich ρ η)
    {a : Nat} {c : Maschine.Kontext} {f : Ast.Semantik.Befehl}
    (opened : Maschine.I.BleibtOffen η c f a)
    (crashfrei : ∀ t', a ≤ t' → (ρ.hw.angebot t').crash = false)
    (u : Nat) (hu : a ≤ u) (zminus zplus : Ast.Semantik.Zustand)
    (hzminus : ρ.zeit.zustand u = some zminus) (hzplus : ρ.zeit.zustand (u + 1) = some zplus)
    (weg : ∀ k, (zminus.kerne k).laeuft ≠ some c) (k : Maschine.Kern) :
    (zplus.kerne k).laeuft ≠ some c := by
  have live : zminus.status c = .laeuft := by
    have hlive : (η.zeit.zustand u).status c = .laeuft := (opened.2 u hu).2.1
    have heq : zminus = η.zeit.zustand u :=
      einheitVon_zustand_gleich P t matched u zminus hzminus
    rw [heq] at hlive
    exact hlive
  cases htakt : ρ.zeit.takt u with
  | schritt label step =>
    cases step with
    | schritt trans =>
      cases trans with
      | @kontext _ w plan spur _ _ _ _ regel aus =>
        obtain ⟨kerneEq, _⟩ := einheitVon_kontext_erhaelt_impl P t regel aus
        intro hk
        rw [kerneEq] at hk
        exact weg k hk
      | @antwort _ _ a_ev _ arrives =>
        obtain ⟨_, _, _, hstate⟩ := arrives
        obtain ⟨kerneEq, _⟩ := einheitVon_antwort_erhaelt hstate
        intro hk
        rw [kerneEq] at hk
        exact weg k hk
      | @interrupt _ _ id_ev _ enters =>
        obtain ⟨k', irq, c', nmi, _, _, _, dormant, _, _, hstate⟩ := enters
        have hne : c' ≠ c := by
          intro hcc
          rw [hcc] at dormant
          rw [live] at dormant
          cases dormant
        have skerne : zplus.kerne =
            (Maschine.Zustandseintritt zminus k' id_ev c' nmi).kerne := by
          have h := congrArg (fun (x : Ast.Semantik.Zustand) => x.kerne) hstate
          have hseq : zplus =
              ({Maschine.Zustandseintritt zminus k' id_ev c' nmi with
                graph := zplus.graph} : Ast.Semantik.Zustand) := hstate
          have hkerne : ({Maschine.Zustandseintritt zminus k' id_ev c' nmi with
              graph := zplus.graph} : Ast.Semantik.Zustand).kerne =
              (Maschine.Zustandseintritt zminus k' id_ev c' nmi).kerne := rfl
          rw [hseq, hkerne]
          exact h
        have einkern : ∀ k, (Maschine.Zustandseintritt zminus k' id_ev c' nmi).kerne k =
            if k = k' then (zminus.kerne k').unterbrechen c' nmi else zminus.kerne k := by
          intro k
          by_cases heq : k = k'
          · rw [heq]
            show Function.update _ _ _ _ = _
            rw [Function.update_self, if_pos rfl]
          · show Function.update _ _ _ _ = _
            rw [Function.update_of_ne heq, if_neg heq]
        intro hk
        rw [skerne, einkern] at hk
        by_cases heq : k = k'
        · subst heq
          simp only [if_true] at hk
          have hdispatch : ((zminus.kerne k').unterbrechen c' nmi).laeuft
              = some c' := rfl
          rw [hdispatch] at hk
          exact hne (Option.some.inj hk)
        · simp only [if_neg heq] at hk
          exact weg k hk
      | absturz crash =>
        obtain ⟨offer, _, _⟩ := crash
        have hc := crashfrei u hu
        rw [offer.2] at hc
        cases hc
  | wartet label eq _ =>
    have hseq : zplus = zminus := Option.some.inj eq
    intro hk
    rw [hseq] at hk
    exact weg k hk

/-- No interrupt displaces a live dispatched context from its core under the return
    premise: the displacement would vacate the core, while the demanded strictly later
    return starts with a re-dispatch, which the previous lemma excludes. The step data is
    taken unpacked so the caller can name the step core. -/
theorem einheitVon_keine_verdraengung (P : Katalog.Plattform) (t : Ast.Unit)
    {H : Katalog.Umgebung} {ρ : Maschine.Lauf (einheitVon P t)}
    (lauf : Maschine.Laeufe (einheitVon P t) H ρ)
    {η : Maschine.I.Lauf (einheitVon P t)} (valid : Maschine.I.Laeufe (einheitVon P t) η)
    (matched : Maschine.I.Laufabgleich ρ η)
    {a : Nat} {c : Maschine.Kontext} {f : Ast.Semantik.Befehl}
    (opened : Maschine.I.BleibtOffen η c f a)
    (crashfrei : ∀ t', a ≤ t' → (ρ.hw.angebot t').crash = false)
    (ret : Maschine.VerdraengungKehrtZurueck (einheitVon P t) ρ)
    (d : Nat) (hd : a ≤ d) (k : Maschine.Kern)
    (s : Ast.Semantik.Zustand) (hs : ρ.zeit.zustand d = some s)
    (hdis : (s.kerne k).laeuft = some c)
    {id : Nat × Nat} {spur : Maschine.SchrittSpur Ast.Semantik.Zelle Int}
    {spost : Ast.Semantik.Zustand}
    (hsplus : ρ.zeit.zustand (d + 1) = some spost)
    (hspur : ρ.zeit.spur d = some (.interrupt id, spur))
    (kstep : Maschine.Kern) (hkk : kstep = k)
    (irq : Katalog.Unterbrechung) (cstep : Maschine.Kontext) (nmi : Bool)
    (dormant : s.status cstep = .ruht)
    (hstate : spost = {Maschine.Zustandseintritt s kstep id cstep nmi with
      graph := spost.graph}) :
    False := by
  subst hkk
  have live : s.status c = .laeuft := by
    have hlive : (η.zeit.zustand d).status c = .laeuft := (opened.2 d hd).2.1
    have heq : s = η.zeit.zustand d :=
      einheitVon_zustand_gleich P t matched d s hs
    rw [heq] at hlive
    exact hlive
  obtain ⟨hliveρ, hsingleρ⟩ := einheitVon_dispatch_eindeutig_rho P t lauf valid matched
  have hne : cstep ≠ c := by
    intro hcc
    rw [hcc] at dormant
    rw [live] at dormant
    cases dormant
  -- The post-state vacates the core: the handler runs there, nothing else moved.
  have nowhere : ∀ k'', (spost.kerne k'').laeuft ≠ some c := by
    have skerne : spost.kerne =
        (Maschine.Zustandseintritt s kstep id cstep nmi).kerne := by
      have hkerne : ({Maschine.Zustandseintritt s kstep id cstep nmi with
          graph := spost.graph} : Ast.Semantik.Zustand).kerne =
          (Maschine.Zustandseintritt s kstep id cstep nmi).kerne := rfl
      rw [hstate, hkerne]
    have einkern : ∀ k, (Maschine.Zustandseintritt s kstep id cstep nmi).kerne k =
        if k = kstep then (s.kerne kstep).unterbrechen cstep nmi else s.kerne k := by
      intro k
      by_cases heq : k = kstep
      · rw [heq]
        show Function.update _ _ _ _ = _
        rw [Function.update_self, if_pos rfl]
      · show Function.update _ _ _ _ = _
        rw [Function.update_of_ne heq, if_neg heq]
    intro k'' hk''
    rw [skerne, einkern] at hk''
    by_cases heq : k'' = kstep
    · subst heq
      simp only [if_true] at hk''
      have hdispatch : ((s.kerne kstep).unterbrechen cstep nmi).laeuft
          = some cstep := rfl
      rw [hdispatch] at hk''
      exact hne (Option.some.inj hk'')
    · simp only [if_neg heq] at hk''
      have hkk'' : k'' = k := hsingleρ d s c k'' k hs hk'' hdis
      exact heq (hkk''.trans rfl)
  -- The return premise fires on the displacement and gives a first return.
  obtain ⟨r, hr, kret, zret, hzret, hret⟩ :=
    ret c k d ⟨s, hs, hdis, live⟩ ⟨id, spur, hspur⟩
  classical
  have hex : ∃ u, d < u ∧ ∃ k''', ∃ z''', ρ.zeit.zustand u = some z''' ∧
      (z'''.kerne k''').laeuft = some c :=
    ⟨r, hr, kret, zret, hzret, hret⟩
  have first := Nat.find_spec hex
  have min := Nat.find_min' hex
  have hle : d + 1 ≤ Nat.find hex := first.1
  obtain ⟨kfst, zfst, hzfst, hfst⟩ := first.2
  rcases Nat.eq_or_lt_of_le hle with h | h
  · -- The return is immediate: against the vacated post-state.
    have hseq : zfst = spost := Option.some.inj (hzfst.symm.trans hsplus)
    have hfind : Nat.find hex = d + 1 := h.symm
    rw [hfind] at hzfst
    rw [hseq] at hfst
    exact nowhere kfst hfst
  · -- The return is later: the tick before is still vacated, against no re-dispatch.
    have hprev : d < Nat.find hex - 1 := by omega
    have hneg : ¬ (d < Nat.find hex - 1 ∧ ∃ k''', ∃ z''', ρ.zeit.zustand (Nat.find hex - 1) =
        some z''' ∧ (z'''.kerne k''').laeuft = some c) := by
      intro hcon
      have hle := min _ hcon
      omega
    have hle1 : a ≤ Nat.find hex - 1 := Nat.le_trans hd (Nat.le_of_lt hprev)
    obtain ⟨zprev, hzprev⟩ := matched.zustand (Nat.find hex - 1)
    have weg : ∀ k''', (zprev.kerne k''').laeuft ≠ some c := by
      intro k''' hk'''
      exact hneg ⟨hprev, k''', zprev, hzprev, hk'''⟩
    have hsucc : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    have hzplus : ρ.zeit.zustand (Nat.find hex - 1 + 1) = some zfst := hsucc ▸ hzfst
    have hcontra := einheitVon_kein_wiedereinsatz P t lauf valid matched
      opened crashfrei (Nat.find hex - 1) hle1 zprev zfst hzprev hzplus weg kfst
    exact hcontra hfst

/-- On the open suffix the dispatch core never changes: context steps and answers
    preserve all cores, a crash is excluded, and an interrupt on the context's own
    core is excluded by the previous lemma. -/
theorem einheitVon_dispatch_konstant_neu (P : Katalog.Plattform) (t : Ast.Unit)
    {H : Katalog.Umgebung} {ρ : Maschine.Lauf (einheitVon P t)}
    (lauf : Maschine.Laeufe (einheitVon P t) H ρ)
    {η : Maschine.I.Lauf (einheitVon P t)} (valid : Maschine.I.Laeufe (einheitVon P t) η)
    (matched : Maschine.I.Laufabgleich ρ η)
    {a : Nat} {c : Maschine.Kontext} {f : Ast.Semantik.Befehl}
    (opened : Maschine.I.BleibtOffen η c f a)
    (crashfrei : ∀ t', a ≤ t' → (ρ.hw.angebot t').crash = false)
    (ret : Maschine.VerdraengungKehrtZurueck (einheitVon P t) ρ) :
    ∃ k, ∀ t' (ht' : a ≤ t') (s : Ast.Semantik.Zustand),
      ρ.zeit.zustand t' = some s → (s.kerne k).laeuft = some c := by
  obtain ⟨hliveρ, hsingleρ⟩ := einheitVon_dispatch_eindeutig_rho P t lauf valid matched
  obtain ⟨sa, hsa⟩ := matched.zustand a
  have hseq_a : sa = η.zeit.zustand a :=
    einheitVon_zustand_gleich P t matched a sa hsa
  obtain ⟨k₀, hk₀η⟩ := opened.1
  have hk₀ : (sa.kerne k₀).laeuft = some c := hseq_a ▸ hk₀η
  refine ⟨k₀, fun t' ht' => ?_⟩
  have key : ∀ m, a ≤ m → ∀ s, ρ.zeit.zustand m = some s →
      (s.kerne k₀).laeuft = some c := by
    intro m hm
    refine Nat.le_induction (P := fun m => ∀ s, ρ.zeit.zustand m = some s →
      (s.kerne k₀).laeuft = some c) ?base ?step hm
    · intro s hs_a
      have hsa_eq : sa = s := Option.some.inj (hsa.symm.trans hs_a)
      obtain ⟨k₁, hk₁⟩ := opened.1
      have hk₁ρ : (sa.kerne k₁).laeuft = some c := hseq_a ▸ hk₁
      have hkk : k₁ = k₀ := hsingleρ a sa c k₁ k₀ hsa hk₁ρ hk₀
      subst hkk
      rw [← hsa_eq]
      exact hk₀
    · intro m hm ih s' hs'
      obtain ⟨z, hz⟩ := matched.zustand m
      have ihz : (z.kerne k₀).laeuft = some c := ih z hz
      cases htakt : ρ.zeit.takt m with
      | schritt label step =>
        cases step with
        | schritt trans =>
          cases trans with
          | @kontext _ w plan spur _ _ _ _ regel aus =>
            obtain ⟨kerneEq, _⟩ := einheitVon_kontext_erhaelt_impl P t regel aus
            rw [kerneEq]
            exact ihz
          | @antwort _ _ a_ev _ arrives =>
            obtain ⟨_, _, _, hstate⟩ := arrives
            obtain ⟨kerneEq, _⟩ := einheitVon_antwort_erhaelt hstate
            rw [kerneEq]
            exact ihz
          | @interrupt _ _ id_ev _ enters =>
            obtain ⟨k', irq, c', nmi, _hoffer, _haus, _nimmt, dormant,
              _haussen, _hmem, hstate⟩ := enters
            by_cases heq : k₀ = k'
            · subst heq
              have hspur := label
              exact (einheitVon_keine_verdraengung P t lauf valid matched
                opened crashfrei ret m hm k₀ z hz ihz hs'
                hspur k₀ rfl irq c' nmi dormant hstate).elim
            · have skerne : s'.kerne =
                  (Maschine.Zustandseintritt z k' id_ev c' nmi).kerne := by
                have h := congrArg (fun (x : Ast.Semantik.Zustand) => x.kerne) hstate
                have hkerne : ({Maschine.Zustandseintritt z k' id_ev c' nmi with
                    graph := s'.graph} : Ast.Semantik.Zustand).kerne =
                    (Maschine.Zustandseintritt z k' id_ev c' nmi).kerne := rfl
                have hseq : s' =
                    ({Maschine.Zustandseintritt z k' id_ev c' nmi with
                      graph := s'.graph} : Ast.Semantik.Zustand) := hstate
                rw [hseq, hkerne]
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
              have hsame : (s'.kerne k₀) = (z.kerne k₀) := by
                rw [skerne, einkern, if_neg heq]
              rw [hsame]
              exact ihz
          | absturz crash =>
            obtain ⟨offer, _, _⟩ := crash
            have hc := crashfrei m hm
            rw [offer.2] at hc
            cases hc
      | wartet label eq _ =>
        have hseq : s' = z := Option.some.inj eq
        rw [hseq]
        exact ihz
  exact key t' ht'

end Gabbro.Core.Ziel.Korrektheit
