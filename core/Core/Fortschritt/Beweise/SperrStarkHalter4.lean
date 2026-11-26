/-
  File:      Core/Fortschritt/Beweise/SperrStarkHalter.lean
  Subject:   GLOBAL HOLDER ELIGIBILITY for the non-vacuous hand-over unit (M8 2b).

  The invariant says: the lock only ever contains statically dispatched contexts; before a
  restart every vector is masked, an NMI is active and A, B, C stay live and dispatched; after a
  restart none of A, B, C is dispatched and the lock is empty. Therefore every reachable holder
  is live, dispatched and release-offering, on EVERY ideal cut, not only on the witness run.
-/
module

public import Core.Fortschritt.Beweise.SperrStarkEinheit4

@[expose] public section

namespace Gabbro.Core.Fortschritt

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog
open Gabbro.Core.Annahme
open Gabbro.Core.Beobachtung

/-- The lock only ever mentions statically dispatched contexts. -/
def lockStatisch4 (s : Zustand Unit Unit Unit Unit Bool Unit) : Prop :=
  (match (s.sperren ()).besitzer with
   | none => True
   | some h => statisch4 h) ∧
  ∀ c ∈ (s.sperren ()).schlange, statisch4 c

/-- Before a restart: no preemption and all three contexts live and dispatched. -/
def vorCrash4 (s : Zustand Unit Unit Unit Unit Bool Unit) : Prop :=
  (∀ k, (s.kerne k).nmiAktiv = true ∧ (s.kerne k).maske = fun _ => true) ∧
  ∀ c, statisch4 c → s.status c = .laeuft ∧ ∃ k, (s.kerne k).laeuft = some c

/-- After a restart: the entry context is outside the dispatched set and the lock is empty. -/
def nachCrash4 (s : Zustand Unit Unit Unit Unit Bool Unit) : Prop :=
  (∀ c, statisch4 c → ∀ k, (s.kerne k).laeuft ≠ some c) ∧
  (∀ k, (s.kerne k).maske = fun _ => true) ∧
  (s.sperren ()).besitzer = none ∧ (s.sperren ()).schlange = []

def inv4 (s : Zustand Unit Unit Unit Unit Bool Unit) : Prop :=
  lockStatisch4 s ∧ (vorCrash4 s ∨ nachCrash4 s)

theorem inv4_start : inv4 s4_ideal0 := by
  refine ⟨?_, Or.inl ?_⟩
  · refine ⟨?_, ?_⟩
    · rw [s4_ideal0_lock]
      trivial
    · intro c hc
      rw [s4_ideal0_schlange] at hc
      cases hc
  · refine ⟨?_, ?_⟩
    · intro k
      exact ⟨s4_ideal0_nmi k, s4_ideal0_maske k⟩
    · intro c hc
      rcases hc with rfl | rfl | rfl
      · exact ⟨s4_ideal0_live A, ⟨0, s4_ideal0_kerne0⟩⟩
      · exact ⟨s4_ideal0_live B, ⟨1, s4_ideal0_kerne1⟩⟩
      · exact ⟨s4_ideal0_live C4, ⟨2, s4_ideal0_kerne2⟩⟩

theorem vorCrash4_von {s u : Zustand Unit Unit Unit Unit Bool Unit}
    (hstatus : u.status = s.status) (hkerne : u.kerne = s.kerne)
    (hvor : vorCrash4 s) : vorCrash4 u := by
  dsimp only [vorCrash4] at hvor ⊢
  rw [hstatus, hkerne]
  exact hvor

theorem lockStatisch4_von {s u : Zustand Unit Unit Unit Unit Bool Unit}
    (hsperren : u.sperren = s.sperren) (hlock : lockStatisch4 s) : lockStatisch4 u := by
  dsimp only [lockStatisch4] at hlock ⊢
  rw [hsperren]
  exact hlock

theorem lockStatisch4_sperr {s : Zustand Unit Unit Unit Unit Bool Unit} {c : Kontext}
    {next : SperrZustand} {a : SperrAktion} (hlock : lockStatisch4 s) (hs : statisch4 c)
    (hss : SperrSchritt a c (s.sperren ()) next) :
    lockStatisch4 {s with sperren := Function.update s.sperren () next} := by
  dsimp only [lockStatisch4] at hlock ⊢
  cases hss with
  | ticket =>
    simp only [Function.update_self, SperrZustand.anstellen, List.mem_append, List.mem_singleton]
    exact ⟨hlock.1, fun d hd => Or.elim hd hlock.2 (fun hdc => hdc ▸ hs)⟩
  | nehmen hn =>
    obtain ⟨r, hs0, hnext⟩ := nimmt_inv hn
    rw [← hnext]
    simp only [Function.update_self]
    exact ⟨hs, hlock.2⟩
  | geben hg =>
    obtain ⟨q, hs0, hnext⟩ := gibt_abgeben hg
    rw [← hnext]
    cases q with
    | nil => simp only [SperrZustand.abgeben, Function.update_self]
    | cons d rest =>
      simp only [SperrZustand.abgeben, Function.update_self]
      exact ⟨hlock.2 d (by simp [hs0]), fun e he => hlock.2 e (by simp [hs0, he])⟩

/-- A context step keeps the invariant: the rule only changes the lock, never dispatch, masks
    or liveness; after a crash no static context is dispatched, so no rule can fire. -/
theorem e4_kontext_inv {hw : HwLauf} {t : Nat} {c : Kontext}
    {s u v s' : Zustand Unit Unit Unit Unit Bool Unit}
    {plan : SchrittPlan Unit Unit Unit Unit} {sperren : List (Speicher.Etikett Unit Unit)}
    {w : Unit} {spur : SchrittSpur Unit Unit} (hinv : inv4 s)
    (bereit : KannSchreiten hw t c s) (hreg : e4Regel c s w [plan] u)
    (hF : FuehrtAus E_4.einrichtung t c s u plan.aktion sperren spur.aussen v)
    (hziel : s' = {v with graph := s'.graph}) : inv4 s' := by
  generalize hev : spur.aussen = evs at hF
  obtain ⟨k, _, hlk, hleb⟩ := bereit
  rcases hinv with ⟨hlock, hcrash⟩
  rcases hreg with hreg | hreg | hreg
  · rcases hreg with ⟨hs, hreg⟩
    rcases hreg with ⟨_, _, hpeq, hueq⟩ | ⟨_, _, hpeq, hueq⟩
    · obtain rfl := (List.cons.inj hpeq).1
      rw [hueq] at hF
      cases hF with
      | sperre hnextF _ =>
        rw [hziel]
        rcases hcrash with hvor | hnach
        · refine ⟨lockStatisch4_sperr hlock hs hnextF, Or.inl ?_⟩
          exact vorCrash4_von (s := s) rfl rfl (vorCrash4_von (s := s) rfl rfl hvor)
        · exact (hnach.1 c hs k hlk).elim
    · obtain rfl := (List.cons.inj hpeq).1
      subst u
      cases hF with
      | sperre hnextF _ =>
        rw [hziel]
        rcases hcrash with hvor | hnach
        · refine ⟨lockStatisch4_sperr hlock hs hnextF, Or.inl ?_⟩
          exact vorCrash4_von (s := s) rfl rfl hvor
        · exact (hnach.1 c hs k hlk).elim
  · rcases hreg with ⟨_, _, hpeq, hueq⟩
    obtain rfl := (List.cons.inj hpeq).1
    subst u
    have hs : statisch4 c := by
      cases hlockstate : (s.sperren ()).besitzer with
      | none =>
        -- the give rule cannot fire on a free lock; this branch is unreachable
        cases hss_dummy : (s.sperren ()) with | mk b q => rw [hlockstate] at hss_dummy; cases b <;> simp at hss_dummy
      | some h =>
        dsimp only [lockStatisch4] at hlock
        rw [hlockstate] at hlock
        exact hlock.1
    cases hF with
    | sperre hnextF _ =>
      rw [hziel]
      rcases hcrash with hvor | hnach
      · refine ⟨lockStatisch4_sperr hlock hs hnextF, Or.inl ?_⟩
        exact vorCrash4_von (s := s) rfl rfl hvor
      · exact (hnach.1 c hs k hlk).elim
  · rcases hreg with ⟨hpeq, hueq⟩
    obtain rfl := (List.cons.inj hpeq).1
    subst u
    cases hF with
    | intern =>
      rw [hziel]
      refine ⟨hlock, ?_⟩
      rcases hcrash with hvor | hnach
      · exact Or.inl (vorCrash4_von (s := s) rfl rfl hvor)
      · exact Or.inr ⟨by intro d hd k'; simpa only using hnach.1 d hd k', hnach.2.2.1, hnach.2.2.2⟩

/-- An answer arrival changes only the answer ledgers, never dispatch, masks or locks. -/
theorem e4_antwort_inv {s s' : Zustand Unit Unit Unit Unit Bool Unit}
    {a : AntwortEreignis} (hinv : inv4 s)
    (heq : s' = { s.antwort a with graph := s'.graph }) : inv4 s' := by
  rw [heq]
  simpa only [inv4, lockStatisch4, vorCrash4, nachCrash4, Zustand.antwort] using hinv

/-- A restart empties the lock and dispatches only the non-static entry context. -/
theorem e4_absturz_inv {s s' : Zustand Unit Unit Unit Unit Bool Unit}
    {spur : SchrittSpur Unit Unit} {run k t}
    (h : AbsturzSchritt E_4.einrichtung.persistenzRegion E_4.einrichtung.wiederanlauf k run t
      s spur s') (hinv : inv4 s) : inv4 s' := by
  have hclear := absturz_leert_schlange (l := ()) h
  refine ⟨⟨by rw [hclear.2]; trivial, by rw [hclear.1]; intro c hc; cases hc⟩, Or.inr ⟨?_, ?_, hclear.2, hclear.1⟩⟩
  · intro k
    obtain ⟨_, rfl⟩ := h.genau
    simp [Zustand.wiederanlauf, wEinrichtungGesperrt4, wDatenGesperrt4, dispatch4, E_4]
  · intro c hc k'
    obtain ⟨_, rfl⟩ := h.genau
    rcases hc with rfl | rfl | rfl
  all_goals
    by_cases hk' : k' = 0
    · subst k'
      simp [Zustand.wiederanlauf, wEinrichtungGesperrt4, eintritt4, E_4, A, B, C4]
    · simp [Zustand.wiederanlauf, wEinrichtungGesperrt4, eintritt4, E_4, A, B, C4,
        Function.update_of_ne hk']

/-- One ideal step preserves the invariant. -/
theorem e4_I_schritt_inv {hw : HwLauf} {t : Nat}
    {s : Zustand Unit Unit Unit Unit Bool Unit}
    {ev : SchrittWahl Unit × SchrittSpur Unit Unit} {s' : Zustand Unit Unit Unit Unit Bool Unit}
    (hinv : inv4 s)
    (step : I.Schritt E_4.einrichtung E_4.system E_4.katalog hw t s ev s') : inv4 s' := by
  cases step with
  | @kontext _ u plan spur c w _ _ hreg haus =>
    obtain ⟨_, bereit, _, v, hF, _, hziel⟩ := haus
    obtain ⟨_, _, hreg4⟩ := hreg
    exact e4_kontext_inv (w := w) hinv bereit hreg4 hF hziel
  | antwort _ h =>
    obtain ⟨_, _, _, heq⟩ := h
    exact e4_antwort_inv hinv heq
  | interrupt _ h =>
    obtain ⟨k, irq, c, nmi, _, _, hnimm, _, _, _, hstate⟩ := h
    rcases hinv.2 with hvor | hnach
    · exfalso
      have hnmi : (s.kerne k).nmiAktiv = true := (hvor.1 k).1
      have hmaske : (s.kerne k).maske = fun _ => true := (hvor.1 k).2
      cases hnimm with
      | handler can _ =>
        have hfalsch : (s.kerne k).maske _ = false := can.1
        rw [hmaske] at hfalsch
        cases hfalsch
      | nmi can _ =>
        change (s.kerne k).nmiAktiv = false at can
        rw [hnmi] at can
        cases can
    · have hsperren : s'.sperren = (Zustandseintritt s k id c nmi).sperren := by
        rw [hstate]
        rfl
      have hkerne : s'.kerne = (Zustandseintritt s k id c nmi).kerne := by
        rw [hstate]
        rfl
      refine ⟨?_, Or.inr ⟨?_, ?_, ?_⟩⟩
      · rw [hsperren]
        simpa only [Zustandseintritt] using hinv.1
      · intro d hd k'
        rw [hkerne]
        dsimp only [Zustandseintritt, KernZustand.unterbrechen]
        by_cases hk' : k' = k
        · subst k'
          rw [Function.update_self]
          cases hnimm with
          | handler can _ =>
            have hfalsch : (s.kerne k).maske _ = false := can.1
            rw [hnach.2.1 k] at hfalsch
            cases hfalsch
          | nmi _ _ => simp only [Option.some.injEq, reduceCtorEq]
        · rw [Function.update_of_ne hk']
          exact hnach.1 d hd k'
      · rw [hsperren]
        simpa only [Zustandseintritt] using hnach.2.2.2.1
      · rw [hsperren]
        simpa only [Zustandseintritt] using hnach.2.2.2
  | absturz h =>
    exact e4_absturz_inv h hinv

/-- The invariant holds on every reachable ideal cut. -/
theorem e4_inv_I (ρ : I.Lauf E_4) (lauf : I.Laeufe E_4 ρ) (t : Nat) :
    inv4 (ρ.zeit.zustand t) := by
  induction t with
  | zero =>
    have h0 := lauf.2.2.2.1
    rw [h0]
    change inv4 s4_ideal0
    exact inv4_start
  | succ t ih =>
    cases ρ.zeit.takt t with
    | wartet heq _ =>
      rw [heq]
      exact ih
    | schritt _ step =>
      exact e4_I_schritt_inv ih step

/-- Global holder eligibility on every ideal cut. -/
theorem e4_halter : SperrHalterHalten E_4 := by
  intro ρ lauf t l h hown
  cases l
  have hi := e4_inv_I ρ lauf t.val
  rcases hi with ⟨hlock, hvor | hnach⟩
  · have hst : statisch4 h := by
      dsimp only [lockStatisch4] at hlock
      rw [hown] at hlock
      exact hlock.1
    have hleb := hvor.2 h hst
    intro _
    have hg : SperrZustand.Gibt ((ρ.zeit.zustand t.val).sperren ()) h (((ρ.zeit.zustand t.val).sperren ()).abgeben) := by
      cases hlockstate : (ρ.zeit.zustand t.val).sperren () with
      | mk besitzer schlange =>
        cases besitzer with
        | none =>
          rw [hlockstate] at hown
          cases hown
        | some h' =>
          have hh' : h' = h := by
            rw [hlockstate] at hown
            injection hown
          subst hh'
          exact SperrZustand.Gibt.besitzer h schlange
    refine ⟨hleb.1, hleb.2, ?_⟩
    refine ⟨(), wGebenPlan, ρ.zeit.zustand t.val, ?_, rfl, ?_⟩
    · exact e4_ideal_geben hg
    · intro next hnext wechsel
      simp [E_4, wEinrichtungGesperrt4]
  · rw [hnach.2.2.1] at hown
    cases hown

theorem waechter_E_4 : WaechterHalten E_4 :=
  ⟨fun ρ _ t op args h => by
      dsimp [kanonischeVerwendung, E_4, Quelltabellen.leer] at h
      exact h.elim,
    fun ρ _ t hC => by
      obtain ⟨C, hC⟩ := hC
      obtain ⟨c, hc⟩ := hC.1
      obtain ⟨b, hblock, _, _, _⟩ := hC.2 c hc
      exact hblock,
    e4_halter⟩

theorem akzeptiert_E_4 : Akzeptiert E_4 :=
  ⟨⟨Plattform.x86_64.katalog_wohlgeformt, e4_regel_lokal,
     ⟨Gabbro.Core.Aussen.zulassung_m2 _, e4_aussen_gueltig⟩, e4_fluss,
     e4_schranken_lokal, e4_sec, e4_domaenen⟩, e4_klauseln, waechter_E_4⟩

end Gabbro.Core.Fortschritt
