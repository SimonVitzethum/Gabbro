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

/-- A context step keeps the invariant: the rule only changes the lock, never dispatch, masks
    or liveness. -/
theorem e4_kontext_inv {t : Nat} {c : Kontext} {s u v s' : Zustand Unit Unit Unit Unit Bool Unit}
    {plan : SchrittPlan Unit Unit Unit Unit} {sperren : List (Speicher.Etikett Unit Unit)}
    {w : Unit} (hinv : inv4 s) (hreg : e4Regel c s w [plan] u)
    (hF : FuehrtAus E_4.einrichtung t c s u plan.aktion sperren [] v)
    (hziel : s' = {v with graph := s'.graph}) : inv4 s' := by
  rcases hreg with ⟨hs, ⟨⟨_, hss, hpeq, hueq⟩ | ⟨_, hss, hpeq, hueq⟩⟩⟩ |
    ⟨_, hss, hpeq, hueq⟩ | ⟨hpeq, hueq⟩
  · obtain rfl := (List.cons.inj hpeq).1
    subst hueq
    cases hF
    rw [hziel]
    rcases hinv with ⟨hlock, hcrash⟩
    refine ⟨?_, hcrash⟩
    cases hss
    constructor
    · simpa only [SperrZustand.anstellen] using hlock.1
    · intro d hd
      simpa only [SperrZustand.anstellen, List.mem_append] using
        (Or.elim hd hlock.2 (fun hdmem => Or.inr ⟨d, hdmem, hs⟩))
  · obtain rfl := (List.cons.inj hpeq).1
    subst hueq
    cases hF
    rw [hziel]
    rcases hinv with ⟨hlock, hcrash⟩
    refine ⟨?_, hcrash⟩
    obtain ⟨r, _, hnext⟩ := nimmt_inv hss
    rw [← hnext]
    exact ⟨hs, by intro d hd; exact hlock.2 d hd⟩
  · obtain rfl := (List.cons.inj hpeq).1
    subst hueq
    cases hF
    rw [hziel]
    rcases hinv with ⟨hlock, hcrash⟩
    refine ⟨?_, hcrash⟩
    obtain ⟨q, _, hnext⟩ := gibt_abgeben hss
    rw [← hnext]
    cases q with
    | nil =>
      exact ⟨⟨by simp only [SperrZustand.abgeben],
        by simp only [SperrZustand.abgeben]; intro d hd; cases hd⟩, hcrash⟩
    | cons d rest =>
      refine ⟨⟨?_, ?_⟩, hcrash⟩
      · simp only [SperrZustand.abgeben]
        exact hlock.2 d (by simp)
      · intro e he
        simp only [SperrZustand.abgeben] at he ⊢
        exact hlock.2 e he
  · obtain rfl := (List.cons.inj hpeq).1
    subst hueq
    cases hF
    rw [hziel]
    exact hinv

/-- An answer arrival changes only the answer ledgers, never dispatch, masks or locks. -/
theorem e4_antwort_inv {s s' : Zustand Unit Unit Unit Unit Bool Unit}
    {a : AntwortEreignis} (hinv : inv4 s)
    (heq : s' = { s.antwort a with graph := s'.graph }) : inv4 s' := by
  rw [heq]
  simpa only [inv4, lockStatisch4, vorCrash4, nachCrash4, Zustand.antwort] using hinv

/-- A restart empties the lock and dispatches only the non-static entry context. -/
theorem e4_absturz_inv {s s' : Zustand Unit Unit Unit Unit Bool Unit}
    {spur : SchrittSpur Unit Unit} {region w k run t}
    (h : AbsturzSchritt region w k run t s spur s') (hinv : inv4 s) : inv4 s' := by
  have hclear := absturz_leert_schlange (l := ()) h
  refine ⟨⟨?_, ?_⟩, Or.inr ⟨?_, hclear.2, hclear.1⟩⟩
  · rw [hclear.2]
    trivial
  · rw [hclear.1]
    intro c hc
    cases hc
  · intro c hc k'
    obtain ⟨_, rfl⟩ := h.genau
    rcases hc with rfl | rfl | rfl
    · dsimp only [Zustand.wiederanlauf, wEinrichtungGesperrt4, eintritt4]
      by_cases hk' : k' = 0
      · subst k'
        simp only [Function.update_self, KernZustand.laeuft, reduceCtorEq]
      · simp only [Function.update_of_ne hk', KernZustand.laeuft]
    · dsimp only [Zustand.wiederanlauf, wEinrichtungGesperrt4, eintritt4]
      by_cases hk' : k' = 0
      · subst k'
        simp only [Function.update_self, KernZustand.laeuft, reduceCtorEq]
      · simp only [Function.update_of_ne hk', KernZustand.laeuft]
    · dsimp only [Zustand.wiederanlauf, wEinrichtungGesperrt4, eintritt4]
      by_cases hk' : k' = 0
      · subst k'
        simp only [Function.update_self, KernZustand.laeuft, reduceCtorEq]
      · simp only [Function.update_of_ne hk', KernZustand.laeuft]

/-- One ideal step preserves the invariant. -/
theorem e4_I_schritt_inv {hw : HwLauf} {t : Nat}
    {s : Zustand Unit Unit Unit Unit Bool Unit}
    {ev : SchrittWahl Unit × SchrittSpur Unit Unit} {s' : Zustand Unit Unit Unit Unit Bool Unit}
    (hinv : inv4 s)
    (step : I.Schritt E_4.einrichtung E_4.system E_4.katalog hw t s ev s') : inv4 s' := by
  cases step with
  | @kontext _ u plan spur c w _ _ hreg haus =>
    obtain ⟨_, _, _, v, hF, _, hziel⟩ := haus
    obtain ⟨_, _, hreg4⟩ := hreg
    exact e4_kontext_inv hinv hreg4 hF hziel
  | antwort _ h =>
    obtain ⟨_, _, _, heq⟩ := h
    exact e4_antwort_inv hinv heq
  | interrupt _ h =>
    obtain ⟨k, irq, c, nmi, _, _, hnimm, _, _, hstate⟩ := h
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
    · rw [hstate]
      refine ⟨⟨?_, ?_⟩, Or.inr ⟨?_, ?_, ?_⟩⟩
      · simpa only [Zustandseintritt] using hinv.1.1
      · simpa only [Zustandseintritt, List.mem_append] using hinv.1.2
      · intro d hd k'
        rcases hd with rfl | rfl | rfl
        all_goals
          by_cases hk' : k' = k
          · subst k'
            dsimp only [Zustandseintritt, KernZustand.unterbrechen]
            rw [Function.update_self]
            cases c <;> simp only [Option.some.injEq, reduceCtorEq]
          · rw [Zustandseintritt, Function.update_of_ne hk']
            exact hnach.1 _ (by first | exact statisch4_A | exact statisch4_B | exact statisch4_C4) k'
      · simpa only [Zustandseintritt] using hnach.2.1
      · simpa only [Zustandseintritt] using hnach.2.2
  | absturz h =>
    exact e4_absturz_inv h hinv

/-- The invariant holds on every reachable ideal cut. -/
theorem e4_inv_I (ρ : I.Lauf E_4) (lauf : I.Laeufe E_4 ρ) (t : Nat) :
    inv4 (ρ.zeit.zustand t) := by
  induction t with
  | zero =>
    have h0 := lauf.2.2.2.1
    rw [h0, start_E_4]
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
      rw [hown] at hlock
      exact hlock.1
    have hleb := hvor.2 h hst
    intro _
    have hg : (ρ.zeit.zustand t.val).sperren ().Gibt h ((ρ.zeit.zustand t.val).sperren ()).abgeben := by
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
          exact Gibt.besitzer h schlange
    refine ⟨hleb.1, hleb.2, ?_⟩
    refine ⟨(), wGebenPlan, ρ.zeit.zustand t.val, ?_, rfl, ?_⟩
    · exact e4_ideal_geben hg
    · intro next hnext wechsel
      simp [E_4, wEinrichtungGesperrt4]
  · rw [hnach.2.1] at hown
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
