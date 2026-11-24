/-
  File:      Core/Fortschritt/SperrGegenbeispiel.lean
  Subject:   HOLD BOUNDS DO NOT IMPLY RELEASE (PERFECT-MODEL §3.7, step M8, Teil 2b): the
              counterexample the design brief asks for.

  `E_h` is `E_1` with one lock held by a stuck holder `H` that never steps and never releases.
  On the fair two-core schedule `hw2`, two other contexts stutter forever; the lock never moves.
  The run is admissible (`lauf_h`) on a fair history (`fair2`), satisfies `HalteSchranken`
  (`eh_halte`: the holder takes no own steps, nobody else ever owns), declares hold bound five
  (`eh_halten`) — and no release step ever occurs. Hence no `hgibt`-shaped conclusion follows
  from `HalteSchranken` plus hardware fairness alone (`halte_gibt_nicht_ab`).

  The missing model rule is a checker-side release obligation for lock holders (B13 remainder):
  an accepted unit must keep a holder live, dispatched and release-enabled until it hands the
  lock off. It is pinned as `SperrFreigabeAussage` in `SperrFair`.
-/
module

public import Core.Fortschritt.SperrErhalt
public import Core.Fortschritt.WarteBeispiel

@[expose] public section

namespace Gabbro.Core.Fortschritt

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog
open Gabbro.Core.Beobachtung

/-- The stuck holder: never dispatched, never steps, never releases. -/
def stuckHalter : Kontext := .faden 2

/-- The held start state: `E_1`'s start with the lock owned by the stuck holder. -/
def sH0 : Zustand Unit Unit Unit Unit Bool Unit :=
  { zE0 with sperren := fun _ => ⟨some stuckHalter, []⟩ }

/-- The stuck-holder unit: `E_1` with the held start loaded. -/
def E_h : Einheit Unit Unit Unit Unit Bool Unit Unit Unit Unit :=
  { E_1 with laden := fun _ _ => some sH0 }

theorem eh_halten : E_h.schranken.halten () = some 5 := rfl

theorem wBild_format : wBild.format = .elf := rfl

theorem wBild_bytes : wBild.bytes = fun a => if a = 0 then some 0 else none := rfl

theorem wBild_entries : wBild.entries = [0] := rfl

/-- `wBild` is a valid image for the x86-64 platform. -/
theorem wBild_gueltig : wBild.gueltig E_1.katalog.plattform.ziel := by
  have hplat : E_1.katalog.plattform = Plattform.x86_64 := rfl
  rw [hplat]
  refine ⟨(ziele_gut _).2.2.2.2.2.2.2.2.2, ?_, ?_⟩
  · intro a v h
    rw [wBild_bytes] at h
    have h' : (if a = 0 then some (0 : UInt8) else none) = some v := h
    by_cases ha : a = 0
    · subst ha
      exact pow_pos (by decide : (0 : Nat) < 2) _
    · rw [if_neg ha] at h'
      nomatch h'
  · intro entry hmem
    rw [wBild_entries, List.mem_singleton] at hmem
    subst hmem
    exact ⟨0, rfl⟩

noncomputable def s_h : AussenStart :=
  Classical.choose (zulStart_erfuellbar fair2.hardware wBild_gueltig)

def zul_h : Katalog.ZulStart Plattform.x86_64.katalog h2 wBild s_h :=
  Classical.choose_spec (zulStart_erfuellbar fair2.hardware wBild_gueltig)

def spur_h (t : Nat) : Option (SchrittWahl Unit × SchrittSpur Unit Unit) :=
  if t % 2 = 0 then some posLabel else some bLabel

theorem sH0_dispatch0 : (sH0.kerne 0).laeuft = some A := rfl

theorem sH0_dispatch1 : (sH0.kerne 1).laeuft = some B := rfl

theorem sH0_live : ∀ c, sH0.status c = .laeuft := fun _ => rfl

def takt_h (t : Nat) : Takt (Lauffolge E_h hw2) (KeinSchritt (Lauffolge E_h hw2))
    t (some sH0) (spur_h t) (some sH0) := by
  by_cases h : t % 2 = 0
  · have hsp : spur_h t = some posLabel := by simp only [spur_h, if_pos h]
    rw [hsp]
    exact .schritt rfl (.schritt (ImplSchritt.kontext (hw2_crash t)
      ⟨0, hw2_opp0 h, sH0_dispatch0, sH0_live _⟩
      ⟨(), rfl, Or.inr ⟨rfl, rfl⟩⟩
      (e1StotterAusfuehr t A sH0)))
  · have h1 : t % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one t with h0 | h1
      · exact (h h0).elim
      · exact h1
    have hsp : spur_h t = some bLabel := by simp only [spur_h, if_neg h]
    rw [hsp]
    exact .schritt rfl (.schritt (ImplSchritt.kontext (hw2_crash t)
      ⟨1, hw2_opp1 h1, sH0_dispatch1, sH0_live _⟩
      ⟨(), rfl, Or.inr ⟨rfl, rfl⟩⟩
      (e1StotterAusfuehr t B sH0)))

noncomputable def ρ_h : Maschine.Lauf E_h :=
  ⟨s_h, hw2, ⟨fun _ => some sH0, spur_h, takt_h⟩⟩

/-- The stuck run is admissible. -/
theorem lauf_h : Laeufe E_h h2 ρ_h :=
  ⟨fair2.hardware, fair2.konform, zul_h, rfl⟩

/-- The lock stays with the stuck holder at every cut. -/
theorem eh_besitzer (t : Nat) (s : Zustand Unit Unit Unit Unit Bool Unit) (l : Unit)
    (hzs : ρ_h.zeit.zustand t = some s) : (s.sperren l).besitzer = some stuckHalter := by
  have hss : s = sH0 := Option.some.inj (hzs.symm.trans rfl)
  subst hss
  cases l
  rfl

/-- The lock state never changes. -/
theorem eh_lock (t : Nat) (s : Zustand Unit Unit Unit Unit Bool Unit) (l : Unit)
    (hzs : ρ_h.zeit.zustand t = some s) :
    s.sperren l = ⟨some stuckHalter, []⟩ := by
  have hss : s = sH0 := Option.some.inj (hzs.symm.trans rfl)
  subst hss
  cases l
  rfl

/-- An everywhere-false marker fills no window. -/
theorem zaehle_null (m : Nat → Bool) (a n : Nat) (hall : ∀ t, m (a + t) = false) :
    I.zaehle m a n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hrec : I.zaehle m a (n + 1) =
        I.zaehle m a n + (if m (a + n) then 1 else 0) := rfl
    have hif : (if m (a + n) then (1 : Nat) else 0) = 0 := by
      rw [hall n]
      exact if_neg (by decide)
    rw [hrec, hif]
    omega

/-- The stuck holder takes no own steps. -/
theorem eh_kosten_null (a n : Nat) : Kontextkosten ρ_h stuckHalter a n = 0 := by
  unfold Kontextkosten
  apply zaehle_null
  intro t
  have hsp : ρ_h.zeit.spur (a + t) = some posLabel ∨
      ρ_h.zeit.spur (a + t) = some bLabel := by
    by_cases h : (a + t) % 2 = 0
    · left
      show spur_h (a + t) = some posLabel
      simp only [spur_h, if_pos h]
    · right
      show spur_h (a + t) = some bLabel
      simp only [spur_h, if_neg h]
  rcases hsp with hsp | hsp
  · rw [hsp]
    rfl
  · rw [hsp]
    rfl

/-- The stuck run meets every hold bound. -/
theorem eh_halte : HalteSchranken E_h ρ_h := by
  intro l c a n hcont H' hH
  have h5 : E_h.schranken.halten l = some 5 := by cases l; rfl
  have hH5 : H' = 5 := Option.some.inj (hH.symm.trans h5)
  subst hH5
  by_cases hcH : c = stuckHalter
  · subst hcH
    have hcost := eh_kosten_null a n
    omega
  · by_cases hn0 : n = 0
    · subst hn0
      have hcost : Kontextkosten ρ_h c a 0 = 0 := rfl
      omega
    · have hlt : a < a + n := by omega
      obtain ⟨s, hzs, hown⟩ := hcont a (Nat.le_refl _) hlt
      have hownH := eh_besitzer a s l hzs
      rw [hownH] at hown
      exact absurd (Option.some.inj hown) (Ne.symm hcH)

/-- No release step ever occurs on the stuck run. -/
theorem eh_kein_gibt (r : Nat) (s₁ s₂ : Zustand Unit Unit Unit Unit Bool Unit)
    (hr1 : ρ_h.zeit.zustand r = some s₁) (hr2 : ρ_h.zeit.zustand (r + 1) = some s₂)
    (h : Kontext) : ¬ (s₁.sperren ()).Gibt h (s₂.sperren ()) := by
  intro hg
  have e1 := eh_lock r s₁ () hr1
  have e2 := eh_lock (r + 1) s₂ () hr2
  have hne := gibt_wechselt hg
  exact hne (by rw [e1, e2])

/-- Hold bounds plus hardware fairness do not imply release: the stuck holder keeps its lock
    forever on an admissible fair run, so no `hgibt`-shaped conclusion follows. -/
theorem halte_gibt_nicht_ab :
    ∃ (E : Einheit Unit Unit Unit Unit Bool Unit Unit Unit Unit) (h : Umgebung)
      (ρ : Maschine.Lauf E) (l : Unit) (hh : Kontext) (H : Nat) (b : Nat)
      (s : Zustand Unit Unit Unit Unit Bool Unit),
      Laeufe E h ρ ∧ FairLaeufe E.katalog h ρ.hw ∧ HalteSchranken E ρ ∧
      E.schranken.halten l = some H ∧ ρ.zeit.zustand b = some s ∧
      (s.sperren l).besitzer = some hh ∧
      ¬ ∃ r, b ≤ r ∧ (∃ s₁ s₂, ρ.zeit.zustand r = some s₁ ∧
        ρ.zeit.zustand (r + 1) = some s₂ ∧
        (s₁.sperren l).Gibt hh (s₂.sperren l)) ∧
        Kontextkosten ρ hh b (r + 1 - b) ≤ H + 1 := by
  refine ⟨E_h, h2, ρ_h, (), stuckHalter, 5, 0, sH0, lauf_h, fair2, eh_halte,
    eh_halten, rfl, rfl, ?_⟩
  rintro ⟨r, _, ⟨s₁, s₂, hr1, hr2, hg⟩, _⟩
  exact eh_kein_gibt r s₁ s₂ hr1 hr2 _ hg

end Gabbro.Core.Fortschritt
