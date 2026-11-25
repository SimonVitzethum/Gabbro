/-
  File:      Core/Fortschritt/SperrFreigabe.lean
  Subject:   THE PROVED LEGS OF THE RELEASE (MK-05, PERFECT-MODEL §3.7, step M8, Teil 2b).

  What follows from the machine rules and the hold bound alone, without any scheduling
  assumption:
  * a crash-free break of continuous ownership is the holder's release
    (`besitzwechsel_ist_gibt`: only the owner releases, takes need a free lock, tickets
    keep the owner, and answers, interrupts and pauses preserve every lock);
  * the conditional release (`sperr_freigabe_bedingt`): if the holder accumulates `H + 1`
    own steps, one of them is the release — otherwise ownership never breaks and
    `HalteSchranken` bounds the cost;
  * the universal fairness premise is unsatisfiable (`faire_umgebung_nicht_eindeutig`):
    widening the core count keeps admissibility but breaks `kerneSchreiten`, so the
    substantive reading pins one fair environment.
  The scheduling step itself — that the holder is actually stepped — is the missing
  premise named at `SperrFreigabeAussage` in `SperrFair`, not proved here.
-/
module

public import Core.Fortschritt.SperrErhalt

@[expose] public section

namespace Gabbro.Core.Fortschritt

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog
open Gabbro.Core.Beobachtung

variable {L Ort Wert Raum Lok Grund Bedingung Wahl F : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F}

/-- A machine tick from a loaded state reaches a loaded state: pauses keep the state,
    protocol steps go from `some` to `some` by construction of `Lauffolge`. -/
theorem lauffolge_bleibt_some {ρ : Maschine.Lauf E} {t : Nat}
    {sm : Zustand L Ort Wert Raum Lok Grund}
    {spur : SchrittWahl Wahl × SchrittSpur Ort Wert}
    {next : Option (Zustand L Ort Wert Raum Lok Grund)}
    (h : Lauffolge E ρ.hw t (some sm) spur next) : ∃ s', next = some s' := by
  cases h with
  | schritt _ => exact ⟨_, rfl⟩

/-- A break of continuous ownership without a crash is the holder's release: only the
    owner releases (`Gibt` needs the owner), a take needs a free lock, a ticket keeps the
    owner, and answers, interrupts and pauses preserve every lock (`lauf_schritt_sperren`). -/
theorem besitzwechsel_ist_gibt {ρ : Maschine.Lauf E} {l : L} {h : Kontext} {k : Nat}
    {sk s : Zustand L Ort Wert Raum Lok Grund}
    (hzk : ρ.zeit.zustand k = some sk) (hzk1 : ρ.zeit.zustand (k + 1) = some s)
    (hfrei : ρ.zeit.spur k ≠ some (.absturz, absturzSpur))
    (hvor : (sk.sperren l).besitzer = some h) (hnach : (s.sperren l).besitzer ≠ some h) :
    ∃ next, (sk.sperren l).Gibt h next ∧ s.sperren l = next := by
  rcases lauf_schritt_sperren hzk hzk1 hfrei with heq | ⟨a, d, next, hss, hvn⟩
  · exfalso
    apply hnach
    rw [heq, hvor]
  · cases hss with
    | ticket =>
      exfalso
      apply hnach
      rw [hvn]
      exact hvor
    | nehmen hN =>
      have hnone := hN.besitzt.2
      rw [hnone] at hvor
      simp only [reduceCtorEq] at hvor
    | geben hG =>
      have hown := hG.besitzt
      have heq2 : d = h := Option.some.inj (hown.symm.trans hvor)
      subst heq2
      exact ⟨next, hG, hvn⟩

/-- **The conditional release (MK-05, proved leg of `SperrFreigabeAussage`)**: on a
    crash-free run, if the holder accumulates `H + 1` own steps from `b`, one of them is
    the release — otherwise ownership never breaks and `HalteSchranken` bounds the cost
    by `H`. The first break of ownership is the release (`besitzwechsel_ist_gibt`), and
    the window before it is continuously owned, so the cost there is at most `H + 1`.
    The unconditional conclusion additionally needs the holder to be scheduled — that
    progress premise (`I`-`Laufabgleich` with starvation freedom) is the missing step
    named at `SperrFreigabeAussage`, not proved here. -/
theorem sperr_freigabe_bedingt {ρ : Maschine.Lauf E} {l : L} {h : Kontext} {H b : Nat}
    (hhalten : E.schranken.halten l = some H)
    (hhalte : HalteSchranken E ρ)
    (hcrash : ∀ k, b ≤ k → ρ.zeit.spur k ≠ some (.absturz, absturzSpur))
    {s : Zustand L Ort Wert Raum Lok Grund} (hown : ρ.zeit.zustand b = some s)
    (hbes : (s.sperren l).besitzer = some h)
    {n : Nat} (hcost : H + 1 ≤ Kontextkosten ρ h b n) :
    ∃ r, b ≤ r ∧ r < b + n ∧
      (∃ s₁ s₂, ρ.zeit.zustand r = some s₁ ∧ ρ.zeit.zustand (r + 1) = some s₂ ∧
        (s₁.sperren l).Gibt h (s₂.sperren l)) ∧
      Kontextkosten ρ h b (r + 1 - b) ≤ H + 1 := by
  classical
  have hsome : ∀ t, b ≤ t → ∃ s', ρ.zeit.zustand t = some s' := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact ⟨s, hown⟩
    | succ m hm ih =>
      obtain ⟨sm, hsm⟩ := ih
      have htakt := ρ.zeit.takt m
      rw [hsm] at htakt
      cases htakt with
      | wartet _ heq _ => exact ⟨sm, heq⟩
      | schritt _ step =>
        obtain ⟨s', hs'⟩ := lauffolge_bleibt_some step
        exact ⟨s', hs'⟩
  have hex : ∃ t, b ≤ t ∧ t ≤ b + n ∧
      ∀ s', ρ.zeit.zustand t = some s' → (s'.sperren l).besitzer ≠ some h := by
    by_contra hcon
    have hcont : ∀ t, b ≤ t → t < b + n →
        ∃ s', ρ.zeit.zustand t = some s' ∧ (s'.sperren l).besitzer = some h := by
      intro t hbt htn
      by_contra hc
      push_neg at hc
      exact hcon ⟨t, hbt, by omega, hc⟩
    have hle : Kontextkosten ρ h b n ≤ H :=
      hhalte l h b n hcont H hhalten
    omega
  set t₀ := Nat.find hex with ht0def
  have hspec := Nat.find_spec hex
  rw [← ht0def] at hspec
  obtain ⟨hb0, hbn0, hbr0⟩ := hspec
  have hmin : ∀ t, t < t₀ →
      ¬(b ≤ t ∧ t ≤ b + n ∧
        ∀ s', ρ.zeit.zustand t = some s' → (s'.sperren l).besitzer ≠ some h) :=
    fun t ht => Nat.find_min hex ht
  have htb : b < t₀ := by
    rcases eq_or_lt_of_le hb0 with heq | hlt
    · exfalso
      rw [← heq] at hbr0
      exact hbr0 s hown hbes
    · exact hlt
  have hown_at : ∀ t, b ≤ t → t < t₀ → ∀ s', ρ.zeit.zustand t = some s' →
      (s'.sperren l).besitzer = some h := by
    intro t hbt htt s' hs'
    have hnot : ¬ ∀ s'', ρ.zeit.zustand t = some s'' →
        (s''.sperren l).besitzer ≠ some h :=
      fun hall => hmin t htt ⟨hbt, by omega, hall⟩
    by_contra hne
    apply hnot
    intro s'' hs''
    have heq : s'' = s' := Option.some.inj (hs''.symm.trans hs')
    subst heq
    exact hne
  set r := t₀ - 1 with hrdef
  have hr1 : r + 1 = t₀ := by omega
  have hbr : b ≤ r := by omega
  obtain ⟨sr, hsr⟩ := hsome r hbr
  have hownr : (sr.sperren l).besitzer = some h :=
    hown_at r hbr (by omega) sr hsr
  obtain ⟨st, hst⟩ := hsome t₀ (by omega)
  have hne0 : (st.sperren l).besitzer ≠ some h := hbr0 st hst
  have hzk1 : ρ.zeit.zustand (r + 1) = some st := hr1 ▸ hst
  obtain ⟨next, hg, hvn⟩ := besitzwechsel_ist_gibt hsr hzk1 (hcrash r hbr) hownr hne0
  have hcont' : ∀ t, b ≤ t → t < b + (r + 1 - b) →
      ∃ s', ρ.zeit.zustand t = some s' ∧ (s'.sperren l).besitzer = some h := by
    intro t hbt htt
    obtain ⟨s', hs'⟩ := hsome t hbt
    exact ⟨s', hs', hown_at t hbt (by omega) s' hs'⟩
  have hle : Kontextkosten ρ h b (r + 1 - b) ≤ H :=
    hhalte l h b (r + 1 - b) hcont' H hhalten
  have hg' : (sr.sperren l).Gibt h (st.sperren l) := by
    rw [hvn]
    exact hg
  exact ⟨r, hbr, by omega, ⟨sr, st, hsr, hzk1, hg'⟩, by omega⟩

/-- **Fairness over all admissible environments is unsatisfiable (MK-05 finding)**:
    widening the core count preserves admissibility (`Laeufe`: hardware validity,
    conformance, start admission and the loaded start only constrain the offered cores
    from above) but breaks hardware fairness (`kerneSchreiten` demands every core be
    offered). Hence a premise of the shape `∀ h', Laeufe E h' ρ → FairLaeufe …` never
    holds on an admissible run — the old `SperrFreigabeAussage` was vacuously true, and
    `halte_gibt_nicht_ab` (existential fairness) never engaged it. The substantive
    reading pins one fair environment (`∃ h', Laeufe E h' ρ ∧ FairLaeufe …`); the
    refutation `sperr_freigabe_ohne_abschnitt_widerlegt` uses that shape. -/
theorem faire_umgebung_nicht_eindeutig {ρ : Maschine.Lauf E} {h : Umgebung}
    (hrun : Laeufe E h ρ) :
    ¬ ∀ h', Laeufe E h' ρ → FairLaeufe E.katalog h' ρ.hw := by
  intro hall
  let K := h.kernzahl + 1
  let h' : Umgebung := { h with kernzahl := K }
  have hkern : 0 < K := Nat.zero_lt_succ _
  have hwiden : ∀ core, core < h.kernzahl → core < K := fun _ hc =>
    Nat.lt_trans hc (Nat.lt_succ_self _)
  have hhard : Hardware E.katalog h' := { hrun.1 with kerne := hkern }
  have hkonf : ρ.hw.konform E.katalog h' := by
    refine ⟨hrun.2.1.1, fun i => ?_⟩
    obtain ⟨hcore, hint, hsig, hdel, hmed⟩ := hrun.2.1.2 i
    refine ⟨fun core hc => hwiden _ (hcore core hc),
      fun core hc => hwiden _ (hint core hc), fun signal hmem => ?_, hdel, hmed⟩
    have hsg := hsig signal hmem
    cases signal with
    | erhoben kern irq =>
      exact ⟨hwiden _ hsg.1, hsg.2⟩
    | zustellen kern id irq =>
      exact ⟨hwiden _ hsg.1, hsg.2.1, hsg.2.2.1, hsg.2.2.2.1, hsg.2.2.2.2.1,
        hsg.2.2.2.2.2⟩
  have hzul : E.ZulStart h' ρ.start := by
    obtain ⟨hbild, hboot, hexists, hassign, hgetrennt, hphys, hbytes, haussen⟩ := hrun.2.2.1
    exact ⟨hbild, hwiden _ hboot, hexists,
      fun i c hc => ⟨(hassign i c hc).1, hwiden _ (hassign i c hc).2⟩,
      hgetrennt, hphys, hbytes, haussen⟩
  have hinit : ρ.zeit.zustand 0 = E.laden ρ.start (h'.lade E.bild) := hrun.2.2.2
  have hrun' : Laeufe E h' ρ := ⟨hhard, hkonf, hzul, hinit, hrun.2.2.2.2⟩
  have hfair := hall h' hrun'
  obtain ⟨i, _, hi⟩ := hfair.kerne.2 h.kernzahl (Nat.lt_succ_self _) 0
  have hlt := (hrun.2.1.2 i).1 h.kernzahl hi
  exact absurd hlt (Nat.lt_irrefl _)

end Gabbro.Core.Fortschritt
