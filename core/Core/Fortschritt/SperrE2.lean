/-
  File:      Core/Fortschritt/SperrE2.lean
  Subject:   THE HANDOVER UNIT AND RUN (PERFECT-MODEL §3.7, step M8, Teil 2b): `E_2`
              extends the ticket rule of `E_1` with takes and releases; `ρ_2` hands the
              lock from `A` to nobody on a crash-free fair schedule. The release is a
              release-to-nobody, so its single memory event is a non-reading write and the
              memory side closes without read reasoning. The tail stutters `A` and `B`
              alternately, so both step infinitely often.
-/
module

public import Core.Fortschritt.SperrFair
public import Core.Katalog.Start

@[expose] public section

namespace Gabbro.Core.Fortschritt

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog
open Gabbro.Core.Annahme
open Gabbro.Core.Beobachtung

/-- A counting window never exceeds its length. -/
theorem zaehle_le (m : Nat → Bool) (a n : Nat) : I.zaehle m a n ≤ n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    by_cases hm : m (a + n) = true
    · simp only [I.zaehle, if_pos hm]
      omega
    · simp only [I.zaehle, if_neg hm, Nat.add_zero]
      exact Nat.le_trans ih (Nat.le_succ _)

def nehmenPlan : SchrittPlan Unit Unit Unit Unit :=
  { wGebenPlan with aktion := .sperre () .nehmen }

/-- The handover rule: tickets, takes and releases as the `SperrSchritt` allows, plus an
    unconditional stutter. Implementation and ideal rule coincide. -/
def e2Regel (c : Kontext) (s : Zustand Unit Unit Unit Unit Bool Unit) (w : Unit)
    (es : List (SchrittPlan Unit Unit Unit Unit)) (u : Zustand Unit Unit Unit Unit Bool Unit) :
    Prop :=
  (∃ next, SperrSchritt .ticket c (s.sperren ()) next ∧ es = [ticketPlan] ∧
    u = toggleUpdate c s) ∨
  (∃ next, SperrSchritt .nehmen c (s.sperren ()) next ∧ es = [nehmenPlan] ∧ u = s) ∨
  (∃ next, SperrSchritt .geben c (s.sperren ()) next ∧ es = [wGebenPlan] ∧ u = s) ∨
  (es = [stutterPlan] ∧ u = s)

def e2System : MaschinenSystem Unit Unit Unit Unit Bool Unit Unit Unit Unit :=
  ⟨fun _ => ⟨e2Regel, e2Regel⟩, fun _ _ => some (), fun _ _ => False, fun _ _ _ => False⟩

/-- The release cut: the holder owns the lock, everything else is the `E_1` start. -/
def s2_0 : Zustand Unit Unit Unit Unit Bool Unit :=
  { zE0 with sperren := fun _ => ⟨some A, []⟩ }

def E_2 : Einheit Unit Unit Unit Unit Bool Unit Unit Unit Unit :=
  { E_1 with system := e2System, laden := fun _ _ => some s2_0 }

theorem e2halten : E_2.schranken.halten () = some 5 := rfl

theorem e2_sec : AbschnittWartefrei E_2 :=
  abschnittWartefrei_ohne_blockade _ fun _ _ _ hb => hb

theorem s2_0_lock : (s2_0.sperren ()) = ⟨some A, []⟩ := rfl

theorem s2_0_kerne0 : (s2_0.kerne 0).laeuft = some A := rfl

theorem s2_0_live : ∀ c, s2_0.status c = .laeuft := fun _ => rfl

theorem s2_0_graph_gut : s2_0.graph.graph.Konsistent ∧ s2_0.graph.graph.Vollstaendig :=
  ⟨Speicher.Zustand.leer_konsistent, Speicher.Zustand.leer_vollstaendig⟩

/-- A non-reading write appends to any consistent complete prefix, with or without a
    prior write at its location. -/
theorem schreiben_folge {g : SpeicherGraph Unit Unit} (hk : g.graph.Konsistent)
    (hv : g.graph.Vollstaendig) (x : Unit) :
    ∃ es g', Speicherfolge (fun _ => ()) (SpeicherAkteur.kontext A) g
      [⟨.schreiben, x, .ra, (), ()⟩] es g' := by
  have hmem : (Speicher.Art.schreiben ≠ Speicher.Art.aussen) := by decide
  by_cases hq : HatQuelle g x
  · obtain ⟨g', hs⟩ := Speicher.Zustand.schritt_ohne_lesen hk hv
      (SpeicherAkteur.kontext A) ⟨.schreiben, x, .ra, (), ()⟩ (fun h => h.elim)
    exact ⟨_, _, .cons (.ohne (Or.inr hq)) hs (.nil _)⟩
  · obtain ⟨gmid, hs_init⟩ := Speicher.Zustand.schritt_ohne_lesen hk hv
      (SpeicherAkteur.initial x) ⟨.schreiben, x, .ra, (), ()⟩ (fun h => h.elim)
    have hz : Initialisierung (fun _ => ()) ⟨.schreiben, x, .ra, (), ()⟩ g
        [((SpeicherAkteur.initial x), ⟨.schreiben, x, .ra, (), ()⟩)] gmid :=
      .erste hmem hq hs_init
    have gut := hz.viele.gut hk hv
    obtain ⟨g', hs⟩ := Speicher.Zustand.schritt_ohne_lesen gut.1 gut.2
      (SpeicherAkteur.kontext A) ⟨.schreiben, x, .ra, (), ()⟩ (fun h => h.elim)
    exact ⟨_, _, .cons hz hs (.nil _)⟩

noncomputable def g2_wit : ∃ es g', Speicherfolge (fun _ => ()) (SpeicherAkteur.kontext A)
    s2_0.graph [⟨.schreiben, (E_2.einrichtung.sperrOrt ()), .ra, (), ()⟩] es g' :=
  schreiben_folge s2_0_graph_gut.1 s2_0_graph_gut.2 _

noncomputable def g2_es : List (SpeicherAkteur Unit × Speicher.Etikett Unit Unit) :=
  Classical.choose g2_wit

noncomputable def g2_g : SpeicherGraph Unit Unit :=
  Classical.choose (Classical.choose_spec g2_wit)

theorem g2_mem : Speicherfolge (fun _ => ()) (SpeicherAkteur.kontext A) s2_0.graph
    [⟨.schreiben, (E_2.einrichtung.sperrOrt ()), .ra, (), ()⟩] g2_es g2_g :=
  Classical.choose_spec (Classical.choose_spec g2_wit)

/-- The free cut after the release. -/
noncomputable def s2_1 : Zustand Unit Unit Unit Unit Bool Unit :=
  { { s2_0 with sperren := Function.update s2_0.sperren () ⟨none, []⟩ } with graph := g2_g }

theorem s2_1_lock : (s2_1.sperren ()) = ⟨none, []⟩ := rfl

theorem s2_1_kerne0 : (s2_1.kerne 0).laeuft = some A := rfl

theorem s2_1_kerne1 : (s2_1.kerne 1).laeuft = some B := rfl

theorem s2_1_live : ∀ c, s2_1.status c = .laeuft := fun _ => rfl

noncomputable def zs2 : Nat → Zustand Unit Unit Unit Unit Bool Unit
  | 0 => s2_0
  | _ + 1 => s2_1

theorem zs2_succ (t : Nat) : zs2 (t + 1) = s2_1 := by
  cases t with
  | zero => rfl
  | succ t => rfl

theorem zs2_kerne : ∀ t, (zs2 t).kerne = zE0.kerne := by
  intro t
  cases t with
  | zero => rfl
  | succ t => rfl

theorem zs2_status : ∀ t, (zs2 t).status = zE0.status := by
  intro t
  cases t with
  | zero => rfl
  | succ t => rfl

/-- The release step fires on both sides with the non-reading write. -/
theorem s2_0_gibt : (s2_0.sperren ()).Gibt A ⟨none, []⟩ := by
  rw [s2_0_lock]
  exact .besitzer A []

theorem e2_impl_geben (w : Unit) : E_2.system.ImplSchritt A s2_0 w [wGebenPlan] s2_0 := by
  refine ⟨(), rfl, ?_⟩
  show e2Regel A s2_0 w [wGebenPlan] s2_0
  exact Or.inr (Or.inr (Or.inl ⟨⟨none, []⟩, SperrSchritt.geben s2_0_gibt, rfl, rfl⟩))

theorem e2_ideal_geben (w : Unit) : E_2.system.ISchritt A s2_0 w [wGebenPlan] s2_0 := by
  refine ⟨(), rfl, ?_⟩
  show e2Regel A s2_0 w [wGebenPlan] s2_0
  exact Or.inr (Or.inr (Or.inl ⟨⟨none, []⟩, SperrSchritt.geben s2_0_gibt, rfl, rfl⟩))

/-- The release execution at cut zero. -/
theorem ausfuehr_geben : FuehrtSchrittAus E_2.einrichtung 0 A s2_0 s2_0 wGebenPlan
    ⟨g2_es, []⟩ s2_1 := by
  have hF : FuehrtAus E_2.einrichtung 0 A s2_0 s2_0 (.sperre () .geben)
      [⟨.schreiben, (E_2.einrichtung.sperrOrt ()), .ra, (), ()⟩] []
      { s2_0 with sperren := Function.update s2_0.sperren () ⟨none, []⟩ } :=
    .sperre (SperrSchritt.geben s2_0_gibt) (fun _ => trivial)
  have hM : Speicherfolge s2_0.initial (SpeicherAkteur.kontext A) s2_0.graph
      [⟨.schreiben, (E_2.einrichtung.sperrOrt ()), .ra, (), ()⟩] g2_es g2_g :=
    g2_mem
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    fun _ h => (List.not_mem_nil h).elim, _,
    { s2_0 with sperren := Function.update s2_0.sperren () ⟨none, []⟩ },
    hF, hM, rfl⟩

noncomputable def spur2 : Nat → Option (SchrittWahl Unit × SchrittSpur Unit Unit)
  | 0 => some (.kontext A (), ⟨g2_es, []⟩)
  | (t + 1) => spurw (t + 1)

theorem spur2_0 : spur2 0 = some (.kontext A (), ⟨g2_es, []⟩) := rfl

theorem spur2_succ (t : Nat) : spur2 (t + 1) = spurw (t + 1) := by
  cases t with
  | zero => rfl
  | succ t => rfl

/-- The ticket schedule never records a crash. -/
theorem spurw_kein_absturz (t : Nat) : spurw t ≠ some (.absturz, absturzSpur) := by
  intro hcon
  cases t with
  | zero =>
    rw [spurw0] at hcon
    simp only [ticketA] at hcon
    have hfst := congrArg Prod.fst (Option.some.inj hcon)
    cases hfst
  | succ t =>
    cases t with
    | zero =>
      rw [spurw1] at hcon
      simp only [ticketB] at hcon
      have hfst := congrArg Prod.fst (Option.some.inj hcon)
      cases hfst
    | succ n =>
      by_cases h : (n + 2) % 2 = 0
      · rw [spurw_ge2 n h] at hcon
        simp only [ticketA] at hcon
        have hfst := congrArg Prod.fst (Option.some.inj hcon)
        cases hfst
      · have h1 : (n + 2) % 2 = 1 := by
          rcases Nat.mod_two_eq_zero_or_one (n + 2) with h0 | h1
          · exact (h h0).elim
          · exact h1
        rw [spurw_ge2' n h1] at hcon
        simp only [ticketB] at hcon
        have hfst := congrArg Prod.fst (Option.some.inj hcon)
        cases hfst

/-- The handover schedule never records a crash. -/
theorem spur2_kein_absturz (t : Nat) : spur2 t ≠ some (.absturz, absturzSpur) := by
  intro hcon
  cases t with
  | zero =>
    rw [spur2_0] at hcon
    have hfst := congrArg Prod.fst (Option.some.inj hcon)
    cases hfst
  | succ t =>
    rw [spur2_succ] at hcon
    exact spurw_kein_absturz _ hcon

def takt2 : ∀ t, Takt (Lauffolge E_2 hw2) (KeinSchritt (Lauffolge E_2 hw2))
    t (some (zs2 t)) (spur2 t) (some (zs2 (t + 1)))
  | 0 =>
    .schritt spur2_0 (.schritt (ImplSchritt.kontext (hw2_crash 0)
      ⟨0, hw2_opp0 rfl, s2_0_kerne0, s2_0_live _⟩
      (e2_impl_geben ())
      ausfuehr_geben))
  | (n + 1) => by
    by_cases hpar : (n + 1) % 2 = 0
    · have hsp : spur2 (n + 1) = some ticketA := by
        cases n with
        | zero => exact absurd hpar (by decide)
        | succ n => exact spurw_ge2 n hpar
      rw [hsp, zs2_succ n, zs2_succ (n + 1)]
      exact .schritt rfl (.schritt (ImplSchritt.kontext (hw2_crash (n + 1))
        ⟨0, hw2_opp0 hpar, s2_1_kerne0, s2_1_live _⟩
        ⟨(), rfl, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
        (e1StotterAusfuehr (n + 1) A s2_1)))
    · have h1 : (n + 1) % 2 = 1 := by
        rcases Nat.mod_two_eq_zero_or_one (n + 1) with h0 | h1
        · exact (hpar h0).elim
        · exact h1
      have hsp : spur2 (n + 1) = some ticketB := by
        cases n with
        | zero => exact spurw1
        | succ n => exact spurw_ge2' n h1
      rw [hsp, zs2_succ n, zs2_succ (n + 1)]
      exact .schritt rfl (.schritt (ImplSchritt.kontext (hw2_crash (n + 1))
        ⟨1, hw2_opp1 h1, s2_1_kerne1, s2_1_live _⟩
        ⟨(), rfl, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
        (e1StotterAusfuehr (n + 1) B s2_1)))

noncomputable def s2_start : AussenStart :=
  Classical.choose (zulStart_erfuellbar fair2.hardware wBild_gueltig)

theorem zul_2 : Katalog.ZulStart Plattform.x86_64.katalog h2 wBild s2_start :=
  Classical.choose_spec (zulStart_erfuellbar fair2.hardware wBild_gueltig)

noncomputable def ρ_2 : Maschine.Lauf E_2 :=
  ⟨s2_start, hw2, ⟨fun t => some (zs2 t), spur2, takt2⟩⟩

/-- The lock is held by `A` at cut zero and free afterwards. -/
theorem zs2_besitzer (t : Nat) (s : Zustand Unit Unit Unit Unit Bool Unit)
    (hzs : ρ_2.zeit.zustand t = some s) :
    (s.sperren ()).besitzer = if t = 0 then some A else none := by
  cases t with
  | zero =>
    have hss : s = s2_0 := Option.some.inj (hzs.symm.trans rfl)
    subst hss
    rw [s2_0_lock, if_pos rfl]
  | succ t =>
    have hss : s = s2_1 := Option.some.inj (hzs.symm.trans rfl)
    subst hss
    rw [s2_1_lock, if_neg (Nat.succ_ne_zero t)]

/-- The handover run meets every hold bound: only `A` ever owns, for a single cut. -/
theorem e2_halte : HalteSchranken E_2 ρ_2 := by
  intro l c a n hcont
  cases l
  intro H' hH
  have hH5 : H' = 5 := Option.some.inj (hH.symm.trans e2halten)
  subst hH5
  by_cases hn0 : n = 0
  · subst hn0
    have hkk : Kontextkosten ρ_2 c a 0 = 0 := rfl
    omega
  · have hlt : a < a + n := by omega
    obtain ⟨s, hzs, hown⟩ := hcont a (Nat.le_refl _) hlt
    have hownA := zs2_besitzer a s hzs
    by_cases ha0 : a = 0
    · subst ha0
      rw [if_pos rfl] at hownA
      have hcA : c = A := Option.some.inj (hown.symm.trans hownA)
      subst hcA
      have hn1 : n ≤ 1 := by
        by_contra hcon
        have hn2 : 2 ≤ n := by omega
        have hlt1 : (0 : Nat) + 1 < 0 + n := by omega
        obtain ⟨s', hzs', hown'⟩ := hcont 1 (Nat.zero_le _) hlt1
        have h1 := zs2_besitzer 1 s' hzs'
        rw [if_neg (by decide : (1 : Nat) ≠ 0)] at h1
        rw [h1] at hown'
        cases hown'
      have hcost1 : Kontextkosten ρ_2 A 0 n ≤ 1 := Nat.le_trans (zaehle_le _ _ _) hn1
      omega
    · rw [if_neg ha0] at hownA
      rw [hownA] at hown
      cases hown

/-- The holder is checker-eligible at every owned cut (only cut zero). -/
theorem e2_bereit : ∀ t s', 0 ≤ t → ρ_2.zeit.zustand t = some s' →
    (s'.sperren ()).besitzer = some A →
    SperrHalterBereit E_2 s' () A := by
  intro t s' _ hzs hown
  cases t with
  | zero =>
    have hss : s' = s2_0 := Option.some.inj (hzs.symm.trans rfl)
    subst hss
    intro hne
    exact ⟨s2_0_live _, ⟨0, s2_0_kerne0⟩, (), wGebenPlan, s2_0,
      e2_ideal_geben (),
      rfl, fun _ _ _ => trivial⟩
  | succ t =>
    have hss : s' = s2_1 := Option.some.inj (hzs.symm.trans rfl)
    subst hss
    rw [s2_1_lock] at hown
    cases hown

/-- The impl bridge holds on the handover run: the ideal `geben` offer fires on the
    implementation side with its protocol execution. -/
theorem e2_hagree : ∀ t s w plan u, 0 ≤ t → ρ_2.zeit.zustand t = some s →
    E_2.system.ISchritt A s w [plan] u → plan.aktion = .sperre () .geben →
    (s.sperren ()).besitzer = some A →
    ∃ u', E_2.system.ImplSchritt A s w [plan] u' ∧
      ∃ spur s', FuehrtSchrittAus E_2.einrichtung t A s u' plan spur s' := by
  intro t s w plan u _ hzs hisch hakt hown
  cases t with
  | zero =>
    have hss : s = s2_0 := Option.some.inj (hzs.symm.trans rfl)
    subst hss
    obtain ⟨i, _, himpl⟩ := hisch
    cases i
    have himpl' : e2Regel A s2_0 w [plan] u := himpl
    rcases himpl' with ⟨next, hss, hpeq, hueq⟩ | ⟨next, hss, hpeq, hueq⟩ |
      ⟨next, hss, hpeq, hueq⟩ | ⟨hpeq, hueq⟩
    · cases hss with
      | ticket hne _ => exact False.elim (hne rfl)
    · cases hss with
      | nehmen hN =>
        have h1 := hN.besitzt.2
        rw [s2_0_lock] at h1
        exact False.elim (Option.some_ne_none A h1)
    · have hplan : plan = wGebenPlan := (List.cons.inj hpeq).1
      subst hplan
      subst hueq
      exact ⟨s2_0, e2_impl_geben w, _, _, ausfuehr_geben⟩
    · have hcon : plan = stutterPlan := (List.cons.inj hpeq).1
      subst hcon
      have hact : stutterPlan.aktion = .intern := rfl
      rw [hact] at hakt
      cases hakt
  | succ t =>
    have hss : s = s2_1 := Option.some.inj (hzs.symm.trans rfl)
    subst hss
    rw [s2_1_lock] at hown
    cases hown

end Gabbro.Core.Fortschritt
