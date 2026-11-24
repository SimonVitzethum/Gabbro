/-
  File:      Core/Fortschritt/WarteBeispiel.lean
  Subject:   WITNESS FOR THE LOCK-WAIT BOUND (PERFECT-MODEL §3.7, step M8): the premise bundle
             of `sperr_warte_schranke` holds jointly — a waiter queued at position zero with a
             free lock, a real take enabled, unit hold-bound data and no owners.

  `E_1` is the ticket-only unit: contexts draw tickets through `SperrSchritt.ticket` (empty
  memory side, so no graph reasoning is needed); takes are not sanctioned, so after two
  tickets the run pauses. The waiter `A` is queued behind nobody; the bound counts zero
  owner steps against the declared hold bound five.
-/
module

public import Core.Fortschritt.SperrSchranke
public import Core.Fortschritt.Beispiele

@[expose] public section

namespace Gabbro.Core.Fortschritt

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog
open Gabbro.Core.Annahme
open Gabbro.Core.Beobachtung

def ticketPlan : SchrittPlan Unit Unit Unit Unit :=
  ⟨.sperre () .ticket, [], [], fun _ => false, fun _ => .na, fun _ => ()⟩

def stutterPlan : SchrittPlan Unit Unit Unit Unit :=
  ⟨.intern, [], [], fun _ => false, fun _ => .na, fun _ => ()⟩

def e1Regel (c : Kontext) (s : Zustand Unit Unit Unit Unit Bool Unit) (w : Unit)
    (es : List (SchrittPlan Unit Unit Unit Unit)) (u : Zustand Unit Unit Unit Unit Bool Unit) :
    Prop :=
  (∃ next, SperrSchritt .ticket c (s.sperren ()) next ∧ es = [ticketPlan] ∧
    u = toggleUpdate c s) ∨
  (es = [stutterPlan] ∧ u = s)

def e1System : MaschinenSystem Unit Unit Unit Unit Bool Unit Unit Unit Unit :=
  ⟨fun _ => ⟨e1Regel, e1Regel⟩, fun _ _ => some (), fun _ _ => False, fun _ _ _ => False⟩

def e1Schranken : Schrankendaten Unit Bool :=
  { kosten := none, speicher := none, stapel := none, halten := fun _ => some 5,
    stapelTiefe := fun _ => 0, zeit := fun _ => none, zeitstand := fun _ => [] }

def E_1 : Einheit Unit Unit Unit Unit Bool Unit Unit Unit Unit :=
  ⟨Plattform.x86_64.katalog, wBild, wEinrichtung dispatch2, e1System,
    fun _ => wDaten dispatch2, fun _ => 0,
    fun _ _ => some (Zustand.start (fun _ => false) (fun _ => .laeuft)
      (fun j => ⟨dispatch2 j, .nutzer, (), fun _ => false, 0, false, []⟩)
      ⟨fun _ => false, fun _ => 0⟩ (fun _ => ()) (.leer (fun _ => 0))),
    Eq, fun _ => 1, .leer, e1Schranken, .leer, .leer⟩

def zE0 : Zustand Unit Unit Unit Unit Bool Unit := (I.start E_1 s0).2

def e1Upd (c : Kontext) (s : Zustand Unit Unit Unit Unit Bool Unit) :
    Zustand Unit Unit Unit Unit Bool Unit :=
  { toggleUpdate c s with sperren := Function.update s.sperren () ((s.sperren ()).anstellen c) }

def S_c : Zustand Unit Unit Unit Unit Bool Unit := e1Upd A zE0

def S_d : Zustand Unit Unit Unit Unit Bool Unit := e1Upd B S_c

theorem zE0lock : (zE0.sperren ()) = SperrZustand.frei := rfl

theorem qc : (S_c.sperren ()) = ⟨none, [A]⟩ := rfl

theorem qd : (S_d.sperren ()) = ⟨none, [A, B]⟩ := rfl

theorem e1halten : (E_1).schranken.halten () = some 5 := rfl

/-- The memory side of a ticket step is empty: no owner changes. -/
theorem ticket_leer (s : Zustand Unit Unit Unit Unit Bool Unit) (c : Kontext) :
    sperrEreignisse (s.sperren ()) ((s.sperren ()).anstellen c)
      ((E_1).einrichtung.sperrOrt ()) (s.initial ((E_1).einrichtung.sperrOrt ())) = [] :=
  sperr_leer_iff _ _ _ _ |>.mpr (fun h => h rfl)

def e1AusfuehrA :
    FuehrtSchrittAus (E_1).einrichtung 0 A zE0 (toggleUpdate A zE0) ticketPlan ⟨[], []⟩ S_c := by
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    fun _ h => (List.not_mem_nil h).elim, _, S_c,
    .sperre (.ticket (fun h => by cases h) List.not_mem_nil) (fun w => (w rfl).elim), ?_, rfl⟩
  rw [ticket_leer]
  exact .nil _

def e1StotterAusfuehr (t : Nat) (c : Zustand Unit Unit Unit Unit Bool Unit)
    (s : Zustand Unit Unit Unit Unit Bool Unit) :
    FuehrtSchrittAus (E_1).einrichtung t c s s stutterPlan ⟨[], []⟩ s := by
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    fun _ h => (List.not_mem_nil h).elim, [], s, .intern, .nil _, rfl⟩

def e1AusfuehrB :
    FuehrtSchrittAus (E_1).einrichtung 1 B S_c (toggleUpdate B S_c) ticketPlan ⟨[], []⟩ S_d := by
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    fun _ h => (List.not_mem_nil h).elim, _, S_d,
    .sperre (.ticket (fun h => by cases h)
      (fun h => (by decide : B ≠ A) (List.mem_singleton.mp h))) (fun w => (w rfl).elim), ?_, rfl⟩
  rw [ticket_leer]
  exact .nil _

def zwSt : Nat → Zustand Unit Unit Unit Unit Bool Unit
  | 0 => zE0
  | 1 => S_c
  | _ + 2 => S_d

theorem zwSt_kerne : ∀ t, (zwSt t).kerne = zE0.kerne := by
  intro t
  cases t with
  | zero => rfl
  | succ t =>
    cases t with
    | zero => rfl
    | succ t => rfl

theorem zwSt_status : ∀ t, (zwSt t).status = zE0.status := by
  intro t
  cases t with
  | zero => rfl
  | succ t =>
    cases t with
    | zero => rfl
    | succ t => rfl

def zw : Nat → Option (Zustand Unit Unit Unit Unit Bool Unit) := fun t => some (zwSt t)

theorem zwSt_0 : zwSt 0 = zE0 := rfl

theorem zwSt_1 : zwSt 1 = S_c := rfl

theorem zwSt_ge2 : ∀ t, 2 ≤ t → zwSt t = S_d := by
  intro t h
  match t with
  | 0 => exact absurd h (by decide)
  | 1 => exact absurd h (by decide)
  | _ + 2 => rfl

def ticketA : SchrittWahl Unit × SchrittSpur Unit Unit :=
  (.kontext A (), ⟨[], []⟩)

def ticketB : SchrittWahl Unit × SchrittSpur Unit Unit :=
  (.kontext B (), ⟨[], []⟩)

def spurw : Nat → Option (SchrittWahl Unit × SchrittSpur Unit Unit)
  | 0 => some ticketA
  | 1 => some ticketB
  | _ + 2 => some ticketB

theorem spurw0 : spurw 0 = some ticketA := rfl

theorem spurw1 : spurw 1 = some ticketB := rfl

theorem spurw_ge2 : ∀ t, 2 ≤ t → spurw t = some ticketB := by
  intro t h
  match t with
  | 0 => exact absurd h (by decide)
  | 1 => exact absurd h (by decide)
  | _ + 2 => rfl

def taktw : ∀ t, Takt (Lauffolge E_1 hw2) (KeinSchritt (Lauffolge E_1 hw2)) t (zw t) (spurw t) (zw (t + 1))
  | 0 =>
    .schritt spurw0 (.schritt (ImplSchritt.kontext (hw2_crash 0)
      ⟨0, hw2_opp0 rfl, rfl, rfl⟩
      ⟨(), rfl, Or.inl ⟨_, .ticket (fun h => by cases h) List.not_mem_nil, rfl, rfl⟩⟩
      e1AusfuehrA))
  | 1 =>
    .schritt spurw1 (.schritt (ImplSchritt.kontext (hw2_crash 1)
      ⟨1, hw2_opp1 rfl, rfl, rfl⟩
      ⟨(), rfl, Or.inl ⟨_, .ticket (fun h => by cases h)
        (fun h => (by decide : B ≠ A) (List.mem_singleton.mp h)), rfl, rfl⟩⟩
      e1AusfuehrB))
  | n + 2 =>
    have hle : 2 ≤ n + 2 := Nat.le_add_left 2 n
    have hsp : spurw (n + 2) = some ticketB := spurw_ge2 _ hle
    have hzw : ∀ t, zw t = some (zwSt t) := fun _ => rfl
    have hcur : zw (n + 2) = some S_d := by
      rw [hzw, zwSt_ge2 _ hle]
    have hnxt : zw ((n + 2) + 1) = some S_d := by
      rw [hzw, zwSt_ge2 _ (by omega)]
    have hker : (S_d.kerne 1).laeuft = some B := rfl
    have hlive : S_d.status B = Status.laeuft := rfl
    rw [hsp, hcur, hnxt]
    exact .schritt rfl (.schritt (ImplSchritt.kontext (hw2_crash (n + 2))
      ⟨1, hw2_opp1 (by omega), hker, hlive⟩
      ⟨(), rfl, Or.inr ⟨rfl, rfl⟩⟩
      (e1StotterAusfuehr (n + 2) B S_d)))

def ρ' : Maschine.Lauf E_1 :=
  ⟨s0, hw2, ⟨zw, spurw, taktw⟩⟩

theorem ρ'_0 : ρ'.zeit.zustand 0 = some zE0 := rfl

theorem ρ'_1 : ρ'.zeit.zustand 1 = some S_c := rfl

theorem ρ'_ge (n : Nat) : ρ'.zeit.zustand (n + 2) = some S_d := rfl

theorem e1_besitzer_zE0 : (zE0.sperren ()).besitzer = none := rfl

theorem e1_besitzer_Sc : (S_c.sperren ()).besitzer = none := rfl

theorem e1_besitzer_Sd : (S_d.sperren ()).besitzer = none := rfl

/-- Locks stay free along the witness run. -/
theorem e1_besitzer_frei : ∀ t s, ρ'.zeit.zustand t = some s → (s.sperren ()).besitzer = none := by
  intro t s hzs
  match t with
  | 0 =>
    rw [ρ'_0] at hzs
    obtain rfl := Option.some.inj hzs
    exact e1_besitzer_zE0
  | 1 =>
    rw [ρ'_1] at hzs
    obtain rfl := Option.some.inj hzs
    exact e1_besitzer_Sc
  | _ + 2 =>
    rw [ρ'_ge _] at hzs
    obtain rfl := Option.some.inj hzs
    exact e1_besitzer_Sd

/-- Queue positions in the witness: only the head is ever the waiter. -/
theorem e1_index_null : ∀ (i : Nat) (q : List Kontext),
    (q = [A] ∨ q = [A, B]) → q[i]? = some A → i = 0 := by
  intro i q hq hi
  rcases hq with rfl | rfl
  · cases i with
    | zero => rfl
    | succ j =>
      simp only [List.getElem?_cons_succ, List.getElem?_nil] at hi
      cases hi
  · cases i with
    | zero => rfl
    | succ j =>
      cases j with
      | zero =>
        simp only [List.getElem?_cons_succ] at hi
        have hBA : B = A := Option.some.inj hi
        cases hBA
      | succ k =>
        simp only [List.getElem?_cons_succ, List.getElem?_nil] at hi
        cases hi

/-- The premise bundle of the waiting bound. -/
structure WartePraemissen (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F)
    (ρ : Maschine.Lauf E) (l : L) (c : Kontext) (i H : Nat) (a : Nat) : Prop where
  halte : E.schranken.halten l = some H
  hhalte : HalteSchranken E ρ
  hqueue : ∃ s, ρ.zeit.zustand a = some s ∧ (s.sperren l).schlange[i]? = some c
  hbleibt : ∀ t s, a ≤ t → ρ.zeit.zustand t = some s → (s.sperren l).besitzer ≠ some c →
    c ∈ (s.sperren l).schlange
  hgibt : ∀ h b s, a ≤ b → ρ.zeit.zustand b = some s → (s.sperren l).besitzer = some h →
    ∃ r, b ≤ r ∧
      (∃ s₁ s₂, ρ.zeit.zustand r = some s₁ ∧ ρ.zeit.zustand (r + 1) = some s₂ ∧
        (s₁.sperren l).Gibt h (s₂.sperren l)) ∧
      Kontextkosten ρ h b (r + 1 - b) ≤ H + 1
  hmono : ∀ t₁ t₂ s₁ s₂ (i₁ i₂ : Nat), a ≤ t₁ → t₁ ≤ t₂ → ρ.zeit.zustand t₁ = some s₁ →
    ρ.zeit.zustand t₂ = some s₂ → (s₁.sperren l).schlange[i₁]? = some c →
    (s₂.sperren l).schlange[i₂]? = some c → i₂ ≤ i₁

theorem e1_halte : HalteSchranken E_1 ρ' := by
  intro l c a n hcont
  cases l
  intro H' hH
  have h55 : (E_1).schranken.halten () = some 5 := rfl
  have hH5 : H' = 5 := Option.some.inj (hH.symm.trans h55)
  subst hH5
  by_cases hn : n = 0
  · subst hn
    have hkk : Kontextkosten ρ' c a 0 = 0 := rfl
    omega
  · have hlt : a < a + n := by omega
    obtain ⟨s, hzs, hown⟩ := hcont a (Nat.le_refl _) hlt
    have hfree := e1_besitzer_frei a s hzs
    rw [hfree] at hown
    cases hown

theorem e1_hbleibt : ∀ t s, 1 ≤ t → ρ'.zeit.zustand t = some s →
    (s.sperren ()).besitzer ≠ some A → A ∈ (s.sperren ()).schlange := by
  intro t s ht hzs _
  match t with
  | 0 => exact absurd ht (by decide)
  | 1 =>
    rw [ρ'_1] at hzs
    obtain rfl := Option.some.inj hzs
    exact List.mem_cons.mpr (Or.inl rfl)
  | _ + 2 =>
    rw [ρ'_ge _] at hzs
    obtain rfl := Option.some.inj hzs
    exact List.mem_cons.mpr (Or.inl rfl)

theorem e1_hgibt : ∀ h b s, 1 ≤ b → ρ'.zeit.zustand b = some s →
    (s.sperren ()).besitzer = some h →
    ∃ r, b ≤ r ∧
      (∃ s₁ s₂, ρ'.zeit.zustand r = some s₁ ∧ ρ'.zeit.zustand (r + 1) = some s₂ ∧
        (s₁.sperren ()).Gibt h (s₂.sperren ())) ∧
      Kontextkosten ρ' h b (r + 1 - b) ≤ 5 + 1 := by
  intro h b s hb hzs hown
  have hfree := e1_besitzer_frei b s hzs
  rw [hfree] at hown
  cases hown

theorem e1_hmono : ∀ t₁ t₂ s₁ s₂ (i₁ i₂ : Nat), 1 ≤ t₁ → t₁ ≤ t₂ → ρ'.zeit.zustand t₁ = some s₁ →
    ρ'.zeit.zustand t₂ = some s₂ → (s₁.sperren ()).schlange[i₁]? = some A →
    (s₂.sperren ()).schlange[i₂]? = some A → i₂ ≤ i₁ := by
  intro t₁ t₂ s₁ s₂ i₁ i₂ h1 h2 hz1 hz2 hq1 hq2
  have e1 : ∀ t s, 1 ≤ t → ρ'.zeit.zustand t = some s →
      (s.sperren ()) = ⟨none, [A]⟩ ∨ (s.sperren ()) = ⟨none, [A, B]⟩ := by
    intro t s ht hzs
    match t with
    | 0 => exact absurd ht (by decide)
    | 1 =>
      rw [ρ'_1] at hzs
      obtain rfl := Option.some.inj hzs
      exact Or.inl qc
    | _ + 2 =>
      rw [ρ'_ge _] at hzs
      obtain rfl := Option.some.inj hzs
      exact Or.inr qd
  rcases e1 t₁ s₁ h1 hz1 with h | h <;> rcases e1 t₂ s₂ (by omega) hz2 with h' | h'
  · rw [h] at hq1
    rw [h] at hq2
    have i1 : i₁ = 0 := e1_index_null i₁ [A] (Or.inl rfl) hq1
    have i2 : i₂ = 0 := e1_index_null i₂ [A] (Or.inl rfl) hq2
    omega
  · rw [h] at hq1
    rw [h'] at hq2
    have i1 : i₁ = 0 := e1_index_null i₁ [A] (Or.inl rfl) hq1
    have i2 : i₂ = 0 := e1_index_null i₂ [A, B] (Or.inr rfl) hq2
    omega
  · rw [h] at hq1
    rw [h'] at hq2
    have i1 : i₁ = 0 := e1_index_null i₁ [A, B] (Or.inr rfl) hq1
    have i2 : i₂ = 0 := e1_index_null i₂ [A] (Or.inl rfl) hq2
    omega
  · rw [h] at hq1
    rw [h'] at hq2
    have i1 : i₁ = 0 := e1_index_null i₁ [A, B] (Or.inr rfl) hq1
    have i2 : i₂ = 0 := e1_index_null i₂ [A, B] (Or.inr rfl) hq2
    omega

/-- The premise bundle holds jointly: queued head waiter, free lock, take enabled,
    declared hold bound five, no owners. -/
theorem warte_praemissen_erfuellbar :
    ∃ (E : Einheit Unit Unit Unit Unit Bool Unit Unit Unit Unit) (ρ : Maschine.Lauf E)
      (c : Kontext) (H a : Nat),
      WartePraemissen E ρ () c 0 H a ∧
      ∃ b e, a ≤ b ∧ (∃ s, ρ.zeit.zustand b = some s ∧
        ((s.sperren ()).besitzer = some c ∨
          (∃ h₀ r, (s.sperren ()).besitzer = none ∧ (s.sperren ()).schlange = h₀ :: r ∧
            ∃ s', (s.sperren ()).Nimmt h₀ s'))) ∧
        e.length ≤ 0 + 1 ∧ (∀ x ∈ e, x ≤ H + 1) ∧ e.sum ≤ (0 + 1) * (H + 1) := by
  refine ⟨E_1, ρ', A, 5, 1,
    ⟨e1halten, e1_halte, ⟨S_c, rfl, rfl⟩, e1_hbleibt, e1_hgibt, e1_hmono⟩, ?_⟩
  exact sperr_warte_schranke 0 0 1 (Nat.le_refl _) e1halten e1_halte ⟨S_c, rfl, rfl⟩
    e1_hbleibt e1_hgibt e1_hmono

end Gabbro.Core.Fortschritt
