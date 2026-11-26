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
public import Core.Fortschritt.Verhungern

@[expose] public section

namespace Gabbro.Core.Fortschritt

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog
open Gabbro.Core.Annahme
open Gabbro.Core.Beobachtung

variable {L Ort Wert Raum Lok Grund Bedingung Wahl F : Type} [DecidableEq L]

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
    Eq, fun _ => 1, .leer, eineTabelle, e1Schranken, .leer, .leer⟩

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
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    fun _ h => (List.not_mem_nil h).elim,
    sperrEreignisse (zE0.sperren ()) ((zE0.sperren ()).anstellen A)
      ((E_1).einrichtung.sperrOrt ()) (zE0.initial ((E_1).einrichtung.sperrOrt ())),
    S_c,
    .sperre (.ticket (fun h => by cases h) List.not_mem_nil) (fun w => (w rfl).elim), by exact .nil _, rfl⟩

def e1StotterAusfuehr (t : Nat) (c : Kontext)
    (s : Zustand Unit Unit Unit Unit Bool Unit) :
    FuehrtSchrittAus (E_1).einrichtung t c s s stutterPlan ⟨[], []⟩ s := by
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    fun _ h => (List.not_mem_nil h).elim, [], s, .intern, .nil _, rfl⟩

def e1AusfuehrB :
    FuehrtSchrittAus (E_1).einrichtung 1 B S_c (toggleUpdate B S_c) ticketPlan ⟨[], []⟩ S_d := by
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    fun _ h => (List.not_mem_nil h).elim,
    sperrEreignisse (S_c.sperren ()) ((S_c.sperren ()).anstellen B)
      ((E_1).einrichtung.sperrOrt ()) (S_c.initial ((E_1).einrichtung.sperrOrt ())),
    S_d,
    .sperre (.ticket (fun h => by cases h)
      (fun h => by cases List.mem_singleton.mp h)) (fun w => (w rfl).elim),
    by exact .nil _, rfl⟩

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
  | n + 2 => if n % 2 = 0 then some ticketA else some ticketB

theorem spurw0 : spurw 0 = some ticketA := rfl

theorem spurw1 : spurw 1 = some ticketB := rfl

theorem spurw_ge2 (n : Nat) (h : (n + 2) % 2 = 0) : spurw (n + 2) = some ticketA := by
  have hn : n % 2 = 0 := by
    have hmod : (n + 2) % 2 = n % 2 := Nat.add_mul_mod_self_left n 2 1
    rw [hmod] at h
    exact h
  simp only [spurw, if_pos hn]

theorem spurw_ge2' (n : Nat) (h : (n + 2) % 2 = 1) : spurw (n + 2) = some ticketB := by
  have hn : ¬ n % 2 = 0 := by
    intro hn0
    have hmod : (n + 2) % 2 = n % 2 := Nat.add_mul_mod_self_left n 2 1
    rw [hmod, hn0] at h
    cases h
  simp only [spurw, if_neg hn]

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
        (fun h => by cases List.mem_singleton.mp h), rfl, rfl⟩⟩
      e1AusfuehrB))
  | n + 2 => by
    by_cases hpar : (n + 2) % 2 = 0
    · -- Even tick: A stutters on core 0; the state stays put.
      have hsp : spurw (n + 2) = some ticketA := spurw_ge2 n hpar
      have hcur : zw (n + 2) = some S_d := by
        have h : zw (n + 2) = some (zwSt (n + 2)) := rfl
        rw [h, zwSt_ge2 _ (Nat.le_add_left 2 n)]
      have hnxt : zw ((n + 2) + 1) = some S_d := by
        have h : zw ((n + 2) + 1) = some (zwSt ((n + 2) + 1)) := rfl
        rw [h, zwSt_ge2 _ (Nat.le_trans (Nat.le_add_left 2 n) (Nat.le_succ _))]
      have hker : (S_d.kerne 0).laeuft = some A := rfl
      have hlive : S_d.status A = Status.laeuft := rfl
      rw [hsp, hcur, hnxt]
      exact .schritt rfl (.schritt (ImplSchritt.kontext (hw2_crash (n + 2))
        ⟨0, hw2_opp0 hpar, hker, hlive⟩
        ⟨(), rfl, Or.inr ⟨rfl, rfl⟩⟩
        (e1StotterAusfuehr (n + 2) A S_d)))
    · -- Odd tick: B stutters on core 1; the state stays put.
      have h1 : (n + 2) % 2 = 1 := by
        rcases Nat.mod_two_eq_zero_or_one (n + 2) with h0 | h1
        · exact (hpar h0).elim
        · exact h1
      have hsp : spurw (n + 2) = some ticketB := spurw_ge2' n h1
      have hcur : zw (n + 2) = some S_d := by
        have h : zw (n + 2) = some (zwSt (n + 2)) := rfl
        rw [h, zwSt_ge2 _ (Nat.le_add_left 2 n)]
      have hnxt : zw ((n + 2) + 1) = some S_d := by
        have h : zw ((n + 2) + 1) = some (zwSt ((n + 2) + 1)) := rfl
        rw [h, zwSt_ge2 _ (Nat.le_trans (Nat.le_add_left 2 n) (Nat.le_succ _))]
      have hker : (S_d.kerne 1).laeuft = some B := rfl
      have hlive : S_d.status B = Status.laeuft := rfl
      rw [hsp, hcur, hnxt]
      exact .schritt rfl (.schritt (ImplSchritt.kontext (hw2_crash (n + 2))
        ⟨1, hw2_opp1 h1, hker, hlive⟩
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

end Gabbro.Core.Fortschritt
