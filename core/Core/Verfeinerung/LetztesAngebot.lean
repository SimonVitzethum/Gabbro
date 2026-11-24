module

public import Core.Verfeinerung.Fortschritt

@[expose] public section

namespace Gabbro.Core.Maschine.I

open Gabbro.Core.Katalog

variable {L Ort Wert Raum Lok Grund Bedingung Wahl F : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F}

/-- Retain the first set of offers and the whole outside policy. No later
    hardware tick offers a transition. -/
def letztesAngebot (hw : HwLauf) : HwLauf :=
  ⟨(fun
    | 0 => hw.angebot 0
    | _ + 1 => ⟨none, fun _ => false, [], fun _ => false, false, false, (hw.angebot 0).cycles⟩),
    hw.politik⟩

private theorem letztesAngebot_konform {k h hw} (valid : HwLauf.konform k h hw) :
    (letztesAngebot hw).konform k h := by
  refine ⟨valid.1, fun t => ?_⟩
  cases t with
  | zero => exact valid.2 0
  | succ _ =>
    exact ⟨fun _ h => (Option.some_ne_none _ h.symm).elim, fun _ h => (Bool.false_ne_true h).elim,
      fun _ h => (List.not_mem_nil h).elim, fun _ h => (Bool.false_ne_true h).elim,
      fun h => (h.elim Bool.false_ne_true Bool.false_ne_true).elim⟩

private theorem letztesAngebot_ideal {hw} (t : Nat) (s : Zustand L Ort Wert Raum Lok Grund) :
    KeinSchritt (Schritt E.einrichtung E.system E.katalog (letztesAngebot hw)) (t + 1) s := by
  intro event next step
  cases step with
  | kontext _ ready _ _ =>
    obtain ⟨_, offered, _, _⟩ := ready
    exact Option.some_ne_none _ offered.symm
  | antwort _ arrives =>
    have received := arrives.1.2.1.1
    rw [arrives.1.1] at received
    exact Bool.false_ne_true received
  | interrupt _ enters =>
    obtain ⟨_, _, _, _, offered, _⟩ := enters
    exact Bool.false_ne_true offered
  | absturz crash => exact Bool.false_ne_true crash.1.2

private theorem letztesAngebot_konkret {hw} (t : Nat) (s : Zustand L Ort Wert Raum Lok Grund) :
    KeinSchritt (Lauffolge E (letztesAngebot hw)) (t + 1) (some s) := by
  intro event next step
  cases step with
  | schritt step =>
    cases step with
    | kontext _ ready _ _ =>
      obtain ⟨_, offered, _, _⟩ := ready
      exact Option.some_ne_none _ offered.symm
    | antwort _ arrives =>
      have received := arrives.1.2.1.1
      rw [arrives.1.1] at received
      exact Bool.false_ne_true received
    | interrupt _ enters =>
      obtain ⟨_, _, _, _, offered, _⟩ := enters
      exact Bool.false_ne_true offered
    | absturz crash => exact Bool.false_ne_true crash.1.2

private theorem hoechstens_eine_markierung (markiert : Nat → Bool)
    (spaeter : ∀ t, markiert (t + 1) = false) (a n : Nat) :
    zaehle markiert a n ≤ if markiert a then 1 else 0 := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    cases n with
    | zero =>
      exact (Nat.zero_add _).le
    | succ n =>
      change zaehle markiert a (n + 1) + (if markiert ((a + n) + 1) then 1 else 0) ≤
        if markiert a then 1 else 0
      simpa only [spaeter, Bool.false_eq_true, ite_false, Nat.add_zero] using ih

/-- A single private transition can consume the last hardware opportunity
    while an ideal step is possible. Both runs remain maximal and finite.
    This match respects the unit's checked bound exactly when the form
    allows at least one private step. -/
theorem lauf_mit_letztem_privattakt {h : Umgebung} {s : AussenStart} {hw : HwLauf}
    {z z' : Zustand L Ort Wert Raum Lok Grund} {c : Kontext} {w : Wahl} {f : F}
    (hardware : Hardware E.katalog h) (zul : E.ZulStart h s) (valid : hw.konform E.katalog h)
    (loaded : E.laden s (h.lade E.bild) = some z)
    (initial : Zustandsbezug E z (start E s).2) (final : Zustandsbezug E z' (start E s).2)
    (first : ImplSchritt E.einrichtung E.system E.katalog (letztesAngebot hw) 0 z (.kontext c w, ⟨[], []⟩) z')
    (normal : (hw.angebot 0).crash = false)
    (ready : KannSchreiten (letztesAngebot hw) 0 c (start E s).2)
    (head : E.system.kopf (start E s).2 c = some f)
    (enabled : ∃ w' spur next, Schritt E.einrichtung E.system E.katalog (letztesAngebot hw)
      0 (start E s).2 (.kontext c w', spur) next) :
    ∃ (ρ : Maschine.Lauf E) (η : Lauf E),
      Maschine.Laeufe E h ρ ∧ Laeufe E η ∧ Laufabgleich ρ η ∧
      ¬ FairLaeufe E.katalog h ρ.hw ∧ ρ.zeit.Endlich ∧ η.zeit.Endlich ∧
      (StotterSchranke η ↔ 1 ≤ E.stotterLaenge f) ∧
      ρ.zeit.spur 0 = some (.kontext c w, ⟨[], []⟩) ∧ η.belegt 0 = some c ∧
      (∀ t, η.zeit.spur t = none) ∧
      (∃ w' spur next, Schritt E.einrichtung E.system E.katalog η.hw
        0 (η.zeit.zustand 0) (.kontext c w', spur) next) := by
  let ρ : Maschine.Lauf E := ⟨s, letztesAngebot hw, {
    zustand := fun | 0 => some z | _ + 1 => some z'
    spur := fun | 0 => some (.kontext c w, ⟨[], []⟩) | _ + 1 => none
    takt := fun
      | 0 => .schritt rfl (.schritt first)
      | t + 1 => .wartet rfl rfl (letztesAngebot_konkret t z') }⟩
  let η : Lauf E := ⟨s, h, letztesAngebot hw, {
    zustand := fun _ => (start E s).2
    spur := fun _ => none
    takt := fun
      | 0 => .wartet rfl rfl (fun h => Bool.false_ne_true (normal.symm.trans h.2))
      | _ + 1 => .wartet rfl rfl (fun h => Bool.false_ne_true h.2) },
    fun | 0 => some c | _ + 1 => none⟩
  have konform := letztesAngebot_konform valid
  have ideal : Laeufe E η := by
    refine ⟨hardware, konform, zul, rfl, ⟨?_, ?_⟩, ?_⟩
    · intro t _ vacant
      cases t with
      | zero => exact (Option.some_ne_none _ vacant).elim
      | succ t => exact letztesAngebot_ideal t _
    · exact fun _ => ⟨1, fun t after => by cases t with
        | zero => exact (Nat.not_succ_le_zero _ after).elim
        | succ _ => rfl⟩
    · intro t d marked
      cases t with
      | zero => exact ⟨rfl, Option.some.inj marked ▸ ready⟩
      | succ _ => exact (Option.some_ne_none _ marked.symm).elim
  have matched : Laufabgleich ρ η := by
    refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
    · intro t
      cases t with
      | zero => exact ⟨z, rfl, initial⟩
      | succ _ => exact ⟨z', rfl, final⟩
    · intro t
      cases t with
      | zero => exact .privat c w
      | succ _ => exact .pause
    · intro t
      cases t with
      | zero =>
        exact ⟨fun none => (Option.some_ne_none _ none).elim, fun alternative =>
          alternative.elim (fun empty => (Option.some_ne_none _ empty).elim) (fun step => (step rfl).elim)⟩
      | succ _ => exact ⟨fun _ => Or.inl rfl, fun _ => rfl⟩
    · intro t d marked
      cases t with
      | zero =>
        have eq : c = d := Option.some.inj marked
        cases eq
        exact ⟨w, f, rfl, head⟩
      | succ _ => exact (Option.some_ne_none _ marked.symm).elim
  have unfair : ¬ FairLaeufe E.katalog h ρ.hw := by
    intro fair
    obtain ⟨t, after, offer⟩ := fair.kerne.2 0 hardware.kerne 1
    cases t with
    | zero => exact (Nat.not_succ_le_zero _ after).elim
    | succ _ => exact Option.some_ne_none _ offer.symm
  have idealFinite : η.zeit.Endlich := ⟨⟨0, Or.inl rfl⟩, fun _ _ => rfl⟩
  have bound : StotterSchranke η ↔ 1 ≤ E.stotterLaenge f := by
    constructor
    · intro bound
      have interval : Stotterintervall η c f 0 1 :=
        fun _ _ _ => ⟨head, fun _ _ h => Option.some_ne_none _ h.symm, fun h => Option.some_ne_none _ h.symm⟩
      have atZero : η.belegt 0 = some c := rfl
      simpa only [zaehle, Nat.zero_add, atZero, decide_true, ite_true] using bound c f 0 1 interval
    · intro allowed d g a n interval
      cases n with
      | zero => exact Nat.zero_le _
      | succ n =>
        have count := hoechstens_eine_markierung (fun t => decide (η.belegt t = some d))
          (fun _ => decide_eq_false (fun h => Option.some_ne_none d h.symm)) a (n + 1)
        apply count.trans
        by_cases mark : η.belegt a = some d
        · have ctx : c = d := by
            cases a with
            | zero => exact Option.some.inj mark
            | succ _ => exact (Option.some_ne_none d mark.symm).elim
          subst d
          have first := (interval a (Nat.le_refl _) (Nat.lt_add_of_pos_right (Nat.succ_pos n))).1
          have form := Option.some.inj (first.symm.trans head)
          subst g
          simpa only [mark, decide_true, ite_true] using allowed
        · simpa only [decide_eq_false mark, Bool.false_eq_true, ite_false] using Nat.zero_le (E.stotterLaenge g)
  exact ⟨ρ, η, ⟨hardware, konform, zul, loaded.symm⟩, ideal, matched, unfair,
    (matched.endlich ideal).mpr idealFinite, idealFinite, bound, rfl, rfl, fun _ => rfl, enabled⟩

end Gabbro.Core.Maschine.I
