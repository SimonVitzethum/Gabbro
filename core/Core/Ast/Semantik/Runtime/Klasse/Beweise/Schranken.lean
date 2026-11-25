/-
  File:      core/Core/Ast/Semantik/Runtime/Klasse/Beweise/Schranken.lean
  Subject:   THE BOUND DUTY OF AN EFFECT CLASS (MK-12, `KlassenSchrankenAussage`). The stack leg is
             `Stapelschranke` at the acting context and the identity at every other context; the memory
             leg is the invariance of `LebendeZellen`, which reads only `rechte` and `buchung.umfang`.
             Neither the form's transfer (`nach`, `zugriffNach`, `verweigert`) nor the protocol action of
             `FuehrtAus` touches those fields, so both legs are proved from the class definition for
             every unit that embeds a form. Two lemmas carry the two preservation facts;
             `klassenSchranken` assembles them into `RegelSchranken`.
-/
module

public import Core.Ast.Semantik.Runtime.Klasse.Pflichten
public import Core.Ast.Semantik.Runtime.Klasse.Beweise.Faden

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Annahme
open Gabbro.Core.Beobachtung

/-- Every protocol action leaves the local states, the authority ledger and the booking extents alone:
    it changes only locks, questions, answers, consumed counts, cores or the graph. -/
theorem FuehrtAus.erhaeltBuchung {L Ort Wert Raum Lok Grund Bedingung : Type} [DecidableEq L]
    {e : Einrichtung L Ort Wert Raum Lok Grund Bedingung} {t : Nat} {c : Kontext}
    {s u : Maschine.Zustand L Ort Wert Raum Lok Grund} {a : Aktion L Bedingung}
    {sperren : List (Speicher.Etikett Ort Wert)} {spur : List Ereignis}
    {v : Maschine.Zustand L Ort Wert Raum Lok Grund}
    (h : FuehrtAus e t c s u a sperren spur v) :
    v.rechte = u.rechte ∧ v.buchung.umfang = u.buchung.umfang ∧ (∀ d, v.lokal d = u.lokal d) := by
  cases h <;> exact ⟨rfl, rfl, fun _ => rfl⟩

/-- The machine step reaches `s'` from the form's successor `u` through one protocol action, then
    replaces only the graph. The fields the memory bound reads therefore survive unchanged. -/
theorem FuehrtSchrittAus.erhaeltBuchung {L Ort Wert Raum Lok Grund Bedingung : Type} [DecidableEq L]
    {e : Einrichtung L Ort Wert Raum Lok Grund Bedingung} {t : Nat} {c : Kontext}
    {s u : Maschine.Zustand L Ort Wert Raum Lok Grund} {plan : SchrittPlan L Ort Wert Bedingung}
    {spur : SchrittSpur Ort Wert} {s' : Maschine.Zustand L Ort Wert Raum Lok Grund}
    (h : FuehrtSchrittAus e t c s u plan spur s') :
    s'.rechte = u.rechte ∧ s'.buchung.umfang = u.buchung.umfang ∧ (∀ d, s'.lokal d = u.lokal d) := by
  obtain ⟨_, _, _, v, fuehrt, _, gleich⟩ := h
  obtain ⟨hR, hU, hL⟩ := FuehrtAus.erhaeltBuchung fuehrt
  rw [gleich]
  exact ⟨hR, hU, hL⟩

/-- **A form step preserves the authority ledger, the booking extents and every non-acting frame.**
    All three outcomes of a class rule (the frame transfer, the booked access and the refusal) replace
    only the acting frame; the ledger's extents and the rights are machine-owned. -/
theorem Schrittform.ideal_erhaelt {ι : Type} (E : Klasseneinheit ι) (F : Schrittform)
    (c : Kontext) (s u : Zustand) (w : PUnit) (p : Plan) (step : F.ideal c s w [p] u)
    (hlz : ¬ F.Lebenszyklus) :
    u.rechte = s.rechte ∧ u.buchung.umfang = s.buchung.umfang ∧
      (∀ d, d ≠ c → u.lokal d = s.lokal d) := by
  obtain ⟨k, o, t⟩ := F
  cases k with
  | lokal =>
      obtain ⟨hp, hu⟩ := step
      cases hp
      subst u
      refine ⟨rfl, rfl, ?_⟩
      intro d hd
      simp only [Schrittform.nach, Function.update_of_ne hd]
  | ruf =>
      obtain ⟨hp, hu⟩ := step
      cases hp
      subst u
      refine ⟨rfl, rfl, ?_⟩
      intro d hd
      simp only [Schrittform.nach, Function.update_of_ne hd]
  | verbrauche =>
      obtain ⟨hp, hu⟩ := step
      cases hp
      subst u
      refine ⟨rfl, rfl, ?_⟩
      intro d hd
      simp only [Schrittform.nach, Function.update_of_ne hd]
  | maskiere =>
      obtain ⟨hp, hu⟩ := step
      cases hp
      subst u
      refine ⟨rfl, rfl, ?_⟩
      intro d hd
      simp only [Schrittform.nach, Function.update_of_ne hd]
  | prioritaet =>
      obtain ⟨hp, hu⟩ := step
      cases hp
      subst u
      refine ⟨rfl, rfl, ?_⟩
      intro d hd
      simp only [Schrittform.nach, Function.update_of_ne hd]
  | sendeUnterbrechung =>
      obtain ⟨hp, hu⟩ := step
      cases hp
      subst u
      refine ⟨rfl, rfl, ?_⟩
      intro d hd
      simp only [Schrittform.nach, Function.update_of_ne hd]
  | leiteLeitung =>
      obtain ⟨hp, hu⟩ := step
      cases hp
      subst u
      refine ⟨rfl, rfl, ?_⟩
      intro d hd
      simp only [Schrittform.nach, Function.update_of_ne hd]
  | lesen m =>
      rcases step with ⟨_, _, hu⟩ | ⟨_, _, _, _, hu⟩
      · subst u
        refine ⟨rfl, rfl, ?_⟩
        intro d hd
        simp only [Schrittform.verweigert, Function.update_of_ne hd]
      · subst u
        refine ⟨rfl, ?_, ?_⟩
        · simp only [Schrittform.zugriffNach, Schrittform.buchungNach]
        · intro d hd
          simp only [Schrittform.zugriffNach, Schrittform.nach, Function.update_of_ne hd]
  | schreiben m =>
      rcases step with ⟨_, _, hu⟩ | ⟨_, _, _, _, hu⟩
      · subst u
        refine ⟨rfl, rfl, ?_⟩
        intro d hd
        simp only [Schrittform.verweigert, Function.update_of_ne hd]
      · subst u
        refine ⟨rfl, ?_, ?_⟩
        · simp only [Schrittform.zugriffNach, Schrittform.buchungNach]
        · intro d hd
          simp only [Schrittform.zugriffNach, Schrittform.nach, Function.update_of_ne hd]
  | rmw m =>
      rcases step with ⟨_, _, hu⟩ | ⟨_, _, _, _, hu⟩
      · subst u
        refine ⟨rfl, rfl, ?_⟩
        intro d hd
        simp only [Schrittform.verweigert, Function.update_of_ne hd]
      · subst u
        refine ⟨rfl, ?_, ?_⟩
        · simp only [Schrittform.zugriffNach, Schrittform.buchungNach]
        · intro d hd
          simp only [Schrittform.zugriffNach, Schrittform.nach, Function.update_of_ne hd]
  | zaun m =>
      rcases step with ⟨_, _, hu⟩ | ⟨_, _, _, _, hu⟩
      · subst u
        refine ⟨rfl, rfl, ?_⟩
        intro d hd
        simp only [Schrittform.verweigert, Function.update_of_ne hd]
      · subst u
        refine ⟨rfl, ?_, ?_⟩
        · simp only [Schrittform.zugriffNach, Schrittform.buchungNach]
        · intro d hd
          simp only [Schrittform.zugriffNach, Schrittform.nach, Function.update_of_ne hd]
  | sperre a =>
      rcases step with ⟨_, _, hu⟩ | ⟨_, _, _, _, hu⟩
      · subst u
        refine ⟨rfl, rfl, ?_⟩
        intro d hd
        simp only [Schrittform.verweigert, Function.update_of_ne hd]
      · subst u
        refine ⟨rfl, ?_, ?_⟩
        · simp only [Schrittform.zugriffNach, Schrittform.buchungNach]
        · intro d hd
          simp only [Schrittform.zugriffNach, Schrittform.nach, Function.update_of_ne hd]
  | frage =>
      rcases step with ⟨_, _, hu⟩ | ⟨_, _, _, _, hu⟩
      · subst u
        refine ⟨rfl, rfl, ?_⟩
        intro d hd
        simp only [Schrittform.verweigert, Function.update_of_ne hd]
      · subst u
        refine ⟨rfl, ?_, ?_⟩
        · simp only [Schrittform.zugriffNach, Schrittform.buchungNach]
        · intro d hd
          simp only [Schrittform.zugriffNach, Schrittform.nach, Function.update_of_ne hd]
  | starte => exact (hlz (Or.inl rfl)).elim
  | beende => exact (hlz (Or.inr (Or.inl rfl))).elim
  | verbinde => exact (hlz (Or.inr (Or.inr (Or.inl rfl)))).elim
  | wechsle => exact (hlz (Or.inr (Or.inr (Or.inr rfl)))).elim

/-- **A lifecycle step keeps the authority state and the booking extents.** -/
theorem Schrittform.lebenszyklus_erhaelt {F : Schrittform} (lz : F.Lebenszyklus) {c : Kontext} {s u : Zustand}
    {w : PUnit} {p : Plan} (step : F.ideal c s w [p] u) :
    u.rechte = s.rechte ∧ u.buchung.umfang = s.buchung.umfang := by
  obtain ⟨hn, _, _, _⟩ := Schrittform.lebenszyklus_ideal lz step
  exact ⟨hn.rechte, hn.umfang⟩

/-- **The form step preserves the stack bound**: the acting frame is the class transfer, which respects
    the declared bound, and a refusal halts the frame without changing its continuation stack. -/
theorem Schrittform.ideal_stapelErhalt {ι : Type} (E : Klasseneinheit ι) (F : Schrittform)
    (stapel : F.Stapelschranke E)
    (tiefe : ∀ r : Rahmen, E.schranken.stapelTiefe r = r.fortsetzungen.length)
    (c : Kontext) (s u : Zustand) (w : PUnit) (p : Plan) (step : F.ideal c s w [p] u) :
    ∀ d n, E.schranken.stapel = some n →
      E.schranken.stapelTiefe (s.lokal d) ≤ n → E.schranken.stapelTiefe (u.lokal d) ≤ n := by
  by_cases lz : F.Lebenszyklus
  · intro d n bound vorTief
    rcases Schrittform.lebenszyklus_zustand lz step with hu | hu
    · subst u
      exact Schrittform.verweigert_stapel E F tiefe c s d n vorTief
    · subst u
      exact Schrittform.faedenNach_stapel E F stapel tiefe c s d n bound vorTief
  have andererseits := (Schrittform.ideal_erhaelt E F c s u w p step lz).2.2
  intro d n bound vorTief
  by_cases hd : d = c
  · subst d
    rw [tiefe] at vorTief ⊢
    obtain ⟨k, o, t⟩ := F
    cases k with
    | lokal =>
        obtain ⟨hp, hu⟩ := step
        cases hp
        subst u
        simp only [Schrittform.nach, Function.update_self]
        exact stapel (s.lokal c) s.regionLive 0 n bound vorTief
    | ruf =>
        obtain ⟨hp, hu⟩ := step
        cases hp
        subst u
        simp only [Schrittform.nach, Function.update_self]
        exact stapel (s.lokal c) s.regionLive 0 n bound vorTief
    | verbrauche =>
        obtain ⟨hp, hu⟩ := step
        cases hp
        subst u
        simp only [Schrittform.nach, Function.update_self]
        exact stapel (s.lokal c) s.regionLive 0 n bound vorTief
    | maskiere =>
        obtain ⟨hp, hu⟩ := step
        cases hp
        subst u
        simp only [Schrittform.nach, Function.update_self]
        exact stapel (s.lokal c) s.regionLive 0 n bound vorTief
    | prioritaet =>
        obtain ⟨hp, hu⟩ := step
        cases hp
        subst u
        simp only [Schrittform.nach, Function.update_self]
        exact stapel (s.lokal c) s.regionLive 0 n bound vorTief
    | sendeUnterbrechung =>
        obtain ⟨hp, hu⟩ := step
        cases hp
        subst u
        simp only [Schrittform.nach, Function.update_self]
        exact stapel (s.lokal c) s.regionLive 0 n bound vorTief
    | leiteLeitung =>
        obtain ⟨hp, hu⟩ := step
        cases hp
        subst u
        simp only [Schrittform.nach, Function.update_self]
        exact stapel (s.lokal c) s.regionLive 0 n bound vorTief
    | lesen m =>
        rcases step with ⟨_, _, hu⟩ | ⟨_, _, _, _, hu⟩
        · subst u
          simp only [Schrittform.verweigert, Rahmen.halt, Function.update_self]
          exact vorTief
        · subst u
          simp only [Schrittform.zugriffNach, Schrittform.nach, Function.update_self]
          exact stapel (s.lokal c) s.regionLive _ n bound vorTief
    | schreiben m =>
        rcases step with ⟨_, _, hu⟩ | ⟨_, _, _, _, hu⟩
        · subst u
          simp only [Schrittform.verweigert, Rahmen.halt, Function.update_self]
          exact vorTief
        · subst u
          simp only [Schrittform.zugriffNach, Schrittform.nach, Function.update_self]
          exact stapel (s.lokal c) s.regionLive _ n bound vorTief
    | rmw m =>
        rcases step with ⟨_, _, hu⟩ | ⟨_, _, _, _, hu⟩
        · subst u
          simp only [Schrittform.verweigert, Rahmen.halt, Function.update_self]
          exact vorTief
        · subst u
          simp only [Schrittform.zugriffNach, Schrittform.nach, Function.update_self]
          exact stapel (s.lokal c) s.regionLive _ n bound vorTief
    | zaun m =>
        rcases step with ⟨_, _, hu⟩ | ⟨_, _, _, _, hu⟩
        · subst u
          simp only [Schrittform.verweigert, Rahmen.halt, Function.update_self]
          exact vorTief
        · subst u
          simp only [Schrittform.zugriffNach, Schrittform.nach, Function.update_self]
          exact stapel (s.lokal c) s.regionLive _ n bound vorTief
    | sperre a =>
        rcases step with ⟨_, _, hu⟩ | ⟨_, _, _, _, hu⟩
        · subst u
          simp only [Schrittform.verweigert, Rahmen.halt, Function.update_self]
          exact vorTief
        · subst u
          simp only [Schrittform.zugriffNach, Schrittform.nach, Function.update_self]
          exact stapel (s.lokal c) s.regionLive _ n bound vorTief
    | frage =>
        rcases step with ⟨_, _, hu⟩ | ⟨_, _, _, _, hu⟩
        · subst u
          simp only [Schrittform.verweigert, Rahmen.halt, Function.update_self]
          exact vorTief
        · subst u
          simp only [Schrittform.zugriffNach, Schrittform.nach, Function.update_self]
          exact stapel (s.lokal c) s.regionLive _ n bound vorTief
    | starte => exact (lz (Or.inl rfl)).elim
    | beende => exact (lz (Or.inr (Or.inl rfl))).elim
    | verbinde => exact (lz (Or.inr (Or.inr (Or.inl rfl)))).elim
    | wechsle => exact (lz (Or.inr (Or.inr (Or.inr rfl)))).elim
  · rw [andererseits d hd]
    exact vorTief

/-- **The stack leg of the bound duty.** -/
theorem klassenSchrankenStapel {ι : Type} (E : Klasseneinheit ι) (F : Schrittform)
    (stapel : F.Stapelschranke E)
    (tiefe : ∀ r : Rahmen, E.schranken.stapelTiefe r = r.fortsetzungen.length)
    (c : Kontext) (vor nach : Zustand) (w : PUnit) (p : Plan) (spur : SchrittSpur Zelle Int)
    {u : Zustand} {t : Nat} (regel : F.ideal c vor w [p] u)
    (aus : FuehrtSchrittAus E.einrichtung t c vor u p spur nach)
    (vorZustand : StapelZustand E vor) : StapelZustand E nach := by
  obtain ⟨_, _, lokalGleich⟩ := FuehrtSchrittAus.erhaeltBuchung aus
  intro d n bound
  rw [lokalGleich d]
  exact Schrittform.ideal_stapelErhalt E F stapel tiefe c vor u w p regel d n bound (vorZustand d n bound)

/-- **The memory leg of the bound duty.** -/
theorem klassenSchrankenSpeicher {ι : Type} (E : Klasseneinheit ι) (F : Schrittform)
    (c : Kontext) (vor nach : Zustand) (w : PUnit) (p : Plan) (spur : SchrittSpur Zelle Int)
    {u : Zustand} {t : Nat} (regel : F.ideal c vor w [p] u)
    (aus : FuehrtSchrittAus E.einrichtung t c vor u p spur nach)
    (vorZustand : SpeicherZustand E vor) : SpeicherZustand E nach := by
  obtain ⟨rechteForm, umfangForm⟩ : u.rechte = vor.rechte ∧ u.buchung.umfang = vor.buchung.umfang := by
    by_cases lz : F.Lebenszyklus
    · exact Schrittform.lebenszyklus_erhaelt lz regel
    · obtain ⟨hr, hu, _⟩ := Schrittform.ideal_erhaelt E F c vor u w p regel lz
      exact ⟨hr, hu⟩
  obtain ⟨rechteAus, umfangAus, _⟩ := FuehrtSchrittAus.erhaeltBuchung aus
  have live : LebendeZellen nach = LebendeZellen vor := by
    unfold LebendeZellen
    rw [rechteAus, rechteForm, umfangAus, umfangForm]
  intro n bound
  rw [live]
  exact vorZustand n bound

/-- **Bounds, once per class** (`KlassenSchrankenAussage`): with the class rule at the head, a step keeps
    the stack bound through the acting form's transfer and keeps the live set through the invariance of
    the authority ledger and booking extents. -/
theorem klassenSchranken (k : Wirkungsklasse) : KlassenSchrankenAussage k := by
  intro ι E f F _ emb stapel tiefe η lauf t c w spur vor nach vorEq kopf spurEq nachEq step stapelVor speicherVor
  cases step with
  | kontext _ _ regel aus =>
      obtain ⟨i, kopfI, regelI⟩ := regel
      have fi : i = f := Option.some.inj (kopfI.symm.trans kopf)
      subst i
      rw [emb.regel] at regelI
      exact ⟨klassenSchrankenStapel E F stapel tiefe c vor nach w _ spur regelI aus stapelVor,
        klassenSchrankenSpeicher E F c vor nach w _ spur regelI aus speicherVor⟩

end Gabbro.Core.Ast.Semantik
