/-
  File:      Core/Fortschritt/Beweise/SperrStarkEinheit4.lean
  Subject:   A NON-VACUOUS ACCEPTED UNIT for the strong waiting-run satisfiability (M8 2b).

  Unlike the earlier draft, the lock is NOT held by the loader: it starts free with a ticket
  queue, and every holder of the run follows a real admitted take from that free start. The rule admits tickets, takes
  and releases only for the three statically dispatched contexts A, B and C; the entry context
  of a restart is a different context, so no holder can arise after a crash. The start data masks
  every vector and keeps an NMI active, so no interrupt can preempt a dispatched holder before a
  crash. Hence holder eligibility is proved globally, over every reachable ideal cut, and not by
  an empty ideal lock state.
-/
module

public import Core.Fortschritt.SperrErfuellbar
public import Core.Fortschritt.SperrAnnahmeE1
public import Core.Fortschritt.SperrE2

@[expose] public section

namespace Gabbro.Core.Fortschritt

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog
open Gabbro.Core.Annahme
open Gabbro.Core.Beobachtung

/-- The third statically dispatched context. -/
def C4 : Kontext := Kontext.faden 2

/-- The restart entry is deliberately outside the dispatched set. -/
def eintritt4 : Kontext := Kontext.faden 99

def dispatch4 : Kern → Option Kontext
  | 0 => some A
  | 1 => some B
  | 2 => some C4
  | _ + 3 => none

/-- Start data with no preempting interrupt: vectors masked, an NMI active. -/
def wDatenGesperrt4 (Dispatch : Kern → Option Kontext) : Startdaten Unit Unit Bool Unit :=
  ⟨fun _ => false, fun _ => .laeuft,
    fun j => ⟨Dispatch j, .nutzer, (), fun _ => true, 0, true, []⟩,
    ⟨fun _ => false, fun _ => 0⟩⟩

def wEinrichtungGesperrt4 : Einrichtung Unit Unit Unit Unit Bool Unit Unit :=
  ⟨fun _ => (), fun _ => (), fun _ => (), fun _ => (), fun _ _ _ => False, fun _ _ => True,
    ⟨0, 1⟩, ⟨eintritt4, 0, fun _ => wDatenGesperrt4 dispatch4, fun _ _ => (), id⟩,
    fun _ => 0, fun _ _ _ => none⟩

/-- The contexts whose acquisition the rule admits. -/
def statisch4 (c : Kontext) : Prop := c = A ∨ c = B ∨ c = C4

theorem statisch4_A : statisch4 A := Or.inl rfl
theorem statisch4_B : statisch4 B := Or.inr (Or.inl rfl)
theorem statisch4_C : statisch4 C4 := Or.inr (Or.inr rfl)

theorem eintritt4_nicht_statisch4 : ¬ statisch4 eintritt4 := by
  intro h
  rcases h with h | h | h
  · cases h
  · cases h
  · cases h

/-- The hand-over rule: tickets, takes and releases as the lock rule allows, but acquisition
    only by statically dispatched contexts; every other context may only stutter. -/
def e4Regel (c : Kontext) (s : Zustand Unit Unit Unit Unit Bool Unit) (w : Unit)
    (es : List (SchrittPlan Unit Unit Unit Unit)) (u : Zustand Unit Unit Unit Unit Bool Unit) :
    Prop :=
  (statisch4 c ∧
    ((∃ next, SperrSchritt .ticket c (s.sperren ()) next ∧ es = [ticketPlan] ∧
        u = toggleUpdate c s) ∨
     (∃ next, SperrSchritt .nehmen c (s.sperren ()) next ∧ es = [nehmenPlan] ∧ u = s))) ∨
  (∃ next, SperrSchritt .geben c (s.sperren ()) next ∧ es = [wGebenPlan] ∧ u = s) ∨
  (es = [stutterPlan] ∧ u = s)

def e4System : MaschinenSystem Unit Unit Unit Unit Bool Unit Unit Unit Unit :=
  ⟨fun _ => ⟨e4Regel, e4Regel⟩, fun _ _ => some (), fun _ _ => False, fun _ _ _ => False⟩

/-- The implementation loader returns a free lock with tickets for A and B: no holder is seeded,
    and the holder of the run arises only by an admitted take. All vectors are masked and an NMI
    is active, so no interrupt can preempt a dispatched holder. -/
def s4_0 : Zustand Unit Unit Unit Unit Bool Unit :=
  { Zustand.start (L := Unit) (fun _ => false) (fun _ => .laeuft)
      (fun j => ⟨dispatch4 j, .nutzer, (), fun _ => true, 0, true, []⟩)
      ⟨fun _ => false, fun _ => 0⟩ (fun _ => ()) (.leer (fun _ => 0)) with
    sperren := fun _ => ⟨none, [A, B]⟩ }

def E_4 : Einheit Unit Unit Unit Unit Bool Unit Unit Unit Unit :=
  { E_1 with
    einrichtung := wEinrichtungGesperrt4
    system := e4System
    startdaten := fun _ => wDatenGesperrt4 dispatch4
    laden := fun _ _ => some s4_0 }

/-- The ideal run starts from the canonical start with the same masked dispatch and an empty lock. -/
noncomputable def s4_ideal0 : Zustand Unit Unit Unit Unit Bool Unit := (I.start E_4 s0).2

theorem start_E_4 : (I.start E_4 s0).2 = s4_ideal0 := rfl

theorem s4_ideal0_lock : (s4_ideal0.sperren ()).besitzer = none := rfl

theorem s4_ideal0_schlange : (s4_ideal0.sperren ()).schlange = [] := rfl

theorem s4_ideal0_kerne0 : (s4_ideal0.kerne 0).laeuft = some A := rfl
theorem s4_ideal0_kerne1 : (s4_ideal0.kerne 1).laeuft = some B := rfl
theorem s4_ideal0_kerne2 : (s4_ideal0.kerne 2).laeuft = some C4 := rfl

theorem s4_ideal0_live : ∀ c, s4_ideal0.status c = .laeuft := fun _ => rfl

theorem s4_ideal0_nmi (k : Kern) : (s4_ideal0.kerne k).nmiAktiv = true := by
  cases k <;> rfl

theorem s4_ideal0_maske (k : Kern) : (s4_ideal0.kerne k).maske = fun _ => true := by
  cases k <;> rfl

theorem e4halten : E_4.schranken.halten () = some 5 := rfl

theorem e4_sec : AbschnittWartefrei E_4 :=
  abschnittWartefrei_ohne_blockade _ fun _ _ _ hb => hb

theorem s4_0_lock : (s4_0.sperren ()).besitzer = none := rfl

theorem s4_0_schlange : (s4_0.sperren ()).schlange = [A, B] := rfl

theorem s4_0_kerne0 : (s4_0.kerne 0).laeuft = some A := rfl
theorem s4_0_kerne1 : (s4_0.kerne 1).laeuft = some B := rfl
theorem s4_0_kerne2 : (s4_0.kerne 2).laeuft = some C4 := rfl

theorem s4_0_live : ∀ c, s4_0.status c = .laeuft := fun _ => rfl

theorem s4_0_nmi (k : Kern) : (s4_0.kerne k).nmiAktiv = true := by
  cases k <;> rfl

theorem s4_0_maske (k : Kern) : (s4_0.kerne k).maske = fun _ => true := by
  cases k <;> rfl

theorem s4_0_graph_gut : s4_0.graph.graph.Konsistent ∧ s4_0.graph.graph.Vollstaendig :=
  ⟨Speicher.Zustand.leer_konsistent, Speicher.Zustand.leer_vollstaendig⟩

theorem e4_ideal_ticket {c : Kontext} {s : Zustand Unit Unit Unit Unit Bool Unit}
    {next : SperrZustand} (hs : statisch4 c)
    (hn : SperrSchritt .ticket c (s.sperren ()) next) :
    E_4.system.ISchritt c s () [ticketPlan] (toggleUpdate c s) := by
  refine ⟨(), rfl, ?_⟩
  exact Or.inl ⟨hs, Or.inl ⟨next, hn, rfl, rfl⟩⟩

theorem e4_ideal_nehmen {c : Kontext} {s : Zustand Unit Unit Unit Unit Bool Unit}
    {next : SperrZustand} (hs : statisch4 c)
    (hn : SperrSchritt .nehmen c (s.sperren ()) next) :
    E_4.system.ISchritt c s () [nehmenPlan] s := by
  refine ⟨(), rfl, ?_⟩
  exact Or.inl ⟨hs, Or.inr ⟨next, hn, rfl, rfl⟩⟩

theorem e4_impl_nehmen {c : Kontext} {s : Zustand Unit Unit Unit Unit Bool Unit}
    {next : SperrZustand} (hs : statisch4 c)
    (hn : SperrSchritt .nehmen c (s.sperren ()) next) :
    E_4.system.ImplSchritt c s () [nehmenPlan] s := by
  refine ⟨(), rfl, ?_⟩
  exact Or.inl ⟨hs, Or.inr ⟨next, hn, rfl, rfl⟩⟩

theorem e4_ideal_geben {c : Kontext} {s : Zustand Unit Unit Unit Unit Bool Unit}
    {next : SperrZustand} (hg : (s.sperren ()).Gibt c next) :
    E_4.system.ISchritt c s () [wGebenPlan] s := by
  refine ⟨(), rfl, ?_⟩
  exact Or.inr (Or.inl ⟨next, SperrSchritt.geben hg, rfl, rfl⟩)

theorem e4_impl_geben {c : Kontext} {s : Zustand Unit Unit Unit Unit Bool Unit}
    {next : SperrZustand} (hg : (s.sperren ()).Gibt c next) :
    E_4.system.ImplSchritt c s () [wGebenPlan] s := by
  refine ⟨(), rfl, ?_⟩
  exact Or.inr (Or.inl ⟨next, SperrSchritt.geben hg, rfl, rfl⟩)

/-- Acceptance, local rows: every plan has an empty footprint and records nothing. -/

theorem e4_regel_lokal (i : Unit) : RegelLokal E_4 i := by
  intro c s u w plan h
  cases i
  have hrule : e4Regel c s w [plan] u := h
  rcases hrule with ⟨_, ⟨_, _, hpeq, _⟩ | ⟨_, _, hpeq, _⟩⟩ |
    ⟨_, _, hpeq, _⟩ | ⟨hpeq, _⟩
  all_goals
    obtain rfl := (List.cons.inj hpeq).1
    exact ⟨fun x hx => (List.not_mem_nil hx).elim,
      fun l hl => (List.not_mem_nil hl).elim⟩

theorem e4_aussen_gueltig : AussenGueltig E_4 := by
  apply aussen_gueltig_aus_kontext
  intro run t s c w spur s' step
  cases step with
  | kontext normal bereit regel aus =>
    obtain ⟨i, _, hideal⟩ := regel
    cases i
    rcases hideal with ⟨_, ⟨_, _, hpeq, hueq⟩ | ⟨_, _, hpeq, hueq⟩⟩ |
      ⟨_, _, hpeq, hueq⟩ | ⟨hpeq, hueq⟩
    · obtain rfl := (List.cons.inj hpeq).1
      obtain ⟨_, _, _, _, hF, _, hziel⟩ := aus
      have hakt : ticketPlan.aktion = .sperre () .ticket := rfl
      rw [hakt] at hF
      obtain ⟨_, au⟩ := spur
      cases hF
      case sperre _ _ =>
        have hwb : s'.buchung.wirkungen = s.buchung.wirkungen := by
          rw [hziel]
          rfl
        refine ⟨⟨fun ev h2 => (List.not_mem_nil h2).elim,
          ⟨[], hwb.trans (List.append_nil _).symm, fun _ h2 => (List.not_mem_nil h2).elim⟩⟩,
          fun hoffen q hmem hepo hant => ?_⟩
        rw [hziel] at hmem hepo hant ⊢
        exact hoffen q hmem hepo hant
    · obtain rfl := (List.cons.inj hpeq).1
      obtain ⟨_, _, _, _, hF, _, hziel⟩ := aus
      have hakt : nehmenPlan.aktion = .sperre () .nehmen := rfl
      rw [hakt] at hF
      obtain ⟨_, au⟩ := spur
      cases hF
      case sperre _ _ =>
        have hwb : s'.buchung.wirkungen = s.buchung.wirkungen := by
          rw [hziel, hueq]
        refine ⟨⟨fun ev h2 => (List.not_mem_nil h2).elim,
          ⟨[], hwb.trans (List.append_nil _).symm, fun _ h2 => (List.not_mem_nil h2).elim⟩⟩,
          fun hoffen q hmem hepo hant => ?_⟩
        rw [hziel, hueq] at hmem hepo hant ⊢
        exact hoffen q hmem hepo hant
    · obtain rfl := (List.cons.inj hpeq).1
      obtain ⟨_, _, _, _, hF, _, hziel⟩ := aus
      have hakt : wGebenPlan.aktion = .sperre () .geben := rfl
      rw [hakt] at hF
      obtain ⟨_, au⟩ := spur
      cases hF
      case sperre _ _ =>
        have hwb : s'.buchung.wirkungen = s.buchung.wirkungen := by
          rw [hziel, hueq]
        refine ⟨⟨fun ev h2 => (List.not_mem_nil h2).elim,
          ⟨[], hwb.trans (List.append_nil _).symm, fun _ h2 => (List.not_mem_nil h2).elim⟩⟩,
          fun hoffen q hmem hepo hant => ?_⟩
        rw [hziel, hueq] at hmem hepo hant ⊢
        exact hoffen q hmem hepo hant
    · obtain rfl := (List.cons.inj hpeq).1
      obtain ⟨_, _, _, _, hF, _, hziel⟩ := aus
      have hakt : stutterPlan.aktion = .intern := rfl
      rw [hakt] at hF
      obtain ⟨_, au⟩ := spur
      cases hF
      case intern =>
        have hwb : s'.buchung.wirkungen = s.buchung.wirkungen := by
          rw [hziel, hueq]
        refine ⟨⟨fun ev h2 => (List.not_mem_nil h2).elim,
          ⟨[], hwb.trans (List.append_nil _).symm, fun _ h2 => (List.not_mem_nil h2).elim⟩⟩,
          fun hoffen q hmem hepo hant => ?_⟩
        rw [hziel, hueq] at hmem hepo hant ⊢
        exact hoffen q hmem hepo hant

theorem e4_fluss : FlussLokal E_4 := by
  refine ⟨?_, fun f => ?_⟩
  · intro s₁ s₂ _
    refine ⟨fun c p h => (Bool.false_ne_true (e1Hoch_verborgen.symm.trans h)).elim,
      fun c => rfl, fun x => rfl, rfl, rfl, fun c => rfl⟩
  · cases f with
    | unit =>
      refine ⟨?_, fun low => (Bool.false_ne_true (e1Hoch_verborgen.symm.trans low)).elim⟩
      intro c v w p u step
      have hideal : e4Regel c v w [p] u := step.2
      refine ⟨⟨rfl, fun _ _ _ mem => (List.not_mem_nil mem).elim⟩, fun _ => ?_⟩
      rcases hideal with ⟨_, ⟨_, _, hpeq, rfl⟩ | ⟨_, _, hpeq, rfl⟩⟩ |
        ⟨_, _, hpeq, rfl⟩ | ⟨hpeq, rfl⟩
      all_goals
        obtain rfl := (List.cons.inj hpeq).1
        exact ⟨⟨fun c p h => (Bool.false_ne_true (e1Hoch_verborgen.symm.trans h)).elim,
          fun c => rfl, fun x => rfl, rfl, rfl, fun c => rfl⟩, rfl, rfl⟩

theorem e4_schranken_lokal : SchrankenLokal E_4 :=
  schrankenLokal_leer rfl rfl rfl

theorem e4_isolation : RegelIsolation E_4 (tabellePlan eineTabelle) () := by
  intro t c s u s' w p spur _ _
  exact ⟨fun a l _ _ hFremd => hFremd (Or.inl rfl),
    fun ev _ d _ hFremd => hFremd (Or.inl rfl)⟩

theorem e4_domaenen : DomaenenLokal E_4 := by
  refine ⟨eineTabelle_akzeptiert, fun s c i _ => ?_⟩
  cases i
  exact e4_isolation

theorem e4_klauseln : KlauselnWahr E_4 := by
  intro ρ _
  exact ⟨fun _ h => (List.not_mem_nil h).elim, fun _ _ h => (List.not_mem_nil h).elim,
    fun _ _ _ h => (List.not_mem_nil h).elim⟩

end Gabbro.Core.Fortschritt
