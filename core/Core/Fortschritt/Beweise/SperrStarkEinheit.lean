/-
  File:      Core/Fortschritt/Beweise/SperrStarkEinheit.lean
  Subject:   THE ACCEPTED HAND-OVER UNIT of the strong waiting-run satisfiability (M8 2b).

  `E_3` keeps the E_1 rule shape (no take) but loads a real holder at queue position zero with
  the waiter at position one. The holder row is a reachability invariant over every ideal run
  and cut: an ideal start is free and the rule never takes, so no ideal cut owns. The concrete
  trace is evaluated only in `SperrStarkLauf`, never here.
-/
module

public import Core.Fortschritt.SperrErfuellbar
public import Core.Fortschritt.SperrAnnahmeE1

@[expose] public section

namespace Gabbro.Core.Fortschritt

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog
open Gabbro.Core.Annahme
open Gabbro.Core.Beobachtung

/-- The hand-over rule: the owner may release, everyone may stutter. There is no take, so an
    ideal run starting from the free canonical start never acquires the lock. -/
def e3Regel (c : Kontext) (s : Zustand Unit Unit Unit Unit Bool Unit) (w : Unit)
    (es : List (SchrittPlan Unit Unit Unit Unit)) (u : Zustand Unit Unit Unit Unit Bool Unit) :
    Prop :=
  (∃ next, SperrSchritt .geben c (s.sperren ()) next ∧ es = [wGebenPlan] ∧ u = s) ∨
  (es = [stutterPlan] ∧ u = s)

def e3System : MaschinenSystem Unit Unit Unit Unit Bool Unit Unit Unit Unit :=
  ⟨fun _ => ⟨e3Regel, e3Regel⟩, fun _ _ => some (), fun _ _ => False, fun _ _ _ => False⟩

/-- The held start of the implementation run: `A` owns, `A` heads the queue, waiter `B` sits at
    position one. -/
def s3_0 : Zustand Unit Unit Unit Unit Bool Unit :=
  { zE0 with sperren := fun _ => ⟨some A, [A, B]⟩ }

def E_3 : Einheit Unit Unit Unit Unit Bool Unit Unit Unit Unit :=
  { E_1 with system := e3System, laden := fun _ _ => some s3_0 }

theorem e3halten : E_3.schranken.halten () = some 5 := rfl

theorem e3_sec : AbschnittWartefrei E_3 :=
  abschnittWartefrei_ohne_blockade _ fun _ _ _ hb => hb

theorem s3_0_lock : (s3_0.sperren ()) = ⟨some A, [A, B]⟩ := rfl

theorem s3_0_kerne0 : (s3_0.kerne 0).laeuft = some A := rfl

theorem s3_0_kerne1 : (s3_0.kerne 1).laeuft = some B := rfl

theorem s3_0_live : ∀ c, s3_0.status c = .laeuft := fun _ => rfl

theorem s3_0_graph_gut : s3_0.graph.graph.Konsistent ∧ s3_0.graph.graph.Vollstaendig :=
  ⟨Speicher.Zustand.leer_konsistent, Speicher.Zustand.leer_vollstaendig⟩

theorem e3_ideal_geben {c : Kontext} {s : Zustand Unit Unit Unit Unit Bool Unit}
    {next : SperrZustand} (hg : (s.sperren ()).Gibt c next) :
    E_3.system.ISchritt c s () [wGebenPlan] s := by
  refine ⟨(), rfl, ?_⟩
  show e3Regel c s () [wGebenPlan] s
  exact Or.inl ⟨next, SperrSchritt.geben hg, rfl, rfl⟩

theorem e3_impl_geben {c : Kontext} {s : Zustand Unit Unit Unit Unit Bool Unit}
    {next : SperrZustand} (hg : (s.sperren ()).Gibt c next) :
    E_3.system.ImplSchritt c s () [wGebenPlan] s := by
  refine ⟨(), rfl, ?_⟩
  show e3Regel c s () [wGebenPlan] s
  exact Or.inl ⟨next, SperrSchritt.geben hg, rfl, rfl⟩

/- Acceptance: the local rows carry over from `E_1` at the smaller rule. -/

theorem e3_regel_lokal (i : Unit) : RegelLokal E_3 i := by
  intro c s u w plan h
  cases i
  have hrule : e3Regel c s w [plan] u := h
  rcases hrule with ⟨_, _, hpeq, _⟩ | ⟨hpeq, _⟩
  · obtain rfl := (List.cons.inj hpeq).1
    exact ⟨fun x hx => (List.not_mem_nil hx).elim, fun l hl => (List.not_mem_nil hl).elim⟩
  · obtain rfl := (List.cons.inj hpeq).1
    exact ⟨fun x hx => (List.not_mem_nil hx).elim, fun l hl => (List.not_mem_nil hl).elim⟩

theorem e3_aussen_gueltig : AussenGueltig E_3 := by
  apply aussen_gueltig_aus_kontext
  intro run t s c w spur s' step
  cases step with
  | kontext normal bereit regel aus =>
    obtain ⟨i, _, hideal⟩ := regel
    cases i
    rcases hideal with ⟨_, _, hpeq, hueq⟩ | ⟨hpeq, hueq⟩
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

theorem e3_fluss : FlussLokal E_3 := by
  refine ⟨?_, fun f => ?_⟩
  · intro s₁ s₂ _
    refine ⟨fun c p h => (Bool.false_ne_true (e1Hoch_verborgen.symm.trans h)).elim,
      fun c => rfl, fun x => rfl, rfl, rfl, fun c => rfl⟩
  · cases f with
    | unit =>
      refine ⟨?_, fun low => (Bool.false_ne_true (e1Hoch_verborgen.symm.trans low)).elim⟩
      intro c v w p u step
      have hideal : e3Regel c v w [p] u := step.2
      refine ⟨⟨rfl, fun _ _ _ mem => (List.not_mem_nil mem).elim⟩, fun _ => ?_⟩
      rcases hideal with ⟨_, _, hpeq, rfl⟩ | ⟨hpeq, rfl⟩
      · obtain rfl := (List.cons.inj hpeq).1
        exact ⟨⟨fun c p h => (Bool.false_ne_true (e1Hoch_verborgen.symm.trans h)).elim,
          fun c => rfl, fun x => rfl, rfl, rfl, fun c => rfl⟩, rfl, rfl⟩
      · obtain rfl := (List.cons.inj hpeq).1
        exact ⟨⟨fun c p h => (Bool.false_ne_true (e1Hoch_verborgen.symm.trans h)).elim,
          fun c => rfl, fun x => rfl, rfl, rfl, fun c => rfl⟩, rfl, rfl⟩

theorem e3_schranken_lokal : SchrankenLokal E_3 :=
  schrankenLokal_leer rfl rfl rfl

theorem e3_isolation : RegelIsolation E_3 (tabellePlan eineTabelle) () := by
  intro t c s u s' w p spur _ _
  exact ⟨fun a l _ _ hFremd => hFremd (Or.inl rfl),
    fun ev _ d _ hFremd => hFremd (Or.inl rfl)⟩

theorem e3_domaenen : DomaenenLokal E_3 := by
  refine ⟨eineTabelle_akzeptiert, fun s c i _ => ?_⟩
  cases i
  exact e3_isolation

theorem e3_klauseln : KlauselnWahr E_3 := by
  intro ρ _
  exact ⟨fun _ h => (List.not_mem_nil h).elim, fun _ _ h => (List.not_mem_nil h).elim,
    fun _ _ _ h => (List.not_mem_nil h).elim⟩

/- The holder row is a reachability invariant over every ideal run and cut: an ideal run starts
   free and the rule never takes, so no ideal cut owns. No concrete trace is evaluated here. -/

theorem e3_I_schritt_erhaelt_frei {hw : HwLauf} {t : Nat}
    {s : Zustand Unit Unit Unit Unit Bool Unit}
    {ev : SchrittWahl Unit × SchrittSpur Unit Unit} {s' : Zustand Unit Unit Unit Unit Bool Unit}
    (hpre : (s.sperren ()).besitzer = none)
    (step : I.Schritt E_3.einrichtung E_3.system E_3.katalog hw t s ev s') :
    (s'.sperren ()).besitzer = none := by
  cases step with
  | @kontext _ u plan spur c w _ _ hreg haus =>
    obtain ⟨i, _, hreg⟩ := hreg
    cases i
    rcases hreg with ⟨_, hss, hpeq, hueq⟩ | ⟨hpeq, hueq⟩
    · subst u
      obtain rfl := (List.cons.inj hpeq).1
      obtain ⟨_, au⟩ := spur
      cases hss with
      | geben hg =>
        obtain ⟨q, hslock, _⟩ := gibt_abgeben hg
        rw [hslock] at hpre
        cases hpre
    · subst u
      obtain rfl := (List.cons.inj hpeq).1
      obtain ⟨_, au⟩ := spur
      obtain ⟨_, _, _, v, hF, _, heq⟩ := haus
      cases hF
      case intern =>
        rw [heq]
        exact hpre
  | antwort _ h =>
    obtain ⟨_, _, _, heq⟩ := h
    rw [heq]
    exact hpre
  | interrupt _ h =>
    obtain ⟨k, irq, c, nmi, hopp, haus, hnimm, hruht, hspur, hmem, hstate⟩ := h
    rw [hstate]
    simpa only [Zustandseintritt] using hpre
  | absturz h =>
    exact (absturz_leert_schlange (l := ()) h).2

theorem e3_kein_besitzer_I (ρ : I.Lauf E_3) (lauf : I.Laeufe E_3 ρ) (t : Nat)
    (s : Zustand Unit Unit Unit Unit Bool Unit) (hzs : ρ.zeit.zustand t = s) :
    (s.sperren ()).besitzer = none := by
  revert s hzs
  induction t with
  | zero =>
    intro s hzs
    have h0 := lauf.2.2.2.1
    rw [h0] at hzs
    subst hzs
    rfl
  | succ t ih =>
    intro s hzs
    cases ρ.zeit.takt t with
    | wartet _ heq _ =>
      rw [heq] at hzs
      exact ih _ hzs
    | schritt _ step =>
      have hpre := ih _ rfl
      have hpost := e3_I_schritt_erhaelt_frei hpre step
      rw [hzs] at hpost
      exact hpost


theorem e3_halter : SperrHalterHalten E_3 := by
  intro ρ lauf t l h hown
  cases l
  have hfree := e3_kein_besitzer_I ρ lauf t.val _ rfl
  rw [hfree] at hown
  cases hown

theorem waechter_E_3 : WaechterHalten E_3 :=
  ⟨fun ρ _ t op args h => by
     dsimp [kanonischeVerwendung, E_3, Quelltabellen.leer] at h
     exact h.elim,
   fun ρ _ t hC => by
     obtain ⟨C, hC⟩ := hC
     obtain ⟨c, hc⟩ := hC.1
     obtain ⟨b, hblock, _, _, _⟩ := hC.2 c hc
     exact hblock,
   e3_halter⟩

theorem akzeptiert_E_3 : Akzeptiert E_3 :=
  ⟨⟨Plattform.x86_64.katalog_wohlgeformt, e3_regel_lokal,
     ⟨Gabbro.Core.Aussen.zulassung_m2 _, e3_aussen_gueltig⟩, e3_fluss,
     e3_schranken_lokal, e3_sec, e3_domaenen⟩, e3_klauseln, waechter_E_3⟩


end Gabbro.Core.Fortschritt
