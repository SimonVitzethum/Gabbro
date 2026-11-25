/-
  File:      core/Core/Ast/Semantik/Runtime/Klasse/Beweise/RegisterCommit.lean
  Subject:   THE REGISTER AND COMMIT SAFETY LEGS, ONCE PER EFFECT CLASS (MK-03). A step of a class records
             no outside event, or exactly one question issued by the guarded `frage` form. Hence a class
             step never commits an outside operation (a commit needs an answer event), and the only event
             that can touch a device is a question whose guard carries `RegisterErlaubt`. The effects
             ledger is untouched by every class rule and by every protocol action, so the new effects of
             a class step are empty. Both legs are statements about every unit that embeds a form of the
             class; the pinned statement `KlassenAussagen` is not changed.
 -/
module

public import Core.Ast.Semantik.Runtime.Klasse.Pflichten
public import Core.Sicherheit.KatalogSchritt
public import Core.Ast.Semantik.Runtime.Klasse.Beweise.Faden

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Sicherheit

/-- The action of the plan of a class step, and the authority of a question it issues. Every other
    action is a private step, a refused access or a lock action; only a guarded `frage` form plans a
    question, and its guard is `Zustand.fragenBefugt`. -/
private theorem klassen_aktion {F : Schrittform} {c : Kontext} {s u : Zustand} {plan : Plan}
    (step : F.impl c s () [plan] u) :
    plan.aktion.Still ∨ (∃ l a, plan.aktion = .sperre l a) ∨
      (∃ q : Frage, plan.aktion = .frage q ∧ s.fragenBefugt c q) := by
  obtain ⟨k, o, tr⟩ := F
  cases k with
  | lokal =>
      have hp : plan = Semantik.plan := (List.cons.inj step.1).1
      subst plan
      exact Or.inl trivial
  | ruf =>
      have hp : plan = Semantik.plan := (List.cons.inj step.1).1
      subst plan
      exact Or.inl trivial
  | verbrauche =>
  | maskiere =>
      have hp : plan = Semantik.plan := (List.cons.inj step.1).1
      subst plan
      exact Or.inl trivial
  | prioritaet =>
      have hp : plan = Semantik.plan := (List.cons.inj step.1).1
      subst plan
      exact Or.inl trivial
  | sendeUnterbrechung =>
      have hp : plan = Semantik.plan := (List.cons.inj step.1).1
      subst plan
      exact Or.inl trivial
  | leiteLeitung =>
      have hp : plan = Semantik.plan := (List.cons.inj step.1).1
      subst plan
      exact Or.inl trivial
  | lesen m =>
      rcases step with ⟨_, same, _⟩ | ⟨_, v, _, same, _⟩
      · have hp : plan = Semantik.plan := (List.cons.inj same).1
        subst plan
        exact Or.inl trivial
      · have hp : plan = Wirkungsklasse.plan (.lesen m) (o (s.lokal c)) v := (List.cons.inj same).1
        subst plan
        exact Or.inl trivial
  | schreiben m =>
      rcases step with ⟨_, same, _⟩ | ⟨_, v, _, same, _⟩
      · have hp : plan = Semantik.plan := (List.cons.inj same).1
        subst plan
        exact Or.inl trivial
      · have hp : plan = Wirkungsklasse.plan (.schreiben m) (o (s.lokal c)) v := (List.cons.inj same).1
        subst plan
        exact Or.inl trivial
  | rmw m =>
      rcases step with ⟨_, same, _⟩ | ⟨_, v, _, same, _⟩
      · have hp : plan = Semantik.plan := (List.cons.inj same).1
        subst plan
        exact Or.inl trivial
      · have hp : plan = Wirkungsklasse.plan (.rmw m) (o (s.lokal c)) v := (List.cons.inj same).1
        subst plan
        exact Or.inl trivial
  | zaun m =>
      rcases step with ⟨_, same, _⟩ | ⟨_, v, _, same, _⟩
      · have hp : plan = Semantik.plan := (List.cons.inj same).1
        subst plan
        exact Or.inl trivial
      · have hp : plan = Wirkungsklasse.plan (.zaun m) (o (s.lokal c)) v := (List.cons.inj same).1
        subst plan
        exact Or.inl trivial
  | sperre a =>
      rcases step with ⟨_, same, _⟩ | ⟨_, v, _, same, _⟩
      · have hp : plan = Semantik.plan := (List.cons.inj same).1
        subst plan
        exact Or.inl trivial
      · have hp : plan = Wirkungsklasse.plan (.sperre a) (o (s.lokal c)) v := (List.cons.inj same).1
        subst plan
        exact Or.inr (Or.inl ⟨(o (s.lokal c)).sperre, a, rfl⟩)
  | frage =>
      rcases step with ⟨_, same, _⟩ | ⟨befugt, v, _, same, _⟩
      · have hp : plan = Semantik.plan := (List.cons.inj same).1
        subst plan
        exact Or.inl trivial
      · change ∃ q : Frage, (o (s.lokal c)).frage = some q ∧ s.fragenBefugt c q at befugt
        obtain ⟨q, hoq, hbefugt⟩ := befugt
        have hp : plan = Wirkungsklasse.plan .frage (o (s.lokal c)) v := (List.cons.inj same).1
        subst plan
        exact Or.inr (Or.inr ⟨q, by simp only [Wirkungsklasse.plan, Operand.fragePlan, hoq], hbefugt⟩)
  | starte =>
      rcases step with ⟨_, same, _⟩ | ⟨_, same, _⟩
      · have hp : plan = Semantik.plan := (List.cons.inj same).1
        subst plan
        exact Or.inl trivial
      · have hp : plan = Wirkungsklasse.plan .starte (o (s.lokal c)) 0 := (List.cons.inj same).1
        subst plan
        exact Or.inl trivial
  | beende =>
      rcases step with ⟨_, same, _⟩ | ⟨_, same, _⟩
      · have hp : plan = Semantik.plan := (List.cons.inj same).1
        subst plan
        exact Or.inl trivial
      · have hp : plan = Wirkungsklasse.plan .beende (o (s.lokal c)) 0 := (List.cons.inj same).1
        subst plan
        exact Or.inl trivial
  | verbinde =>
      rcases step with ⟨_, same, _⟩ | ⟨_, same, _⟩
      · have hp : plan = Semantik.plan := (List.cons.inj same).1
        subst plan
        exact Or.inl trivial
      · have hp : plan = Wirkungsklasse.plan .verbinde (o (s.lokal c)) 0 := (List.cons.inj same).1
        subst plan
        exact Or.inl trivial
  | wechsle =>
      rcases step with ⟨_, same, _⟩ | ⟨_, same, _⟩
      · have hp : plan = Semantik.plan := (List.cons.inj same).1
        subst plan
        exact Or.inl trivial
      · have hp : plan = Wirkungsklasse.plan .wechsle (o (s.lokal c)) 0 := (List.cons.inj same).1
        subst plan
        exact Or.inl trivial

/-- Only an authorised question plan has a `.frage` action; its guard carries the device authority. -/
private theorem frage_aktion_befugt {F : Schrittform} {c : Kontext} {s u : Zustand} {plan : Plan}
    (step : F.impl c s () [plan] u) {q : Frage} (hq : plan.aktion = .frage q) :
    s.fragenBefugt c q := by
  rcases klassen_aktion step with still | sperre | frage
  · rw [hq] at still
    exact False.elim still
  · obtain ⟨l, a, hs⟩ := sperre
    rw [hs] at hq
    cases hq
  · obtain ⟨q', hq', befugt⟩ := frage
    rw [hq'] at hq
    cases hq
    exact befugt

/-- A class step leaves the effects ledger unchanged: its frame transfer books an address at most, and
    each protocol action touches only its own field. -/
private theorem wirkungen_gleich (F : Schrittform) (c : Kontext) (s u : Zustand) (plan : Plan)
    (step : F.impl c s () [plan] u) : u.buchung.wirkungen = s.buchung.wirkungen := by
  obtain ⟨k, o, tr⟩ := F
  cases k with
  | lokal =>
      rw [step.2]
      rfl
  | ruf =>
      rw [step.2]
      rfl
  | verbrauche =>
  | maskiere =>
      rw [step.2]
      rfl
  | prioritaet =>
      rw [step.2]
      rfl
  | sendeUnterbrechung =>
      rw [step.2]
      rfl
  | leiteLeitung =>
      rw [step.2]
      rfl
  | lesen m =>
      rcases step with ⟨_, _, hu⟩ | ⟨_, v, _, _, hu⟩ <;> rw [hu] <;> rfl
  | schreiben m =>
      rcases step with ⟨_, _, hu⟩ | ⟨_, v, _, _, hu⟩ <;> rw [hu] <;> rfl
  | rmw m =>
      rcases step with ⟨_, _, hu⟩ | ⟨_, v, _, _, hu⟩ <;> rw [hu] <;> rfl
  | zaun m =>
      rcases step with ⟨_, _, hu⟩ | ⟨_, v, _, _, hu⟩ <;> rw [hu] <;> rfl
  | sperre a =>
      rcases step with ⟨_, _, hu⟩ | ⟨_, v, _, _, hu⟩ <;> rw [hu] <;> rfl
  | frage =>
      rcases step with ⟨_, _, hu⟩ | ⟨_, v, _, _, hu⟩ <;> rw [hu] <;> rfl
  | starte =>
      rcases step with ⟨_, _, hu⟩ | ⟨_, _, hu⟩
      · rw [hu]
        rfl
      · rw [hu]
        exact (Schrittform.faedenNach_nurFaden ⟨.starte, o, tr⟩ c s).wirkungen
  | beende =>
      rcases step with ⟨_, _, hu⟩ | ⟨_, _, hu⟩
      · rw [hu]
        rfl
      · rw [hu]
        exact (Schrittform.faedenNach_nurFaden ⟨.beende, o, tr⟩ c s).wirkungen
  | verbinde =>
      rcases step with ⟨_, _, hu⟩ | ⟨_, _, hu⟩
      · rw [hu]
        rfl
      · rw [hu]
        exact (Schrittform.faedenNach_nurFaden ⟨.verbinde, o, tr⟩ c s).wirkungen
  | wechsle =>
      rcases step with ⟨_, _, hu⟩ | ⟨_, _, hu⟩
      · rw [hu]
        rfl
      · rw [hu]
        exact (Schrittform.faedenNach_nurFaden ⟨.wechsle, o, tr⟩ c s).wirkungen

private theorem fuehrtAus_buchung {L Ort Wert Raum Lok Grund Bedingung : Type} [DecidableEq L]
    {t : Nat} {c : Kontext} {s u : Maschine.Zustand L Ort Wert Raum Lok Grund}
    {p : SchrittPlan L Ort Wert Bedingung} {sperren : List (Speicher.Etikett Ort Wert)}
    {ereignisse : List Ereignis} {v : Maschine.Zustand L Ort Wert Raum Lok Grund}
    (e : Einrichtung L Ort Wert Raum Lok Grund Bedingung)
    (action : FuehrtAus e t c s u p.aktion sperren ereignisse v) :
    v.buchung.wirkungen = u.buchung.wirkungen := by
  generalize hA : p.aktion = a at action
  cases action <;> rfl

private theorem fuehrtAus_aussen {L Ort Wert Raum Lok Grund Bedingung : Type} [DecidableEq L]
    {t : Nat} {c : Kontext} {s u : Maschine.Zustand L Ort Wert Raum Lok Grund}
    {p : SchrittPlan L Ort Wert Bedingung} {sperren : List (Speicher.Etikett Ort Wert)}
    {ereignisse : List Ereignis} {v : Maschine.Zustand L Ort Wert Raum Lok Grund}
    (e : Einrichtung L Ort Wert Raum Lok Grund Bedingung)
    (action : FuehrtAus e t c s u p.aktion sperren ereignisse v) :
    ereignisse = [] ∨ ∃ q : Frage, ereignisse = [.frage (s.stelleFrage t c q)] ∧ p.aktion = .frage q := by
  generalize hA : p.aktion = a at action
  cases action with
  | frage q => exact Or.inr ⟨q, rfl, by simpa using hA⟩
  | _ => exact Or.inl rfl

/-- The outside record and the new effects of one class step. The record is empty, or one question with
    its device authority; the ledger gains nothing. -/
private theorem klassen_spur {ι : Type} (E : Klasseneinheit ι) (f : ι) (F : Schrittform)
    (emb : F.Eingebettet E f) (t : Nat) (c : Kontext) (vor zwischen nach : Zustand)
    (plan : Plan) (spur : SchrittSpur Zelle Int)
    (step : (E.system.regel f).impl c vor () [plan] zwischen)
    (aus : FuehrtSchrittAus E.einrichtung t c vor zwischen plan spur nach) :
    (spur.aussen = [] ∨ ∃ q : Frage, spur.aussen = [.frage (vor.stelleFrage t c q)] ∧
      RegisterErlaubt vor c.nummer q) ∧
    nach.buchung.wirkungen = vor.buchung.wirkungen := by
  rw [emb.regel] at step
  obtain ⟨_, _, _, v, action, _, nach_eq⟩ := aus
  have wirkungen : nach.buchung.wirkungen = vor.buchung.wirkungen := by
    rw [nach_eq]
    change v.buchung.wirkungen = vor.buchung.wirkungen
    rw [fuehrtAus_buchung E.einrichtung action, wirkungen_gleich F c vor zwischen plan step]
  constructor
  · rcases fuehrtAus_aussen E.einrichtung action with leer | ⟨q, geformt, hA⟩
    · exact Or.inl leer
    · exact Or.inr ⟨q, geformt, (frage_aktion_befugt step hA).2⟩
  · exact wirkungen

/-- **The register leg of every class** (`KlassenRegisterbeinAussage`). The only outside event a class
    step records is a question, and its guard carries the device authority. No new effect is emitted. -/
theorem klassenRegisterbein (k : Wirkungsklasse) : KlassenRegisterbeinAussage k := by
  intro ι E f F _ emb _ t c _ vor zwischen nach plan spur _ regel aus
  rcases klassen_spur E.maschine f F emb t c vor zwischen nach plan spur regel aus with ⟨ spurform, wirkungen ⟩
  constructor
  · intro e mem
    rcases spurform with leer | ⟨q, geformt, erlaubt⟩
    · rw [leer] at mem
      exact (List.not_mem_nil mem).elim
    · rw [geformt] at mem
      obtain rfl := List.mem_singleton.mp mem
      constructor
      · intro qe gleich
        cases gleich
        simpa only [Zustand.stelleFrage] using erlaubt
      · intro a commit
        cases commit.1
  · refine ⟨[], Or.inr ⟨?_, ?_⟩, ?_⟩
    · rcases spurform with leer | ⟨q, geformt, _⟩
      · rw [Absturz, leer]
        exact List.not_mem_nil
      · rw [Absturz, geformt]
        intro crash
        cases List.mem_singleton.mp crash
    · simpa only [List.append_nil] using wirkungen
    · intro e mem
      exact (List.not_mem_nil mem).elim

/-- **The commit leg of every class** (`KlassenCommitbeinAussage`). A commit needs an answer event in the
    outside record; the record of a class step is empty or holds one question. The ledger gains nothing. -/
theorem klassenCommitbein (k : Wirkungsklasse) : KlassenCommitbeinAussage k := by
  intro ι E f F _ emb _ _ t c _ vor zwischen nach plan spur _ regel aus
  rcases klassen_spur E.maschine f F emb t c vor zwischen nach plan spur regel aus with ⟨ spurform, wirkungen ⟩
  constructor
  · intro e mem a commit
    rcases spurform with leer | ⟨q, geformt, _⟩
    · rw [leer] at mem
      exact (List.not_mem_nil mem).elim
    · rw [geformt] at mem
      obtain rfl := List.mem_singleton.mp mem
      cases commit.1
  · refine ⟨[], Or.inr ⟨?_, ?_⟩, ?_⟩
    · rcases spurform with leer | ⟨q, geformt, _⟩
      · rw [Absturz, leer]
        exact List.not_mem_nil
      · rw [Absturz, geformt]
        intro crash
        cases List.mem_singleton.mp crash
    · simpa only [List.append_nil] using wirkungen
    · intro e mem
      exact (List.not_mem_nil mem).elim

end Gabbro.Core.Ast.Semantik
