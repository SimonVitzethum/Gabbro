/-
  File:      core/Core/Ast/Semantik/Runtime/Klasse/Beweise/Faden.lean
  Subject:   THE STEP OF A LIFECYCLE CLASS, IN FACTS (MK-07). A form of the classes `starte`, `beende`, `verbinde`
             and `wechsle` has a step that either REFUSES (the operands name nothing: the private plan, the acting
             frame halts) or runs the planned step of its class: a plan with no memory event, no footprint and a
             protocol action that records no lock and no outside event (`Aktion.Still`), and a state that differs from
             the pre-state only in the frames, the status of the acting thread and the holdings of the ledger
             (`Zustand.NurFaden`). The two facts are all the class duties need: the safety legs, the bounds, the
             locality and the flow of the lifecycle classes follow from them and from `FuehrtAus.still_erhaelt`.
-/
module

public import Core.Ast.Semantik.Runtime.Klasse.Pflichten
public import Core.Ast.Semantik.Runtime.Faden.Erhalt

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog

/-- **A form of a lifecycle class.** -/
def Schrittform.Lebenszyklus (F : Schrittform) : Prop :=
  F.klasse = .starte ∨ F.klasse = .beende ∨ F.klasse = .verbinde ∨ F.klasse = .wechsle

/-- **The states agree in every field a lifecycle step leaves alone**: it changes the frames, the status of the
    acting thread and the holdings of the ledger, and nothing else. -/
structure Zustand.NurFaden (a b : Zustand) : Prop where
  rechte : a.rechte = b.rechte
  graph : a.graph = b.graph
  fragen : a.fragen = b.fragen
  antworten : a.antworten = b.antworten
  epoche : a.epoche = b.epoche
  sperren : a.sperren = b.sperren
  kerne : a.kerne = b.kerne
  verbraucht : a.verbraucht = b.verbraucht
  verlauf : a.verlauf = b.verlauf
  geliefert : a.geliefert = b.geliefert
  leihen : a.leihen = b.leihen
  initial : a.initial = b.initial
  persistenz : a.persistenz = b.persistenz
  verworfen : a.verworfen = b.verworfen
  naechsterFaden : a.naechsterFaden = b.naechsterFaden
  erzeuger : a.erzeuger = b.erzeuger
  umfang : a.buchung.umfang = b.buchung.umfang
  adresse : a.buchung.adresse = b.buchung.adresse
  schreibt : a.buchung.schreibt = b.buchung.schreibt
  aussengriff : a.buchung.aussengriff = b.buchung.aussengriff
  geraet : a.buchung.geraet = b.buchung.geraet
  wirkungen : a.buchung.wirkungen = b.buchung.wirkungen

theorem Zustand.NurFaden.refl (s : Zustand) : s.NurFaden s := by
  constructor <;> rfl

/-- A lifecycle step keeps the framed fields the protocol keeps: it is a `Zustandsrahmen`. -/
theorem Zustand.NurFaden.rahmen {a b : Zustand} (h : a.NurFaden b) : Zustandsrahmen b a :=
  ⟨h.graph, h.kerne, h.sperren, h.fragen, h.antworten, h.verbraucht, h.verlauf, h.geliefert, h.initial,
    h.persistenz, h.epoche, h.verworfen, h.naechsterFaden, h.erzeuger⟩

/-- The refusal of an access changes only the acting frame. -/
theorem Schrittform.verweigert_nurFaden (F : Schrittform) (c : Kontext) (s : Zustand) :
    (F.verweigert c s).NurFaden s := by
  constructor <;> rfl

/-- **A lifecycle step changes only frames, status and holdings.** -/
theorem Schrittform.faedenNach_nurFaden (F : Schrittform) (c : Kontext) (s : Zustand) :
    (F.faedenNach c s).NurFaden s := by
  unfold Schrittform.faedenNach
  try dsimp only
  split <;> (try split) <;> constructor <;> rfl

/-- **The step of a lifecycle form, in facts**: the state differs from the pre-state only in frames, status and
    holdings; the plan records no memory event and has no footprint; its action is still (internal after a refusal,
    the lifecycle action of the class otherwise). -/
theorem Schrittform.lebenszyklus_ideal {F : Schrittform} (hk : F.Lebenszyklus) {c : Kontext} {s : Zustand}
    {w : PUnit.{1}} {p : Plan} {u : Zustand} (step : F.ideal c s w [p] u) :
    u.NurFaden s ∧ p.aktion.Still ∧ p.lesen = [] ∧ p.fuss = [] := by
  obtain ⟨k, o, t⟩ := F
  rcases hk with hk | hk | hk | hk <;> change k = _ at hk <;> subst hk <;>
    rcases step with ⟨_, same, hu⟩ | ⟨_, same, hu⟩
  all_goals first
    | (have hp : p = Semantik.plan := (List.cons.inj same).1
       subst hp
       subst hu
       exact ⟨Schrittform.verweigert_nurFaden _ c s, trivial, rfl, rfl⟩)
    | (have hp := (List.cons.inj same).1
       subst hp
       subst hu
       exact ⟨Schrittform.faedenNach_nurFaden _ c s, trivial, rfl, rfl⟩)

/-- **The state of a lifecycle step**: the refusal or the lifecycle state of the class. -/
theorem Schrittform.lebenszyklus_zustand {F : Schrittform} (hk : F.Lebenszyklus) {c : Kontext} {s : Zustand}
    {w : PUnit.{1}} {p : Plan} {u : Zustand} (step : F.ideal c s w [p] u) :
    u = F.verweigert c s ∨ u = F.faedenNach c s := by
  obtain ⟨k, o, t⟩ := F
  rcases hk with hk | hk | hk | hk <;> change k = _ at hk <;> subst hk <;>
    rcases step with ⟨_, _, hu⟩ | ⟨_, _, hu⟩
  all_goals first | exact Or.inl hu | exact Or.inr hu

/-- Replacing the frame of one context keeps the stack bound of every context, if the new frame keeps it. -/
private theorem update_stapel {s : Zustand} {c d : Kontext} {X : Rahmen} {n : Nat}
    (hX : d = c → X.fortsetzungen.length ≤ n) (vor : (s.lokal d).fortsetzungen.length ≤ n) :
    (Function.update s.lokal c X d).fortsetzungen.length ≤ n := by
  by_cases h : d = c
  · rw [h, Function.update_self]
    exact hX h
  · rw [Function.update_of_ne h]
    exact vor

/-- **A refused step keeps the stack bound**: the acting frame halts and keeps its continuation stack. -/
theorem Schrittform.verweigert_stapel {ι : Type} (E : Klasseneinheit ι) (F : Schrittform)
    (tiefe : ∀ r : Rahmen, E.schranken.stapelTiefe r = r.fortsetzungen.length) (c : Kontext) (s : Zustand)
    (d : Kontext) (n : Nat) (vorTief : E.schranken.stapelTiefe (s.lokal d) ≤ n) :
    E.schranken.stapelTiefe ((F.verweigert c s).lokal d) ≤ n := by
  rw [tiefe] at vorTief ⊢
  exact update_stapel (fun h => by rw [← h]; exact vorTief) vorTief

/-- **The stack leg of a lifecycle step.** The acting frame is the class transfer, which respects the declared
    bound; the new thread starts with an empty continuation stack; every other frame is unchanged. -/
theorem Schrittform.faedenNach_stapel {ι : Type} (E : Klasseneinheit ι) (F : Schrittform)
    (stapel : F.Stapelschranke E)
    (tiefe : ∀ r : Rahmen, E.schranken.stapelTiefe r = r.fortsetzungen.length) (c : Kontext) (s : Zustand)
    (d : Kontext) (n : Nat) (bound : E.schranken.stapel = some n)
    (vorTief : E.schranken.stapelTiefe (s.lokal d) ≤ n) :
    E.schranken.stapelTiefe ((F.faedenNach c s).lokal d) ≤ n := by
  rw [tiefe] at vorTief ⊢
  have acting : d = c → ∀ v : Int, (F.uebertrag (s.lokal c) s.regionLive v).fortsetzungen.length ≤ n := by
    intro hdc v
    rw [← hdc]
    exact stapel (s.lokal d) s.regionLive v n bound vorTief
  unfold Schrittform.faedenNach
  try dsimp only
  split <;> (try split) <;> first
    | exact vorTief
    | exact update_stapel (fun h => acting h _) vorTief
    | exact update_stapel (fun h => by rw [← h]; exact vorTief) vorTief
    | (by_cases h1 : d = Kontext.faden s.naechsterFaden
       · rw [h1]
         change (Function.update (Function.update s.lokal c _) (Kontext.faden s.naechsterFaden) _
           (Kontext.faden s.naechsterFaden)).fortsetzungen.length ≤ n
         rw [Function.update_self]
         exact Nat.zero_le _
       · change (Function.update (Function.update s.lokal c _) (Kontext.faden s.naechsterFaden) _ d).fortsetzungen.length ≤ n
         rw [Function.update_of_ne h1]
         exact update_stapel (fun h => acting h _) vorTief)

end Gabbro.Core.Ast.Semantik
