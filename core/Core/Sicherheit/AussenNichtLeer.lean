module

public import Core.Sicherheit.Aussen
public import Core.Sicherheit.Laufkonstruktion

@[expose] public section

namespace Gabbro.Core.Sicherheit

open Maschine Katalog Laufkonstruktion

/-- A loader leaves one pending question. Its real success at tick zero does not authorise
    the unmediated commit at tick one, by which time the endpoint's object is dead. -/
theorem toctoufrei_nichtLeer :
    ∃ (E : Modell) (H : Umgebung) (ρ : Lauf E), Maschine.Laeufe E.maschine H ρ ∧ ¬ ToctouFrei E H ρ := by
  let griff : Handle := ⟨0, ⟨⟨.hosted, 0⟩, 0⟩, [.read, .write]⟩
  let q : Frage := ⟨.hosted, griff, [], .read⟩
  let commit : Frage := { q with operation := .write [0] }
  let a : Antwort := ⟨griff.origin, [griff.origin], .ok (.data [])⟩
  let lebend : AussenSicht :=
    ⟨fun _ => ⟨0, true, true, [], fun _ => 0⟩,
      fun e i => if e = .hosted ∧ i = 0 then some griff else none, fun _ _ => none⟩
  have antwort : atomar .x86_64 lebend q = .antwort a := rfl
  let sicht : Sicht := fun t _ => if t = 0 then lebend else .leer
  let c := Kontext.faden 1
  let frage : FrageEreignis := ⟨0, c.nummer, 0, q⟩
  let arrival : AntwortEreignis := ⟨0, c.nummer, 0, q, a⟩
  let effect : AussenCommit := ⟨c, commit, Aussen.einzel a.origin⟩
  let z : Laufkonstruktion.Zustand :=
    { start.frage frage with buchung := { Buchung.leer with aussengriff := fun _ _ _ => True } }
  let label := aussenEtikett einrichtung (.antwort arrival)
  obtain ⟨g, append⟩ := Speicher.Zustand.schritt_ohne_lesen
    Speicher.Zustand.leer_konsistent Speicher.Zustand.leer_vollstaendig (.aussen : SpeicherAkteur Unit)
    label id
  let middle : Laufkonstruktion.Zustand := { z.antwort arrival with graph := g }
  let last : Laufkonstruktion.Zustand :=
    { middle with buchung := { middle.buchung with wirkungen := [.aussen effect] } }
  let spur₀ : Spur := ⟨[(.aussen, label)], [.antwort arrival]⟩
  let spur₁ : Spur := ⟨[], []⟩
  let form : Formular := fun d s plans u => d = c ∧ s = middle ∧ plans = [ruhigerPlan] ∧ u = last
  let E := einheit z form []
  have selected : katalog.enthaelt (.endpoint q.endpoint) := by
    change katalog.enthaelt (.endpoint .hosted)
    apply List.mem_append_right
    apply List.mem_cons_of_mem
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_map_of_mem
    exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  have offered : z.AntwortAngeboten katalog (hardware sicht) 0 arrival := by
    refine ⟨rfl, ⟨decide_eq_true selected, ?_⟩, selected,
      ⟨frage, List.Mem.head _, Nat.le_refl _, Nat.le_refl _, rfl, rfl, rfl⟩,
      fun _ absent => (List.not_mem_nil absent).elim⟩
    change atomar .x86_64 (sicht 0 z.verlauf) q = .antwort a
    simpa only [sicht, ↓reduceIte] using antwort
  have first : Lauffolge E.maschine (hardware sicht) 0 (some z) (.antwort arrival, spur₀) (some middle) :=
    .schritt (.antwort rfl ⟨offered, rfl, .cons (.ohne (Or.inl rfl)) append (.nil _), rfl⟩)
  have execute : FuehrtSchrittAus einrichtung 1 c middle last ruhigerPlan spur₁ last :=
    ⟨rahmen middle last.buchung, fun _ absent => (List.not_mem_nil absent).elim, [], last,
      .intern, .nil _, rfl⟩
  have second : Lauffolge E.maschine (hardware sicht) 1 (some middle) (.kontext c (), spur₁) (some last) :=
    ausfuehren (c := c) (plan := ruhigerPlan) ⟨1, rfl, rfl, rfl⟩
      (show form c middle [ruhigerPlan] last from ⟨rfl, rfl, rfl, rfl⟩) execute
  let tail := Maschine.fairerZeitAb E.maschine (hardware sicht) (some last) 2
  have h1' : Maschine.Lauffolge E.maschine (hardware sicht) 1 (some middle) (.kontext c (), spur₁)
      (tail.zustand 0) := second
  have h0' : Maschine.Lauffolge E.maschine (hardware sicht) 0 (some z) (.antwort arrival, spur₀)
      (some middle) := first
  let zeit := voran2 h1' (some z) (.antwort arrival, spur₀) h0'
  have boot : zeit.zustand 0 = some z := rfl
  have between : zeit.zustand 1 = some middle := rfl
  have lab : zeit.spur 1 = some (.kontext c (), spur₁) := rfl
  have after : zeit.zustand 2 = some last := rfl
  have fair : ∀ a, Maschine.SchedulerFair E.maschine ⟨a, hardware sicht, zeit⟩ := fun a =>
    voran2_fair h1' h0' (Maschine.fairerZeitAb_fair E.maschine (hardware sicht) (some last) 2 a)
  obtain ⟨bootStart, run⟩ := laeuft zeit boot fair
  let ρ : Lauf E := ⟨bootStart, hardware sicht, zeit⟩
  refine ⟨E, _, ρ, run, fun safe => ?_⟩
  obtain ⟨neu, journal, effects⟩ := (safe.2 1 middle spur₁ last ⟨between, ⟨_, lab⟩, after⟩).2
  have neuIst : [.aussen effect] = neu := by
    rcases journal with ⟨impossible, _⟩ | ⟨_, suffix⟩
    · exact (List.not_mem_nil impossible).elim
    · exact suffix
  have valid := (effects effect (neuIst ▸ List.Mem.head [])).2.2.2.1
  change Aussen.GueltigBeiCommit .x86_64 AussenSicht.leer commit at valid
  cases valid with
  | frisch alle =>
    let key : Zugriff := ⟨commit.handle, commit.operation.required⟩
    have yes := List.all_eq_true.mp alle key List.mem_cons_self
    have no := Aussen.tot_gueltig_falsch AussenSicht.leer commit.endpoint key (fun _ => rfl)
    exact Bool.false_ne_true (no.symm.trans yes)
  | stabil alle =>
    exact Aussen.hosted_nicht_stabil _ _ rfl (alle ⟨commit.handle, commit.operation.required⟩ List.mem_cons_self)

end Gabbro.Core.Sicherheit
