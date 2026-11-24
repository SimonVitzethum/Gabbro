module

public import Core.Sicherheit.Invarianten
public import Core.Sicherheit.Laufkonstruktion

@[expose] public section

namespace Gabbro.Core.Sicherheit

open Maschine Katalog Laufkonstruktion

/-- A loaded writer can release a lock with its declared invariant false. -/
theorem invarianten_nichtLeer :
    ∃ (E : Modell) (H : Umgebung) (ρ : Lauf E), Maschine.Laeufe E.maschine H ρ ∧ ¬ InvariantenErhalten E H ρ := by
  let c := Kontext.faden 0
  let z : Laufkonstruktion.Zustand :=
    { start with
      sperren := fun _ => ⟨some c, []⟩
      buchung := { Buchung.leer with schreibt := fun d _ => d = c } }
  let d : Invariante Unit Laufkonstruktion.Zustand := ⟨some (), fun _ => False⟩
  let plan : Plan := { ruhigerPlan with aktion := .sperre () .geben }
  let form : Formular := fun _ s ps u => ps = [plan] ∧ u = s
  let E := einheit z form [d]
  obtain ⟨r, es, g, append⟩ := speicherzug_existiert z.initial (.kontext c)
    Speicher.Zustand.leer_konsistent Speicher.Zustand.leer_vollstaendig .schreiben () .ra ()
  cases r
  let spur : Spur := ⟨es, []⟩
  let freigegeben : Laufkonstruktion.Zustand := { z with sperren := Function.update z.sperren () .frei }
  let next : Laufkonstruktion.Zustand := { freigegeben with graph := g }
  have execute : FuehrtSchrittAus einrichtung 0 c z z plan spur next := by
    refine ⟨rahmen z z.buchung, fun _ absent => (List.not_mem_nil absent).elim, [⟨.schreiben, (), .ra, (), ()⟩],
      freigegeben, ?_, append, rfl⟩
    exact FuehrtAus.sperre (e := einrichtung) (t := 0) (c := c) (s := z) (u := z) (l := ())
      (.geben (.besitzer c [])) (fun _ => trivial)
  have first : Lauffolge E.maschine (hardware leer) 0 (some z) (.kontext c (), spur) (some next) :=
    ausfuehren (c := c) (plan := plan) ⟨0, rfl, rfl, rfl⟩
      (show form c z [plan] z from ⟨rfl, rfl⟩) execute
  obtain ⟨zeit, boot, lab, after⟩ := schritt_erfuellbar first
  obtain ⟨a, run⟩ := laeuft zeit boot
  let ρ : Lauf E := ⟨a, hardware leer, zeit⟩
  refine ⟨E, _, ρ, run, fun safe => ?_⟩
  have nonCrash : ¬ Absturz spur := List.not_mem_nil
  have wechselt : (z.sperren ()).Wechsel (next.sperren ()) := by
    change some c ≠ (Function.update z.sperren () SperrZustand.frei ()).besitzer
    rw [Function.update_self]
    exact fun eq => nomatch eq
  exact (safe.2 0 z spur next ⟨boot, ⟨_, lab⟩, after⟩ nonCrash () wechselt).2 d (List.Mem.head _) rfl

end Gabbro.Core.Sicherheit
