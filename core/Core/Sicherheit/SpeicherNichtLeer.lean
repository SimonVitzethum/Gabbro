module

public import Core.Sicherheit.Speicher
public import Core.Sicherheit.Rennen
public import Core.Sicherheit.Laufkonstruktion

@[expose] public section

namespace Gabbro.Core.Sicherheit

open Maschine Katalog
open Laufkonstruktion (Modell Formular)
open Gabbro.Core.Speicher (Etikett Art)

namespace ZweiSchreiber

open Laufkonstruktion

def g₀ : SpeicherGraph Unit Unit := Speicher.Zustand.leer

def g₁ : SpeicherGraph Unit Unit :=
  g₀.senke (.initial ()) schreibLabel (fun _ => False) 0

def g₂ : SpeicherGraph Unit Unit :=
  g₁.senke (.kontext (.faden 0)) schreibLabel (fun _ => False) 0

def g₃ : SpeicherGraph Unit Unit :=
  g₂.senke (.kontext (.faden 1)) schreibLabel (fun _ => False) 0

theorem erweiterung₁ : g₀.Schritt (.initial ()) schreibLabel g₁ :=
  Speicher.Zustand.senke_schritt
    ⟨fun i hi _ => Nat.not_lt_zero i hi, fun _ _ _ _ h _ => h, fun h => False.elim h,
      fun h => by change Art.schreiben = Art.rmw at h; cases h⟩
    Speicher.Zustand.leer_konsistent Speicher.Zustand.leer_vollstaendig

theorem erweiterung₂ : g₁.Schritt (.kontext (.faden 0)) schreibLabel g₂ := by
  refine Speicher.Zustand.senke_schritt ⟨?_, fun _ _ _ _ h _ => h, fun h => False.elim h,
    fun h => by change Art.schreiben = Art.rmw at h; cases h⟩
    erweiterung₁.konsistent erweiterung₁.vollstaendig
  intro i hi eq
  have lt : i < 1 := hi
  have zero : i = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ lt)
  subst i
  cases eq

theorem erweiterung₃ : g₂.Schritt (.kontext (.faden 1)) schreibLabel g₃ := by
  refine Speicher.Zustand.senke_schritt ⟨?_, fun _ _ _ _ h _ => h, fun h => False.elim h,
    fun h => by change Art.schreiben = Art.rmw at h; cases h⟩
    erweiterung₂.konsistent erweiterung₂.vollstaendig
  intro i hi eq
  have lt : i < 2 := hi
  have idx : i = 0 ∨ i = 1 := by omega
  rcases idx with rfl | rfl <;> cases eq

def spur₀ : Spur :=
  ⟨[(.initial (), schreibLabel), (.kontext (.faden 0), schreibLabel)], []⟩

def spur₁ : Spur := ⟨[(.kontext (.faden 1), schreibLabel)], []⟩

def buch (gen : Nat) : Buchung Unit :=
  { (Buchung.leer : Buchung Unit) with
    umfang := fun _ => [()]
    haelt := fun _ _ _ => True
    adresse := fun _ => some ⟨⟨0, gen⟩, 0⟩ }

def vor (gen : Nat) : Laufkonstruktion.Zustand := { start with buchung := buch gen }
def nach₀ (gen : Nat) : Laufkonstruktion.Zustand := { vor gen with graph := g₂ }
def nach₁ (gen : Nat) : Laufkonstruktion.Zustand := { vor gen with graph := g₃ }

def form : Formular := fun _ s plans u => plans = [schreibPlan] ∧ u = s

def E (gen : Nat) : Modell := einheit (vor gen) form []

theorem schritt₀ (gen : Nat) :
    Lauffolge (E gen).maschine (hardware leer) 0 (some (vor gen)) (.kontext (.faden 0) (), spur₀)
      (some (nach₀ gen)) := by
  have folge : Speicherfolge (vor gen).initial (.kontext (.faden 0)) (vor gen).graph [schreibLabel] spur₀.speicher g₂ :=
    .cons (.erste (fun h => by change Art.schreiben = Art.aussen at h; cases h) (fun ⟨i, lt, _⟩ => Nat.not_lt_zero i lt) erweiterung₁)
      erweiterung₂ (.nil _)
  exact ausfuehren (c := .faden 0) (plan := schreibPlan)
    ⟨0, rfl, rfl, rfl⟩ (show form _ (vor gen) [schreibPlan] (vor gen) from ⟨rfl, rfl⟩) (schreiben (vor gen) (buch gen) folge)

theorem schritt₁ (gen : Nat) :
    Lauffolge (E gen).maschine (hardware leer) 1 (some (nach₀ gen)) (.kontext (.faden 1) (), spur₁)
      (some (nach₁ gen)) := by
  have quelle : HatQuelle g₂ () := ⟨0, Nat.zero_lt_succ 1, trivial, rfl⟩
  have folge : Speicherfolge (nach₀ gen).initial (.kontext (.faden 1)) (nach₀ gen).graph
      [schreibLabel] spur₁.speicher g₃ :=
    .cons (.ohne (Or.inr quelle)) erweiterung₃ (.nil _)
  exact ausfuehren (c := .faden 1) (plan := schreibPlan)
    ⟨1, rfl, rfl, rfl⟩ (show form _ (nach₀ gen) [schreibPlan] (nach₀ gen) from ⟨rfl, rfl⟩) (schreiben (nach₀ gen) (buch gen) folge)

theorem ungeordnet : ∀ i j : Fin g₃.ev.length, ¬ g₃.graph.hb i j := by
  have keinPo (i j : Nat) : ¬ g₃.po i j := by
    simp only [g₃, g₂, g₁, g₀, Speicher.Zustand.senke, Speicher.Zustand.anhaengen,
      Speicher.Zustand.leer, and_false, or_false, not_false_eq_true]
  have keinRf (i j : Nat) : ¬ g₃.rf i j := by
    simp only [g₃, g₂, g₁, g₀, schreibLabel, Art.liest, Speicher.Zustand.senke,
      Speicher.Zustand.anhaengen, Speicher.Zustand.leer, false_and, and_false, or_false, not_false_eq_true]
  intro i j hb
  obtain ⟨k, po | sw⟩ := Speicher.transGen_kopf hb
  · exact keinPo i k po
  · obtain ⟨_, _, _, _, x, _, rf⟩ := sw
    exact keinRf x k rf

end ZweiSchreiber

open Laufkonstruktion ZweiSchreiber
/-- A real write through an allocated object's previous generation violates memory safety. -/
theorem speichersicher_nichtLeer :
    ∃ (E : Modell) (H : Umgebung) (ρ : Lauf E), Maschine.Laeufe E.maschine H ρ ∧ ¬ Speichersicher E H ρ := by
  obtain ⟨zeit, boot, lab, after⟩ := schritt_erfuellbar (schritt₀ 0)
  obtain ⟨a, run⟩ := laeuft zeit boot
  let ρ : Lauf (E 0) := ⟨a, hardware leer, zeit⟩
  refine ⟨_, _, ρ, run, fun safe => ?_⟩
  have h := (safe.2 0 (vor 0) spur₀ (nach₀ 0) ⟨boot, ⟨_, lab⟩, after⟩).1 1 (.kontext (.faden 0))
    schreibLabel rfl (fun eq => by change Art.schreiben = Art.aussen at eq; cases eq)
  obtain ⟨a, ha, valid, _⟩ := h
  have stale : (⟨⟨0, 0⟩, 0⟩ : Adresse) = a := Option.some.inj ha
  subst a
  exact Nat.one_ne_zero valid.2

/-- Two implementation threads really append plain writes to the same location, with no hb edge. -/
theorem rennfrei_nichtLeer :
    ∃ (E : Modell) (H : Umgebung) (ρ : Lauf E), Maschine.Laeufe E.maschine H ρ ∧ ¬ Rennfrei E H ρ := by
  obtain ⟨zeit, boot, _, _, lab, after⟩ := praefix_erfuellbar (schritt₀ 1) (schritt₁ 1)
  obtain ⟨a, run⟩ := laeuft zeit boot
  let ρ : Lauf (E 1) := ⟨a, hardware leer, zeit⟩
  refine ⟨_, _, ρ, run, fun safe => ?_⟩
  let cut : Maschine.Schnitt (E 1).maschine ρ := ⟨2, Or.inr ⟨1, _, rfl, lab⟩⟩
  let i : Fin g₃.ev.length := ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 1)⟩
  let j : Fin g₃.ev.length := ⟨2, Nat.lt_succ_self 2⟩
  have conflict : Konflikt g₃ i j :=
    ⟨fun eq => by have h := congrArg Fin.val eq; change 1 = 2 at h; omega, ⟨Or.inr trivial, trivial⟩,
      ⟨Or.inr trivial, trivial⟩, rfl, Or.inl trivial, Or.inl rfl⟩
  exact (safe.1 cut (nach₁ 1) after i j conflict).elim (ungeordnet _ _) (ungeordnet _ _)

end Gabbro.Core.Sicherheit
