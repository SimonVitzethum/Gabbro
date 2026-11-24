module

public import Core.Beobachtung.Fluss.Beschriftung.Sprung

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Beobachtung Katalog

/-- A secret compartment. -/
def geheim : Etikett := {0}

theorem geheim_verborgen : oeffentlich geheim = false := by
  apply decide_eq_false
  intro eq
  have mem : 0 ∈ geheim := Finset.mem_singleton_self _
  rw [eq] at mem
  exact Finset.notMem_empty _ mem

/-- A start whose inputs are all empty; it only supplies a machine state to place frames in. -/
def leererStart : AussenStart :=
  ⟨0, fun _ => some 0, [], fun _ => none,
    ⟨fun _ => ⟨0, false, false, [], fun _ => 0⟩, fun _ _ => none, fun _ _ => none⟩⟩

/-- A frame whose only local, a boolean, is the secret `x`. -/
def rahmenGeheim (x : Bool) : Rahmen :=
  { Rahmen.start [] with lokale := [some ⟨.bool, x⟩] }

/-- The unit's state with the entry context holding `rahmenGeheim x`. -/
def zustandGeheim (E : Einheit) (x : Bool) : Zustand :=
  let v := (I.start E leererStart).2
  { v with lokal := Function.update v.lokal eintritt (rahmenGeheim x) }

/-- Local 0 is secret at every position, every temporary is public. -/
def leckBeschriftung : Beschriftung :=
  { lokal := fun _ i => if i = 0 then geheim else ∅ }

/-- The program that copies the secret local into a public temporary. -/
def leckFragment : Fragment := Fragment.einzel (.lesen 0 0)

theorem sicht_geheim (β : Beschriftung) (h : oeffentlich (β.lokal 0 0) = false) (x y : Bool) :
    (rahmenGeheim x).sicht β = (rahmenGeheim y).sicht β := by
  simp only [Rahmen.sicht, rahmenGeheim, Rahmen.start, maskiere, h, Bool.false_eq_true, if_false]
  rfl

/-- The labelled unit of the leaking program. -/
def leckEinheit (platform : Plattform) : Einheit :=
  leckFragment.beschriftet platform leckBeschriftung

theorem leck_oeffentlich : oeffentlich (leckBeschriftung.lokal 0 0) = false := by
  simp only [leckBeschriftung, if_true]
  exact geheim_verborgen

theorem kopf_geheim (platform : Plattform) (x : Bool) :
    (leckEinheit platform).system.kopf (zustandGeheim (leckEinheit platform) x) eintritt =
      some (.lesen 0 0) :=
  rfl

/-- The two states differ only in the secret local. -/
theorem quellzustand_geheim (platform : Plattform) (x y : Bool) :
    QuellzustandGleich (leckEinheit platform) (zustandGeheim (leckEinheit platform) x)
      (zustandGeheim (leckEinheit platform) y) := by
  refine ⟨?_, fun _ => rfl, fun _ => rfl, rfl, rfl, fun _ => rfl⟩
  intro c p pub
  change ((zustandGeheim (leckEinheit platform) x).lokal c).sicht leckBeschriftung =
    ((zustandGeheim (leckEinheit platform) y).lokal c).sicht leckBeschriftung
  by_cases hc : c = eintritt
  · subst hc
    simp only [zustandGeheim, Function.update_self]
    exact sicht_geheim leckBeschriftung leck_oeffentlich x y
  · simp only [zustandGeheim, Function.update_of_ne hc]

/-- **A flow from a secret local to a public temporary is refused by `Lokal`.** The two
    states agree on everything public and differ in the secret; one step of the copy makes
    the public views differ. -/
theorem leck_abgelehnt (platform : Plattform) : ¬ FlussLokal (leckEinheit platform) := by
  intro h
  have regel := (h.2 (.lesen 0 0)).2
  have oeff : oeffentlich ((leckEinheit platform).fluss.kontrolle (.lesen 0 0)) = true :=
    oeffentlich_leer
  have schritt (x : Bool) : FormSchritt (leckEinheit platform) (.lesen 0 0) eintritt
      (zustandGeheim (leckEinheit platform) x) () plan
      ((Befehl.lesen 0 0).nach eintritt (zustandGeheim (leckEinheit platform) x)) :=
    ⟨kopf_geheim platform x, rfl, rfl⟩
  have res := regel oeff eintritt _ () plan _ _ () plan _ (quellzustand_geheim platform true false)
    (schritt true) (schritt false)
  have gleich : (((Befehl.lesen 0 0).nach eintritt
        (zustandGeheim (leckEinheit platform) true)).lokal eintritt).sicht leckBeschriftung =
      (((Befehl.lesen 0 0).nach eintritt
        (zustandGeheim (leckEinheit platform) false)).lokal eintritt).sicht leckBeschriftung :=
    res.1.1 eintritt ⟨0, Nat.zero_lt_succ _⟩ rfl
  have temp := congrFun (congrArg Rahmen.temp gleich) 0
  simp only [Befehl.nach, Befehl.auswerten, zustandGeheim, Function.update_self, Rahmen.schreibe,
    Rahmen.sicht, rahmenGeheim, Rahmen.start, leckBeschriftung, oeffentlich_leer, if_true] at temp
  simp at temp
  cases temp

end Gabbro.Core.Ast.Semantik
