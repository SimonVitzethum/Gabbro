module

public import Core.Beobachtung.Fluss.Beschriftung.AufrufSchleife
public import Core.Beobachtung.Fluss.Beschriftung.AufgabenBeweise

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Beobachtung Katalog

/-- The view after defining a function: the program counter jumps and one static
    entry is pushed onto the always-public function table. -/
theorem sicht_definiere (β : Beschriftung) (r : Rahmen) (live : Nat → Bool)
    (name : Identifier) (ps : List (Ty .value)) (res : Option (Ty .value))
    (glob skip : Nat) (meas : Bool) (calls : List Rufstelle)
    (effs : Option (List CarrierEffect)) :
    ((Befehl.definiere name ps res glob skip meas calls effs).auswerten r live).sicht β =
      { r.sicht β with
        pc := r.pc + skip
        temp := fun s => if oeffentlich (β.temp (r.pc + skip) s) = true then r.temp s else none
        lokale := maskiere (β.lokal (r.pc + skip)) 0 r.lokale
        funktionen :=
          ⟨name, r.pc + 1, ps, res, glob, meas, calls, effs⟩ :: r.funktionen } := rfl

theorem definiereSicht : DefiniereSichtAussage := by
  intro β pc name ps res glob skip meas calls effs hT hL r₁ r₂ live hpc h
  subst hpc
  obtain ⟨pcEq, tempPub, lokEq⟩ := sicht_oeffentliche_teile h
  have hTe : (fun s => if oeffentlich (β.temp (r₁.pc + skip) s) = true then r₁.temp s else none) =
      (fun s => if oeffentlich (β.temp (r₁.pc + skip) s) = true then r₂.temp s else none) := by
    funext s
    by_cases hp : oeffentlich (β.temp (r₁.pc + skip) s) = true
    · simp only [hp, if_true]
      exact tempPub s (hT s hp)
    · simp only [if_neg hp]
  have hLe : maskiere (β.lokal (r₁.pc + skip)) 0 r₁.lokale =
      maskiere (β.lokal (r₁.pc + skip)) 0 r₂.lokale :=
    maskiere_gleich_mono hL 0 _ _ lokEq
  have hF : (⟨name, r₁.pc + 1, ps, res, glob, meas, calls, effs⟩ : Funktion) ::
        r₁.funktionen =
      (⟨name, r₂.pc + 1, ps, res, glob, meas, calls, effs⟩ : Funktion) ::
        r₂.funktionen := by
    have hFu : r₁.funktionen = r₂.funktionen := by
      simpa only [Rahmen.sicht] using
        congrArg (fun r : Rahmen => (r.sicht β).funktionen) h
    rw [pcEq, hFu]
  rw [sicht_definiere, sicht_definiere, h, pcEq, hTe, hLe, hF]

theorem zurueckSprungSicht : ZurueckSprungSichtAussage := by
  intro β pc abstand hT hL r₁ r₂ live hpc h
  subst hpc
  have pcEq : r₂.pc = r₁.pc := (sicht_pc h).symm
  simp only [Befehl.auswerten, pcEq]
  exact sicht_pcWechsel hT hL h

/-- The view after setting a pass counter: the always-visible counter table gains
    one entry derived from the converted value. -/
theorem sicht_setzePasszahl_some (β : Beschriftung) (r : Rahmen) (stelle : Nat)
    (value : Ganzzahl) :
    ({ r with pc := r.pc + 1,
      zaehler := Function.update r.zaehler (r.pc + stelle)
        (some value.zahl.wert.toNat) }).sicht β =
      { r.sicht β with
        pc := r.pc + 1
        temp := fun s => if oeffentlich (β.temp (r.pc + 1) s) = true then r.temp s else none
        lokale := maskiere (β.lokal (r.pc + 1)) 0 r.lokale } := rfl

theorem setzePasszahlSicht : SetzePasszahlSichtAussage := by
  intro β pc quelle stelle hq hT hL r₁ r₂ live hpc h
  subst hpc
  obtain ⟨pcEq, tempPub, lokEq⟩ := sicht_oeffentliche_teile h
  have hZ : r₁.zahl quelle = r₂.zahl quelle := by
    simp only [Rahmen.zahl, tempPub quelle hq]
  have hTe : (fun s => if oeffentlich (β.temp (r₁.pc + 1) s) = true then r₁.temp s else none) =
      (fun s => if oeffentlich (β.temp (r₁.pc + 1) s) = true then r₂.temp s else none) := by
    funext s
    by_cases hp : oeffentlich (β.temp (r₁.pc + 1) s) = true
    · simp only [hp, if_true]
      exact tempPub s (hT s hp)
    · simp only [if_neg hp]
  have hLe : maskiere (β.lokal (r₁.pc + 1)) 0 r₁.lokale =
      maskiere (β.lokal (r₁.pc + 1)) 0 r₂.lokale :=
    maskiere_gleich_mono hL 0 _ _ lokEq
  cases hZc : r₁.zahl quelle with
  | none =>
    have hZ₂ : r₂.zahl quelle = none := by rw [← hZ, hZc]
    simp only [Befehl.auswerten, hZc, hZ₂, sicht_halt]
    rw [h]
  | some value =>
    have hZ₂ : r₂.zahl quelle = some value := by rw [← hZ, hZc]
    have hZaehler : r₁.zaehler = r₂.zaehler := by
      simpa only [Rahmen.sicht] using
        congrArg (fun r : Rahmen => (r.sicht β).zaehler) h
    simp only [Befehl.auswerten, hZc, hZ₂, sicht_setzePasszahl_some, h, pcEq, hTe,
      hLe, hZaehler]

end Gabbro.Core.Ast.Semantik
