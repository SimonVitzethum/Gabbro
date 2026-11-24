module

public import Core.Beobachtung.Fluss.Beschriftung.AufrufSchleife
public import Core.Beobachtung.Fluss.Beschriftung.Aufgaben
public import Core.Beobachtung.Fluss.Beschriftung.AufgabenBeweise
public import Core.Beobachtung.Fluss.Beschriftung.AufrufSchleifeBeweise

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Beobachtung Katalog

/-- A halt changes only the stop reason, so equal views before it stay equal. -/
theorem sicht_halt_gleich {β : Beschriftung} {r₁ r₂ : Rahmen} (grund : Abschluss)
    (h : r₁.sicht β = r₂.sicht β) :
    (r₁.halt grund).sicht β = (r₂.halt grund).sicht β := by
  rw [sicht_halt, sicht_halt, h]

/-- Masking with every label public is the identity. -/
theorem maskiere_allesOeffentlich {l : Nat → Etikett}
    (h : ∀ i, oeffentlich (l i) = true) : ∀ (i : Nat) (xs : List (Option Dynamisch)),
      maskiere l i xs = xs
  | _, [] => rfl
  | i, _ :: xs => by
      simp only [maskiere, h i, if_true, maskiere_allesOeffentlich (l := l) h (i + 1) xs]

/-- `rufArgumente` reads only the temporary slots, so equal temporaries give equal arguments. -/
theorem rufArgumente_gleich (r₁ r₂ : Rahmen) (slot : Nat)
    (hTemp : ∀ s, r₁.temp s = r₂.temp s) :
    ∀ (sources targets : List (Ty .value)),
      r₁.rufArgumente slot sources targets = r₂.rufArgumente slot sources targets := by
  intro sources
  induction sources with
  | nil =>
      intro targets
      cases targets <;> rfl
  | cons source sources ih =>
      intro targets
      cases targets with
      | nil => rfl
      | cons target targets =>
          unfold Rahmen.rufArgumente
          rw [← hTemp slot, ih targets]

/-- Equal views give equal masked result components. -/
theorem sicht_rueckgabe_gleich {β : Beschriftung} {r₁ r₂ : Rahmen}
    (h : r₁.sicht β = r₂.sicht β) :
    (if oeffentlich β.ergebnis = true then r₁.rueckgabe else none) =
      (if oeffentlich β.ergebnis = true then r₂.rueckgabe else none) := by
  exact congrArg (fun r : Rahmen => (r.sicht β).rueckgabe) h

theorem rueckVoidSicht : RueckVoidSichtAussage := by
  intro β pc hT hL r₁ r₂ live hpc h
  subst hpc
  obtain ⟨pcEq, tempPub, lokEq⟩ := sicht_oeffentliche_teile h
  have hFort : r₁.fortsetzungen = r₂.fortsetzungen := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).fortsetzungen) h
  change (r₁.rueckkehr none).sicht β = (r₂.rueckkehr none).sicht β
  unfold Rahmen.rueckkehr
  rw [← hFort]
  cases hstack : r₁.fortsetzungen with
  | nil =>
      simp only [hstack]
      rw [sicht_rueckkehr_ohne, sicht_rueckkehr_ohne]
      have hTe :
          (fun s => if oeffentlich (β.temp (r₁.pc + 1) s) = true then r₁.temp s else none) =
          (fun s => if oeffentlich (β.temp (r₁.pc + 1) s) = true then r₂.temp s else none) := by
        funext s
        by_cases hp : oeffentlich (β.temp (r₁.pc + 1) s) = true
        · simp only [hp, if_true]
          exact tempPub s (hT s hp)
        · simp only [if_neg hp]
      have hLe :
          maskiere (β.lokal (r₁.pc + 1)) 0 r₁.lokale =
            maskiere (β.lokal (r₁.pc + 1)) 0 r₂.lokale :=
        maskiere_gleich_mono hL 0 _ _ lokEq
      rw [h, pcEq, hTe, hLe]
  | cons k stack =>
      simp only [hstack]
      rw [sicht_rueckkehr_mit, sicht_rueckkehr_mit]
      rw [h]

theorem zurueckSicht : ZurueckSichtAussage := by
  intro β pc quelle zieltyp hq hT hL r₁ r₂ live hpc h
  subst hpc
  obtain ⟨pcEq, tempPub, lokEq⟩ := sicht_oeffentliche_teile h
  have hFort : r₁.fortsetzungen = r₂.fortsetzungen := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).fortsetzungen) h
  have hResult : (r₁.temp quelle).bind (wertIn zieltyp) =
      (r₂.temp quelle).bind (wertIn zieltyp) := by
    rw [tempPub quelle hq]
  change (r₁.rueckkehr ((r₁.temp quelle).bind (wertIn zieltyp))).sicht β =
    (r₂.rueckkehr ((r₂.temp quelle).bind (wertIn zieltyp))).sicht β
  unfold Rahmen.rueckkehr
  rw [← hFort, ← hResult]
  cases hstack : r₁.fortsetzungen with
  | nil =>
      simp only [hstack]
      rw [sicht_rueckkehr_ohne, sicht_rueckkehr_ohne]
      have hTe :
          (fun s => if oeffentlich (β.temp (r₁.pc + 1) s) = true then r₁.temp s else none) =
          (fun s => if oeffentlich (β.temp (r₁.pc + 1) s) = true then r₂.temp s else none) := by
        funext s
        by_cases hp : oeffentlich (β.temp (r₁.pc + 1) s) = true
        · simp only [hp, if_true]
          exact tempPub s (hT s hp)
        · simp only [if_neg hp]
      have hLe :
          maskiere (β.lokal (r₁.pc + 1)) 0 r₁.lokale =
            maskiere (β.lokal (r₁.pc + 1)) 0 r₂.lokale :=
        maskiere_gleich_mono hL 0 _ _ lokEq
      rw [h, pcEq, hTe, hLe]
  | cons k stack =>
      simp only [hstack]
      rw [sicht_rueckkehr_mit, sicht_rueckkehr_mit]
      rw [h]

theorem pruefeMassSicht : PruefeMassSichtAussage := by
  intro β pc quelle hq hT hL r₁ r₂ live hpc h
  subst hpc
  obtain ⟨pcEq, tempPub, lokEq⟩ := sicht_oeffentliche_teile h
  have hpc' : r₁.pc = r₂.pc := pcEq.symm
  have hZahl : r₁.zahl quelle = r₂.zahl quelle := by
    simp only [Rahmen.zahl, tempPub quelle hq]
  have hFun : r₁.funktion = r₂.funktion := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).funktion) h
  have hFort : r₁.fortsetzungen = r₂.fortsetzungen := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).fortsetzungen) h
  have hStopp : r₁.stopp = r₂.stopp := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).stopp) h
  have hGlob : r₁.globale = r₂.globale := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).globale) h
  have hZa : r₁.zaehler = r₂.zaehler := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).zaehler) h
  have hOb : r₁.obergrenzen = r₂.obergrenzen := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).obergrenzen) h
  have hArr : r₁.arrivalRegions = r₂.arrivalRegions := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).arrivalRegions) h
  have hPlat : r₁.platform = r₂.platform := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).platform) h
  have hEnv : r₁.environment = r₂.environment := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).environment) h
  have hRueck := sicht_rueckgabe_gleich (β := β) h
  have hTe :
      (fun s => if oeffentlich (β.temp (r₁.pc + 1) s) = true then r₁.temp s else none) =
      (fun s => if oeffentlich (β.temp (r₁.pc + 1) s) = true then r₂.temp s else none) := by
    funext s
    by_cases hp : oeffentlich (β.temp (r₁.pc + 1) s) = true
    · simp only [hp, if_true]
      exact tempPub s (hT s hp)
    · simp only [if_neg hp]
  have hLe :
      maskiere (β.lokal (r₁.pc + 1)) 0 r₁.lokale =
        maskiere (β.lokal (r₁.pc + 1)) 0 r₂.lokale :=
    maskiere_gleich_mono hL 0 _ _ lokEq
  change (r₁.setzeMass quelle).sicht β = (r₂.setzeMass quelle).sicht β
  unfold Rahmen.setzeMass
  simp only [← hpc', ← hZahl, ← hFun, ← hFort, ← hStopp, ← hGlob, ← hZa, ← hOb,
    ← hArr, ← hPlat, ← hEnv]
  cases hfunk : r₁.funktion with
  | none =>
      simp only [hfunk, Id.run]
      exact sicht_halt_gleich .ungueltigerWert h
  | some name =>
      cases hzahl : r₁.zahl quelle with
      | none =>
          simp only [hfunk, hzahl, Id.run]
          exact sicht_halt_gleich (.abstieg name) h
      | some value =>
          by_cases hneg : value.zahl.wert < 0
          · simp only [hfunk, hzahl, hneg, Id.run]
            exact sicht_halt_gleich (.abstieg name) h
          · cases hprev : r₁.fortsetzungen.find?
                (fun k => (k.funktion.map Subtype.val) == some name.val) with
            | none =>
                simp only [hfunk, hzahl, hneg, hprev, Id.run]
                unfold Rahmen.sicht
                rw [hTe, hLe, hRueck]
            | some k =>
                cases hmass : k.mass with
                | none =>
                    simp only [hfunk, hzahl, hneg, hprev, hmass, Id.run]
                    exact sicht_halt_gleich (.abstieg name) h
                | some old =>
                    by_cases hge : value.zahl.wert.toNat ≥ old
                    · simp only [hfunk, hzahl, hneg, hprev, hmass, hge, Id.run]
                      exact sicht_halt_gleich (.abstieg name) h
                    · simp only [hfunk, hzahl, hneg, hprev, hmass, hge, Id.run]
                      unfold Rahmen.sicht
                      rw [hTe, hLe, hRueck]

theorem rufeSicht : RufeSichtAussage := by
  intro β pc name args bind hT hL r₁ r₂ live hpc h
  subst hpc
  obtain ⟨pcEq, tempPub, lokEq⟩ := sicht_oeffentliche_teile h
  have hpc' : r₁.pc = r₂.pc := pcEq.symm
  have hTemp : r₁.temp = r₂.temp := funext (fun s => tempPub s (hT s))
  have hLok : r₁.lokale = r₂.lokale := by
    rw [← maskiere_allesOeffentlich (l := β.lokal r₁.pc) hL 0 r₁.lokale,
        ← maskiere_allesOeffentlich (l := β.lokal r₁.pc) hL 0 r₂.lokale]
    exact lokEq
  have hFun : r₁.funktionen = r₂.funktionen := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).funktionen) h
  have hGlob : r₁.globale = r₂.globale := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).globale) h
  have hZa : r₁.zaehler = r₂.zaehler := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).zaehler) h
  have hOb : r₁.obergrenzen = r₂.obergrenzen := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).obergrenzen) h
  have hFunk : r₁.funktion = r₂.funktion := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).funktion) h
  have hMass : r₁.mass = r₂.mass := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).mass) h
  have hFort : r₁.fortsetzungen = r₂.fortsetzungen := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).fortsetzungen) h
  have hStopp : r₁.stopp = r₂.stopp := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).stopp) h
  have hArr : r₁.arrivalRegions = r₂.arrivalRegions := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).arrivalRegions) h
  have hPlat : r₁.platform = r₂.platform := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).platform) h
  have hEnv : r₁.environment = r₂.environment := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).environment) h
  have hRueck := sicht_rueckgabe_gleich (β := β) h
  change (r₁.ruf name args bind).sicht β = (r₂.ruf name args bind).sicht β
  unfold Rahmen.ruf
  simp only [← hpc', ← hTemp, ← hLok, ← hFun, ← hGlob, ← hZa, ← hOb, ← hFunk, ← hMass,
    ← hFort, ← hStopp, ← hArr, ← hPlat, ← hEnv]
  cases hfind : Funktion.finde r₁.funktionen name with
  | none =>
      simp only [hfind, Id.run]
      exact sicht_halt_gleich (.ungueltigerRuf name) h
  | some callee =>
      simp only [← rufArgumente_gleich r₁ r₂ 0 hTemp args callee.parameter]
      cases hargs : r₁.rufArgumente 0 args callee.parameter with
      | none =>
          simp only [hfind, hargs, Id.run]
          exact sicht_halt_gleich (.ungueltigerRuf name) h
      | some callArgs =>
          cases hbind : bind with
          | none =>
              simp only [hfind, hargs, hbind, Id.run]
              by_cases habstieg :
                ((⟨r₁.pc + 1, r₁.temp, r₁.lokale, r₁.zaehler, r₁.obergrenzen,
                    r₁.funktion, r₁.mass, none⟩ : Fortsetzung) :: r₁.fortsetzungen).any
                    (fun k => (k.funktion.map Subtype.val) == some name.val) &&
                  !callee.misstAbstieg
              · simp only [habstieg]
                exact sicht_halt_gleich (.abstieg name) h
              · simp only [habstieg]
                unfold Rahmen.sicht
                rw [hRueck]
          | some target =>
              cases hres : callee.result with
              | none =>
                  simp only [hfind, hargs, hbind, hres, Id.run]
                  exact sicht_halt_gleich (.ungueltigerRuf name) h
              | some source =>
                  by_cases hfit : !tyFits source target
                  · simp only [hfind, hargs, hbind, hres, hfit, Id.run]
                    exact sicht_halt_gleich (.ungueltigerRuf name) h
                  · simp only [hfind, hargs, hbind, hres, hfit, Id.run]
                    by_cases habstieg :
                      ((⟨r₁.pc + 1, r₁.temp, r₁.lokale, r₁.zaehler, r₁.obergrenzen,
                          r₁.funktion, r₁.mass, some target⟩ : Fortsetzung) :: r₁.fortsetzungen).any
                          (fun k => (k.funktion.map Subtype.val) == some name.val) &&
                        !callee.misstAbstieg
                    · simp only [habstieg]
                      exact sicht_halt_gleich (.abstieg name) h
                    · simp only [habstieg]
                      unfold Rahmen.sicht
                      rw [hRueck]

end Gabbro.Core.Ast.Semantik
