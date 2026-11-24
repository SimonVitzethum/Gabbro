module

public import Core.Beobachtung.Fluss.Beschriftung.Sprung
public import Core.Beobachtung.Fluss.Beschriftung.AufgabenBeweise
public import Core.Beobachtung.Fluss.Beschriftung.Offen.Erfuellbar
public import Core.Beobachtung.Fluss.Beschriftung.Offen.Ruf

@[expose] public section

/-! Pinned duties for the three control-flow instructions still on the all-public fallback.
    The statements fix the least publicity a declaration owes for each of them, and the proofs
    show that the rule is sound for the public view. -/

namespace Gabbro.Core.Ast.Semantik

open Maschine Beobachtung Katalog

/-- `starte`: the checks read only the always-visible function table and arrival regions, and
    the successful step builds a fresh entry frame (cleared temporaries, locals from the visible
    globals) at the callee's public address. All temporaries at `pc` must nevertheless be public:
    when the target has no owned-region parameters the entry reuses the current temporary array
    and stores it in the always-visible continuation stack. Locals at `pc` are discarded and
    never read, so they may stay secret; no successor labels are needed because the entry clears
    the temporaries and rebuilds the locals from public data. -/
def StarteSichtAussage : Prop :=
  ∀ (β : Beschriftung) (pc : Nat) (name : Identifier),
    (∀ s, oeffentlich (β.temp pc s) = true) →
    (Befehl.starte name).SichtErhaltendBei β pc

/-- `ende`: the step only sets the public stop reason and publishes local 0 as the result.
    Local 0 must be public exactly when the result component is public; if the result is secret
    both views hide it and the local may stay secret. No other slot is read and `pc` does not
    move, hence no fall-through labels are needed. -/
def EndeSichtAussage : Prop :=
  ∀ (β : Beschriftung) (pc : Nat),
    (oeffentlich β.ergebnis = true → oeffentlich (β.lokal pc 0) = true) →
    Befehl.ende.SichtErhaltendBei β pc

/-- `bindeRegion`: the receiver local decides which arrival region is bound and the borrow check
    scans the whole local stack for a view of that slot, so every local at `pc` must be public.
    No temporary is read, but the temporaries survive unchanged into `pc + 1`, hence their
    labels at the successor must be at least as secret as at `pc`. The new local 0 comes from
    the visible platform contract, so no label on the successor locals is required. -/
def BindeRegionSichtAussage : Prop :=
  ∀ (β : Beschriftung) (pc receiver : Nat) (init : RegionInitializer),
    (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) →
    (∀ i, oeffentlich (β.lokal pc i) = true) →
    (Befehl.bindeRegion receiver init).SichtErhaltendBei β pc

/-- A declaration whose local `i` is secret at every cut; all temporaries, all other locals and
    the result are public. -/
def niGeheimLokalBeschriftung (i : Nat) : Beschriftung :=
  { lokal := fun _ j => if j = i then geheim else ∅ }

theorem niGeheimLokal_temp (i pc s : Nat) :
    oeffentlich ((niGeheimLokalBeschriftung i).temp pc s) = true := by
  simp only [niGeheimLokalBeschriftung, oeffentlich_leer]

theorem niGeheimLokal_lokal (i pc j : Nat) :
    oeffentlich ((niGeheimLokalBeschriftung i).lokal pc j) = true ↔ j ≠ i := by
  simp only [niGeheimLokalBeschriftung]
  split
  · simp only [geheim_verborgen, Bool.false_eq_true, false_iff, ne_eq, not_not]
    assumption
  · rename_i h
    simp only [oeffentlich_leer, true_iff]
    exact h

/-- A call keeps equal views when the two frames already have equal temporary and local arrays.
    This is the call proof without deriving those two agreements from labels: `starte` supplies
    them for the entry frames it builds. -/
theorem rufSichtGleich (β : Beschriftung) (r₁ r₂ : Rahmen) (name : Identifier)
    (args : List (Ty .value)) (bind : Option (Ty .value))
    (hTemp : r₁.temp = r₂.temp) (hLok : r₁.lokale = r₂.lokale)
    (h : r₁.sicht β = r₂.sicht β) :
    (r₁.ruf name args bind).sicht β = (r₂.ruf name args bind).sicht β := by
  obtain ⟨pcEq, tempPub, lokEq⟩ := sicht_oeffentliche_teile h
  have hpc' : r₁.pc = r₂.pc := pcEq.symm
  have hFort : r₁.fortsetzungen = r₂.fortsetzungen := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).fortsetzungen) h
  have hStopp : r₁.stopp = r₂.stopp := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).stopp) h
  have hZa : r₁.zaehler = r₂.zaehler := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).zaehler) h
  have hOb : r₁.obergrenzen = r₂.obergrenzen := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).obergrenzen) h
  have hGlob : r₁.globale = r₂.globale := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).globale) h
  have hFun : r₁.funktionen = r₂.funktionen := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).funktionen) h
  have hFunk : r₁.funktion = r₂.funktion := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).funktion) h
  have hMass : r₁.mass = r₂.mass := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).mass) h
  have hArr : r₁.arrivalRegions = r₂.arrivalRegions := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).arrivalRegions) h
  have hPlat : r₁.platform = r₂.platform := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).platform) h
  have hEnv : r₁.environment = r₂.environment := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).environment) h
  have hRueck := sicht_rueckgabe_gleich (β := β) h
  unfold Rahmen.ruf
  simp only [← hpc', ← hTemp, ← hLok, ← hFun, ← hGlob, ← hZa, ← hOb, ← hFunk, ← hMass,
    ← hFort, ← hStopp, ← hArr, ← hPlat, ← hEnv]
  cases hfind : Funktion.finde r₁.funktionen name with
  | none =>
      simp only [hfind, Id.run, pure, if_true, Bool.false_eq_true, eq_self_iff_true]
      exact sicht_halt_gleich (.ungueltigerRuf name) h
  | some callee =>
      simp only [← rufArgumente_gleich r₁ r₂ (fun s => congrFun hTemp s) 0 args callee.parameter]
      cases hargs : r₁.rufArgumente 0 args callee.parameter with
      | none =>
          simp only [hfind, hargs, Id.run, pure, if_true, Bool.false_eq_true, eq_self_iff_true]
          exact sicht_halt_gleich (.ungueltigerRuf name) h
      | some callArgs =>
          cases hbind : bind with
          | none =>
              simp only [hfind, hargs, hbind, Id.run, pure, if_true, Bool.false_eq_true, eq_self_iff_true]
              by_cases habstieg :
                ((⟨r₁.pc + 1, r₁.temp, r₁.lokale, r₁.zaehler, r₁.obergrenzen,
                    r₁.funktion, r₁.mass, none⟩ : Fortsetzung) :: r₁.fortsetzungen).any
                    (fun k => (k.funktion.map Subtype.val) == some name.val) &&
                  !callee.misstAbstieg
              · simp only [habstieg, if_true, Bool.false_eq_true, eq_self_iff_true]
                exact sicht_halt_gleich (.abstieg name) h
              · simp only [habstieg, if_false, Bool.false_eq_true, eq_self_iff_true]
                unfold Rahmen.sicht
                rw [hRueck]
          | some target =>
              cases hres : callee.result with
              | none =>
                  simp only [hfind, hargs, hbind, hres, Id.run, pure, if_true, Bool.false_eq_true, eq_self_iff_true]
                  exact sicht_halt_gleich (.ungueltigerRuf name) h
              | some source =>
                  by_cases hfit : !tyFits source target
                  · simp only [hfind, hargs, hbind, hres, hfit, Id.run, pure, if_true, if_false,
                      Bool.false_eq_true, eq_self_iff_true]
                    exact sicht_halt_gleich (.ungueltigerRuf name) h
                  · simp only [hfind, hargs, hbind, hres, hfit, Id.run, pure, if_true, if_false,
                      Bool.false_eq_true, eq_self_iff_true]
                    by_cases habstieg :
                      ((⟨r₁.pc + 1, r₁.temp, r₁.lokale, r₁.zaehler, r₁.obergrenzen,
                          r₁.funktion, r₁.mass, some target⟩ : Fortsetzung) :: r₁.fortsetzungen).any
                          (fun k => (k.funktion.map Subtype.val) == some name.val) &&
                        !callee.misstAbstieg
                    · simp only [habstieg, if_true, Bool.false_eq_true, eq_self_iff_true]
                      exact sicht_halt_gleich (.abstieg name) h
                    · simp only [habstieg, if_false, Bool.false_eq_true, eq_self_iff_true]
                      unfold Rahmen.sicht
                      rw [hRueck]

theorem starteSicht : StarteSichtAussage := by
  intro β pc name hT r₁ r₂ live hpc h
  subst hpc
  obtain ⟨pcEq, tempPub, lokEq⟩ := sicht_oeffentliche_teile h
  have hpc' : r₁.pc = r₂.pc := pcEq.symm
  have hTemp : r₁.temp = r₂.temp := funext (fun s => tempPub s (hT s))
  have hFun : r₁.funktionen = r₂.funktionen := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).funktionen) h
  have hArr : r₁.arrivalRegions = r₂.arrivalRegions := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).arrivalRegions) h
  have hGlob : r₁.globale = r₂.globale := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).globale) h
  have hFort : r₁.fortsetzungen = r₂.fortsetzungen := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).fortsetzungen) h
  have hZa : r₁.zaehler = r₂.zaehler := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).zaehler) h
  have hOb : r₁.obergrenzen = r₂.obergrenzen := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).obergrenzen) h
  have hFunk : r₁.funktion = r₂.funktion := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).funktion) h
  have hMass : r₁.mass = r₂.mass := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).mass) h
  have hStopp : r₁.stopp = r₂.stopp := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).stopp) h
  have hPlat : r₁.platform = r₂.platform := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).platform) h
  have hEnv : r₁.environment = r₂.environment := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).environment) h
  have hRueck := sicht_rueckgabe_gleich (β := β) h
  by_cases hnd : ¬ (r₁.funktionen.map (fun f => f.name.val)).Nodup
  · have hnd₂ : ¬ (r₂.funktionen.map (fun f => f.name.val)).Nodup := by
      simpa only [hFun] using hnd
    have e₁ : (Befehl.starte name).auswerten r₁ live = r₁.halt (.ungueltigerRuf name) := by
      simpa only [Befehl.auswerten, hnd, Id.run, pure, if_true, not_false_eq_true,
        Bool.false_eq_true, eq_self_iff_true]

    have e₂ : (Befehl.starte name).auswerten r₂ live = r₂.halt (.ungueltigerRuf name) := by
      simpa only [Befehl.auswerten, hnd₂, Id.run, pure, if_true, not_false_eq_true,
        Bool.false_eq_true, eq_self_iff_true]

    rw [e₁, e₂, sicht_halt, sicht_halt, h]
  · have hnd₂ : ¬ ¬ (r₂.funktionen.map (fun f => f.name.val)).Nodup := by
      simpa only [hFun] using hnd
    cases hrec : r₁.funktionen.find?
        (fun f => !f.misstAbstieg && Funktion.rekursiv r₁.funktionen f) with
    | none =>
        have hrec₂ : r₂.funktionen.find?
            (fun f => !f.misstAbstieg && Funktion.rekursiv r₂.funktionen f) = none := by
          simpa only [← hFun] using hrec
        cases hbad : (r₁.funktionen.flatMap Funktion.ruft).find?
            (fun call => !(call.passt r₁.funktionen)) with
        | none =>
            have hbad₂ : (r₂.funktionen.flatMap Funktion.ruft).find?
                (fun call => !(call.passt r₂.funktionen)) = none := by
              simpa only [← hFun] using hbad
            cases htarget : Funktion.finde r₁.funktionen name with
            | none =>
                have htarget₂ : Funktion.finde r₂.funktionen name = none := by
                  simpa only [← hFun] using htarget
                have e₁ : (Befehl.starte name).auswerten r₁ live = r₁.halt (.ungueltigerRuf name) := by
                  simpa only [Befehl.auswerten, hnd, hrec, hbad, htarget, Id.run, pure, if_true,
                    if_false, Bool.false_eq_true, eq_self_iff_true]
                have e₂ : (Befehl.starte name).auswerten r₂ live = r₂.halt (.ungueltigerRuf name) := by
                  simpa only [Befehl.auswerten, hnd₂, hrec₂, hbad₂, htarget₂, Id.run, pure, if_true,
                    if_false, Bool.false_eq_true, eq_self_iff_true]
                rw [e₁, e₂, sicht_halt, sicht_halt, h]
            | some target =>
                have htarget₂ : Funktion.finde r₂.funktionen name = some target := by
                  simpa only [← hFun] using htarget
                by_cases htypes : target.parameter = []
                · have htypes₂ : target.parameter = [] := htypes
                  have e₁ : (Befehl.starte name).auswerten r₁ live =
                      (({ r₁ with lokale := [] } : Rahmen).ruf name target.parameter target.result) := by
                    simpa only [Befehl.auswerten, hnd, hrec, hbad, htarget, htypes,
                      Rahmen.eintrittArgumente, Id.run, pure, if_true, if_false,
                      Bool.not_eq_true, Bool.false_eq_true, eq_self_iff_true]
                  have e₂ : (Befehl.starte name).auswerten r₂ live =
                      (({ r₂ with lokale := [] } : Rahmen).ruf name target.parameter target.result) := by
                    simpa only [Befehl.auswerten, hnd₂, hrec₂, hbad₂, htarget₂, htypes₂,
                      Rahmen.eintrittArgumente, Id.run, pure, if_true, if_false,
                      Bool.not_eq_true, Bool.false_eq_true, eq_self_iff_true]
                  rw [e₁, e₂]
                  apply rufSichtGleich β ({ r₁ with lokale := [] } : Rahmen)
                    ({ r₂ with lokale := [] } : Rahmen) name target.parameter target.result
                  · funext s
                    exact congrFun hTemp s
                  · rfl
                  · unfold Rahmen.sicht
                    rw [← hpc', ← hTemp, ← hRueck, ← hFun, ← hGlob, ← hFort, ← hZa, ← hOb,
                      ← hFunk, ← hMass, ← hStopp, ← hArr, ← hPlat, ← hEnv]
                · by_cases hready :
                    target.parameter.all (· == .ownedRegion) &&
                      target.parameter.length ≤ r₁.arrivalRegions.length
                  · have hready₂ :
                        target.parameter.all (· == .ownedRegion) &&
                          target.parameter.length ≤ r₂.arrivalRegions.length := by
                      simpa only [hArr] using hready
                    let frisch : Nat → Option Dynamisch := fun slot =>
                      if slot < target.parameter.length then some ⟨.ownedRegion, slot⟩ else none
                    have e₁ : (Befehl.starte name).auswerten r₁ live =
                        (({ r₁ with lokale := [], temp := frisch } : Rahmen).ruf
                          name target.parameter target.result) := by
                      simpa only [Befehl.auswerten, hnd, hrec, hbad, htarget, htypes, hready,
                        frisch, Rahmen.eintrittArgumente, Id.run, pure, if_true, if_false,
                        Bool.not_eq_true, Bool.false_eq_true, eq_self_iff_true]
                    have e₂ : (Befehl.starte name).auswerten r₂ live =
                        (({ r₂ with lokale := [], temp := frisch } : Rahmen).ruf
                          name target.parameter target.result) := by
                      simpa only [Befehl.auswerten, hnd₂, hrec₂, hbad₂, htarget₂, htypes, hready₂,
                        frisch, Rahmen.eintrittArgumente, Id.run, pure, if_true, if_false,
                        Bool.not_eq_true, Bool.false_eq_true, eq_self_iff_true]
                    rw [e₁, e₂]
                    apply rufSichtGleich β ({ r₁ with lokale := [], temp := frisch } : Rahmen)
                      ({ r₂ with lokale := [], temp := frisch } : Rahmen)
                      name target.parameter target.result
                    · rfl
                    · rfl
                    · unfold Rahmen.sicht
                      rw [← hpc', ← hRueck, ← hFun, ← hGlob, ← hFort, ← hZa, ← hOb, ← hFunk,
                        ← hMass, ← hStopp, ← hArr, ← hPlat, ← hEnv]
                  · have hreadyf :
                        (target.parameter.all (· == .ownedRegion) &&
                          target.parameter.length ≤ r₁.arrivalRegions.length) = false :=
                      eq_false_of_ne_true hready
                    have hready₂f :
                        (target.parameter.all (· == .ownedRegion) &&
                          target.parameter.length ≤ r₂.arrivalRegions.length) = false := by
                      simpa only [hArr] using hreadyf
                    have e₁ : (Befehl.starte name).auswerten r₁ live = r₁.halt (.ungueltigerRuf name) := by
                      simpa only [Befehl.auswerten, hnd, hrec, hbad, htarget, htypes, hreadyf,
                        Rahmen.eintrittArgumente, Id.run, pure, if_true, if_false,
                        Bool.false_eq_true, eq_self_iff_true]
                    have e₂ : (Befehl.starte name).auswerten r₂ live = r₂.halt (.ungueltigerRuf name) := by
                      simpa only [Befehl.auswerten, hnd₂, hrec₂, hbad₂, htarget₂, htypes, hready₂f,
                        Rahmen.eintrittArgumente, Id.run, pure, if_true, if_false,
                        Bool.false_eq_true, eq_self_iff_true]
                    rw [e₁, e₂, sicht_halt, sicht_halt, h]
        | some bad =>
            have hbad₂ : (r₂.funktionen.flatMap Funktion.ruft).find?
                (fun call => !(call.passt r₂.funktionen)) = some bad := by
              simpa only [← hFun] using hbad
            have e₁ : (Befehl.starte name).auswerten r₁ live = r₁.halt (.ungueltigerRuf bad.name) := by
              simpa only [Befehl.auswerten, hnd, hrec, hbad, Id.run, pure, if_true, if_false,
                Bool.false_eq_true, eq_self_iff_true]
        
            have e₂ : (Befehl.starte name).auswerten r₂ live = r₂.halt (.ungueltigerRuf bad.name) := by
              simpa only [Befehl.auswerten, hnd₂, hrec₂, hbad₂, Id.run, pure, if_true, if_false,
                Bool.false_eq_true, eq_self_iff_true]
        
            rw [e₁, e₂, sicht_halt, sicht_halt, h]
    | some f =>
        have hrec₂ : r₂.funktionen.find?
            (fun f => !f.misstAbstieg && Funktion.rekursiv r₂.funktionen f) = some f := by
          simpa only [← hFun] using hrec
        have e₁ : (Befehl.starte name).auswerten r₁ live = r₁.halt (.unbeschraenkteRekursion f.name) := by
          simpa only [Befehl.auswerten, hnd, hrec, Id.run, pure, if_true, if_false,
            Bool.false_eq_true, eq_self_iff_true]
    
        have e₂ : (Befehl.starte name).auswerten r₂ live = r₂.halt (.unbeschraenkteRekursion f.name) := by
          simpa only [Befehl.auswerten, hnd₂, hrec₂, Id.run, pure, if_true, if_false,
            Bool.false_eq_true, eq_self_iff_true]
    
        rw [e₁, e₂, sicht_halt, sicht_halt, h]

theorem endeSicht : EndeSichtAussage := by
  intro β pc hergebnis r₁ r₂ live hpc h
  subst hpc
  obtain ⟨pcEq, tempPub, lokEq⟩ := sicht_oeffentliche_teile h
  have hKopf : (if oeffentlich β.ergebnis = true then r₁.lokale.head?.join else none) =
      (if oeffentlich β.ergebnis = true then r₂.lokale.head?.join else none) := by
    by_cases hpub : oeffentlich β.ergebnis = true
    · simp only [hpub, if_true]
      have hp0 : oeffentlich (β.lokal r₁.pc 0) = true := hergebnis hpub
      have e := maskiere_eintrag (l := β.lokal r₁.pc) 0 r₁.lokale r₂.lokale 0 lokEq hp0
      simpa only [List.head?_eq_getElem?] using e
    · simp only [hpub, if_false, Bool.false_eq_true]
  have hs (r : Rahmen) :
      (({ r with stopp := some .fertig, rueckgabe := r.lokale.head?.join } : Rahmen).sicht β) =
        { r.sicht β with
          stopp := some .fertig
          rueckgabe := if oeffentlich β.ergebnis = true then r.lokale.head?.join else none } := by
    rfl
  simp only [Befehl.auswerten]
  rw [hs, hs, h, hKopf]

theorem bindeRegionSicht : BindeRegionSichtAussage := by
  intro β pc receiver init hT hL r₁ r₂ live hpc h
  subst hpc
  obtain ⟨pcEq, tempPub, lokEq⟩ := sicht_oeffentliche_teile h
  have hpc' : r₁.pc = r₂.pc := pcEq.symm
  have hLok : r₁.lokale = r₂.lokale := by
    rw [← maskiere_allesOeffentlich (l := β.lokal r₁.pc) hL 0 r₁.lokale,
      ← maskiere_allesOeffentlich (l := β.lokal r₁.pc) hL 0 r₂.lokale]
    exact lokEq
  have hArr : r₁.arrivalRegions = r₂.arrivalRegions := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).arrivalRegions) h
  have hPlat : r₁.platform = r₂.platform := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).platform) h
  have hFort : r₁.fortsetzungen = r₂.fortsetzungen := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).fortsetzungen) h
  have hStopp : r₁.stopp = r₂.stopp := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).stopp) h
  have hRueck := sicht_rueckgabe_gleich (β := β) h
  have hTe : (fun s => if oeffentlich (β.temp (r₁.pc + 1) s) = true then r₁.temp s else none) =
      (fun s => if oeffentlich (β.temp (r₁.pc + 1) s) = true then r₂.temp s else none) := by
    funext s
    by_cases hp : oeffentlich (β.temp (r₁.pc + 1) s) = true
    · simp only [hp, if_true]
      exact tempPub s (hT s hp)
    · simp only [if_neg hp]
  have hs (r : Rahmen) (value : Dynamisch) :
      (({ r with pc := r.pc + 1, lokale := some value :: r.lokale } : Rahmen).sicht β) =
        { r.sicht β with
          pc := r.pc + 1
          temp := fun s => if oeffentlich (β.temp (r.pc + 1) s) = true then r.temp s else none
          lokale := maskiere (β.lokal (r.pc + 1)) 0 (some value :: r.lokale) } := by
    rfl
  cases hslot : r₁.lokale[receiver]?.join.bind (wertAls .ownedRegion) with
  | none =>
      have hslot₂ : r₂.lokale[receiver]?.join.bind (wertAls .ownedRegion) = none := by
        simpa only [hLok] using hslot
      have e₁ : (Befehl.bindeRegion receiver init).auswerten r₁ live =
          r₁.halt .ungueltigerBereich := by
        simp only [Befehl.auswerten]
        unfold Rahmen.bindeRegion
        simp only [Id.run, pure, hslot]
      have e₂ : (Befehl.bindeRegion receiver init).auswerten r₂ live =
          r₂.halt .ungueltigerBereich := by
        simp only [Befehl.auswerten]
        unfold Rahmen.bindeRegion
        simp only [Id.run, pure, hslot₂]
      rw [e₁, e₂, sicht_halt, sicht_halt, h]
  | some slot =>
      have hslot₂ : r₂.lokale[receiver]?.join.bind (wertAls .ownedRegion) = some slot := by
        simpa only [hLok] using hslot
      cases hext : r₁.arrivalRegions[show Nat from slot]? with
      | none =>
          have hext₂ : r₂.arrivalRegions[show Nat from slot]? = none := by
            simpa only [hArr] using hext
          have e₁ : (Befehl.bindeRegion receiver init).auswerten r₁ live =
              r₁.halt .ungueltigerBereich := by
            simp only [Befehl.auswerten]
            unfold Rahmen.bindeRegion
            simp only [Id.run, pure]
            simp only [hslot, hext]
          have e₂ : (Befehl.bindeRegion receiver init).auswerten r₂ live =
              r₂.halt .ungueltigerBereich := by
            simp only [Befehl.auswerten]
            unfold Rahmen.bindeRegion
            simp only [Id.run, pure]
            simp only [hslot₂, hext₂]
          rw [e₁, e₂, sicht_halt, sicht_halt, h]
      | some extent =>
          have hext₂ : r₂.arrivalRegions[show Nat from slot]? = some extent := by
            simpa only [hArr] using hext
          by_cases hbad : (!live (show Nat from slot) || r₁.borrowsRegion (show Nat from slot)) = true
          · have hbad₂ : (!live (show Nat from slot) || r₂.borrowsRegion (show Nat from slot)) = true := by
              simpa only [Rahmen.borrowsRegion, hLok, hFort] using hbad
            have e₁ : (Befehl.bindeRegion receiver init).auswerten r₁ live =
                r₁.halt .ungueltigerBereich := by
              simp only [Befehl.auswerten]
              unfold Rahmen.bindeRegion
              simp only [Id.run, pure]
              simp only [hslot, hext, hbad, if_true]
            have e₂ : (Befehl.bindeRegion receiver init).auswerten r₂ live =
                r₂.halt .ungueltigerBereich := by
              simp only [Befehl.auswerten]
              unfold Rahmen.bindeRegion
              simp only [Id.run, pure]
              simp only [hslot₂, hext₂, hbad₂, if_true]
            rw [e₁, e₂, sicht_halt, sicht_halt, h]
          · have hbadf : (!live (show Nat from slot) || r₁.borrowsRegion (show Nat from slot)) = false :=
              eq_false_of_ne_true hbad
            have hbad₂f : (!live (show Nat from slot) || r₂.borrowsRegion (show Nat from slot)) = false := by
              simpa only [Rahmen.borrowsRegion, hLok, hFort] using hbadf
            cases hval : LowLevel.RegionInitializer.value r₁.platform.ziel (show Nat from slot) extent init with
            | none =>
                have hval₂ : LowLevel.RegionInitializer.value r₂.platform.ziel (show Nat from slot) extent init = none := by
                  simpa only [hPlat] using hval
                have e₁ : (Befehl.bindeRegion receiver init).auswerten r₁ live =
                    r₁.halt .ungueltigerBereich := by
                  simp only [Befehl.auswerten]
                  unfold Rahmen.bindeRegion
                  simp only [Id.run, pure]
                  simp only [hslot, hext, hbadf, hval, if_false, Bool.false_eq_true]
                have e₂ : (Befehl.bindeRegion receiver init).auswerten r₂ live =
                    r₂.halt .ungueltigerBereich := by
                  simp only [Befehl.auswerten]
                  unfold Rahmen.bindeRegion
                  simp only [Id.run, pure]
                  simp only [hslot₂, hext₂, hbad₂f, hval₂, if_false, Bool.false_eq_true]
                rw [e₁, e₂, sicht_halt, sicht_halt, h]
            | some value =>
                have hval₂ : LowLevel.RegionInitializer.value r₂.platform.ziel (show Nat from slot) extent init = some value := by
                  simpa only [hPlat] using hval
                have e₁ : (Befehl.bindeRegion receiver init).auswerten r₁ live =
                    ({ r₁ with pc := r₁.pc + 1, lokale := some value :: r₁.lokale } : Rahmen) := by
                  simp only [Befehl.auswerten]
                  unfold Rahmen.bindeRegion
                  simp only [Id.run, pure]
                  simp only [hslot, hext, hbadf, hval, if_false, Bool.false_eq_true]
                have e₂ : (Befehl.bindeRegion receiver init).auswerten r₂ live =
                    ({ r₂ with pc := r₂.pc + 1, lokale := some value :: r₂.lokale } : Rahmen) := by
                  simp only [Befehl.auswerten]
                  unfold Rahmen.bindeRegion
                  simp only [Id.run, pure]
                  simp only [hslot₂, hext₂, hbad₂f, hval₂, if_false, Bool.false_eq_true]
                rw [e₁, e₂, hs, hs, h, ← hpc', hTe, hLok]

/-- The `starte` premise holds jointly with a secret local, which `starte` never reads: it
    discards the locals and builds the entry frame from the visible globals. -/
theorem starteSicht_erfuellbar (name : Identifier) :
    ∃ (β : Beschriftung) (pc : Nat), ∀ s, oeffentlich (β.temp pc s) = true :=
  ⟨niGeheimLokalBeschriftung 0, 0, fun s => niGeheimLokal_temp 0 0 s⟩

/-- The `ende` premise holds jointly with a secret temporary, which `ende` never reads. -/
theorem endeSicht_erfuellbar :
    ∃ (β : Beschriftung) (pc : Nat),
      oeffentlich β.ergebnis = true → oeffentlich (β.lokal pc 0) = true :=
  ⟨niGeheimTempBeschriftung 0, 0, fun _ => niGeheimTemp_lokal 0 0 0⟩

/-- The `bindeRegion` premises hold jointly with a secret temporary; the instruction reads only
    locals and the always-visible region state. -/
theorem bindeRegionSicht_erfuellbar (receiver : Nat) (init : RegionInitializer) :
    ∃ (β : Beschriftung) (pc : Nat),
      (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) ∧
      (∀ i, oeffentlich (β.lokal pc i) = true) :=
  ⟨niGeheimTempBeschriftung 0, 0,
    (fun s hs => by
      rw [niGeheimTemp_temp] at hs ⊢
      exact hs),
    fun i => niGeheimTemp_lokal 0 0 i⟩

end Gabbro.Core.Ast.Semantik
