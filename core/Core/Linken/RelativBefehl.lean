module

public import Core.Linken.RelativSchritt

@[expose] public section

namespace Gabbro.Core.Linken

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Annahme
open Gabbro.Core.Maschine
open Gabbro.Core.Katalog

/-- Relocation keeps the measure. -/
theorem frameZurueck_mass (off : Nat) (r : Rahmen) : (frameZurueck off r).mass = r.mass :=
  rfl

/-- Returning a frame is the frame. -/
theorem pure_rahmen_eq (r : Rahmen) : (pure r : Id Rahmen) = r :=
  rfl

/-- Setting a pass counter commutes with relocation. -/
theorem setzePasszahlRec_proj (off : Nat) (r p : Rahmen) (hp : p = frameZurueck off r)
    (hpc : off ≤ r.pc) (stelle : Nat) (v : Option Nat) :
    frameZurueck off { r with pc := r.pc + 1, zaehler := Function.update r.zaehler (r.pc + stelle) v } =
      { p with pc := p.pc + 1, zaehler := Function.update p.zaehler (p.pc + stelle) v } := by
  subst hp
  simp only [frameZurueck]
  congr 1
  · show (r.pc + 1) - off = (r.pc - off) + 1
    omega
  · funext j
    have hkey : (r.pc - off) + stelle = (r.pc + stelle) - off := by omega
    by_cases hj : j = (r.pc + stelle) - off
    · subst hj
      have h1 : ((r.pc + stelle) - off) + off = r.pc + stelle := by omega
      simp only [karteZurueck, hkey, Function.update_self, h1, Function.update_self]
    · have h2 : j + off ≠ r.pc + stelle := by omega
      simp only [karteZurueck, hkey, Function.update_of_ne hj, Function.update_of_ne h2]

/-- Choosing a variant branch commutes with relocation. -/
theorem waehleVarianteRec_proj (off : Nat) (r p : Rahmen) (hp : p = frameZurueck off r)
    (hpc : off ≤ r.pc) (offset : Nat) (l : List (Option Dynamisch)) :
    frameZurueck off { r with pc := r.pc + offset, lokale := l } =
      { p with pc := p.pc + offset, lokale := l } := by
  subst hp
  have h : (r.pc + offset) - off = (r.pc - off) + offset := by omega
  simp only [frameZurueck, frameZurueck_lokale, h]

/-- The call continuation relocates with the frame. -/
theorem rufKont_proj (off : Nat) (r : Rahmen) (hpc : off ≤ r.pc) (bind : Option (Ty .value)) :
    (⟨(frameZurueck off r).pc + 1, (frameZurueck off r).temp, (frameZurueck off r).lokale, (frameZurueck off r).zaehler, (frameZurueck off r).obergrenzen, (frameZurueck off r).funktion, (frameZurueck off r).mass, bind⟩ : Fortsetzung) =
    fortsetzungZurueck off ⟨r.pc + 1, r.temp, r.lokale, r.zaehler, r.obergrenzen, r.funktion, r.mass, bind⟩ := by
  have h : ((r.pc - off) + 1) = ((r.pc + 1) - off) := by omega
  simp only [fortsetzungZurueck, frameZurueck_temp, frameZurueck_lokale, frameZurueck, funktionAktuell_proj, h]

/-- The call transfer record commutes with relocation. -/
theorem rufFinal_proj (off : Nat) (r p : Rahmen) (hp : p = frameZurueck off r)
    (adresse : Nat) (lok : List (Option Dynamisch)) (stack : List Fortsetzung) (target : Identifier) :
    frameZurueck off { r with pc := adresse, temp := fun _slot => none, lokale := lok, zaehler := fun _slot => none, obergrenzen := fun _slot => none, fortsetzungen := stack, funktion := some target, mass := none } =
      { p with pc := adresse - off, temp := fun _slot => none, lokale := lok, zaehler := fun _slot => none, obergrenzen := fun _slot => none, fortsetzungen := stack.map (fortsetzungZurueck off), funktion := some target, mass := none } := by
  subst hp
  unfold frameZurueck
  rfl

/-- Entry arguments preserve the program counter. -/
theorem eintrittArgumente_behaeltPc (r : Rahmen) (types : List (Ty .value)) (entry : Rahmen)
    (h : r.eintrittArgumente types = some entry) : entry.pc = r.pc := by
  simp only [Rahmen.eintrittArgumente] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    rfl
  · split at h
    · simp only [Option.some.injEq] at h
      subst h
      rfl
    · exact nomatch h

/-- A call commutes with relocation. -/
theorem ruf_proj (off : Nat) (r : Rahmen) (hpc : off ≤ r.pc) (name : Identifier)
    (sources : List (Ty .value)) (bind : Option (Ty .value)) :
    (frameZurueck off r).ruf name sources bind = frameZurueck off (r.ruf name sources bind) := by
  have hfind : ∀ n, Funktion.finde (frameZurueck off r).funktionen n =
      ((Funktion.finde r.funktionen n).map (funktionZurueck off)) := by
    intro n
    rw [funktionen_proj]
    exact finde_abbild _ _ _
  simp only [Rahmen.ruf, hfind, Id.run, pure_rahmen_eq]
  cases hcallee : Funktion.finde r.funktionen name with
  | none =>
    simp only [hcallee, Option.map_some, Option.map_none, halt_proj, pure_rahmen_eq]
  | some callee =>
    simp only [hcallee, Option.map_some, Option.map_none, funktionZurueck_parameter, rufArgumente_proj]
    cases hargs : r.rufArgumente 0 sources callee.parameter with
    | none =>
      simp only [hargs, halt_proj]
    | some args =>
      simp only [hargs, funktionZurueck_result]
      have hkont : ∀ b : Option (Ty .value),
          ({ pc := (frameZurueck off r).pc + 1, temp := (frameZurueck off r).temp, lokale := (frameZurueck off r).lokale, zaehler := (frameZurueck off r).zaehler, obergrenzen := (frameZurueck off r).obergrenzen, funktion := (frameZurueck off r).funktion, mass := (frameZurueck off r).mass, eingang := b } : Fortsetzung) =
          fortsetzungZurueck off ⟨r.pc + 1, r.temp, r.lokale, r.zaehler, r.obergrenzen, r.funktion, r.mass, b⟩ := by
        intro b
        have h : ((r.pc - off) + 1) = ((r.pc + 1) - off) := by omega
        simp only [fortsetzungZurueck, frameZurueck, frameZurueck_pc, h]
      cases hbind : bind with
      | none =>
        simp only [hbind]
        rw [hkont, fortsetzungen_proj, ← List.map_cons, stackAny_map, funktionZurueck_misstAbstieg]
        split
        all_goals (unfold frameZurueck; congr 1)
      | some target =>
        simp only [hbind]
        cases hres : callee.result with
        | none =>
          simp only [hres, halt_proj, Option.map_some, Option.map_none]
        | some source =>
          simp only [hres, Option.map_some, Option.map_none]
          by_cases hfit : (!tyFits source target) = true
          · simp only [if_pos hfit, halt_proj]
          · simp only [if_neg hfit]
            rw [hkont, fortsetzungen_proj, ← List.map_cons, stackAny_map, funktionZurueck_misstAbstieg]
            split
            all_goals (unfold frameZurueck; congr 1)

/-- Setting the descent measure commutes with relocation. -/
theorem setzeMass_proj (off : Nat) (r : Rahmen) (hpc : off ≤ r.pc) (slot : Nat) :
    (frameZurueck off r).setzeMass slot = frameZurueck off (r.setzeMass slot) := by
  have h : (r.pc + 1) - off = (r.pc - off) + 1 := by omega
  simp only [Rahmen.setzeMass, funktionAktuell_proj, zahl_proj, Id.run, pure_rahmen_eq]
  cases hfun : r.funktion with
  | none =>
    simp only [hfun, halt_proj]
  | some name =>
    simp only [hfun]
    cases hzahl : r.zahl slot with
    | none =>
      simp only [hzahl, halt_proj]
    | some value =>
      simp only [hzahl]
      have hfind : ((frameZurueck off r).fortsetzungen.find?
          (fun k => (k.funktion.map Subtype.val) == some name.val)) =
          ((r.fortsetzungen.find? (fun k => (k.funktion.map Subtype.val) == some name.val)).map
            (fortsetzungZurueck off)) := by
        rw [fortsetzungen_proj]
        exact stackFind_map _ _ _
      simp only [hfind]
      cases hprev : r.fortsetzungen.find? (fun k => (k.funktion.map Subtype.val) == some name.val) with
      | none =>
        simp only [hprev, Option.map_some, Option.map_none]
        have h : (r.pc + 1) - off = (r.pc - off) + 1 := by omega
        split
        all_goals try split
        all_goals first
          | simp only [halt_proj]
          | simp only [frameZurueck, h]
      | some k =>
        simp only [hprev, Option.map_some, Option.map_none, fortsetzungZurueck_mass]
        cases hmass : k.mass with
        | none =>
          simp only [hmass]
          split
          all_goals try split
          all_goals first
            | simp only [halt_proj]
            | simp only [frameZurueck, h]
        | some old =>
          simp only [hmass]
          split
          all_goals try split
          all_goals first
            | simp only [halt_proj]
            | simp only [frameZurueck, h]

/-- A thread start checks the relocated table like the original one. -/
theorem starte_proj (off : Nat) (r : Rahmen) (hpc : off ≤ r.pc) (name : Identifier)
    (_live : Nat → Bool) :
    (Befehl.starte name).auswerten (frameZurueck off r) _live =
      frameZurueck off ((Befehl.starte name).auswerten r _live) := by
  simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, funktionen_proj, nodupNamen_map, findRekursiv_map, findPasst_map, finde_abbild]
  by_cases hN : ¬(r.funktionen.map fun f => f.name.val).Nodup
  · simp only [if_pos hN, halt_proj]
  · simp only [if_neg hN]
    cases hrec : (r.funktionen.find? fun f => !f.misstAbstieg && Funktion.rekursiv r.funktionen f) with
    | some f =>
      simp only [hrec, Option.map_some, Option.map_none, funktionZurueck_name, halt_proj]
    | none =>
      simp only [hrec, Option.map_some, Option.map_none]
      cases hpas : ((r.funktionen.flatMap Funktion.ruft).find? fun call => !(call.passt r.funktionen)) with
      | some bad =>
        simp only [hpas, Option.map_some, Option.map_none, halt_proj]
      | none =>
        simp only [hpas, Option.map_some, Option.map_none, finde_abbild, rufArgumente_proj, funktionZurueck_parameter, funktionZurueck_result, eintrittArgumente_proj]
        cases hfin : Funktion.finde r.funktionen name with
        | none =>
          simp only [hfin, Option.map_some, Option.map_none, halt_proj]
        | some target =>
          simp only [hfin, Option.map_some, Option.map_none, funktionZurueck_parameter, eintrittArgumente_proj]
          cases hentry : r.eintrittArgumente target.parameter with
          | none =>
            simp only [hentry, Option.map_some, Option.map_none, halt_proj]
          | some entry =>
            simp only [hentry, Option.map_some, Option.map_none]
            have hpcEntry : off ≤ entry.pc := by
              rw [eintrittArgumente_behaeltPc r _ _ hentry]
              exact hpc
            simp only [funktionZurueck_result, ruf_proj, hpcEntry, hpc]

/-- Relocating the acting frame commutes with evaluating any instruction. -/
theorem auswerten_projektion (off : Nat) (b : Befehl) (r : Rahmen) (live : Nat → Bool)
    (hpc : off ≤ r.pc) (modullaenge : Nat) :
    b.auswerten (frameZurueck off r) live = frameZurueck off (b.auswerten r live) := by
  cases b with
  | literal =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, schreibe_proj, hpc]
  | binaer =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, schreibe_proj, hpc, zahl_proj]
  | binden =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, schrittLokal2_proj, hpc, temp_proj, frameZurueck_temp, frameZurueck_lokale, frameZurueck_rueckgabe, frameZurueck_stopp, globale_proj, funktionAktuell_proj, frameZurueck_mass, arrivalRegions_proj, platform_proj, environment_proj]
  | wahrheitswert =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, schreibe_proj, hpc]
  | lesen =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, schreibe_proj, hpc, frameZurueck_lokale]
  | negativ =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, schreibe_proj, hpc]
  | negieren =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, schreibe_proj, hpc, zahl_proj]
  | verneinen =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, schreibe_proj, hpc, temp_proj]
  | teilen =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, schreibe_proj, hpc, zahl_proj]
  | vergleichen =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, schreibe_proj, hpc, zahl_proj]
  | springeWenn =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, vorwaerts_proj, weiter_proj, hpc, temp_proj]
  | zuweisen =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, schrittLokal_proj, hpc, temp_proj, frameZurueck_temp, frameZurueck_lokale, frameZurueck_rueckgabe, frameZurueck_stopp, globale_proj, funktionAktuell_proj, frameZurueck_mass, arrivalRegions_proj, platform_proj, environment_proj]
  | zurueck =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, rueckkehr_proj, hpc, temp_proj]
  | springe =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, vorwaerts_proj, hpc]
  | blockEnde =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, schrittLokal2_proj, hpc, frameZurueck_temp, frameZurueck_lokale, frameZurueck_rueckgabe, frameZurueck_stopp, globale_proj, funktionAktuell_proj, frameZurueck_mass, arrivalRegions_proj, platform_proj, environment_proj]
  | bindeWert =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, schrittLokal_proj, hpc, temp_proj, frameZurueck_temp, frameZurueck_lokale, frameZurueck_rueckgabe, frameZurueck_stopp, globale_proj, funktionAktuell_proj, frameZurueck_mass, arrivalRegions_proj, platform_proj, environment_proj]
  | definiere =>
    have hadr : ((r.pc - off) + 1) = ((r.pc + 1) - off) := by omega
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, definiereRecord_proj, hpc, funktionZurueck, frameZurueck_pc, hadr, frameZurueck_temp, frameZurueck_lokale, frameZurueck_rueckgabe, frameZurueck_stopp, globale_proj, funktionAktuell_proj, frameZurueck_mass, arrivalRegions_proj, platform_proj, environment_proj]
  | rufe =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, ruf_proj, hpc]
  | rueckVoid =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, rueckkehr_proj, hpc]
  | pruefeMass =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, setzeMass_proj, hpc, zahl_proj]
  | setzePasszahl src _dist =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, zahl_proj]
    cases hzahl : r.zahl src with
    | none =>
      simp only [hzahl, halt_proj]
    | some value =>
      simp only [hzahl, setzePasszahlRec_proj, hpc]
  | whileTest src _exit _handler =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, temp_proj]
    cases hmatch : (r.temp src).bind alsBoolean with
    | none =>
      simp only [hmatch, halt_proj]
    | some test =>
      simp only [hmatch, pass_proj, hpc]
  | forAnfang lower upper index skipEmpty shadowed missing =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, zahl_proj]
    cases hlow : r.zahl lower with
    | none =>
      simp only [hlow, halt_proj]
    | some a =>
      simp only [hlow]
      cases hup : r.zahl upper with
      | none =>
        simp only [hup, halt_proj]
      | some b =>
        simp only [hup]
        by_cases hsh : shadowed || (missing && decide (a.zahl.wert < b.zahl.wert))
        · simp only [if_pos hsh, halt_proj]
        · simp only [if_neg hsh]
          by_cases hle : b.zahl.wert ≤ a.zahl.wert
          · simp only [if_pos hle, vorwaerts_proj, hpc]
          · simp only [if_neg hle]
            cases hval : wertIn index a.pack with
            | none =>
              simp only [hval, halt_proj]
            | some initial =>
              simp only [hval, forAnfangMain_proj, hpc]
  | forTest =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq]
    rw [frameZurueck_lokale, obergrenzenAmPc_proj _ _ hpc]
    cases hcur : r.lokale.head?.join.bind alsGanzzahl with
    | none =>
      simp only [hcur, halt_proj]
    | some current =>
      simp only [hcur]
      cases hup : r.obergrenzen r.pc with
      | none =>
        simp only [hup, halt_proj]
      | some upper =>
        simp only [hup, pass_proj, hpc]
  | forNaechster =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, frameZurueck_lokale, ganz_proj]
    cases hcur : r.lokale.head?.join.bind alsGanzzahl with
    | none =>
      simp only [hcur, halt_proj]
    | some current =>
      simp only [hcur]
      split
      · simp only [forNaechsterRec_proj, hpc]
      · simp only [halt_proj]
  | zurueckSprung =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, rueckwaerts_proj]
  | starte =>
    simp only [starte_proj, hpc]
  | ende =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, ende_proj, frameZurueck_temp, frameZurueck_lokale, frameZurueck_rueckgabe, frameZurueck_stopp, globale_proj, funktionAktuell_proj, frameZurueck_mass, arrivalRegions_proj, platform_proj, environment_proj]
  | baueArray =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, schreibe_proj, hpc, temp_proj]
  | liesArray =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, schreibe_proj, hpc, temp_proj, frameZurueck_temp, zahl_proj]
  | baueTupel =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, schreibe_proj, hpc, temp_proj, frameZurueck_temp]
  | liesTupelfeld =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, schreibe_proj, hpc, temp_proj]
  | bindeTupel =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, schrittLokal2_proj, hpc, temp_proj, frameZurueck_temp, frameZurueck_lokale, frameZurueck_rueckgabe, frameZurueck_stopp, globale_proj, funktionAktuell_proj, frameZurueck_mass, arrivalRegions_proj, platform_proj, environment_proj]
  | definiereRecord =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, schrittLokal_proj, hpc, Rahmen.installSchema, frameZurueck_temp, frameZurueck_lokale, frameZurueck_rueckgabe, frameZurueck_stopp, globale_proj, funktionAktuell_proj, frameZurueck_mass, arrivalRegions_proj, platform_proj, environment_proj]
  | baueRecord =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, schreibe_proj, hpc, temp_proj, frameZurueck_temp]
  | liesRecordFeld =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, schreibe_proj, hpc, temp_proj]
  | setzeRecordFeld =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, schrittLokal2_proj, hpc, temp_proj, frameZurueck_lokale, frameZurueck_temp, frameZurueck_lokale, frameZurueck_rueckgabe, frameZurueck_stopp, globale_proj, funktionAktuell_proj, frameZurueck_mass, arrivalRegions_proj, platform_proj, environment_proj]
  | definiereVariante =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, schrittLokal_proj, hpc, Rahmen.installSchema, frameZurueck_temp, frameZurueck_lokale, frameZurueck_rueckgabe, frameZurueck_stopp, globale_proj, funktionAktuell_proj, frameZurueck_mass, arrivalRegions_proj, platform_proj, environment_proj]
  | baueVariante =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, schreibe_proj, hpc, temp_proj]
  | waehleVariante src _name _labels _cases _branches =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, temp_proj]
    cases htmp : (r.temp src).bind (wertAls (variantValueType _name _labels _cases)) with
    | none =>
      simp only [htmp, halt_proj, Option.map_some, Option.map_none]
    | some value =>
      simp only [htmp, Option.map_some, Option.map_none]
      cases hbr : _branches[(variantCase _cases value).1]? with
      | none =>
        simp only [hbr, halt_proj, Option.map_some, Option.map_none]
      | some out =>
        have h : (r.pc - off) + out.1 = (r.pc + out.1) - off := by omega
        simp only [hbr, Option.map_some, Option.map_none, frameZurueck, frameZurueck_pc, frameZurueck_temp, frameZurueck_lokale, frameZurueck_rueckgabe, frameZurueck_stopp, globale_proj, funktionAktuell_proj, frameZurueck_mass, arrivalRegions_proj, platform_proj, environment_proj, h]
  | textLiteral =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, schreibe_proj, hpc]
  | textConcat =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, schreibe_proj, hpc, temp_proj]
  | textIndex base capacity =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, temp_proj, zahl_proj, frameZurueck_temp]
    cases htxt : (r.temp base).bind (wertAls (.text capacity)) with
    | none =>
      simp only [htxt, halt_proj]
    | some text =>
      simp only [htxt]
      cases hoff : r.zahl (base + 1) with
      | none =>
        simp only [hoff, halt_proj]
      | some offset =>
        simp only [hoff]
        split
        · simp only [halt_proj]
        · cases hbyte : text.bytes[offset.zahl.wert.toNat]? with
          | none =>
            simp only [hbyte, halt_proj]
          | some byte =>
            simp only [hbyte, schreibe_proj, hpc]
  | substring base capacity =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, temp_proj, zahl_proj, frameZurueck_temp]
    cases htxt : (r.temp base).bind (wertAls (.text capacity)) with
    | none =>
      simp only [htxt, halt_proj]
    | some text =>
      simp only [htxt]
      cases hfirst : r.zahl (base + 1) with
      | none =>
        simp only [hfirst, halt_proj]
      | some first =>
        simp only [hfirst]
        cases hlast : r.zahl (base + 2) with
        | none =>
          simp only [hlast, halt_proj]
        | some last =>
          simp only [hlast]
          split
          all_goals simp only [halt_proj, schreibe_proj, hpc, temp_proj]
  | textLength =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, schreibe_proj, hpc, temp_proj]
  | definiereTraeger =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, schrittLokal_proj, hpc, Rahmen.installSchema, frameZurueck_temp, frameZurueck_lokale, frameZurueck_rueckgabe, frameZurueck_stopp, globale_proj, funktionAktuell_proj, frameZurueck_mass, arrivalRegions_proj, platform_proj, environment_proj]
  | optionIstBesetzt =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, schreibe_proj, hpc, temp_proj]
  | definiereEffektgruppe =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, schrittLokal_proj, hpc, Rahmen.installSchema, frameZurueck_temp, frameZurueck_lokale, frameZurueck_rueckgabe, frameZurueck_stopp, globale_proj, funktionAktuell_proj, frameZurueck_mass, arrivalRegions_proj, platform_proj, environment_proj]
  | waehleUmgebung =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, umgebung_proj, hpc, frameZurueck_temp, frameZurueck_lokale, frameZurueck_rueckgabe, frameZurueck_stopp, globale_proj, funktionAktuell_proj, frameZurueck_mass, arrivalRegions_proj, platform_proj, environment_proj]
  | bindeRegion =>
    have hpc0 : (r.pc - off) + off = r.pc := by omega
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, frameZurueck_lokale, arrivalRegions_proj, platform_proj, borrowsRegion_proj, hpc0]
    trace_state
    sorry
  | zugriff =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, zugriff_proj, hpc]
  | faden =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, faden_proj, hpc]
  | maskiere =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, weiter_proj, hpc]
  | prioritaet =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, weiter_proj, hpc]
  | sendeUnterbrechung =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, weiter_proj, hpc]
  | leiteLeitung =>
    simp only [Befehl.auswerten, Id.run, pure_rahmen_eq, weiter_proj, hpc]

/-- A relocated step commutes with the original step. -/
theorem nach_projektion_kommutiert (off : Nat) (c : Kontext) (b : Befehl) (s : Zustand)
    (hpc : off ≤ (s.lokal c).pc) (hdeckel : (s.lokal c).pc < off + modullaenge) :
    b.nach c (zustandImModul off c s) = zustandImModul off c (b.nach c s) := by
  have _hdeckel := hdeckel
  have hframe : (zustandImModul off c s).lokal c = frameZurueck off (s.lokal c) :=
    zustandImModul_frame _ _ _
  have hlive : (zustandImModul off c s).regionLive = s.regionLive := rfl
  have haus := auswerten_projektion off b (s.lokal c) s.regionLive hpc modullaenge
  have hnach : (b.nach c s).lokal c = b.auswerten (s.lokal c) s.regionLive :=
    Befehl.nach_lokal_eigener b c s
  change { (zustandImModul off c s) with lokal := Function.update (zustandImModul off c s).lokal c (b.auswerten ((zustandImModul off c s).lokal c) (zustandImModul off c s).regionLive) } = _
  simp only [hframe, hlive, haus, hnach]
  unfold zustandImModul Befehl.nach
  simp only [Function.update_idem, Function.update_self]

end Gabbro.Core.Linken
