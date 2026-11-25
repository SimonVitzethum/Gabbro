module

public import Core.Beobachtung.Unentscheidbar.Simulation.KodierBefehlB

noncomputable section

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Ast.LowLevel
open Gabbro.Core.Katalog
open Gabbro.Core.Text
open Nat.Partrec


theorem inv_literal (f0 : _) (f1 : _) :
    befehlVonCode (befehlZuCode (.literal f0 f1)) = some (.literal f0 f1) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_binaer (f0 : _) (f1 : _) :
    befehlVonCode (befehlZuCode (.binaer f0 f1)) = some (.binaer f0 f1) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_binden (f0 : _) (f1 : _) :
    befehlVonCode (befehlZuCode (.binden f0 f1)) = some (.binden f0 f1) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_wahrheitswert (f0 : _) (f1 : _) :
    befehlVonCode (befehlZuCode (.wahrheitswert f0 f1)) = some (.wahrheitswert f0 f1) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_lesen (f0 : _) (f1 : _) :
    befehlVonCode (befehlZuCode (.lesen f0 f1)) = some (.lesen f0 f1) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_negativ (f0 : _) (f1 : _) :
    befehlVonCode (befehlZuCode (.negativ f0 f1)) = some (.negativ f0 f1) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_negieren (f0 : _) :
    befehlVonCode (befehlZuCode (.negieren f0)) = some (.negieren f0) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_verneinen (f0 : _) :
    befehlVonCode (befehlZuCode (.verneinen f0)) = some (.verneinen f0) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_teilen (f0 : _) :
    befehlVonCode (befehlZuCode (.teilen f0)) = some (.teilen f0) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_vergleichen (f0 : _) (f1 : _) :
    befehlVonCode (befehlZuCode (.vergleichen f0 f1)) = some (.vergleichen f0 f1) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_springeWenn (f0 : _) (f1 : _) (f2 : _) :
    befehlVonCode (befehlZuCode (.springeWenn f0 f1 f2)) = some (.springeWenn f0 f1 f2) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_zuweisen (f0 : _) (f1 : _) (f2 : _) :
    befehlVonCode (befehlZuCode (.zuweisen f0 f1 f2)) = some (.zuweisen f0 f1 f2) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_zurueck (f0 : _) (f1 : _) :
    befehlVonCode (befehlZuCode (.zurueck f0 f1)) = some (.zurueck f0 f1) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_springe (f0 : _) :
    befehlVonCode (befehlZuCode (.springe f0)) = some (.springe f0) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_blockEnde (f0 : _) :
    befehlVonCode (befehlZuCode (.blockEnde f0)) = some (.blockEnde f0) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_bindeWert (f0 : _) (f1 : _) (f2 : _) :
    befehlVonCode (befehlZuCode (.bindeWert f0 f1 f2)) = some (.bindeWert f0 f1 f2) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_definiere (f0 : _) (f1 : _) (f2 : _) (f3 : _) (f4 : _) (f5 : _) (f6 : _) (f7 : _) :
    befehlVonCode (befehlZuCode (.definiere f0 f1 f2 f3 f4 f5 f6 f7)) = some (.definiere f0 f1 f2 f3 f4 f5 f6 f7) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_rufe (f0 : _) (f1 : _) (f2 : _) :
    befehlVonCode (befehlZuCode (.rufe f0 f1 f2)) = some (.rufe f0 f1 f2) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_rueckVoid  :
    befehlVonCode (befehlZuCode (.rueckVoid )) = some (.rueckVoid ) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_pruefeMass (f0 : _) :
    befehlVonCode (befehlZuCode (.pruefeMass f0)) = some (.pruefeMass f0) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_setzePasszahl (f0 : _) (f1 : _) :
    befehlVonCode (befehlZuCode (.setzePasszahl f0 f1)) = some (.setzePasszahl f0 f1) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_whileTest (f0 : _) (f1 : _) (f2 : _) :
    befehlVonCode (befehlZuCode (.whileTest f0 f1 f2)) = some (.whileTest f0 f1 f2) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_forAnfang (f0 : _) (f1 : _) (f2 : _) (f3 : _) (f4 : _) (f5 : _) :
    befehlVonCode (befehlZuCode (.forAnfang f0 f1 f2 f3 f4 f5)) = some (.forAnfang f0 f1 f2 f3 f4 f5) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_forTest (f0 : _) (f1 : _) :
    befehlVonCode (befehlZuCode (.forTest f0 f1)) = some (.forTest f0 f1) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_forNaechster (f0 : _) (f1 : _) :
    befehlVonCode (befehlZuCode (.forNaechster f0 f1)) = some (.forNaechster f0 f1) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_zurueckSprung (f0 : _) :
    befehlVonCode (befehlZuCode (.zurueckSprung f0)) = some (.zurueckSprung f0) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_starte (f0 : _) :
    befehlVonCode (befehlZuCode (.starte f0)) = some (.starte f0) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_ende  :
    befehlVonCode (befehlZuCode (.ende )) = some (.ende ) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_baueArray (f0 : _) (f1 : _) (f2 : _) :
    befehlVonCode (befehlZuCode (.baueArray f0 f1 f2)) = some (.baueArray f0 f1 f2) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_liesArray (f0 : _) (f1 : _) (f2 : _) :
    befehlVonCode (befehlZuCode (.liesArray f0 f1 f2)) = some (.liesArray f0 f1 f2) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_baueTupel (f0 : _) (f1 : _) :
    befehlVonCode (befehlZuCode (.baueTupel f0 f1)) = some (.baueTupel f0 f1) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_liesTupelfeld (f0 : _) (f1 : _) (f2 : _) :
    befehlVonCode (befehlZuCode (.liesTupelfeld f0 f1 f2)) = some (.liesTupelfeld f0 f1 f2) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_bindeTupel (f0 : _) (f1 : _) (f2 : _) :
    befehlVonCode (befehlZuCode (.bindeTupel f0 f1 f2)) = some (.bindeTupel f0 f1 f2) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_definiereRecord (f0 : _) (f1 : _) (f2 : _) :
    befehlVonCode (befehlZuCode (.definiereRecord f0 f1 f2)) = some (.definiereRecord f0 f1 f2) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_baueRecord (f0 : _) (f1 : _) (f2 : _) (f3 : _) (f4 : _) :
    befehlVonCode (befehlZuCode (.baueRecord f0 f1 f2 f3 f4)) = some (.baueRecord f0 f1 f2 f3 f4) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_liesRecordFeld (f0 : _) (f1 : _) (f2 : _) (f3 : _) (f4 : _) :
    befehlVonCode (befehlZuCode (.liesRecordFeld f0 f1 f2 f3 f4)) = some (.liesRecordFeld f0 f1 f2 f3 f4) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_setzeRecordFeld (f0 : _) (f1 : _) (f2 : _) (f3 : _) (f4 : _) (f5 : _) :
    befehlVonCode (befehlZuCode (.setzeRecordFeld f0 f1 f2 f3 f4 f5)) = some (.setzeRecordFeld f0 f1 f2 f3 f4 f5) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_definiereVariante (f0 : _) (f1 : _) (f2 : _) :
    befehlVonCode (befehlZuCode (.definiereVariante f0 f1 f2)) = some (.definiereVariante f0 f1 f2) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_baueVariante (f0 : _) (f1 : _) (f2 : _) (f3 : _) (f4 : _) :
    befehlVonCode (befehlZuCode (.baueVariante f0 f1 f2 f3 f4)) = some (.baueVariante f0 f1 f2 f3 f4) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_waehleVariante (f0 : _) (f1 : _) (f2 : _) (f3 : _) (f4 : _) :
    befehlVonCode (befehlZuCode (.waehleVariante f0 f1 f2 f3 f4)) = some (.waehleVariante f0 f1 f2 f3 f4) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_textLiteral (f0 : _) (f1 : _) :
    befehlVonCode (befehlZuCode (.textLiteral f0 f1)) = some (.textLiteral f0 f1) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_textConcat (f0 : _) (f1 : _) (f2 : _) :
    befehlVonCode (befehlZuCode (.textConcat f0 f1 f2)) = some (.textConcat f0 f1 f2) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_textIndex (f0 : _) (f1 : _) :
    befehlVonCode (befehlZuCode (.textIndex f0 f1)) = some (.textIndex f0 f1) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_substring (f0 : _) (f1 : _) :
    befehlVonCode (befehlZuCode (.substring f0 f1)) = some (.substring f0 f1) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_textLength (f0 : _) (f1 : _) :
    befehlVonCode (befehlZuCode (.textLength f0 f1)) = some (.textLength f0 f1) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_definiereTraeger (f0 : _) (f1 : _) (f2 : _) (f3 : _) :
    befehlVonCode (befehlZuCode (.definiereTraeger f0 f1 f2 f3)) = some (.definiereTraeger f0 f1 f2 f3) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_optionIstBesetzt (f0 : _) (f1 : _) :
    befehlVonCode (befehlZuCode (.optionIstBesetzt f0 f1)) = some (.optionIstBesetzt f0 f1) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_definiereEffektgruppe (f0 : _) :
    befehlVonCode (befehlZuCode (.definiereEffektgruppe f0)) = some (.definiereEffektgruppe f0) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_waehleUmgebung (f0 : _) (f1 : _) (f2 : _) :
    befehlVonCode (befehlZuCode (.waehleUmgebung f0 f1 f2)) = some (.waehleUmgebung f0 f1 f2) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_bindeRegion (f0 : _) (f1 : _) :
    befehlVonCode (befehlZuCode (.bindeRegion f0 f1)) = some (.bindeRegion f0 f1) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem inv_zugriff (f0 : _) :
    befehlVonCode (befehlZuCode (.zugriff f0)) = some (.zugriff f0) := by
  simp_all [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode,
    codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

theorem befehlCode_ofCode : ∀ b : Befehl, befehlVonCode (befehlZuCode b) = some b
  | .literal f0 f1 => inv_literal f0 f1
  | .binaer f0 f1 => inv_binaer f0 f1
  | .binden f0 f1 => inv_binden f0 f1
  | .wahrheitswert f0 f1 => inv_wahrheitswert f0 f1
  | .lesen f0 f1 => inv_lesen f0 f1
  | .negativ f0 f1 => inv_negativ f0 f1
  | .negieren f0 => inv_negieren f0
  | .verneinen f0 => inv_verneinen f0
  | .teilen f0 => inv_teilen f0
  | .vergleichen f0 f1 => inv_vergleichen f0 f1
  | .springeWenn f0 f1 f2 => inv_springeWenn f0 f1 f2
  | .zuweisen f0 f1 f2 => inv_zuweisen f0 f1 f2
  | .zurueck f0 f1 => inv_zurueck f0 f1
  | .springe f0 => inv_springe f0
  | .blockEnde f0 => inv_blockEnde f0
  | .bindeWert f0 f1 f2 => inv_bindeWert f0 f1 f2
  | .definiere f0 f1 f2 f3 f4 f5 f6 f7 => inv_definiere f0 f1 f2 f3 f4 f5 f6 f7
  | .rufe f0 f1 f2 => inv_rufe f0 f1 f2
  | .rueckVoid => inv_rueckVoid
  | .pruefeMass f0 => inv_pruefeMass f0
  | .setzePasszahl f0 f1 => inv_setzePasszahl f0 f1
  | .whileTest f0 f1 f2 => inv_whileTest f0 f1 f2
  | .forAnfang f0 f1 f2 f3 f4 f5 => inv_forAnfang f0 f1 f2 f3 f4 f5
  | .forTest f0 f1 => inv_forTest f0 f1
  | .forNaechster f0 f1 => inv_forNaechster f0 f1
  | .zurueckSprung f0 => inv_zurueckSprung f0
  | .starte f0 => inv_starte f0
  | .ende => inv_ende
  | .baueArray f0 f1 f2 => inv_baueArray f0 f1 f2
  | .liesArray f0 f1 f2 => inv_liesArray f0 f1 f2
  | .baueTupel f0 f1 => inv_baueTupel f0 f1
  | .liesTupelfeld f0 f1 f2 => inv_liesTupelfeld f0 f1 f2
  | .bindeTupel f0 f1 f2 => inv_bindeTupel f0 f1 f2
  | .definiereRecord f0 f1 f2 => inv_definiereRecord f0 f1 f2
  | .baueRecord f0 f1 f2 f3 f4 => inv_baueRecord f0 f1 f2 f3 f4
  | .liesRecordFeld f0 f1 f2 f3 f4 => inv_liesRecordFeld f0 f1 f2 f3 f4
  | .setzeRecordFeld f0 f1 f2 f3 f4 f5 => inv_setzeRecordFeld f0 f1 f2 f3 f4 f5
  | .definiereVariante f0 f1 f2 => inv_definiereVariante f0 f1 f2
  | .baueVariante f0 f1 f2 f3 f4 => inv_baueVariante f0 f1 f2 f3 f4
  | .waehleVariante f0 f1 f2 f3 f4 => inv_waehleVariante f0 f1 f2 f3 f4
  | .textLiteral f0 f1 => inv_textLiteral f0 f1
  | .textConcat f0 f1 f2 => inv_textConcat f0 f1 f2
  | .textIndex f0 f1 => inv_textIndex f0 f1
  | .substring f0 f1 => inv_substring f0 f1
  | .textLength f0 f1 => inv_textLength f0 f1
  | .definiereTraeger f0 f1 f2 f3 => inv_definiereTraeger f0 f1 f2 f3
  | .optionIstBesetzt f0 f1 => inv_optionIstBesetzt f0 f1
  | .definiereEffektgruppe f0 => inv_definiereEffektgruppe f0
  | .waehleUmgebung f0 f1 f2 => inv_waehleUmgebung f0 f1 f2
  | .bindeRegion f0 f1 => inv_bindeRegion f0 f1
  | .zugriff f0 => inv_zugriff f0

instance : Encodable Befehl :=
  Encodable.ofLeftInjection
    (fun b => Encodable.encode (befehlZuCode b))
    (fun n => (Encodable.decode n).bind befehlVonCode)
    (by intro b; simp_all [Encodable.encodek, befehlCode_ofCode])

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation
