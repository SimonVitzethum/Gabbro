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


/-! ## The command code is inverse -/

theorem befehlCode_ofCode : ∀ b : Befehl, befehlVonCode (befehlZuCode b) = some b
  | .literal f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .binaer f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .binden f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .wahrheitswert f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .lesen f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .negativ f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .negieren f0 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .verneinen f0 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .teilen f0 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .vergleichen f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .springeWenn f0 f1 f2 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .zuweisen f0 f1 f2 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .zurueck f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .springe f0 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .blockEnde f0 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .bindeWert f0 f1 f2 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .definiere f0 f1 f2 f3 f4 f5 f6 f7 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .rufe f0 f1 f2 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .rueckVoid => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .pruefeMass f0 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .setzePasszahl f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .whileTest f0 f1 f2 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .forAnfang f0 f1 f2 f3 f4 f5 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .forTest f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .forNaechster f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .zurueckSprung f0 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .starte f0 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .ende => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .baueArray f0 f1 f2 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .liesArray f0 f1 f2 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .baueTupel f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .liesTupelfeld f0 f1 f2 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .bindeTupel f0 f1 f2 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .definiereRecord f0 f1 f2 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .baueRecord f0 f1 f2 f3 f4 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .liesRecordFeld f0 f1 f2 f3 f4 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .setzeRecordFeld f0 f1 f2 f3 f4 f5 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .definiereVariante f0 f1 f2 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .baueVariante f0 f1 f2 f3 f4 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .waehleVariante f0 f1 f2 f3 f4 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .textLiteral f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .textConcat f0 f1 f2 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .textIndex f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .substring f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .textLength f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .definiereTraeger f0 f1 f2 f3 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .optionIstBesetzt f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .definiereEffektgruppe f0 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .waehleUmgebung f0 f1 f2 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]
  | .bindeRegion f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck]

instance : Encodable Befehl :=
  Encodable.ofLeftInjection
    (fun b => Encodable.encode (befehlZuCode b))
    (fun n => (Encodable.decode n).bind befehlVonCode)
    (by intro b; simp only [Encodable.encodek, befehlCode_ofCode])

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation

