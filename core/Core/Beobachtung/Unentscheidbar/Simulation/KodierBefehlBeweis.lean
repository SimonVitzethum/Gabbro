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
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .binaer f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .binden f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .wahrheitswert f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .lesen f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .negativ f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .negieren f0 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .verneinen f0 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .teilen f0 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .vergleichen f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .springeWenn f0 f1 f2 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .zuweisen f0 f1 f2 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .zurueck f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .springe f0 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .blockEnde f0 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .bindeWert f0 f1 f2 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .definiere f0 f1 f2 f3 f4 f5 f6 f7 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .rufe f0 f1 f2 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .rueckVoid => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .pruefeMass f0 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .setzePasszahl f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .whileTest f0 f1 f2 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .forAnfang f0 f1 f2 f3 f4 f5 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .forTest f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .forNaechster f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .zurueckSprung f0 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .starte f0 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .ende => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .baueArray f0 f1 f2 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .liesArray f0 f1 f2 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .baueTupel f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .liesTupelfeld f0 f1 f2 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .bindeTupel f0 f1 f2 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .definiereRecord f0 f1 f2 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .baueRecord f0 f1 f2 f3 f4 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .liesRecordFeld f0 f1 f2 f3 f4 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .setzeRecordFeld f0 f1 f2 f3 f4 f5 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .definiereVariante f0 f1 f2 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .baueVariante f0 f1 f2 f3 f4 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .waehleVariante f0 f1 f2 f3 f4 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .textLiteral f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .textConcat f0 f1 f2 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .textIndex f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .substring f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .textLength f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .definiereTraeger f0 f1 f2 f3 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .optionIstBesetzt f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .definiereEffektgruppe f0 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .waehleUmgebung f0 f1 f2 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]
  | .bindeRegion f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.bind_some]

instance : Encodable Befehl :=
  Encodable.ofLeftInjection
    (fun b => Encodable.encode (befehlZuCode b))
    (fun n => (Encodable.decode n).bind befehlVonCode)
    (by intro b; simp only [Encodable.encodek, befehlCode_ofCode, Option.bind_some])

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation

