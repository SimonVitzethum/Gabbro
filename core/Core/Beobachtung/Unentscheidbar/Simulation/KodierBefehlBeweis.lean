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
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .binaer f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .binden f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .wahrheitswert f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .lesen f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .negativ f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .negieren f0 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .verneinen f0 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .teilen f0 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .vergleichen f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .springeWenn f0 f1 f2 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .zuweisen f0 f1 f2 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .zurueck f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .springe f0 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .blockEnde f0 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .bindeWert f0 f1 f2 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .definiere f0 f1 f2 f3 f4 f5 f6 f7 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .rufe f0 f1 f2 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .rueckVoid => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .pruefeMass f0 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .setzePasszahl f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .whileTest f0 f1 f2 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .forAnfang f0 f1 f2 f3 f4 f5 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .forTest f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .forNaechster f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .zurueckSprung f0 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .starte f0 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .ende => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .baueArray f0 f1 f2 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .liesArray f0 f1 f2 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .baueTupel f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .liesTupelfeld f0 f1 f2 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .bindeTupel f0 f1 f2 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .definiereRecord f0 f1 f2 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .baueRecord f0 f1 f2 f3 f4 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .liesRecordFeld f0 f1 f2 f3 f4 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .setzeRecordFeld f0 f1 f2 f3 f4 f5 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .definiereVariante f0 f1 f2 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .baueVariante f0 f1 f2 f3 f4 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .waehleVariante f0 f1 f2 f3 f4 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .textLiteral f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .textConcat f0 f1 f2 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .textIndex f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .substring f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .textLength f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .definiereTraeger f0 f1 f2 f3 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .optionIstBesetzt f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .definiereEffektgruppe f0 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .waehleUmgebung f0 f1 f2 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .bindeRegion f0 f1 => by
      simp only [befehlVonCode, befehlVonCodeA, befehlVonCodeB, befehlZuCode, natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, intRueck, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]

instance : Encodable Befehl :=
  Encodable.ofLeftInjection
    (fun b => Encodable.encode (befehlZuCode b))
    (fun n => (Encodable.decode n).bind befehlVonCode)
    (by intro b; simp only [Encodable.encodek, befehlCode_ofCode, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one])

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation

