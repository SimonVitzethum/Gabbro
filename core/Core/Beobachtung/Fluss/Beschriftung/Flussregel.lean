module

public import Core.Beobachtung.Fluss.Beschriftung.Sprung
public import Core.Beobachtung.Fluss.Beschriftung.AufgabenBeweise
public import Core.Beobachtung.Fluss.Beschriftung.AufrufSchleifeBeweise
public import Core.Beobachtung.Fluss.Beschriftung.AggregatBeweise
public import Core.Beobachtung.Fluss.Beschriftung.VarianteBeweise
public import Core.Beobachtung.Fluss.Beschriftung.TextBeweise

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Beobachtung

/-- The label rule of an instruction at `pc`: the checker's decision for that instruction.
    Instructions without a precise rule are accepted only under the all-public declaration;
    a labelled unit using them is refused, never accepted on an unproved rule. -/
def Befehl.FlussRegel (β : Beschriftung) (pc : Nat) : Befehl → Prop
  | .literal dst _ => β.SchreibRegel pc dst []
  | .wahrheitswert dst _ => β.SchreibRegel pc dst []
  | .negativ dst _ => β.SchreibRegel pc dst []
  | .lesen dst index => β.SchreibRegel pc dst [.lokal index]
  | .negieren dst => β.SchreibRegel pc dst [.temp dst]
  | .verneinen dst => β.SchreibRegel pc dst [.temp dst]
  | .binaer _ left => β.SchreibRegel pc left [.temp left, .temp (left + 1)]
  | .teilen left => β.SchreibRegel pc left [.temp left, .temp (left + 1)]
  | .vergleichen _ left => β.SchreibRegel pc left [.temp left, .temp (left + 1)]
  | .springe abstand =>
    (∀ s, oeffentlich (β.temp (pc + abstand) s) = true → oeffentlich (β.temp pc s) = true) ∧
    (∀ i, oeffentlich (β.lokal (pc + abstand) i) = true → oeffentlich (β.lokal pc i) = true)
  | .springeWenn quelle _ abstand =>
    oeffentlich (β.temp pc quelle) = true ∧
    ∀ q, q = pc + 1 ∨ q = pc + abstand →
      (∀ s, oeffentlich (β.temp q s) = true → oeffentlich (β.temp pc s) = true) ∧
      (∀ i, oeffentlich (β.lokal q i) = true → oeffentlich (β.lokal pc i) = true)
  | .zuweisen quelle index _ =>
    (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) ∧
    (∀ i, i ≠ index → oeffentlich (β.lokal (pc + 1) i) = true →
      oeffentlich (β.lokal pc i) = true) ∧
    (oeffentlich (β.lokal (pc + 1) index) = true → oeffentlich (β.temp pc quelle) = true)
  | .binden _ quelle =>
    (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) ∧
    (∀ i, oeffentlich (β.lokal (pc + 1) (i + 1)) = true → oeffentlich (β.lokal pc i) = true) ∧
    (oeffentlich (β.lokal (pc + 1) 0) = true → oeffentlich (β.temp pc quelle) = true)
  | .bindeWert quelle _ global =>
    (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) ∧
    (∀ i, oeffentlich (β.lokal (pc + 1) (i + 1)) = true → oeffentlich (β.lokal pc i) = true) ∧
    (oeffentlich (β.lokal (pc + 1) 0) = true → oeffentlich (β.temp pc quelle) = true) ∧
    (global = true → oeffentlich (β.temp pc quelle) = true)
  | .blockEnde count =>
    (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) ∧
    (∀ i, oeffentlich (β.lokal (pc + 1) i) = true → oeffentlich (β.lokal pc (i + count)) = true)
  | .definiere _ _ _ _ skip _ _ _ =>
    (∀ s, oeffentlich (β.temp (pc + skip) s) = true → oeffentlich (β.temp pc s) = true) ∧
    (∀ i, oeffentlich (β.lokal (pc + skip) i) = true → oeffentlich (β.lokal pc i) = true)
  | .zurueckSprung abstand =>
    (∀ s, oeffentlich (β.temp (pc - abstand) s) = true → oeffentlich (β.temp pc s) = true) ∧
    (∀ i, oeffentlich (β.lokal (pc - abstand) i) = true → oeffentlich (β.lokal pc i) = true)
  | .setzePasszahl quelle _ =>
    oeffentlich (β.temp pc quelle) = true ∧
    (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) ∧
    (∀ i, oeffentlich (β.lokal (pc + 1) i) = true → oeffentlich (β.lokal pc i) = true)
  | .liesArray basis _ _ => β.SchreibRegel pc basis [.temp basis, .temp (basis + 1)]
  | .liesTupelfeld basis _ _ => β.SchreibRegel pc basis [.temp basis]
  | .liesRecordFeld basis _ _ _ _ => β.SchreibRegel pc basis [.temp basis]
  | .definiereRecord _ _ _ =>
    (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) ∧
    (∀ i, oeffentlich (β.lokal (pc + 1) (i + 1)) = true → oeffentlich (β.lokal pc i) = true)
  | .baueVariante ziel _ _ _ _ => β.SchreibRegel pc ziel [.temp ziel]
  | .optionIstBesetzt ziel _ => β.SchreibRegel pc ziel [.temp ziel]
  | .definiereVariante _ _ _ =>
    (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) ∧
    (∀ i, oeffentlich (β.lokal (pc + 1) (i + 1)) = true → oeffentlich (β.lokal pc i) = true)
  | .definiereTraeger _ _ _ _ =>
    (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) ∧
    (∀ i, oeffentlich (β.lokal (pc + 1) (i + 1)) = true → oeffentlich (β.lokal pc i) = true)
  | .definiereEffektgruppe _ =>
    (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) ∧
    (∀ i, oeffentlich (β.lokal (pc + 1) (i + 1)) = true → oeffentlich (β.lokal pc i) = true)
  | .waehleUmgebung _ _ _ =>
    (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) ∧
    (∀ i, oeffentlich (β.lokal (pc + 1) i) = true → oeffentlich (β.lokal pc i) = true)
  | .textLiteral ziel _ => β.SchreibRegel pc ziel []
  | .textConcat basis _ _ => β.SchreibRegel pc basis [.temp basis, .temp (basis + 1)]
  | .textLength basis _ => β.SchreibRegel pc basis [.temp basis]
  | _ => β = Beschriftung.alleOeffentlich

theorem Befehl.sichtErhaltend_oeffentlich {pc : Nat} (f : Befehl) :
    f.SichtErhaltendBei Beschriftung.alleOeffentlich pc := by
  intro r₁ r₂ live _ h
  rw [sicht_alleOeffentlich, sicht_alleOeffentlich] at h
  rw [sicht_alleOeffentlich, sicht_alleOeffentlich, h]

/-- **Soundness of the checker's flow rule, instruction by instruction.** -/
theorem Befehl.sichtErhaltend {β : Beschriftung} {pc : Nat} (f : Befehl)
    (regel : f.FlussRegel β pc) : f.SichtErhaltendBei β pc := by
  cases f with
  | literal dst val => exact Befehl.sichtErhaltend_schreibform (schreibform_literal dst val) regel
  | wahrheitswert dst value =>
    exact Befehl.sichtErhaltend_schreibform (schreibform_wahrheitswert dst value) regel
  | negativ dst magnitude =>
    exact Befehl.sichtErhaltend_schreibform (schreibform_negativ dst magnitude) regel
  | lesen dst index => exact Befehl.sichtErhaltend_schreibform (schreibform_lesen dst index) regel
  | negieren dst => exact Befehl.sichtErhaltend_schreibform (schreibform_negieren dst) regel
  | verneinen dst => exact Befehl.sichtErhaltend_schreibform (schreibform_verneinen dst) regel
  | binaer op left => exact Befehl.sichtErhaltend_schreibform (schreibform_binaer op left) regel
  | teilen left => exact Befehl.sichtErhaltend_schreibform (schreibform_teilen left) regel
  | vergleichen op left =>
    exact Befehl.sichtErhaltend_schreibform (schreibform_vergleichen op left) regel
  | springe abstand => exact springeSicht β pc abstand regel.1 regel.2
  | springeWenn quelle bei abstand => exact springeWennSicht β pc quelle abstand bei regel.1 regel.2
  | zuweisen quelle index zieltyp =>
    exact zuweisenSicht β pc quelle index zieltyp regel.1 regel.2.1 regel.2.2
  | binden name quelle => exact bindenSicht β pc name quelle regel.1 regel.2.1 regel.2.2
  | bindeWert quelle ziel global =>
    exact bindeWertSicht β pc quelle ziel global regel.1 regel.2.1 regel.2.2.1 regel.2.2.2
  | blockEnde count => exact blockEndeSicht β pc count regel.1 regel.2
  | definiere name ps res glob skip meas calls effs =>
    exact definiereSicht β pc name ps res glob skip meas calls effs regel.1 regel.2
  | zurueckSprung abstand => exact zurueckSprungSicht β pc abstand regel.1 regel.2
  | setzePasszahl quelle stelle =>
    exact setzePasszahlSicht β pc quelle stelle regel.1 regel.2.1 regel.2.2
  | liesArray basis element count =>
    exact liesArraySicht β pc basis element count regel
  | liesTupelfeld basis types index =>
    exact liesTupelfeldSicht β pc basis types index regel
  | liesRecordFeld basis name labels types index =>
    exact liesRecordFeldSicht β pc basis name labels types index regel
  | definiereRecord name labels types =>
    exact definiereRecordSicht β pc name labels types regel.1 regel.2
  | baueVariante ziel name labels cases index =>
    exact baueVarianteSicht β pc ziel name labels cases index regel
  | optionIstBesetzt ziel count => exact optionIstBesetztSicht β pc ziel count regel
  | definiereVariante name labels cases =>
    exact definiereVarianteSicht β pc name labels cases regel.1 regel.2
  | definiereTraeger count labels layout exported =>
    exact definiereTraegerSicht β pc count labels layout exported regel.1 regel.2
  | definiereEffektgruppe effects =>
    exact definiereEffektgruppeSicht β pc effects regel.1 regel.2
  | waehleUmgebung name abi row =>
    exact waehleUmgebungSicht β pc name abi row regel.1 regel.2
  | textLiteral ziel decoded => exact textLiteralSicht β pc ziel decoded regel
  | textConcat basis a b => exact textConcatSicht β pc basis a b regel
  | textLength basis capacity => exact textLengthSicht β pc basis capacity regel
  | _ =>
    have gleich : β = Beschriftung.alleOeffentlich := regel
    rw [gleich]
    exact Befehl.sichtErhaltend_oeffentlich _

/-- Per instruction family: the rule is sound for every declaration. -/
def FamilienSicht (familie : SimFamilie) : Prop :=
  ∀ (β : Beschriftung) (pc : Nat) (f : Befehl), f.simFamilie = familie →
    f.FlussRegel β pc → f.SichtErhaltendBei β pc

theorem familienSicht (familie : SimFamilie) : FamilienSicht familie :=
  fun _ _ f _ regel => f.sichtErhaltend regel

/-- A fragment is accepted at the labelled flow rule when each instruction's rule holds at each
    position where it stands. -/
def Fragment.FlussAkzeptiert (p : Fragment) (β : Beschriftung) : Prop :=
  ∀ (pc : Nat) (f : Befehl), p.code[pc]? = some f → f.FlussRegel β pc

theorem Fragment.flussAkzeptiert_lokal (p : Fragment) (platform : Katalog.Plattform) (β : Beschriftung)
    (h : p.FlussAkzeptiert β) : FlussLokal (p.beschriftet platform β) :=
  p.beschriftet_fluss_lokal platform β fun pc f hf => f.sichtErhaltend (h pc f hf)

end Gabbro.Core.Ast.Semantik
