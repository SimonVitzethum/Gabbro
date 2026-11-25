module

public import Core.Beobachtung.Fluss.Beschriftung.Sprung
public import Core.Beobachtung.Fluss.Beschriftung.AufgabenBeweise
public import Core.Beobachtung.Fluss.Beschriftung.AufrufSchleifeBeweise
public import Core.Beobachtung.Fluss.Beschriftung.Beweise.AggregatBeweise
public import Core.Beobachtung.Fluss.Beschriftung.Beweise.VarianteBeweise
public import Core.Beobachtung.Fluss.Beschriftung.Beweise.TextBeweise
public import Core.Beobachtung.Fluss.Beschriftung.Offen.Ruf
public import Core.Beobachtung.Fluss.Beschriftung.Offen.Schleife
public import Core.Beobachtung.Fluss.Beschriftung.Offen.Aggregat
public import Core.Beobachtung.Fluss.Beschriftung.Offen.VarianteText
public import Core.Beobachtung.Fluss.Beschriftung.Offen.Kontrollfluss
public import Core.Ast.Semantik.Runtime.Unterbrechung.Beweise

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Beobachtung

/-- The label rule of an instruction at `pc`: the checker's decision for that instruction.
    Every instruction has a pinned, proved sight statement, so every instruction gets its
    precise rule here from the premises of that statement. -/
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
  | .zurueck quelle _ =>
    oeffentlich (β.temp pc quelle) = true ∧
    (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) ∧
    (∀ i, oeffentlich (β.lokal (pc + 1) i) = true → oeffentlich (β.lokal pc i) = true)
  | .rufe _ _ _ =>
    (∀ s, oeffentlich (β.temp pc s) = true) ∧
    (∀ i, oeffentlich (β.lokal pc i) = true)
  | .rueckVoid =>
    (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) ∧
    (∀ i, oeffentlich (β.lokal (pc + 1) i) = true → oeffentlich (β.lokal pc i) = true)
  | .pruefeMass quelle =>
    oeffentlich (β.temp pc quelle) = true ∧
    (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) ∧
    (∀ i, oeffentlich (β.lokal (pc + 1) i) = true → oeffentlich (β.lokal pc i) = true)
  | .whileTest quelle exitPunkt _ =>
    oeffentlich (β.temp pc quelle) = true ∧
    ∀ q, q = pc + 1 ∨ q = pc + exitPunkt →
      (∀ s, oeffentlich (β.temp q s) = true → oeffentlich (β.temp pc s) = true) ∧
      (∀ i, oeffentlich (β.lokal q i) = true → oeffentlich (β.lokal pc i) = true)
  | .forAnfang unter ober _ skipEmpty _ _ =>
    oeffentlich (β.temp pc unter) = true ∧
    oeffentlich (β.temp pc ober) = true ∧
    (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) ∧
    (∀ i, oeffentlich (β.lokal (pc + 1) (i + 1)) = true → oeffentlich (β.lokal pc i) = true) ∧
    (oeffentlich (β.lokal (pc + 1) 0) = true → oeffentlich (β.temp pc unter) = true) ∧
    (∀ s, oeffentlich (β.temp (pc + skipEmpty) s) = true → oeffentlich (β.temp pc s) = true) ∧
    (∀ i, oeffentlich (β.lokal (pc + skipEmpty) i) = true → oeffentlich (β.lokal pc i) = true)
  | .forTest exitPunkt _ =>
    oeffentlich (β.lokal pc 0) = true ∧
    ∀ q, q = pc + 1 ∨ q = pc + exitPunkt →
      (∀ s, oeffentlich (β.temp q s) = true → oeffentlich (β.temp pc s) = true) ∧
      (∀ i, oeffentlich (β.lokal q i) = true → oeffentlich (β.lokal pc i) = true)
  | .forNaechster rueckAbstand _ =>
    oeffentlich (β.lokal pc 0) = true ∧
    (∀ s, oeffentlich (β.temp (pc - rueckAbstand) s) = true →
      oeffentlich (β.temp pc s) = true) ∧
    (∀ i, i ≠ 0 → oeffentlich (β.lokal (pc - rueckAbstand) i) = true →
      oeffentlich (β.lokal pc i) = true) ∧
    (oeffentlich (β.lokal (pc - rueckAbstand) 0) = true →
      oeffentlich (β.lokal pc 0) = true)
  | .starte _ => ∀ s, oeffentlich (β.temp pc s) = true
  | .ende => oeffentlich β.ergebnis = true → oeffentlich (β.lokal pc 0) = true
  | .baueArray ziel _ count => β.SchreibRegel pc ziel (tempBereich ziel count)
  | .baueTupel ziel types => β.SchreibRegel pc ziel (tempBereich ziel types.length)
  | .bindeTupel quelle types bind =>
    (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) ∧
    oeffentlich (β.temp pc quelle) = true ∧
    (∀ i, oeffentlich (β.lokal (pc + 1) i) = true → oeffentlich (β.lokal pc i) = true) ∧
    (∀ i, oeffentlich (β.lokal (pc + 1) (i + behalteneTupel types bind)) = true →
      oeffentlich (β.lokal pc i) = true)
  | .baueRecord ziel _ _ _ sources => β.SchreibRegel pc ziel (sources.map Komp.temp)
  | .setzeRecordFeld source indexLocal _ _ _ _ =>
    (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) ∧
    (∀ j, j ≠ indexLocal → oeffentlich (β.lokal (pc + 1) j) = true →
      oeffentlich (β.lokal pc j) = true) ∧
    (oeffentlich (β.lokal (pc + 1) indexLocal) = true → oeffentlich (β.temp pc source) = true) ∧
    (oeffentlich (β.lokal (pc + 1) indexLocal) = true → oeffentlich (β.lokal pc indexLocal) = true)
  | .waehleVariante source _ _ _ branches =>
    oeffentlich (β.temp pc source) = true ∧
    ∀ b ∈ branches,
      (∀ s, oeffentlich (β.temp (pc + b.1) s) = true → oeffentlich (β.temp pc s) = true) ∧
      (∀ i, oeffentlich (β.lokal (pc + b.1) (i + (if b.2 then 1 else 0))) = true →
        oeffentlich (β.lokal pc i) = true) ∧
      (b.2 = true → oeffentlich (β.lokal (pc + b.1) 0) = true →
        oeffentlich (β.temp pc source) = true)
  | .textIndex basis _ =>
    oeffentlich (β.temp pc basis) = true ∧
    oeffentlich (β.temp pc (basis + 1)) = true ∧
    (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) ∧
    (∀ i, oeffentlich (β.lokal (pc + 1) i) = true → oeffentlich (β.lokal pc i) = true)
  | .substring basis _ =>
    oeffentlich (β.temp pc basis) = true ∧
    oeffentlich (β.temp pc (basis + 1)) = true ∧
    oeffentlich (β.temp pc (basis + 2)) = true ∧
    (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) ∧
    (∀ i, oeffentlich (β.lokal (pc + 1) i) = true → oeffentlich (β.lokal pc i) = true)
  | .bindeRegion _ _ =>
    (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) ∧
    (∀ i, oeffentlich (β.lokal pc i) = true)
  | .maskiere .. | .prioritaet .. | .sendeUnterbrechung .. | .leiteLeitung .. =>
    (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) ∧
    (∀ i, oeffentlich (β.lokal (pc + 1) i) = true → oeffentlich (β.lokal pc i) = true)
  -- An access instruction has no label rule yet: the label rule of a memory event is MK-13, and a form the
  -- model has no rule for is refused (AGENTS.md §2), so the labelled flow rule is never accepted for it.
  | .zugriff _ => False
  -- A lifecycle instruction has no label rule either (thread creation is labelled in MK-13), so it is refused.
  | .faden _ => False

theorem Befehl.sichtErhaltend_oeffentlich {pc : Nat} (f : Befehl) :
    f.SichtErhaltendBei Beschriftung.alleOeffentlich pc := by
  intro r₁ r₂ live _ h
  rw [sicht_alleOeffentlich, sicht_alleOeffentlich] at h
  rw [sicht_alleOeffentlich, sicht_alleOeffentlich, h]

/-- An instruction the labelled flow rule accepts is frame-only: an access instruction has no label rule. -/
theorem Befehl.FlussRegel.privat {β : Beschriftung} {pc : Nat} {f : Befehl} (regel : f.FlussRegel β pc) :
    f.Privat := by
  cases f <;> first
    | exact Or.inl rfl
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr (Or.inl rfl))
    | exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    | exact False.elim regel

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
  | zurueck quelle zieltyp =>
    exact zurueckSicht β pc quelle zieltyp regel.1 regel.2.1 regel.2.2
  | rufe name args bind => exact rufeSicht β pc name args bind regel.1 regel.2
  | rueckVoid => exact rueckVoidSicht β pc regel.1 regel.2
  | pruefeMass quelle => exact pruefeMassSicht β pc quelle regel.1 regel.2.1 regel.2.2
  | whileTest quelle exitPunkt handler =>
    exact whileTestSicht β pc quelle exitPunkt handler regel.1 regel.2
  | forAnfang unter ober index skipEmpty shadowed missingHandler =>
    exact forAnfangSicht β pc unter ober index skipEmpty shadowed missingHandler
      regel.1 regel.2.1 regel.2.2.1 regel.2.2.2.1 regel.2.2.2.2.1 regel.2.2.2.2.2.1
      regel.2.2.2.2.2.2
  | forTest exitPunkt handler =>
    exact forTestSicht β pc exitPunkt handler regel.1 regel.2
  | forNaechster rueckAbstand index =>
    exact forNaechsterSicht β pc rueckAbstand index regel.1 regel.2.1 regel.2.2.1 regel.2.2.2
  | starte name => exact starteSicht β pc name regel
  | ende => exact endeSicht β pc regel
  | baueArray ziel element count => exact baueArraySicht β pc ziel element count regel
  | baueTupel ziel types => exact baueTupelSicht β pc ziel types regel
  | bindeTupel quelle types bind =>
    exact bindeTupelSicht β pc quelle types bind regel.1 regel.2.1 regel.2.2.1 regel.2.2.2
  | baueRecord ziel name labels types sources =>
    exact baueRecordSicht β pc ziel name labels types sources regel
  | setzeRecordFeld source indexLocal name labels types index =>
    exact setzeRecordFeldSicht β pc source indexLocal name labels types index
      regel.1 regel.2.1 regel.2.2.1 regel.2.2.2
  | waehleVariante source name labels cases branches =>
    exact waehleVarianteSicht β pc source name labels cases branches regel.1 regel.2
  | textIndex basis capacity =>
    exact textIndexSicht β pc basis capacity regel.1 regel.2.1 regel.2.2.1 regel.2.2.2
  | substring basis capacity =>
    exact substringSicht β pc basis capacity regel.1 regel.2.1 regel.2.2.1 regel.2.2.2.1
      regel.2.2.2.2
  | bindeRegion receiver init => exact bindeRegionSicht β pc receiver init regel.1 regel.2
  | maskiere vektor aus => exact maskiereSicht β pc vektor aus regel.1 regel.2
  | prioritaet grenze => exact prioritaetSicht β pc grenze regel.1 regel.2
  | sendeUnterbrechung vektor kern =>
    exact sendeUnterbrechungSicht β pc vektor kern regel.1 regel.2
  | leiteLeitung leitung kern prioritaet =>
    exact leiteLeitungSicht β pc leitung kern prioritaet regel.1 regel.2
  | zugriff form => exact False.elim regel
  | faden form => exact False.elim regel

/-- Per instruction family: the rule is sound for every declaration. -/
def FamilienSicht (familie : LokalFamilie) : Prop :=
  ∀ (β : Beschriftung) (pc : Nat) (f : Befehl), f.familie = familie →
    f.FlussRegel β pc → f.SichtErhaltendBei β pc

theorem familienSicht (familie : LokalFamilie) : FamilienSicht familie :=
  fun _ _ f _ regel => f.sichtErhaltend regel

/-- A fragment is accepted at the labelled flow rule when each instruction's rule holds at each
    position where it stands. -/
def Fragment.FlussAkzeptiert (p : Fragment) (β : Beschriftung) : Prop :=
  ∀ (pc : Nat) (f : Befehl), p.code[pc]? = some f → f.FlussRegel β pc

theorem Fragment.flussAkzeptiert_lokal (p : Fragment) (platform : Katalog.Plattform) (β : Beschriftung)
    (h : p.FlussAkzeptiert β) : FlussLokal (p.beschriftet platform β) :=
  p.beschriftet_fluss_lokal platform β
    (fun f hf => by
      obtain ⟨pc, hpc⟩ := List.mem_iff_getElem?.mp hf
      exact (h pc f hpc).privat)
    fun pc f hf => f.sichtErhaltend (h pc f hf)

end Gabbro.Core.Ast.Semantik
