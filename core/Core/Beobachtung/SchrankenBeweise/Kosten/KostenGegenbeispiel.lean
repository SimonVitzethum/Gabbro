/-
  File:      core/Core/Beobachtung/SchrankenBeweise/Kosten/KostenGegenbeispiel.lean
  Subject:   A NONZERO MEASURE AND AN UNDERESTIMATED ENTRY SEGMENT.
              The accepted unit installs mass six in the singleton interval [6,6].
              The elaborated measure prologue contributes two private context ticks
              that the structural estimator does not charge.
-/
module

public import Core.Beobachtung.SchrankenBeweise.KostenEndlich
public import Core.Beobachtung.SchrankenBeweise.BindungKosten
public import Core.Ast.LowLevel.Proofs.EnvironmentSatisfiability
public import Core.Ast.Semantik.Runtime.Atom.Rein
public import Core.Sicherheit.Praefix
public import Core.Sicherheit.Laufkonstruktion
public import Core.Katalog.Erfuellbar

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine Annahme
open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Sicherheit

/-- A constant measure at value six: its interval `[6,6]` has width zero. -/
private def kkMass : Measure [] :=
  ⟨6, 6, Expr.lit 6, by omega⟩

/-- A unit whose only function `main` declares `kkMass` and has an empty body. -/
private def kkBaum : Ast.Unit :=
  ⟨_, UnitBody.step
    (Decl.function mainName mainName_direct [] none
      (by intro t mem; cases mem) (some kkMass)
      (BracedBlock.braces Block.done)
      List.nodup_nil (by intro h; cases h) none)
    UnitBody.done⟩

private def kkUnit : UnitMitSchranken := ⟨kkBaum, Schrankendeklaration.leer⟩

/-- Function lookup returns the declared interval. -/
private theorem kk_intervall :
    (findeKern kkBaum.2 mainName).map FunktionsKern.massIntervall = some (some (6, 6)) := by
  rfl

/-- Installing the constant measure writes the absolute value six. -/
private theorem kk_mass_auswertung (frame : Rahmen) (name : Identifier)
    (hf : frame.funktion = some name)
    (hprev : frame.fortsetzungen.find?
      (fun k => (k.funktion.map Subtype.val) == some name.val) = none)
    (h : frame.zahl 0 = some (⟨6, 6, Zahl.literal 6⟩ : Ganzzahl)) :
    ((Befehl.pruefeMass 0).auswerten frame).mass = some 6 := by
  unfold Befehl.auswerten Rahmen.setzeMass
  have hto : Int.toNat (6 : Int) = 6 := by decide
  simp only [hf, hprev, h, Zahl.literal,
    if_neg (by omega : ¬ (6 : Int) < 0), hto]
  rfl

/-- A private step of a program unit at the entry context. -/
private theorem kk_schritt (P : Plattform) (u : UnitMitSchranken) (hw : HwLauf) (t : Nat)
    (s : Zustand) (b : Befehl)
    (normal : (hw.angebot t).crash = false) (bereit : KannSchreiten hw t eintritt s)
    (kopf : (einheitMitSchranken P u).system.kopf s eintritt = some b) (privat : b.Privat) :
    Lauffolge (einheitMitSchranken P u) hw t (some s) (.kontext eintritt (), ⟨[], []⟩)
      (some (b.nach eintritt s)) :=
  .schritt (.kontext normal bereit
    ⟨b, kopf, (b.impl_privat privat eintritt s () [Semantik.plan] (b.nach eintritt s)).2 ⟨rfl, rfl⟩⟩
    (b.vollzug _ t eintritt s))

/-- The plain clause table of the counterexample unit is empty. -/
private theorem kk_klauseln : (programm kkBaum).klauseln = .leer := by
  rfl

/-- Every instruction of the counterexample code is frame-only. -/
private theorem kk_rein : (programm kkBaum).Rein := by
  intro b hb
  cases b <;>
    simp only [programm, unitBody, decl, functionCode, bracedBlock, block, functionInstruction,
      Fragment.anhaengen, Fragment.einzel, Fragment.leer, expr, kkBaum, kkMass, functionScope,
      writtenResult, declaredEffects, List.filterMap, List.map, List.length, List.length_append,
      List.length_cons, List.length_nil, List.nil_append, List.append_nil, List.append_assoc,
      List.filterMap_cons, List.filterMap_nil, List.map_cons, List.map_nil,
      List.mem_append, List.mem_singleton, List.mem_nil_iff, List.mem_cons, List.not_mem_nil,
      Nat.sub_self, Nat.add_zero, or_false, false_or, or_true, true_or, reduceCtorEq,
      Befehl.Privat, Befehl.klasse] at hb ⊢
  all_goals contradiction

/-- No instruction of the counterexample code has a guard. -/
private theorem kk_guard : ∀ b ∈ (programm kkBaum).code, ∀ frame, b.guard frame = none := by
  intro b hb frame
  simp only [programm, unitBody, decl, functionCode, bracedBlock, block, functionInstruction,
    Fragment.anhaengen, Fragment.einzel, Fragment.leer, expr, kkBaum, kkMass, functionScope,
    writtenResult, declaredEffects, List.filterMap, List.map, List.length, List.length_append,
    List.length_cons, List.length_nil, List.nil_append, List.append_nil, List.append_assoc,
    List.filterMap_cons, List.filterMap_nil, List.map_cons, List.map_nil,
    List.mem_append, List.mem_singleton, List.mem_nil_iff, List.mem_cons,
    List.not_mem_nil, Nat.sub_self, Nat.add_zero, or_false, false_or] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

/-- The counterexample unit is accepted by the perfect checker. -/
private theorem kk_akzeptiert : Akzeptiert (einheitMitSchranken Plattform.x86_64 kkUnit) := by
  let p := programm kkBaum
  let E := einheitMitSchranken Plattform.x86_64 kkUnit
  refine ⟨⟨Plattform.x86_64.katalog_wohlgeformt, fun b => Befehl.regelLokal p Plattform.x86_64 b,
    ⟨Aussen.zulassung_m2 _, ?_⟩,
    Beobachtung.fragment_fluss_lokal p Plattform.x86_64 kk_rein, ?_, ?_, ?_⟩, ?_, ?_⟩
  · apply aussen_gueltig_aus_kontext
    intro run t s c w spur next step
    cases step with
    | kontext _ _ rule execute =>
      obtain ⟨b, head, transfer⟩ := rule
      obtain ⟨rfl, rfl⟩ := b.vollzug_genau (w := w) transfer execute
        (kk_rein b (kopf_mem (code := p.code) head))
      exact ⟨⟨fun _ mem => (List.not_mem_nil mem).elim, [], (List.append_nil _).symm,
        fun _ mem => (List.not_mem_nil mem).elim⟩, fun h => h⟩
  · exact schrankenLokal_leer rfl rfl rfl
  · exact Gabbro.Core.Annahme.abschnittWartefrei_ohne_blockade _ fun _ _ _ hb => hb
  · refine ⟨Gabbro.Core.Maschine.eineTabelle_akzeptiert,
      fun s c i hkopf t c' sv u sv' w q spur himpl haus => ?_⟩
    have memb : i ∈ p.code := kopf_mem hkopf
    obtain ⟨rfl, _⟩ := i.vollzug_genau (w := w) himpl haus (kk_rein i memb)
    exact spurRespektiert_leer _ _ _
  · intro run conforms
    change (∀ pred ∈ p.klauseln.voraus, _) ∧
      (∀ _ : I.Schnitt E run, ∀ pred ∈ p.klauseln.invariant, _) ∧
      ∀ _ : I.Schnitt E run, _ → ∀ pred ∈ p.klauseln.sicher, _
    rw [kk_klauseln]
    exact ⟨fun _ h => (List.not_mem_nil h).elim, fun _ _ h => (List.not_mem_nil h).elim,
      fun _ _ _ h => (List.not_mem_nil h).elim⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro run conforms t op args need
      obtain ⟨c, b, head, operands⟩ := need
      rw [kk_guard b (List.mem_of_getElem? (kopf_code head))] at operands
      cases operands
    · intro run conforms t waiting
      obtain ⟨contexts, ⟨c, member⟩, blocked⟩ := waiting
      obtain ⟨_, impossible, _⟩ := blocked c member
      exact impossible
    · intro run conforms t l h _ hne
      exact (hne rfl).elim

/-- The counterexample unit is accepted by the endliche line with an empty declaration. -/
private theorem kk_akk :
    EndlichAkzeptiertAussage Plattform.x86_64 kkUnit [] Wirkungsklasse.kostenZeile :=
  ⟨kk_akzeptiert, rfl⟩

/-- The estimator is defined on the counterexample unit; its value is five. -/
private theorem kk_schaetze : schaetzeEinheit Wirkungsklasse.kostenZeile [] kkBaum = some 5 := by
  rfl

/-- The admitted run installs mass six and takes six entry ticks without a crash. -/
private theorem kk_lauf :
    ∃ (h : Umgebung) (ρ : Lauf (einheitMitSchranken Plattform.x86_64 kkUnit)),
      Laeufe (einheitMitSchranken Plattform.x86_64 kkUnit) h ρ ∧
      (∀ t, t < 6 → ρ.zeit.spur t = some (.kontext eintritt (), ⟨[], []⟩)) ∧
      ∃ s, ρ.zeit.zustand 4 = some s ∧
        (s.lokal eintritt).funktion = some mainName ∧ (s.lokal eintritt).mass = some 6 := by
  let platform := Plattform.x86_64
  let E := einheitMitSchranken platform kkUnit
  let p := programm kkBaum
  let b0 : Befehl := (p.code[0]?).getD Befehl.ende
  let b1 : Befehl := (p.code[1]?).getD Befehl.ende
  let b2 : Befehl := (p.code[2]?).getD Befehl.ende
  let b3 : Befehl := (p.code[3]?).getD Befehl.ende
  let b4 : Befehl := (p.code[4]?).getD Befehl.ende
  let b5 : Befehl := (p.code[5]?).getD Befehl.ende
  have e0 : p.code[0]? = some b0 := by rfl
  have e1 : p.code[1]? = some b1 := by rfl
  have e2 : p.code[2]? = some b2 := by rfl
  have e3 : p.code[3]? = some b3 := by rfl
  have e4 : p.code[4]? = some b4 := by rfl
  have e5 : p.code[5]? = some b5 := by rfl
  let H := Umgebung.referenz platform.katalog 1 Laufkonstruktion.leer
  let hw := Umgebung.referenzLauf platform.katalog 1 Laufkonstruktion.leer
  have fair : FairLaeufe platform.katalog H hw :=
    Umgebung.referenz_fair _ _ _ platform.katalog_wohlgeformt (Nat.zero_lt_succ 0)
  obtain ⟨start, admissible⟩ := zulStart_erfuellbar fair.hardware Laufkonstruktion.bild_gueltig
  obtain ⟨kern, zugeordnet⟩ := admissible.2.2.1 0 (Nat.zero_lt_succ 0)
  have kernNull : kern = 0 := Nat.lt_one_iff.mp (admissible.2.2.2.1 0 kern zugeordnet).2
  have assignment : start.assignment 0 = some 0 := kernNull ▸ zugeordnet
  let d := startdaten p.eingang p.eintritte (some 0) platform start.regions
  let z₀ : Zustand := Zustand.start d.lokal d.status d.kerne d.rechte
    E.einrichtung.initial (.leer (E.startmedium start))
  have geladen : E.laden start (H.lade E.bild) = some z₀ := by
    change Ast.Semantik.laden p.eingang p.eintritte p.speicher platform start
      (Ast.Semantik.bild.lade) = some z₀
    have image : Ast.Semantik.bild.lade.starts 0 = some 0 ∧
        Ast.Semantik.bild.lade.bytes 0 = some 0 := ⟨rfl, rfl⟩
    rw [Ast.Semantik.laden, if_pos image, assignment]
    rfl
  let z₁ := b0.nach eintritt z₀
  let z₂ := b5.nach eintritt z₁
  let z₃ := b1.nach eintritt z₂
  let z₄ := b2.nach eintritt z₃
  let z₅ := b3.nach eintritt z₄
  let z₆ := b4.nach eintritt z₅
  have kopf0 : E.system.kopf z₀ eintritt = some b0 := by rfl
  have kopf1 : E.system.kopf z₁ eintritt = some b5 := by rfl
  have kopf2 : E.system.kopf z₂ eintritt = some b1 := by rfl
  have kopf3 : E.system.kopf z₃ eintritt = some b2 := by rfl
  have kopf4 : E.system.kopf z₄ eintritt = some b3 := by rfl
  have kopf5 : E.system.kopf z₅ eintritt = some b4 := by rfl
  have priv (b : Befehl) (mem : b ∈ p.code) : b.Privat := kk_rein b (by simpa only [p] using mem)
  let spur : SchrittSpur Zelle Int := ⟨[], []⟩
  have s0 : Lauffolge E hw 0 (some z₀) (.kontext eintritt (), spur) (some z₁) :=
    kk_schritt platform kkUnit hw 0 z₀ b0 rfl ⟨0, rfl, rfl, rfl⟩ kopf0 (priv b0 (List.mem_of_getElem? e0))
  have s1 : Lauffolge E hw 1 (some z₁) (.kontext eintritt (), spur) (some z₂) :=
    kk_schritt platform kkUnit hw 1 z₁ b5 rfl ⟨0, rfl, rfl, rfl⟩ kopf1 (priv b5 (List.mem_of_getElem? e5))
  have s2 : Lauffolge E hw 2 (some z₂) (.kontext eintritt (), spur) (some z₃) :=
    kk_schritt platform kkUnit hw 2 z₂ b1 rfl ⟨0, rfl, rfl, rfl⟩ kopf2 (priv b1 (List.mem_of_getElem? e1))
  have s3 : Lauffolge E hw 3 (some z₃) (.kontext eintritt (), spur) (some z₄) :=
    kk_schritt platform kkUnit hw 3 z₃ b2 rfl ⟨0, rfl, rfl, rfl⟩ kopf3 (priv b2 (List.mem_of_getElem? e2))
  have s4 : Lauffolge E hw 4 (some z₄) (.kontext eintritt (), spur) (some z₅) :=
    kk_schritt platform kkUnit hw 4 z₄ b3 rfl ⟨0, rfl, rfl, rfl⟩ kopf4 (priv b3 (List.mem_of_getElem? e3))
  have s5 : Lauffolge E hw 5 (some z₅) (.kontext eintritt (), spur) (some z₆) :=
    kk_schritt platform kkUnit hw 5 z₅ b4 rfl ⟨0, rfl, rfl, rfl⟩ kopf5 (priv b4 (List.mem_of_getElem? e4))
  obtain ⟨rest, ende⟩ := Zeitlauf.existiert (fun t => Lauffolge E hw (t + 6)) (some z₆)
  let ab5 := voran (schritt := fun t => Lauffolge E hw (t + 5)) rest (some z₅)
    (.kontext eintritt (), spur) (ende.symm ▸ s5)
  let ab4 := voran (schritt := fun t => Lauffolge E hw (t + 4)) ab5 (some z₄)
    (.kontext eintritt (), spur) (by change Lauffolge E hw 4 (some z₄) _ (ab5.zustand 0); exact s4)
  let ab3 := voran (schritt := fun t => Lauffolge E hw (t + 3)) ab4 (some z₃)
    (.kontext eintritt (), spur) (by change Lauffolge E hw 3 (some z₃) _ (ab4.zustand 0); exact s3)
  let ab2 := voran (schritt := fun t => Lauffolge E hw (t + 2)) ab3 (some z₂)
    (.kontext eintritt (), spur) (by change Lauffolge E hw 2 (some z₂) _ (ab3.zustand 0); exact s2)
  let ab1 := voran (schritt := fun t => Lauffolge E hw (t + 1)) ab2 (some z₁)
    (.kontext eintritt (), spur) (by change Lauffolge E hw 1 (some z₁) _ (ab2.zustand 0); exact s1)
  let zeit := voran (schritt := fun t => Lauffolge E hw t) ab1 (some z₀)
    (.kontext eintritt (), spur) (by change Lauffolge E hw 0 (some z₀) _ (ab1.zustand 0); exact s0)
  let ρ : Lauf E := ⟨start, hw, zeit⟩
  have lauf : Laeufe E H ρ := by
    refine ⟨fair.hardware, fair.konform, admissible, ?_⟩
    change some z₀ = E.laden start (H.lade E.bild)
    exact geladen.symm
  have hmass : (z₄.lokal eintritt).mass = some 6 := by
    change (((Befehl.pruefeMass 0).auswerten (z₃.lokal eintritt)).mass = some 6)
    exact kk_mass_auswertung (z₃.lokal eintritt) mainName rfl rfl rfl
  refine ⟨H, ρ, lauf, ?_, z₄, rfl, rfl, hmass⟩
  intro t ht
  obtain rfl | rfl | rfl | rfl | rfl | rfl :
      t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 := by omega
  all_goals rfl

/-- The corrected measure statement has jointly satisfiable premises at a positive mass. -/
theorem kostenKorrespondenzMass_nichtTrivial :
    ∃ (u : UnitMitSchranken) (h : Umgebung)
      (ρ : Lauf (einheitMitSchranken Plattform.x86_64 u)) (s : Zustand) (kern : FunktionsKern),
      EndlichAkzeptiertAussage Plattform.x86_64 u [] Wirkungsklasse.kostenZeile ∧
      schaetzeEinheit Wirkungsklasse.kostenZeile [] u.baum = some 5 ∧
      Laeufe (einheitMitSchranken Plattform.x86_64 u) h ρ ∧
      ρ.zeit.zustand 4 = some s ∧ (s.lokal eintritt).funktion = some mainName ∧
      (s.lokal eintritt).mass = some 6 ∧ findeKern u.baum.2 mainName = some kern ∧
      kern.massIntervall = some (6, 6) ∧ 6 ≤ (6 : Int) ∧ (6 : Int) ≤ 6 := by
  obtain ⟨h, ρ, lauf, _, s, hcut, hfunk, hmass⟩ := kk_lauf
  cases hfinde : findeKern kkBaum.2 mainName with
  | none => have hs := kk_intervall; rw [hfinde] at hs; cases hs
  | some kern =>
    have hs := kk_intervall
    rw [hfinde] at hs
    exact ⟨kkUnit, h, ρ, s, kern, kk_akk, kk_schaetze, lauf, hcut, hfunk, hmass, hfinde,
      Option.some.inj hs, le_rfl, le_rfl⟩

/-- The measure prologue makes the admitted entry prefix cost more than the estimate. -/
theorem kostenSchaetzerKorrektAussage_falsch : ¬ KostenSchaetzerKorrektAussage := by
  intro all
  obtain ⟨h, ρ, lauf, ticks, _⟩ := kk_lauf
  have seg : EintrittSegmentAussage Plattform.x86_64 kkUnit ρ 0 6 := by
    refine ⟨by omega, ?_, Or.inl rfl⟩
    intro t _ ht spur contrad
    rw [ticks t ht] at contrad
    cases contrad
  have cost (n : Nat) (hn : n ≤ 6) : Kontextkosten ρ eintritt 0 n = n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [kontextkosten_schritt_gleich (Nat.zero_add n) (ticks n (by omega)), ih (by omega)]
  have hle := (all Plattform.x86_64 kkUnit [] Wirkungsklasse.kostenZeile 5
    kk_akk kk_schaetze lauf).2 0 6 seg
  rw [Nat.sub_zero, cost 6 (by omega)] at hle
  omega

end Gabbro.Core.Beobachtung
