module

public import Core.Sicherheit.Lauf
public import Core.Ast.Semantik.Runtime.Sicherheit
import Core.Sicherheit.Laufkonstruktion

@[expose] public section

namespace Gabbro.Core.Sicherheit

open Maschine Katalog Ast Ast.Semantik

private theorem ohneDeklarationen {p : Fragment} (platform : Plattform)
    (keine : p.klauseln.invariant = []) (s : Ast.Semantik.Zustand) :
    InvariantenAmSchnitt (p.sicherheitsEinheit platform) s := by
  refine ⟨fun _ _ => trivial, ?_⟩
  intro i d vorhanden _
  change (p.klauseln.invariant.map (fun gilt => ⟨none, gilt⟩))[i]? = some d at vorhanden
  rw [keine] at vorhanden
  cases vorhanden

private theorem arithmetik_grenzen {p : Fragment} (platform : Plattform)
    (keine : p.klauseln.invariant = []) : GrenzenSicher (p.sicherheitsEinheit platform) := by
  refine ⟨?_, fun _ _ _ _ _ nach _ _ => ohneDeklarationen platform keine nach,
    fun _ _ _ _ _ nach _ _ => ohneDeklarationen platform keine nach,
    fun _ _ _ _ nach _ _ => ohneDeklarationen platform keine nach⟩
  intro H start s _ _ h
  change Ast.Semantik.laden p.eingang start (H.lade Ast.Semantik.bild) = some s at h
  unfold Ast.Semantik.laden at h
  split at h
  · cases h
    exact ⟨rfl, rfl, rfl, ohneDeklarationen platform keine _⟩
  · cases h

private theorem arithmetik_antwortrechte (p : Fragment) (platform : Plattform) (b : Befehl) :
    RegelAntwortSicher (p.sicherheitsEinheit platform) b := by
  intro t c w vor zwischen nach plan spur _ regel vollzug befugt
  obtain ⟨_, rfl⟩ := b.vollzug_genau (w := w) regel vollzug
  exact befugt

private theorem arithmetik_schritt
    (p : Fragment) (platform : Plattform) (hw : HwLauf) (t : Nat)
    (s : Ast.Semantik.Zustand) (b : Befehl)
    (normal : (hw.angebot t).crash = false) (bereit : KannSchreiten hw t eintritt s)
    (kopf : (p.einheit platform).system.kopf s eintritt = some b) :
    Lauffolge (p.einheit platform) hw t (some s) (.kontext eintritt (), ⟨[], []⟩)
      (some (b.nach eintritt s)) :=
  .schritt (.kontext normal bereit ⟨b, kopf, rfl, rfl⟩ (b.vollzug _ t eintritt s))

/-- The rule and boundary obligations hold jointly for a loaded unit that actually
    executes literals, both binary operators and a local binding. -/
theorem sicherheit_aus_regeln_erfuellbar :
    ∃ (E : Einheit PUnit PUnit Int PUnit Rahmen PUnit PUnit PUnit Befehl)
      (H : Umgebung) (ρ : Lauf E),
      GrenzenSicher E ∧ (∀ f, RegelAntwortSicher E f) ∧ (∀ f, RegelSicher E f) ∧
      Maschine.Laeufe E.maschine H ρ ∧
      ∃ s (wert : Zahl 7 7), ρ.zeit.zustand 6 = some s ∧
        (s.lokal eintritt).lokale.head? = some (some ⟨.int 7 7, wert⟩) ∧ wert.wert = 7 := by
  let name : Identifier :=
    ⟨['x'], 'x', [], rfl, Or.inl (Or.inl ⟨by change 97 ≤ 120; omega, by change 120 ≤ 122; omega⟩),
      fun _ member => (List.not_mem_nil member).elim⟩
  have ordinary : name.val ≠ "mut".toList := by
    change ['x'] ≠ ['m', 'u', 't']
    intro eq
    cases eq
  let tree := Stmt.letValue (scope := []) name
    ⟨ordinary, (directName_of_singleton (name := name) rfl).1⟩
    (.binary .add (.lit 1) (.binary .mul (.lit 2) (.lit 3)))
  let p := stmt tree
  have keine : p.klauseln.invariant = [] := stmt_keine_invarianten tree
  let platform := Plattform.x86_64
  let E := p.sicherheitsEinheit platform
  let H := Umgebung.referenz platform.katalog 1 Laufkonstruktion.leer
  let hw := Umgebung.referenzLauf platform.katalog 1 Laufkonstruktion.leer
  have fair : FairLaeufe platform.katalog H hw :=
    Umgebung.referenz_fair _ _ _ platform.katalog_wohlgeformt (Nat.zero_lt_succ 0)
  obtain ⟨start, admissible⟩ := zulStart_erfuellbar fair.hardware Laufkonstruktion.bild_gueltig
  obtain ⟨kern, zugeordnet⟩ := admissible.2.2.1 0 (Nat.zero_lt_succ 0)
  have kernNull : kern = 0 := Nat.lt_one_iff.mp (admissible.2.2.2.1 0 kern zugeordnet).2
  have assignment : start.assignment 0 = some 0 := kernNull ▸ zugeordnet
  let d := startdaten (some 0)
  let z₀ : Ast.Semantik.Zustand := Maschine.Zustand.start d.lokal d.status d.kerne d.rechte einrichtung.initial
    (.leer (startmedium start))
  have geladen : E.maschine.laden start (H.lade E.maschine.bild) = some z₀ := by
    change Ast.Semantik.laden p.eingang start (Ast.Semantik.bild.lade) = some z₀
    have image : Ast.Semantik.bild.lade.starts 0 = some 0 ∧
        Ast.Semantik.bild.lade.bytes 0 = some 0 := ⟨rfl, rfl⟩
    rw [Ast.Semantik.laden, if_pos image, assignment]
  let z₁ := (Befehl.literal 0 1).nach eintritt z₀
  let z₂ := (Befehl.literal 1 2).nach eintritt z₁
  let z₃ := (Befehl.literal 2 3).nach eintritt z₂
  let z₄ := (Befehl.binaer .mul 1).nach eintritt z₃
  let z₅ := (Befehl.binaer .add 0).nach eintritt z₄
  let z₆ := (Befehl.binden name 0).nach eintritt z₅
  obtain ⟨rest, ende⟩ := Zeitlauf.existiert (fun t => Lauffolge E.maschine hw (t + 6)) (some z₆)
  have s₀ := arithmetik_schritt p platform hw 0 z₀ (.literal 0 1) rfl ⟨0, rfl, rfl, rfl⟩ rfl
  have s₁ := arithmetik_schritt p platform hw 1 z₁ (.literal 1 2) rfl ⟨0, rfl, rfl, rfl⟩ rfl
  have s₂ := arithmetik_schritt p platform hw 2 z₂ (.literal 2 3) rfl ⟨0, rfl, rfl, rfl⟩ rfl
  have s₃ := arithmetik_schritt p platform hw 3 z₃ (.binaer .mul 1) rfl ⟨0, rfl, rfl, rfl⟩ rfl
  have s₄ := arithmetik_schritt p platform hw 4 z₄ (.binaer .add 0) rfl ⟨0, rfl, rfl, rfl⟩ rfl
  have s₅ := arithmetik_schritt p platform hw 5 z₅ (.binden name 0) rfl ⟨0, rfl, rfl, rfl⟩ rfl
  let schritt := Lauffolge E.maschine hw
  let abFuenf := voran (schritt := fun t => schritt (t + 5)) rest (some z₅) _ (ende.symm ▸ s₅)
  let abVier := voran (schritt := fun t => schritt (t + 4)) abFuenf (some z₄) _ s₄
  let abDrei := voran (schritt := fun t => schritt (t + 3)) abVier (some z₃) _ s₃
  let abZwei := voran (schritt := fun t => schritt (t + 2)) abDrei (some z₂) _ s₂
  let abEins := voran (schritt := fun t => schritt (t + 1)) abZwei (some z₁) _ s₁
  let zeit := voran (schritt := schritt) abEins (some z₀) _ s₀
  let ρ : Lauf E := ⟨start, hw, zeit⟩
  exact ⟨E, H, ρ, arithmetik_grenzen platform keine, arithmetik_antwortrechte p platform,
    Befehl.sicher p platform keine, ⟨fair.hardware, fair.konform, admissible, geladen.symm⟩,
    z₆, ⟨7, Int.le_refl _, Int.le_refl _⟩, ende, rfl, rfl⟩

end Gabbro.Core.Sicherheit
