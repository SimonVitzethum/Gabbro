module

public import Core.Linken.Modul
public import Core.Linken.Gegenbeispiel
public import Core.Maschine.Schritte
public import Core.Maschine.Start
public import Core.Maschine.Zeitlauf
public import Core.Ast.Semantik.Elaborierung
public import Core.Annahme.Waechter
public import Core.Katalog.Erfuellbar
public import Core.Ast.Semantik.Runtime.Mehrkontext.System

@[expose] public section

namespace Gabbro.Core.Linken

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Annahme
open Gabbro.Core.Maschine
open Gabbro.Core.Katalog

/-- An entry program counter of a module: either a context entry recorded in the fragment, or the
    instruction right after a function definition (a call lands behind the definition header). -/
def EintrittsPc (m : Modul) (p : Nat) : Prop :=
  (∃ c, m.fragment.eintritte c = some p) ∨
    (∃ i name ps res glob skip ms calls eff,
      m.fragment.code[i]? = some (.definiere name ps res glob skip ms calls eff) ∧ p = i + 1)

/-- An entry state of a module: some context runs at an entry program counter with no return value
    and no stop reason. Calls clear temporaries on entry, so no condition on them is needed. -/
def Eintrittszustand (m : Modul) (s : Zustand) : Prop :=
  ∃ c p, EintrittsPc m p ∧ s.status c = .laeuft ∧ Rahmen.pc (s.lokal c) = p ∧
    Rahmen.rueckgabe (s.lokal c) = none ∧ Rahmen.stopp (s.lokal c) = none

/-- The guard uses of a fragment unit are the state-level guard uses of its code: a context poised
    at an instruction whose guard reports the operation and operands. -/
theorem tabellen_guard_form (p : Fragment) (platform : Plattform)
    (s : Zustand) (op : PartielleOperation) (args : Operanden op) :
    (p.einheit platform).quelltabellen.guard s op args ↔
      ∃ c b, kopf p.code s c = some b ∧ b.guard (s.lokal c) = some ⟨op, args⟩ := Iff.rfl

/-- Open acceptance of one module: every run that starts at an entry state satisfies every guard
    use, for every hardware run. A module entered through a call or start with foreign arguments is
    no run from a canonical start; the entry state is its own start. -/
def OffenAkzeptiertAussage (m : Modul) (platform : Plattform) : Prop :=
  ∀ s, Eintrittszustand m s →
    ∀ (hw : HwLauf)
      (ρ : Zeitlauf (I.Schritt (m.fragment.einheit platform).einrichtung
        (m.fragment.einheit platform).system (m.fragment.einheit platform).katalog hw)),
      ρ.zustand 0 = s →
      ∀ (t : ρ.Schnitt) (op : PartielleOperation) (args : Operanden op),
        (m.fragment.einheit platform).quelltabellen.guard (ρ.zustand t.val) op args →
          waechterBedarf op args

/-- The checker row for open acceptance: false exactly at the guard-carrying constructors. -/
def befehlOffenOk : Befehl → Bool
  | .teilen _ => false
  | .liesArray _ _ _ => false
  | .textIndex _ _ => false
  | .substring _ _ => false
  | _ => true

/-- A module passes the open checker row when none of its instructions carries a guard. -/
def modulOffenOk (m : Modul) : Bool :=
  m.fragment.code.all befehlOffenOk

/-- A passing instruction has no guard at any frame: the four refused constructors are exactly the
    ones with a guard arm. -/
theorem befehlOffenOk_guard (b : Befehl) (h : befehlOffenOk b = true) (frame : Rahmen) :
    b.guard frame = none := by
  cases b <;> first
    | exact (Bool.false_ne_true (by simpa only [befehlOffenOk] using h)).elim
    | rfl

/-- The checker row is sound: a module with no guard-carrying instruction is openly accepted, since
    no run starting at any entry state can report a guard use. -/
theorem modulOffenOk_korrekt (m : Modul) (platform : Plattform)
    (h : modulOffenOk m = true) : OffenAkzeptiertAussage m platform := by
  intro s _entry hw ρ h0 t op args need
  rw [tabellen_guard_form] at need
  obtain ⟨c, b, head, g⟩ := need
  have hmem : b ∈ m.fragment.code := kopf_mem head
  have hall : ∀ b ∈ m.fragment.code, befehlOffenOk b = true := by
    simp only [modulOffenOk, List.all_eq_true] at h
    exact h
  have gnone : b.guard ((ρ.zustand t.val).lokal c) = none :=
    befehlOffenOk_guard b (hall b hmem) _
  rw [gnone] at g
  cases g

/-- The calling module passes the open checker row: a call carries no guard. -/
theorem modulB_offenOk : modulOffenOk modulB = true := by
  rfl

/-- Open acceptance is satisfiable: the guard-free calling module is openly accepted. -/
theorem offenAkzeptiert_erfuellbar :
    ∃ (m : Modul) (platform : Plattform), OffenAkzeptiertAussage m platform :=
  ⟨modulB, .x86_64, modulOffenOk_korrekt modulB .x86_64 modulB_offenOk⟩

/-- The zero value for the entry temporaries of the counterexample module. -/
def nullWert : Dynamisch :=
  ⟨.int ((0 : Nat) : Int) ((0 : Nat) : Int), Zahl.literal ((0 : Nat) : Int)⟩

/-- The entry frame of the counterexample module: all temporaries hold zero. -/
def gegenRahmen : Rahmen :=
  { Rahmen.start [] with temp := fun _ => some nullWert }

/-- The counterexample fragment: a single division at the entry position. -/
def gegenFragment : Fragment :=
  { code := [Befehl.teilen 0], klauseln := .leer, eingang := [],
    eintritte := fun _ => some 0, speicher := .leer }

/-- The counterexample module: dividing by zero at its entry. -/
def gegenModul : Modul :=
  { name := "gegen", fragment := gegenFragment, exporte := [], importe := [] }

/-- An outside start for the entry state: no assignment, no regions, no input, empty view. -/
def gegenStart : AussenStart :=
  ⟨0, fun _ => none, [], fun _ => none, AussenSicht.leer⟩

/-- A quiet hardware run for the counterexample: no core, no interrupt, no crash. -/
def gegenHw : HwLauf :=
  ⟨fun _ => ⟨none, fun _ => false, [], fun _ => false, false, false, 0⟩,
   ⟨fun _ _ => AussenSicht.leer, fun _ _ _ => .warten, fun _ _ _ _ => none⟩⟩

/-- The entry state of the counterexample module: the entry context runs the division with zero
    temporaries. -/
def gegenZustand : Zustand :=
  let base := (I.start (gegenFragment.einheit .x86_64) gegenStart).2
  { base with lokal := Function.update base.lokal eintritt gegenRahmen,
              status := Function.update base.status eintritt .laeuft }

/-- The entry state is an entry state of the counterexample module. -/
theorem gegenEintritt : Eintrittszustand gegenModul gegenZustand := by
  have hstatus : gegenZustand.status eintritt = .laeuft := by
    simp only [gegenZustand, Function.update_self]
  have hpc : (gegenZustand.lokal eintritt).pc = 0 := by
    simp only [gegenZustand, gegenRahmen, Rahmen.start, Function.update_self]
  have hrueck : (gegenZustand.lokal eintritt).rueckgabe = none := by
    simp only [gegenZustand, gegenRahmen, Rahmen.start, Function.update_self]
  have hstopp : (gegenZustand.lokal eintritt).stopp = none := by
    simp only [gegenZustand, gegenRahmen, Rahmen.start, Function.update_self]
  exact ⟨eintritt, 0, Or.inl ⟨eintritt, rfl⟩, hstatus, hpc, hrueck, hstopp⟩

/-- The entry state is poised at the division. -/
theorem gegenKopf :
    kopf gegenFragment.code gegenZustand eintritt = some (Befehl.teilen 0) := by
  have hstatus : gegenZustand.status eintritt = .laeuft := by
    simp only [gegenZustand, Function.update_self]
  have hpc : (gegenZustand.lokal eintritt).pc = 0 := by
    simp only [gegenZustand, gegenRahmen, Rahmen.start, Function.update_self]
  have hrueck : (gegenZustand.lokal eintritt).rueckgabe = none := by
    simp only [gegenZustand, gegenRahmen, Rahmen.start, Function.update_self]
  have hstopp : (gegenZustand.lokal eintritt).stopp = none := by
    simp only [gegenZustand, gegenRahmen, Rahmen.start, Function.update_self]
  have hcode : gegenFragment.code = [Befehl.teilen 0] := rfl
  unfold kopf
  rw [hstatus, hrueck, hstopp, hpc, hcode]
  rfl

/-- The entry state reports a division by zero. -/
theorem gegenGuard :
    (Befehl.teilen 0).guard (gegenZustand.lokal eintritt) =
      some ⟨.division, (0, 0)⟩ := by
  have htemp : gegenZustand.lokal eintritt = gegenRahmen := by
    simp only [gegenZustand, Function.update_self]
  rw [htemp]
  rfl

/-- Open acceptance is not trivial: the module dividing by zero at its entry is refused. -/
theorem offenAkzeptiert_nichtTrivial :
    ∃ (m : Modul) (platform : Plattform), ¬ OffenAkzeptiertAussage m platform := by
  refine ⟨gegenModul, .x86_64, ?_⟩
  intro hOffen
  obtain ⟨ρ, h0⟩ := Zeitlauf.existiert
    (I.Schritt (gegenFragment.einheit .x86_64).einrichtung
      (gegenFragment.einheit .x86_64).system (gegenFragment.einheit .x86_64).katalog gegenHw)
    gegenZustand
  have hentry : Eintrittszustand gegenModul gegenZustand := gegenEintritt
  have need : (gegenFragment.einheit .x86_64).quelltabellen.guard (ρ.zustand 0)
      .division (0, 0) :=
    ⟨eintritt, Befehl.teilen 0, by rw [h0]; exact gegenKopf, by rw [h0]; exact gegenGuard⟩
  have hbad := hOffen gegenZustand hentry _ ρ h0 ⟨0, Or.inl rfl⟩ .division (0, 0) need
  simp only [waechterBedarf] at hbad
  exact hbad rfl

/-- Entry states exist: the counterexample module has one. -/
theorem eintrittszustand_erfuellbar :
    ∃ (m : Modul) (s : Zustand), Eintrittszustand m s :=
  ⟨gegenModul, gegenZustand, gegenEintritt⟩

end Gabbro.Core.Linken
