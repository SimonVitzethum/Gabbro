/-
  File:      core/Core/Verfeinerung/Abnahme/LockFreeRmw.lean
  Subject:   A SECOND, non-vacuous refutation of `LockFreeFamilienAussage`: the lost-value
             implementation of a real MK-04 rmw instruction (`Befehl.zugriff` with
             `Zugriffsform.tausche`). The concrete machine represents the error: the false rule
             performs an rmw event at a state where the instruction's guarded ideal rule refuses
             the access, and binds a different value than the event records. The family statement
             excludes the error through its simulation leg (`RegelSimulation`), hence through
             `LockFreeFamilienAussage.1`. The existing `nichtTrivial`, which changes only the
             declared start abstraction, is not reused here.
-/
module

public import Core.Verfeinerung.Abnahme.LockFree
public import Core.Ast.Semantik.Runtime.Atom.Aussagen
public import Core.Ast.Semantik.Runtime.Klasse.Pflichten
public import Core.Maschine.Speicherfolge

@[expose] public section

namespace Gabbro.Core.Maschine.I

open Gabbro.Core.Katalog
open Gabbro.Core.Ast.Semantik

/-- The unit, state and plan types of the witness. -/
abbrev RmwZeugeEinheit := Einheit Nat Zelle Int Nat Rahmen PUnit PUnit PUnit Unit
abbrev RmwZeugeZustand := Zustand Nat Zelle Int Nat Rahmen PUnit
abbrev RmwZeugePlan := SchrittPlan Nat Zelle Int PUnit
abbrev RmwZeugeRegel := Regel RmwZeugeZustand RmwZeugePlan PUnit

/-- A real atomic update instruction of MK-04: `tausche` of region 0, cell 0. -/
def rmwZeugeBefehl : Befehl := .zugriff (.tausche 0 0 0 0 (Ast.Ty.int 0 0) .sc)

/-- Its step form: one rmw event that reads and writes the cell. -/
def rmwZeugeForm : Schrittform := rmwZeugeBefehl.form

/-- The false implementation: the rule fires the rmw and binds `0`, whatever the memory returned.
    Its ideal side is the guarded instruction rule, which refuses an access without authority. -/
def rmwZeugeRegel : RmwZeugeRegel := Schrittform.verloren rmwZeugeForm

/-- The unit whose only form is that false rmw instruction. -/
def rmwZeugeEinheitWert : RmwZeugeEinheit := Regeleinheit .x86_64 rmwZeugeRegel

/-- The frame of the empty start holds no temporary, so the instruction names the outside cell.
    No context holds a handle there and the guarded rule refuses. -/
theorem rmwZeuge_operand_aussen :
    (rmwZeugeForm.operand (Leerzustand.lokal eintritt)) =
      ⟨.aussen, 0, 0, none, .tausche⟩ := by
  rfl

theorem rmwZeuge_keinRecht :
    ¬ rmwZeugeForm.klasse.befugt (rmwZeugeForm.operand (Leerzustand.lokal eintritt))
        Leerzustand eintritt := by
  rw [rmwZeuge_operand_aussen]
  simp only [Wirkungsklasse.befugt, Zustand.befugt, Zustand.griff]
  rintro ⟨⟨_, _, griff, _⟩, _⟩
  cases griff

/-- The model represents the error: a concrete rmw step with a non-empty memory trace, whose
    implementation binds `0` while the recorded event reads another value, and whose ideal rule
    refuses the access at the same state. -/
theorem rmwZeugeKonfiguration :
    ∃ (gelesen : Int) (plan : RmwZeugePlan) (spur : SchrittSpur Zelle Int)
      (u s' : RmwZeugeZustand),
    plan = rmwZeugeForm.plan (Leerzustand.lokal eintritt) gelesen ∧
      u = Schrittform.zugriffNach rmwZeugeForm eintritt Leerzustand 0 ∧
      rmwZeugeRegel.impl eintritt Leerzustand () [plan] u ∧
      FuehrtSchrittAus rmwZeugeEinheitWert.einrichtung 0 eintritt Leerzustand u plan spur s' ∧
      spur.speicher ≠ [] ∧
      ¬ rmwZeugeRegel.ideal eintritt Leerzustand () [plan] u := by
  obtain ⟨gelesen, es, graph, folge⟩ := speicherzug_existiert
    (anfang := Leerzustand.initial) (f := .kontext eintritt)
    (g := Leerzustand.graph) Speicher.Zustand.leer_konsistent
    Speicher.Zustand.leer_vollstaendig (a := .rmw) (x := .aussen) (m := .sc) (v := 0)
  let plan := rmwZeugeForm.plan (Leerzustand.lokal eintritt) gelesen
  let spur : SchrittSpur Zelle Int := ⟨es, []⟩
  let u := Schrittform.zugriffNach rmwZeugeForm eintritt Leerzustand 0
  let s' : RmwZeugeZustand := { u with graph := graph }
  have rahmen : Zustandsrahmen Leerzustand u := by
    simp only [u, Schrittform.zugriffNach, Schrittform.nach, Zustandsrahmen]
  have liest : ∀ l ∈ plan.lesen, l.art.liest := by
    intro l mem
    simp only [plan, rmwZeugeForm, Schrittform.plan, Wirkungsklasse.plan,
      rmwZeuge_operand_aussen, List.mem_singleton] at mem
    subst l
    rfl
  have spurGefuellt : spur.speicher ≠ [] := by
    cases folge with
    | nil => simp only [plan, rmwZeugeForm, Schrittform.plan, Wirkungsklasse.plan,
        rmwZeuge_operand_aussen, List.nil_append, List.cons_append, List.cons_ne_nil] at *
    | cons _ _ _ => simp only [spur, List.nil_append, List.cons_append, List.cons_ne_nil]
  have aus : FuehrtSchrittAus rmwZeugeEinheitWert.einrichtung 0 eintritt Leerzustand u plan spur s' := by
    refine ⟨rahmen, liest, [], u, .intern, ?_, rfl⟩
    simpa only [plan, rmwZeugeForm, Schrittform.plan, Wirkungsklasse.plan,
      rmwZeuge_operand_aussen, spur, List.nil_append, List.append_nil] using folge
  have impl : rmwZeugeRegel.impl eintritt Leerzustand () [plan] u := by
    refine ⟨gelesen, ?_, rfl⟩
    rfl
  have idealVerweigert : ¬ rmwZeugeRegel.ideal eintritt Leerzustand () [plan] u := by
    intro step
    change rmwZeugeForm.zugriffsschritt eintritt Leerzustand [plan] u at step
    rcases step with ⟨_, planPrivat, _⟩ | ⟨befugt, _, _, _⟩
    · have lesenLeer : plan.lesen = [] := by
        rw [planPrivat]
        rfl
      simp only [plan, rmwZeugeForm, Schrittform.plan, Wirkungsklasse.plan,
        rmwZeuge_operand_aussen, List.cons_ne_nil] at lesenLeer
    · exact rmwZeuge_keinRecht befugt
  exact ⟨gelesen, plan, spur, u, s', rfl, rfl, impl, aus, spurGefuellt, idealVerweigert⟩

/-- The family statement refuses that error: the false rmw rule cannot satisfy its simulation leg. -/
theorem rmwZeuge_nichtRegelSimulation : ¬ RegelSimulation rmwZeugeEinheitWert () := by
  intro sim
  obtain ⟨gelesen, plan, spur, u, s', planEq, uEq, impl, exec, spurNe, idealNe⟩ :=
    rmwZeugeKonfiguration
  subst plan
  subst u
  have hw : HwLauf := Umgebung.referenzLauf Plattform.x86_64.katalog 1
    (fun _ _ => ⟨(fun _ => ⟨0, false, false, [], fun _ => 0⟩),
      (fun _ _ => none), (fun _ _ => none)⟩)
  have crash : (hw.angebot 0).crash = false := rfl
  have ready : KannSchreiten hw 0 eintritt Leerzustand := by
    refine ⟨0, ?_, ?_, ?_⟩
    · exact congrArg some (Nat.mod_one _)
    · change (Leerzustand.kerne 0).laeuft = some eintritt
      rfl
    · change Leerzustand.status eintritt = .laeuft
      simp only [Leerzustand, startdaten, Zustand.start, ite_eq_left rfl]
  have bezug : Zustandsbezug rmwZeugeEinheitWert Leerzustand Leerzustand :=
    ⟨ProtokollBezug.refl _, rfl⟩
  have simuliert := sim.schritt (hw := hw) (t := 0) (c := eintritt) (w := ())
    (s := Leerzustand) (u := u) (s' := s') (i := Leerzustand)
    (plan := rmwZeugeForm.plan (Leerzustand.lokal eintritt) gelesen) (spur := spur)
    bezug crash ready rfl impl exec
  rcases simuliert with ⟨i', idealSchritt, _⟩ | ⟨leer, _, _, _, _⟩
  · cases idealSchritt with
    | kontext _ _ rule ausIdeal =>
      have planPrivat : rmwZeugeForm.plan (Leerzustand.lokal eintritt) gelesen = Semantik.plan := by
        change rmwZeugeForm.zugriffsschritt eintritt Leerzustand
          [rmwZeugeForm.plan (Leerzustand.lokal eintritt) gelesen] _ at rule
        rcases rule with ⟨_, privat, _⟩ | ⟨befugt, _, _, _⟩
        · exact (List.cons.inj privat).1
        · exact (rmwZeuge_keinRecht befugt).elim
      subst planPrivat
      rcases ausIdeal with ⟨_, _, sperren, vIdeal, aus, folge, _⟩
      cases aus
      simp only [List.nil_append, List.append_nil] at folge
      cases folge
      exact spurNe rfl
  · exact spurNe (congrArg SchrittSpur.speicher leer)

/-- The non-triviality is a statement about the family, not about a changed declaration of its
    abstraction: a family with the false rmw rule as a member owes its simulation and cannot pay it. -/
theorem LockFreeFamilienAussage.nichtTrivialRmw :
    ∃ U : LockFreeEinheit Nat Zelle Int Nat Rahmen PUnit PUnit PUnit PUnit,
      ¬ LockFreeFamilienAussage U := by
  let U : LockFreeEinheit Nat Zelle Int Nat Rahmen PUnit PUnit PUnit PUnit :=
    ⟨rmwZeugeEinheitWert, PUnit, PUnit, PUnit, PUnit, fun _ => True,
      ⟨fun _ => none, rfl, fun _ _ => rfl⟩, fun _ => (), (), fun _ _ _ _ => True⟩
  refine ⟨U, ?_⟩
  intro aussage
  have sim : RegelSimulation U.einheit () := aussage.1 () trivial
  exact rmwZeuge_nichtRegelSimulation (by simpa only [U] using sim)

end Gabbro.Core.Maschine.I
