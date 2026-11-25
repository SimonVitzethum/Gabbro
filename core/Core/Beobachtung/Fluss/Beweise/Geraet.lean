module

public import Core.Beobachtung.Fluss.Geraet
public import Core.Ast.LowLevel.DeviceUnit

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Ast.LowLevel.Device (Denotation Binding RegisterAccess Befugt Rule)

/-- A device rule always comes from `Rule.machine`. Both of its constructors need the device
    authority in the booking; an empty booking rules out every rule step. -/
private theorem geraete_regel_unmoeglich {k : Katalog}
    {c : Kontext} {s u : Ast.LowLevel.Device.State}
    {w : PUnit} {plans : List Ast.LowLevel.Device.Plan}
    {binding : Binding k} {access : RegisterAccess} {required : GeraetePhase}
    {target : Option GeraetePhase}
    (leer : s.buchung.geraet = fun _ => none)
    (impl : (Rule.machine binding access required target).impl c s w plans u) : False := by
  rcases impl with ⟨plan, _, rule⟩
  have nicht : s.buchung.geraet binding.handle.origin.object ≠ some (c, .frei) := by
    rw [congrFun leer binding.handle.origin.object]
    intro gleich
    cases gleich
  rcases rule with ⟨owned, _⟩ | ⟨owned, _, _, _⟩
  · exact nicht owned.1
  · exact nicht owned.1

/-- Every rule a device denotation supplies is a `Rule.machine` with fixed access and phase. -/
private theorem geraete_denotation_unmoeglich {k scope} {c : Kontext}
    {s u : Ast.LowLevel.Device.State} {w : PUnit} {plans : List Ast.LowLevel.Device.Plan}
    (d : Denotation k scope) (locals : Ast.Umgebung scope)
    (leer : s.buchung.geraet = fun _ => none)
    (impl : (d.rule locals).impl c s w plans u) : False := by
  cases d with
  | read destination binding offset =>
      exact geraete_regel_unmoeglich (binding := binding) (access := .read offset)
        (required := .ready) (target := none) leer impl
  | fallibleRead destination binding offset promise handler =>
      exact geraete_regel_unmoeglich (binding := binding) (access := .fallibleRead offset promise)
        (required := .ready) (target := none) leer impl
  | write binding offset value =>
      exact geraete_regel_unmoeglich (binding := binding)
        (access := .write offset (value.wert locals).wert.toNat)
        (required := .ready) (target := none) leer impl
  | transition decl =>
      exact geraete_regel_unmoeglich (binding := decl.binding)
        (access := .write decl.row.offset decl.data)
        (required := decl.changes.prior) (target := some decl.changes.after) leer impl

/-- A device run starts with an empty booking and no step refills the device ledger:
    protocol arrivals, interrupts and context steps keep it, and a crash resets it. -/
private theorem geraete_zustand_geraet_leer (k : Katalog) (scope : Ast.Scope)
    (locals : Ast.Umgebung scope) (d : Denotation k scope) {h : Umgebung}
    {ρ : Lauf (d.unit locals)} (lauf : Laeufe (d.unit locals) h ρ) :
    ∀ t z, ρ.zeit.zustand t = some z → z.buchung.geraet = fun _ => none := by
  intro t
  induction t with
  | zero =>
      intro z hz
      rw [lauf.2.2.2] at hz
      unfold Denotation.unit Gabbro.Core.Ast.LowLevel.Device.unit at hz
      dsimp only at hz
      split at hz
      · have zEq := Option.some.inj hz.symm
        subst z
        rfl
      · cases hz
  | succ t ih =>
      intro z hz
      cases hvor : ρ.zeit.zustand t with
      | none =>
          have tick := ρ.zeit.takt t
          rw [hvor, hz] at tick
          cases tick with
          | wartet label eq _ => cases eq
          | schritt _ step => cases step
      | some vor =>
          have leerVor := ih vor hvor
          have tick := ρ.zeit.takt t
          rw [hvor, hz] at tick
          cases tick with
          | wartet label eq _ =>
              have zEq : z = vor := Option.some.inj eq
              subst z
              exact leerVor
          | schritt _ step =>
              cases step with
              | schritt impl =>
                  cases impl with
                  | kontext _ _ regel _ =>
                      exfalso
                      obtain ⟨i, _, implI⟩ := regel
                      exact geraete_denotation_unmoeglich d locals leerVor implI
                  | antwort _ h =>
                      obtain ⟨_, _, _, stateEq⟩ := h
                      rw [stateEq]
                      exact leerVor
                  | interrupt _ h =>
                      obtain ⟨_, _, _, _, _, _, _, _, _, _, stateEq⟩ := h
                      rw [stateEq]
                      exact leerVor
                  | absturz h =>
                      obtain ⟨_, stateEq⟩ := AbsturzSchritt.genau h
                      rw [stateEq]
                      rfl

/-- The device form's flow rule is vacuous: no device context step can ever occur, so the
    non-interference duty has no instance to discharge. -/
theorem geraeteNI : GeraeteNIAussage := by
  intro k scope locals d _
  intro h₁ h₂ ρ₁ ρ₂ vergleich predictor t c w spur vor zustand kopf spurGlied kopplung
  have leerVor := geraete_zustand_geraet_leer k scope locals d vergleich.links t vor zustand
  have tick := ρ₁.zeit.takt t
  rw [spurGlied, zustand] at tick
  generalize nachEq : ρ₁.zeit.zustand (t + 1) = nach at tick
  cases tick with
  | wartet label _ _ => cases label
  | schritt label step =>
      cases label
      cases step with
      | schritt impl =>
          cases impl with
          | kontext _ _ regel _ =>
              exfalso
              obtain ⟨i, _, implI⟩ := regel
              exact geraete_denotation_unmoeglich d locals leerVor implI

end Gabbro.Core.Beobachtung
