/-
  File:      Core/Beobachtung/Wahrscheinlichkeit/Hebung/KatalogErhalt.lean
  Subject:   Atomic-decision invariance under a one-object body overwrite at a commit cut.
-/
module

public import Core.Beobachtung.Wahrscheinlichkeit.Hebung.KatalogAnkunft

public section

namespace Gabbro.Core.Beobachtung

open Gabbro.Core.Katalog Gabbro.Core.Maschine

/- The body change leaves every other object field, both handle tables and the device
   phases untouched. -/

theorem austauschSicht_felder (basis : AussenSicht) (objekt : Objekt) (body : List UInt8) (o : Objekt) :
    ((austauschSicht basis objekt body).objects o).generation = (basis.objects o).generation ∧
    ((austauschSicht basis objekt body).objects o).alive = (basis.objects o).alive ∧
    ((austauschSicht basis objekt body).objects o).ready = (basis.objects o).ready ∧
    ((austauschSicht basis objekt body).objects o).registers = (basis.objects o).registers := by
  by_cases h : o = objekt
  · subst o
    simp only [austauschSicht, Function.update_self]
    exact ⟨trivial, trivial, trivial, trivial⟩
  · simp only [austauschSicht, Function.update_of_ne h]
    exact ⟨trivial, trivial, trivial, trivial⟩

theorem austauschSicht_body_gleich (basis : AussenSicht) (objekt o : Objekt) (body : List UInt8)
    (h : o = objekt) :
    ((austauschSicht basis objekt body).objects o).body = body := by
  subst o
  simp only [austauschSicht, Function.update_self]

theorem austauschSicht_body_verschieden (basis : AussenSicht) (objekt o : Objekt) (body : List UInt8)
    (h : o ≠ objekt) :
    ((austauschSicht basis objekt body).objects o).body = (basis.objects o).body := by
  simp only [austauschSicht, Function.update_of_ne h]

theorem austauschSicht_herkunft (basis : AussenSicht) (objekt : Objekt) (body : List UInt8) (o : Objekt) :
    (austauschSicht basis objekt body).herkunft o = basis.herkunft o := by
  obtain ⟨hgen, _, _, _⟩ := austauschSicht_felder basis objekt body o
  simp only [AussenSicht.herkunft, hgen]

theorem austauschSicht_gueltig (basis : AussenSicht) (objekt : Objekt) (body : List UInt8)
    (endpoint : Endpunkt) (z : Zugriff) :
    (austauschSicht basis objekt body).gueltig endpoint z = basis.gueltig endpoint z := by
  obtain ⟨hgen, halive, _, _⟩ := austauschSicht_felder basis objekt body z.handle.origin.object
  have kanaele : (austauschSicht basis objekt body).channels = basis.channels := rfl
  simp only [AussenSicht.gueltig, AussenSicht.herkunft]
  rw [kanaele, hgen, halive]

theorem austauschSicht_wartet (p : Plattform) (basis : AussenSicht) (objekt : Objekt)
    (body : List UInt8) (q : Frage) :
    (austauschSicht basis objekt body).wartet p q = basis.wartet p q := by
  cases op : q.operation with
  | waitRegister offset expected =>
      obtain ⟨_, _, hready, hregs⟩ := austauschSicht_felder basis objekt body q.handle.origin.object
      simp only [AussenSicht.wartet, op, Plattform.registerWert, hready, hregs]
  | read | write | resolve | firmware | exchange | registerRead | registerWrite =>
      simp only [AussenSicht.wartet, op]

/- Exactly the three operations whose answer carries the object body. -/

def koerperEmpfindlich (op : AussenOperation) : Bool :=
  match op with
  | .read | .firmware _ _ | .exchange _ => true
  | .write _ | .resolve _ | .registerRead _ | .registerWrite _ _ | .waitRegister _ _ => false

theorem koerperEmpfindlich_iff (op : AussenOperation) :
    koerperEmpfindlich op = true ↔
      match op with
      | .read | .firmware _ _ | .exchange _ => True
      | _ => False := by
  cases op <;> simp only [koerperEmpfindlich, Bool.false_eq_true]

theorem koerperEmpfindlich_false_of_not_true {op : AussenOperation}
    (h : ¬ koerperEmpfindlich op = true) : koerperEmpfindlich op = false := by
  cases b : koerperEmpfindlich op with
  | true => exact (h b).elim
  | false => rfl

theorem austauschSicht_erfolg_unempfindlich (p : Plattform) (basis : AussenSicht) (objekt : Objekt)
    (body : List UInt8) (q : Frage) (hsens : koerperEmpfindlich q.operation = false) :
    (austauschSicht basis objekt body).erfolg p q = basis.erfolg p q := by
  cases op : q.operation with
  | read | firmware | exchange =>
      simp only [koerperEmpfindlich, op] at hsens
      cases hsens
  | write bytes =>
      simp only [AussenSicht.erfolg, op]
  | resolve name =>
      have namen : (austauschSicht basis objekt body).names = basis.names := rfl
      have kanaele : (austauschSicht basis objekt body).channels = basis.channels := rfl
      simp only [AussenSicht.erfolg, op, namen]
      cases n : basis.names q.handle.origin.object name with
      | none => simp only [n]
      | some h =>
          obtain ⟨hgen, halive, _, _⟩ := austauschSicht_felder basis objekt body h.origin.object
          simp only [n, kanaele, AussenSicht.herkunft, hgen, halive]
          rfl
  | registerRead offset | waitRegister offset _ =>
      obtain ⟨_, _, _, hregs⟩ := austauschSicht_felder basis objekt body q.handle.origin.object
      simp only [AussenSicht.erfolg, op, Plattform.registerWert, hregs]
  | registerWrite offset value =>
      simp only [AussenSicht.erfolg, op]

theorem austauschSicht_erfolg_sensibel (p : Plattform) (basis : AussenSicht) (objekt : Objekt)
    (body : List UInt8) (q : Frage) (hsens : koerperEmpfindlich q.operation = true) :
    (austauschSicht basis objekt body).erfolg p q =
      let alt := if q.handle.origin.object = objekt then body
        else (basis.objects q.handle.origin.object).body
      match q.operation with
      | .read => .ok (.data alt)
      | .firmware service bytes => .ok (.firmware service bytes alt)
      | .exchange bytes => .ok (.exchanged bytes alt)
      | _ => basis.erfolg p q := by
  cases op : q.operation with
  | read =>
      simp only [AussenSicht.erfolg, op]
      by_cases hobj : q.handle.origin.object = objekt
      · simp only [hobj, ite_true, austauschSicht, Function.update_self]
      · simp only [hobj, ite_false]
        rw [austauschSicht_body_verschieden basis objekt q.handle.origin.object body hobj]
  | firmware service bytes =>
      simp only [AussenSicht.erfolg, op]
      by_cases hobj : q.handle.origin.object = objekt
      · simp only [hobj, ite_true, austauschSicht, Function.update_self]
      · simp only [hobj, ite_false]
        rw [austauschSicht_body_verschieden basis objekt q.handle.origin.object body hobj]
  | exchange bytes =>
      simp only [AussenSicht.erfolg, op]
      by_cases hobj : q.handle.origin.object = objekt
      · simp only [hobj, ite_true, austauschSicht, Function.update_self]
      · simp only [hobj, ite_false]
        rw [austauschSicht_body_verschieden basis objekt q.handle.origin.object body hobj]
  | write bytes | resolve name | registerRead offset | registerWrite offset value
  | waitRegister offset expected =>
      simp only [koerperEmpfindlich, op] at hsens
      cases hsens

/- `atomar` reads the snapshot only through these five projections. -/

theorem atomar_vonSicht {p : Plattform} {s t : AussenSicht} {q : Frage}
    (herkunft : ∀ o : Objekt, s.herkunft o = t.herkunft o)
    (gueltig : ∀ z : Zugriff, s.gueltig q.endpoint z = t.gueltig q.endpoint z)
    (wartet : s.wartet p q = t.wartet p q)
    (ready : (s.objects q.handle.origin.object).ready = (t.objects q.handle.origin.object).ready)
    (erfolg : s.erfolg p q = t.erfolg p q) :
    atomar p s q = atomar p t q := by
  unfold atomar
  dsimp only
  rw [funext herkunft, funext gueltig, wartet, ready, erfolg]

/-- **Sharp sufficient law:** overwriting only one object's body leaves the entire atomic
    decision unchanged for every question on a different object, whatever its operation.
    Every nonrandom operation disjoint from the draw therefore keeps its decision, so the
    nonrandom policy and its band measure are unaffected by the overwrite. -/
theorem atomar_austauschSicht_verschieden {p : Plattform} {basis : AussenSicht} {objekt : Objekt}
    {body : List UInt8} {q : Frage} (hd : q.handle.origin.object ≠ objekt) :
    atomar p (austauschSicht basis objekt body) q = atomar p basis q := by
  apply atomar_vonSicht
  · intro o
    exact austauschSicht_herkunft basis objekt body o
  · intro z
    exact austauschSicht_gueltig basis objekt body q.endpoint z
  · exact austauschSicht_wartet p basis objekt body q
  · exact (austauschSicht_felder basis objekt body q.handle.origin.object).2.2.1
  · by_cases hsens : koerperEmpfindlich q.operation = true
    · have sichtbar := austauschSicht_erfolg_sensibel p basis objekt body q hsens
      cases op : q.operation with
      | read =>
          simpa only [AussenSicht.erfolg, op, hd, ite_false] using sichtbar
      | firmware service bytes =>
          simpa only [AussenSicht.erfolg, op, hd, ite_false] using sichtbar
      | exchange bytes =>
          simpa only [AussenSicht.erfolg, op, hd, ite_false] using sichtbar
      | write bytes | resolve name | registerRead offset | registerWrite offset value
      | waitRegister offset expected =>
          simp only [koerperEmpfindlich, op] at hsens
          cases hsens
    · exact austauschSicht_erfolg_unempfindlich p basis objekt body q
        (koerperEmpfindlich_false_of_not_true hsens)

theorem atomar_austauschSicht_unempfindlich {p : Plattform} {basis : AussenSicht} {objekt : Objekt}
    {body : List UInt8} {q : Frage} (hsens : koerperEmpfindlich q.operation = false) :
    atomar p (austauschSicht basis objekt body) q = atomar p basis q := by
  apply atomar_vonSicht
  · intro o
    exact austauschSicht_herkunft basis objekt body o
  · intro z
    exact austauschSicht_gueltig basis objekt body q.endpoint z
  · exact austauschSicht_wartet p basis objekt body q
  · exact (austauschSicht_felder basis objekt body q.handle.origin.object).2.2.1
  · exact austauschSicht_erfolg_unempfindlich p basis objekt body q hsens

/-- The actual draw policy keeps a selected question's decision when the body update
    cannot affect that question. This also holds at every cut other than the draw cut. -/
theorem austauschUmgebung_antwort_unveraendert {k : Katalog} {h : Umgebung}
    (hardware : Hardware k h) (t u : Nat) (history : AussenVerlauf)
    (objekt : Objekt) (body : List UInt8) (q : Frage)
    (selected : k.enthaelt (.endpoint q.endpoint))
    (keineWirkung : q.handle.origin.object ≠ objekt ∨ koerperEmpfindlich q.operation = false) :
    (austauschUmgebung k h t objekt body).politik.antwort u history q =
      h.politik.antwort u history q := by
  by_cases cut : u = t
  · subst u
    simp only [austauschUmgebung_antwort, if_pos rfl]
    rw [hardware.antwort t history q selected]
    exact keineWirkung.elim atomar_austauschSicht_verschieden atomar_austauschSicht_unempfindlich
  · simp only [austauschUmgebung_antwort, if_neg cut]

/-- Rewrite the body payload of a successful result, leaving errors untouched. -/
def wertBody (op : AussenOperation) (body : List UInt8) (v : AussenWert) : AussenWert :=
  match op with
  | .read => .data body
  | .firmware service bytes => .firmware service bytes body
  | .exchange bytes => .exchanged bytes body
  | _ => v

def erfolgBody (op : AussenOperation) (body : List UInt8)
    (e : Except AussenFehler AussenWert) : Except AussenFehler AussenWert :=
  match e with
  | .ok v => .ok (wertBody op body v)
  | .error err => .error err

def antwortBody (q : Frage) (body : List UInt8) (a : Antwort) : Antwort :=
  { a with result := erfolgBody q.operation body a.result }

/-- **Uniform same-object law:** an admitted question on the overwritten object keeps its
    origin, checked objects, waiting state and failure channel; only a successful body-carrying
    answer changes. `koerperEmpfindlich_iff` names those operations: `read`, `firmware` and
    `exchange`. Register reads/writes, writes, name resolution and waits cannot see the body. -/
theorem atomar_austauschSicht_sichtbar {p : Plattform} {basis : AussenSicht} {objekt : Objekt}
    {body : List UInt8} {q : Frage} (hobj : q.handle.origin.object = objekt) :
    atomar p (austauschSicht basis objekt body) q =
      match atomar p basis q with
      | .antwort a => .antwort (antwortBody q body a)
      | .warten => .warten := by
  have herkunft : ∀ o : Objekt,
      (austauschSicht basis objekt body).herkunft o = basis.herkunft o :=
    fun o => austauschSicht_herkunft basis objekt body o
  have gueltig : ∀ z : Zugriff,
      (austauschSicht basis objekt body).gueltig q.endpoint z = basis.gueltig q.endpoint z :=
    fun z => austauschSicht_gueltig basis objekt body q.endpoint z
  have wartetNeu : (austauschSicht basis objekt body).wartet p q = basis.wartet p q :=
    austauschSicht_wartet p basis objekt body q
  have gueltigNeu : q.zugriffe.all ((austauschSicht basis objekt body).gueltig q.endpoint) =
      q.zugriffe.all (basis.gueltig q.endpoint) := by
    rw [funext gueltig]
  have readyNeu : ((austauschSicht basis objekt body).objects q.handle.origin.object).ready =
      (basis.objects q.handle.origin.object).ready :=
    (austauschSicht_felder basis objekt body q.handle.origin.object).2.2.1
  have erfolgNeu : (austauschSicht basis objekt body).erfolg p q =
      erfolgBody q.operation body (basis.erfolg p q) := by
    by_cases hsens : koerperEmpfindlich q.operation = true
    · have sichtbar := austauschSicht_erfolg_sensibel p basis objekt body q hsens
      rw [sichtbar]
      simp only [hobj, ite_true]
      cases op : q.operation with
      | read =>
          simp only [AussenSicht.erfolg, op, erfolgBody, wertBody]
      | firmware service bytes =>
          simp only [AussenSicht.erfolg, op, erfolgBody, wertBody]
      | exchange bytes =>
          simp only [AussenSicht.erfolg, op, erfolgBody, wertBody]
      | write bytes | resolve name | registerRead offset | registerWrite offset value
      | waitRegister offset expected =>
          simp only [koerperEmpfindlich, op] at hsens
          cases hsens
    · rw [austauschSicht_erfolg_unempfindlich p basis objekt body q
        (koerperEmpfindlich_false_of_not_true hsens)]
      cases op : q.operation with
      | read | firmware | exchange =>
          simp only [koerperEmpfindlich, op] at hsens
          exact (hsens trivial).elim
      | write bytes | resolve name | registerRead offset | registerWrite offset value
      | waitRegister offset expected =>
          cases h : basis.erfolg p q <;> simp only [h, erfolgBody, wertBody, op]
  cases offered : p.operationAngeboten q <;>
    cases valid : q.zugriffe.all (basis.gueltig q.endpoint) <;>
    cases wait : basis.wartet p q <;>
    cases ready : (basis.objects q.handle.origin.object).ready <;>
    simp only [atomar, offered, gueltigNeu, valid, wartetNeu, wait, readyNeu, ready,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false, antwortBody, erfolgBody] <;>
    simp only [funext herkunft, erfolgNeu, erfolgBody]

end Gabbro.Core.Beobachtung
