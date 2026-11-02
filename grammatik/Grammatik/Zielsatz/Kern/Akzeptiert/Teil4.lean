/- C16: the site duty holds on the fixture -- with its full user logic.

   The fixture probe (`true`: one `Bool` return) and gate (`false`: one retired Duty,
   one empty return) meet every body obligation: `KoerperGutR` by evaluating `execEnd`
   on the two bodies (`rfl`: a `ret` returns, a `retires` is `ok`, the `ensures`
   `.var .here`/`.tru` holds of the returned value), `KeineLogik` because no `logik`
   outcome is reachable (the bodies `decide` `logikFrei`), `InvGutS` because the fixture
   owes no invariant (`invGutS_leer`), and `InvGutGrund` because neither body returns
   a reason (`gruende = 0`). With the empty lock family and the trivial axiom ensures
   this is the full `LogikPflicht` of the fixture, and `checkSitePflicht_aus` turns it
   into the `CheckSitePflicht` witness. -/
module

public import Grammatik.Zielsatz.Kern.Akzeptiert.Teil3
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtRahmenSem.Teil1
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtRahmenBeweis.Teil1
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtGanz.T2.Teil1
public import Grammatik.Nebenlaeufigkeit.Sperren.SperreFuss.Teil1
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtInv

@[expose] public section

namespace Gabbro.Grammatik

open Zielsatz

/-- The probe returns `true` with its Duty in hand: the body triple and the caller duty. -/
theorem pruef_koerperR_true (passes : Nat) : KoerperGutR pruefP passes true := by
  intro O' _ _ R _ _ σ ρ _
  refine ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩
  · have hcomp : execEnd (V := vertragVon pruefD true) O' passes R (pruefP.rumpf true) σ ρ = EndAusgang.zurueck σ true := rfl
    rw [hcomp] at hrun
    cases hrun
    rfl
  · have hcomp : execEnd (V := vertragVon pruefD true) O' passes (torRuf pruefP R) (pruefP.rumpf true) σ ρ = EndAusgang.zurueck σ true := rfl
    rw [hcomp] at hrun
    cases hrun

/-- The gate retires the Duty and returns empty: the body triple and the caller duty. -/
theorem pruef_koerperR_false (passes : Nat) : KoerperGutR pruefP passes false := by
  intro O' _ _ R _ _ σ ρ _
  refine ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩
  · have hcomp : execEnd (V := vertragVon pruefD false) O' passes R (pruefP.rumpf false) σ ρ = EndAusgang.zurueck σ () := rfl
    rw [hcomp] at hrun
    cases hrun
    rfl
  · have hcomp : execEnd (V := vertragVon pruefD false) O' passes (torRuf pruefP R) (pruefP.rumpf false) σ ρ = EndAusgang.zurueck σ () := rfl
    rw [hcomp] at hrun
    cases hrun

/-- Both bodies together, at any function of the fixture. -/
theorem pruef_koerperR (passes : Nat) (f : Bool) : KoerperGutR pruefP passes f := by
  cases f with
  | false => exact pruef_koerperR_false passes
  | true => exact pruef_koerperR_true passes

/-- Neither fixture body reaches a `logik` outcome: both are `logikFrei`. -/
theorem pruef_logikFrei_true : (pruefP.rumpf true).logikFrei = true := by decide

/-- Neither fixture body reaches a `logik` outcome: both are `logikFrei`. -/
theorem pruef_logikFrei_false : (pruefP.rumpf false).logikFrei = true := by decide

/-- The fixture meets the goal theorem's per-function obligation. -/
theorem pruef_koerperZ (passes : Nat) (f : Bool) : KoerperGutZ pruefP passes (axWahr pruefD) f := by
  refine ⟨koerperGutRQ_of_R _ (pruef_koerperR passes f), ?_⟩
  cases f with
  | false => exact logikFrei_keineLogik passes _ pruef_logikFrei_false
  | true => exact logikFrei_keineLogik passes _ pruef_logikFrei_true

/-- The fixture meets the lock-invariant obligation: the Duty threads through `SperrInv.leer`. -/
theorem pruef_koerperS (passes : Nat) (f : Bool) :
    KoerperGutS pruefP passes (axWahr pruefD) (SperrInv.leer pruefD) f :=
  koerperGutS_leer (pruef_koerperZ passes f)

/-- Neither fixture body returns a reason: both signatures are reason-free. -/
theorem pruef_grund (passes : Nat) (f : Bool) :
    InvGutGrund pruefP passes (axWahr pruefD) (SperrInv.leer pruefD) f := by
  intro O' _ _ _ U _ R _ _ σ ρ _ σ' r hrun
  have h0 : pruefD.gruende f = 0 := by cases f <;> rfl
  have h := r.isLt
  rw [h0] at h
  omega

/-- **The fixture's full user logic**: both bodies at every budget, no owed invariants at
    value or reason exits, the empty lock family and the trivial axiom ensures. -/
theorem pruef_logik (passes : Nat) :
    LogikPflicht (D := pruefD) pruefP (SperrInv.leer pruefD) (axWahr pruefD) :=
  ⟨fun p f => ⟨pruef_koerperS p f, invGutS_leer rfl f, pruef_grund p f⟩, (fun _ _ _ _ => rfl), axEnsLokal_wahr⟩

/-- **The site duty holds on the fixture**: probe and gate meet their body duties, tied to
    the same Duty by the admitted expansion -- with the full `LogikPflicht` proof above. -/
theorem checkSitePflicht_zeuge (passes : Nat) :
    CheckSitePflicht pruefP (axWahr pruefD) (SperrInv.leer pruefD) passes pruefC :=
  checkSitePflicht_aus checkAdmission_zeuge (pruef_logik passes) (List.Mem.head _)

end Gabbro.Grammatik
