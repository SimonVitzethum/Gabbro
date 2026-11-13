/-
  File:      stage0/Stage0/Senke/Bild/Gleich/RufAtUmkehr.lean
  Subject:   **`rufRumpf` against `rufAt` under the contract duty** (package P2 of the closed calls of the image
             theorem, the converse direction; the (i) of `EmittedZiel`). The short direction (`RufAt.lean`) relates
             the two handlers up to `rufAt`'s own contract failures. Where those cannot happen the relation is exact
             in both directions: an `ok` (a reason) of the body run that machine G realises is an `ok` (the same
             reason) of `rufAt` with the same value and a `≈` world (`rufRumpf_ok_rufAt`, `rufRumpf_why_rufAt`), and
             every other outcome is the same on both sides (`rufAt_rufRumpf_genau`, error set empty).

             "No contract failure at this call" (`Vertragsfrei`) is what the user duty gives:
             * per call, from the one-unfolding duty -- `requires` at entry, no `logik` of the body, `ensures` and the
               owed invariants at every return (`vertragsfrei_schritt`, from `rufSchritt_nicht_logik`);
             * from the discharge of the whole user obligation (`NurAbstieg`, proved by `rufAt_nurAbstieg` from
               `KoerperGutS`/`InvGutS`) at a disciplined entry meeting the callee's `requires`
               (`vertragsfrei_nurAbstieg`), closed in `rufAt_rufRumpf_pflicht`;
             * everywhere and at every depth for contracts that are valid formulas (`VertragGueltig`), where the
               short-direction induction runs with the empty error set (`rufAt_rufRumpf_gueltig`).
             All of it carries `Leseblind O` (lead decision: the trace is ghost state, real answers do not depend on
             read events; it is the named oracle property `LeseblindOK`, `Ruf/RufOkGleich.lean`).
-/
module
public import Stage0.Senke.Bild.Gleich.RufAt
public import Grammatik.Logik.Ruf.RufLogika
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik

set_option linter.unusedSectionVars false

variable {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}

/-! ## 1. No contract failure at one call -/

/-- **`rufAt` fails none of its own contract checks at this call** (at any nesting depth inside it). -/
def Vertragsfrei (P : Programm D) (O : Orakel D) (passes n : Nat) (g : D.Fn) (σ : World D)
    (ρ : Env D (D.params g)) : Prop :=
  ∀ e : Logik D, rufAt P O passes n g σ ρ = .logik e → ¬ VertragMarke (.logik e)

/-- **The exact relation**: where `rufAt` fails no contract check, `rufAt` and `rufRumpf` give the same outcome up to
    `≈`, with no early failure on either side. -/
theorem rufAt_rufRumpf_genau (hO : Leseblind O) {n : Nat} {g : D.Fn} {σ σ' : World D}
    {ρ : Env D (D.params g)} (hV : Vertragsfrei P O passes n g σ ρ) (hσ : WeltGleich σ σ') :
    RufLG (fun _ => False) (rufAt P O passes n g σ ρ) (rufRumpf P O passes n g σ' ρ) := by
  have h := rufAt_rufRumpf_lg (P := P) (O := O) (passes := passes) hO n g σ σ' ρ hσ
  unfold Vertragsfrei at hV
  generalize rufAt P O passes n g σ ρ = a₁ at h hV ⊢
  generalize rufRumpf P O passes n g σ' ρ = a₂ at h ⊢
  cases h with
  | ok hw => exact .ok hw
  | why hw => exact .why hw
  | logik e => exact .logik e
  | hardware e => exact .hardware e
  | frueh hm => exact absurd hm (hV _ rfl)
  | fruehH hm => cases hm

/-- **An `ok` of the body run is an `ok` of `rufAt`** with the same value and a `≈` world, where `rufAt` fails no
    contract check. -/
theorem rufRumpf_ok_rufAt (hO : Leseblind O) {n : Nat} {g : D.Fn} {σ σ' σ₂ : World D}
    {ρ : Env D (D.params g)} {v : ErgVal D (D.erg g)} (hV : Vertragsfrei P O passes n g σ ρ)
    (hσ : WeltGleich σ σ') (h : rufRumpf P O passes n g σ' ρ = .ok σ₂ v) :
    ∃ σ₁, rufAt P O passes n g σ ρ = .ok σ₁ v ∧ WeltGleich σ₁ σ₂ := by
  have hg := rufAt_rufRumpf_genau hO hV hσ
  rw [h] at hg
  generalize rufAt P O passes n g σ ρ = a at hg ⊢
  cases hg with
  | ok hw => exact ⟨_, rfl, hw⟩
  | frueh hm => exact False.elim hm
  | fruehH hm => exact False.elim hm

/-- **A reason of the body run is the same reason of `rufAt`**, with a `≈` world, where `rufAt` fails no contract
    check. -/
theorem rufRumpf_why_rufAt (hO : Leseblind O) {n : Nat} {g : D.Fn} {σ σ' σ₂ : World D}
    {ρ : Env D (D.params g)} {r : Fin (D.gruende g)} (hV : Vertragsfrei P O passes n g σ ρ)
    (hσ : WeltGleich σ σ') (h : rufRumpf P O passes n g σ' ρ = .why σ₂ r) :
    ∃ σ₁, rufAt P O passes n g σ ρ = .why σ₁ r ∧ WeltGleich σ₁ σ₂ := by
  have hg := rufAt_rufRumpf_genau hO hV hσ
  rw [h] at hg
  generalize rufAt P O passes n g σ ρ = a at hg ⊢
  cases hg with
  | why hw => exact ⟨_, rfl, hw⟩
  | frueh hm => exact False.elim hm
  | fruehH hm => exact False.elim hm

/-! ## 2. Where `Vertragsfrei` comes from: the user duty -/

/-- **The one-unfolding duty**: `requires` at entry, no `logik` outcome of the body under `rufAt`, `ensures` and the
    owed invariants at every return of the body. -/
theorem vertragsfrei_schritt {n : Nat} {g : D.Fn} {σ : World D} {ρ : Env D (D.params g)}
    (hq : ReqAmEintritt P g σ ρ)
    (hbody : ∀ e : Logik D,
      execEnd (V := vertragVon D g) O passes (rufAt P O passes n) (P.rumpf g)
        (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρ ≠ .logik e)
    (hens : ∀ (σ₂ : World D) (v : ErgVal D (D.erg g)),
      execEnd (V := vertragVon D g) O passes (rufAt P O passes n) (P.rumpf g)
        (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρ = .zurueck σ₂ v →
        EnsAmRueck P g (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) σ₂ ρ v)
    (hinv : ∀ (σ₂ : World D) (v : ErgVal D (D.erg g)),
      execEnd (V := vertragVon D g) O passes (rufAt P O passes n) (P.rumpf g)
        (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρ = .zurueck σ₂ v →
        InvAmRueck P g σ₂) :
    Vertragsfrei P O passes (n + 1) g σ ρ := by
  intro e he _
  rw [rufAt_succ_eq] at he
  exact rufSchritt_nicht_logik P O passes (rufAt P O passes n) g σ ρ hq hbody hens hinv e he

/-- **From the discharge of the user obligation**: where `rufAt`'s only `logik` outcome is the depth residue
    (`NurAbstieg`), a disciplined entry meeting the callee's `requires` fails no contract check. -/
theorem vertragsfrei_nurAbstieg {n : Nat} (hN : NurAbstieg P O passes n) {g : D.Fn} {σ : World D}
    {ρ : Env D (D.params g)}
    (hh : HeldB (D.signatur g).boden (Signatur.anfang D (D.signatur g)) σ.haelt)
    (hq : ReqAmEintritt P g σ ρ) : Vertragsfrei P O passes n g σ ρ := by
  intro e he hm
  obtain ⟨k, hk⟩ := hN g σ ρ e hh hq he
  subst hk
  exact nicht_vertragMarke_abstieg k hm

/-- **(i) OF `EmittedZiel`: `rufAt ≈ rufRumpf` UNDER THE USER DUTY.** Under the user's own obligation
    (`KoerperGutS`, `InvGutS`), an oracle in the named class that is read-blind, and bodies without `locks`: at a
    disciplined entry meeting the callee's `requires`, from `≈` worlds, `rufAt` and the body run of machine G give the
    same outcome up to `≈` -- in both directions, with no early failure on either side. -/
theorem rufAt_rufRumpf_pflicht {Q : AxEns D} {S : SperrInv D} {U : Umwelt D}
    (hTO : TreuO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hU : HavocOk S U)
    (hlocks : ∀ f : D.Fn, (P.rumpf f).ohneLocks = true)
    (hK : ∀ f : D.Fn, KoerperGutS P passes Q S f) (hI : ∀ f : D.Fn, InvGutS P passes Q S f)
    (hS : ScopesOkProg P) (hO : Leseblind O) (n : Nat) {g : D.Fn} {σ σ' : World D}
    {ρ : Env D (D.params g)}
    (hh : HeldB (D.signatur g).boden (Signatur.anfang D (D.signatur g)) σ.haelt)
    (hq : ReqAmEintritt P g σ ρ) (hσ : WeltGleich σ σ') :
    RufLG (fun _ => False) (rufAt P O passes n g σ ρ) (rufRumpf P O passes n g σ' ρ) :=
  rufAt_rufRumpf_genau hO
    (vertragsfrei_nurAbstieg
      (rufAt_nurAbstieg (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (U := U)
        hTO hRL hQ hU hlocks hK hI hS n) hh hq) hσ

/-! ## 3. Valid contracts: the exact relation at every depth -/

/-- **Contracts that are valid formulas**: every `requires`, `ensures` and invariant holds in every world. -/
structure VertragGueltig (P : Programm D) : Prop where
  requires : ∀ (g : D.Fn) (σ : World D) (ρ : Env D (D.params g)), wahr? (eval σ (P.requires g) σ ρ) = true
  ensures : ∀ (g : D.Fn) (σ₀ σ : World D) (ρ : Env D (D.params g)) (v : ErgVal D (D.erg g)),
    wahr? (eval σ₀ (P.ensures g) σ (ergEnv (D.erg g) v ρ)) = true
  invariante : ∀ (i : D.Inv) (σ : World D), wahr? (eval σ (P.invariante i) σ .nil) = true

/-- **Under valid contracts `rufAt ≈ rufRumpf` exactly**, at every depth and in every world: the short-direction
    induction with the empty error set. -/
theorem rufAt_rufRumpf_gueltig (hP : VertragGueltig P) (hO : Leseblind O) (n : Nat) :
    HandlerLG (fun _ => False) (rufAt P O passes n) (rufRumpf P O passes n) :=
  rufAt_rufRumpf_unter (fun _ => False) hO
    (fun g σ ρ hq => absurd ((hP.requires g σ ρ).symm.trans hq) (by decide))
    (fun g σ₀ σ ρ v hq => absurd ((hP.ensures g σ₀ σ ρ v).symm.trans hq) (by decide))
    (fun i σ hq => absurd ((hP.invariante i σ).symm.trans hq) (by decide)) n

#print axioms rufAt_rufRumpf_genau
#print axioms rufAt_rufRumpf_pflicht
#print axioms rufAt_rufRumpf_gueltig

end Gabbro.Stage0.Senke.BildLauf
