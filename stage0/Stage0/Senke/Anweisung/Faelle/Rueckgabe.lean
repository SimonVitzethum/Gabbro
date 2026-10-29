/- End-block simulation and its structural operations. -/
import Stage0.Senke.Anweisung.Simulation

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration}

/-- What the body's code from `t` does for G's outcome of an end block: `zurueck` returns (`RetZ`), `logik` stops
    with its code, `leave` and `next` reach the loop's targets `eL` and `eN`. -/
def Ret (L : Lay D) (P : Programm D) (f : D.Fn) (σ0 : World D) (ρ0 : Env D (D.params f)) (fp : Runner.W) (lo K : Nat)
    (pr : List Nat) (rp cfp : Runner.W) (t : T) (m : Runner.Mem) (eL eN : Runner.W) {l : Bool} {Γ : Ctx} :
    EndAusgang (vertragVon D f) l Γ → Prop
  | .zurueck σ' v => RetZ L P f σ0 ρ0 fp K rp cfp t m σ' v
  | .logik e => Stops t m (logikCode e)
  | .hardware h => Stops t m (hwCode h)
  | .leave _ σ' ρ' => Reach L fp lo K pr t m eL σ' ρ'
  | .next _ σ' ρ' => Reach L fp lo K pr t m eN σ' ρ'
  | _ => False

section
variable {L : Lay D} {P : Programm D} {f : D.Fn} {σ0 : World D} {ρ0 : Env D (D.params f)} {fp : Runner.W} {lo K : Nat}
  {pr : List Nat} {rp cfp : Runner.W} {l : Bool} {Γ : Ctx}

theorem Ret.prefix {o : EndAusgang (vertragVon D f) l Γ} {t0 t : T} {m0 m : Runner.Mem} {eL eN : Runner.W}
    (hl : 2 ≤ lo) (h : Star t0 m0 t m) (ha : AgreeW L fp lo K m0 m) (hk : Keeps fp pr m0 m) (hs : Ret L P f σ0 ρ0 fp lo K pr rp cfp t m eL eN o) :
    Ret L P f σ0 ρ0 fp lo K pr rp cfp t0 m0 eL eN o := by
  cases o with
  | zurueck σ' v => exact RetZ.prefix h (ha.mono hl) hs
  | logik e => exact Stops.prefix h hs
  | hardware e => exact Stops.prefix h hs
  | leave _ σ' ρ' => exact Reach.prefix h ha hk hs
  | next _ σ' ρ' => exact Reach.prefix h ha hk hs
  | why => exact hs

theorem Ret.cast {o : EndAusgang (vertragVon D f) l Γ} {t t' : T} {m : Runner.Mem} {eL eN eL' eN' : Runner.W}
    (hs : Ret L P f σ0 ρ0 fp lo K pr rp cfp t m eL eN o) (h : t = t') (h3 : eL = eL') (h4 : eN = eN') :
    Ret L P f σ0 ρ0 fp lo K pr rp cfp t' m eL' eN' o := by
  subst h h3 h4; exact hs

theorem Ret.schrumpf {τ : Ty} {o : EndAusgang (vertragVon D f) l (τ :: Γ)} {t : T} {m : Runner.Mem} {eL eN : Runner.W}
    (hs : Ret L P f σ0 ρ0 fp lo K pr rp cfp t m eL eN o) : Ret L P f σ0 ρ0 fp lo K pr rp cfp t m eL eN o.schrumpf := by
  cases o with
  | leave _ σ ρ => obtain ⟨m', s, a, en, hw, kp⟩ := hs; exact ⟨m', s, a, envAt_tail en, hw, kp⟩
  | next _ σ ρ => obtain ⟨m', s, a, en, hw, kp⟩ := hs; exact ⟨m', s, a, envAt_tail en, hw, kp⟩
  | zurueck | logik | why | hardware => exact hs

end

end Gabbro.Stage0.Senke
