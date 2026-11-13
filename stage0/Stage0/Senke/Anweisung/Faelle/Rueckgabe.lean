/- End-block simulation and its structural operations. -/
module
public import Stage0.Senke.Anweisung.Simulation
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration} {L : Lay D}

/-- What the body's code from `t` does for G's outcome of an end block: `zurueck` and `why` return (`RetZR`,
    `RetWhyR`) under the pending releases `sc` of the enclosing `locks` scopes, `logik` stops with its code, `leave` and
    `next` reach the loop's targets `eL` and `eN`. -/
def Ret (L : Lay D) (P : Programm D) (f : D.Fn) (σ0 : World D) (ρ0 : Env D (D.params f)) (fp : Runner.W) (lo K : Nat)
    (pr : List Nat) (rp cfp : Runner.W) (t : T) (m : Runner.Mem) (eL eN : Runner.W) {l : Bool} {Γ : Ctx}
    (o : EndAusgang (vertragVon D f) l Γ) (reserved : Nat := 0) (sc : List D.Lock := []) : Prop :=
  match o with
  | .zurueck σ' v => RetZR L P f σ0 ρ0 fp K rp cfp sc t m σ' v
  | .logik e => Stops t m (logikCode e)
  | .hardware h => Stops t m (hwCode h)
  | .leave _ σ' ρ' => Reach L fp lo K pr t m eL σ' ρ' reserved
  | .next _ σ' ρ' => Reach L fp lo K pr t m eN σ' ρ' reserved
  | .why σ' r => RetWhyR L f fp K rp cfp sc t m σ' r

section
variable {L : Lay D} {P : Programm D} {f : D.Fn} {σ0 : World D} {ρ0 : Env D (D.params f)} {fp : Runner.W} {lo K : Nat}
  {reserved : Nat} {sc : List D.Lock} {pr : List Nat} {rp cfp : Runner.W} {l : Bool} {Γ : Ctx}

theorem Ret.prefix {o : EndAusgang (vertragVon D f) l Γ} {t0 t : T} {m0 m : Runner.Mem} {eL eN : Runner.W}
    (hl : 2 ≤ lo) (h : Star t0 m0 t m) (ha : AgreeW L fp lo K m0 m) (hk : Keeps fp pr m0 m) (hs : Ret L P f σ0 ρ0 fp lo K pr rp cfp t m eL eN o reserved sc) :
    Ret L P f σ0 ρ0 fp lo K pr rp cfp t0 m0 eL eN o reserved sc := by
  cases o with
  | zurueck σ' v => exact RetZR.prefix h (ha.mono hl) hs
  | logik e => exact Stops.prefix h hs
  | hardware e => exact Stops.prefix h hs
  | leave _ σ' ρ' => exact Reach.prefix h ha hk hs
  | next _ σ' ρ' => exact Reach.prefix h ha hk hs
  | why σ' r => exact RetWhyR.prefix h (ha.mono hl) hs

theorem Ret.cast {o : EndAusgang (vertragVon D f) l Γ} {t t' : T} {m : Runner.Mem} {eL eN eL' eN' : Runner.W}
    (hs : Ret L P f σ0 ρ0 fp lo K pr rp cfp t m eL eN o reserved sc) (h : t = t') (h3 : eL = eL') (h4 : eN = eN') :
    Ret L P f σ0 ρ0 fp lo K pr rp cfp t' m eL' eN' o reserved sc := by
  subst h h3 h4; exact hs

theorem Ret.schrumpf {τ : Ty} {o : EndAusgang (vertragVon D f) l (τ :: Γ)} {t : T} {m : Runner.Mem} {eL eN : Runner.W}
    (hs : Ret L P f σ0 ρ0 fp lo K pr rp cfp t m eL eN o reserved sc) : Ret L P f σ0 ρ0 fp lo K pr rp cfp t m eL eN o.schrumpf reserved sc := by
  cases o with
  | leave _ σ ρ => obtain ⟨m', s, a, en, hw, kp⟩ := hs; exact ⟨m', s, a, envAt_tail en, hw, kp⟩
  | next _ σ ρ => obtain ⟨m', s, a, en, hw, kp⟩ := hs; exact ⟨m', s, a, envAt_tail en, hw, kp⟩
  | zurueck | logik | why | hardware => exact hs

end

/-- End-block outcomes keep their return or loop target when used as an else statement. -/
theorem Ret.zuAusgang {P : Programm D} {f : D.Fn} {σ0 : World D}
    {ρ0 : Env D (D.params f)} {fp : Runner.W} {lo K : Nat} {reserved : Nat} {sc : List D.Lock} {pr : List Nat}
    {rp cfp : Runner.W} {t : T} {m : Runner.Mem} {e eL eN : Runner.W} {l : Bool} {Γ : Ctx}
    {o : EndAusgang (vertragVon D f) l Γ}
    (h : Ret L P f σ0 ρ0 fp lo K pr rp cfp t m eL eN o reserved sc) :
    Sim L P f σ0 ρ0 rp cfp fp lo K pr t m e eL eN o.zuAusgang reserved sc := by
  cases o <;> exact h

end Gabbro.Stage0.Senke
