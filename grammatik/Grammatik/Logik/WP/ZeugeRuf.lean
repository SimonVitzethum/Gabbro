import Grammatik.Logik.WP.Regeln

/-!
# GabbroV over machine G: a recursive function, total correctness

`f(n : 0 .. 5) -> 0 .. 5 { if n == 0 { return 0; } let m = narrow n - 1 to 0 .. 5 else { return 0; };
let r = f(m); return r; }`. `f_korrekt`: at every depth above `n`, the call `f(n)` answers NORMALLY with `0` --
through `ruf_mass` (the measure is `n`) and `rufAt_succ_wp`, with the recursive call taken from the induction
hypothesis.
-/

namespace Gabbro.Grammatik.WP.ZeugeRuf

open Gabbro.Grammatik Gabbro.Grammatik.WP

/-- The signature of `f`: one parameter in `0 .. 5`, a result in `0 .. 5`, no effects. -/
def sigF : Signatur Empty Empty Empty Empty where
  params := [.int 0 5]
  erg := some (.int 0 5)
  gruende := 0
  haelt := []
  schreibt := fun _ => false
  gschreibt := fun _ => false
  konsumiert := []
  produziert := []
  boden := none

/-- One function, nothing else. -/
@[reducible] def rD : Deklaration where
  Tab := Empty
  decTab := inferInstance
  count := fun t => t.elim
  Feld := fun t => t.elim
  decFeld := fun t => t.elim
  typ := fun t => t.elim
  erlaubt := fun t => t.elim
  tabNr := fun _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun g => g.elim
  nutzlast := fun g => g.elim
  atomar := fun g => g.elim
  geteilt := fun t => t.elim
  ggeteilt := fun g => g.elim
  Lock := Empty
  decLock := inferInstance
  rang := fun L => L.elim
  maskiert := fun L => L.elim
  Marke := Empty
  decMarke := inferInstance
  stufen := fun m => m.elim
  braucht := fun t => t.elim
  gbraucht := fun g => g.elim
  eigner := fun t => t.elim
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ => sigF
  eigner_nie_erzeugt := fun _ t => t.elim
  Inv := Empty
  traeger := fun i => i.elim
  invs := []
  Ax := Empty
  aparams := fun a => a.elim
  aerg := fun a => a.elim
  aschreibt := fun a => a.elim
  agschreibt := fun a => a.elim
  Reg := Empty
  rtyp := fun r => r.elim
  rklasse := fun r => r.elim
  spiegel := fun r => r.elim
  rzusage := fun r => r.elim
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t => t.elim
  invarianten_gehalten := fun _ i => i.elim
  ggeteilt_bewacht := fun g => g.elim

abbrev V : Vertrag rD := vertragVon rD ()

theorem hp : RufPasst rD V (rD.signatur ()) [] where
  hw := fun t => t.elim
  hg := fun g => g.elim
  hk := ⟨[], List.Perm.refl [], List.Sublist.refl []⟩
  hh := fun _ h => by cases h

def null {Γ : Ctx} : Expr rD Γ [] (.int 0 5) := .widen (by decide) (by decide) (.lit 0)

/-- `let r = f(m); return r;` -/
def ruf : Block rD V false [.int 0 5, .int 0 5] [] [] :=
  .bindCall () (.cons (.var .here) .nil) rfl hp rfl (.cons (.ret (.val (.var .here)) (List.Perm.refl _)) .nil)

/-- `let m = narrow n - 1 to 0 .. 5 else { return 0; }; …` -/
def sonst : Block rD V false [.int 0 5] [] [] :=
  .narrow (.sub (.var .here) (.lit 1)) 0 5 (.ret (.val null) (List.Perm.refl _)) ruf

/-- The body. -/
def rumpf : Endblock rD V false [.int 0 5] [] :=
  .cons (.ite (.eq (.var .here) (.lit 0)) (.cons (.ret (.val null) (List.Perm.refl _)) .nil) sonst)
    (.ret (.val null) (List.Perm.refl _))

def P : Programm rD where
  invariante := fun i => i.elim
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf := fun _ => rumpf

/-- The parameter of a call. -/
def arg (ρ : Env rD (rD.params ())) : Int := (ρ.get .here).n

/-- The specification: a normal answer `0`. -/
def S : Spez rD := fun _ _ _ out => ∃ (σ' : World rD) (v : ErgVal rD (rD.erg ())), out = .ok σ' v ∧ v.n = 0

/-- The measure: the parameter. -/
def μ : ∀ f : rD.Fn, World rD → Env rD (rD.params f) → Nat := fun _ _ ρ => (arg ρ).toNat

variable (O : Orakel rD) (passes : Nat) {N : Int}

/-- The specification of the recursive call inside the body: below `N`, a normal answer `0`. -/
def Unter (N : Int) : Spez rD := fun _ _ a out =>
  arg a < N → ∃ (σ' : World rD) (v : ErgVal rD (rD.erg ())), out = .ok σ' v ∧ v.n = 0

/-- **The body**, for any call meaning that answers `0` below the argument: it returns `0`. -/
theorem rumpf_lauf (R : ∀ f : rD.Fn, World rD → Env rD (rD.params f) → RufAusgang f)
    (hR : Erfuellt (Unter N) R) (σ : World rD) (x : Zahl 0 5) (hx : x.n ≤ N) :
    ∃ (σ' : World rD) (v : ErgVal rD V.erg), execEnd O passes R rumpf σ (.cons x .nil) = .zurueck σ' v ∧
      v.n = 0 := by
  show wpE O passes R rumpf (fun eo => ∃ (σ' : World rD) (v : ErgVal rD V.erg), eo = .zurueck σ' v ∧ v.n = 0)
    σ (.cons x .nil)
  rw [rumpf, wpE_cons, wpS_ite]
  split
  · rw [wpB_cons]
    exact ⟨_, _, rfl, rfl⟩
  · rename_i hc
    have h0 : x.n ≠ 0 := by
      intro h; apply hc; exact decide_eq_true h
    have hx0 := x.lo_le
    have hx5 := x.le_hi
    rw [sonst, wpB_narrow]
    split
    · rw [ruf]
      apply wpB_bindCall_spez O passes R hR
      intro out hout
      obtain ⟨σ', v, rfl, hv⟩ := hout (show x.n - 1 < N by omega)
      simp only [bindRufB]
      exact ⟨_, _, rfl, hv⟩
    · rename_i hn
      exact absurd ⟨show (0 : Int) ≤ x.n - 1 by omega, show x.n - 1 ≤ (5 : Int) by omega⟩ hn

/-- **`f(n)` answers normally with `0` at every depth above `n`.** -/
theorem f_korrekt : ∀ n f σ ρ, μ f σ ρ < n → S f σ ρ (rufAt P O passes n f σ ρ) := by
  apply ruf_mass P O passes S μ
  intro n ih f σ ρ hμ
  apply rufAt_succ_wp
  · intro h; simp only [wahr?, P, eval, Bool.true_eq_false] at h
  · intro _
    cases ρ with
    | cons x rest =>
      cases rest
      have hR : Erfuellt (Unter (n : Int)) (rufAt P O passes n) := by
        intro g σ' a ha
        obtain ⟨σ'', v, h1, h2⟩ := ih g σ' a (by
          have := (a.get .here).lo_le; simp only [μ, arg] at ha ⊢; omega)
        exact ⟨σ'', v, h1, h2⟩
      have hx : x.n ≤ (n : Int) := by
        change (x.n).toNat < n + 1 at hμ; have := x.lo_le; omega
      obtain ⟨σ', v, hrun, hv⟩ := rumpf_lauf O passes (rufAt P O passes n) hR (rufEintritt P () σ) x hx
      show S () σ (.cons x .nil) (rufNach P () (rufEintritt P () σ) (.cons x .nil)
        (execEnd O passes (rufAt P O passes n) rumpf (rufEintritt P () σ) (.cons x .nil)))
      erw [hrun]
      exact ⟨_, v, rfl, hv⟩

#print axioms f_korrekt

end Gabbro.Grammatik.WP.ZeugeRuf
