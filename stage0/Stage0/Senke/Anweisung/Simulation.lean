/-
  File:      stage0/Stage0/Senke/Anweisung/Simulation.lean
  Subject:   What the code of a statement does for each outcome of machine G (`Sim`): `ok` reaches the end, `leave`
             and `next` the loop's targets (`Reach`: the new environment in the frame, the new world in memory, the
             protected slots kept), `zurueck` returns (`RetZ`), `logik` stops. The targets of a part of the code
             against the whole (`tgt_eq`), and `jmp` to a target (`jmp_reach`).
-/
import Stage0.Senke.Rueckkehr

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

variable {D : Deklaration} {V : Vertrag D}

/-- The code from `t` reaches `e` with the environment `ρ'` in the frame and the world `σ'` in memory, changing no
    slot below `lo`. -/
abbrev Reach (L : Lay D) {Γ : Ctx} (fp : Runner.W) (lo K : Nat) (pr : List Nat) (t : T) (m : Runner.Mem)
    (e : Runner.W) (σ' : World D) (ρ' : Env D Γ) : Prop :=
  ∃ m', Star t m ⟨e, fp⟩ m' ∧ Agree fp lo K m m' ∧ EnvAt m' fp ρ' ∧ WeltAt m' L σ' ∧ Keeps fp pr m m'

/-- What the code from `t` does for G's outcome `o` in the body of `f`: `ok` reaches the end `e`, `leave` and `next`
    the loop's targets `eL` and `eN`, `zurueck` returns (`RetZ`), `logik` stops with its code. -/
def Sim (L : Lay D) (P : Programm D) (f : D.Fn) (σ0 : World D) (ρ0 : Env D (D.params f)) (rp cfp : Runner.W)
    {l : Bool} {Γ : Ctx} (fp : Runner.W) (lo K : Nat) (pr : List Nat) (t : T) (m : Runner.Mem) (e eL eN : Runner.W) :
    Ausgang (vertragVon D f) l Γ → Prop
  | .ok σ' ρ' => Reach L fp lo K pr t m e σ' ρ'
  | .leave _ σ' ρ' => Reach L fp lo K pr t m eL σ' ρ'
  | .next _ σ' ρ' => Reach L fp lo K pr t m eN σ' ρ'
  | .zurueck σ' v => RetZ L P f σ0 ρ0 fp K rp cfp t m σ' v
  | .logik c => Stops t m (logikCode c)
  | _ => False

section
variable {L : Lay D} {P : Programm D} {f : D.Fn} {σ0 : World D} {ρ0 : Env D (D.params f)} {rp cfp : Runner.W}
  {l : Bool} {Γ : Ctx} {fp : Runner.W} {lo K : Nat} {pr : List Nat}

theorem Reach.prefix {t0 t : T} {m0 m : Runner.Mem} {e : Runner.W} {σ' : World D} {ρ' : Env D Γ}
    (h : Star t0 m0 t m) (ha : Agree fp lo K m0 m) (hk : Keeps fp pr m0 m) (hs : Reach L fp lo K pr t m e σ' ρ') :
    Reach L fp lo K pr t0 m0 e σ' ρ' := by
  obtain ⟨m', s, a, en, hw, kp⟩ := hs; exact ⟨m', h.trans s, ha.trans a, en, hw, hk.trans kp⟩

theorem Sim.prefix {o : Ausgang (vertragVon D f) l Γ} {t0 t : T} {m0 m : Runner.Mem} {e eL eN : Runner.W}
    (hl : FB ≤ lo) (h : Star t0 m0 t m) (ha : Agree fp lo K m0 m) (hk : Keeps fp pr m0 m)
    (hs : Sim L P f σ0 ρ0 rp cfp fp lo K pr t m e eL eN o) : Sim L P f σ0 ρ0 rp cfp fp lo K pr t0 m0 e eL eN o := by
  cases o with
  | ok σ ρ => exact Reach.prefix h ha hk hs
  | leave _ σ ρ => exact Reach.prefix h ha hk hs
  | next _ σ ρ => exact Reach.prefix h ha hk hs
  | zurueck σ' v =>
    have hFB3 : FB = 3 := rfl
    exact RetZ.prefix h (ha.mono (by omega)) hs
  | logik c => exact Stops.prefix h hs
  | why | hardware => exact hs

/-- `ok` goes on from `e1` to `e2`; `leave` and `next` keep their targets. -/
theorem Sim.cont {o : Ausgang (vertragVon D f) l Γ} {t : T} {m : Runner.Mem} {e1 e2 eL eN eL' eN' : Runner.W}
    (hs : Sim L P f σ0 ρ0 rp cfp fp lo K pr t m e1 eL eN o)
    (hj : ∀ m', Agree fp lo K m m' → Star ⟨e1, fp⟩ m' ⟨e2, fp⟩ m') (hL : eL = eL') (hN : eN = eN') :
    Sim L P f σ0 ρ0 rp cfp fp lo K pr t m e2 eL' eN' o := by
  subst hL hN
  cases o with
  | ok σ ρ => obtain ⟨m', s, a, en, hw, kp⟩ := hs; exact ⟨m', s.trans (hj m' a), a, en, hw, kp⟩
  | logik c => exact hs
  | zurueck | why | leave | next | hardware => exact hs

theorem Sim.cast {o : Ausgang (vertragVon D f) l Γ} {t t' : T} {m : Runner.Mem} {e e' eL eN eL' eN' : Runner.W}
    (hs : Sim L P f σ0 ρ0 rp cfp fp lo K pr t m e eL eN o) (h1 : t = t') (h2 : e = e') (h3 : eL = eL') (h4 : eN = eN') :
    Sim L P f σ0 ρ0 rp cfp fp lo K pr t' m e' eL' eN' o := by subst h1 h2 h3 h4; exact hs

/-- An outcome other than `ok` keeps its meaning under other `ok` targets. -/
theorem Sim.ziel {o : Ausgang (vertragVon D f) l Γ} {t : T} {m : Runner.Mem} {e e' eL eN eL' eN' : Runner.W}
    (hs : Sim L P f σ0 ρ0 rp cfp fp lo K pr t m e eL eN o) (hok : ∀ σ ρ, o ≠ .ok σ ρ) (h3 : eL = eL') (h4 : eN = eN') :
    Sim L P f σ0 ρ0 rp cfp fp lo K pr t m e' eL' eN' o := by
  subst h3 h4
  cases o with
  | ok σ ρ => exact absurd rfl (hok σ ρ)
  | logik c => exact hs
  | zurueck | why | leave | next | hardware => exact hs

theorem Sim.schrumpf {τ : Ty} {o : Ausgang (vertragVon D f) l (τ :: Γ)} {t : T} {m : Runner.Mem}
    {e eL eN : Runner.W} (hs : Sim L P f σ0 ρ0 rp cfp fp lo K pr t m e eL eN o) :
    Sim L P f σ0 ρ0 rp cfp fp lo K pr t m e eL eN o.schrumpf := by
  cases o with
  | ok σ ρ => obtain ⟨m', s, a, en, hw, kp⟩ := hs; exact ⟨m', s, a, envAt_tail en, hw, kp⟩
  | leave _ σ ρ => obtain ⟨m', s, a, en, hw, kp⟩ := hs; exact ⟨m', s, a, envAt_tail en, hw, kp⟩
  | next _ σ ρ => obtain ⟨m', s, a, en, hw, kp⟩ := hs; exact ⟨m', s, a, envAt_tail en, hw, kp⟩
  | logik c => exact hs
  | zurueck | why | hardware => exact hs

end

/-- A target `x` bytes from the end of the whole code, seen from the end of a piece `n` instructions earlier. -/
theorem tgt_eq {p : Runner.W} {a b n : Nat} {x : Int} (h : a + 16 * n = b) :
    p + BitVec.ofNat 64 a + BitVec.ofInt 64 (x + 16 * (n : Int)) = p + BitVec.ofNat 64 b + BitVec.ofInt 64 x := by
  have e : BitVec.ofInt 64 (16 * (n : Int)) = BitVec.ofNat 64 (16 * n) := by
    rw [show (16 * (n : Int)) = ((16 * n : Nat) : Int) by omega, BitVec.ofInt_natCast]
  rw [BitVec.ofInt_add, e, ← h, ← addr_norm]
  ac_rfl

theorem tgt_eq0 {p : Runner.W} {a b : Nat} {x : Int} (h : a = b) :
    p + BitVec.ofNat 64 a + BitVec.ofInt 64 x = p + BitVec.ofNat 64 b + BitVec.ofInt 64 x := by rw [h]

/-- `jmp` to a target `x` bytes after the end of the one instruction. -/
theorem jmp_reach {L : Lay D} {Γ : Ctx} {m : Runner.Mem} {pc fp : Runner.W} {lo K : Nat} {pr : List Nat} {x : Int}
    {σ : World D} {ρ : Env D Γ} (hc : CodeAt m pc [ci 18 (16 + x) 0 0]) (hl : lit32 (16 + x) = true)
    (he : EnvAt m fp ρ) (hw : WeltAt m L σ) :
    Reach L fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * [ci 18 (16 + x) 0 0].length) + BitVec.ofInt 64 x) σ ρ := by
  have hi := hc 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
  refine ⟨m, star_cast (Star.one (run_step (t := ⟨pc, fp⟩) hi (by decide) (run_jmp (t := ⟨pc, fp⟩) hi))) rfl ?_,
    Agree.refl _ _ _ _, he, hw, Keeps.refl _ _ _⟩
  simp only [T.mk.injEq, and_true]
  have h16 : BitVec.ofInt 64 16 = BitVec.ofNat 64 (16 * 1) := by decide
  rw [sx_lit hl, BitVec.ofInt_add, List.length_singleton, h16, BitVec.add_assoc]

end Gabbro.Stage0.Senke
