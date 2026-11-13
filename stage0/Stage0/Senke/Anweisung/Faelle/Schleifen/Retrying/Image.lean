/- The single retry header and its world-aware runtime interface. -/
module
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Retrying.Emission
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Runtime.Teil1
public import Stage0.Senke.Anweisung.SchleifeTeile
@[expose] public section

namespace Gabbro.Stage0.Senke.Retrying
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {P : Programm D} {f : D.Fn}

/-- Proof data for one emitted image; no execution premise is stored here. -/
structure Image (L : Lay D) (P : Programm D) (f : D.Fn) (Γ : Ctx) (reserved : Nat) where
  A : D.Fn → Nat
  C : D.Fn → List II
  dv : W
  fp : W
  pc : W
  rp : W
  cfp : W
  K : Nat
  Ks : Nat
  lo : Nat
  counter : Nat
  one : Nat
  condition : List II
  body : List II
  overflow : List II
  σ0 : World D
  ρ0 : Env D (D.params f)
  pr : List Nat
  H : List D.Lock
  layout : WIn L fp Ks K
  abi : lo = (functionFrame P f).internalResult
  low : FB ≤ lo
  controls : lo ≤ counter ∧ counter < one ∧ one < FB + reserved
  room : frei Γ reserved + 1 ≤ Ks
  kept : ∀ j ∈ pr, j < frei Γ reserved ∧ j ≠ counter ∧ j ≠ one
  sized : 16 * (condition.length + body.length + overflow.length + 7) < 2 ^ 31

namespace Image
variable {Γ : Ctx} {reserved : Nat} (x : Image L P f Γ reserved)

def code : List II := retryHeader x.counter x.one (frei Γ reserved) x.condition x.body x.overflow

def addr (i : Nat) : W := x.pc + BitVec.ofNat 64 (16 * i)
def controlIndex : Nat := x.condition.length + 2
def bodyIndex : Nat := x.condition.length + 4
def backIndex : Nat := x.condition.length + x.body.length + 4
def overflowIndex : Nat := x.condition.length + x.body.length + 5
def exitIndex : Nat := x.condition.length + x.body.length + x.overflow.length + 5

def read (m : Mem) (j : Nat) (v : W) : Prop :=
  m.rd64 (slot x.fp (BitVec.ofNat 64 j)) = some v

structure Ready (m : Mem) (σ : World D) (ρ : Env D Γ) : Prop where
  pre : PreS L m x.pc x.fp x.K (frei Γ reserved) x.code ρ reserved
  surround : Umf L x.A x.C x.dv m x.fp x.Ks x.K x.H
  head : Kopf L f m x.fp x.K x.rp x.cfp x.ρ0 P x.σ0
  world : WeltAt m L σ

variable {x} {m m' : Mem} {σ τ : World D} {ρ η : Env D Γ}

theorem Ready.after (h : x.Ready m σ ρ) (a : AgreeW L x.fp x.lo x.K m m')
    (env : EnvAt L m' x.fp η reserved) (world : WeltAt m' L τ) : x.Ready m' τ η :=
  { pre := (mkPreS h.pre.ctx h.pre.small (frameOK_agreeW h.pre.frame a)
      (codeAt_agreeWIn x.layout a h.pre.code h.pre.far) h.pre.far env)
    surround := (h.surround.agreeW x.layout a x.low)
    head := (h.head.agreeW x.layout a (by rw [x.abi]))
    world := world }

/-- Extract a literal list slice at its instruction index. -/
theorem Ready.slice (h : x.Ready m σ ρ) (i : Nat) (before block after : List II)
    (shape : x.code = before ++ (block ++ after)) (offset : before.length = i) :
    PreS L m (x.addr i) x.fp x.K (frei Γ reserved) block ρ reserved := by
  have bound : i + block.length ≤ x.code.length := by
    rw [shape]
    simp only [List.length_append, offset]
    omega
  exact mkPreS h.pre.ctx h.pre.small h.pre.frame
    (codeAt_at (xs := before) (zs := after) (by rw [← shape]; exact h.pre.code)
      (by rw [offset]; rfl)) (codeFar_at h.pre.far bound) h.pre.env

theorem Ready.condition (h : x.Ready m σ ρ) :
    PreS L m x.pc x.fp x.K (frei Γ reserved) x.condition ρ reserved := by
  exact h.pre.left

theorem Ready.test (h : x.Ready m σ ρ) :
    CodeAt m (x.addr x.condition.length) [ci 19 (frei Γ reserved) 32 0] := by
  exact (h.slice x.condition.length x.condition _ _ rfl rfl).code

theorem Ready.exitJump (h : x.Ready m σ ρ) :
    CodeAt m (x.addr (x.condition.length + 1))
      [ci 18 (16 * (x.body.length + x.overflow.length + 4)) 0 0] := by
  refine (h.slice _ (x.condition ++ [ci 19 (frei Γ reserved) 32 0])
    [ci 18 (16 * (x.body.length + x.overflow.length + 4)) 0 0]
    ([ci 19 x.counter (16 * (x.body.length + 3)) 0, ci 4 x.counter x.counter x.one] ++
      (x.body ++ ([ci 18 (-(16 * (x.condition.length + x.body.length + 4 : Nat) : Int)) 0 0] ++
        x.overflow))) ?_ ?_).code
  · simp only [code, retryHeader_eq, List.append_assoc, List.cons_append, List.nil_append]
  · simp only [List.length_append, List.length_singleton]

theorem Ready.control (h : x.Ready m σ ρ) :
    PreS L m (x.addr x.controlIndex) x.fp x.K (frei Γ reserved)
      (foreverCounter x.counter x.one (16 * (x.body.length + 3)) ++
        (x.body ++ [ci 18 (-(16 * (x.condition.length + x.body.length + 4 : Nat) : Int)) 0 0] ++
          x.overflow)) ρ reserved := by
  refine h.slice _
    (x.condition ++ [ci 19 (frei Γ reserved) 32 0,
      ci 18 (16 * (x.body.length + x.overflow.length + 4)) 0 0]) _ [] ?_ ?_
  · simp only [code, retryHeader_eq, foreverCounter, List.append_assoc,
      List.append_nil, List.cons_append, List.nil_append]
  · simp only [controlIndex, List.length_append, List.length_cons, List.length_nil]

theorem Ready.body (h : x.Ready m σ ρ) :
    PreS L m (x.addr x.bodyIndex) x.fp x.K (frei Γ reserved) x.body ρ reserved := by
  refine h.slice _
    (x.condition ++ [ci 19 (frei Γ reserved) 32 0,
      ci 18 (16 * (x.body.length + x.overflow.length + 4)) 0 0,
      ci 19 x.counter (16 * (x.body.length + 3)) 0, ci 4 x.counter x.counter x.one]) x.body
    ([ci 18 (-(16 * (x.condition.length + x.body.length + 4 : Nat) : Int)) 0 0] ++ x.overflow) ?_ ?_
  · simp only [code, retryHeader_eq, List.append_assoc, List.cons_append, List.nil_append]
  · simp only [bodyIndex, List.length_append, List.length_cons, List.length_nil]

theorem Ready.back (h : x.Ready m σ ρ) :
    CodeAt m (x.addr x.backIndex)
      [ci 18 (-(16 * (x.condition.length + x.body.length + 4 : Nat) : Int)) 0 0] := by
  refine (h.slice _
    ((x.condition ++ [ci 19 (frei Γ reserved) 32 0,
      ci 18 (16 * (x.body.length + x.overflow.length + 4)) 0 0,
      ci 19 x.counter (16 * (x.body.length + 3)) 0, ci 4 x.counter x.counter x.one]) ++ x.body)
    [ci 18 (-(16 * (x.condition.length + x.body.length + 4 : Nat) : Int)) 0 0] x.overflow ?_ ?_).code
  · simp only [code, retryHeader_eq, List.append_assoc, List.cons_append, List.nil_append]
  · simp only [backIndex, List.length_append, List.length_cons, List.length_nil]
    omega

theorem Ready.overflow (h : x.Ready m σ ρ) :
    PreS L m (x.addr x.overflowIndex) x.fp x.K (frei Γ reserved) x.overflow ρ reserved := by
  refine h.slice _
    ((x.condition ++ [ci 19 (frei Γ reserved) 32 0,
      ci 18 (16 * (x.body.length + x.overflow.length + 4)) 0 0,
      ci 19 x.counter (16 * (x.body.length + 3)) 0, ci 4 x.counter x.counter x.one]) ++
        x.body ++ [ci 18 (-(16 * (x.condition.length + x.body.length + 4 : Nat) : Int)) 0 0])
    _ [] ?_ ?_
  · simp only [code, retryHeader_eq, foreverCounter, List.append_assoc,
      List.append_nil, List.cons_append, List.nil_append]
  · simp only [overflowIndex, List.length_append, List.length_cons, List.length_nil]
    omega

theorem back_target (x : Image L P f Γ reserved) :
    x.addr x.backIndex + sx (II.f (-(16 * (x.condition.length + x.body.length + 4 : Nat) : Int))) =
      x.pc := by
  rw [sx_lit (retry_displacements _ _ _ x.sized).2.2]
  change x.pc + BitVec.ofNat 64 (16 * x.backIndex) +
    BitVec.ofInt 64 (-(16 * (x.backIndex : Nat) : Int)) = x.pc
  have cast : (16 * (x.backIndex : Nat) : Int) = ((16 * x.backIndex : Nat) : Int) := by omega
  rw [cast, BitVec.ofInt_neg, BitVec.ofInt_natCast, BitVec.add_neg_eq_sub, BitVec.add_sub_cancel]

end Image
end Gabbro.Stage0.Senke.Retrying
