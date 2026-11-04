/- Full-word tag tests and complete payload binding for aggregate sums. -/
module
public import Stage0.Senke.Anweisung.Faelle.Tag
public import Stage0.Senke.Ausdruck.Aggregat.Werte.Sum.Model
public import Stage0.Senke.Ausdruck.Aggregat.Frame.Copy
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}

/-- The test writes exclusively above the complete source sum. -/
theorem sumSpanTest_ok {m : Runner.Mem} {pc fp : Runner.W} {K s scratch k i : Nat}
    {Γ : Ctx} {ρ : Env D Γ} (hi : i < 2 ^ 64) (hk : k < 2 ^ 31)
    (hK : scratch + 2 ≤ K) (hs : s < K)
    (hp : PreS L m pc fp K scratch (sumSpanTestC s scratch k) ρ reserved)
    (hw : m.rd64 (slot fp (BitVec.ofNat 64 s)) = some (BitVec.ofNat 64 i)) :
    Ok m pc fp K scratch (sumSpanTestC s scratch k) (fun w => w = if i == k then 1 else 0) := by
  have p : PreS L m pc fp K scratch
      ([ci 2 scratch s 0] ++ [ci 1 (scratch + 1) k 0] ++ [ci 14 scratch scratch (scratch + 1)]) ρ reserved := hp
  refine bin_ok2 (mov_ok p.left.left hs (by omega) hw)
    (fun m pc pre => const_ok pre (lit32_nat hk) (by omega))
    (g := fun a b => some (Runner.IR.bool (a == b))) ?_ rfl (by decide) (by omega)
    (by simpa only [Int.natCast_add, Int.ofNat_one] using p)
  intro a b ha hb
  refine ⟨_, rfl, ?_⟩
  rw [ha, hb, BitVec.ofInt_natCast, bool_word]
  have eq : (BitVec.ofNat 64 i == BitVec.ofNat 64 k) = (i == k) := by
    by_cases same : i = k
    · simp [same]
    · have different : BitVec.ofNat 64 i ≠ BitVec.ofNat 64 k := by
        intro words
        have values := congrArg BitVec.toNat words
        simp only [BitVec.toNat_ofNat] at values
        omega
      rw [beq_eq_false_iff_ne.mpr different, beq_eq_false_iff_ne.mpr same]
  rw [eq]

theorem PayloadAt.agree_low {m m' : Runner.Mem} {fp : Runner.W} {s lo K : Nat}
    {c : Option Ty} {v : Nutzlast D.Fn D.passt c}
    (value : PayloadAt L m fp s c v) (changed : Agree fp lo K m m')
    (room : fp.toNat + 8 * K ≤ 2 ^ 64) (below : s + payloadWords c ≤ lo)
    (inside : lo ≤ K) : PayloadAt L m' fp s c v :=
  ⟨value.1, value.2.agree_low changed room (by simpa only [payloadEncoding_length] using below)
    inside⟩

section
variable {O : Orakel D} {passes : Nat}
  {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
  {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat}
  {P : Programm D} {f : D.Fn} {σ0 : World D} {ρ0 : Env D (D.params f)}
  {rp cfp fp : Runner.W} {lo Ks K : Nat} {ens : List II × Nat} {pr : List Nat}

local notation "BR" => BlockRuns (reserved := reserved) O passes R L A C dv cap P f σ0 ρ0 rp cfp fp lo Ks K ens pr

/-- Arm execution binds the entire payload, including its nested validity duties. -/
theorem sumSpanArm_ok {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {c : Option Ty}
    {b : Block D (vertragVon D f) l (ArmCtx Γ c) Λ Λ'} {cb : List II} {tb : Nat} {ex : Int × Int}
    (hb : BR b) (made : lowB (reserved := reserved) passes A L (functionFrame P f) ens pr ex b = some (cb, tb))
    (fits : tb + cap ≤ Ks) (size : 16 * ((sumSpanPayloadC (frei Γ reserved) c).length + cb.length) < 2 ^ 31)
    (bound : frei Γ reserved + 1 + payloadWords c ≤ Ks) (hW : WIn L fp Ks K)
    (hlo : FB ≤ lo) (hlo0 : lo = (functionFrame P f).internalResult)
    (hlo2 : lo ≤ frei Γ reserved) (hpr : ∀ j ∈ pr, j < frei Γ reserved)
    {m : Runner.Mem} {pc : Runner.W} {σ : World D} {ρ : Env D Γ}
    (v : Nutzlast D.Fn D.passt c) (value : PayloadAt L m fp (frei Γ reserved + 1) c v)
    (pre : PreS L m pc fp K (frei Γ reserved) (sumSpanPayloadC (frei Γ reserved) c ++ cb) ρ reserved)
    (hu : Umf L A C dv m fp Ks K) (hk : Kopf L f m fp K rp cfp ρ0 P σ0) (world : WeltAt m L σ) :
    Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m
      (pc + BitVec.ofNat 64 (16 * (sumSpanPayloadC (frei Γ reserved) c ++ cb).length))
      (pc + BitVec.ofNat 64 (16 * (sumSpanPayloadC (frei Γ reserved) c ++ cb).length) + BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * (sumSpanPayloadC (frei Γ reserved) c ++ cb).length) + BitVec.ofInt 64 ex.2)
      ((execBlock O passes R b σ (armEnv v ρ)).schrumpfArm c) reserved := by
  cases c with
  | none =>
    simpa only [sumSpanPayloadC, payloadWords, copyWords, List.nil_append,
      armEnv, Ausgang.schrumpfArm] using
      hb ex cb tb made fits (by simpa [sumSpanPayloadC, payloadWords] using size)
        m pc σ ρ (by simpa [sumSpanPayloadC, payloadWords, copyWords] using pre)
        hlo2 hu hk world hpr
  | some τ =>
    have hks := hW.ks
    have span : frei Γ reserved + 1 + valueWords τ ≤ Ks := by
      simpa only [payloadWords] using bound
    have destination : frei Γ reserved + valueWords τ ≤ K := by omega
    have payload : ValueAt L m fp (frei Γ reserved + 1) τ v := value
    obtain ⟨m1, steps, changed, output⟩ := copyValue_run pre.frame pre.small
      destination (Nat.le_trans span hks)
      (Or.inl (by omega)) pre.left.code
      (by simpa only [sumSpanPayloadC, payloadWords, copyWords_length] using pre.left.far) payload
    have steps' : Star ⟨pc, fp⟩ m
        ⟨pc + BitVec.ofNat 64 (16 * (sumSpanPayloadC (frei Γ reserved) (some τ)).length), fp⟩ m1 := by
      simpa only [sumSpanPayloadC, payloadWords, copyWords_length] using steps
    have ch : Agree fp (frei Γ reserved) K m m1 := Agree.widen changed destination
    have p1 := pre.next ch (by omega : frei Γ reserved ≤ frei Γ reserved + valueWords τ) (by omega)
    have ctx : frei (ArmCtx Γ (some τ)) reserved = frei Γ reserved + valueWords τ := by
      simp [frei, ArmCtx, Nat.add_assoc]
    have pb : PreS L m1 _ fp K (frei (ArmCtx Γ (some τ)) reserved) cb (armEnv v ρ) reserved :=
      ⟨by rw [ctx]; have := p1.ctx; omega, p1.small, p1.frame, p1.code, p1.far,
        envAt_cons p1.env output, trivial, wstab_true _ _⟩
    have result := hb ex cb tb made fits (by omega) m1 _ σ _ pb (by rw [ctx]; omega)
      (hu.agreeW hW (agreeW_of (ch.mono hlo2)) hlo)
      (hk.agreeW hW (agreeW_of (ch.mono hlo2)) (by omega))
      (weltAt_stab hW.lay hW.top m m1 world (ch.mono (Nat.zero_le _)))
      (fun j hj => by have := hpr j hj; rw [ctx]; omega)
    rw [pc_add1]
    apply Sim.prefix hlo steps' (agreeW_of (ch.mono hlo2))
      (keeps_of_agreeW hW ch hpr (by omega)) (Sim.schrumpf result)
end
end Gabbro.Stage0.Senke
