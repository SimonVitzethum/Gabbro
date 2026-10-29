/-
  Subject: Full word reason dispatch and its simulation of G's execGrund.
-/
import Stage0.Senke.Anweisung.Faelle.Tag
import Stage0.Senke.Anweisung.Faelle.Kontext

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
variable [Kern] {D : Deklaration} {L : Lay D}

theorem whyTest_ok {m : Runner.Mem} {pc fp : Runner.W} {K s k : Nat} {Γ : Ctx} {ρ : Env D Γ}
    {i : Nat} (hi : i < 2 ^ 64) (hk : k < 2 ^ 31)
    (hK : s + 3 ≤ K) (hp : PreS L m pc fp K (s + 1) (whyTestC s k) ρ)
    (hw : m.rd64 (slot fp (BitVec.ofNat 64 s)) = some (BitVec.ofNat 64 i)) :
    Ok m pc fp K (s + 1) (whyTestC s k) (fun w => w = if i == k then 1 else 0) := by
  have hq : PreS L m pc fp K (s + 1)
    ([ci 2 (s + 1) s 0] ++ [ci 1 (s + 2) k 0] ++ [ci 14 (s + 1) (s + 1) (s + 2)]) ρ := hp
  refine bin_ok2 (mov_ok hq.left.left (by omega) (by omega) hw)
    (fun m pc hp => const_ok hp (lit32_nat hk) (by omega))
    (g := fun a b => some (Runner.IR.bool (a == b))) ?_ rfl (by decide) (by omega)
    (by simpa only [Int.natCast_add, Int.ofNat_one, Int.add_assoc,
      show (1 : Int) + 1 = 2 from rfl] using hq)
  intro a b ha hb
  refine ⟨_, rfl, ?_⟩
  rw [ha, hb, BitVec.ofInt_natCast, bool_word]
  have he : (BitVec.ofNat 64 i == BitVec.ofNat 64 k) = (i == k) := by
    by_cases he : i = k
    · simp [he]
    · have hn : BitVec.ofNat 64 i ≠ BitVec.ofNat 64 k := by
        intro hh
        have ht := congrArg BitVec.toNat hh
        simp only [BitVec.toNat_ofNat] at ht
        omega
      rw [beq_eq_false_iff_ne.mpr hn, beq_eq_false_iff_ne.mpr he]
  rw [he]

/-- The induction hypothesis for all branches of a reason dispatch. -/
def GrundAll {V : Vertrag D} (H : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} →
    Block D V l Γ Λ Λ' → Prop) : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} →
    {n : Nat} → GrundArms D V l Γ Λ Λ' n → Prop
  | _, _, _, _, _, .nil => True
  | _, _, _, _, _, .cons b rest => H b ∧ GrundAll H rest

section
variable {O : Orakel D} {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
  {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} {L : Lay D} {P : Programm D}
  {f : D.Fn} {σ0 : World D} {ρ0 : Env D (D.params f)} {rp cfp fp : Runner.W} {lo Ks K : Nat}
  {ens : List II × Nat} {pr : List Nat}

local notation "BR" => BlockRuns O passes R L A C dv cap P f σ0 ρ0 rp cfp fp lo Ks K ens pr

theorem lowGrund_ok {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Nat} (arms : GrundArms D (vertragVon D f) l Γ Λ Λ' n)
    (hblocks : GrundAll (fun b => BR b) arms) {k : Nat} {cd : List II} {top : Nat}
    (hc : lowGrund passes A L lo ens pr ex arms k = some (cd, top)) (ht : top + cap ≤ Ks)
    (hs : 16 * cd.length < 2 ^ 31) (hW : WIn L fp Ks K) (hlo : FB ≤ lo)
    (hlo0 : lo = FB + (D.params f).length) (hlo2 : lo ≤ frei Γ) (hpr : ∀ j ∈ pr, j < frei Γ)
    {m : Runner.Mem} {pc : Runner.W} {σ : World D} {ρ : Env D Γ} 
    (v : Fin n) (hi : k + v.val < 2 ^ 64)
    (hw : m.rd64 (slot fp (BitVec.ofNat 64 (frei Γ))) = some (BitVec.ofNat 64 (k + v.val)))
    (hp : PreS L m pc fp K (frei Γ) cd ρ) (hu : Umf L A C dv m fp Ks K)
    (hk : Kopf L f m fp K rp cfp ρ0 P σ0) (hWa : WeltAt m L σ) :
    Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * cd.length))
      (pc + BitVec.ofNat 64 (16 * cd.length) + BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * cd.length) + BitVec.ofInt 64 ex.2)
      (execGrund O passes R arms v σ ρ) := by
  cases arms with
  | nil => exact Fin.elim0 v
  | cons b rest =>
    simp only [lowGrund] at hc
    split at hc
    · next hki =>
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hc
      obtain ⟨⟨cr, tr⟩, hcr, ⟨cb, tb⟩, hcb, he⟩ := hc
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      simp only [List.length_append, whyTestC, List.length_cons, List.length_nil] at hs
      have hp' : PreS L m pc fp K (frei Γ)
          (whyTestC (frei Γ) k ++ [ci 19 (frei Γ + 1) (16 * (cb.length + 2)) 0] ++
            cb ++ [ci 18 (16 * (cr.length + 1)) 0 0] ++ cr) ρ := by
        simpa only [List.length_append, List.append_assoc, Int.natCast_add] using hp
      have hh := choice_ok (P := P) (σ0 := σ0) (ex := ex) (d := frei Γ + 1) (b := k + v.val == k)
        (ot := execGrund O passes R (.cons b rest) v σ ρ)
        (oe := execGrund O passes R (.cons b rest) v σ ρ)
        (by omega) (by have := hW.ks; omega) (by
          simp only [whyTestC, List.length_cons, List.length_nil, List.length_append]
          omega) hW hlo hlo0 hlo2 hpr
        (fun hpc => whyTest_ok hi hki (by have := hW.ks; omega)
          ⟨by have := hpc.ctx; omega, hpc.small, hpc.frame, hpc.code, hpc.far, hpc.env,
            trivial, wstab_true _ _⟩ hw)
        (fun hb m' pc' hp1 ha hu1 hk1 hw1 => ?_)
        (fun hb m' pc' hp1 ha hu1 hk1 hw1 => ?_) hp' hu hk hWa
      · simpa only [ite_self, List.length_append, List.length_singleton, Nat.add_assoc] using hh
      · have hz : v.val = 0 := by have := eq_of_beq hb; omega
        rcases v with ⟨i, hiv⟩
        change i = 0 at hz
        subst i
        simp only [execGrund]
        have hr : m'.rd64 (slot fp (BitVec.ofNat 64 (frei Γ))) = some (BitVec.ofNat 64 (k + 0)) := by
          rw [agree_rd_low ha hp.frame.room (by omega) (by have := hW.ks; omega)]; exact hw
        exact hblocks.1 (exPlus ex (cr.length + 1)) cb tb hcb (by omega) (by omega)
          m' pc' σ ρ hp1 hlo2 hu1 hk1 hw1 hpr
      · have hn : v.val ≠ 0 := by intro hz; simp only [hz, Nat.add_zero, beq_self_eq_true] at hb; cases hb
        rcases v with ⟨i, hiv⟩
        cases i with
        | zero => exact (hn rfl).elim
        | succ i =>
          simp only [execGrund]
          have hr : m'.rd64 (slot fp (BitVec.ofNat 64 (frei Γ))) = some (BitVec.ofNat 64 (k + (i + 1))) := by
            rw [agree_rd_low ha hp.frame.room (by omega) (by have := hW.ks; omega)]; exact hw
          exact lowGrund_ok rest hblocks.2 hcr (by omega) (by omega) hW hlo hlo0 hlo2 hpr ⟨i, Nat.lt_of_succ_lt_succ hiv⟩
            (by simpa only [Fin.val_mk, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi)
            (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hr) hp1 hu1 hk1 hw1
    · cases hc

termination_by n

theorem onWhy_ok {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    {v : Expr D Γ Λ (.why n)} {arms : GrundArms D (vertragVon D f) l Γ Λ Λ' n}
    {cv ca : List II} {tv ta : Nat} {ex : Int × Int}
    (hn : n < 2 ^ 31) (hblocks : GrundAll (fun b => BR b) arms)
    (hcv : lowE L v (frei Γ) = some (cv, tv))
    (hca : lowGrund passes A L lo ens pr ex arms 0 = some (ca, ta))
    (htv : tv ≤ Ks) (hta : ta + cap ≤ Ks) (hs : 16 * (cv.length + ca.length) < 2 ^ 31)
    (hW : WIn L fp Ks K) (hlo : FB ≤ lo) (hlo0 : lo = FB + (D.params f).length)
    (hlo2 : lo ≤ frei Γ) (hpr : ∀ j ∈ pr, j < frei Γ)
    {m : Runner.Mem} {pc : Runner.W} {σ : World D} {ρ : Env D Γ}
    (hp : PreS L m pc fp K (frei Γ) (cv ++ ca) ρ) (hu : Umf L A C dv m fp Ks K)
    (hk : Kopf L f m fp K rp cfp ρ0 P σ0) (hWa : WeltAt m L σ) :
    Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * (cv ++ ca).length))
      (pc + BitVec.ofNat 64 (16 * (cv ++ ca).length) + BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * (cv ++ ca).length) + BitVec.ofInt 64 ex.2)
      (execStmt O passes R (.onWhy v arms) σ ρ) := by
  have htop := lowE_top v _ _ _ hcv
  have hks := hW.ks
  have hpw := PreS.welt hp.left hks hWa hW.lay (by have := hW.lo; omega)
  obtain ⟨m1, st, a1s, w, hw, hen⟩ := lowE_ok (σ.lese Λ v.orte) (σ.lese Λ v.orte)
    (fun _ h => h) v _ cv tv hcv htv m pc ρ hpw
  have a1 := Agree.widen a1s hks
  have hp1 := hp.next a1 (Nat.le_refl _) (by omega)
  have ih := lowGrund_ok (σ := σ.lese Λ v.orte) arms hblocks hca hta (by omega) hW hlo hlo0 hlo2 hpr
    (eval (σ.lese Λ v.orte) v (σ.lese Λ v.orte) ρ)
    (by have := (eval (σ.lese Λ v.orte) v (σ.lese Λ v.orte) ρ).isLt; simp only [Enc] at hen; omega) (by simpa only [Enc, Nat.zero_add] using hw.trans (congrArg some hen)) hp1
    (hu.agreeW hW (agreeW_of (a1.mono hlo2)) hlo)
    (hk.agreeW hW (agreeW_of (a1.mono hlo2)) (by omega))
    (hpw.wstab m m1 hWa (a1s.mono (Nat.zero_le _)))
  simp only [execStmt]
  rw [pc_add1]
  exact Sim.prefix hlo st (agreeW_of (a1.mono hlo2))
    (keeps_of_agreeW hW a1 hpr (by omega)) ih

/-- Several distinct reasons are accepted in one dispatch, without payload slots. -/
theorem onWhy_ok_zeuge (A : D.Fn → Nat) (L : Lay D) (lo : Nat) (ens : List II × Nat)
    (pr : List Nat) (ex : Int × Int) (f : D.Fn) :
    let arms : GrundArms D (vertragVon D f) false [.why 3] [] [] 3 :=
      .cons .nil (.cons .nil (.cons .nil .nil))
    ∃ code top, lowS passes A L lo ens pr ex (.onWhy (.var .here) arms) = some (code, top) := by
  exact ⟨_, _, rfl⟩

end

theorem retWhy_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (D.params f).length) (hens : lowEns L (P.ensures f) (lo + 1) = some (cens, tens))
    {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
     {r : Fin (D.gruende f)} {proof0 : _} :
    StmtCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Stmt D (vertragVon D f) l Γ Λ Λ from .retWhy r proof0) := by
  intro c top h hK _ hW m pc σ ρ hp _ hlo2 _ hk hWa hpr
  simp only [lowS] at h
  split at h
  · next hr =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact retWhy_ok r hlo0 hr (by simp only [retTop] at hK; omega) hp hk hW hWa
  · cases h

theorem endWhy_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (D.params f).length) (hens : lowEns L (P.ensures f) (lo + 1) = some (cens, tens))
    {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
     {r : Fin (D.gruende f)} {proof0 : _} :
    EndCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Endblock D (vertragVon D f) l Γ Λ from .retWhy r proof0) := by
  intro c top h hK _ hW m pc σ ρ hp hlo2 _ hk hWa hpr
  simp only [lowEnd] at h
  split at h
  · next hr =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact retWhy_ok r hlo0 hr (by simp only [retTop] at hK; omega) hp hk hW hWa
  · cases h

end Gabbro.Stage0.Senke
