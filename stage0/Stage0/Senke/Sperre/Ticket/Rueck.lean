/-
  File:      stage0/Stage0/Senke/Sperre/Ticket/Rueck.lean
  Subject:   A return out of `locks Lk { body }` on the ticket code (lock stage 3), the two return conjuncts of the
              `locks` case beside `locks_okT`: the take (`locksT_take`), then the body's return under the pending
              releases `Lk :: Hs` -- its own return code gives `Lk` with the others (`retScopedC`) -- is a return of
              the whole under `Hs`. No give of `locksCodeT` runs on these paths, as in the model, where `.zurueck`
              and `.why` cross the wrapper unchanged (`execStmt` of `.locks`). The pending locks are held
              (`hHs`), so the free `Lk` is not among them.
-/
module
public import Stage0.Senke.Sperre.Ticket.Gabe
public import Stage0.Senke.Sperre.Ticket.Anfang
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration}

/-- **A normal return out of `locks Lk { body }`**: the body returns from its start (after the take) under the
    pending releases `Lk :: Hs`; the whole returns from its start under `Hs`. -/
theorem locks_okT_zurueck {reserved : Nat} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : W} {L : Lay D}
    {P : Programm D} {f : D.Fn} {fp : W} {K Ks lo : Nat} {rp cfp : W} {σ0 : World D} {ρ0 : Env D (D.params f)}
    {ex : Int × Int} {Γ : Ctx} {Λ : List (Res D)} {Lk : D.Lock} {H Hs : List D.Lock} {bo : Option Int}
    {cb : List II} {m : Mem} {pc : W} {σ σ' : World D} {ρ : Env D Γ} {v : ErgVal D (D.erg f)}
    (hs18 : frei Γ reserved + 18 ≤ Ks) (hW : WIn L fp Ks K) (hlo0 : lo = (functionFrame P f).internalResult)
    (hlo2 : lo ≤ frei Γ reserved)
    (hp : PreS L m pc fp K (frei Γ reserved) (locksCodeT L (L.lk Lk) (frei Γ reserved) cb ex.1 ex.2) ρ reserved)
    (hu : Umf L A C dv m fp Ks K H) (hk : Kopf L f m fp K rp cfp ρ0 P σ0) (hWa : WeltAt m L σ)
    (hH : HeldIn H Λ bo) (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang Lk)
    (hb : ∀ c, bo = some c → c ≤ D.rang Lk) (hHs : ∀ M, M ∈ Hs → M ∈ H)
    (hbody : ∀ m1, PreS L m1 (pc + BitVec.ofNat 64 (16 * 35)) fp K (frei Γ reserved) cb ρ reserved →
      Umf L A C dv m1 fp (Ks - 1) K (Lk :: H) → Kopf L f m1 fp K rp cfp ρ0 P σ0 → WeltAt m1 L (σ.nimmt Lk) →
      HeldIn (Lk :: H) (Res.held Lk :: Λ) bo →
      RetZR L P f σ0 ρ0 fp K rp cfp (Lk :: Hs) ⟨pc + BitVec.ofNat 64 (16 * 35), fp⟩ m1 σ' v) :
    RetZR L P f σ0 ρ0 fp K rp cfp Hs ⟨pc, fp⟩ m σ' v := by
  obtain ⟨m1, n, f1, E0, s1, h0n, h0u, h0w, hL1, hp1, hu1, hk1, hWa1⟩ :=
    locksT_take rfl rfl hs18 hW hlo0 hlo2 hp hu hk hWa hH hr hb
  have hnot : Lk ∉ Hs := fun h => hH.frei hr hb (hHs Lk h)
  have run := hbody m1 hp1 hu1 hk1 hWa1 hH.nimmt
  have hks := hW.ks
  have htop := hW.top
  have hord := hW.ord
  have lower := functionFrame_lo4 P f
  have hfh : fp.toNat + 8 * (frei Γ reserved + 18) ≤ L.hi := by omega
  unfold RetZR at run ⊢
  by_cases hc : returnFault P f σ0 σ' ρ0 v ≠ 0
  · rw [if_pos hc] at run ⊢
    exact Stops.prefix s1 run
  · rw [if_neg hc] at run ⊢
    obtain ⟨m', s2, a2, res, world⟩ := run
    exact ⟨m', s1.trans s2, AgreeWR.nimmt hu.sync hord hfh (by omega) (by omega) hnot hL1.ag h0n h0u h0w
      hL1.o hL1.c hL1.w a2, res, world⟩

/-- **A reason return out of `locks Lk { body }`**: as `locks_okT_zurueck`, for `RetWhyR`. -/
theorem locks_okT_why {reserved : Nat} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : W} {L : Lay D}
    {P : Programm D} {f : D.Fn} {fp : W} {K Ks lo : Nat} {rp cfp : W} {σ0 : World D} {ρ0 : Env D (D.params f)}
    {ex : Int × Int} {Γ : Ctx} {Λ : List (Res D)} {Lk : D.Lock} {H Hs : List D.Lock} {bo : Option Int}
    {cb : List II} {m : Mem} {pc : W} {σ σ' : World D} {ρ : Env D Γ} {r : Fin (D.gruende f)}
    (hs18 : frei Γ reserved + 18 ≤ Ks) (hW : WIn L fp Ks K) (hlo0 : lo = (functionFrame P f).internalResult)
    (hlo2 : lo ≤ frei Γ reserved)
    (hp : PreS L m pc fp K (frei Γ reserved) (locksCodeT L (L.lk Lk) (frei Γ reserved) cb ex.1 ex.2) ρ reserved)
    (hu : Umf L A C dv m fp Ks K H) (hk : Kopf L f m fp K rp cfp ρ0 P σ0) (hWa : WeltAt m L σ)
    (hH : HeldIn H Λ bo) (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang Lk)
    (hb : ∀ c, bo = some c → c ≤ D.rang Lk) (hHs : ∀ M, M ∈ Hs → M ∈ H)
    (hbody : ∀ m1, PreS L m1 (pc + BitVec.ofNat 64 (16 * 35)) fp K (frei Γ reserved) cb ρ reserved →
      Umf L A C dv m1 fp (Ks - 1) K (Lk :: H) → Kopf L f m1 fp K rp cfp ρ0 P σ0 → WeltAt m1 L (σ.nimmt Lk) →
      HeldIn (Lk :: H) (Res.held Lk :: Λ) bo →
      RetWhyR L f fp K rp cfp (Lk :: Hs) ⟨pc + BitVec.ofNat 64 (16 * 35), fp⟩ m1 σ' r) :
    RetWhyR L f fp K rp cfp Hs ⟨pc, fp⟩ m σ' r := by
  obtain ⟨m1, n, f1, E0, s1, h0n, h0u, h0w, hL1, hp1, hu1, hk1, hWa1⟩ :=
    locksT_take rfl rfl hs18 hW hlo0 hlo2 hp hu hk hWa hH hr hb
  have hnot : Lk ∉ Hs := fun h => hH.frei hr hb (hHs Lk h)
  obtain ⟨m', s2, a2, value, mirror, flag, world⟩ := hbody m1 hp1 hu1 hk1 hWa1 hH.nimmt
  have hks := hW.ks
  have htop := hW.top
  have hord := hW.ord
  have lower := functionFrame_lo4 P f
  have hfh : fp.toNat + 8 * (frei Γ reserved + 18) ≤ L.hi := by omega
  exact ⟨m', s1.trans s2, AgreeWR.nimmt hu.sync hord hfh (by omega) (by omega) hnot hL1.ag h0n h0u h0w
    hL1.o hL1.c hL1.w a2, value, mirror, flag, world⟩

end Gabbro.Stage0.Senke
