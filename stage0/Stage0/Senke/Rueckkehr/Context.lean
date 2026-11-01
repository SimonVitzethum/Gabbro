/- Shared contracts for complete return publication and preserved entry-frame data. -/
import Stage0.Senke.Rueckkehr.Call
import Stage0.Senke.Ausdruck.Old.Sound

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable [Kern]

variable {D : Deklaration} {L : Lay D}

/-- What the code from `t` does when G returns `v` in the world `σ'` from the body of `f`, without the world:
    failed ensures stops with 102; success publishes the complete canonical result,
    its first-word mirror and normal status while preserving the two return addresses. -/
def RetZ0 (L : Lay D) (P : Programm D) (f : D.Fn) (σ0 : World D) (ρ0 : Env D (D.params f)) (fp : Runner.W) (K : Nat)
    (rp cfp : Runner.W) (t : T) (m : Runner.Mem) (σ' : World D) (v : ErgVal D (D.erg f)) : Prop :=
  if wahr? (eval σ0 (P.ensures f) (σ'.lese (vertragVon D f).ende (P.ensures f).orte) (ergEnv (D.erg f) v ρ0)) = false
  then Stops t m 102
  else ∃ m', Star t m ⟨rp, cfp⟩ m' ∧ Agree fp 2 K m m' ∧
    ResultAt L m' fp (FB + contextWords (D.params f)) (D.erg f) v ∧
      ReturnMirror m' fp (FB + contextWords (D.params f)) ∧
      ReturnFlag m' fp (contextWords (D.params f)) true (returnWords (D.erg f) (D.gruende f))

/-- `RetZ0` and the world `σ'` in memory after the return (`WeltAt`). -/
def RetZ (L : Lay D) (P : Programm D) (f : D.Fn) (σ0 : World D) (ρ0 : Env D (D.params f)) (fp : Runner.W) (K : Nat)
    (rp cfp : Runner.W) (t : T) (m : Runner.Mem) (σ' : World D) (v : ErgVal D (D.erg f)) : Prop :=
  if wahr? (eval σ0 (P.ensures f) (σ'.lese (vertragVon D f).ende (P.ensures f).orte) (ergEnv (D.erg f) v ρ0)) = false
  then Stops t m 102
  else ∃ m', Star t m ⟨rp, cfp⟩ m' ∧ AgreeW L fp 2 K m m' ∧
    (ResultAt L m' fp (FB + contextWords (D.params f)) (D.erg f) v ∧
      ReturnMirror m' fp (FB + contextWords (D.params f)) ∧
      ReturnFlag m' fp (contextWords (D.params f)) true (returnWords (D.erg f) (D.gruende f))) ∧ WeltAt m' L σ'

theorem RetZ.prefix {L : Lay D} {P : Programm D} {f : D.Fn} {σ0 : World D} {ρ0 : Env D (D.params f)} {fp : Runner.W}
    {K : Nat} {rp cfp : Runner.W} {t0 t : T} {m0 m : Runner.Mem} {σ' : World D} {v : ErgVal D (D.erg f)}
    (h : Star t0 m0 t m) (ha : AgreeW L fp 2 K m0 m) (hs : RetZ L P f σ0 ρ0 fp K rp cfp t m σ' v) :
    RetZ L P f σ0 ρ0 fp K rp cfp t0 m0 σ' v := by
  simp only [RetZ] at hs ⊢
  split
  · next hf => rw [if_pos hf] at hs; exact Stops.prefix h hs
  · next hf =>
    rw [if_neg hf] at hs
    obtain ⟨m', s, a, hw, hw'⟩ := hs
    exact ⟨m', h.trans s, ha.trans a, hw, hw'⟩

/-- Return addresses, original parameters and complete snapshots below the internal result. -/
structure Kopf (L : Lay D) (f : D.Fn) (m : Runner.Mem) (fp : Runner.W) (K : Nat) (rp cfp : Runner.W)
    (ρ0 : Env D (D.params f)) (P : Programm D) (σ0 : World D) : Prop where
  r0 : m.rd64 (slot fp (BitVec.ofNat 64 0)) = some rp
  r1 : m.rd64 (slot fp (BitVec.ofNat 64 1)) = some cfp
  env : EnvAt L m fp ρ0 (functionFrame P f).ensReserved
  big : (functionFrame P f).internalResult ≤ K
  entry : EntrySnapshots.At L σ0 m fp (oldCells (P.ensures f)) FB

theorem Kopf.agree {P : Programm D} {σ0 : World D} {f : D.Fn} {m m' : Runner.Mem}
    {fp : Runner.W} {K lo : Nat} {rp cfp : Runner.W} {ρ0 : Env D (D.params f)}
    (h : Kopf L f m fp K rp cfp ρ0 P σ0) (ha : Agree fp lo K m m') (hF : FrameOK m fp K)
    (hl : (functionFrame P f).internalResult ≤ lo) : Kopf L f m' fp K rp cfp ρ0 P σ0 := by
  have hb := h.big
  have lower : 4 ≤ (functionFrame P f).internalResult := by
    simp only [functionFrame, FrameLayout.internalResult, FrameLayout.ensParams,
      FrameLayout.ensReserved, FrameLayout.parameterWords, FB]
    omega
  have snapshotBound : FB + EntrySnapshots.words (oldCells (P.ensures f)) ≤
      (functionFrame P f).internalResult := by
    simp only [functionFrame, FrameLayout.internalResult, FrameLayout.ensParams,
      FrameLayout.ensReserved, FrameLayout.parameterWords]
    omega
  have ha' := ha.mono hl
  refine ⟨?_, ?_, envAt_agree h.env ha' hF (Nat.le_refl _) hb, hb,
    h.entry.agree hF ha' snapshotBound hb⟩
  · rw [agree_rd_low ha' hF.room (by omega) hb]; exact h.r0
  · rw [agree_rd_low ha' hF.room (by omega) hb]; exact h.r1

/-! ## What a statement keeps, under the frame's `WIn` -/

theorem agreeW_rdW {L : Lay D} {m m' : Runner.Mem} {fp : Runner.W} {Ks K lo i : Nat} (hW : WIn L fp Ks K)
    (ha : AgreeW L fp lo K m m') (hi : i < lo) (hK : lo ≤ K) :
    m'.rd64 (slot fp (BitVec.ofNat 64 i)) = m.rd64 (slot fp (BitVec.ofNat 64 i)) :=
  agreeW_rd_low ha hW.top (by have := hW.room; omega) hi hK

theorem codeAt_agreeWIn {L : Lay D} {m m' : Runner.Mem} {fp : Runner.W} {Ks K lo : Nat} (hW : WIn L fp Ks K)
    (ha : AgreeW L fp lo K m m') {pc : Runner.W} {is : List II} (hc : CodeAt m pc is)
    (hf : CodeFar pc is.length fp K) : CodeAt m' pc is :=
  codeAt_agreeW ha hW.top hW.lay.2.2 hW.ord hc hf

theorem envAt_agreeWIn {L : Lay D} {m m' : Runner.Mem} {fp : Runner.W} {Ks K d reserved : Nat} {Γ : Ctx} {ρ : Env D Γ}
    (hW : WIn L fp Ks K) (h : EnvAt L m fp ρ reserved) (ha : AgreeW L fp d K m m') (hd : frei Γ reserved ≤ d) (hK : d ≤ K) :
    EnvAt L m' fp ρ reserved :=
  envAt_agreeW h ha hW.top (by have := hW.room; omega) hd hK

theorem keeps_of_agreeW {L : Lay D} {fp : Runner.W} {pr : List Nat} {Ks K d : Nat} {m m' : Runner.Mem}
    (hW : WIn L fp Ks K) (ha : AgreeW L fp d K m m') (hp : ∀ j ∈ pr, j < d) (hd : d ≤ K) : Keeps fp pr m m' :=
  fun j hj => agreeW_rdW hW ha (hp j hj) hd

theorem Umf.agreeW {L : Lay D} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {m m' : Runner.Mem}
    {fp : Runner.W} {Ks Ks' K lo : Nat} (hW : WIn L fp Ks' K) (h : Umf L A C dv m fp Ks K) (ha : AgreeW L fp lo K m m')
    (hlo : FB ≤ lo) : Umf L A C dv m' fp Ks K :=
  ⟨pcode_agreeW h.code ha hW.top hW.lay.2.2 hW.ord, by
    have hFB3 : FB = 4 := rfl
    have hb := h.big
    rw [agreeW_rdW hW (ha.mono (Nat.min_le_left lo K)) (by omega) (Nat.min_le_right lo K)]
    exact h.depth, h.big, h.sync.agreeW ha h.hiK, h.hiK⟩

theorem Kopf.agreeW {P : Programm D} {σ0 : World D} {f : D.Fn} {m m' : Runner.Mem}
    {fp : Runner.W} {Ks K lo : Nat} {rp cfp : Runner.W} {ρ0 : Env D (D.params f)}
    (hW : WIn L fp Ks K) (h : Kopf L f m fp K rp cfp ρ0 P σ0) (ha : AgreeW L fp lo K m m')
    (hl : (functionFrame P f).internalResult ≤ lo) : Kopf L f m' fp K rp cfp ρ0 P σ0 := by
  have hb := h.big
  have lower : 4 ≤ (functionFrame P f).internalResult := by
    simp only [functionFrame, FrameLayout.internalResult, FrameLayout.ensParams,
      FrameLayout.ensReserved, FrameLayout.parameterWords, FB]
    omega
  have snapshotBound : FB + EntrySnapshots.words (oldCells (P.ensures f)) ≤
      (functionFrame P f).internalResult := by
    simp only [functionFrame, FrameLayout.internalResult, FrameLayout.ensParams,
      FrameLayout.ensReserved, FrameLayout.parameterWords]
    omega
  have ha' := ha.mono hl
  refine ⟨?_, ?_, envAt_agreeWIn hW h.env ha' (Nat.le_refl _) hb, hb, ?_⟩
  · rw [agreeW_rdW hW ha' (by omega) hb]; exact h.r0
  · rw [agreeW_rdW hW ha' (by omega) hb]; exact h.r1
  · exact h.entry.agreeW (by have := hW.room; omega) ha' hW.top snapshotBound hb

/-- `Pre.next` after a statement that changed the slots from `lo` on and the world. -/
theorem Pre.nextW {L : Lay D} {m m' : Runner.Mem} {pc fp : Runner.W} {Ks K d d' lo reserved : Nat} {a b : List II}
    {Γ : Ctx} {ρ : Env D Γ} (hW : WIn L fp Ks K) (h : PreS L m pc fp K d (a ++ b) ρ reserved) (ha : AgreeW L fp lo K m m')
    (hlo : frei Γ reserved ≤ lo) (hd : d ≤ d') (hK : lo ≤ K) : PreS L m' (pc + BitVec.ofNat 64 (16 * a.length)) fp K d' b ρ reserved :=
  have hf := codeFar_right (n := a.length) (k := b.length) (by simpa using h.far)
  ⟨Nat.le_trans h.ctx hd, h.small, frameOK_agreeW h.frame ha, codeAt_agreeWIn hW ha (codeAt_right h.code) hf, hf,
   envAt_agreeWIn hW h.env ha hlo hK, trivial, wstab_true _ _⟩

theorem envAt_ergEnv {reserved : Nat} {m : Runner.Mem} {fp : Runner.W} {Γ : Ctx} {ρ : Env D Γ} :
    {e : Option Ty} → {v : ErgVal D e} → EnvAt L m fp ρ reserved →
    ResultAt L m fp (frei Γ reserved) e v → EnvAt L m fp (ergEnv e v ρ) reserved
  | none, _, h, _ => h
  | some _, _, h, value => envAt_cons h value

theorem frei_ergCtx (Γ : Ctx) (reserved : Nat := 0) : (e : Option Ty) → frei (ErgCtx Γ e) reserved ≤ frei Γ reserved + resultWords e
  | none => by simp [ErgCtx]
  | some _ => by simp [ErgCtx, frei, resultWords, Nat.add_assoc]

theorem lowErg_span {reserved : Nat} {Λ : List (Res D)} {Γ : Ctx} : {e : Option Ty} → (x : ErgExpr D Γ Λ e) → (d : Nat) →
    (c : List II) → (top : Nat) → lowErg L x d reserved = some (c, top) → d + resultWords e ≤ top
  | _, .empty, d, c, top, h => by simp only [lowErg, Option.some.injEq, Prod.mk.injEq] at h; change d + 1 ≤ top; omega
  | _, .val e, d, c, top, h => by
    simp only [lowErg, Option.map_eq_some_iff] at h
    obtain ⟨⟨ce, te⟩, he, out⟩ := h
    cases out
    exact Nat.le_max_right _ _

theorem lowErg_top {reserved : Nat} {Λ : List (Res D)} {Γ : Ctx} {e : Option Ty}
    (x : ErgExpr D Γ Λ e) (d : Nat) (c : List II) (top : Nat)
    (lower : lowErg L x d reserved = some (c, top)) : d < top := by
  have span := lowErg_span x d c top lower
  have positive := resultWords_pos e
  omega

theorem lowErg_ok {reserved : Nat} {Λ : List (Res D)} {fp : Runner.W} {K : Nat} {W : Runner.Mem → Prop} (σ₀ σ : World D)
    (hWL : ∀ m, W m → WeltAt m L σ) (hLay : LayIn L) {Γ : Ctx} :
    {e : Option Ty} → (x : ErgExpr D Γ Λ e) → (d : Nat) → (c : List II) → (top : Nat) →
    lowErg L x d reserved = some (c, top) → top ≤ K → ∀ (m : Runner.Mem) (pc : Runner.W) (ρ : Env D Γ),
    Pre L m pc fp K d c ρ W reserved → ResultOk L m pc fp K d c e (evalErg σ₀ x σ ρ)
  | _, .empty, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowErg, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨m', run, changed, w, read, equal⟩ := const_ok hp (by decide) (by omega)
    subst w
    refine ⟨m', run, changed, ?_⟩
    intro i hi
    have zero : i = 0 := by simpa using hi
    subst i
    exact read
  | _, .val e, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowErg, Option.map_eq_some_iff] at h
    obtain ⟨⟨ce, te⟩, he, out⟩ := h
    cases out
    exact lowE_ok (reserved := reserved) σ₀ σ hWL hLay e d ce te he
      (Nat.le_trans (Nat.le_max_left _ _) hK) m pc ρ hp

theorem codeFar_tail {pc fp : Runner.W} {K : Nat} {a b : List II} (h : CodeFar pc (a ++ b).length fp K) :
    CodeFar (pc + BitVec.ofNat 64 (16 * a.length)) b.length fp K :=
  codeFar_right (by rw [List.length_append] at h; exact h)

theorem slot_one (fp : Runner.W) : slot fp (BitVec.ofNat 64 1) = fp + 8 := by simp [slot]


end Gabbro.Stage0.Senke
