/-
  File:      stage0/Stage0/Senke/Spez.lean
  Subject:   What a lowered function owes its caller (`FunSpec`), and frames inside frames.

  `PCode m A C fp K`: every function's code `C g` lies at its address `A g`, apart from the stack (the slots
  `0 .. K-1` of the frame at `fp`, which hold every frame called from there). `FunSpec A C S dv c`: for every
  function `f`, entered with a frame whose header the `call` wrote, depth `dv` in slot 2 and the arguments in the
  parameter slots, and a stack of at least `c` slots: where `S f` (the call semantics) answers `ok v`, the IR
  returns to the caller with the word of `v` in slot 2, having changed nothing but its own frame from slot 2 on;
  Normal returns additionally keep status 1 in `FB + parameter count + 1`, the successful ensures output.
  A `why` answer returns its ordinal in slot 2 and status 0, bypassing ensures exactly as G does.
  Logic and hardware outcomes retain their named stops.
-/
import Stage0.Senke.Funktion
import Stage0.Senke.Welt.WeltAt
import Stage0.Senke.Sperre.Sync

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration} {L : Lay D}

def PCode (m : Runner.Mem) (A : D.Fn → Nat) (C : D.Fn → List II) (fp : Runner.W) (K : Nat) : Prop :=
  ∀ g, CodeAt m (BitVec.ofNat 64 (A g)) (C g) ∧ CodeFar (BitVec.ofNat 64 (A g)) (C g).length fp K

/-- The frame at `fp` has `K` slots, the current body's own below `Ks`; the world lies above the whole frame, apart
    from every frame (each thread's stack lies below it). Every frame nested in it ends at the same address
    (`WIn.sub`). -/
structure WIn (L : Lay D) (fp : Runner.W) (Ks K : Nat) : Prop where
  lay : LayIn L
  dis : LayDis L
  top : fp.toNat + 8 * K ≤ L.lo
  ord : L.lo ≤ L.hi
  ks : Ks ≤ K

theorem WIn.lo {L : Lay D} {fp : Runner.W} {Ks K : Nat} (h : WIn L fp Ks K) : fp.toNat + 8 * Ks ≤ L.lo := by
  have := h.top; have := h.ks; omega

/-- The word of a result. -/
def EncErg (L : Lay D) : (e : Option Ty) → ErgVal D e → Runner.W → Prop
  | some τ, v, w => Enc L τ v w
  | none, _, _ => True

/-- The checked normal return keeps the successful ensures Boolean in its output slot.
    A reason return writes zero there and its ordinal in slot 2. No parameter slot changes. -/
def ReturnFlag (m : Runner.Mem) (fp : Runner.W) (np : Nat) (ok : Bool) : Prop :=
  m.rd64 (slot fp (BitVec.ofNat 64 (FB + np + 1))) = some (if ok then 1 else 0)

/-- A reason return preserves the frame header and carries the resulting world. -/
def RetWhy (L : Lay D) (f : D.Fn) (fp : Runner.W) (K : Nat) (rp cfp : Runner.W)
    (t : T) (m : Runner.Mem) (σ : World D) (r : Fin (D.gruende f)) : Prop :=
  ∃ m', Star t m ⟨rp, cfp⟩ m' ∧ AgreeW L fp 2 K m m' ∧
    m'.rd64 (slot fp (BitVec.ofNat 64 2)) = some (BitVec.ofNat 64 r.val) ∧
    ReturnFlag m' fp (D.params f).length false ∧ WeltAt m' L σ

theorem RetWhy.prefix {f : D.Fn} {fp : Runner.W} {K : Nat} {rp cfp : Runner.W}
    {t0 t : T} {m0 m : Runner.Mem} {σ : World D} {r : Fin (D.gruende f)}
    (h : Star t0 m0 t m) (ha : AgreeW L fp 2 K m0 m) (hs : RetWhy L f fp K rp cfp t m σ r) :
    RetWhy L f fp K rp cfp t0 m0 σ r := by
  obtain ⟨m', s, a, hw, flag, hw'⟩ := hs
  exact ⟨m', h.trans s, ha.trans a, hw, flag, hw'⟩

structure FunSpec (L : Lay D) (A : D.Fn → Nat) (C : D.Fn → List II)
    (S : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (dv : Runner.W) (c : Nat) : Prop where
  addr : L.fa = A
  run : ∀ (f : D.Fn) (m : Runner.Mem) (fp : Runner.W) (K Ks : Nat) (rp cfp : Runner.W) (σ : World D)
    (ρ : Env D (D.params f)),
    c ≤ Ks → WIn L fp Ks K → K < 2 ^ 31 → FrameOK m fp K → PCode m A C fp K →
    m.rd64 (slot fp (BitVec.ofNat 64 0)) = some rp → m.rd64 (slot fp (BitVec.ofNat 64 1)) = some cfp →
    m.rd64 (slot fp (BitVec.ofNat 64 2)) = some dv → EnvAt L m fp ρ → WeltAt m L σ → SyncOK m L fp Ks →
    match S f σ ρ with
    | .ok σ' v => ∃ m', Star ⟨BitVec.ofNat 64 (A f), fp⟩ m ⟨rp, cfp⟩ m' ∧ AgreeW L fp 2 K m m' ∧
        (∃ w, m'.rd64 (slot fp (BitVec.ofNat 64 2)) = some w ∧ EncErg L (D.erg f) v w ∧ ReturnFlag m' fp (D.params f).length true) ∧ WeltAt m' L σ'
    | .logik e => Stops ⟨BitVec.ofNat 64 (A f), fp⟩ m (logikCode e)
    | .hardware h => Stops ⟨BitVec.ofNat 64 (A f), fp⟩ m (hwCode h)
    | .why σ' r => RetWhy L f fp K rp cfp ⟨BitVec.ofNat 64 (A f), fp⟩ m σ' r

/-! ## Frames inside frames -/

/-- Slot `i` of the frame at slot `F` is slot `F + i`. -/
theorem slot_slot (fp : Runner.W) (F i : Nat) :
    slot (slot fp (BitVec.ofNat 64 F)) (BitVec.ofNat 64 i) = slot fp (BitVec.ofNat 64 (F + i)) := by
  simp only [slot]
  apply BitVec.eq_of_toNat_eq
  have h8 : (8 : Runner.W).toNat = 8 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h8]
  omega

theorem frame_sub {m : Runner.Mem} {fp : Runner.W} {K F : Nat} (h : FrameOK m fp K) (hF : F ≤ K) :
    FrameOK m (slot fp (BitVec.ofNat 64 F)) (K - F) := by
  have hr := h.lt
  have hs : (slot fp (BitVec.ofNat 64 F)).toNat = fp.toNat + 8 * F := by
    have := fp.isLt
    have h8 : (8 : Runner.W).toNat = 8 := rfl
    simp only [slot, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h8]
    rw [Nat.mod_eq_of_lt (a := F) (by omega)]; omega
  refine ⟨by rw [hs]; omega, fun i hi => ?_, fun i hi => ?_⟩
  · rw [slot_slot]; exact h.rd _ (by omega)
  · rw [slot_slot]; exact h.wr _ (by omega)

/-- What the callee's frame changes is, in the caller's frame, the slots from `F` on. -/
theorem agree_sub {m m' : Runner.Mem} {fp : Runner.W} {K F lo : Nat} (hr : fp.toNat + 8 * K < 2 ^ 64) (hF : F ≤ K)
    (h : Agree (slot fp (BitVec.ofNat 64 F)) lo (K - F) m m') : Agree fp (F + lo) K m m' := by
  have hs : (slot fp (BitVec.ofNat 64 F)).toNat = fp.toNat + 8 * F := by
    have := fp.isLt
    have h8 : (8 : Runner.W).toNat = 8 := rfl
    simp only [slot, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h8]
    rw [Nat.mod_eq_of_lt (a := F) (by omega)]; omega
  refine ⟨h.rd, h.wr, fun x hx => h.b x fun ⟨h1, h2⟩ => hx ⟨?_, ?_⟩⟩
  · rw [hs] at h1; omega
  · rw [hs] at h2; omega

theorem agreeW_sub {L : Lay D} {m m' : Runner.Mem} {fp : Runner.W} {K F lo : Nat} (hr : fp.toNat + 8 * K < 2 ^ 64)
    (hF : F ≤ K) (h : AgreeW L (slot fp (BitVec.ofNat 64 F)) lo (K - F) m m') : AgreeW L fp (F + lo) K m m' := by
  have hs : (slot fp (BitVec.ofNat 64 F)).toNat = fp.toNat + 8 * F := by
    have := fp.isLt
    have h8 : (8 : Runner.W).toNat = 8 := rfl
    simp only [slot, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h8]
    rw [Nat.mod_eq_of_lt (a := F) (by omega)]; omega
  refine ⟨h.rd, h.wr, fun x hx hw => h.b x (fun ⟨h1, h2⟩ => hx ⟨?_, ?_⟩) hw⟩
  · rw [hs] at h1; omega
  · rw [hs] at h2; omega

theorem codeFar_sub {pc fp : Runner.W} {n K F : Nat} (h : CodeFar pc n fp K) (hlt : fp.toNat + 8 * K < 2 ^ 64)
    (hF : F ≤ K) : CodeFar pc n (slot fp (BitVec.ofNat 64 F)) (K - F) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hs : (slot fp (BitVec.ofNat 64 F)).toNat = fp.toNat + 8 * F := by
    have := fp.isLt
    have h8 : (8 : Runner.W).toNat = 8 := rfl
    simp only [slot, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h8]
    rw [Nat.mod_eq_of_lt (a := F) (by omega)]; omega
  refine ⟨h1, by rw [hs]; omega, by rw [hs]; omega⟩

theorem pcode_sub {m : Runner.Mem} {A : D.Fn → Nat} {C : D.Fn → List II} {fp : Runner.W} {K F : Nat}
    (h : PCode m A C fp K) (hlt : fp.toNat + 8 * K < 2 ^ 64) (hF : F ≤ K) :
    PCode m A C (slot fp (BitVec.ofNat 64 F)) (K - F) :=
  fun g => ⟨(h g).1, codeFar_sub (h g).2 hlt hF⟩

theorem pcode_agree {m m' : Runner.Mem} {A : D.Fn → Nat} {C : D.Fn → List II} {fp : Runner.W} {K lo : Nat}
    (h : PCode m A C fp K) (ha : Agree fp lo K m m') : PCode m' A C fp K :=
  fun g => ⟨(h g).1.agree ha (h g).2, (h g).2⟩

theorem WIn.sub {L : Lay D} {fp : Runner.W} {Ks K F : Nat} (h : WIn L fp Ks K) (hF : F ≤ Ks)
    (hr : fp.toNat + 8 * K < 2 ^ 64) : WIn L (slot fp (BitVec.ofNat 64 F)) (Ks - F) (K - F) := by
  have hs : (slot fp (BitVec.ofNat 64 F)).toNat = fp.toNat + 8 * F := by
    have := fp.isLt
    have h8 : (8 : Runner.W).toNat = 8 := rfl
    simp only [slot, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h8]
    rw [Nat.mod_eq_of_lt (a := F) (by have := h.ks; omega)]; have := h.ks; omega
  have := h.top; have := h.ks
  exact ⟨h.lay, h.dis, by rw [hs]; omega, h.ord, by omega⟩

/-! ## What a statement keeps -/

theorem envAt_agreeW {L : Lay D} {m m' : Runner.Mem} {fp : Runner.W} {Γ : Ctx} {ρ : Env D Γ} {d K : Nat}
    (h : EnvAt L m fp ρ) (ha : AgreeW L fp d K m m') (htop : fp.toNat + 8 * K ≤ L.lo) (hr : fp.toNat + 8 * K ≤ 2 ^ 64)
    (hd : frei Γ ≤ d) (hK : d ≤ K) : EnvAt L m' fp ρ := by
  intro τ x
  obtain ⟨w, hw, he⟩ := h τ x
  refine ⟨w, ?_, he⟩
  rw [agreeW_rd_low ha htop hr (by have := vslot_lt x; omega) hK]
  exact hw

theorem pcode_agreeW {L : Lay D} {m m' : Runner.Mem} {A : D.Fn → Nat} {C : D.Fn → List II} {fp : Runner.W}
    {K lo : Nat} (h : PCode m A C fp K) (ha : AgreeW L fp lo K m m') (htop : fp.toNat + 8 * K ≤ L.lo)
    (hl : L.hi < 2 ^ 31) (hord : L.lo ≤ L.hi) : PCode m' A C fp K :=
  fun g => ⟨codeAt_agreeW ha htop hl hord (h g).1 (h g).2, (h g).2⟩

theorem WIn.room {L : Lay D} {fp : Runner.W} {Ks K : Nat} (h : WIn L fp Ks K) : fp.toNat + 8 * K < 2 ^ 31 := by
  have := h.top; have := h.lay.2.2; have := h.ord; omega

end Gabbro.Stage0.Senke
