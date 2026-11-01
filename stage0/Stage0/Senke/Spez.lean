/- The external complete-value call contract and checked nested frames.
   Parameters use contextWords; the canonical result starts at FB + parameterWords.
   Header word 2 mirrors its first word for startup/exit only. The status follows
   the complete shared normal/reason area, independently of private snapshots.
   Normal and reason returns preserve caller header words 0/1 and carry the resulting
   world. Logic and hardware outcomes retain their named stops. -/
import Stage0.Senke.Funktion
import Stage0.Senke.Ausdruck.Aggregat.Scalar
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

/-- What the exit status of a finished thread says about its result: the low word of the canonical
    encoding, and for a word-compatible type also the full scalar relation. Wider results exit with
    their first word. -/
def ExitErg (L : Lay D) : (e : Option Ty) → ErgVal D e → Runner.W → Prop
  | some τ, v, w => w = (encodeWords L τ v).headD 0 ∧ (WordCompatible τ → Enc L τ v w)
  | none, _, _ => True

/-- The checked normal return keeps the successful ensures Boolean in its output slot.
    A reason return writes zero there and mirrors its first encoded word in slot 2. -/
def ReturnFlag (m : Runner.Mem) (fp : Runner.W) (np : Nat) (ok : Bool) (nr : Nat := 1) : Prop :=
  m.rd64 (slot fp (BitVec.ofNat 64 (FB + np + nr))) = some (if ok then 1 else 0)

/-- A reason return preserves the frame header and carries the resulting world. -/
def RetWhy (L : Lay D) (f : D.Fn) (fp : Runner.W) (K : Nat) (rp cfp : Runner.W)
    (t : T) (m : Runner.Mem) (σ : World D) (r : Fin (D.gruende f)) : Prop :=
  ∃ m', Star t m ⟨rp, cfp⟩ m' ∧ AgreeW L fp 2 K m m' ∧
    ValueAt L m' fp (FB + contextWords (D.params f)) (.why (D.gruende f)) r ∧
    ReturnMirror m' fp (FB + contextWords (D.params f)) ∧
    ReturnFlag m' fp (contextWords (D.params f)) false (returnWords (D.erg f) (D.gruende f)) ∧ WeltAt m' L σ

theorem RetWhy.prefix {f : D.Fn} {fp : Runner.W} {K : Nat} {rp cfp : Runner.W}
    {t0 t : T} {m0 m : Runner.Mem} {σ : World D} {r : Fin (D.gruende f)}
    (h : Star t0 m0 t m) (ha : AgreeW L fp 2 K m0 m) (hs : RetWhy L f fp K rp cfp t m σ r) :
    RetWhy L f fp K rp cfp t0 m0 σ r := by
  obtain ⟨m', s, a, value, mirror, flag, world⟩ := hs
  exact ⟨m', h.trans s, ha.trans a, value, mirror, flag, world⟩

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
        (ResultAt L m' fp (FB + contextWords (D.params f)) (D.erg f) v ∧
          ReturnMirror m' fp (FB + contextWords (D.params f)) ∧
          ReturnFlag m' fp (contextWords (D.params f)) true (returnWords (D.erg f) (D.gruende f))) ∧ WeltAt m' L σ'
    | .logik e => Stops ⟨BitVec.ofNat 64 (A f), fp⟩ m (logikCode e)
    | .hardware h => Stops ⟨BitVec.ofNat 64 (A f), fp⟩ m (hwCode h)
    | .why σ' r => RetWhy L f fp K rp cfp ⟨BitVec.ofNat 64 (A f), fp⟩ m σ' r

/-! ## Frames inside frames -/

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

/-- A userspace world update preserves every limb of a value below the local write area. -/
theorem ValueAt.agreeW {L : Lay D} {m m' : Runner.Mem} {fp : Runner.W} {base d K : Nat}
    {τ : Ty} {v : Wert D τ} (value : ValueAt L m fp base τ v)
    (changed : AgreeW L fp d K m m') (world : fp.toNat + 8 * K ≤ L.lo)
    (room : fp.toNat + 8 * K ≤ 2 ^ 64) (below : base + valueWords τ ≤ d)
    (fits : d ≤ K) : ValueAt L m' fp base τ v := by
  refine ⟨value.1, ?_⟩
  intro i hi
  have width : i < valueWords τ := by simpa only [encodeWords_length] using hi
  rw [agreeW_rd_low changed world room (by omega) fits]
  exact value.2 i hi

theorem envAt_agreeW {L : Lay D} {m m' : Runner.Mem} {fp : Runner.W} {Γ : Ctx} {ρ : Env D Γ} {d K reserved : Nat}
    (h : EnvAt L m fp ρ reserved) (ha : AgreeW L fp d K m m') (htop : fp.toNat + 8 * K ≤ L.lo) (hr : fp.toNat + 8 * K ≤ 2 ^ 64)
    (hd : frei Γ reserved ≤ d) (hK : d ≤ K) : EnvAt L m' fp ρ reserved := by
  intro τ x
  have placed : vslot x reserved + valueWords τ ≤ frei Γ reserved := by
    have bound := variableOffset_bound x
    unfold vslot frei
    omega
  exact (h τ x).agreeW ha htop hr (by omega) hK
theorem pcode_agreeW {L : Lay D} {m m' : Runner.Mem} {A : D.Fn → Nat} {C : D.Fn → List II} {fp : Runner.W}
    {K lo : Nat} (h : PCode m A C fp K) (ha : AgreeW L fp lo K m m') (htop : fp.toNat + 8 * K ≤ L.lo)
    (hl : L.hi < 2 ^ 31) (hord : L.lo ≤ L.hi) : PCode m' A C fp K :=
  fun g => ⟨codeAt_agreeW ha htop hl hord (h g).1 (h g).2, (h g).2⟩

theorem WIn.room {L : Lay D} {fp : Runner.W} {Ks K : Nat} (h : WIn L fp Ks K) : fp.toNat + 8 * K < 2 ^ 31 := by
  have := h.top; have := h.lay.2.2; have := h.ord; omega

end Gabbro.Stage0.Senke
