/- Storage address correctness, with child-expression obligations for table rows. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Stored.Read
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {currentOld : Bool}

/-- The one child of a storage root is its row index or checked reference.
    This is an induction interface, not another evaluator. -/
def StorageChildrenOk {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (σ₀ σ : World D) (ρ : Env D Γ) (fp : Runner.W) (K reserved : Nat)
    (W : Runner.Mem → Prop) (e : Expr D Γ Λ τ) : Prop :=
  match e with
  | .slot _ _ i _ | .thru _ _ _ _ i _ | .thruOwn _ _ _ _ i _ _ _ _ _ _ =>
    ∀ d c top, lowE (currentOld := currentOld) L (reserved := reserved) i d = some (c, top) → top ≤ K →
      ∀ m pc, Pre L m pc fp K d c ρ W reserved → ValueOk L m pc fp K d c _ (eval σ₀ i σ ρ)
  | .slotRef r _ _ _ _ _ =>
    ∀ d c top, lowE (currentOld := currentOld) L (reserved := reserved) r d = some (c, top) → top ≤ K →
      ∀ m pc, Pre L m pc fp K d c ρ W reserved → ValueOk L m pc fp K d c _ (eval σ₀ r σ ρ)
  | _ => True

theorem frameAddress_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K d base reserved : Nat}
    (pre : Pre L m pc fp K d [ci 17 d base 0] ρ W reserved)
    (baseFits : base < K) (destFits : d < K) :
    Ok m pc fp K d [ci 17 d base 0] (· = slot fp (BitVec.ofNat 64 base)) := by
  refine one_ok pre (by simp [ci]) destFits rfl fun m' write => ?_
  have instruction := pre.code 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at instruction
  simp only [ci, op]
  refine f2_run (t := ⟨_, fp⟩) instruction ?_
  simp only [ret1]
  refine f1_run (t := ⟨_, fp⟩) instruction ?_
  rw [sx_nat (by have := pre.small; omega), sx_nat (by have := pre.small; omega)]
  exact run_wr64 write

theorem storageCell_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {σ : World D} {t : D.Tab} {f : D.Feld t} {idx d K top reserved : Nat}
    {index : List II × Nat} {c : List II} {m : Runner.Mem} {pc fp : Runner.W}
    (made : cellAddressC L t f d index = some (c, top)) (fits : top ≤ K)
    (bound : (idx : Int) < L.count t) (world : ∀ m, W m → WeltAt m L σ)
    (child : ∀ m pc, Pre L m pc fp K d index.1 ρ W reserved →
      Ok m pc fp K d index.1 (· = BitVec.ofNat 64 idx))
    (pre : Pre L m pc fp K d c ρ W reserved) :
    StoredOk (L := L) m pc fp K d c ρ W reserved (D.typ t f) (σ.slots t idx f) :=
  ⟨_, cellAddressC_ok made fits child pre, fun m _ hm => (world m hm).1 t f idx bound⟩

/-- Address lowering never copies a stored value. Unsupported roots return none;
    accepted roots use the same canonical environment and world representation. -/
theorem lowStorage_sound {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} {W : Runner.Mem → Prop}
    (σ₀ σ : World D) (world : ∀ m, W m → WeltAt m L σ)
    (e : Expr D Γ Λ τ) {ρ : Env D Γ} {fp pc : Runner.W} {K d top reserved : Nat}
    {c : List II} {m : Runner.Mem}
    (child : StorageChildrenOk (L := L) (currentOld := currentOld) σ₀ σ ρ fp K reserved W e)
    (made : lowStorage (currentOld := currentOld) L (reserved := reserved) e d = some (c, top))
    (fits : top ≤ K) (pre : Pre L m pc fp K d c ρ W reserved) :
    StoredOk (L := L) m pc fp K d c ρ W reserved τ (eval σ₀ e σ ρ) := by
  cases e <;> try (simp only [lowStorage, lowStorageWith] at made; contradiction)
  case var x =>
    simp only [lowStorage, lowStorageWith, specLookup, Option.some.injEq, Prod.mk.injEq] at made
    obtain ⟨rfl, rfl⟩ := made
    refine ⟨_, frameAddress_ok pre (by have := vslot_lt (reserved := reserved) x; have := pre.ctx; omega)
      (by omega), ?_⟩
    intro m env _
    exact (env _ x).rebase
  case glob g access =>
    simp only [lowStorage, lowStorageWith] at made
    split at made
    · next literal =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj made)
      refine ⟨BitVec.ofNat 64 (L.ga g), ?_, fun m _ hm => (world m hm).2.1 g⟩
      exact (const_ok pre (by simp only [lit32, Bool.and_eq_true, decide_eq_true_eq]; omega)
        (by omega)).mono fun w hw => by simpa only [BitVec.ofInt_natCast] using hw
    · cases made
  case slot t f access i | thru t ht f access a i |
      thruOwn t ht f ownerMark ownerStage ownerNamed ownerHeld ownerGuard access a i =>
    simp only [lowStorage, lowStorageWith, bind, Option.bind_eq_some_iff] at made
    obtain ⟨⟨ci', ti⟩, hi, made⟩ := made
    have tops := cellAddressC_top made
    let index := eval σ₀ i σ ρ
    have nonnegative := index.lo_le
    have bound : (index.n.toNat : Int) < L.count t :=
      L.bounded (by have := index.le_hi; omega)
    have result := storageCell_ok made fits bound world
      (fun m pc hp => (child d ci' ti hi (by omega) m pc hp).word trivial |>.mono fun w hw => by
        change w = BitVec.ofInt 64 index.n at hw
        rw [hw, ← BitVec.ofInt_natCast, Int.toNat_of_nonneg nonnegative]) pre
    simpa only [eval, Int.toNat_of_nonneg nonnegative] using result
  case slotRef t ht ho f access r =>
    simp only [lowStorage, lowStorageWith, bind, Option.bind_eq_some_iff] at made
    obtain ⟨⟨ci', ti⟩, hi, made⟩ := made
    have tops := cellAddressC_top made
    have refWord := fun m pc hp => (child d ci' ti hi (by omega) m pc hp).word trivial
    have refPre : Pre L m pc fp K d ci' ρ W reserved := by
      unfold cellAddressC at made
      split at made
      · cases made
        exact pre.left
      · cases made
    obtain ⟨_, _, _, _, _, hv⟩ := refWord m pc refPre
    obtain ⟨_, _, t', ht', _, bound⟩ := hv
    have equal : t' = t := Option.some.inj (ht'.symm.trans ht)
    subst t'
    exact storageCell_ok made fits bound world
      (fun m pc hp => (refWord m pc hp).mono fun w hw => hw.1) pre

end Gabbro.Stage0.Senke
