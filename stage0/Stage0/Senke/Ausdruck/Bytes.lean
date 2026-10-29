/-
  Subject: Little-endian byte spans against G's `bytesAb` and `bytesZuZahl`.
  Each byte is read from its own world word; arithmetic packs the result into one IR word.
-/
import Stage0.Senke.Ausdruck.Lesen

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
set_option maxRecDepth 2048
variable [Kern] {D : Deklaration}

theorem wert_transport_eq_cast {τ τ' : Ty} (h : τ = τ') (v : Wert D τ) :
    (h ▸ v : Wert D τ') = cast (congrArg (Wert D) h) v := by
  cases h; rfl

theorem readBytesL_ok {L : Lay D} {Λ : List (Res D)} {Γ : Ctx} {a b : Int}
    (i : Expr D Γ Λ (.int a b)) {t : D.Tab} {f : D.Feld t} (hf : D.typ t f = .int 0 255)
    {σ₀ σ : World D} {fp : Runner.W} {K : Nat} {W : Runner.Mem → Prop} {ρ : Env D Γ}
    (hWL : ∀ m, W m → WeltAt m L σ) (hlo : 0 ≤ a)
    (ih : ∀ d c top, lowE L i d = some (c, top) → top ≤ K → ∀ m pc,
      Pre L m pc fp K d c ρ W → Ok m pc fp K d c (Enc L (.int a b) (eval σ₀ i σ ρ))) :
    (n j d : Nat) → (c : List II) → (top : Nat) →
    b + j + n ≤ D.count t → j + n ≤ 8 →
    readBytesL L t f (lowE L i) j n d = some (c, top) → top ≤ K →
    ∀ m pc, Pre L m pc fp K d c ρ W →
    Ok m pc fp K d c (fun w => w = BitVec.ofInt 64
      (bytesZuZahl (σ.bytesAb t f hf n ((eval σ₀ i σ ρ).n + j))))
  | 0, j, d, c, top, _, _, h, hK, m, pc, hp => by
    simp only [readBytesL, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (const_ok hp (by decide) (by omega)).mono (fun w hw => hw)
  | n + 1, j, d, c, top, hhi, hj, h, hK, m, pc, hp => by
    simp only [readBytesL, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ci', ti⟩, hi, ⟨head, th⟩, hh, ⟨tail, tt⟩, ht, h⟩ := h
    simp only [bin2, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hhTop := slotC_top hh
    simp only [bin2] at hhTop
    let ix : Expr D Γ Λ (.index (D.count t)) :=
      .widen (by omega) (by omega) (.add i (.lit (j : Int)))
    have hhead : ∀ m pc, Pre L m pc fp K d head ρ W →
        Ok m pc fp K d head (fun w => w = BitVec.ofInt 64
          (hf ▸ σ.slots t ((eval σ₀ i σ ρ).n + j) f : Wert D (.int 0 255)).n) := by
      intro m pc hp
      have hread := slotC_ok (σ₀ := σ₀) (i := ix) hh (by omega) (fun m pc hp => ?_) hWL hp
      · exact hread.mono (fun w hw => (enc_int_cast hf _ w).mp hw)
      · refine bin_ok (ih d ci' ti hi (by omega))
          (fun m pc hp => const_ok hp (lit32_nat (by omega)) (by omega))
          (g := fun x y => some (x + y)) ?_ rfl (by decide) (by omega) hp
        intro wa wb pa pb
        refine ⟨_, rfl, ?_⟩
        simp only [Enc] at pa
        rw [pa, pb, ← BitVec.ofInt_add]
        rfl
    refine bin_ok (Pb := fun w => w = BitVec.ofInt 64
      (bytesZuZahl (σ.bytesAb t f hf n ((eval σ₀ i σ ρ).n + (j + 1))) * 256)) hhead (fun m pc hp => bin_ok
      (readBytesL_ok i hf hWL hlo ih n (j + 1) (d + 1) tail tt (by omega) (by omega) ht (by omega))
      (fun m pc hp => const_ok hp (by decide) (by omega))
      (g := fun x y => some (x * y))
      (fun wa wb pa pb => ⟨_, rfl, by rw [pa, pb, ← BitVec.ofInt_mul]; simp only [Int.natCast_add, Int.natCast_one]⟩)
      rfl (by decide) (by omega) hp)
      (g := fun x y => some (x + y)) ?_ rfl (by decide) (by omega) hp
    intro wa wb pa pb
    refine ⟨_, rfl, ?_⟩
    rw [pa, pb, ← BitVec.ofInt_add]
    simp only [World.bytesAb, bytesZuZahl]
    apply congrArg (BitVec.ofInt 64)
    simp only [wert_transport_eq_cast, Int.add_assoc, Int.mul_comm]

end Gabbro.Stage0.Senke
